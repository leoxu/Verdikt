#include <cctype>
// z3 as a child process speaking SMT-LIB2 over pipes. Third-party specifics (the executable, its output syntax) stay in
// this file; nothing here leaks through smt::Solver.
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <cerrno>
#include <unordered_map>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include "hlir/smt/Solver.h"
#include "llvm/ADT/StringRef.h"

namespace hlir::smt {

namespace {

const char *kSentinel = "@@END@@";

// Minimal S-expression tree for z3's replies.
struct SExp {
  std::string atom;
  std::vector<SExp> list;
  bool isList = false;
};

class SExpParser {
 public:
  explicit SExpParser(const std::string &s) : s_(s) {}
  bool parse(SExp &out) {
    skip();
    if (i_ >= s_.size()) return false;
    if (s_[i_] == '(') {
      ++i_;
      out.isList = true;
      for (;;) {
        skip();
        if (i_ >= s_.size()) return false;
        if (s_[i_] == ')') { ++i_; return true; }
        SExp c;
        if (!parse(c)) return false;
        out.list.push_back(std::move(c));
      }
    }
    size_t b = i_;
    if (s_[i_] == '|') {
      ++i_;
      while (i_ < s_.size() && s_[i_] != '|') ++i_;
      if (i_ >= s_.size()) return false;
      ++i_;
      out.atom = s_.substr(b + 1, i_ - b - 2);
      return true;
    }
    while (i_ < s_.size() && !isspace(static_cast<unsigned char>(s_[i_])) && s_[i_] != '(' && s_[i_] != ')') ++i_;
    out.atom = s_.substr(b, i_ - b);
    return true;
  }

 private:
  void skip() { while (i_ < s_.size() && isspace(static_cast<unsigned char>(s_[i_]))) ++i_; }
  const std::string &s_;
  size_t i_ = 0;
};

bool toAPInt(const SExp &e, unsigned width, llvm::APInt &out) {
  if (!e.isList) {
    const std::string &a = e.atom;
    if (a.size() > 2 && a[0] == '#' && a[1] == 'x') { out = llvm::APInt(width, llvm::StringRef(a).substr(2), 16); return true; }
    if (a.size() > 2 && a[0] == '#' && a[1] == 'b') { out = llvm::APInt(width, llvm::StringRef(a).substr(2), 2); return true; }
    return false;
  }
  // (_ bv<N> <w>)
  if (e.list.size() == 3 && !e.list[0].isList && e.list[0].atom == "_" && e.list[1].atom.rfind("bv", 0) == 0) {
    out = llvm::APInt(width, llvm::StringRef(e.list[1].atom).substr(2), 10);
    return true;
  }
  return false;
}

class Z3Process final : public Solver {
 public:
  Z3Process(pid_t pid, int in, int out) : pid_(pid), in_(in), out_(out) {}
  ~Z3Process() override {
    if (in_ >= 0) { send("(exit)\n"); close(in_); }
    if (out_ >= 0) close(out_);
    if (pid_ > 0) {
      int st;
      waitpid(pid_, &st, 0);
    }
  }

  bool init(unsigned timeoutMs) {
    initTimeoutMs_ = timeoutMs;
    std::string cmd = "(set-option :print-success false)\n(set-option :produce-unsat-cores true)\n(set-option :produce-models true)\n";
    if (timeoutMs) cmd += "(set-option :timeout " + std::to_string(timeoutMs) + ")\n";
    cmd += "(set-logic QF_ABV)\n";
    std::string r;
    return roundTrip(cmd, r) && r.empty();
  }

  void push() override { emit_.push(); command("(push 1)\n"); ++depth_; }
  void pop() override { emit_.pop(); command("(pop 1)\n"); --depth_; }

  // Each distinct term is asserted once, at the top level, as `lit => term`; a query is a check-sat-assuming over the literals.
  SatResult checkAssuming(const std::vector<TermRef> &terms) override {
    static const char *force = getenv("HLIR_SMT_MODE");  // debugging/A-B aid: "push" or "assume" instead of the adaptive choice
    lastCoreable_ = false;  // only the literal path can answer unsatCoreAssumptions(); the push path asserts anonymously
    if (depth_ != 0 || !inSession_) return Solver::checkAssuming(terms);
    bool viaAssume = chooseAssume(force);
    auto tq = std::chrono::steady_clock::now();
    SatResult res = viaAssume ? checkViaLiterals(terms) : (usedPush_ = true, Solver::checkAssuming(terms));
    double ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - tq).count();
    (viaAssume ? assumeStat_ : pushStat_).add(ms);
    if (!viaAssume) usedPush_ = true;
    return res;
  }

  // Two ways to answer the same query: (a) assumption literals — every distinct term is parsed once, later queries reuse it; good
  // when queries share large cones; (b) push/assert/check/pop with the assertions batched into one write — no global state, good
  // when cones are small or rarely repeated. Which one is faster depends on the workload, so both are sampled and the faster
  // mean wins, with a regular re-sample of the other one.
  struct Stat {
    double sum = 0; unsigned n = 0;
    void add(double ms) { sum += ms; ++n; if (n > 200) { sum *= 0.5; n /= 2; } }   // forgets old samples
    double mean() const { return n ? sum / n : 1e30; }
  };
  // THE MODE IS FIXED, and that is a correctness property, not a tuning preference (DESIGN.md §22.444).
  //
  // This used to pick whichever of the two protocols had the lower MEASURED MEAN so far. The two are equivalent
  // in what they decide -- sat is sat -- but not in what they hand back: `(check-sat-assuming ...)` can answer
  // `(get-unsat-core)` and the push path cannot, and, decisive here, the two return DIFFERENT satisfying models
  // for the same query. The concolic search feeds that model back in as the next run's input, so which protocol
  // answered decided what the scanner explored next. Measured: identical commands differing only in where the
  // adaptive switch happened to flip gave 98/99/103 solver queries and 2/5/11 findings on the same entry, and
  // the transcripts were byte-identical -- queries AND answers -- right up to the query where one run said
  // `(push 1)` and the other said `(check-sat-assuming ...)`.
  //
  // `assume` is the default: on the same fixed work it was the faster of the two here (analysis 1.6s vs 1.7-1.9s,
  // solver 0.37s vs 0.47s), and it is the only one that can produce an unsat core, which --unsat-core-guide
  // otherwise silently does without. HLIR_SMT_MODE=adaptive restores the old timing-based choice for
  // benchmarking; it makes the scan irreproducible and is never the default.
  bool chooseAssume(const char *force) {
    if (force) {
      const std::string m(force);
      if (m == "assume") return true;
      if (m == "push") return false;
      if (m != "adaptive") return true;   // an unknown value is not a silent fall-back to the timing race
      unsigned q = assumeStat_.n + pushStat_.n;
      if (assumeStat_.n < 24 || pushStat_.n < 24) return assumeStat_.n <= pushStat_.n;  // initial sampling, alternating
      bool assumeBetter = assumeStat_.mean() <= pushStat_.mean();
      if (q % 16 == 0) return !assumeBetter;                                            // keep sampling the loser
      return assumeBetter;
    }
    return true;
  }
  Stat assumeStat_, pushStat_;
  bool usedPush_ = false;
  std::map<std::string, size_t> lastAssumPos_;  // assumption literal name -> its position in the last checkAssuming
  bool lastCoreable_ = false;

  SatResult checkViaLiterals(const std::vector<TermRef> &terms) {
    ++checks_;
    // The emitter and the literal table know terms by (manager, id): one manager at a time. When another manager's terms
    // arrive, everything z3 was told at the top level is forgotten ((reset) + options again).
    if (!terms.empty()) noteMgr(terms.front());
    topDirty_ = true;
    std::string out, assuming;
    lastAssumPos_.clear();
    for (size_t i = 0; i < terms.size(); ++i) {
      TermRef t = terms[i];
      if (t->isTrue()) continue;
      auto it = lits_.find(t->id);
      if (it == lits_.end()) {
        std::string name = "|la" + std::to_string(t->id) + "|";
        std::string e = emit_.emit(t, out);
        out += "(declare-const " + name + " Bool)\n(assert (=> " + name + " " + e + "))\n";
        it = lits_.emplace(t->id, name).first;
      }
      // A term can legitimately appear twice in one query; the FIRST position is the one reported, which is the
      // earliest path condition that carries it and therefore the earliest branch a caller could flip.
      lastAssumPos_.emplace(it->second, i);
      assuming += it->second + " ";
    }
    lastCoreable_ = true;
    command(out);
    std::string r;
    auto t0 = std::chrono::steady_clock::now();
    bool okRt = roundTrip("(check-sat-assuming (" + assuming + "))\n", r);
    if (const char *lp = getenv("HLIR_Z3_TIMES")) {
      static FILE *tl = fopen(lp, "a");
      if (tl) { fprintf(tl, "%.1f %s\n", std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count(), r.c_str()); fflush(tl); }
    }
    if (!okRt) return SatResult::Unknown;
    if (r == "sat") return SatResult::Sat;
    if (r == "unsat") return SatResult::Unsat;
    if (r != "unknown") err_ = "unexpected check-sat-assuming reply: " + r;
    return SatResult::Unknown;
  }
  void endCheckAssuming() override { Solver::endCheckAssuming(); }
  void beginSession() override { if (topDirty_ && depth_ == 0) resetTopLevel(); inSession_ = true; }
  void endSession() override { inSession_ = false; if (topDirty_ && depth_ == 0) resetTopLevel(); }

  void assertTerm(TermRef t, const std::string &name) override {
    noteMgr(t);
    std::string out;
    std::string e = emit_.emit(t, out);
    if (name.empty()) out += "(assert " + e + ")\n";
    else out += "(assert (! " + e + " :named |" + name + "|))\n";
    command(out);
  }

  SatResult check() override {
    ++checks_;
    std::string r;
    auto t0 = std::chrono::steady_clock::now();
    bool okRt = roundTrip("(check-sat)\n", r);
    if (const char *lp = getenv("HLIR_Z3_TIMES")) {  // debugging aid: one line per check-sat: milliseconds, reply
      static FILE *tl = fopen(lp, "a");
      if (tl) { fprintf(tl, "%.1f %s\n", std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count(), r.c_str()); fflush(tl); }
    }
    if (!okRt) return SatResult::Unknown;
    if (r == "sat") return SatResult::Sat;
    if (r == "unsat") return SatResult::Unsat;
    if (r != "unknown") err_ = "unexpected check-sat reply: " + r;
    return SatResult::Unknown;
  }

  std::vector<llvm::APInt> values(const std::vector<TermRef> &vars) override {
    std::vector<llvm::APInt> res;
    for (auto *v : vars) res.emplace_back(v->sort.width, 0);
    if (vars.empty()) return res;
    std::string cmd, names;
    std::vector<std::string> exprs;
    if (!vars.empty()) noteMgr(vars.front());
    if (depth_ == 0) topDirty_ = true;
    for (auto *v : vars) exprs.push_back(emit_.emit(v, cmd));  // any bit-vector term, not only variables
    for (auto &e : exprs) names += e + " ";
    cmd += "(get-value (" + names + "))\n";
    std::string r;
    if (!roundTrip(cmd, r)) return res;
    SExp e;
    SExpParser p(r);
    if (!p.parse(e) || !e.isList || e.list.size() != vars.size()) { err_ = "cannot parse model: " + r; return res; }
    for (size_t i = 0; i < vars.size(); ++i) {
      const SExp &pair = e.list[i];
      llvm::APInt v;
      if (!pair.isList || pair.list.size() != 2 || !toAPInt(pair.list[1], vars[i]->sort.width, v)) { err_ = "cannot parse model value: " + r; return res; }
      res[i] = v;
    }
    return res;
  }

  // The literal path already names every assumption (|la<termid>|) and the session already runs with
  // :produce-unsat-cores true, so the core comes back as a subset of those names and only has to be mapped to the
  // positions the caller passed. The push path asserts anonymously and reports nothing, which is "no information".
  std::vector<size_t> unsatCoreAssumptions() override {
    std::vector<size_t> res;
    if (!lastCoreable_ || lastAssumPos_.empty()) return res;
    std::string r;
    if (!roundTrip("(get-unsat-core)\n", r)) return res;
    SExp e;
    SExpParser p(r);
    if (!p.parse(e) || !e.isList) { err_ = "cannot parse unsat core: " + r; return res; }
    // z3 echoes a symbol WITHOUT the |...| quoting when it does not need it, and "la123" does not, so the name that
    // comes back is not spelled the way it was sent. Both sides are stripped before they are compared.
    auto bare = [](const std::string &n) {
      return n.size() >= 2 && n.front() == '|' && n.back() == '|' ? n.substr(1, n.size() - 2) : n;
    };
    std::map<std::string, size_t> byBare;
    for (auto &kv : lastAssumPos_) byBare.emplace(bare(kv.first), kv.second);
    for (auto &c : e.list) {
      auto it = byBare.find(bare(c.atom));
      if (it != byBare.end()) res.push_back(it->second);
    }
    std::sort(res.begin(), res.end());
    res.erase(std::unique(res.begin(), res.end()), res.end());
    return res;
  }

  std::vector<std::string> unsatCore() override {
    std::vector<std::string> res;
    std::string r;
    if (!roundTrip("(get-unsat-core)\n", r)) return res;
    SExp e;
    SExpParser p(r);
    if (!p.parse(e) || !e.isList) { err_ = "cannot parse unsat core: " + r; return res; }
    for (auto &c : e.list) res.push_back(c.atom);
    return res;
  }

  void setTimeoutMs(unsigned ms) override { command("(set-option :timeout " + std::to_string(ms ? ms : 4294967295u) + ")\n"); }
  std::string name() const override { return "z3-process"; }
  std::string lastError() const override { return err_; }
  uint64_t checkCount() const override { return checks_; }

 private:
  static FILE *logFile() {
    static FILE *log = [] { const char *p = getenv("HLIR_Z3_LOG"); return p ? fopen(p, "a") : nullptr; }();
    return log;
  }
  static void logReply(const std::string &r) {
    if (FILE *log = logFile()) { fprintf(log, ";; <- %s\n", r.c_str()); fflush(log); }
  }
  bool send(const std::string &s) {
    FILE *log = logFile();  // debugging aid: every byte sent to z3, and every answer
    if (log) { fwrite(s.data(), 1, s.size(), log); fflush(log); }
    size_t off = 0;
    while (off < s.size()) {
      ssize_t n = write(in_, s.data() + off, s.size() - off);
      if (n < 0) {
        if (errno == EINTR) continue;
        err_ = std::string("write to z3 failed: ") + strerror(errno);
        return false;
      }
      off += static_cast<size_t>(n);
    }
    return true;
  }

  // Sends `cmd` followed by an echo sentinel; `reply` receives everything printed before it (trimmed).
  bool roundTrip(const std::string &cmd, std::string &reply) {
    reply.clear();
    if (!err_.empty() && dead_) return false;
    std::string batch;
    batch.swap(pending_);
    lastBatch_ = batch + cmd;
    if (!send(batch + cmd + "(echo \"" + kSentinel + "\")\n")) { dead_ = true; return false; }
    std::string buf;
    char tmp[4096];
    for (;;) {
      size_t pos = buf.find(kSentinel);
      if (pos != std::string::npos) { buf.resize(pos); break; }
      ssize_t n = read(out_, tmp, sizeof tmp);
      if (n < 0 && errno == EINTR) continue;
      if (n <= 0) { err_ = "z3 closed its output unexpectedly"; dead_ = true; return false; }
      buf.append(tmp, static_cast<size_t>(n));
    }
    size_t b = buf.find_first_not_of(" \r\n\t"), e = buf.find_last_not_of(" \r\n\t");
    reply = b == std::string::npos ? "" : buf.substr(b, e - b + 1);
    logReply(reply);  // HLIR_Z3_LOG is a TRANSCRIPT, not a send-log: without the answers a diff of two runs
                      // cannot tell "we asked something different" from "z3 answered differently" (§22.444).
    if (reply.rfind("(error", 0) == 0 || reply.rfind("unsupported", 0) == 0 || reply.find("(error ") != std::string::npos) {
      err_ = "z3: " + reply;
      if (getenv("HLIR_Z3_DEBUG")) fprintf(stderr, "[z3 error] %s\n--- batch:\n%s\n---\n", reply.c_str(), lastBatch_.c_str());
      return false;
    }
    return true;
  }

  // For commands whose only output would be an error (print-success is off): queued and sent together with the next command
  // that has an answer (check-sat, get-value, ...), so a query costs one round trip, not one per assertion. An error z3 reports
  // for a queued command shows up in that answer.
  void command(const std::string &cmd) { pending_ += cmd; }
  std::string pending_, lastBatch_;
  unsigned depth_ = 0;
  std::unordered_map<uint32_t, std::string> lits_;  // Term::id (of manager litMgr_) -> literal name
  uint32_t litMgr_ = 0;
  bool inSession_ = false;
  bool topDirty_ = false;  // something was declared/asserted at the top level (literal mode): it belongs to litMgr_
  // The emitter and the literal table know terms by (manager, id), one manager at a time. Terms of another manager arriving when
  // the top level holds state from the previous one: forget it all ((reset) + options again).
  void noteMgr(TermRef t) {
    if (litMgr_ == t->mgr) return;
    if (litMgr_ != 0 && topDirty_ && depth_ == 0) resetTopLevel();
    litMgr_ = t->mgr;
  }
  unsigned initTimeoutMs_ = 0;
  void resetTopLevel() {
    pending_.clear();
    lits_.clear();
    emit_ = SmtLibEmitter();
    topDirty_ = false;
    std::string cmd = "(reset)\n(set-option :print-success false)\n(set-option :produce-unsat-cores true)\n(set-option :produce-models true)\n";
    if (initTimeoutMs_) cmd += "(set-option :timeout " + std::to_string(initTimeoutMs_) + ")\n";
    cmd += "(set-logic QF_ABV)\n";
    command(cmd);
  }

  pid_t pid_;
  int in_, out_;
  SmtLibEmitter emit_;
  std::string err_;
  bool dead_ = false;
  uint64_t checks_ = 0;
};

}  // namespace

std::unique_ptr<Solver> makeZ3ProcessSolver(const std::string &exe, unsigned timeoutMs) {
  signal(SIGPIPE, SIG_IGN);
  int toChild[2], fromChild[2];
  if (pipe(toChild) != 0) return nullptr;
  if (pipe(fromChild) != 0) { close(toChild[0]); close(toChild[1]); return nullptr; }
  pid_t pid = fork();
  if (pid < 0) return nullptr;
  if (pid == 0) {
    dup2(toChild[0], 0);
    dup2(fromChild[1], 1);
    close(toChild[0]); close(toChild[1]); close(fromChild[0]); close(fromChild[1]);
    execlp(exe.c_str(), exe.c_str(), "-in", static_cast<char *>(nullptr));
    _exit(127);
  }
  close(toChild[0]);
  close(fromChild[1]);
  auto s = std::make_unique<Z3Process>(pid, toChild[1], fromChild[0]);
  if (!s->init(timeoutMs)) return nullptr;
  return s;
}

}  // namespace hlir::smt

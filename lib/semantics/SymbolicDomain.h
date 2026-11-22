// Private. Symbolic value domain: values are SMT terms (bool = 1-bit vector, like the concrete domain), and the domain
// carries the path state: path condition, the branch-decision schedule being replayed, and the findings sink.
#pragma once
#include <chrono>
#include <algorithm>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

#include "llvm/ADT/SmallString.h"
#include "Machine.h"
#include "Pred.h"
#include "TermOps.h"
#include "hlir/smt/Solver.h"

namespace hlir {

// Results of solver queries, shared by all runs of one exploration (replayed prefixes hit it every time).
struct QueryCache {
  std::unordered_map<std::string, smt::SatResult> map;
};

class SymbolicDomain : public TermOps {
 public:
  using Val = smt::TermRef;
  using Schedule = std::vector<uint8_t>;

  struct Hooks {
    // A property can fail on this path: `inputs` is a satisfying assignment of the symbolic variables.
    std::function<void(const Finding &, const smt::Assignment &)> onFinding;
    std::function<void(const Schedule &)> onFork;  // the alternative branch, to be explored later
  };

  SymbolicDomain(smt::TermManager &tm, smt::Solver &sol, QueryCache &cache, Hooks hooks, Schedule schedule)
      : TermOps(tm), sol_(sol), cache_(cache), hooks_(std::move(hooks)), schedule_(std::move(schedule)) {}

  // ---- path state
  const std::vector<smt::TermRef> &pc() const { return pc_; }
  bool incomplete() const { return incomplete_; }
  bool dead() const { return dead_; }
  uint64_t queries() const { return queries_; }
  const std::vector<smt::TermRef> &nondetVars() const { return nondets_; }
  void addInputVar(smt::TermRef v) { vars_.push_back(v); }
  void constrain(smt::TermRef boolTerm) { if (!boolTerm->isTrue()) pc_.push_back(boolTerm); }

  // ---- memory-model support (see Memory.h)
  static constexpr bool kExact = false;
  static constexpr bool kArrays = true;
  // Evidence only: answer "is this symbolic" / "what concrete value does it carry" WITHOUT the
  // concretisation side effect constValue() has on the concolic domain (it counts a followed tainted
  // pointer, which would make the concretized_pointer assumption count reads that are only being
  // reported). Used by Memory::objEvidence (DESIGN.md §22.369).
  // A Val here is a POINTER, and an unset one is null: the second half of a register slot (`Slot::b`, the
  // offset of a non-pointer value) and the fields of an object that was never given a size or contents are
  // all default-constructed. The taint domain's Val is a struct, so this case does not arise there and the
  // setup-region freeze (DESIGN.md §22.438, §22.442) called straight through to `v->kind` and crashed the
  // worker with SIGSEGV. Null is "nothing here": not symbolic, nothing to freeze.
  static bool isSymbolicVal(const Val &v) { return v && !constValue(v).has_value(); }
  static std::optional<llvm::APInt> peekVal(const Val &v) { return constValue(v); }
  static std::optional<llvm::APInt> constValue(Val v) {
    if (v && v->kind == smt::Kind::BvConst) return v->value;
    return std::nullopt;
  }
  static bool same(Val a, Val b) { return a == b; }
  bool asIte(Val v, Val &c, Val &a, Val &b) {
    if (v->kind != smt::Kind::Ite) return false;
    c = tm_.fromBool(v->args[0]);
    a = v->args[1];
    b = v->args[2];
    return true;
  }
  Val input(Env &, const std::string &name, unsigned w) {
    smt::TermRef v = tm_.bvVar(name, w);
    if (std::find(vars_.begin(), vars_.end(), v) == vars_.end()) vars_.push_back(v);
    return v;
  }
  Val harnessInput(Env &e, const std::string &name, unsigned w) { return input(e, name, w); }
  // The "w<idx>x<elem>" suffix is load-bearing, for the same reason as in `fresh` below (DESIGN.md §22.414).
  Val freshArr(const std::string &name, unsigned idxW, unsigned elemW) {
    return tm_.arrVar(name + "#" + std::to_string(freshCount_++) + "w" + std::to_string(idxW) + "x" + std::to_string(elemW), idxW, elemW);
  }
  // An entry-parameter object's content array was read at `idx`: remember it so a model can name the bytes it chose.
  void noteInputRead(uint32_t objId, Val idx) { inputReads_.push_back({objId, idx}); }
  // Unwinding assertion: `cond` must hold for the exploration to be complete. A feasible violation is reported as an
  // incomplete bound (not a bug); the path continues under `cond`.
  void unwind(Val cond, const char *what) {
    smt::TermRef b = tm_.toBool(cond);
    if (b->isTrue()) return;
    if (sat(tm_.mkNot(b)) != smt::SatResult::Unsat) { boundInsufficient_ = true; boundWhat_ = what; }
    pc_.push_back(b);
  }
  bool boundInsufficient() const { return boundInsufficient_; }
  const std::string &boundWhat() const { return boundWhat_; }
  // `freshCount_` restarts with each run; the TermManager does not. So the same name+counter can come back on a
  // later run standing for a DIFFERENT value -- and if that value has another width, TermManager::bvVar used to
  // abort the worker with SIGABRT, leaving the entry a silent `unknown` with runs=0 (DESIGN.md §22.414). The
  // width belongs in the name.
  Val fresh(const std::string &name, unsigned w) {
    smt::TermRef v = tm_.bvVar(name + "#" + std::to_string(freshCount_++) + "w" + std::to_string(w), w);
    vars_.push_back(v);
    return v;
  }

  // Instrumentation hooks (no-ops here; the taint domain uses them to classify functions and build its slice).
  static constexpr bool kTaint = false;
  static bool isTainted(Val) { return false; }
  static void noteSelectedAddress() {}  // see TaintDomain::noteSelectedAddress (DESIGN.md Sec.22.487)
  static bool isAttackerControlled(Val) { return false; }
  static bool onlyFrontier(Val) { return false; }
  static void beginOp(const Op &) {}
  // Inside a harness-declared setup region (DESIGN.md §22.442) this domain must NOT fork.
  //
  // Two reasons, and the second is the one that makes it a correctness condition rather than a policy:
  //
  // 1. The harness declared the region input-independent. A branch in there is decided by constants or by
  //    something the ENGINE invented (an allocation that may fail, an opaque external's result) -- never by
  //    the entry's input. Forking on the engine's own inventions is exploring the environment, not the
  //    program, and §22.440 already settled that question for allocations, for every engine.
  //
  // 2. A path is replayed from a SCHEDULE of branch decisions. If path 0 forked inside the region and a
  //    later path RESTORES the region instead of executing it, every queued schedule whose prefix lies
  //    inside the region indexes decisions that no longer happen, and each one replays a different program
  //    than the one it was queued for. Caching the region and forking inside it are mutually exclusive.
  //
  // So in the region: pick a feasible direction, queue nothing, and -- this is the part that is easy to get
  // wrong -- do not extend `taken_`. `taken_` IS the schedule later paths replay; a decision recorded here
  // would be a decision a restoring path never makes.
  void setSetupRegion(bool on) { setupRegion_ = on; }
  // Nothing to freeze: this domain has no concrete side to fall back on, so a non-constant simply refuses.
  static std::optional<Val> freezeVal(const Val &v) {
    if (!v) return std::optional<Val>(v);  // nothing there to freeze; see isSymbolicVal
    return constValue(v) ? std::optional<Val>(v) : std::nullopt;
  }
  static void onCall(const Function &) {}
  static void onReturn(const Function &, const Val *) {}
  static void noteStore(const Val &) {}
  static void noteKill() {}
  Val modelInput(Env &env, const std::string &name, unsigned w, const std::string &, const std::optional<llvm::APInt> & = std::nullopt) { return input(env, name, w); }
  static Val opaqueDerived(Val cur, const std::vector<Val> &, const std::string &) { return cur; }
  static Val clearTaint(Val v) { return v; }
  template <class MakeFinding> static void taintSink(Val, MakeFinding &&) {}

  // ---- values: inherited from TermOps

  // ---- control and properties
  // Which way does this branch go? Beyond the scheduled prefix, a feasible alternative is queued for later.
  bool decide(Val cond) {
    smt::TermRef b = tm_.toBool(cond);
    if (b->isConst()) return b->isTrue();
    if (setupRegion_) {  // see setSetupRegion: no fork, no schedule entry, one feasible direction
      smt::SatResult st = sat(b);
      if (st == smt::SatResult::Unknown) incomplete_ = true;
      bool dir = st != smt::SatResult::Unsat;
      if (!dir && sat(tm_.mkNot(b)) == smt::SatResult::Unsat) { dead_ = true; return false; }
      pc_.push_back(dir ? b : tm_.mkNot(b));
      return dir;
    }
    size_t idx = taken_.size();
    if (idx < schedule_.size()) {
      bool dir = schedule_[idx] != 0;
      taken_.push_back(dir);
      pc_.push_back(dir ? b : tm_.mkNot(b));
      return dir;
    }
    smt::SatResult st = sat(b), sf = sat(tm_.mkNot(b));
    if (st == smt::SatResult::Unknown || sf == smt::SatResult::Unknown) incomplete_ = true;
    bool canT = st != smt::SatResult::Unsat, canF = sf != smt::SatResult::Unsat;
    if (!canT && !canF) { dead_ = true; return false; }
    if (canT && canF && hooks_.onFork) {
      Schedule alt = taken_;
      alt.push_back(0);
      hooks_.onFork(alt);
    }
    bool dir = canT;
    taken_.push_back(dir);
    pc_.push_back(dir ? b : tm_.mkNot(b));
    return dir;
  }

  // True when the property can fail here (the path ends with it); false when it cannot, or when the path is narrowed
  // to the executions where it does not fail and goes on. A feasible failure is reported once, as a finding.
  template <class MakeFinding>
  bool violated(Val cond, MakeFinding &&mk) {
    if (dead_) return true;
    smt::TermRef b = tm_.toBool(cond);
    if (b->isFalse()) return false;
    smt::SatResult r = b->isTrue() ? smt::SatResult::Sat : sat(b);
    if (r == smt::SatResult::Unsat) return false;
    if (r == smt::SatResult::Unknown) { incomplete_ = true; return false; }
    if (taken_.size() >= schedule_.size()) report(mk(), b);  // earlier segments were reported when first executed
    if (b->isTrue() || sat(tm_.mkNot(b)) == smt::SatResult::Unsat) return true;
    pc_.push_back(tm_.mkNot(b));
    return false;
  }

  bool assume(Val cond) {
    if (dead_) return false;
    smt::TermRef b = tm_.toBool(cond);
    if (b->isTrue()) return true;
    if (b->isFalse() || sat(b) == smt::SatResult::Unsat) return false;
    pc_.push_back(b);
    return true;
  }

  // See TaintDomain::assumeConcretisation. The symbolic pass ENUMERATES paths instead of flipping one run's
  // branches, so there is no flip query to keep this out of; it is the same assumption here.
  bool assumeConcretisation(Val cond) { return assume(cond); }

  Val nondet(Env &, const Op &op, unsigned width) {
    std::string base = "nd";
    if (const Attr *n = op.attr("name")) base = n->s;
    smt::TermRef v = tm_.bvVar("nd." + base + "." + std::to_string(nondets_.size()), width);
    nondets_.push_back(v);
    vars_.push_back(v);
    return v;
  }

 public:
  // wall-clock budget: past it every query answers Unknown immediately (the path ends as incomplete, no solver is started)
  void setDeadline(std::chrono::steady_clock::time_point d) { deadline_ = d; }

 private:
  bool setupRegion_ = false;  // see setSetupRegion (DESIGN.md §22.442)
  std::chrono::steady_clock::time_point deadline_ = std::chrono::steady_clock::time_point::max();
  smt::SatResult sat(smt::TermRef extra) {
    if (std::chrono::steady_clock::now() >= deadline_) return smt::SatResult::Unknown;
    std::string key;
    for (auto *c : pc_) key += std::to_string(c->id) + ",";
    key += "|" + std::to_string(extra->id);
    auto it = cache_.map.find(key);
    if (it != cache_.map.end()) return it->second;
    ++queries_;
    std::vector<smt::TermRef> terms(pc_.begin(), pc_.end());
    terms.push_back(extra);
    limitSolver();
    smt::SatResult r = sol_.checkAssuming(terms);
    sol_.endCheckAssuming();
    cache_.map.emplace(std::move(key), r);
    return r;
  }

  void report(const Finding &f, smt::TermRef violation) {
    if (!hooks_.onFinding) return;
    if (std::chrono::steady_clock::now() >= deadline_) return;
    std::vector<smt::TermRef> terms(pc_.begin(), pc_.end());
    terms.push_back(violation);
    limitSolver();
    smt::Assignment asg;
    if (sol_.checkAssuming(terms) == smt::SatResult::Sat) {
      auto vals = sol_.values(vars_);
      for (size_t i = 0; i < vars_.size(); ++i) asg.emplace(vars_[i]->name, vals[i]);
      // content bytes of parameter objects read at symbolic offsets: ask the model for the index, then for the byte
      if (!inputReads_.empty()) {
        std::vector<smt::TermRef> idxs;
        for (auto &r : inputReads_) idxs.push_back(r.second);
        auto iv = sol_.values(idxs);
        std::vector<smt::TermRef> sel;
        for (size_t k = 0; k < inputReads_.size(); ++k)
          sel.push_back(tm_.mkSelect(tm_.arrVar("in.o" + std::to_string(inputReads_[k].first), iv[k].getBitWidth(), 8), tm_.bvConst(iv[k])));
        auto bv = sol_.values(sel);
        for (size_t k = 0; k < inputReads_.size(); ++k)
          asg.emplace("in.o" + std::to_string(inputReads_[k].first) + "+" + std::to_string(iv[k].getZExtValue()), bv[k]);
      }
    }
    sol_.endCheckAssuming();
    hooks_.onFinding(f, asg);
  }

  // a query never runs past the wall-clock budget
  void limitSolver() {
    if (deadline_ == std::chrono::steady_clock::time_point::max()) return;
    auto left = std::chrono::duration_cast<std::chrono::milliseconds>(deadline_ - std::chrono::steady_clock::now()).count();
    sol_.setTimeoutMs(left <= 50 ? 50u : static_cast<unsigned>(std::min<long long>(left, 10000)));
  }
  smt::Solver &sol_;
  QueryCache &cache_;
  Hooks hooks_;
  Schedule schedule_, taken_;
  std::vector<smt::TermRef> pc_, vars_, nondets_;
  bool incomplete_ = false, dead_ = false;
  uint64_t queries_ = 0;
  unsigned freshCount_ = 0;
  std::vector<std::pair<uint32_t, smt::TermRef>> inputReads_;
  bool boundInsufficient_ = false;
  std::string boundWhat_;
};

}  // namespace hlir

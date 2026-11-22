// Tests for taint-selective execution (P6):
//  1. DESIGN.md §20.10 scenario: validate (Observer) / log_stats (Inert) / alloc_buf / sink; the slice is tiny and
//     dropping the Observer's path constraint gives a wrong (unconfirmable) verdict
//  2. taint through memory: store / memcpy / load, kill by overwrite
//  3. real (concrete) UB needs no solver; entry harness + promotion of environment values
//  4. differential: taint-selective concolic == full symbolic on 200 random programs
//  5. scale: the slice does not grow with the amount of untainted code
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>

#include "hlir/entry/HarnessGen.h"
#include "hlir/entry/SeedSolver.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/ReachTarget.h"
#include "hlir/semantics/Symbolic.h"
#include "hlir/semantics/Taint.h"
#include "hlir/semantics/WriteSiteReach.h"
#include "hlir/semantics/WriteSites.h"

using namespace hlir;
using llvm::APInt;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }
static std::unique_ptr<smt::Solver> g_z3;

static std::unique_ptr<Module> load(const std::string &text, const std::string &name) {
  Diagnostics d;
  auto m = parseModule(text, name, d);
  if (!m || d.hasErrors() || !verifyModule(*m, {}, d)) { std::cerr << "cannot load " << name << ":\n" << d.str() << "\n"; std::exit(2); }
  return m;
}

static std::set<std::string> kinds(const TaintResult &r, bool onlyConfirmed = false) {
  std::set<std::string> s;
  for (auto &f : r.findings) {
    if (f.ub && ubKindIsWarning(f.ub->kind)) continue;  // UB / sink findings only; DoS warnings are checked separately
    if (!onlyConfirmed || (f.confirmed && *f.confirmed)) s.insert(f.ub ? ubKindName(f.ub->kind) : "assert");
  }
  return s;
}

// ---------------------------------------------------------------- 1. §20.10
static std::string scenario(const char *validateBody) {
  return std::string(validateBody) + R"(
core.func @log_stats() -> void {
^entry:
  %g = core.global_addr @counter {size=4} : ptr
  %v = core.load %g : i32
  %one = core.const 1 : i32
  %n = core.add %v, %one : i32
  core.store %n, %g
  core.return
}
core.func @alloc_buf() -> ptr {
^entry:
  %n = core.const 256 : i64
  %p = core.heap_alloc %n {fail=never} : ptr
  core.return %p
}
core.func @recv32(ptr) -> void {
^entry(%p: ptr):
  %v = core.nondet {name="recv", taint="network"} : i32
  core.store %v, %p
  core.return
}
core.func @handle() -> i32 {
^entry:
  %slot = core.alloca {size=4, align=4} : ptr
  core.call @recv32(%slot)
  %len = core.load %slot : i32
  core.call @log_stats()
  %r = core.call @validate(%len) : i32
  %zero = core.const 0 : i32
  %rej = core.icmp slt %r, %zero : bool
  core.cond_br %rej, ^out, ^go
^out:
  core.return %r
^go:
  %buf = core.call @alloc_buf() : ptr
  %n = core.sext %len : i64
  core.check.ptr_arith %buf, %n {origin="memcpy n"} loc("net.c":35:5)
  core.return %zero
}
)";
}

static const char *kValidate = R"(
core.func @validate(i32) -> i32 {
^entry(%len: i32):
  %max = core.const 512 : i32
  %big = core.icmp sgt %len, %max : bool
  core.cond_br %big, ^rej, ^ok
^rej:
  %m1 = core.const -1 : i32
  core.return %m1
^ok:
  %z = core.const 0 : i32
  core.return %z
}
)";

// stricter: rejects negative lengths too, so the sink is safe
static const char *kValidateStrict = R"(
core.func @validate(i32) -> i32 {
^entry(%len: i32):
  %max = core.const 100 : i32
  %zero = core.const 0 : i32
  %big = core.icmp sgt %len, %max : bool
  %neg = core.icmp slt %len, %zero : bool
  %bad = core.or %big, %neg : bool
  core.cond_br %bad, ^rej, ^ok
^rej:
  %m1 = core.const -1 : i32
  core.return %m1
^ok:
  core.return %zero
}
)";

static const FunctionTaintClass *classOf(const TaintResult &r, const std::string &fn) {
  for (auto &c : r.functions)
    if (c.function == fn) return &c;
  return nullptr;
}

static void testScenario() {
  auto m = load(scenario(kValidate), "scenario");
  smt::TermManager tm;
  TaintExecutor ex(*m, tm, *g_z3);
  TaintResult r = ex.run("handle", {});
  CHECK(r.complete && !r.runs.empty(), "scenario runs to completion: " << r.note);
  const SliceStats &s = r.runs[0].slice;
  CHECK(s.sources == 1, "one symbolic input (the recv'd length), got " << s.sources);
  CHECK(s.flippableBranches == 1, "one tainted branch (validate's), got " << s.flippableBranches);
  CHECK(s.queries == 1, "one query site");
  CHECK(s.taintedOps <= 6, "only a handful of ops touch tainted data, got " << s.taintedOps << " of " << s.steps << " executed");
  CHECK(s.steps > 3 * s.taintedOps, "most executed ops never reached the solver");
  bool has256 = false;
  for (auto &e : r.runs[0].envFacts) has256 |= e.value.getBitWidth() == 64 && e.value == 256 && e.op == "core.check.ptr_arith";
  CHECK(has256, "the object size 256 is recorded as an environment fact of the query");
  CHECK((kinds(r, true) == std::set<std::string>{"ptr_arith_oob"}), "the sign-extension bug is found and replay-confirmed");
  CHECK(!r.findings.empty() && r.findings[0].nondets.size() == 1 && (r.findings[0].nondets[0].isNegative() || r.findings[0].nondets[0].ugt(256)), "witness: a length the buffer cannot hold passes validate");
  auto *v = classOf(r, "validate"), *l = classOf(r, "log_stats"), *rv = classOf(r, "recv32");
  CHECK(v && v->observer == v->calls && v->calls > 0, "validate is an Observer: reads taint, nothing flows out");
  CHECK(l && l->inert == l->calls && l->calls > 0, "log_stats is Inert");
  CHECK(rv && rv->source == rv->calls, "recv32 is a Source");
  CHECK(r.termsSolved < 40, "the SMT terms sent to the solver are few: " << r.termsSolved);

  // Regression: the Observer's path constraint is essential. With a validate that rejects negative lengths, the sink is
  // safe; forgetting validate's constraint (the "ΔT = ∅ means irrelevant" mistake) yields a spurious, unconfirmable finding.
  auto strict = load(scenario(kValidateStrict), "strict");
  smt::TermManager tm2;
  TaintExecutor ex2(*strict, tm2, *g_z3);
  TaintResult ok = ex2.run("handle", {});
  CHECK(ok.complete && ok.findings.empty(), "strict validate: no findings");
  TaintConfig drop;
  drop.dropPcsAboveDepth = 1;
  TaintResult wrong = ex2.run("handle", {}, drop);
  CHECK(!wrong.findings.empty() && wrong.findings[0].confirmed && !*wrong.findings[0].confirmed,
        "dropping the Observer's constraints produces a false positive that replay refutes");
}

// ---------------------------------------------------------------- 2. memory taint
static void testMemory() {
  const char *text = R"(
core.func @through_memcpy() -> i32 {
^entry:
  %a = core.alloca {size=8} : ptr
  %b = core.alloca {size=8} : ptr
  %t = core.nondet {name="t", taint="x"} : i8
  core.store %t, %a
  %eight = core.const 8 : i64
  core.memcpy %b, %a, %eight
  %v = core.load %b : i8
  %idx = core.zext %v : i64
  %buf = core.alloca {size=4} : ptr
  %q = core.ptr_add %buf, %idx : ptr
  core.check.oob %q {w=1, access="w"} loc("m.c":9:3)
  %z = core.const 0 : i32
  core.return %z
}
core.func @overwritten() -> i32 {
^entry:
  %a = core.alloca {size=8} : ptr
  %b = core.alloca {size=8} : ptr
  %t = core.nondet {name="t", taint="x"} : i8
  core.store %t, %a
  %c = core.const 1 : i8
  core.store %c, %a
  %eight = core.const 8 : i64
  core.memcpy %b, %a, %eight
  %v = core.load %b : i8
  %idx = core.zext %v : i64
  %buf = core.alloca {size=4} : ptr
  %q = core.ptr_add %buf, %idx : ptr
  core.check.oob %q {w=1, access="w"} loc("m.c":20:3)
  %z = core.const 0 : i32
  core.return %z
}
core.func @concrete_ub() -> i32 {
^entry:
  %a = core.const 5 : i32
  %z = core.const 0 : i32
  core.check.div %a, %z loc("c.c":3:3)
  %q = core.udiv %a, %z : i32
  core.return %q
}
)";
  auto m = load(text, "mem");
  smt::TermManager tm;
  TaintExecutor ex(*m, tm, *g_z3);
  TaintResult r = ex.run("through_memcpy", {});
  CHECK(r.complete && r.runs[0].slice.queries == 1, "taint survives store -> memcpy -> load: the check becomes a query");
  CHECK((kinds(r, true) == std::set<std::string>{"oob_write"}), "tainted index found out of bounds (value 4..255), replay confirmed");
  if (!r.findings.empty()) CHECK(r.findings[0].nondets[0].getZExtValue() >= 4, "witness index is >= 4");
  TaintResult o = ex.run("overwritten", {});
  CHECK(o.complete && o.runs[0].slice.queries == 0 && o.findings.empty(), "overwriting a tainted byte with a constant kills the taint: no query, no finding");
  TaintResult c = ex.run("concrete_ub", {});
  CHECK(c.solverQueries == 0 && (kinds(c, true) == std::set<std::string>{"div_by_zero"}), "UB on untainted data is found concretely, without the solver");
}

// ---------------------------------------------------------------- 3. entry harness, promotion
static void testEntry() {
  std::string core = slurp(HLIR_ENTRY_DIR "/copy_if_small.core") + "\n" + slurp(HLIR_MODELS_DIR "/libc.core");
  std::string yaml = slurp(HLIR_ENTRY_DIR "/copy_if_small.yaml");
  auto run = [&](const std::string &spec, const TaintConfig &cfg, bool useSymbolic, std::set<std::string> *out) {
    Diagnostics d;
    entry::EntryFile ef;
    CHECK(entry::parseEntrySpec(spec, "s.yaml", ef, d), d.str());
    auto m0 = parseModule(core, "c", d);
    smt::TermManager tm;
    entry::InitPlan plan;
    CHECK(entry::buildInitPlan(*m0, ef, *ef.find("copy_if_small"), tm, plan, d), d.str());
    entry::SeedSolver ss(tm, *g_z3, plan);
    entry::Seed seed = ss.benign();
    CHECK(seed.result == smt::SatResult::Sat, "M0 exists");
    auto full = parseModule(core + "\n" + entry::generateHarness(plan), "full", d);
    CHECK(full && verifyModule(*full, {}, d), d.str());
    smt::TermManager tm2;
    if (useSymbolic) {
      SymbolicExecutor sx(*full, tm2, *g_z3);
      SymResult sr = sx.run(entry::harnessName(plan), {}, {});
      for (auto &f : sr.findings) out->insert(f.ub ? ubKindName(f.ub->kind) : "assert");
      return;
    }
    TaintExecutor ex(*full, tm2, *g_z3);
    TaintResult tr = ex.run(entry::harnessName(plan), std::map<std::string, APInt>(seed.model.begin(), seed.model.end()), cfg);
    CHECK(tr.complete, "complete: " << tr.note);
    *out = kinds(tr, true);
    for (auto &f : tr.findings) CHECK(f.confirmed && *f.confirmed, "every finding is confirmed by replay");
  };
  std::set<std::string> contract, contractSym;
  run(yaml, {}, false, &contract);
  run(yaml, {}, true, &contractSym);
  CHECK((contract == std::set<std::string>{"oob_write"}), "contract mode (taint): only the sign-extension overflow");
  CHECK(contract == contractSym, "taint-selective and full symbolic agree on the entry harness");

  std::string hostile = yaml.substr(0, yaml.find("    relations:"));
  std::set<std::string> hostileDefault, hostilePromoted, hostileSym;
  run(hostile, {}, false, &hostileDefault);
  TaintConfig promo;
  promo.promote.insert("size.src");
  run(hostile, promo, false, &hostilePromoted);
  run(hostile, {}, true, &hostileSym);
  CHECK((hostileDefault == std::set<std::string>{"oob_write", "oob_read"}), "hostile mode: the over-read of src is found even with size(src) concretised to the seed's 64");
  CHECK(hostilePromoted == hostileDefault, "promoting size(src) to a symbolic input changes nothing here");
  CHECK(hostilePromoted == hostileSym, "... and matches the full symbolic engine");
}

// ---------------------------------------------------------------- 4. differential on random programs
struct Gen {
  std::mt19937_64 rng;
  std::vector<std::string> blocks;  // text of each finished block
  std::string cur;                  // text of the open block
  std::string curLabel;
  std::vector<std::string> vals;
  int n = 0, line = 100, lbl = 0;

  explicit Gen(uint64_t seed) : rng(seed) {}
  uint64_t r(uint64_t k) { return rng() % k; }
  std::string fresh() { return "%v" + std::to_string(n++); }
  void emit(const std::string &s) { cur += "  " + s + "\n"; }
  std::string loc() { return " loc(\"r.c\":" + std::to_string(line++) + ":1)"; }
  std::string pick() { return vals[r(vals.size())]; }
  std::string constant() {
    static const int64_t cs[] = {0, 1, -1, 2, 7, 8, 31, 32, 100, 255, 256, 1000, 2147483647LL, -2147483648LL};
    std::string c = fresh();
    emit(c + " = core.const " + std::to_string(cs[r(14)]) + " : i32");
    return c;
  }
  std::string operand() { return r(3) == 0 ? constant() : pick(); }
  void open(const std::string &label, const std::string &args) { curLabel = label; cur = "^" + label + args + ":\n"; }
  void close(const std::string &term) { cur += "  " + term + "\n"; blocks.push_back(cur); cur.clear(); }

  void stmt(int depth) {
    switch (r(depth > 0 ? 10 : 9)) {
      case 0: case 1: {
        static const char *ops[] = {"add", "sub", "mul", "and", "or", "xor"};
        std::string a = operand(), b = operand(), v = fresh();
        emit(v + " = core." + ops[r(6)] + " " + a + ", " + b + " : i32");
        vals.push_back(v);
        break;
      }
      case 2: {  // division with its UB check
        std::string a = operand(), b = operand(), v = fresh();
        bool rem = r(2);
        emit("core.check.div " + a + ", " + b + " {signed}" + loc());
        emit(v + " = core." + (rem ? "srem " : "sdiv ") + a + ", " + b + " : i32");
        vals.push_back(v);
        break;
      }
      case 3: {  // shift
        std::string a = operand(), b = operand(), v = fresh();
        bool left = r(2);
        emit("core.check.shift " + a + ", " + b + (left ? " {signed_left}" : "") + loc());
        emit(v + " = core." + (left ? "shl " : "ashr ") + a + ", " + b + " : i32");
        vals.push_back(v);
        break;
      }
      case 4: {  // checked signed add / mul
        std::string a = operand(), b = operand(), v = fresh();
        bool mul = r(2);
        emit(std::string("core.check.") + (mul ? "smul_ovf " : "sadd_ovf ") + a + ", " + b + loc());
        emit(v + " = core." + (mul ? "mul " : "add ") + a + ", " + b + " {sov} : i32");
        vals.push_back(v);
        break;
      }
      case 5: {  // compare + select
        static const char *preds[] = {"eq", "ne", "slt", "sle", "sgt", "ult", "uge"};
        std::string a = operand(), b = operand(), c = fresh(), v = fresh(), x = operand(), y = operand();
        emit(c + " = core.icmp " + preds[r(7)] + " " + a + ", " + b + " : bool");
        emit(v + " = core.select " + c + ", " + x + ", " + y + " : i32");
        vals.push_back(v);
        break;
      }
      case 6: {  // assertion
        static const char *preds[] = {"slt", "sge", "ne", "ule"};
        std::string a = operand(), b = operand(), c = fresh();
        emit(c + " = core.icmp " + preds[r(4)] + " " + a + ", " + b + " : bool");
        emit("core.assert " + c + " {msg=\"assertion\"}" + loc());
        break;
      }
      case 7: {  // buffer write at an unchecked index
        std::string buf = fresh(), m = fresh(), i = fresh(), q = fresh(), b = fresh(), x = pick();
        emit(m + " = core.const " + std::to_string(r(2) ? 7 : 15) + " : i32");
        std::string masked = fresh();
        emit(masked + " = core.and " + x + ", " + m + " : i32");
        emit(buf + " = core.alloca {size=8} : ptr");
        emit(i + " = core.zext " + masked + " : i64");
        emit(q + " = core.ptr_add " + buf + ", " + i + " : ptr");
        emit("core.check.oob " + q + " {w=1, access=\"w\"}" + loc());
        emit(b + " = core.trunc " + x + " : i8");
        emit("core.store " + b + ", " + q);
        break;
      }
      case 8: {  // helper calls: an Observer and an Inert one
        std::string v = fresh();
        if (r(2)) emit(v + " = core.call @obs(" + pick() + ") : i32");
        else emit(v + " = core.call @inert(" + constant() + ") : i32");
        vals.push_back(v);
        break;
      }
      default: {  // if / else with a join value
        int id = lbl++;
        std::string c = fresh(), a = operand(), b = operand();
        static const char *preds[] = {"slt", "eq", "ugt", "sge"};
        emit(c + " = core.icmp " + preds[r(4)] + " " + a + ", " + b + " : bool");
        std::string T = "t" + std::to_string(id), E = "e" + std::to_string(id), J = "j" + std::to_string(id);
        close("core.cond_br " + c + ", ^" + T + ", ^" + E);
        auto saved = vals;
        std::string tv, ev;
        open(T, "");
        for (int k = 0, e = 1 + static_cast<int>(r(3)); k < e; ++k) stmt(depth - 1);
        tv = pick();
        close("core.br ^" + J + "(" + tv + ")");
        vals = saved;
        open(E, "");
        for (int k = 0, e = 1 + static_cast<int>(r(3)); k < e; ++k) stmt(depth - 1);
        ev = pick();
        close("core.br ^" + J + "(" + ev + ")");
        vals = saved;
        std::string jv = "%j" + std::to_string(id) + "v";
        open(J, "(" + jv + ": i32)");
        vals.push_back(jv);
        break;
      }
    }
  }

  std::string program() {
    std::string out =
        "core.func @obs(i32) -> i32 {\n^entry(%x: i32):\n  %m = core.const 100 : i32\n  %c = core.icmp sgt %x, %m : bool\n  core.cond_br %c, ^big, ^small\n"
        "^big:\n  %one = core.const 1 : i32\n  core.return %one\n^small:\n  %zero = core.const 0 : i32\n  core.return %zero\n}\n"
        "core.func @inert(i32) -> i32 {\n^entry(%x: i32):\n  %one = core.const 1 : i32\n  %r = core.add %x, %one : i32\n  core.return %r\n}\n";
    open("entry", "(%a: i32, %b: i32)");
    vals = {"%a", "%b"};
    for (int k = 0, e = 2 + static_cast<int>(r(4)); k < e; ++k) stmt(2);
    std::string res = pick();
    close("core.return " + res);
    out += "core.func @f(i32, i32) -> i32 {\n";
    for (auto &b : blocks) out += b;
    out += "}\n";
    return out;
  }
};

static void testDifferential() {
  int programs = 0, withFindings = 0, total = 0, skipped = 0;
  double symSec = 0, taintSec = 0;
  auto solver = smt::makeZ3ProcessSolver("z3", 2000);  // nonlinear 32-bit queries may time out: such programs are skipped
  const int want = getenv("HLIR_DIFF_N") ? atoi(getenv("HLIR_DIFF_N")) : 200;
  for (uint64_t seed = 1; programs < want && seed < 3000; ++seed) {
    if (getenv("HLIR_DIFF_VERBOSE")) std::cerr << "program " << seed << " (done " << programs << ", skipped " << skipped << ")\n";
    Gen g(seed);
    std::string prog = g.program();
    Diagnostics d;
    auto m = parseModule(prog, "gen", d);
    if (!m || d.hasErrors() || !verifyModule(*m, {}, d)) { CHECK(false, "generated program " << seed << " does not verify:\n" << d.str() << prog); continue; }
    ++programs;
    std::string harness =
        "core.func @h() -> i32 {\n^entry:\n  %a = core.nondet {name=\"a\", taint=\"t\"} : i32\n  %b = core.nondet {name=\"b\", taint=\"t\"} : i32\n"
        "  %r = core.call @f(%a, %b) : i32\n  core.return %r\n}\n";
    auto full = load(prog + harness, "gen+h");

    smt::TermManager tmS, tmT;
    SymbolicExecutor sx(*m, tmS, *solver);
    SymConfig sc;
    sc.maxPaths = 2000;
    auto t0 = std::chrono::steady_clock::now();
    SymResult sr = sx.run("f", {}, sc);
    auto t1 = std::chrono::steady_clock::now();
    TaintExecutor tx(*full, tmT, *solver);
    TaintConfig tc;
    tc.maxRuns = 2000;
    TaintResult tr = tx.run("h", {}, tc);
    auto t2 = std::chrono::steady_clock::now();
    symSec += std::chrono::duration<double>(t1 - t0).count();
    taintSec += std::chrono::duration<double>(t2 - t1).count();

    auto key = [](const Loc &l, const std::string &k) { return std::to_string(l.line) + ":" + k; };
    std::set<std::string> a, b;
    for (auto &f : sr.findings) a.insert(key(f.loc, f.ub ? ubKindName(f.ub->kind) : "assert"));
    for (auto &f : tr.findings) {
      b.insert(key(f.loc, f.ub ? ubKindName(f.ub->kind) : "assert"));
      CHECK(f.confirmed && *f.confirmed, "program " << seed << ": taint finding not confirmed");
    }
    if (!sr.complete || !tr.complete) { ++skipped; --programs; continue; }
    bool same = a == b;
    CHECK(same, "program " << seed << ": verdicts differ (symbolic " << a.size() << " vs taint " << b.size() << ")");
    if (!same && g_fail < 6) {
      for (auto &x : a) if (!b.count(x)) std::cerr << "  only symbolic: " << x << "\n";
      for (auto &x : b) if (!a.count(x)) std::cerr << "  only taint: " << x << "\n";
      std::cerr << prog;
    }
    withFindings += !a.empty();
    total += static_cast<int>(a.size());
  }
  CHECK(skipped < 60, "too many programs hit the solver timeout: " << skipped);
  std::cout << "  (symbolic " << symSec << "s, taint " << taintSec << "s)\n";
  std::cout << "  differential: " << programs << " programs (" << skipped << " skipped on solver timeouts), " << withFindings << " with findings, " << total << " finding sites compared\n";
  CHECK(withFindings > programs / 4, "the random programs actually exercise bugs (" << withFindings << ")");
}

// ---------------------------------------------------------------- 5. scale
static std::string bigProgram(int n) {
  std::string body = "core.func @big(i32) -> i32 {\n^entry(%x: i32):\n";
  std::string prev = "%x";
  for (int i = 0; i < n; ++i) {
    body += "  %c" + std::to_string(i) + " = core.const " + std::to_string(i % 7 + 1) + " : i32\n";
    body += "  %u" + std::to_string(i) + " = core.add %c" + std::to_string(i) + ", %c" + std::to_string(i) + " : i32\n";
  }
  body += "  core.return %x\n}\n";
  return body;
}

static void testScale() {
  auto measure = [&](int n, SliceStats &s, uint64_t &terms) {
    std::string prog = bigProgram(n) + R"(
core.func @h() -> i32 {
^entry:
  %t = core.nondet {name="len", taint="net"} : i32
  %pad = core.const 3 : i32
  %u = core.call @big(%pad) : i32
  %max = core.const 512 : i32
  %big = core.icmp sgt %t, %max : bool
  core.cond_br %big, ^rej, ^go
^rej:
  core.return %max
^go:
  %buf = core.alloca {size=64} : ptr
  %n = core.sext %t : i64
  core.check.ptr_arith %buf, %n loc("s.c":1:1)
  core.return %u
}
)";
    auto m = load(prog, "scale");
    smt::TermManager tm;
    TaintExecutor ex(*m, tm, *g_z3);
    TaintResult r = ex.run("h", {});
    CHECK(r.complete && !r.runs.empty(), "scale run");
    s = r.runs[0].slice;
    terms = r.termsSolved;
    CHECK(!r.findings.empty() && r.findings[0].confirmed && *r.findings[0].confirmed, "the bug is found regardless of the amount of unrelated code");
  };
  SliceStats a, b;
  uint64_t ta = 0, tb = 0;
  measure(50, a, ta);
  measure(5000, b, tb);
  CHECK(b.steps > 10000 && a.steps < 500, "the big program really executes thousands of ops (" << a.steps << " vs " << b.steps << ")");
  CHECK(a.taintedOps == b.taintedOps && a.pcs == b.pcs && a.queries == b.queries && a.sources == b.sources && a.envFacts == b.envFacts,
        "slice size does not depend on the amount of untainted code");
  CHECK(ta == tb, "neither do the SMT terms sent to the solver (" << ta << " vs " << tb << ")");
  std::cout << "  scale: " << b.steps << " ops executed -> " << b.taintedOps << " tainted ops, " << b.pcs << " constraints, " << tb << " solver terms\n";
}

// ---------------------------------------------------------------- 6. TaintConfig::reachTarget (target-guided search)
// computeTargetDistance in isolation: a small hand-built call graph, `root -> {mid, side}`, `mid -> deep`, `side` is a
// dead end. Distances to `deep` should be 0/1/2, `side` and an unrelated function get the sentinel.
static void testReachTargetDistance() {
  const char *prog = R"(
core.func @deep() -> void {
^entry:
  core.return
}
core.func @mid() -> void {
^entry:
  core.call @deep()
  core.return
}
core.func @side() -> void {
^entry:
  core.return
}
core.func @unrelated() -> void {
^entry:
  core.return
}
core.func @root() -> void {
^entry:
  core.call @mid()
  core.call @side()
  core.return
}
)";
  auto m = load(prog, "dist");
  auto dist = computeTargetDistance(*m, "root", "deep");
  CHECK(dist.count("deep") && dist.at("deep") == 0, "target itself is distance 0");
  CHECK(dist.count("mid") && dist.at("mid") == 1, "deep's only caller is distance 1, got " << (dist.count("mid") ? dist.at("mid") : -1));
  CHECK(dist.count("root") && dist.at("root") == 2, "root reaches deep only through mid, distance 2, got " << (dist.count("root") ? dist.at("root") : -1));
  CHECK(dist.count("side") && dist.at("side") == kUnreachableTargetDistance, "side never calls deep: sentinel distance");
  CHECK(!dist.count("unrelated"), "unrelated is not forward-reachable from root at all: absent, not just sentinel");
  // An unknown target name: every reachable function still gets the sentinel (no crash, no false proximity).
  auto bad = computeTargetDistance(*m, "root", "does_not_exist");
  CHECK(bad.count("root") && bad.at("root") == kUnreachableTargetDistance, "unknown target: sentinel for everything reachable");
}

// A noise-vs-target differential: `chain_entry` calls `noise` (kNoiseBranches independent tainted branches, on
// variables named distinctly from the target's, none of which call anywhere near `target`) and then `near`, which
// calls `target` (one tainted branch gated by a value > 100, hiding an `core.assert` bug on the far side). After the
// first run, every branch registers as an equally "fresh" flip candidate; ties break by the order constraints were
// recorded on that one straight-line path (noise's branches first, target's last) -- so with a small run budget and
// no target, the frontier exhausts itself on noise and never reaches target's branch. `--reach-target target` should
// instead put target's branch (distance 0) ahead of noise's (unreachable: noise never calls target), reaching the bug
// almost immediately within the same budget.
static std::string reachTargetProgram(int noiseBranches) {
  std::string noise = "core.func @noise() -> void {\n^entry:\n  core.br ^n0\n";
  for (int i = 0; i < noiseBranches; ++i) {
    std::string cur = "n" + std::to_string(i), next = i + 1 == noiseBranches ? "done" : "n" + std::to_string(i + 1);
    noise += "^" + cur + ":\n  %v" + std::to_string(i) + " = core.nondet {name=\"noise" + std::to_string(i) + "\", taint=\"t\"} : i32\n";
    noise += "  %c" + std::to_string(i) + " = core.const 10 : i32\n";
    noise += "  %b" + std::to_string(i) + " = core.icmp sgt %v" + std::to_string(i) + ", %c" + std::to_string(i) + " : bool\n";
    noise += "  core.cond_br %b" + std::to_string(i) + ", ^" + cur + "t, ^" + cur + "f\n";
    noise += "^" + cur + "t:\n  core.br ^" + next + "\n^" + cur + "f:\n  core.br ^" + next + "\n";
  }
  noise += "^done:\n  core.return\n}\n";
  return noise + R"(
core.func @target(i32) -> void {
^entry(%z: i32):
  %max = core.const 100 : i32
  %big = core.icmp sgt %z, %max : bool
  core.cond_br %big, ^bug, ^safe
^bug:
  %bz = core.const 0 : i32
  %bo = core.const 1 : i32
  %f = core.icmp eq %bz, %bo : bool
  core.assert %f {msg="target bug"}
  core.return
^safe:
  core.return
}
core.func @near(i32) -> void {
^entry(%y: i32):
  core.call @target(%y)
  core.return
}
core.func @chain_entry() -> void {
^entry:
  core.call @noise()
  %tseed = core.nondet {name="targetseed", taint="t"} : i32
  core.call @near(%tseed)
  core.return
}
)";
}

static void testReachTargetSearch() {
  constexpr int kNoiseBranches = 15;
  constexpr unsigned kMaxRuns = 10;  // enough to work through several noise branches, not all 15 plus target's
  auto m = load(reachTargetProgram(kNoiseBranches), "reach");

  smt::TermManager tm1;
  TaintExecutor exDefault(*m, tm1, *g_z3);
  TaintConfig cfgDefault;
  cfgDefault.maxRuns = kMaxRuns;
  TaintResult rDefault = exDefault.run("chain_entry", {}, cfgDefault);
  CHECK(kinds(rDefault, true) != std::set<std::string>{"assert"}, "default coverage-guided order: " << kNoiseBranches
        << " noise branches outrank target's single branch (lower seq, same freshness), so the budget runs out before target is reached -- no confirmed bug, got " << rDefault.findings.size() << " findings");

  smt::TermManager tm2;
  TaintExecutor exGuided(*m, tm2, *g_z3);
  TaintConfig cfgGuided;
  cfgGuided.maxRuns = kMaxRuns;
  cfgGuided.reachTarget = "target";
  TaintResult rGuided = exGuided.run("chain_entry", {}, cfgGuided);
  CHECK((kinds(rGuided, true) == std::set<std::string>{"assert"}), "--reach-target target: target's branch (distance 0) is dequeued ahead of noise's (unreachable from target, sentinel distance), finding the bug well inside the same run budget");

  // The empty-string default and a default-constructed TaintConfig must be indistinguishable: same maxRuns, one with
  // reachTarget left at its default, one with it explicitly set to "" -- every pre-existing caller (which never
  // mentions reachTarget) gets the former, so this is the actual no-regression invariant.
  smt::TermManager tm3;
  TaintExecutor exImplicit(*m, tm3, *g_z3);
  TaintResult rImplicit = exImplicit.run("chain_entry", {}, cfgDefault);  // reachTarget left at TaintConfig's own default
  smt::TermManager tm4;
  TaintExecutor exExplicit(*m, tm4, *g_z3);
  TaintConfig cfgExplicitEmpty = cfgDefault;
  cfgExplicitEmpty.reachTarget = "";
  TaintResult rExplicit = exExplicit.run("chain_entry", {}, cfgExplicitEmpty);
  CHECK(rImplicit.runs.size() == rExplicit.runs.size() && kinds(rImplicit, true) == kinds(rExplicit, true),
        "an explicitly empty reachTarget behaves identically to leaving it at its default (same run count, same findings)");
}

// ---------------------------------------------------------------- 7. buildConeIndex/collectVars scale (DESIGN.md
// Sec.22.294/296): a single run of N chained tainted branches, each gated on an accumulator that is itself built
// by nesting one more core.add on top of the previous block's accumulator (%accn_i = %acc_i + %s_i). This mirrors
// the real-world pattern found in SQLite's sqlite3VListNumToName (a do-while loop whose per-step advance is tainted
// and can be 0, so a single taint-concolic run unrolls very deep): the path condition at step i embeds the whole
// i-deep accumulator term, and successive steps' terms overlap almost completely. Before the fix, buildConeIndex
// re-walked each pcTerm's reachable subgraph from scratch (no cross-call node cache), so total cost grew with the
// square of the path length; the fix (collectVarsMemo) memoizes every node visited, shared across all N pcTerms of
// the run, turning it into roughly linear cost. With maxRuns=1 only the single seed run executes (no branch
// flipping), isolating buildConeIndex's own cost from solver-query cost.
static std::string coneChainProgram(int n) {
  std::string p = "core.func @cone_chain() -> void {\n^entry:\n  %z0 = core.const 0 : i32\n  core.br ^b0(%z0)\n";
  for (int i = 0; i < n; ++i) {
    std::string cur = "b" + std::to_string(i);
    std::string next = (i + 1 == n) ? "done" : ("b" + std::to_string(i + 1));
    p += "^" + cur + "(%acc" + std::to_string(i) + ": i32):\n";
    p += "  %s" + std::to_string(i) + " = core.nondet {name=\"s" + std::to_string(i) + "\", taint=\"t\"} : i32\n";
    p += "  %accn" + std::to_string(i) + " = core.add %acc" + std::to_string(i) + ", %s" + std::to_string(i) + " : i32\n";
    p += "  %lim" + std::to_string(i) + " = core.const 1000000000 : i32\n";
    p += "  %cmp" + std::to_string(i) + " = core.icmp slt %accn" + std::to_string(i) + ", %lim" + std::to_string(i) + " : bool\n";
    p += "  core.cond_br %cmp" + std::to_string(i) + ", ^t" + std::to_string(i) + ", ^f" + std::to_string(i) + "\n";
    p += "^t" + std::to_string(i) + ":\n  core.br ^" + next + "(%accn" + std::to_string(i) + ")\n";
    p += "^f" + std::to_string(i) + ":\n  core.return\n";
  }
  p += "^done(%accD: i32):\n  core.return\n}\n";
  return p;
}

static double measureConeChain(int n) {
  auto m = load(coneChainProgram(n), "cone_chain");
  smt::TermManager tm;
  TaintExecutor ex(*m, tm, *g_z3);
  TaintConfig cfg;
  cfg.maxRuns = 1;  // isolate the single deep run's own buildConeIndex cost from any branch-flip/solver-query cost
  auto t0 = std::chrono::steady_clock::now();
  TaintResult r = ex.run("cone_chain", {}, cfg);
  auto t1 = std::chrono::steady_clock::now();
  CHECK(!r.runs.empty(), "cone_chain run executes for n=" << n);
  return std::chrono::duration<double>(t1 - t0).count();
}

static void testConeIndexScale() {
  // A coarse regression tripwire, not a precise complexity proof: this harness's own per-step bookkeeping
  // (interpreter stepping, frontier generation for every flippable branch) adds its own cost on top of
  // buildConeIndex/collectVars, so the clean O(path^2)-vs-O(path) separation only shows unambiguously on a much
  // deeper, real workload. The actual before/after evidence for this fix is the real SQLite case captured with gdb
  // in docs/DESIGN.md Sec.22.294/296 (buildConeIndex measurably the sole bottleneck there, 0 solver queries reached
  // in 60-120s before the fix, same case completing well inside budget after). Here we just check that a few
  // thousand chained tainted branches in one run complete quickly, to catch a gross regression (e.g. an accidental
  // revert back to re-walking each path condition's reachable subgraph from scratch).
  double t = measureConeChain(4000);
  std::cout << "  cone index scale: n=4000 chained tainted branches (one run) in " << t << "s\n";
  CHECK(t < 10.0, "4000 chained tainted branches in a single run complete in well under 10s: took " << t << "s");
}

// §3.3b step 2 (docs/LLM_ASSISTED_TRIAGE_DESIGN.md, docs/DESIGN.md Sec.22.330): the write-site CANDIDATE
// (`helper`'s store of a tainted value at `%p+4`) is behind `noiseBranches` worth of coverage-order noise in
// `chain_entry`, same shape as testReachTargetSearch's program -- except the target here isn't a hand-written
// `core.assert`, it's one `findWriteSites()` found and `reachWriteSite()` injected itself.
static std::string writeSiteReachProgram(int noiseBranches) {
  std::string noise = "core.func @noise() -> void {\n^entry:\n  core.br ^n0\n";
  for (int i = 0; i < noiseBranches; ++i) {
    std::string cur = "n" + std::to_string(i), next = i + 1 == noiseBranches ? "done" : "n" + std::to_string(i + 1);
    noise += "^" + cur + ":\n  %v" + std::to_string(i) + " = core.nondet {name=\"noise" + std::to_string(i) + "\", taint=\"t\"} : i32\n";
    noise += "  %c" + std::to_string(i) + " = core.const 10 : i32\n";
    noise += "  %b" + std::to_string(i) + " = core.icmp sgt %v" + std::to_string(i) + ", %c" + std::to_string(i) + " : bool\n";
    noise += "  core.cond_br %b" + std::to_string(i) + ", ^" + cur + "t, ^" + cur + "f\n";
    noise += "^" + cur + "t:\n  core.br ^" + next + "\n^" + cur + "f:\n  core.br ^" + next + "\n";
  }
  noise += "^done:\n  core.return\n}\n";
  return noise + R"(
core.func @helper(ptr) -> void {
^entry(%p: ptr):
  %val = core.nondet {name="val", taint="t"} : i32
  %off = core.const 4 : i64
  %addr = core.ptr_add %p, %off : ptr
  core.store %val, %addr
  core.return
}
core.func @near(ptr) -> void {
^entry(%s: ptr):
  %sel = core.nondet {name="sel", taint="t"} : i32
  %hundred = core.const 100 : i32
  %big = core.icmp sgt %sel, %hundred : bool
  core.cond_br %big, ^callit, ^skip
^callit:
  core.call @helper(%s)
  core.return
^skip:
  core.return
}
core.func @chain_entry() -> void {
^entry:
  core.call @noise()
  %s = core.alloca {size=8} : ptr
  core.call @near(%s)
  core.return
}
)";
}

static void testWriteSiteReach() {
  // kMaxRuns=2 (seed + exactly one more run) makes the contrast airtight by construction, not by tuning: in the
  // seed run, helper's call site ("near"'s branch) is always inserted as a flip candidate AFTER all kNoise noise
  // branches (it is recorded later in execution order, so it always gets the highest initial seq) -- so with no
  // reachTarget bias, the single extra run can only ever pop a noise branch (lowest seq), never reach helper,
  // regardless of kNoise's value. With bias, helper's branch (distance 1, vs. noise's unreachable-sentinel
  // distance) is dequeued first no matter how many noise branches exist, so one extra run suffices to reach it.
  constexpr int kNoise = 15;
  constexpr unsigned kMaxRuns = 2;
  constexpr int64_t kTargetValue = 1337;
  const std::string programText = writeSiteReachProgram(kNoise);

  // Each run below gets its own freshly parsed module, since injecting the assert mutates it in place.
  auto findStore = [](const Module &mod) -> const Op * {
    const Function *helper = mod.findFunction("helper");
    if (!helper || helper->isDeclaration()) return nullptr;
    for (auto &op : helper->entry()->ops)
      if (op->opc == Opc::Store) return op.get();
    return nullptr;
  };

  // Baseline: injectWriteSiteAssert() directly, then TaintExecutor::run with reachTarget left EMPTY -- unlike
  // reachWriteSite() (which always sets cfg.reachTarget to the candidate's own function, that being its whole
  // point), this shows what the search does on the same injected assertion with the bias off. Default
  // coverage-guided order: 15 noise branches outrank helper's single call site within the same tiny budget, so
  // without the bias the engine should not confirm targetValue is reachable there.
  auto mDefault = load(programText, "wsreach_default");
  const Op *storeDefault = findStore(*mDefault);
  CHECK(storeDefault != nullptr, "found helper's core.store (default-order module)");
  const Function *helperDefault = mDefault->findFunction("helper");
  auto sitesDefault = findWriteSites(*mDefault, *helperDefault, storeDefault->operands[1]);
  CHECK(sitesDefault.size() == 1 && sitesDefault[0].storeOp == storeDefault,
        "findWriteSites recovers exactly the one real candidate (self-match: anchored at the store's own address)");
  Op *assertOpDefault = injectWriteSiteAssert(*mDefault, sitesDefault[0], kTargetValue);
  CHECK(assertOpDefault != nullptr, "assertion injection succeeded (scalar i32 store)");
  smt::TermManager tmDefault;
  TaintExecutor exDefault(*mDefault, tmDefault, *g_z3);
  TaintResult rDefault = exDefault.run("chain_entry", {}, TaintConfig{.maxRuns = kMaxRuns});  // reachTarget left at its empty default
  bool confirmedDefault = false;
  for (auto &f : rDefault.findings)
    if (f.status == RunStatus::AssertFailed && f.confirmed && *f.confirmed) confirmedDefault = true;
  CHECK(!confirmedDefault, "noise branches (recorded first, lower seq) outrank helper's call site within budget " << kMaxRuns
        << " when reachTarget bias is off -- got confirmed=" << confirmedDefault);

  // §3.3b step 2 itself: reachWriteSite() injects the same assertion and sets cfg.reachTarget = "helper" (the
  // candidate's own function) -- the exact mechanism `hlir-scan --reach-target helper` would apply, not a mock of
  // it (same TaintExecutor, same TaintConfig::reachTarget, same ReachTarget.h distance computation).
  auto mGuided = load(programText, "wsreach_guided");
  const Op *storeGuided = findStore(*mGuided);
  const Function *helperGuided = mGuided->findFunction("helper");
  auto sitesGuided = findWriteSites(*mGuided, *helperGuided, storeGuided->operands[1]);
  CHECK(sitesGuided.size() == 1, "findWriteSites recovers the candidate again in the fresh module");
  smt::TermManager tmGuided;
  WriteSiteReachResult rGuided = reachWriteSite(*mGuided, tmGuided, *g_z3, sitesGuided[0], "chain_entry", kTargetValue, TaintConfig{.maxRuns = kMaxRuns});
  CHECK(rGuided.confirmed, "--reach-target bias (via reachWriteSite) finds a concrete input making helper's store deposit "
        << kTargetValue << " within the same budget " << kMaxRuns << " -- note: " << rGuided.taint.note);
}

int main() {
  g_z3 = smt::makeZ3ProcessSolver("z3", 20000);
  if (!g_z3) { std::cout << "z3 not available: taint tests skipped\n"; return 0; }
  testScenario();
  testMemory();
  testEntry();
  testDifferential();
  testScale();
  testReachTargetDistance();
  testReachTargetSearch();
  testWriteSiteReach();
  testConeIndexScale();
  std::cout << "taint_tests: " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}

// Tests for symbolic execution (P2):
//  1. DESIGN.md §19.9 example 1 end to end, findings replayed on the concrete interpreter
//  2. exploration structure (forks, switch, loops, calls, nondet, assume, limits) on test/symbolic/*.core
//  3. three-way agreement: interpreter == evalTerm(encode) == solver, for every integer op
//  4. UB conditions: symbolic findings == interpreter verdicts (exhaustive on i4 with the enumeration solver,
//     sampled on i8 with z3)
#include <algorithm>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>

#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/Symbolic.h"

using namespace hlir;
using llvm::APInt;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }
static APInt ap(unsigned w, uint64_t v) { return APInt(w, v); }

static std::unique_ptr<Module> load(const std::string &text, const std::string &name) {
  Diagnostics d;
  auto m = parseModule(text, name, d);
  if (!m || d.hasErrors() || !verifyModule(*m, {}, d)) { std::cerr << "cannot load " << name << ":\n" << d.str(); std::exit(2); }
  return m;
}

static std::unique_ptr<smt::Solver> g_z3;  // null when z3 is not installed

struct Ctx {
  std::unique_ptr<Module> mod;
  smt::TermManager tm;
};

static SymResult symRun(const Module &m, smt::TermManager &tm, smt::Solver &s, const std::string &fn,
                        const std::vector<SymArg> &args = {}, SymConfig cfg = {}) {
  return SymbolicExecutor(m, tm, s).run(fn, args, cfg);
}

// Every finding must be reproducible by the concrete interpreter (the replay rate is a CI metric).
static void checkReplay(const Module &m, const std::string &fn, const SymResult &r, UBMode ub = UBMode::Report) {
  Interpreter in(m);
  for (auto &f : r.findings) {
    SeqEnv env(f.nondets);
    RunConfig cfg;
    cfg.ub = ub;
    RunResult rr = in.run(fn, f.args, env, cfg);
    // Same rule as lib/semantics/Taint.cpp (DESIGN.md §22.418): a UB the engine walks past is recorded in
    // `ubContinued` instead of ending the run. See ENGINE_LIMITATIONS.md §7.12.
    bool ok = f.ub ? ((rr.status == RunStatus::UB && rr.ub && rr.ub->kind == f.ub->kind) ||
                      std::any_of(rr.ubContinued.begin(), rr.ubContinued.end(),
                                  [&](const std::string &k) {
                                    return k.rfind(std::string(ubKindName(f.ub->kind)) + "@", 0) == 0;
                                  }))
                   : rr.status == RunStatus::AssertFailed;
    CHECK(ok, "@" << fn << ": finding not reproduced by the interpreter (got " << runStatusName(rr.status) << ")");
  }
}

static std::set<std::string> kinds(const SymResult &r) {
  std::set<std::string> s;
  for (auto &f : r.findings) s.insert(f.ub ? ubKindName(f.ub->kind) : "assert");
  return s;
}

// ---------------------------------------------------------------- 1 + 2
static void testPrograms() {
  smt::Solver &z = *g_z3;
  {
    auto m = load(slurp(HLIR_TEST_DIR "/copy_if_small.core"), "copy");
    smt::TermManager tm;
    SymResult r = symRun(*m, tm, z, "copy_unchecked");
    CHECK(r.complete && r.findings.size() == 1, "unchecked copy: exactly one finding, got " << r.findings.size());
    if (!r.findings.empty()) {
      auto &f = r.findings[0];
      CHECK(f.status == RunStatus::AssertFailed && f.message == "copy size exceeds buffer", "assertion message kept");
      CHECK(f.loc.file == "copy.c" && f.loc.line == 13, "source location kept");
      CHECK(f.args[0].isNegative() && f.args[0].getSExtValue() <= 256, "witness is a negative len: " << f.args[0].getSExtValue());
    }
    checkReplay(*m, "copy_unchecked", r);
    SymResult c = symRun(*m, tm, z, "copy_checked");
    CHECK(c.complete && c.findings.empty(), "checked copy has no findings");
    CHECK(c.pathsExplored == 3, "checked copy explores 3 paths, got " << c.pathsExplored);
  }
  auto m = load(slurp(HLIR_TEST_DIR "/paths.core"), "paths");
  smt::TermManager tm;
  {
    SymConfig cfg;
    cfg.collectPaths = true;
    SymResult r = symRun(*m, tm, z, "classify", {}, cfg);
    CHECK(r.complete && r.findings.empty() && r.pathsExplored == 4, "classify: 4 paths, got " << r.pathsExplored);
    std::set<int64_t> rets;
    for (auto &p : r.paths)
      if (p.returnValue && p.returnValue->kind == smt::Kind::BvConst) rets.insert(p.returnValue->value.getSExtValue());
    CHECK((rets == std::set<int64_t>{10, 20, 30, 99}), "classify returns 10/20/30/99 on its paths");
    // block coverage (SymResult::blocksVisited): all 4 case blocks plus the entry block were entered across the 4 paths.
    CHECK(r.blocksVisited.size() == 5, "classify: 5 blocks visited (entry + one/two/three/other), got " << r.blocksVisited.size());
    // every path condition is satisfiable and path conditions are pairwise exclusive
    for (size_t i = 0; i < r.paths.size(); ++i)
      for (size_t j = i + 1; j < r.paths.size(); ++j) {
        z.push();
        for (auto *c : r.paths[i].pc) z.assertTerm(c);
        for (auto *c : r.paths[j].pc) z.assertTerm(c);
        CHECK(z.check() == smt::SatResult::Unsat, "paths " << i << " and " << j << " overlap");
        z.pop();
      }
  }
  {
    SymResult r = symRun(*m, tm, z, "div_by_arg");
    CHECK((kinds(r) == std::set<std::string>{"div_by_zero", "div_overflow"}), "div_by_arg raises both division UBs");
    for (auto &f : r.findings) {
      if (f.ub->kind == UBKind::DivByZero) CHECK(f.args[1].isZero(), "div-by-zero witness has b == 0");
      else CHECK(f.args[0].isMinSignedValue() && f.args[1].isAllOnes(), "overflow witness is INT_MIN / -1");
      CHECK(f.ub->origin == "hl.binop sdiv" && f.ub->function == "div_by_arg", "UB report keeps origin and function");
    }
    checkReplay(*m, "div_by_arg", r);
    SymConfig assume;
    assume.ub = UBMode::AssumeAbsent;
    CHECK(symRun(*m, tm, z, "div_by_arg", {}, assume).findings.empty(), "assume-absent mode: no findings");
  }
  {
    SymResult r = symRun(*m, tm, z, "guarded_div");
    CHECK((kinds(r) == std::set<std::string>{"div_overflow"}), "guard removes div_by_zero, overflow remains");
    checkReplay(*m, "guarded_div", r);
    SymResult t = symRun(*m, tm, z, "twice");
    CHECK(t.complete && t.findings.empty(), "x / x can never overflow: call + guard analysed across frames");
  }
  {
    SymArg range;
    range.lo = ap(32, 0);
    range.hi = ap(32, 3);
    range.isSigned = true;
    SymResult r = symRun(*m, tm, z, "count_to", {range});
    CHECK(r.complete && r.pathsExplored == 4, "count_to(n in 0..3): 4 paths, got " << r.pathsExplored);
    SymConfig small;
    small.maxSteps = 20;
    SymResult lim = symRun(*m, tm, z, "count_to", {}, small);
    CHECK(!lim.complete && lim.note.find("step limit") != std::string::npos, "unbounded loop hits the step limit: " << lim.note);
    SymConfig onePath;
    onePath.maxPaths = 1;
    SymResult lp = symRun(*m, tm, z, "classify", {}, onePath);
    CHECK(!lp.complete && lp.note == "path limit reached", "path limit reported");
  }
  {
    SymResult r = symRun(*m, tm, z, "use_nondet");
    CHECK((kinds(r) == std::set<std::string>{"div_by_zero"}), "nondet divisor can be zero (and < 100 is assumed)");
    CHECK(r.findings.size() == 1 && r.findings[0].nondets.size() == 1 && r.findings[0].nondets[0].isZero(), "finding carries the nondet value");
    checkReplay(*m, "use_nondet", r);
    CHECK(symRun(*m, tm, z, "assume_then_div").findings.empty(), "assume(b != 0) removes the division UBs");
    SymResult u = symRun(*m, tm, z, "unreachable_if_big");
    CHECK((kinds(u) == std::set<std::string>{"unreachable_reached"}) && u.findings[0].args[0].ugt(1000), "unreachable reached only for x > 1000");
    checkReplay(*m, "unreachable_if_big", u);
  }
  {
    SymResult bad = symRun(*m, tm, z, "nope");
    CHECK(!bad.complete && bad.note.find("unknown function") != std::string::npos, "unknown function reported");
    auto pm = load("core.func @p(ptr) -> i32 {\n^entry(%a: ptr):\n  %z = core.const 0 : i32\n  core.return %z\n}\n", "ptr");
    SymResult pr = symRun(*pm, tm, z, "p");
    CHECK(!pr.complete && pr.note.find("pointer") != std::string::npos, "pointer parameters need the memory model");
  }
}

// ---------------------------------------------------------------- 3. three-way op consistency
struct OpSpec { const char *name; bool cmp; };

static std::string binProgram(const std::string &op, unsigned w, bool cmp) {
  std::string t = "i" + std::to_string(w);
  std::string res = cmp ? "bool" : t;
  std::string line = cmp ? "core.icmp " + op : "core." + op;
  return "core.func @f(" + t + ", " + t + ") -> " + res + " {\n^entry(%a: " + t + ", %b: " + t + "):\n  %r = " + line + " %a, %b : " + res + "\n  core.return %r\n}\n";
}

static void threeWay(const std::string &prog, unsigned w, int evalSamples, int solverSamples, const std::string &label, std::mt19937_64 &rng) {
  auto m = load(prog, label);
  smt::TermManager tm;
  auto en = smt::makeEnumSolver(1);  // never asked to solve here
  SymConfig cfg;
  cfg.collectPaths = true;
  SymResult r = symRun(*m, tm, *en, "f", {}, cfg);
  CHECK(r.complete && r.paths.size() == 1 && r.paths[0].returnValue, label << ": straight-line function, one path");
  if (r.paths.size() != 1 || !r.paths[0].returnValue) return;
  smt::TermRef R = r.paths[0].returnValue;
  Interpreter in(*m);
  TableEnv env;
  static const uint64_t edges[] = {0, 1, 2, 3, 7, 8, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0x7fffffff, 0x80000000, 0xffffffff, ~0ull, 0x8000000000000000ull};
  int solved = 0;
  for (int i = 0; i < evalSamples; ++i) {
    uint64_t xa = i < 256 ? edges[i % 16] : rng(), xb = i < 256 ? edges[(i / 16) % 16] : rng();
    APInt x = ap(w, xa), y = ap(w, xb);
    RunResult rr = in.run("f", {x, y}, env);
    if (rr.status != RunStatus::Returned) { CHECK(false, label << ": interpreter failed"); return; }
    smt::Assignment asg{{"arg.a", x}, {"arg.b", y}};
    APInt viaTerm = smt::evalTerm(R, asg);
    CHECK(viaTerm == *rr.returnValue, label << " w=" << w << " (" << x.getSExtValue() << "," << y.getSExtValue() << "): interpreter " << rr.returnValue->getSExtValue() << " vs term " << viaTerm.getSExtValue());
    if (g_z3 && solved < solverSamples && (i < 64 || i % 7 == 0)) {
      ++solved;
      g_z3->push();
      g_z3->assertTerm(tm.mkEq(r.argVars[0], tm.bvConst(x)));
      g_z3->assertTerm(tm.mkEq(r.argVars[1], tm.bvConst(y)));
      g_z3->assertTerm(tm.mkNot(tm.mkEq(R->sort.isBool ? tm.fromBool(R) : R, tm.bvConst(*rr.returnValue))));
      CHECK(g_z3->check() == smt::SatResult::Unsat, label << " w=" << w << " (" << x.getSExtValue() << "," << y.getSExtValue() << "): z3 disagrees with the interpreter");
      g_z3->pop();
    }
  }
}

static void testThreeWay() {
  std::mt19937_64 rng(2024);
  const char *bins[] = {"add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "and", "or", "xor", "shl", "lshr", "ashr"};
  const char *preds[] = {"eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"};
  for (unsigned w : {8u, 16u, 32u, 64u}) {
    int evalN = w == 8 ? 2000 : 10000, zN = w == 8 ? 60 : 40;
    for (auto *op : bins) threeWay(binProgram(op, w, false), w, evalN, zN, std::string(op), rng);
    for (auto *p : preds) threeWay(binProgram(p, w, true), w, evalN / 5, zN, std::string("icmp ") + p, rng);
  }
  // unary / conversion ops through a small harness
  struct U { const char *line; const char *ret; };
  for (unsigned w : {8u, 32u}) {
    std::string t = "i" + std::to_string(w);
    const std::pair<std::string, std::string> un[] = {
        {"core.not %a : " + t, t}, {"core.neg %a : " + t, t}, {"core.zext %a : i64", "i64"}, {"core.sext %a : i64", "i64"},
        {"core.trunc %a : i4", "i4"}, {"core.i2b %a : bool", "bool"}, {"core.select %c, %a, %b : " + t, t}};
    for (auto &u : un) {
      bool sel = u.first.find("select") != std::string::npos;
      std::string c = sel ? "  %c = core.icmp slt %a, %b : bool\n" : "";
      std::string prog = "core.func @f(" + t + ", " + t + ") -> " + u.second + " {\n^entry(%a: " + t + ", %b: " + t + "):\n" + c + "  %r = " + u.first + "\n  core.return %r\n}\n";
      threeWay(prog, w, 3000, 30, u.first, rng);
    }
  }
}

// ---------------------------------------------------------------- 4. UB conditions
struct UBProg { const char *name; const char *line; };

static void testUBConditions() {
  const UBProg progs[] = {
      {"div_s", "core.check.div %a, %b {signed}"},
      {"div_u", "core.check.div %a, %b"},
      {"shift", "core.check.shift %a, %b"},
      {"shift_sl", "core.check.shift %a, %b {signed_left}"},
      {"sadd", "core.check.sadd_ovf %a, %b"},
      {"ssub", "core.check.ssub_ovf %a, %b"},
      {"smul", "core.check.smul_ovf %a, %b"},
      {"sneg", "core.check.sneg_ovf %a"},
  };
  std::mt19937_64 rng(99);
  auto enumSolver = smt::makeEnumSolver(24);
  for (auto &p : progs) {
    for (unsigned w : {4u, 8u}) {
      std::string t = "i" + std::to_string(w);
      auto m = load("core.func @f(" + t + ", " + t + ") -> i32 {\n^entry(%a: " + t + ", %b: " + t + "):\n  " + p.line + "\n  %z = core.const 0 : i32\n  core.return %z\n}\n", p.name);
      Interpreter in(*m);
      smt::TermManager tm;
      smt::Solver &s = w == 4 ? *enumSolver : *g_z3;
      uint64_t mask = (1ull << w) - 1;
      int n = 0;
      for (uint64_t a = 0; a <= mask; ++a)
        for (uint64_t b = 0; b <= mask; ++b) {
          if (w == 8) {  // sampled: edges + random
            static const uint64_t e[] = {0, 1, 2, 7, 8, 0x7f, 0x80, 0xff};
            bool edge = std::find(std::begin(e), std::end(e), a) != std::end(e) && std::find(std::begin(e), std::end(e), b) != std::end(e);
            if (!edge && (rng() % 600) != 0) continue;
          }
          ++n;
          TableEnv env;
          RunResult rr = in.run("f", {ap(w, a), ap(w, b)}, env);
          SymArg A, B;
          A.lo = A.hi = ap(w, a);
          B.lo = B.hi = ap(w, b);
          SymResult sr = symRun(*m, tm, s, "f", {A, B});
          std::set<std::string> want;
          if (rr.status == RunStatus::UB) want.insert(ubKindName(rr.ub->kind));
          CHECK(sr.complete && kinds(sr) == want, p.name << " w=" << w << " (" << a << "," << b << "): symbolic " << (kinds(sr).empty() ? "none" : *kinds(sr).begin()) << " vs interpreter " << (want.empty() ? "none" : *want.begin()));
        }
      (void)n;
    }
  }
}


// ---------------------------------------------------------------- 5. symbolic memory
static void testMemory() {
  smt::Solver &z = *g_z3;
  auto m = load(slurp(HLIR_TEST_DIR "/memory.core"), "memory");
  smt::TermManager tm;
  {
    SymResult r = symRun(*m, tm, z, "cond_double_free");
    CHECK(r.complete && (kinds(r) == std::set<std::string>{"double_free"}), "conditional double free found (and nothing else)");
    for (auto &f : r.findings) {
      CHECK(f.loc.line == 14, "reported at the second free (x.c:14), got line " << f.loc.line);
      CHECK(!f.args[0].isZero(), "witness has flag != 0");
    }
    checkReplay(*m, "cond_double_free", r);
  }
  {
    SymResult r = symRun(*m, tm, z, "last_byte");
    CHECK(r.complete && (kinds(r) == std::set<std::string>{"ptr_arith_oob"}), "buf[len-1] with len == 0 is a pointer-arithmetic UB");
    CHECK(r.findings.size() == 1 && r.findings[0].args[0].isZero(), "witness is len == 0");
    checkReplay(*m, "last_byte", r);
  }
  {
    SymConfig cfg;
    cfg.collectPaths = true;
    SymResult r = symRun(*m, tm, z, "roundtrip", {}, cfg);
    CHECK(r.complete && r.findings.empty() && r.paths.size() == 1, "roundtrip: no UB, one path");
    if (r.paths.size() == 1) {
      z.push();
      z.assertTerm(tm.mkNot(tm.mkEq(r.paths[0].returnValue, r.argVars[0])));
      CHECK(z.check() == smt::SatResult::Unsat, "load returns exactly the stored symbolic value");
      z.pop();
    }
    SymResult s = symRun(*m, tm, z, "select_ptr", {}, cfg);
    CHECK(s.complete && s.findings.empty(), "select_ptr: no findings");
    for (auto &p : s.paths) {
      // on each path the result is 10 iff the argument is non-zero
      z.push();
      for (auto *c : p.pc) z.assertTerm(c);
      z.assertTerm(tm.mkNot(tm.mkEq(p.returnValue, tm.mkIte(tm.mkEq(s.argVars[0], tm.bvConst(32, 0)), tm.bvConst(32, 20), tm.bvConst(32, 10)))));
      CHECK(z.check() == smt::SatResult::Unsat, "select_ptr returns 10/20 according to the condition");
      z.pop();
    }
    // core.ptr_to_int of a pointer whose `obj` is itself symbolic (merged across two objects by a select) must not
    // bail as unsupported (regression for Memory::ptrToIntVal). Both branches select a real alloca, so the packed
    // high 32 bits (object id) must be nonzero on every path regardless of the condition.
    SymResult pi = symRun(*m, tm, z, "ptr_to_int_select", {}, cfg);
    CHECK(pi.complete && pi.findings.empty(), "ptr_to_int_select: no findings");
    CHECK(pi.paths.size() == 1, "select does not fork paths");
    if (pi.paths.size() == 1) {
      z.push();
      z.assertTerm(tm.mkEq(tm.mkExtract(pi.paths[0].returnValue, 63, 32), tm.bvConst(32, 0)));
      CHECK(z.check() == smt::SatResult::Unsat, "ptr_to_int_select: object id (high 32 bits) is never 0 on any path");
      z.pop();
    }
  }
  {
    SymResult r = symRun(*m, tm, z, "index_write");
    CHECK((kinds(r) == std::set<std::string>{"oob_write"}) && r.findings.size() == 1 && r.findings[0].args[0].uge(8), "unchecked index: oob_write for i >= 8");
    CHECK(!r.overApprox, "a symbolic offset store is modelled exactly (array memory), not over-approximated");
    checkReplay(*m, "index_write", r);
  }
  {
    SymResult r = symRun(*m, tm, z, "sized_read");
    CHECK((kinds(r) == std::set<std::string>{"oob_read"}) && r.findings[0].args[0].ule(16), "heap size is a symbolic term: oob iff n <= 16");
    checkReplay(*m, "sized_read", r);
    SymArg big;
    big.lo = ap(64, 17);
    big.hi = ap(64, 1000);
    SymResult ok = symRun(*m, tm, z, "sized_read", {big});
    CHECK(ok.complete && kinds(ok).count("oob_read") == 0, "with n >= 17 the read is in bounds");
    CHECK(kinds(ok).count("uninit_read") == 0, "(no uninit check in this function)");
  }
  {
    SymResult r = symRun(*m, tm, z, "uninit_heap");
    CHECK((kinds(r) == std::set<std::string>{"uninit_read"}) && r.findings.size() == 1 && r.findings[0].loc.line == 9, "only the unwritten half is uninitialised");
    checkReplay(*m, "uninit_heap", r);
  }
  {
    SymResult r = symRun(*m, tm, z, "uaf_via_slot");
    CHECK(r.complete && (kinds(r) == std::set<std::string>{"use_after_free"}), "UAF through a pointer that went through memory (provenance kept)");
    checkReplay(*m, "uaf_via_slot", r);
  }
}

static void testLibcModels() {
  smt::Solver &z = *g_z3;
  auto m = load(slurp(HLIR_TEST_DIR "/libc_user.core") + "\n" + slurp(HLIR_MODELS_DIR "/libc.core"), "libc");
  smt::TermManager tm;
  SymResult o = symRun(*m, tm, z, "overflow");
  CHECK(o.complete && (kinds(o) == std::set<std::string>{"oob_write"}), "memcpy model: 8 bytes into a 4-byte malloc");
  CHECK(!o.findings.empty() && o.findings[0].ub->function == "memcpy", "the model reports the UB inside memcpy");
  checkReplay(*m, "overflow", o);
  SymResult f = symRun(*m, tm, z, "fine");
  CHECK(f.complete && f.findings.empty(), "memcpy model: exact fit is fine");
  SymResult d = symRun(*m, tm, z, "free_twice");
  CHECK((kinds(d) == std::set<std::string>{"double_free"}), "free model: double free");
  checkReplay(*m, "free_twice", d);
  SymArg overflowing;  // 2^62 * n wraps for n >= 4
  overflowing.lo = ap(64, 4);
  overflowing.hi = ap(64, 8);
  SymResult c = symRun(*m, tm, z, "calloc_overflow", {overflowing});
  CHECK(c.complete && c.findings.empty(), "calloc model: n*size overflow returns NULL instead of UB");
  SymResult unb = symRun(*m, tm, z, "calloc_overflow");
  CHECK(!unb.complete && unb.reason == "bound_insufficient", "an unbounded memset length is reported as an insufficient unrolling bound, not silently truncated");
}

// ---------------------------------------------------------------- 6. array memory (symbolic offsets)
static smt::TermRef bvc(smt::TermManager &tm, unsigned w, uint64_t v) { return tm.bvConst(w, v); }

static void testArrayMemory() {
  smt::Solver &z = *g_z3;
  auto m = load(slurp(HLIR_TEST_DIR "/memory.core"), "memory");
  smt::TermManager tm;
  SymConfig cfg;
  cfg.collectPaths = true;
  auto proves = [&](const SymPath &p, smt::TermRef claim, const std::string &what) {
    z.push();
    for (auto *c : p.pc) z.assertTerm(c);
    z.assertTerm(tm.mkNot(claim));
    CHECK(z.check() == smt::SatResult::Unsat, what);
    z.pop();
  };
  {
    SymResult r = symRun(*m, tm, z, "sym_roundtrip", {}, cfg);
    CHECK(r.complete && r.findings.empty() && r.paths.size() == 1 && !r.overApprox, "symbolic offset roundtrip: exact, no findings");
    if (r.paths.size() == 1) proves(r.paths[0], tm.mkEq(r.paths[0].returnValue, tm.bvVar("arg.v", 8)), "the byte read back at the same symbolic offset is the stored one");
  }
  {
    SymResult r = symRun(*m, tm, z, "sym_partial_init", {}, cfg);
    CHECK((kinds(r) == std::set<std::string>{"uninit_read"}) && r.findings.size() == 1 && r.findings[0].loc.line == 9, "buf[0] is uninitialised unless the symbolic store hit it");
    if (!r.findings.empty()) CHECK((r.findings[0].args[0].getZExtValue() & 7) != 0, "witness: the store went elsewhere");
    checkReplay(*m, "sym_partial_init", r);
  }
  {
    SymResult r = symRun(*m, tm, z, "sym_two_offsets", {}, cfg);
    CHECK(r.complete && r.findings.empty() && r.paths.size() == 1, "zero-initialised global with two symbolic offsets");
    if (r.paths.size() == 1) {
      smt::TermRef i = tm.bvVar("arg.i", 32), j = tm.bvVar("arg.j", 32), v = tm.bvVar("arg.v", 8);
      smt::TermRef mi = tm.mkBin(smt::Kind::BvAnd, i, bvc(tm, 32, 15)), mj = tm.mkBin(smt::Kind::BvAnd, j, bvc(tm, 32, 15));
      proves(r.paths[0], tm.mkEq(r.paths[0].returnValue, tm.mkIte(tm.mkEq(mi, mj), v, bvc(tm, 8, 0))), "the load sees the store only when the offsets coincide");
    }
  }
  {
    SymResult r = symRun(*m, tm, z, "sym_memcpy", {}, cfg);
    CHECK(r.complete && r.findings.empty() && r.paths.size() == 1 && !r.overApprox, "bounded symbolic-length memcpy is exact and complete");
    if (r.paths.size() == 1) {
      smt::TermRef n = tm.bvVar("arg.n", 64), v = tm.bvVar("arg.v", 8);
      proves(r.paths[0], tm.mkEq(r.paths[0].returnValue, tm.mkIte(tm.mkCmp(smt::Kind::Ult, bvc(tm, 64, 5), n), v, bvc(tm, 8, 0))), "dst[5] is copied iff 5 < n");
    }
    SymResult u = symRun(*m, tm, z, "sym_memcpy_unbounded");
    CHECK(!u.complete && u.reason == "bound_insufficient", "no bound on n: the engine reports the unrolling bound as insufficient");
    SymConfig big;
    big.memBound = 4096;
    SymResult ub = symRun(*m, tm, z, "sym_memcpy_unbounded", {}, big);
    CHECK(!ub.complete && ub.reason == "bound_insufficient", "a bigger bound does not make an unbounded length bounded");
  }
  {
    SymResult r = symRun(*m, tm, z, "sym_ptr_slots", {}, cfg);
    CHECK(r.complete && r.findings.empty() && r.paths.size() == 1, "pointers in symbolic slots: no UB (complete " << r.complete << ", findings " << r.findings.size() << ", " << r.note << ")");
    if (r.paths.size() == 1) {
      smt::TermRef i = tm.bvVar("arg.i", 32), j = tm.bvVar("arg.j", 32);
      smt::TermRef bi = tm.mkBin(smt::Kind::BvAnd, i, bvc(tm, 32, 1)), bj = tm.mkBin(smt::Kind::BvAnd, j, bvc(tm, 32, 1));
      proves(r.paths[0], tm.mkEq(r.paths[0].returnValue, tm.mkIte(tm.mkEq(bi, bj), bvc(tm, 32, 10), bvc(tm, 32, 20))), "the loaded pointer keeps its provenance through the symbolic slot");
    }
  }
}

// Differential: with every argument pinned to a concrete value, the symbolic engine over array memory must agree with the
// concrete interpreter on the verdict and on the returned value.
struct MemGen {
  std::mt19937_64 rng;
  std::string body;
  int n = 0, line = 10;
  explicit MemGen(uint64_t seed) : rng(seed) {}
  uint64_t r(uint64_t k) { return rng() % k; }
  std::string v() { return "%t" + std::to_string(n++); }
  void e(const std::string &s) { body += "  " + s + "\n"; }
  std::string loc() { return " loc(\"g.c\":" + std::to_string(line++) + ":1)"; }

  // a symbolic (argument-derived) byte offset into a buffer of `size` bytes; sometimes unmasked => possibly out of bounds
  std::string offset(const std::string &arg, int size, bool mask) {
    std::string x = v(), z = v();
    if (mask) { std::string m = v(); e(m + " = core.const " + std::to_string(size - 1) + " : i32"); e(x + " = core.and " + arg + ", " + m + " : i32"); }
    else { std::string m = v(); e(m + " = core.const 31 : i32"); e(x + " = core.and " + arg + ", " + m + " : i32"); }
    e(z + " = core.zext " + x + " : i64");
    return z;
  }
  std::string program() {
    body.clear();
    const int sizes[2] = {8, 16};
    e("%b0 = core.alloca {size=8, align=8} : ptr");
    e("%b1 = core.alloca {size=16, align=8} : ptr");
    e("%z8 = core.const 0 : i8");
    if (r(2)) { e("%e8 = core.const 8 : i64"); e("core.memset %b0, %z8, %e8"); }
    if (r(2)) { e("%e16 = core.const 16 : i64"); e("core.memset %b1, %z8, %e16"); }
    std::string last = "%z8";
    std::vector<std::string> bytes{"%z8"};
    int stmts = 3 + static_cast<int>(r(6));
    for (int k = 0; k < stmts; ++k) {
      int bi = static_cast<int>(r(2));
      std::string buf = bi ? "%b1" : "%b0";
      std::string arg = r(2) ? "%a" : "%b";
      bool mask = r(3) != 0;
      switch (r(5)) {
        case 0: case 1: {  // store a byte at a symbolic offset
          std::string off = offset(arg, sizes[bi], mask), q = v(), val = v();
          e(q + " = core.ptr_add " + buf + ", " + off + " : ptr");
          e("core.check.oob " + q + " {w=1, access=\"w\"}" + loc());
          e(val + " = core.trunc " + (r(2) ? "%a" : "%b") + " : i8");
          e("core.store " + val + ", " + q);
          bytes.push_back(val);
          break;
        }
        case 2: case 3: {  // load a byte at a symbolic offset (uninit-checked)
          std::string off = offset(arg, sizes[bi], mask), q = v(), val = v();
          e(q + " = core.ptr_add " + buf + ", " + off + " : ptr");
          e("core.check.oob " + q + " {w=1, access=\"r\"}" + loc());
          e("core.check.uninit " + q + " {w=1}" + loc());
          e(val + " = core.load " + q + " : i8");
          bytes.push_back(val);
          last = val;
          break;
        }
        default: {  // memcpy between the buffers with a constant length, from/to a symbolic offset
          std::string off = offset(arg, 8, true), q = v(), len = v();
          e(q + " = core.ptr_add " + (bi ? "%b0" : "%b1") + ", " + off + " : ptr");
          e(len + " = core.const " + std::to_string(1 + r(4)) + " : i64");
          e("core.check.oob " + q + " {w=4, access=\"r\"}" + loc());
          e("core.check.oob " + std::string(buf) + " {w=4, access=\"w\"}" + loc());
          e("core.memcpy " + buf + ", " + q + ", " + len);
          break;
        }
      }
    }
    std::string a = v(), res = v();
    e(a + " = core.zext " + last + " : i32");
    e("core.return " + a);
    return "core.func @f(i32, i32) -> i32 {\n^entry(%a: i32, %b: i32):\n" + body + "}\n";
  }
};

static void testArrayDifferential() {
  smt::Solver &z = *g_z3;
  int cases = 0, withUB = 0;
  for (uint64_t seed = 1; seed <= 60; ++seed) {
    MemGen g(seed);
    std::string prog = g.program();
    Diagnostics d;
    auto m = parseModule(prog, "memgen", d);
    if (!m || d.hasErrors() || !verifyModule(*m, {}, d)) { CHECK(false, "generated memory program " << seed << " does not verify:\n" << d.str() << prog); continue; }
    Interpreter in(*m);
    std::mt19937_64 rng(seed * 77);
    for (int k = 0; k < 6; ++k) {
      uint64_t a = rng() & 0xffff, b = rng() & 0xffff;
      if (k == 0) a = b = 0;
      TableEnv env;
      RunResult rr = in.run("f", {ap(32, a), ap(32, b)}, env);
      smt::TermManager tm;
      SymArg A, B;
      A.lo = A.hi = ap(32, a);
      B.lo = B.hi = ap(32, b);
      SymConfig cfg;
      cfg.collectPaths = true;
      SymResult sr = symRun(*m, tm, z, "f", {A, B}, cfg);
      ++cases;
      std::set<std::string> want;
      if (rr.status == RunStatus::UB) { want.insert(ubKindName(rr.ub->kind)); ++withUB; }
      // A UB the engine deliberately walks past (a dead uninitialised read, out-of-range pointer arithmetic)
      // is REPORTED but does not end the run, so `status` alone is not the whole set of what happened. The
      // interpreter records those sites in `ubContinued`; the symbolic side reports them as findings. Same
      // rule as lib/semantics/Taint.cpp (DESIGN.md §22.418).
      for (auto &k : rr.ubContinued) want.insert(k.substr(0, k.find('@')));
      CHECK(sr.complete, "seed " << seed << ": symbolic run incomplete: " << sr.note);
      CHECK(kinds(sr) == want, "seed " << seed << " args(" << a << "," << b << "): interpreter " << (want.empty() ? "no UB" : *want.begin()) << " vs symbolic " << (kinds(sr).empty() ? "no UB" : *kinds(sr).begin()) << "\n" << prog);
      if (rr.status == RunStatus::Returned && sr.complete) {
        bool matched = false;
        for (auto &p : sr.paths) {
          if (!p.returnValue || p.status != RunStatus::Returned) continue;
          smt::Assignment asg{{"arg.a", ap(32, a)}, {"arg.b", ap(32, b)}};
          // arrays inside the term are evaluated by z3: the path is feasible and returns exactly the interpreter's value
          z.push();
          for (auto *c : p.pc) z.assertTerm(c);
          z.assertTerm(tm.mkEq(p.returnValue, tm.bvConst(*rr.returnValue)));
          matched |= z.check() == smt::SatResult::Sat;
          z.pop();
        }
        CHECK(matched, "seed " << seed << " args(" << a << "," << b << "): the interpreter's return value " << rr.returnValue->getZExtValue() << " is not produced by any symbolic path\n" << prog);
      }
    }
  }
  std::cout << "  array-memory differential: " << cases << " cases (" << withUB << " with UB)\n";
  CHECK(withUB > 10, "the generated programs exercise UB (" << withUB << ")");
}

int main() {
  g_z3 = smt::makeZ3ProcessSolver("z3", 20000);
  if (!g_z3) { std::cout << "z3 not available: symbolic tests skipped\n"; return 0; }
  testPrograms();
  testThreeWay();
  testUBConditions();
  testMemory();
  testLibcModels();
  testArrayMemory();
  testArrayDifferential();
  std::cout << "symbolic_tests: " << g_pass << " passed, " << g_fail << " failed (z3 queries: " << g_z3->checkCount() << ")\n";
  return g_fail ? 1 : 0;
}

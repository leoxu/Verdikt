// Tests for the `smt` module (P2): hash-consing and simplification soundness, evaluation against native arithmetic,
// SMT-LIB printing, and one conformance suite run against every solver backend.
#include <cstdint>
#include <iostream>
#include <random>

#include "hlir/smt/Solver.h"

using namespace hlir;
using namespace hlir::smt;
using llvm::APInt;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static APInt ap(unsigned w, uint64_t v) { return APInt(w, v); }

// ---------------------------------------------------------------- terms
static void testHashConsing() {
  TermManager tm;
  TermRef x = tm.bvVar("x", 8), y = tm.bvVar("y", 8);
  CHECK(tm.bvVar("x", 8) == x, "same variable is the same term");
  CHECK(tm.mkBin(Kind::BvAdd, x, y) == tm.mkBin(Kind::BvAdd, y, x), "commutative ops are canonicalised");
  CHECK(tm.mkBin(Kind::BvSub, x, y) != tm.mkBin(Kind::BvSub, y, x), "sub is not commutative");
  CHECK(tm.bvConst(8, 5) == tm.bvConst(8, 5), "constants interned");
  CHECK(tm.bvConst(8, 5) != tm.bvConst(16, 5), "constants of different widths differ");
  CHECK(tm.mkNot(tm.mkNot(tm.mkEq(x, y))) == tm.mkEq(x, y), "double negation");
  CHECK(tm.mkEq(x, x)->isTrue(), "x = x");
  CHECK(tm.mkBin(Kind::BvAdd, x, tm.bvConst(8, 0)) == x, "x + 0");
  CHECK(tm.mkBin(Kind::BvXor, x, x)->kind == Kind::BvConst, "x ^ x folds");
  CHECK(tm.mkBin(Kind::BvAdd, tm.bvConst(8, 200), tm.bvConst(8, 100))->value == 44, "constant folding wraps");
  CHECK(tm.mkExtract(x, 7, 0) == x, "full-width extract is identity");
  CHECK(tm.mkZExt(x, 8) == x, "zext to same width");
  // every field of the hash-consing identity distinguishes terms (Sec.22.337: interning compares fields, not a string key)
  TermRef z = tm.bvVar("z", 16);
  CHECK(tm.mkExtract(z, 7, 0) == tm.mkExtract(z, 7, 0) && tm.mkExtract(z, 7, 0) != tm.mkExtract(z, 8, 1), "extract: hi/lo distinguish");
  CHECK(tm.mkExtract(z, 7, 0) != tm.mkExtract(z, 15, 8), "extract: same width, other bits");
  CHECK(tm.mkZExt(x, 16) == tm.mkZExt(x, 16) && tm.mkZExt(x, 16) != tm.mkZExt(x, 32), "zext: target width distinguishes");
  CHECK(tm.mkZExt(x, 16) != tm.mkSExt(x, 16), "zext vs sext: kind distinguishes");
  CHECK(tm.mkCmp(Kind::Ult, x, y) != tm.mkCmp(Kind::Ult, y, x), "argument order distinguishes");
  CHECK(tm.mkCmp(Kind::Ult, x, y) != tm.mkCmp(Kind::Slt, x, y), "comparison kind distinguishes");
  CHECK(tm.mkConcat(x, y) != tm.mkConcat(y, x) && tm.mkConcat(x, y)->sort.width == 16, "concat order distinguishes");
  CHECK(tm.boolConst(true) != tm.bvConst(1, 1), "Bool true and bv1 #b1 are different terms");
  CHECK(tm.bvConst(8, 5) != tm.bvConst(8, 6), "constant value distinguishes");
  CHECK(tm.bvConst(APInt::getAllOnes(64)) == tm.bvConst(APInt::getAllOnes(64)), "wide constants intern");
  CHECK(tm.bvVar("x", 8) != tm.bvVar("y", 8), "variable name distinguishes");
  {
    TermManager tm2;  // terms of another manager are never confused (separate tables)
    CHECK(tm2.bvVar("x", 8) != x && tm2.bvVar("x", 8)->mgr != x->mgr, "managers do not share terms");
  }
  auto build = [&] { for (int i = 0; i < 1000; ++i) (void)tm.mkBin(Kind::BvMul, tm.mkBin(Kind::BvAdd, x, tm.bvConst(8, i % 7)), y); };
  build();
  size_t before = tm.size();
  build();
  CHECK(tm.size() == before, "rebuilding the same terms creates no new ones, got " << tm.size() - before);
  // bridges
  TermRef c = tm.mkCmp(Kind::Ult, x, y);
  TermRef bv = tm.fromBool(c);
  CHECK(tm.toBool(bv) == c, "toBool(fromBool(c)) == c");
  CHECK(tm.toBool(tm.mkUn(Kind::BvNot, tm.bvConst(1, 1)))->isFalse(), "bridge on constants");
  CHECK(tm.mkIte(c, tm.bvConst(8, 1), tm.bvConst(8, 1))->kind == Kind::BvConst, "ite with equal branches");
}

// Every simplification rule must agree with the reference semantics: evaluate the *simplified* term and the plain
// operator application on all combinations of interesting operands.
static void testSimplifierSoundness() {
  std::mt19937_64 rng(7);
  const Kind bins[] = {Kind::BvAdd, Kind::BvSub, Kind::BvMul, Kind::BvUdiv, Kind::BvUrem, Kind::BvSdiv, Kind::BvSrem,
                       Kind::BvAnd, Kind::BvOr, Kind::BvXor, Kind::BvShl, Kind::BvLshr, Kind::BvAshr};
  for (unsigned w : {1u, 4u, 8u}) {
    TermManager tm;
    TermRef x = tm.bvVar("x", w), y = tm.bvVar("y", w);
    std::vector<TermRef> operands{x, y, tm.bvConst(w, 0), tm.bvConst(w, 1), tm.bvConst(APInt::getAllOnes(w)),
                                  tm.bvConst(APInt::getSignedMinValue(w)), tm.bvConst(w, rng())};
    for (Kind k : bins)
      for (TermRef a : operands)
        for (TermRef b : operands) {
          TermRef t = tm.mkBin(k, a, b);
          for (int i = 0; i < 40; ++i) {
            Assignment asg{{"x", ap(w, rng())}, {"y", ap(w, rng())}};
            APInt av = evalTerm(a, asg), bv = evalTerm(b, asg);
            APInt want = evalApply(k, 0, 0, w, {av, bv});
            CHECK(evalTerm(t, asg) == want, kindName(k) << " w=" << w << " simplified term disagrees with the operator");
          }
        }
    for (Kind k : {Kind::Ult, Kind::Ule, Kind::Slt, Kind::Sle})
      for (TermRef a : operands)
        for (TermRef b : operands) {
          TermRef t = tm.mkCmp(k, a, b);
          for (int i = 0; i < 20; ++i) {
            Assignment asg{{"x", ap(w, rng())}, {"y", ap(w, rng())}};
            CHECK(evalTerm(t, asg) == evalApply(k, 0, 0, 1, {evalTerm(a, asg), evalTerm(b, asg)}), kindName(k) << " simplified");
          }
        }
  }
}

// evalApply against native C++ for i8/i32/i64 with the SMT-LIB conventions written out by hand.
static void testEvalNative() {
  std::mt19937_64 rng(11);
  auto edge = [&](int i) -> uint64_t {
    static const uint64_t e[] = {0, 1, 2, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff, ~0ull, 0x8000000000000000ull, 0x7fffffffffffffffull};
    return i < 12 ? e[i] : rng();
  };
  for (unsigned w : {8u, 32u, 64u}) {
    uint64_t mask = w == 64 ? ~0ull : ((1ull << w) - 1);
    auto sx = [&](uint64_t v) -> int64_t { return w == 64 ? static_cast<int64_t>(v) : (static_cast<int64_t>(v << (64 - w)) >> (64 - w)); };
    for (int i = 0; i < 40; ++i)
      for (int j = 0; j < 40; ++j) {
        uint64_t a = edge(i) & mask, b = edge(j) & mask;
        APInt A = ap(w, a), B = ap(w, b);
        auto ev = [&](Kind k) { return evalApply(k, 0, 0, w, {A, B}).getZExtValue(); };
        uint64_t udiv = b == 0 ? mask : a / b;
        uint64_t urem = b == 0 ? a : a % b;
        // bvsdiv/bvsrem via magnitudes (SMT-LIB definition), computed here in unsigned 64-bit arithmetic
        auto mag = [&](uint64_t v) { return (v >> (w - 1)) & 1 ? ((~v + 1) & mask) : v; };
        bool na = (a >> (w - 1)) & 1, nb = (b >> (w - 1)) & 1;
        uint64_t ua = mag(a), ub = mag(b);
        uint64_t qd = ub == 0 ? mask : ua / ub, rm = ub == 0 ? ua : ua % ub;
        uint64_t sdiv = (na != nb) ? ((~qd + 1) & mask) : qd;
        uint64_t srem = na ? ((~rm + 1) & mask) : rm;
        CHECK(ev(Kind::BvUdiv) == udiv, "udiv w=" << w << " " << a << "/" << b);
        CHECK(ev(Kind::BvUrem) == urem, "urem w=" << w);
        CHECK(ev(Kind::BvSdiv) == sdiv, "sdiv w=" << w << " " << sx(a) << "/" << sx(b));
        CHECK(ev(Kind::BvSrem) == srem, "srem w=" << w << " " << sx(a) << "%" << sx(b));
        CHECK(ev(Kind::BvShl) == (b >= w ? 0 : (a << b) & mask), "shl w=" << w);
        CHECK(ev(Kind::BvLshr) == (b >= w ? 0 : a >> b), "lshr w=" << w);
        uint64_t ash = b >= w ? (sx(a) < 0 ? mask : 0) : (static_cast<uint64_t>(sx(a) >> b) & mask);
        CHECK(ev(Kind::BvAshr) == ash, "ashr w=" << w);
        CHECK(ev(Kind::BvMul) == ((a * b) & mask), "mul w=" << w);
      }
  }
}

static void testPrinter() {
  TermManager tm;
  TermRef x = tm.bvVar("len", 32);
  TermRef n = tm.mkSExt(x, 64);
  TermRef c = tm.mkCmp(Kind::Ult, tm.bvConst(64, 255), n);
  SmtLibEmitter em;
  std::string out;
  std::string e = em.emit(c, out);
  CHECK(out.find("(declare-fun |len| () (_ BitVec 32))") != std::string::npos, "declares variables: " << out);
  CHECK(out.find("((_ sign_extend 32) |len|)") != std::string::npos, "sign_extend printed: " << out);
  CHECK(out.find("#x00000000000000ff") != std::string::npos, "hex literal for 64-bit constant: " << out);
  std::string again;
  CHECK(em.emit(c, again) == e && again.empty(), "second emit of the same term prints nothing new");
  em.push();
  TermRef y = tm.bvVar("y", 3);
  std::string o2;
  em.emit(tm.mkEq(y, tm.bvConst(3, 5)), o2);
  CHECK(o2.find("#b101") != std::string::npos, "odd widths use binary literals: " << o2);
  em.pop();
  std::string o3;
  em.emit(tm.mkEq(y, tm.bvConst(3, 5)), o3);
  CHECK(!o3.empty(), "after pop the scoped declarations are emitted again");
}

// ---------------------------------------------------------------- solver conformance
static void conformance(Solver &s, bool big) {
  const std::string who = s.name();
  TermManager tm;
  TermRef x = tm.bvVar("x", 8), y = tm.bvVar("y", 4);

  // basic sat / values
  s.push();
  s.assertTerm(tm.mkEq(tm.mkBin(Kind::BvAdd, x, tm.bvConst(8, 1)), tm.bvConst(8, 0)));
  CHECK(s.check() == SatResult::Sat, who << ": x+1==0 sat");
  CHECK(s.values({x})[0] == 255, who << ": x == 255");
  s.pop();

  // unsat with named assertions and a core
  s.push();
  s.assertTerm(tm.mkEq(tm.mkBin(Kind::BvAdd, x, tm.bvConst(8, 1)), tm.bvConst(8, 0)), "a1");
  s.assertTerm(tm.mkEq(x, tm.bvConst(8, 5)), "a2");
  s.assertTerm(tm.mkEq(y, tm.bvConst(4, 3)), "unrelated");
  CHECK(s.check() == SatResult::Unsat, who << ": contradiction is unsat");
  auto core = s.unsatCore();
  bool has1 = false, has2 = false, bad = false;
  for (auto &n : core) { has1 |= n == "a1"; has2 |= n == "a2"; bad |= (n != "a1" && n != "a2" && n != "unrelated"); }
  CHECK(has1 && has2 && !bad, who << ": core mentions the conflicting assertions");
  s.pop();

  // push/pop restores satisfiability; scoped declarations can be re-used
  s.push();
  s.assertTerm(tm.mkEq(x, tm.bvConst(8, 7)));
  CHECK(s.check() == SatResult::Sat, who << ": x==7");
  s.push();
  s.assertTerm(tm.mkEq(x, tm.bvConst(8, 8)));
  CHECK(s.check() == SatResult::Unsat, who << ": x==7 && x==8");
  s.pop();
  CHECK(s.check() == SatResult::Sat && s.values({x})[0] == 7, who << ": sat again after pop");
  s.pop();
  s.push();
  s.assertTerm(tm.mkEq(y, tm.bvConst(4, 9)));
  CHECK(s.check() == SatResult::Sat && s.values({y})[0] == 9, who << ": y==9 (4-bit, odd width)");
  s.pop();

  // a variable that no assertion mentions still has a value of the right width
  s.push();
  s.assertTerm(tm.boolConst(true));
  TermRef free = tm.bvVar("free", 5);
  CHECK(s.check() == SatResult::Sat, who << ": trivial sat");
  CHECK(s.values({free})[0].getBitWidth() == 5, who << ": unconstrained variable has a value");
  s.pop();

  // arithmetic semantics edge: division by zero is total
  s.push();
  s.assertTerm(tm.mkEq(y, tm.bvConst(4, 0)));
  s.assertTerm(tm.mkNot(tm.mkEq(tm.mkBin(Kind::BvUdiv, tm.bvConst(4, 5), y), tm.bvConst(4, 15))));
  CHECK(s.check() == SatResult::Unsat, who << ": 5 /u 0 == all-ones");
  s.pop();

  CHECK(s.lastError().empty(), who << ": no backend error: " << s.lastError());

  if (big) {
    TermRef a = tm.bvVar("a", 32), b = tm.bvVar("b", 64);
    s.push();
    s.assertTerm(tm.mkNot(tm.mkEq(tm.mkBin(Kind::BvAdd, a, a), tm.mkBin(Kind::BvMul, a, tm.bvConst(32, 2)))));
    CHECK(s.check() == SatResult::Unsat, who << ": a+a == a*2 for 32-bit a");
    s.pop();
    s.push();  // the int -> size_t sign-extension of DESIGN.md §19.9
    s.assertTerm(tm.mkNot(tm.mkCmp(Kind::Slt, tm.bvConst(32, 0x100), a)), "pc.small");
    s.assertTerm(tm.mkCmp(Kind::Ult, tm.bvConst(64, 256), tm.mkSExt(a, 64)), "ub.huge");
    CHECK(s.check() == SatResult::Sat, who << ": huge sign-extended size reachable");
    APInt v = s.values({a})[0];
    CHECK(v.isNegative(), who << ": witness is negative: " << v.getSExtValue());
    s.push();
    s.assertTerm(tm.mkNot(tm.mkCmp(Kind::Slt, a, tm.bvConst(32, 0))), "pc.nonneg");
    CHECK(s.check() == SatResult::Unsat, who << ": unsat once len >= 0 is known");
    auto c2 = s.unsatCore();
    CHECK(c2.size() == 3, who << ": core is exactly the three assertions, got " << c2.size());
    s.pop();
    s.pop();
    (void)b;
  }
}

static void testSolvers() {
  auto en = makeEnumSolver(20);
  conformance(*en, /*big=*/false);

  // Three-way conformance: EnumSolver (version-independent oracle, above), Z3Process, and Z3Native must all agree
  // on sat/unsat for the same fixed formulas in conformance() (the CHECK()s inside it hardcode the expected
  // SatResult per formula, so running the same function against all three backends already enforces agreement --
  // nothing additional needs to be diffed here). Z3Process and Z3Native are compared at the SAME libz3 version by
  // passing /usr/bin/z3 explicitly: on this machine $PATH resolves bare "z3" to a pip-installed 5.1.0 that does not
  // match the 4.8.12 libz3.so Z3Native links against (see lib/smt/Z3Native.cpp's VERSION NOTE), which would make any
  // disagreement impossible to attribute to a real bug vs. a version difference.
  auto z3 = makeZ3ProcessSolver("/usr/bin/z3", 10000);
  if (!z3) { std::cout << "  (z3 not available: z3-backed tests skipped)\n"; return; }
  conformance(*z3, /*big=*/true);

  auto native = makeZ3NativeSolver(10000);
  if (native) {
    conformance(*native, /*big=*/true);
  } else {
    std::cout << "  (Z3Native not built: HLIR_HAVE_Z3_NATIVE off, native conformance skipped)\n";
  }

  // Unknown handling: the enumeration backend must refuse problems that are too large
  auto tiny = makeEnumSolver(4);
  TermManager tm;
  tiny->assertTerm(tm.mkEq(tm.bvVar("p", 8), tm.bvConst(8, 1)));
  CHECK(tiny->check() == SatResult::Unknown, "enum solver gives up beyond its bit budget");
}

// ---------------------------------------------------------------- arrays
static void testArrays() {
  TermManager tm;
  TermRef a = tm.arrVar("a", 4, 8), i = tm.bvVar("i", 4), j = tm.bvVar("j", 4), v = tm.bvVar("v", 8);
  CHECK(tm.arrVar("a", 4, 8) == a, "array variables are interned");
  CHECK(tm.mkSelect(tm.mkStore(a, i, v), i) == v, "read-over-write at the same index");
  CHECK(tm.mkSelect(tm.mkStore(a, tm.bvConst(4, 1), v), tm.bvConst(4, 2)) == tm.mkSelect(a, tm.bvConst(4, 2)), "read-over-write at distinct constants");
  CHECK(tm.mkSelect(tm.mkConstArray(4, tm.bvConst(8, 9)), j) == tm.bvConst(8, 9), "read of a constant array");
  CHECK(tm.mkStore(tm.mkStore(a, i, v), i, tm.bvConst(8, 1)) == tm.mkStore(a, i, tm.bvConst(8, 1)), "overwritten store disappears");
  CHECK(tm.mkSelect(tm.mkStore(a, i, v), j)->kind == Kind::Select, "symbolic distinct indices stay a select");

  // evaluation against a reference model
  std::mt19937_64 rng(5);
  for (int round = 0; round < 200; ++round) {
    TermRef arr = tm.mkConstArray(4, tm.bvConst(8, rng() & 0xff));
    std::map<uint64_t, uint64_t> ref;
    uint64_t dflt = arr->args[0]->value.getZExtValue();
    for (int k = 0; k < 12; ++k) {
      uint64_t idx = rng() & 15, val = rng() & 0xff;
      arr = tm.mkStore(arr, tm.bvConst(4, idx), val == 0xfe ? tm.bvVar("v", 8) : tm.bvConst(8, val));
      ref[idx] = val == 0xfe ? 0x42 : val;
    }
    Assignment asg{{"v", ap(8, 0x42)}, {"i", ap(4, rng() & 15)}};
    uint64_t q = asg.at("i").getZExtValue();
    TermRef sel = tm.mkSelect(arr, tm.bvVar("i", 4));
    CHECK(evalTerm(sel, asg) == (ref.count(q) ? ref[q] : dflt), "array evaluation matches the reference model");
  }
  SmtLibEmitter em;
  std::string out;
  em.emit(tm.mkSelect(tm.mkStore(tm.mkConstArray(4, tm.bvConst(8, 0)), i, v), j), out);
  CHECK(out.find("(Array (_ BitVec 4) (_ BitVec 8))") != std::string::npos && out.find("(as const") != std::string::npos && out.find("(store ") != std::string::npos && out.find("(select ") != std::string::npos,
        "array printing: " << out);

  auto en = makeEnumSolver(20);
  en->assertTerm(tm.mkEq(tm.mkSelect(a, i), v));
  CHECK(en->check() == SatResult::Unknown, "the enumeration solver declines array problems");

  auto z3 = makeZ3ProcessSolver("z3", 10000);
  if (!z3) return;
  z3->push();  // store/select semantics, proved by z3
  TermRef lhs = tm.mkSelect(tm.mkStore(a, i, v), j);
  z3->assertTerm(tm.mkNot(tm.mkEq(lhs, tm.mkIte(tm.mkEq(i, j), v, tm.mkSelect(a, j)))));
  CHECK(z3->check() == SatResult::Unsat, "select(store(a,i,v),j) == (i==j ? v : select(a,j))");
  z3->pop();
  z3->push();  // models: values of select terms and of index expressions
  z3->assertTerm(tm.mkEq(tm.mkSelect(a, tm.bvConst(4, 3)), tm.bvConst(8, 7)));
  z3->assertTerm(tm.mkEq(i, tm.bvConst(4, 5)));
  CHECK(z3->check() == SatResult::Sat, "array model exists");
  auto vals = z3->values({tm.mkSelect(a, tm.bvConst(4, 3)), tm.mkBin(Kind::BvAdd, i, tm.bvConst(4, 1))});
  CHECK(vals[0] == 7 && vals[1] == 6, "values() evaluates arbitrary terms: " << vals[0].getZExtValue() << " " << vals[1].getZExtValue());
  z3->pop();
  CHECK(z3->lastError().empty(), "no backend error: " << z3->lastError());
}

// checkAssuming: assumption literals (inside a session) answer exactly like push/assert/check/pop, terms are kept across queries,
// and a second TermManager on the same solver does not see the first one's state.
static void testCheckAssuming() {
  auto z3 = makeZ3ProcessSolver("z3", 10000);
  CHECK(z3 != nullptr, "z3 available");
  if (!z3) return;
  for (int mgrRound = 0; mgrRound < 3; ++mgrRound) {
    TermManager tm;
    TermRef x = tm.bvVar("x", 8), y = tm.bvVar("y", 8);
    TermRef c1 = tm.mkCmp(Kind::Ult, x, tm.bvConst(8, 10));              // x < 10
    TermRef c2 = tm.mkEq(tm.mkBin(Kind::BvAdd, x, y), tm.bvConst(8, 12)); // x + y == 12
    TermRef c3 = tm.mkCmp(Kind::Ult, tm.bvConst(8, 20), y);              // y > 20
    z3->beginSession();
    for (int rep = 0; rep < 3; ++rep) {
      CHECK(z3->checkAssuming({c1, c2}) == SatResult::Sat, "x<10, x+y==12 is satisfiable (round " << mgrRound << ")");
      auto v = z3->values({x, y});
      CHECK(static_cast<uint8_t>(v[0].getZExtValue() + v[1].getZExtValue()) == 12 && v[0].getZExtValue() < 10, "the model satisfies the assumed terms");
      z3->endCheckAssuming();
      CHECK(z3->checkAssuming({c1, c2, c3}) == SatResult::Unsat, "x<10, y>20, x+y==12 (mod 256) has no solution: y would be 12-x, at most 12");
      z3->endCheckAssuming();
      CHECK(z3->checkAssuming({c1, tm.mkNot(c1)}) == SatResult::Unsat, "a term and its negation");
      z3->endCheckAssuming();
    }
    // the terms are still asserted at the top level only through their literals: a plain check() sees none of them
    z3->push();
    z3->assertTerm(tm.mkEq(x, tm.bvConst(8, 200)));
    CHECK(z3->check() == SatResult::Sat, "push/assert/check after literal queries is unaffected (c1 was only assumed)");
    z3->pop();
    z3->endSession();
    // a push-style query after the session with the same names must not clash with what the session declared
    z3->push();
    z3->assertTerm(tm.mkEq(x, tm.bvConst(8, 7)));
    CHECK(z3->check() == SatResult::Sat, "no clash after the session ended");
    z3->pop();
  }
  CHECK(z3->lastError().empty(), "no backend error: " << z3->lastError());
}

int main() {
  testHashConsing();
  testSimplifierSoundness();
  testEvalNative();
  testPrinter();
  testSolvers();
  testArrays();
  testCheckAssuming();
  std::cout << "smt_tests: " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}

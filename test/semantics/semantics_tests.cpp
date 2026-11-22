// Tests for the `semantics` module (concrete interpreter, P1):
//  1. directive-driven programs (`// RUN: @f(args) [env(k=v)] [mode=wrap|assume] => expectation`)
//  2. differential tests of every integer op against native C++ arithmetic (SMT-LIB conventions)
//  3. exhaustive i8 checks of every UB condition against a wider-integer oracle
#include <dirent.h>

#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>

#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/WriteSites.h"

using namespace hlir;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }
static std::string trim(std::string s) {
  while (!s.empty() && isspace(static_cast<unsigned char>(s.front()))) s.erase(s.begin());
  while (!s.empty() && isspace(static_cast<unsigned char>(s.back()))) s.pop_back();
  return s;
}

// ---------------------------------------------------------------- 1. directive files
static bool parseI64(const std::string &s, int64_t &v) {
  try {
    size_t n;
    if (s.rfind("0x", 0) == 0 || s.rfind("-0x", 0) == 0) { v = static_cast<int64_t>(std::stoull(s.rfind("-", 0) == 0 ? s.substr(3) : s.substr(2), &n, 16)); if (s[0] == '-') v = -v; return true; }
    v = std::stoll(s, &n, 10);
    return n == s.size();
  } catch (...) { return false; }
}

static void runDirective(const Module &mod, const std::string &file, const std::string &line) {
  // @f(a, b) [env(k=v,...)] [mode=wrap|assume] => expect
  auto arrow = line.find("=>");
  CHECK(arrow != std::string::npos, file << ": malformed RUN line: " << line);
  if (arrow == std::string::npos) return;
  std::string lhs = trim(line.substr(0, arrow)), expect = trim(line.substr(arrow + 2));
  CHECK(!lhs.empty() && lhs[0] == '@', file << ": RUN line must start with @func: " << line);
  auto lp = lhs.find('('), rp = lhs.find(')');
  std::string fn = lhs.substr(1, lp - 1);
  std::string argText = lhs.substr(lp + 1, rp - lp - 1), rest = lhs.substr(rp + 1);

  RunConfig cfg;
  TableEnv env;
  if (rest.find("mode=wrap") != std::string::npos) cfg.ub = UBMode::Wrap;
  if (rest.find("mode=assume") != std::string::npos) cfg.ub = UBMode::AssumeAbsent;
  auto ep = rest.find("env(");
  if (ep != std::string::npos) {
    std::string kvs = rest.substr(ep + 4, rest.find(')', ep) - ep - 4);
    std::stringstream ss(kvs);
    std::string kv;
    while (std::getline(ss, kv, ',')) {
      auto eq = kv.find('=');
      int64_t v = 0;
      parseI64(trim(kv.substr(eq + 1)), v);
      env.set(trim(kv.substr(0, eq)), v);
    }
  }
  if (expect == "steplimit") cfg.maxSteps = 10000;
  if (expect == "depthlimit") cfg.maxCallDepth = 50;

  const Function *f = mod.findFunction(fn);
  CHECK(f != nullptr, file << ": unknown function @" << fn);
  if (!f) return;
  std::vector<llvm::APInt> args;
  std::stringstream as(argText);
  std::string a;
  size_t i = 0;
  while (std::getline(as, a, ',')) {
    a = trim(a);
    if (a.empty()) continue;
    const Type *t = f->paramTys.at(i++);
    int64_t v = 0;
    if (a == "true") v = 1; else if (a == "false") v = 0; else CHECK(parseI64(a, v), file << ": bad argument " << a);
    args.emplace_back(t->isBool() ? 1 : t->width(), static_cast<uint64_t>(v), true);
  }
  RunResult r = Interpreter(mod).run(fn, args, env, cfg);
  std::string got = runStatusName(r.status);
  bool ok = false;
// A UB the engine deliberately WALKS PAST does not end the run, so `status == UB` is not the only shape of
// evidence that it happened: `ubContinued` records the site it walked past, and that is the same fact. This is
// the rule lib/semantics/Taint.cpp already uses to confirm findings (DESIGN.md §22.418); since
// ENGINE_LIMITATIONS.md §7.12 made every `ptr_arith_oob` continue, a test that only accepts the halt is
// asserting the old pre-emption, not the property.
  if (expect.rfind("ub:", 0) == 0)
    ok = (r.status == RunStatus::UB && r.ub && std::string(ubKindName(r.ub->kind)) == expect.substr(3)) ||
         std::any_of(r.ubContinued.begin(), r.ubContinued.end(),
                     [&](const std::string &k) { return k.rfind(expect.substr(3) + "@", 0) == 0; });
  else if (expect == "assert_failed") ok = r.status == RunStatus::AssertFailed;
  else if (expect == "infeasible") ok = r.status == RunStatus::Infeasible;
  else if (expect == "unsupported") ok = r.status == RunStatus::Unsupported;
  else if (expect == "steplimit") ok = r.status == RunStatus::StepLimit;
  else if (expect == "depthlimit") ok = r.status == RunStatus::DepthLimit;
  else if (expect == "void") ok = r.status == RunStatus::Returned && !r.returnValue;
  else if (expect == "true" || expect == "false") ok = r.status == RunStatus::Returned && r.returnValue && r.returnValue->getBoolValue() == (expect == "true");
  else {
    int64_t want = 0;
    CHECK(parseI64(expect, want), file << ": bad expectation " << expect);
    ok = r.status == RunStatus::Returned && r.returnValue && r.returnValue->getSExtValue() == llvm::APInt(r.returnValue->getBitWidth(), static_cast<uint64_t>(want), true).getSExtValue();
    if (r.returnValue) got += " " + std::to_string(r.returnValue->getSExtValue());
  }
  if (r.ub) got += std::string(" ") + ubKindName(r.ub->kind);
  CHECK(ok, file << ": `" << line << "` -> got " << got << (r.message.empty() ? "" : " (" + r.message + ")"));
}

static void runFile(const std::string &dir, const std::string &name) {
  std::string text = slurp(dir + "/" + name);
  Diagnostics d;
  auto mod = parseModule(text, name, d);
  CHECK(mod != nullptr && verifyModule(*mod, {}, d), name << ": " << d.str());
  if (!mod) return;
  std::istringstream in(text);
  std::string line;
  while (std::getline(in, line)) {
    auto p = line.find("// RUN:");
    if (p != std::string::npos) runDirective(*mod, name, trim(line.substr(p + 7)));
  }
}

// ---------------------------------------------------------------- 2. differential: ops vs native
template <class S> struct Ref {
  using U = std::make_unsigned_t<S>;
  static constexpr unsigned W = sizeof(S) * 8;
  static U udiv(U a, U b) { return b == 0 ? static_cast<U>(~U(0)) : static_cast<U>(a / b); }
  static U urem(U a, U b) { return b == 0 ? a : static_cast<U>(a % b); }
  static S sdiv(S a, S b) {
    if (b == 0) return a < 0 ? S(1) : S(-1);
    if (b == -1) return static_cast<S>(U(0) - static_cast<U>(a));
    return static_cast<S>(a / b);
  }
  static S srem(S a, S b) { return b == 0 ? a : (b == -1 ? S(0) : static_cast<S>(a % b)); }
  static U shl(U a, U s) { return s >= W ? U(0) : static_cast<U>(a << s); }
  static U lshr(U a, U s) { return s >= W ? U(0) : static_cast<U>(a >> s); }
  static S ashr(S a, U s) { return s >= W ? (a < 0 ? S(-1) : S(0)) : static_cast<S>(a >> s); }
};

static llvm::APInt ap(unsigned w, int64_t v) { return llvm::APInt(w, static_cast<uint64_t>(v), true); }

// Builds `i<w> f(i<w> a, i<w> b)` applying `opc`, or a comparison returning bool.
static std::unique_ptr<Module> makeBin(Opc opc, unsigned w, const std::string &pred = "") {
  auto m = std::make_unique<Module>();
  Context &c = m->ctx;
  Type *t = c.intTy(w);
  Function *f = m->addFunction("f", {t, t}, pred.empty() ? t : c.boolTy());
  Builder b(*m);
  b.setInsertionPoint(f->entry());
  Value *r = pred.empty() ? b.binop(opc, f->entry()->args[0].get(), f->entry()->args[1].get())
                          : b.icmp(pred, f->entry()->args[0].get(), f->entry()->args[1].get());
  b.ret(r);
  return m;
}

static llvm::APInt run2(const Module &m, unsigned w, int64_t a, int64_t b, bool *ok = nullptr) {
  TableEnv env;
  RunResult r = Interpreter(m).run("f", {ap(w, a), ap(w, b)}, env);
  if (ok) *ok = r.status == RunStatus::Returned;
  return r.returnValue ? *r.returnValue : llvm::APInt(1, 0);
}

template <class S> static void diffWidth() {
  using R = Ref<S>;
  using U = typename R::U;
  constexpr unsigned W = R::W;
  std::mt19937_64 rng(1234 + W);
  std::vector<int64_t> vals = {0, 1, -1, 2, -2, 3, 7, W - 1, W, W + 1, std::numeric_limits<S>::min(), std::numeric_limits<S>::max(),
                               std::numeric_limits<S>::min() + 1, std::numeric_limits<S>::max() - 1};
  for (int i = 0; i < 40; ++i) vals.push_back(static_cast<S>(rng()));

  struct BinCase { Opc opc; const char *name; S (*f)(S, S); };
  BinCase cases[] = {
      {Opc::Add, "add", [](S a, S b) { return static_cast<S>(static_cast<U>(a) + static_cast<U>(b)); }},
      {Opc::Sub, "sub", [](S a, S b) { return static_cast<S>(static_cast<U>(a) - static_cast<U>(b)); }},
      {Opc::Mul, "mul", [](S a, S b) { return static_cast<S>(static_cast<U>(a) * static_cast<U>(b)); }},
      {Opc::And, "and", [](S a, S b) { return static_cast<S>(a & b); }},
      {Opc::Or, "or", [](S a, S b) { return static_cast<S>(a | b); }},
      {Opc::Xor, "xor", [](S a, S b) { return static_cast<S>(a ^ b); }},
      {Opc::UDiv, "udiv", [](S a, S b) { return static_cast<S>(R::udiv(static_cast<U>(a), static_cast<U>(b))); }},
      {Opc::URem, "urem", [](S a, S b) { return static_cast<S>(R::urem(static_cast<U>(a), static_cast<U>(b))); }},
      {Opc::SDiv, "sdiv", [](S a, S b) { return R::sdiv(a, b); }},
      {Opc::SRem, "srem", [](S a, S b) { return R::srem(a, b); }},
      {Opc::Shl, "shl", [](S a, S b) { return static_cast<S>(R::shl(static_cast<U>(a), static_cast<U>(b))); }},
      {Opc::LShr, "lshr", [](S a, S b) { return static_cast<S>(R::lshr(static_cast<U>(a), static_cast<U>(b))); }},
      {Opc::AShr, "ashr", [](S a, S b) { return R::ashr(a, static_cast<U>(b)); }},
  };
  for (auto &bc : cases) {
    auto m = makeBin(bc.opc, W);
    for (int64_t a : vals)
      for (int64_t b : vals) {
        S sa = static_cast<S>(a), sb = static_cast<S>(b);
        llvm::APInt got = run2(*m, W, sa, sb);
        S want = bc.f(sa, sb);
        CHECK(got.getSExtValue() == static_cast<int64_t>(want), "i" << W << " " << bc.name << "(" << +sa << ", " << +sb << ") = " << got.getSExtValue() << ", want " << +want);
      }
  }
  struct CmpCase { const char *p; bool (*f)(S, S); };
  CmpCase cmps[] = {
      {"eq", [](S a, S b) { return a == b; }}, {"ne", [](S a, S b) { return a != b; }},
      {"slt", [](S a, S b) { return a < b; }}, {"sle", [](S a, S b) { return a <= b; }},
      {"sgt", [](S a, S b) { return a > b; }}, {"sge", [](S a, S b) { return a >= b; }},
      {"ult", [](S a, S b) { return static_cast<U>(a) < static_cast<U>(b); }}, {"ule", [](S a, S b) { return static_cast<U>(a) <= static_cast<U>(b); }},
      {"ugt", [](S a, S b) { return static_cast<U>(a) > static_cast<U>(b); }}, {"uge", [](S a, S b) { return static_cast<U>(a) >= static_cast<U>(b); }},
  };
  for (auto &cc : cmps) {
    auto m = makeBin(Opc::ICmp, W, cc.p);
    for (int64_t a : vals)
      for (int64_t b : vals) {
        S sa = static_cast<S>(a), sb = static_cast<S>(b);
        CHECK(run2(*m, W, sa, sb).getBoolValue() == cc.f(sa, sb), "i" << W << " icmp " << cc.p << "(" << +sa << ", " << +sb << ")");
      }
  }
}

static void testUnaryAndCasts() {
  // neg / not / ext / trunc / extract / concat / select, i32 <-> i8 <-> i64
  Module m;
  Context &c = m.ctx;
  Function *f = m.addFunction("f", {c.intTy(32)}, c.intTy(64));
  Builder b(m);
  b.setInsertionPoint(f->entry());
  Value *a = f->entry()->args[0].get();
  Value *t8 = b.cast(Opc::Trunc, a, c.intTy(8));
  Value *s64 = b.cast(Opc::SExt, t8, c.intTy(64));
  Value *z64 = b.cast(Opc::ZExt, t8, c.intTy(64));
  Value *x = b.binop(Opc::Xor, s64, z64);  // nonzero iff the low byte is negative
  Value *n = b.unop(Opc::Neg, b.unop(Opc::Not, x));
  b.ret(n);
  Diagnostics d;
  CHECK(verifyModule(m, {}, d), d.str());
  TableEnv env;
  for (int64_t v : {0, 1, 127, 128, 255, 256, -1, -128, -129, 0x7fffffff}) {
    RunResult r = Interpreter(m).run("f", {ap(32, v)}, env);
    int8_t lo = static_cast<int8_t>(v);
    int64_t sx = lo, zx = static_cast<uint8_t>(lo);
    int64_t want = -(~(sx ^ zx));
    CHECK(r.status == RunStatus::Returned && r.returnValue->getSExtValue() == want, "unary/cast chain v=" << v);
  }
}

// ---------------------------------------------------------------- 3. exhaustive i8 UB conditions
static std::unique_ptr<Module> makeCheck(Opc chk, Opc op, bool withSigned, bool signedLeft) {
  auto m = std::make_unique<Module>();
  Context &c = m->ctx;
  Type *t = c.intTy(8);
  bool unary = chk == Opc::CheckSNegOvf;
  Function *f = m->addFunction("f", unary ? std::vector<Type *>{t} : std::vector<Type *>{t, t}, t);
  Builder b(*m);
  b.setInsertionPoint(f->entry());
  Value *a = f->entry()->args[0].get();
  Value *s = unary ? nullptr : f->entry()->args[1].get();
  Op *ck = b.check(chk, unary ? std::vector<Value *>{a} : std::vector<Value *>{a, s});
  if (withSigned) ck->setAttr("signed", Attr::boolean(true));
  if (signedLeft) ck->setAttr("signed_left", Attr::boolean(true));
  Value *r = unary ? b.unop(op, a) : b.binop(op, a, s);
  b.ret(r);
  return m;
}

static void testExhaustiveUB() {
  struct Case { const char *name; Opc chk, op; bool sgn, sl; };
  Case cases[] = {{"sadd", Opc::CheckSAddOvf, Opc::Add, false, false}, {"ssub", Opc::CheckSSubOvf, Opc::Sub, false, false},
                  {"smul", Opc::CheckSMulOvf, Opc::Mul, false, false}, {"sneg", Opc::CheckSNegOvf, Opc::Neg, false, false},
                  {"udivchk", Opc::CheckDiv, Opc::UDiv, false, false}, {"sdivchk", Opc::CheckDiv, Opc::SDiv, true, false},
                  {"shlrange", Opc::CheckShift, Opc::Shl, false, false}, {"shlsigned", Opc::CheckShift, Opc::Shl, false, true}};
  for (auto &cs : cases) {
    auto m = makeCheck(cs.chk, cs.op, cs.sgn, cs.sl);
    Diagnostics d;
    VerifyOptions vo;
    vo.checkCoverage = true;
    CHECK(verifyModule(*m, vo, d), cs.name << ": generated module must verify with coverage: " << d.str());
    bool unary = cs.chk == Opc::CheckSNegOvf;
    TableEnv env;
    for (int a = -128; a <= 127; ++a)
      for (int b = unary ? 0 : -128; b <= (unary ? 0 : 127); ++b) {
        std::vector<llvm::APInt> args = {ap(8, a)};
        if (!unary) args.push_back(ap(8, b));
        RunResult r = Interpreter(*m).run("f", args, env);
        // oracle with wider integers
        std::string want = "";
        std::string nm = cs.name;
        if (nm == "sadd") { int x = a + b; if (x < -128 || x > 127) want = "signed_overflow"; }
        else if (nm == "ssub") { int x = a - b; if (x < -128 || x > 127) want = "signed_overflow"; }
        else if (nm == "smul") { int x = a * b; if (x < -128 || x > 127) want = "signed_overflow"; }
        else if (nm == "sneg") { if (a == -128) want = "signed_overflow"; }
        else if (nm == "udivchk") { if (b == 0) want = "div_by_zero"; }
        else if (nm == "sdivchk") { if (b == 0) want = "div_by_zero"; else if (a == -128 && b == -1) want = "div_overflow"; }
        else if (nm == "shlrange") { if (static_cast<uint8_t>(b) >= 8) want = "shift_range"; }
        else if (nm == "shlsigned") {
          if (static_cast<uint8_t>(b) >= 8) want = "shift_range";
          else if (a < 0) want = "shift_negative";
          else { int x = a * (1 << static_cast<uint8_t>(b)); if (x > 127) want = "shift_overflow"; }
        }
        std::string got = r.status == RunStatus::UB ? ubKindName(r.ub->kind) : (r.status == RunStatus::Returned ? "" : runStatusName(r.status));
        CHECK(got == want, nm << "(" << a << ", " << b << "): got '" << got << "', want '" << want << "'");
      }
  }
}

// ---------------------------------------------------------------- misc API behaviour
static void testApi() {
  Diagnostics d;
  auto mod = parseModule("core.func @f(i32) -> i32 {\n^entry(%a: i32):\n  core.return %a\n}\ncore.declare @e() -> void\n", "api", d);
  TableEnv env;
  Interpreter in(*mod);
  CHECK(in.run("nope", {}, env).status == RunStatus::BadInput, "unknown function");
  CHECK(in.run("e", {}, env).status == RunStatus::BadInput, "declaration has no body");
  CHECK(in.run("f", {}, env).status == RunStatus::BadInput, "wrong arg count");
  CHECK(in.run("f", {llvm::APInt(8, 1)}, env).status == RunStatus::BadInput, "wrong arg width");
  RunResult ok = in.run("f", {ap(32, 41)}, env);
  CHECK(ok.status == RunStatus::Returned && ok.returnValue->getSExtValue() == 41, "identity");

  // trace + UB report details
  auto m2 = parseModule(
      "core.func @g(i32) -> i32 {\n^entry(%a: i32):\n  %z = core.const 0 : i32\n"
      "  core.check.div %a, %z {origin=\"hl.binop sdiv\"} loc(\"x.c\":12:5)\n  %q = core.udiv %a, %z : i32\n  core.return %q\n}\n", "api2", d);
  RunConfig cfg;
  cfg.trace = true;
  RunResult r = Interpreter(*m2).run("g", {ap(32, 9)}, env, cfg);
  CHECK(r.status == RunStatus::UB && r.ub && r.ub->kind == UBKind::DivByZero, "div by zero reported");
  if (r.ub) {
    CHECK(r.ub->loc.file == "x.c" && r.ub->loc.line == 12 && r.ub->loc.col == 5, "UB report carries the op's location");
    CHECK(r.ub->origin == "hl.binop sdiv", "UB report carries origin");
    CHECK(r.ub->function == "g" && r.ub->block == "entry", "UB report names function and block");
    CHECK(r.ub->detail == "operands: 9, 0", "UB report lists operand values: " << r.ub->detail);
  }
  CHECK(!r.trace.empty() && r.trace.front().kind == TraceEvent::Call, "trace starts with the entry call");
  UBKind k;
  CHECK(ubKindFromName("use_after_free", k) && k == UBKind::UseAfterFree, "ub kind names round-trip");
}

// ---------------------------------------------------------------- RunConfig::memExpandMax (kMaxExpand gap, P2)
// Memory.h's bulk() refuses to physically expand a core.memcpy/core.memset whose length (even when it is a
// compile-time constant, not just an unrolled symbolic one) exceeds Memory::kMaxExpandDefault (1<<20): it reports
// RunStatus::Unsupported instead. RunConfig::memExpandMax makes that cap configurable; its default must reproduce
// the old hardcoded behaviour exactly, and a caller that opts in by raising it must get a real (non-Unsupported)
// verdict for a length that would otherwise be refused.
static void testMemExpandMax() {
  // One constant-length memcpy of kMaxExpandDefault+1 bytes between two equally sized buffers. The over-the-cap
  // check in bulk() runs before the (count-bounded) per-byte copy loop, so this stays cheap even at the real
  // 1<<20 boundary: no million-iteration loop is exercised by the default (rejected) case below.
  constexpr uint64_t kOverCap = (1ull << 20) + 1;  // Memory::kMaxExpandDefault + 1
  std::string src = "core.func @big_memcpy(i32) -> i32 {\n^entry(%x: i32):\n"
                     "  %a = core.alloca {size=" + std::to_string(kOverCap) + ", align=1} : ptr\n"
                     "  %b = core.alloca {size=" + std::to_string(kOverCap) + ", align=1} : ptr\n"
                     "  %n = core.const " + std::to_string(kOverCap) + " : i64\n"
                     "  core.memcpy %b, %a, %n\n"
                     "  core.return %x\n}\n";
  Diagnostics d;
  auto mod = parseModule(src, "memexpand", d);
  CHECK(mod && !d.hasErrors(), "memExpandMax test module parses: " << d.str());
  if (!mod) return;
  TableEnv env;
  Interpreter in(*mod);

  // Default config: behaviour must be unchanged from the old hardcoded kMaxExpand -- a length one byte over the
  // cap is refused.
  RunResult r0 = in.run("big_memcpy", {llvm::APInt(32, 7)}, env);
  CHECK(r0.status == RunStatus::Unsupported, "default memExpandMax (1<<20): over-cap memcpy reports Unsupported, got " << runStatusName(r0.status));

  // Opt-in override: raising RunConfig::memExpandMax lets the same call expand and the run complete normally.
  RunConfig cfgBig;
  cfgBig.memExpandMax = kOverCap;
  RunResult r1 = in.run("big_memcpy", {llvm::APInt(32, 7)}, env, cfgBig);
  CHECK(r1.status == RunStatus::Returned && r1.returnValue && r1.returnValue->getZExtValue() == 7,
        "memExpandMax raised to " << kOverCap << ": over-cap memcpy now completes normally, got " << runStatusName(r1.status));

  // A config that leaves memExpandMax at its struct default (no override at all) must behave identically to the
  // explicit default-config run above -- i.e. the field's own default must equal the old hardcoded constant.
  RunConfig cfgDefault;
  RunResult r2 = in.run("big_memcpy", {llvm::APInt(32, 7)}, env, cfgDefault);
  CHECK(r2.status == RunStatus::Unsupported, "RunConfig{} (no override) still rejects the over-cap memcpy, got " << runStatusName(r2.status));

  // Sanity: a well-under-the-cap memcpy with the raised config still behaves normally too (no off-by-one from the
  // new field at the boundary).
  RunConfig cfgBig2;
  cfgBig2.memExpandMax = kOverCap;
  std::string src2 = "core.func @small_memcpy(i32) -> i32 {\n^entry(%x: i32):\n"
                      "  %a = core.alloca {size=4, align=4} : ptr\n  %b = core.alloca {size=4, align=4} : ptr\n"
                      "  core.store %x, %a\n  %four = core.const 4 : i64\n  core.memcpy %b, %a, %four\n"
                      "  %v = core.load %b : i32\n  core.return %v\n}\n";
  auto mod2 = parseModule(src2, "memexpand_small", d);
  CHECK(mod2 && !d.hasErrors(), "small memcpy test module parses");
  if (mod2) {
    Interpreter in2(*mod2);
    RunResult rs = in2.run("small_memcpy", {llvm::APInt(32, 258)}, env, cfgBig2);
    CHECK(rs.status == RunStatus::Returned && rs.returnValue && rs.returnValue->getZExtValue() == 258,
          "small memcpy unaffected by a raised memExpandMax, got " << runStatusName(rs.status));
  }
}

// ---------------------------------------------------------------- RunConfig::detectNonTermination (docs/DESIGN.md
// Sec.22.325/22.326): a loop header revisited with its branch decisions' entire dependency set unwritten, and no
// new core.nondet drawn, since the previous visit proves the next iteration replays identically (step-1 prototype:
// purely diagnostic, never changes `status`).
static void testDetectNonTermination() {
  Diagnostics d;
  // @spin(x): while (a == 0) { counter++; } where `a` is never written inside the loop -- a genuine zero-progress
  // infinite loop when called with x=0 (the loop body only ever touches `counter`, irrelevant to the guard).
  auto spin = parseModule(
      "core.func @spin(i32) -> i32 {\n"
      "^entry(%x: i32):\n"
      "  %pa = core.alloca {size=4, align=4} : ptr\n"
      "  core.store %x, %pa\n"
      "  %pc = core.alloca {size=4, align=4} : ptr\n"
      "  %z0 = core.const 0 : i32\n"
      "  core.store %z0, %pc\n"
      "  core.br ^head\n"
      "^head:\n"
      "  %a = core.load %pa : i32\n"
      "  %z1 = core.const 0 : i32\n"
      "  %cond = core.icmp eq %a, %z1 : bool\n"
      "  core.cond_br %cond, ^body, ^exit\n"
      "^body:\n"
      "  %c = core.load %pc : i32\n"
      "  %one = core.const 1 : i32\n"
      "  %c2 = core.add %c, %one : i32\n"
      "  core.store %c2, %pc\n"
      "  core.br ^head\n"
      "^exit:\n"
      "  %r = core.load %pc : i32\n"
      "  core.return %r\n"
      "}\n",
      "spin", d);
  CHECK(spin && !d.hasErrors(), "spin module parses: " << d.str());
  // @countdown(x): while (n != 0) { n--; } -- a genuinely terminating loop whose guard variable `n` IS written
  // every iteration; the negative control (must never be flagged, and must actually terminate, not hit StepLimit).
  auto countdown = parseModule(
      "core.func @countdown(i32) -> i32 {\n"
      "^entry(%x: i32):\n"
      "  %pn = core.alloca {size=4, align=4} : ptr\n"
      "  core.store %x, %pn\n"
      "  core.br ^head\n"
      "^head:\n"
      "  %n = core.load %pn : i32\n"
      "  %z = core.const 0 : i32\n"
      "  %cond = core.icmp eq %n, %z : bool\n"
      "  core.cond_br %cond, ^exit, ^body\n"
      "^body:\n"
      "  %n2 = core.load %pn : i32\n"
      "  %one = core.const 1 : i32\n"
      "  %n3 = core.sub %n2, %one : i32\n"
      "  core.store %n3, %pn\n"
      "  core.br ^head\n"
      "^exit:\n"
      "  core.return %n\n"
      "}\n",
      "countdown", d);
  CHECK(countdown && !d.hasErrors(), "countdown module parses: " << d.str());
  if (!spin || !countdown) return;
  TableEnv env;

  // Positive: detectNonTermination on, a genuine zero-progress loop -> proven, and the run is cut by max-steps
  // (not an infinite hang of the test itself).
  RunConfig cfgOn;
  cfgOn.detectNonTermination = true;
  cfgOn.maxSteps = 500;
  RunResult rSpinOn = Interpreter(*spin).run("spin", {ap(32, 0)}, env, cfgOn);
  CHECK(rSpinOn.status == RunStatus::StepLimit, "spin(0) with detection on still runs to the step limit (diagnostic-only, status unchanged), got " << runStatusName(rSpinOn.status));
  CHECK(rSpinOn.zeroProgressLoopObserved, "spin(0): zero-progress loop proven");
  CHECK(rSpinOn.zeroProgressLoopFunction == "spin" && rSpinOn.zeroProgressLoopHeader == "head",
        "spin(0): reported function/header are the real ones, got @" << rSpinOn.zeroProgressLoopFunction << " ^" << rSpinOn.zeroProgressLoopHeader);

  // Flag off (RunConfig{} default): identical status, but the new field must stay unset -- same input, only the
  // diagnostic is disabled.
  RunConfig cfgOff;
  cfgOff.maxSteps = 500;
  RunResult rSpinOff = Interpreter(*spin).run("spin", {ap(32, 0)}, env, cfgOff);
  CHECK(rSpinOff.status == RunStatus::StepLimit, "spin(0) with detection off: same status as with it on");
  CHECK(!rSpinOff.zeroProgressLoopObserved, "spin(0) with detection off: field stays unset (opt-in, zero behaviour change by default)");

  // Negative control: a loop that DOES make real progress on the guard's own dependency must never be flagged,
  // and must actually terminate (not hit the step limit) -- confirms recordWrite()/collectDeps() correctly see the
  // write to `n` and do not spuriously treat the countdown as zero-progress.
  RunResult rCd = Interpreter(*countdown).run("countdown", {ap(32, 50)}, env, cfgOn);
  CHECK(rCd.status == RunStatus::Returned && rCd.returnValue && rCd.returnValue->getZExtValue() == 0,
        "countdown(50) actually terminates with the real result, got " << runStatusName(rCd.status));
  CHECK(!rCd.zeroProgressLoopObserved, "countdown(50): a genuinely progressing loop is never flagged");
}

// ---------------------------------------------------------------- hlir::findWriteSites (docs/DESIGN.md
// Sec.22.326-22.328, docs/LLM_ASSISTED_TRIAGE_DESIGN.md Sec.3.3b): reaching-definitions-style candidate
// write-site search, cross-function via direct core.call edges, offsets compared structurally (not just
// constants). `entry_fn` allocates a local struct-like object, writes its own field #4 once, then calls
// `write_field(s)` (passing the whole object through unchanged, mirroring how brotli's `BrotliDecoderState* s`
// threads through DecodeXxxBlockSwitch -> ...Internal -> DecodeBlockTypeAndLength, Sec.22.322), which writes the
// SAME field #4 from inside a different function. The anchor is the load right before `entry_fn`'s own return.
static void testFindWriteSites() {
  Diagnostics d;
  auto mod = parseModule(
      "core.func @entry_fn(i32) -> i32 {\n"
      "^entry(%x: i32):\n"
      "  %s = core.alloca {size=8, align=4} : ptr\n"
      "  %z = core.const 0 : i32\n"
      "  %off0 = core.const 4 : i64\n"
      "  %fp0 = core.ptr_add %s, %off0 : ptr\n"
      "  core.store %z, %fp0\n"
      "  core.call @write_field(%s)\n"
      "  %off1 = core.const 4 : i64\n"
      "  %fp1 = core.ptr_add %s, %off1 : ptr\n"
      "  %v = core.load %fp1 : i32\n"
      "  core.return %v\n"
      "}\n"
      "core.func @write_field(ptr) -> void {\n"
      "^entry(%s: ptr):\n"
      "  %off = core.const 4 : i64\n"
      "  %p = core.ptr_add %s, %off : ptr\n"
      "  %c = core.const 42 : i32\n"
      "  core.store %c, %p\n"
      "  core.return\n"
      "}\n",
      "writesites", d);
  CHECK(mod && !d.hasErrors(), "findWriteSites test module parses: " << d.str());
  if (!mod) return;
  const Function *entryFn = mod->findFunction("entry_fn");
  CHECK(entryFn, "entry_fn found");
  if (!entryFn) return;

  // The anchor: the address operand of the last core.load in entry_fn's entry block (%fp1, feeding its own
  // return value) -- found structurally, not by hardcoding a Value* the test can't otherwise obtain.
  const Value *anchorAddr = nullptr;
  for (auto &op : entryFn->entry()->ops)
    if (op->opc == Opc::Load && !op->operands.empty()) anchorAddr = op->operands[0];
  CHECK(anchorAddr, "anchor load found in entry_fn");
  if (!anchorAddr) return;

  auto sites = findWriteSites(*mod, *entryFn, anchorAddr);
  CHECK(sites.size() == 2, "findWriteSites finds exactly 2 candidates (one local, one cross-function), got " << sites.size());
  bool sawLocal = false, sawCrossFn = false;
  for (auto &s : sites) {
    if (s.fn == entryFn) sawLocal = true;
    if (s.fn && s.fn->name == "write_field") sawCrossFn = true;
  }
  CHECK(sawLocal, "findWriteSites finds the write inside entry_fn itself");
  CHECK(sawCrossFn, "findWriteSites follows the direct call and finds the write inside write_field");

  // Negative control: a target offset that is never written anywhere reachable (offset 0 of the same object) must
  // come back empty, not a false positive.
  const Value *neverWrittenAddr = nullptr;
  for (auto &op : entryFn->entry()->ops)
    if (op->opc == Opc::Alloca) neverWrittenAddr = op->result.get();  // offset 0 of %s itself: never stored to
  CHECK(neverWrittenAddr, "alloca found in entry_fn");
  if (neverWrittenAddr) {
    auto none = findWriteSites(*mod, *entryFn, neverWrittenAddr);
    CHECK(none.empty(), "findWriteSites: offset 0 of %s (never written) correctly comes back empty, got " << none.size());
  }
}

// ---------------------------------------------------------------- RunConfig::captureRegs (--entries registered)
// The discovery mechanism behind `--entries registered`: run the module's
// `main`, and at a registration call capture the dispatch table it is handed, resolving each slot's function
// pointer back to the handler's name. Here `main` writes @io_devctl into byte offset 24 of a table and passes
// that table as argument 6 of @resmgr_attach; the capture must report io_devctl@24. bestEffortInit lets the
// unmodelled @resmgr_attach be a no-op so the run reaches it without a model.
static void testRegisteredCapture() {
  const char *ir =
      "core.declare @resmgr_attach(ptr, ptr, ptr, i32, i32, ptr, ptr, ptr) -> i32\n"
      "core.func @io_devctl(ptr, ptr, ptr) -> i32 {\n"
      "^entry(%a: ptr, %b: ptr, %c: ptr):\n"
      "  %z = core.const 0 : i32\n"
      "  core.return %z\n"
      "}\n"
      "core.func @main() -> i32 {\n"
      "^entry:\n"
      "  %iof = core.alloca {size=64} : ptr\n"
      "  %fp = core.func_addr @io_devctl : ptr\n"
      "  %off = core.const 24 : i64\n"
      "  %slot = core.ptr_add %iof, %off : ptr\n"
      "  core.store %fp, %slot\n"
      "  %n0 = core.const 0 : i32\n"
      "  %r = core.call @resmgr_attach(%iof, %iof, %iof, %n0, %n0, %iof, %iof, %iof) : i32\n"
      "  core.return %r\n"
      "}\n";
  Diagnostics d;
  auto mod = parseModule(ir, "regcap", d);
  CHECK(mod && verifyModule(*mod, {}, d), "regcap module parses: " << d.str());
  if (!mod) return;
  std::vector<RunConfig::RegCapture> regs = {{"resmgr_attach", 6, 64}};
  std::vector<RunConfig::CapturedReg> sink;
  RunConfig cfg;
  cfg.bestEffortInit = true;
  cfg.captureRegs = &regs;
  cfg.capturedRegs = &sink;
  TableEnv env;
  Interpreter(*mod).run("main", {}, env, cfg);
  CHECK(sink.size() == 1, "capture: exactly one registration call seen, got " << sink.size());
  bool found = false;
  if (!sink.empty()) {
    CHECK(sink[0].function == "resmgr_attach", "capture: from resmgr_attach, got " << sink[0].function);
    for (auto &h : sink[0].handlers)
      if (h.first == 24 && h.second == "io_devctl") found = true;
  }
  CHECK(found, "capture: io_devctl resolved at table offset 24");
}

int main() {
  std::vector<std::string> files;
  if (DIR *dir = opendir(HLIR_TEST_DIR)) {
    while (auto *e = readdir(dir)) {
      std::string n = e->d_name;
      if (n.size() > 5 && n.substr(n.size() - 5) == ".core") files.push_back(n);
    }
    closedir(dir);
  }
  std::sort(files.begin(), files.end());
  for (auto &n : files) runFile(HLIR_TEST_DIR, n);
  testApi();
  diffWidth<int8_t>();
  diffWidth<int16_t>();
  diffWidth<int32_t>();
  diffWidth<int64_t>();
  testUnaryAndCasts();
  testExhaustiveUB();
  testMemExpandMax();
  testDetectNonTermination();
  testFindWriteSites();
  testRegisteredCapture();
  std::cout << "directive files: " << files.size() << ", checks passed: " << g_pass << ", failed: " << g_fail << "\n";
  return g_fail ? 1 : 0;
}

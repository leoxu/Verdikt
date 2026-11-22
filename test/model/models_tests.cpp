// Tests for ModelDB and taint_transfer (P8-lite): YAML loading and diagnostics, concrete semantics of modelled functions,
// attacker-controlled sources, taint flow / clearing / copies, sinks, and agreement between the three engines.
#include <algorithm>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>

#include "hlir/driver/Pipeline.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/model/Model.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/Symbolic.h"
#include "hlir/semantics/Taint.h"

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
static model::ModelDB g_db;

static std::unique_ptr<Module> load(const std::string &text, const std::string &name) {
  Diagnostics d;
  auto m = parseModule(text, name, d);
  if (!m || d.hasErrors() || !verifyModule(*m, {}, d)) { std::cerr << "cannot load " << name << ":\n" << d.str() << "\n"; std::exit(2); }
  return m;
}

static std::set<std::string> kinds(const std::vector<SymFinding> &fs, bool onlyConfirmed = false) {
  std::set<std::string> s;
  for (auto &f : fs) {
    if (f.ub && ubKindIsWarning(f.ub->kind)) continue;  // UB / sink findings only; DoS warnings are checked separately
    if (!onlyConfirmed || (f.confirmed && *f.confirmed)) s.insert(f.ub ? ubKindName(f.ub->kind) : "assert");
  }
  return s;
}

// ---------------------------------------------------------------- loading and diagnostics
static void testLoading() {
  Diagnostics d;
  model::ModelDB db;
  CHECK(db.load(slurp(HLIR_MODELS_DIR "/libc.yaml"), "libc.yaml", d), "the shipped model file loads: " << d.str());
  CHECK(db.size() >= 10 && db.lookup("recv") && db.lookup("strcpy") && db.lookup("system") && !db.lookup("nonexistent"), "lookup by function name");
  const model::CallModel *recv = db.lookup("recv");
  CHECK(recv && recv->ret.kind == model::ReturnSpec::Nondet && recv->ret.taintLabel == "network" && recv->sources.size() == 1 &&
            recv->sources[0].ptr.kind == model::Ref::Arg && recv->sources[0].ptr.index == 1 && recv->sources[0].size.kind == model::Size::Ret,
        "recv: tainted result, source into arg1 of size ret");
  const model::CallModel *cp = db.lookup("strcpy");
  CHECK(cp && cp->copies.size() == 1 && cp->copies[0].size.kind == model::Size::StrlenPlus1 && cp->copies[0].size.index == 1 && cp->ret.kind == model::ReturnSpec::Arg, "strcpy: copy of strlen(arg1)+1, returns arg0");

  auto bad = [&](const std::string &yaml, const std::string &needle, unsigned line) {
    Diagnostics dd;
    model::ModelDB x;
    bool ok = x.load(yaml, "m.yaml", dd);
    bool found = false;
    for (auto &dg : dd.all()) found |= dg.message.find(needle) != std::string::npos && (!line || dg.loc.line == line);
    CHECK(!ok && found, "expected '" << needle << "' at line " << line << ", got: " << dd.str());
  };
  bad("models:\n  - function: f\n    sorce: []\n", "unknown key 'sorce'", 3);
  bad("models:\n  - function: f\n    source: [ { label: n, ptr: arg1, size: banana } ]\n", "bad size 'banana'", 3);
  bad("models:\n  - function: f\n    copy: [ { dst: arg0, src: nope, size: 4 } ]\n", "bad reference 'nope'", 3);
  bad("models:\n  - function: f\n    sink: [ { kind: x, arg: ret } ]\n", "sink.arg must be argK", 3);
  bad("models:\n  - function: f\n  - function: f\n", "duplicate model for 'f'", 3);
  bad("models:\n  - note: no function\n", "no 'function'", 2);
  bad("models:\n  - function: f\n    returns: { nondet: { min: arg0_pointee } }\n", "min/max/default must be", 3);
  bad("models: 3\n", "'models' must be a list", 1);
  CHECK(g_db.load(slurp(HLIR_MODELS_DIR "/libc.yaml"), "libc.yaml", d), "shared db");
  CHECK(g_db.load("models:\n  - function: sanitize_len\n    returns: { arg: 0 }\n    flow: [ { clear: ret } ]\n  - function: escape_shell\n    returns: { arg: 0 }\n    flow: [ { clear: ret_pointee, size: strlen(arg0)+1 } ]\n", "extra.yaml", d), "extra models: " << d.str());
}

// ---------------------------------------------------------------- concrete semantics of modelled calls
static void testConcrete() {
  const char *text = R"(
core.declare @recv(i32, ptr, i64, i32) -> i64
core.declare @strlen(ptr) -> i64
core.declare @strcpy(ptr, ptr) -> ptr
core.declare @memset(ptr, i32, i64) -> ptr
core.declare @memcpy(ptr, ptr, i64) -> ptr
core.declare @getenv(ptr) -> ptr
core.func @recv_second_byte() -> i32 {
^entry:
  %buf = core.alloca {size=16} : ptr
  %fd = core.const 3 : i32
  %len = core.const 16 : i64
  %fl = core.const 0 : i32
  %n = core.call @recv(%fd, %buf, %len, %fl) : i64
  %one = core.const 1 : i64
  %q = core.ptr_add %buf, %one : ptr
  %b = core.load %q : i8
  %w = core.zext %b : i32
  %nn = core.trunc %n : i32
  %hundred = core.const 100 : i32
  %t = core.mul %nn, %hundred : i32
  %r = core.add %w, %t : i32
  core.return %r
}
core.func @copy_and_measure() -> i64 {
^entry:
  %src = core.alloca {size=8} : ptr
  %dst = core.alloca {size=8} : ptr
  %zero = core.const 0 : i32
  %eight = core.const 8 : i64
  %m1 = core.call @memset(%src, %zero, %eight) : ptr
  %m2 = core.call @memset(%dst, %zero, %eight) : ptr
  %a = core.const 104 : i8
  %b = core.const 105 : i8
  %one = core.const 1 : i64
  %p1 = core.ptr_add %src, %one : ptr
  core.store %a, %src
  core.store %b, %p1
  %c = core.call @strcpy(%dst, %src) : ptr
  %n = core.call @strlen(%dst) : i64
  %p = core.call @memcpy(%dst, %src, %one) : ptr
  return_marker:
  core.return %n
}
)";
  // (the stray label above is removed below; kept simple by building the module from two functions)
  std::string t(text);
  t.erase(t.find("  return_marker:\n"), std::string("  return_marker:\n").size());
  auto m = load(t, "concrete");
  Interpreter in(*m);
  RunConfig cfg;
  cfg.models = &g_db;
  {
    // the environment decides what recv returns (3) and which bytes arrive: 7, 9, 11
    SeqEnv env({}, {{"in.recv#0.ret", APInt(64, 3)}, {"in.recv#0.s0+0", APInt(8, 7)}, {"in.recv#0.s0+1", APInt(8, 9)}, {"in.recv#0.s0+2", APInt(8, 11)}});
    RunResult r = in.run("recv_second_byte", {}, env, cfg);
    CHECK(r.status == RunStatus::Returned && r.returnValue && r.returnValue->getSExtValue() == 9 + 300, "recv fills the buffer from the environment: " << (r.returnValue ? r.returnValue->getSExtValue() : -1) << " " << r.message);
    // bytes beyond the returned count stay uninitialised (0 here)
    SeqEnv env2({}, {{"in.recv#0.ret", APInt(64, 1)}, {"in.recv#0.s0+0", APInt(8, 7)}, {"in.recv#0.s0+1", APInt(8, 99)}});
    RunResult r2 = in.run("recv_second_byte", {}, env2, cfg);
    CHECK(r2.status == RunStatus::Returned && r2.returnValue->getSExtValue() == 0 + 100, "only `ret` bytes are written");
    // the result is bounded by the length argument: a larger value is infeasible
    SeqEnv env3({}, {{"in.recv#0.ret", APInt(64, 17)}});
    CHECK(in.run("recv_second_byte", {}, env3, cfg).status == RunStatus::Infeasible, "returns.nondet max is enforced");
  }
  {
    TableEnv env;
    RunResult r = in.run("copy_and_measure", {}, env, cfg);
    CHECK(r.status == RunStatus::Returned && r.returnValue->getSExtValue() == 2, "strcpy copies including the terminator, strlen measures it: " << (r.returnValue ? r.returnValue->getSExtValue() : -1) << r.message);
    RunConfig none;
    RunResult u = in.run("copy_and_measure", {}, env, none);
    CHECK(u.status == RunStatus::Unsupported && u.message.find("no model") != std::string::npos, "without a ModelDB an external call is Unsupported with a pointer to the fix");
  }
}

// ---------------------------------------------------------------- taint: sources, flows, sinks
static const char *kProgram = R"(
core.declare @recv(i32, ptr, i64, i32) -> i64
core.declare @atoi(ptr) -> i32
core.declare @strcpy(ptr, ptr) -> ptr
core.declare @system(ptr) -> i32
core.declare @getenv(ptr) -> ptr
core.declare @sanitize_len(i32) -> i32
core.declare @escape_shell(ptr) -> ptr
core.declare @memset(ptr, i32, i64) -> ptr

// recv into a zeroed 16-byte buffer, return the (zero-terminated) buffer
core.func @read_cmd(ptr) -> void {
^entry(%buf: ptr):
  %zero = core.const 0 : i32
  %sixteen = core.const 16 : i64
  %m = core.call @memset(%buf, %zero, %sixteen) : ptr
  %fd = core.const 3 : i32
  %fl = core.const 0 : i32
  %fifteen = core.const 15 : i64
  %n = core.call @recv(%fd, %buf, %fifteen, %fl) : i64
  core.return
}

// recv's byte count indexes an 8 byte buffer: too large counts overflow it
core.func @count_overflow() -> i32 {
^entry:
  %buf = core.alloca {size=16} : ptr
  %small = core.alloca {size=8} : ptr
  %fd = core.const 3 : i32
  %len = core.const 16 : i64
  %fl = core.const 0 : i32
  %n = core.call @recv(%fd, %buf, %len, %fl) : i64
  core.check.ptr_arith %small, %n loc("m.c":10:3)
  %z = core.const 0 : i32
  core.return %z
}

// network data copied and handed to system()
core.func @to_system() -> i32 {
^entry:
  %buf = core.alloca {size=16} : ptr
  call_read:
  %dst = core.alloca {size=16} : ptr
  core.call @read_cmd(%buf)
  %zero = core.const 0 : i32
  %sixteen = core.const 16 : i64
  %m = core.call @memset(%dst, %zero, %sixteen) : ptr
  %c = core.call @strcpy(%dst, %buf) : ptr
  %r = core.call @system(%dst) : i32
  core.return %r
}

// a constant command is no finding
core.func @const_to_system() -> i32 {
^entry:
  %dst = core.alloca {size=16} : ptr
  %zero = core.const 0 : i32
  %sixteen = core.const 16 : i64
  %m = core.call @memset(%dst, %zero, %sixteen) : ptr
  %a = core.const 108 : i8
  core.store %a, %dst
  %r = core.call @system(%dst) : i32
  core.return %r
}

// the attacker-controlled string is escaped before it reaches system()
core.func @escaped_to_system() -> i32 {
^entry:
  %buf = core.alloca {size=16} : ptr
  core.call @read_cmd(%buf)
  %e = core.call @escape_shell(%buf) : ptr
  %r = core.call @system(%e) : i32
  core.return %r
}

// atoi of attacker data is attacker data; it indexes a small buffer
core.func @atoi_index() -> i32 {
^entry:
  %buf = core.alloca {size=16} : ptr
  core.call @read_cmd(%buf)
  %n = core.call @atoi(%buf) : i32
  %w = core.sext %n : i64
  %small = core.alloca {size=8} : ptr
  core.check.ptr_arith %small, %w loc("m.c":40:3)
  %z = core.const 0 : i32
  core.return %z
}

// the sanitizer clears the taint of its result: the same index is no longer attacker controlled
core.func @sanitized_index() -> i32 {
^entry:
  %buf = core.alloca {size=16} : ptr
  core.call @read_cmd(%buf)
  %n = core.call @atoi(%buf) : i32
  %s = core.call @sanitize_len(%n) : i32
  %w = core.sext %s : i64
  %small = core.alloca {size=8} : ptr
  core.check.ptr_arith %small, %w loc("m.c":50:3)
  %z = core.const 0 : i32
  core.return %z
}

// getenv is a source of its own
core.func @env_to_system() -> i32 {
^entry:
  %name = core.alloca {size=4} : ptr
  %e = core.call @getenv(%name) : ptr
  %r = core.call @system(%e) : i32
  core.return %r
}
)";

static TaintResult runTaint(Module &m, const std::string &fn, std::map<std::string, APInt> seed = {}) {
  smt::TermManager tm;
  TaintExecutor ex(m, tm, *g_z3);
  TaintConfig cfg;
  cfg.models = &g_db;
  return ex.run(fn, seed, cfg);
}

static void testTaint() {
  std::string text(kProgram);
  text.erase(text.find("  call_read:\n"), std::string("  call_read:\n").size());
  auto m = load(text, "taint");

  TaintResult a = runTaint(*m, "count_overflow");
  CHECK(a.complete && (kinds(a.findings, true) == std::set<std::string>{"ptr_arith_oob"}), "tainted recv count overflows the 8 byte buffer, replay-confirmed (" << a.note << ")");
  CHECK(!a.runs.empty() && a.runs[0].slice.sources >= 1, "the result of recv is a symbolic source");
  bool hasRecv = false;
  for (auto &c : a.functions) hasRecv |= c.function == "recv" && c.source == c.calls && c.calls >= 1;
  CHECK(hasRecv, "recv is classified as a Source");

  TaintResult s = runTaint(*m, "to_system");
  CHECK(s.complete && (kinds(s.findings, true) == std::set<std::string>{"tainted_sink"}), "recv -> strcpy -> system: a tainted sink finding that replay confirms");
  if (!s.findings.empty()) CHECK(s.findings[0].ub->origin == "sink:command_exec" && s.findings[0].ub->op == "core.call @system", "the finding names the sink kind and call: " << s.findings[0].ub->origin);

  CHECK(runTaint(*m, "const_to_system").findings.empty(), "a constant command reaches system(): no finding");
  CHECK(runTaint(*m, "escaped_to_system").findings.empty(), "escape_shell clears the taint of what it returns");

  TaintResult i = runTaint(*m, "atoi_index");
  CHECK(i.complete && (kinds(i.findings, true) == std::set<std::string>{"ptr_arith_oob"}), "atoi(tainted string) is tainted: its use as an index is a finding, and the witness replays");
  TaintResult sl = runTaint(*m, "sanitized_index");
  CHECK(sl.complete && sl.findings.empty(), "sanitize_len clears taint: no query, no finding");

  TaintResult e = runTaint(*m, "env_to_system");
  CHECK(e.complete && (kinds(e.findings, true) == std::set<std::string>{"tainted_sink"}), "getenv() result flows to system()");

  // without models the external calls are unsupported, and the report says so
  smt::TermManager tm;
  TaintExecutor ex(*m, tm, *g_z3);
  TaintResult nomodel = ex.run("to_system", {});
  CHECK(!nomodel.complete && nomodel.reason == "unsupported", "no ModelDB: unsupported");

  // engine agreement on the memory-safety finding: full symbolic execution sees the same bug
  smt::TermManager tm2;
  SymbolicExecutor sx(*m, tm2, *g_z3);
  SymConfig sc;
  sc.models = &g_db;
  SymResult sr = sx.run("count_overflow", {}, sc);
  CHECK(sr.complete && (kinds(sr.findings) == std::set<std::string>{"ptr_arith_oob"}), "symbolic engine agrees on count_overflow (" << sr.note << ")");
  Interpreter in(*m);
  for (auto &f : sr.findings) {
    SeqEnv env(f.nondets, f.inputs);
    RunConfig rc;
    rc.models = &g_db;
    RunResult rr = in.run("count_overflow", {}, env, rc);
    // §22.418 / ENGINE_LIMITATIONS §7.12: ptr_arith_oob no longer ends the run; the site it walked past is
    // the same evidence.
    CHECK((rr.status == RunStatus::UB && rr.ub && rr.ub->kind == f.ub->kind) ||
              std::any_of(rr.ubContinued.begin(), rr.ubContinued.end(),
                          [&](const std::string &k) { return k.rfind(std::string(ubKindName(f.ub->kind)) + "@", 0) == 0; }),
          "the symbolic witness (recv's count) replays");
  }
  smt::TermManager tm3;
  SymbolicExecutor sx2(*m, tm3, *g_z3);
  SymResult sa = sx2.run("atoi_index", {}, sc);
  CHECK(sa.complete && (kinds(sa.findings) == std::set<std::string>{"ptr_arith_oob"}), "symbolic engine agrees on atoi_index (an unspecified-result model is a free value)");
}

// ---------------------------------------------------------------- through the full pipeline
static void testPipeline() {
  const char *core = R"(
core.declare @recv(i32, ptr, i64, i32) -> i64
core.func @handle(i32) -> i32 {
^entry(%fd: i32):
  %buf = core.alloca {size=16} : ptr
  %small = core.alloca {size=8} : ptr
  %len = core.const 16 : i64
  %fl = core.const 0 : i32
  %n = core.call @recv(%fd, %buf, %len, %fl) : i64
  core.check.ptr_arith %small, %n loc("h.c":7:3)
  %z = core.const 0 : i32
  core.return %z
}
)";
  driver::AnalysisOptions o;
  o.coreText = core;
  o.specText = "taint_entries:\n  - function: handle\n    label: network\n    params:\n      fd: { taint: none, type: int, value: 3 }\n";
  o.entry = "handle";
  o.models.push_back({"libc.yaml", slurp(HLIR_MODELS_DIR "/libc.yaml")});
  auto r = driver::analyzeEntry(o);
  CHECK(r.ok, r.error);
  if (!r.ok) return;
  std::vector<report::Finding> ub;
  for (auto &f : r.entry.findings) if (!f.warning) ub.push_back(f);
  CHECK(r.entry.verdict == report::Verdict::Bug && ub.size() == 1 && ub[0].kind == "ptr_arith_oob", "pipeline: bug found through the model");
  bool modelAssumption = false;
  for (auto &a : r.entry.assumptions) modelAssumption |= a.category == "model";
  CHECK(modelAssumption, "the report lists the ModelDB as an assumption");
  bool classified = false;
  for (auto &c : r.entry.functionClasses) classified |= c.function == "recv" && c.source > 0;
  CHECK(classified, "function classes include the modelled source");
  o.models.clear();
  auto nm = driver::analyzeEntry(o);
  CHECK(nm.ok && nm.entry.verdict == report::Verdict::Unknown, "without models the verdict is unknown (unsupported external call)");
  // a model file with an error is a input error, not a verdict
  o.models.push_back({"bad.yaml", "models:\n  - function: recv\n    source: [ { label: n, ptr: arg1, size: oops } ]\n"});
  auto bm = driver::analyzeEntry(o);
  CHECK(!bm.ok && bm.error.find("bad.yaml:3") != std::string::npos, "model file errors carry file:line: " << bm.error);
}

int main() {
  g_z3 = smt::makeZ3ProcessSolver("z3", 20000);
  if (!g_z3) { std::cout << "z3 not available: model tests skipped\n"; return 0; }
  testLoading();
  testConcrete();
  testTaint();
  testPipeline();
  std::cout << "models_tests: " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}

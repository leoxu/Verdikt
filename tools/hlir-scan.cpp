// hlir-scan: find the entry points of C sources automatically, generate their taint-entry specs, and analyse them all.
//
//   hlir-scan [options] <file.c|dir>... [clang flags such as -Iinc -DX=1]
//
// Per translation unit: C -> core (functions that use an unsupported construct stay declared), entry discovery
// (hlir/scan), one generated spec per entry, then one analysis per entry in a forked worker process (isolation: a crash
// or a timeout of one entry only marks that entry unknown). The combined result is a table plus the detailed reports of
// every entry that has findings or is inconclusive; --format json|sarif gives the machine-readable form.
//
// Exit: 0 nothing found (all safe under the assumptions), 1 at least one confirmed bug, 3 inconclusive entries, 2 input error.
#include <dirent.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <cctype>
#include <chrono>
#include <cstring>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <memory>
#include <thread>
#include <map>
#include <unordered_map>

#include "hlir/buildinfo/BuildInfo.h"
#include "hlir/ir/InvariantCheck.h"
#include "hlir/ir/Printer.h"
#include "llvm/Support/raw_ostream.h"
#include "hlir/ir/Loops.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/link/Link.h"
#include "hlir/support/Diagnostics.h"
#include "hlir/driver/Pipeline.h"
#include "hlir/frontend/Frontend.h"
#include "hlir/scan/Scan.h"
#include "hlir/semantics/Interpreter.h"  // --entries registered: run @main to capture the registration table
#include "hlir/semantics/Taint.h"        // --entries registered (symbolic, direction A): run @main through the concolic engine
#include "hlir/smt/Solver.h"             // ...which needs a TermManager + Solver
#include "hlir/semantics/Env.h"
#include "hlir/model/Model.h"

using namespace hlir;

namespace {

std::string slurp(const std::string &p, bool &ok) {
  std::ifstream in(p);
  ok = static_cast<bool>(in);
  std::stringstream ss;
  ss << in.rdbuf();
  return ss.str();
}
bool endsWith(const std::string &s, const std::string &e) { return s.size() >= e.size() && s.compare(s.size() - e.size(), e.size(), e) == 0; }
// Removes `core.func @NAME(...) { ... }` definitions (by brace matching; the opening line always ends the signature
// with a bare "{") for every name in `names` from `text`. Used so a model text loaded later (e.g. linux.core) can
// give a function a different signature than the generic one in libc.core instead of conflicting with it at parse
// time: the two can't coexist as two bodies of the same name (the IR has no overloading-by-arity), so the generic
// one is dropped wherever the specific one applies. Leaves unrelated `core.declare`s of the same name untouched.
std::string stripFuncBodies(const std::string &text, const std::set<std::string> &names) {
  if (names.empty()) return text;
  std::string out;
  out.reserve(text.size());
  size_t i = 0;
  while (i < text.size()) {
    static const std::string marker = "core.func @";
    size_t at = text.find(marker, i);
    if (at == std::string::npos) { out.append(text, i, std::string::npos); break; }
    size_t nameStart = at + marker.size();
    size_t nameEnd = nameStart;
    while (nameEnd < text.size() && (std::isalnum(static_cast<unsigned char>(text[nameEnd])) || text[nameEnd] == '_' || text[nameEnd] == '.' || text[nameEnd] == '$')) ++nameEnd;
    std::string name = text.substr(nameStart, nameEnd - nameStart);
    if (!names.count(name)) { out.append(text, i, nameEnd - i); i = nameEnd; continue; }
    out.append(text, i, at - i);  // keep everything before this "core.func @name"
    // skip past the matching closing '}' of this function's body
    size_t brace = text.find('{', nameEnd);
    if (brace == std::string::npos) { i = at; break; }
    size_t depth = 1, j = brace + 1;
    while (j < text.size() && depth > 0) { if (text[j] == '{') ++depth; else if (text[j] == '}') --depth; ++j; }
    i = j;  // drop [at, j): the whole "core.func @name(...) { ... }" block, including a trailing newline if present
    if (i < text.size() && text[i] == '\n') ++i;
  }
  return out;
}
bool isDir(const std::string &p) { struct stat st; return stat(p.c_str(), &st) == 0 && S_ISDIR(st.st_mode); }
void mkdirs(const std::string &p) {
  for (size_t i = 1; i <= p.size(); ++i)
    if (i == p.size() || p[i] == '/') mkdir(p.substr(0, i).c_str(), 0755);
}
void collect(const std::string &p, std::vector<std::string> &out) {
  if (!isDir(p)) { out.push_back(p); return; }
  std::vector<std::string> names;
  if (DIR *d = opendir(p.c_str())) {
    while (auto *e = readdir(d)) if (e->d_name[0] != '.') names.push_back(e->d_name);
    closedir(d);
  }
  std::sort(names.begin(), names.end());
  for (auto &n : names) {
    std::string q = p + "/" + n;
    if (isDir(q)) collect(q, out);
    else if (endsWith(n, ".c")) out.push_back(q);
  }
}
std::string safeName(std::string s) {
  for (char &c : s) if (!isalnum(static_cast<unsigned char>(c)) && c != '_' && c != '-' && c != '.') c = '_';
  return s;
}

// "4" or "4,16,64": ascending loop bounds
static bool parseBounds(const std::string &s, std::vector<unsigned> &out) {
  std::stringstream ss(s);
  std::string t;
  while (std::getline(ss, t, ',')) {
    if (t.empty() || t.find_first_not_of("0123456789") != std::string::npos) return false;
    out.push_back(static_cast<unsigned>(std::stoul(t)));
  }
  return !out.empty() && std::is_sorted(out.begin(), out.end());
}

// "LABEL=0102 0304 ..." -> label seed stream (hex bytes; spaces, ':' and '_' ignored). Returns false on a malformed argument.
static bool parseSeedBytes(const std::string &arg, std::map<std::string, std::vector<uint8_t>> &out, std::string &err) {
  size_t eq = arg.find('=');
  if (eq == std::string::npos || eq == 0) { err = "expected LABEL=HEXBYTES"; return false; }
  std::string hex;
  for (char c : arg.substr(eq + 1))
    if (c != ' ' && c != ':' && c != '_') hex += c;
  if (hex.size() % 2) { err = "odd number of hex digits"; return false; }
  std::vector<uint8_t> bytes;
  for (size_t i = 0; i < hex.size(); i += 2) {
    if (!isxdigit(static_cast<unsigned char>(hex[i])) || !isxdigit(static_cast<unsigned char>(hex[i + 1]))) { err = "not a hex digit in '" + hex.substr(i, 2) + "'"; return false; }
    bytes.push_back(static_cast<uint8_t>(std::stoi(hex.substr(i, 2), nullptr, 16)));
  }
  out[arg.substr(0, eq)] = bytes;
  return true;
}

// NAME=VALUE for --seed-value: the initial value of a named scalar input. Decimal, or 0x-prefixed hex.
static bool parseSeedValue(const std::string &arg, std::map<std::string, uint64_t> &out, std::string &err) {
  size_t eq = arg.find('=');
  if (eq == std::string::npos || eq == 0) { err = "expected NAME=VALUE"; return false; }
  std::string name = arg.substr(0, eq), val = arg.substr(eq + 1);
  if (val.empty()) { err = "empty value"; return false; }
  errno = 0;
  char *end = nullptr;
  unsigned long long v = std::strtoull(val.c_str(), &end, 0);
  if (errno != 0 || end == val.c_str() || *end != '\0') { err = "not an integer: '" + val + "'"; return false; }
  out[name] = static_cast<uint64_t>(v);
  return true;
}

// Function bodies of `core` text turned into declarations (the body is unusable: it does not verify).
static std::string demoteFunctions(const std::string &core, const std::set<std::string> &names) {
  std::istringstream in(core);
  std::string line, out;
  bool skipping = false;
  while (std::getline(in, line)) {
    if (skipping) { if (line == "}") skipping = false; continue; }
    if (line.rfind("core.func @", 0) == 0 || line.rfind("core.func internal @", 0) == 0) {  // `internal` = C static linkage
      size_t at = line.find('@');
      size_t e = line.find('(', at);
      std::string nm = line.substr(at + 1, e - at - 1);
      if (names.count(nm) && line.back() == '{') {
        out += "core.declare @" + line.substr(at + 1, line.size() - (at + 1) - 2) + "\n";  // drop " {" (demotes to external)
        skipping = true;
        continue;
      }
    }
    out += line + "\n";
  }
  return out;
}

// --link only: a pointer field a unit's own AST couldn't prove used (PtrFieldInfo::pendingLinkUse) is kept only if some
// *other* unit's whole-TU field-use set (frontend::LowerResult::fieldUses, matched by PtrFieldInfo::fieldKey) says
// otherwise; still-unused ones are pruned now, the same outcome collectPtrFields would have reached with whole-program
// knowledge at the time. This is a conservative whole-program approximation (any unit using the field anywhere counts, not
// just units reachable from this particular entry): it can keep a few fields that no actual path to this entry reaches,
// trading a little extra harness size for not missing fields a precise but much more expensive cross-file reachability
// analysis would have kept anyway.
void pruneUnusedLinkFields(std::vector<frontend::PtrFieldInfo> &v, const std::set<std::string> &globalUsed) {
  v.erase(std::remove_if(v.begin(), v.end(),
                          [&](frontend::PtrFieldInfo &pf) {
                            if (pf.pendingLinkUse && (pf.fieldKey.empty() || !globalUsed.count(pf.fieldKey))) return true;
                            pruneUnusedLinkFields(pf.children, globalUsed);
                            return false;
                          }),
          v.end());
}
// --link only, the same shape for the opposite decision: a function-pointer field may be synthesised as NULL only if
// some unit tests it for NULL (frontend::LowerResult::fieldNullTests). The unit that declares the pointer almost never
// is that unit -- FreeType's `FT_StreamRec.read` is tested in ftstream.c and reached from ttload.c -- so the per-unit
// answer is a floor, not the answer, and this pass raises it with whole-program knowledge (DESIGN.md §22.353).
void markNullTestedLinkFields(std::vector<frontend::PtrFieldInfo> &v, const std::set<std::string> &globalNullTested) {
  for (auto &pf : v) {
    if (!pf.nullTested && pf.kind == "func" && !pf.fieldKey.empty() && globalNullTested.count(pf.fieldKey)) pf.nullTested = true;
    markNullTestedLinkFields(pf.children, globalNullTested);
  }
}
void markNullTestedLinkFields(std::vector<frontend::FunctionInfo> &fns, const std::set<std::string> &globalNullTested) {
  std::set<const std::vector<frontend::PtrFieldInfo> *> done;
  for (auto &f : fns)
    for (auto &p : f.params) {
      if (p.ptrFields && done.insert(p.ptrFields.get()).second) markNullTestedLinkFields(*p.ptrFields, globalNullTested);
      if (p.udPtrFields && done.insert(p.udPtrFields.get()).second) markNullTestedLinkFields(*p.udPtrFields, globalNullTested);
    }
}
void pruneUnusedLinkFields(std::vector<frontend::FunctionInfo> &fns, const std::set<std::string> &globalUsed) {
  // ptrFields/udPtrFields are shared_ptrs (many params commonly point at the identical tree, e.g. every function taking
  // `struct amdgpu_device *adev` in one file): prune each underlying vector once, not once per sharer.
  std::set<const std::vector<frontend::PtrFieldInfo> *> done;
  for (auto &f : fns)
    for (auto &p : f.params) {
      if (p.ptrFields && done.insert(p.ptrFields.get()).second) pruneUnusedLinkFields(*p.ptrFields, globalUsed);
      if (p.udPtrFields && done.insert(p.udPtrFields.get()).second) pruneUnusedLinkFields(*p.udPtrFields, globalUsed);
    }
}


// ---------------------------------------------------------------- loop inventory (--dump-loops)
//
// The input to the LLM loop-invariant experiment (docs/LLM_GUIDED_SE.md §3 second layer, §5 item 0).
//
// The point of this file is NOT "here are the loops". It is "here are the loops the search budget was
// actually spent on, with the evidence that says so". Handing an LLM every loop in a program is both
// expensive and unmeasurable: most loops cost nothing, and an invariant for one of those buys nothing even
// when it is correct. Selection is cost attribution, and every input to it is already measured:
//
//   1. the ENTRY did not reach a verdict (`unknown`, or any `incomplete` reason). An entry that is already
//      `bug` or `safe` has nothing to buy -- it contributes no loops at all;
//   2. the loop's FUNCTION holds a real share of the flippable path conditions (§22.392's frontier profile,
//      the same instrument that picks fold candidates);
//   3. the loop is not already handled exactly -- a library function with a model, or a fold candidate.
//
// Those are recorded per loop as `selected` plus the numbers behind it, so the selection can be argued with
// rather than taken on faith.

static std::string jesc(const std::string &s) {
  std::string o;
  for (char c : s) {
    if (c == '"' || c == '\\') { o += '\\'; o += c; }
    else if (c == '\n') o += "\\n";
    else if (c == '\t') o += "\\t";
    else if (static_cast<unsigned char>(c) < 0x20) continue;
    else o += c;
  }
  return o;
}

// The source text an invariant has to be written against. Without it the inventory is a list of line
// numbers and the prompt has to go find them, which is one more place for the wrong file to be read.
static std::string sourceWindow(const std::string &file, unsigned line, unsigned before, unsigned after) {
  std::ifstream in(file);
  if (!in) return "";
  std::string l, out;
  unsigned n = 0;
  unsigned lo = line > before ? line - before : 1;
  while (std::getline(in, l)) {
    ++n;
    if (n < lo) continue;
    if (n > line + after) break;
    out += std::to_string(n) + "\t" + l + "\n";
  }
  return out;
}

struct Job {
  std::string file, entry, why, specText, specName, notes;
  std::shared_ptr<const std::string> core;                 // the unit's (or, with --link, the whole program's) core text, shared by its jobs
  // Parsed+verified once per distinct `core` text, before any job sharing it is forked (see the pre-parse pass right
  // before the worker loop). Every worker forked afterwards inherits this Module copy-on-write for free instead of
  // re-parsing (and re-verifying) the same, potentially huge, `--link` text itself — see docs/DESIGN.md §22.13.
  std::shared_ptr<Module> parsedBase;
  std::vector<std::pair<std::string, std::string>> pre;  // preconditions with `field:` names resolved for this translation unit
  unsigned line = 0;
  std::string resultPath;
  pid_t pid = 0;
  std::chrono::steady_clock::time_point started;
  bool done = false, timedOut = false;
  int status = 0;
  report::EntryReport result;
  bool haveResult = false;
};

report::EntryReport inconclusive(const Job &j, const std::string &code, const std::string &detail) {
  report::EntryReport r;
  r.function = j.entry;
  r.specFile = j.specName;
  r.verdict = report::Verdict::Unknown;
  r.incomplete.push_back({code, detail});
  return r;
}

// runs in the worker process
int workerMain(const Job &j, const driver::AnalysisOptions &base) {
  driver::AnalysisOptions opt = base;
  // Both, on purpose. `preParsedBase` is the fast path and is what a normal entry uses; `coreText` is the only
  // thing a SECOND analysis in this process can start from, because analyzeOnce appends the harness to the parsed
  // module and a pre-parsed base may be used once (see AnalysisOptions::preParsedBase). The session-constructor
  // fallback (DESIGN.md §22.371) is exactly such a second analysis: without the text it silently could not run,
  // and the entry kept the result of the constructor run it was supposed to replace.
  if (j.parsedBase) opt.preParsedBase = j.parsedBase;  // skip re-parsing: see the pre-parse pass before the fork loop
  if (j.core) opt.coreText = *j.core;
  opt.coreName = j.file;
  opt.specText = j.specText;
  opt.specName = j.specName;
  opt.entry = j.entry;
  opt.preconditions = j.pre;
  driver::AnalysisOutcome out = driver::analyzeEntry(opt);
  report::Report rep;
  rep.entries.push_back(out.ok ? out.entry : inconclusive(j, "input_error", out.error));
  std::ofstream f(j.resultPath);
  f << report::toJson(rep);
  f.close();
  switch (rep.entries[0].verdict) {
    case report::Verdict::SafeUnderAssumptions: case report::Verdict::SafeUpToLoopBound: return 0;
    case report::Verdict::Bug: return 1;
    default: return 3;
  }
}

const char *vname(report::Verdict v) { return report::verdictName(v); }

}  // namespace

// --entries registered: run the linked program's @main and, at each
// resmgr_attach call, read the io_funcs / connect_funcs table it is handed and resolve each slot's function
// pointer to the handler's name. Those are the real taint entries -- found by RUNNING the setup chain, so a
// handler passed through a parameter or stored in a heap field is found all the same. bestEffortInit makes any
// unmodelled call a no-op so the run reaches the registration without executing faithfully.
// Returns handler -> { "<structTag>#<slot>" } bindings discovered by running @main. The caller merges them into
// globalVtableBindings so Scan's EntryMode::Iface machinery scans them exactly as it scans statically-bound
// handlers. For QNX resmgr every io_funcs slot shares one (ctp, msg, ocb) contract (models/interfaces/
// qnx_resmgr.yaml), so a captured io_funcs handler is bound to the interface's primary attack-surface slot,
// `_resmgr_io_funcs#devctl` -- the exact slot label can differ from the real field but the contract does not.
static std::map<std::string, std::set<std::string>>
discoverRegisteredEntries(const std::string &core, const std::string &libcText,
                          const std::vector<std::pair<std::string, std::string>> &models,
                          const std::string &argvStr, const std::map<std::string, long> &passFns,
                          bool symbolic, double wallSeconds) {
  std::map<std::string, std::set<std::string>> bindings;
  Diagnostics d;
  auto mod = parseModule(core + "\n" + libcText, "linked.core", d);
  if (!mod || d.hasErrors() || !verifyModule(*mod, {}, d)) {
    std::cerr << "hlir-scan: --entries registered: linked module did not parse/verify:\n" << d.str() << "\n";
    return bindings;
  }
  const Function *mainFn = mod->findFunction("main");
  if (!mainFn || mainFn->isDeclaration())  // --link may keep a differently-qualified name; find a `main` body
    for (auto &f : mod->functions)
      if (!f->isDeclaration() && (f->name == "main" || f->name.size() >= 5 && f->name.compare(f->name.size() - 5, 5, "#main") == 0)) { mainFn = f.get(); break; }
  if (!mainFn || mainFn->isDeclaration()) {
    std::cerr << "hlir-scan: --entries registered: no @main body to run the discovery from\n";
    return bindings;
  }
  // `int main(int argc, char **argv)` cannot be run through the scalar-args run() API (argv is a pointer). Wrap it
  // in a no-arg entry that calls it with argc=1 and a dummy argv; getopt and friends are skipped by bestEffortInit,
  // so argv's contents never matter. A 0-arg main is run directly.
  std::string runFn = mainFn->name;
  if (!mainFn->paramTys.empty()) {
    std::vector<std::string> av;  // --discover-argv split on whitespace
    { std::istringstream is(argvStr); std::string t; while (is >> t) av.push_back(t); }
    // A real argv is built only when the caller supplied one and main is the conventional (int argc, char **argv);
    // then getopt-gated setup actually parses it. Otherwise argc=1 and a dummy argv (fine when there is no getopt).
    bool realArgv = !av.empty() && mainFn->paramTys.size() == 2 && !mainFn->paramTys[0]->isPtr() &&
                    mainFn->paramTys[1]->isPtr();
    std::string decl, args;
    if (realArgv) {
      decl += "  %argc = core.const " + std::to_string(av.size()) + " : i32\n";
      decl += "  %argv = core.alloca {size=" + std::to_string((av.size() + 1) * 8) + "} : ptr\n";
      decl += "  %zero = core.const 0 : i64\n  %nullp = core.int_to_ptr %zero : ptr\n";
      for (size_t i = 0; i < av.size(); ++i) {
        const std::string &s = av[i];
        std::string sv = "%s" + std::to_string(i), tag = std::to_string(i);
        decl += "  " + sv + " = core.alloca {size=" + std::to_string(s.size() + 1) + "} : ptr\n";
        for (size_t j = 0; j <= s.size(); ++j) {
          unsigned byte = j < s.size() ? (unsigned char)s[j] : 0u;
          std::string id = tag + "_" + std::to_string(j);
          decl += "  %o" + id + " = core.const " + std::to_string(j) + " : i64\n";
          decl += "  %p" + id + " = core.ptr_add " + sv + ", %o" + id + " : ptr\n";
          decl += "  %c" + id + " = core.const " + std::to_string(byte) + " : i8\n";
          decl += "  core.store %c" + id + ", %p" + id + "\n";
        }
        decl += "  %ao" + tag + " = core.const " + std::to_string(i * 8) + " : i64\n";
        decl += "  %ap" + tag + " = core.ptr_add %argv, %ao" + tag + " : ptr\n";
        decl += "  core.store " + sv + ", %ap" + tag + "\n";
      }
      decl += "  %aoN = core.const " + std::to_string(av.size() * 8) + " : i64\n";
      decl += "  %apN = core.ptr_add %argv, %aoN : ptr\n  core.store %nullp, %apN\n";
      args = "%argc, %argv";
    } else {
      for (size_t i = 0; i < mainFn->paramTys.size(); ++i) {
        const Type *t = mainFn->paramTys[i];
        std::string v = "%a" + std::to_string(i);
        if (t->isPtr()) decl += "  " + v + " = core.alloca {size=16} : ptr\n";
        else decl += "  " + v + " = core.const " + std::to_string(i == 0 ? 1 : 0) + " : i" + std::to_string(t->width()) + "\n";
        args += (args.empty() ? "" : ", ") + v;
      }
    }
    runFn = "__hlir_discover_main";
    std::string wrap = "core.func @" + runFn + "() -> i32 {\n^entry:\n" + decl +
                       "  %r = core.call @" + mainFn->name + "(" + args + ") : i32\n  core.return %r\n}\n";
    Diagnostics wd;
    auto wm = parseModule(core + "\n" + libcText + "\n" + wrap, "linked.core", wd);
    if (wm && !wd.hasErrors() && verifyModule(*wm, {}, wd)) mod = std::move(wm);
    else { std::cerr << "hlir-scan: --entries registered: could not wrap @" << mainFn->name << " (argc/argv): " << wd.str() << "\n"; return bindings; }
  }
  model::ModelDB modelDb;
  for (auto &m : models) modelDb.load(m.second, m.first, d);
  modelDb.setOpaqueFallback(true);
  std::vector<RunConfig::RegCapture> regs = {
      {"resmgr_attach", 6, 256},                 // raw QNX: io_funcs is arg 6
  };
  // which interface slot a handler captured from each registration call is bound to (its contract). Every resmgr
  // slot shares the (ctp, msg, ocb) contract, so the primary devctl slot is used for all of them.
  std::map<std::string, std::string> tagFieldFor = {
      {"resmgr_attach", "_resmgr_io_funcs#devctl"},
  };
  std::vector<RunConfig::CapturedReg> sink;
  if (symbolic) {
    // Direction A (M3b-A): run @main through the CONCOLIC engine, not one concrete path. promoteAll makes every
    // untainted nondet / unconstrained field a symbolic input, so a DATA gate that selects the registration path
    // (e.g. a driver: `if (hal_ctx->num_items > 0) register_handlers(/*registers*/)`) forks, and the path on which setup
    // succeeds reaches the registration. The capture hook fires in Machine<TaintDomain> exactly as on the concrete
    // path and appends to `sink`, which is shared across every run (dedup happens below via the bindings set).
    smt::TermManager tm;
    auto solver = smt::makeZ3NativeSolver(10000);
    if (!solver) solver = smt::makeZ3ProcessSolver("z3", 10000);
    if (!solver) { std::cerr << "hlir-scan: --entries registered (symbolic): no Z3 solver available\n"; return bindings; }
    TaintExecutor tx(*mod, tm, *solver);
    TaintConfig tcfg;
    tcfg.bestEffortInit = true;
    tcfg.forceAllocSuccess = true;
    tcfg.models = &modelDb;
    tcfg.captureRegs = &regs;
    tcfg.capturedRegs = &sink;
    if (!passFns.empty()) tcfg.passFns = &passFns;
    tcfg.promoteAll = true;                                  // the data gates that select the registration path must fork
    tcfg.discoverHavoc = true;                               // an unmodelled setup call turns the environment symbolic (num_items etc.)
    tcfg.replay = false;                                     // discovery captures a call target, it is not looking for a UB to confirm
    // The registration call sits behind a deep conjunction of setup gates (e.g. a driver: num_items in (0,MAX], then ~5
    // gates inside the registration function). Coverage-guided search alone empties its frontier long before lining them all
    // up, so bias it toward the registration function: flips in functions closer to it on the call graph go first.
    tcfg.reachTarget = regs.empty() ? "" : regs.back().function;  // the util wrapper (resmgr_attach modules override below)
    tcfg.maxRuns = 200000;                                   // the guided search needs room to stack the gate flips
    tcfg.wallSeconds = wallSeconds > 0 ? wallSeconds : 120;  // discovery is a prefix walk; it should not eat the scan's budget
    TaintResult tr = tx.run(runFn, {}, tcfg);
    std::cerr << "hlir-scan: --entries registered (symbolic): @" << runFn << " ran " << tr.runs.size()
              << " concolic path(s) (" << (tr.complete ? "complete" : "incomplete:" + tr.reason)
              << "); symbolic branches=" << tr.branchSymbolic.size() << " covered=" << tr.branchesCovered
              << " flips queued/solved/unsat=" << tr.flipsQueued << "/" << tr.flipsSolved << "/" << tr.flipsUnsat
              << " sources=" << (tr.runs.empty() ? 0u : (unsigned)tr.runs.back().slice.sources)
              << " captured=" << sink.size() << "\n";
    if (getenv("HLIR_DISCOVER_REACHED")) {  // which setup functions any path reached -- diagnoses where the search stalls
      std::set<std::string> fns;
      for (const Block *b : tr.blocksVisited) if (b && b->parent) fns.insert(b->parent->name);
      std::cerr << "hlir-scan: --entries registered (symbolic): reached " << fns.size() << " function(s):";
      for (auto &f : fns) std::cerr << " " << f;
      std::cerr << "\n";
    }
  } else {
    RunConfig cfg;
    cfg.bestEffortInit = true;
    cfg.forceAllocSuccess = true;  // the discovery run only has to reach the registration; a may_fail alloc must not bail it
    cfg.models = &modelDb;
    cfg.captureRegs = &regs;
    cfg.capturedRegs = &sink;
    if (!passFns.empty()) cfg.passFns = &passFns;
    cfg.trace = true;
    TableEnv env;
    RunResult rr = Interpreter(*mod).run(runFn, {}, env, cfg);
    if (sink.empty()) {
      std::cerr << "hlir-scan: --entries registered: @" << runFn << " ended as status=" << (int)rr.status
                << (rr.message.empty() ? "" : " (" + rr.message + ")")
                << " at " << rr.messageLoc.file << ":" << rr.messageLoc.line << "; calls made:";
      int shown = 0;
      for (auto &ev : rr.trace)
        if (ev.kind == TraceEvent::Call && shown++ < 200) std::cerr << " " << ev.function;
      std::cerr << "\n";
    }
  }
  std::cerr << "hlir-scan: --entries registered: reached " << sink.size() << " registration call(s)\n";
  for (auto &c : sink) {
    auto tf = tagFieldFor.find(c.function);
    const std::string tagField = tf == tagFieldFor.end() ? "_resmgr_io_funcs#devctl" : tf->second;
    std::cerr << "  " << c.function << " (" << tagField << "):";
    for (auto &h : c.handlers) {
      std::cerr << " [+" << h.first << "] @" << h.second;
      bindings[h.second].insert(tagField);
    }
    std::cerr << "\n";
  }
  std::cerr << "hlir-scan: discovered " << bindings.size() << " registered handler(s):";
  for (auto &b : bindings) std::cerr << " @" << b.first;
  std::cerr << "\n";
  return bindings;
}

int main(int argc, char **argv) {
  driver::AnalysisOptions base;
  scan::Options sopt;
  // whole-program bounds the code asserts about its own integer members, filled by the --link pass below and read
  // by the spec generator afterwards (DESIGN.md §22.358)
  std::map<std::string, frontend::AssertedBound> globalAsserts;
  sopt.assertBounds = &globalAsserts;
  // The same harvest, in the shape the ENGINE takes (semantics does not depend on the frontend). The spec
  // generator turns these into `where:` preconditions on the objects the InitPlan names; this copy reaches the
  // objects it cannot -- the ones materialised at run time past the synthesis frontier (DESIGN.md §22.365).
  std::map<std::string, FieldBound> globalFieldBounds;
  base.taint.fieldBounds = &globalFieldBounds;
  // `--no-field-bounds`: harvest as usual (the spec generator's `where:` still uses it) but do not hand the bounds
  // to the ENGINE, so objects materialised past the synthesis frontier go unconstrained. Exists to isolate what
  // DESIGN.md §22.365's A1 is worth: with it, a run differs from the default run in that one respect and nothing
  // else -- comparing a debug build against a release build would confound A1 with the asserts becoming live code.
  bool noFieldBounds = false;
  std::map<std::string, frontend::VtableInstance> globalVtableInstances;  // see LowerResult::vtableInstances
  // whole-program dispatch-table registrations (frontend::LowerResult::vtableBindings), keyed by the name the
  // function has AFTER linking -- a static handler is renamed per unit, and the entry selector works on linked
  // names. Filled in both the --link and the single-file path below (DESIGN.md §22.359).
  std::map<std::string, std::set<std::string>> globalVtableBindings;
  frontend::LowerOptions lopt;
  lopt.partial = true;
  lopt.recover = true;
  base.opaqueExternals = true;
  std::vector<std::string> inputs, onlyNames;
  buildinfo::BuildSource bsrc;
  std::string outDir, format = "text", output, specDir;
  // Accumulated work queue of externals a scan actually CALLED with no model (--model-todo / $HLIR_MODEL_TODO).
  std::string modelTodo = getenv("HLIR_MODEL_TODO") ? getenv("HLIR_MODEL_TODO") : "";
  // Loop inventory for the LLM loop-invariant experiment (docs/LLM_GUIDED_SE.md §3 second layer, §5 item 0).
  std::string dumpLoops;
  std::string dumpBranches;   // --dump-branches: every uncovered conditional edge, with the reason the search observed
  // Decide a candidate loop invariant with the FULL scan machinery (DESIGN.md §22.425 says why it cannot be
  // decided by hlir-entry/hlir-sym): "FUNCTION:HEADER:EXPR".
  std::string checkInvariant, invariantAssert;
  unsigned jobs = std::max(1u, std::min(4u, std::thread::hardware_concurrency()));
  unsigned timeoutS = 120;
  bool list = false, verbose = false, libc = true;
  bool autoCtor = true;  // run `__attribute__((constructor))` functions first; --no-auto-ctor turns it off
  auto usage = [] {
    std::cerr << "usage: hlir-scan [options] <file.c|dir>... [clang flags]\n"
                 "  --list                 only discover entries and print their specs' summary\n"
                 "  --entries roots|exported|all|iface   which functions are entries (default roots: not static and not called in the file, plus address-taken).\n                         iface: only the handlers registered in a slot of a modelled dispatch interface (see --interfaces)\n"
                 "  --struct-ranges DIR    declared per-struct field ranges (default models/structs): what a mount path or subsystem validated about an object a handler is handed. A NARROWING, named in each entry's assumptions\n"
                 "  --interfaces FILE|DIR  dispatch-interface models for `--entries iface` (default models/interfaces)\n"
                 "  --entry NAME           analyse exactly this function (repeatable)\n"
                 "  --only RE / --skip RE  filter entries by name\n"
                 "  --label L              taint label (default network)\n"
                 "  --hostile              no length<->buffer relations in the generated specs\n"
                 "  --reach-target NAME    bias the search frontier toward reaching function NAME sooner (default: off, pure coverage-guided order)\n"
                 "  --auto-target N        when an entry ends without a defect, re-run it aimed at up to N functions the search never entered (default: 0, off; each round is a full analysis, and the reported coverage is the union of all rounds)\n"
                 "  --buf-max N            byte buffers are 1..N bytes (default 256)\n"
                 "  --no-ptr-fields        leave pointer fields of input structs NULL (default: point them to legal objects)\n"
                 "  --max-fields N         pointer fields initialised per parameter (default 128)\n"
                 "  --ctx-names RE         parameters that are context objects (untainted)\n"
                 "  --include-noarg        also run entries without attacker-controlled parameters\n"
                 "  --spec-dir DIR         use DIR/<function>.yaml instead of the generated spec when it exists\n"
                 "  --out DIR              write specs, per-entry reports and the combined report there\n"
                 "  --jobs N  --timeout S  worker processes (default min(4,cores)) and wall-clock limit per entry (default 120)\n"
                 "  --runs N               concolic runs per entry\n"
                 "  --auto-seed N          spend N concrete probes picking the FIRST run's attacker bytes, instead of starting from zeros: the alphabet is\n"
                 "                         mined from the constants the entry's own code compares against (icmp operands, and the bytes of constant globals a strchr\n"
                 "                         runs over), the fitness is block coverage. Changes only where the search starts, never what is legal; the chosen seed is\n"
                 "                         named in the report. An explicit --seed-bytes for the same label wins\n"
                 "  --max-frontier N       pending branch flips the search may hold (default 20000, 0 = unbounded). Past this the least promising are\n"
                 "                         discarded, the run is reported incomplete:frontier_dropped and can no longer be `safe`. Larger is not uniformly\n"
                 "                         better: with the same --runs budget a bigger frontier spreads it thinner\n"
                 "  --max-steps N          interpreter step budget per run (default 1000000); a run that exceeds it is cut, reported incomplete:step_limit. Raise this for\n                         deep-loop/large-data bugs that need more real execution steps than the default budget; --timeout still bounds the wall-clock time regardless of this value\n"
                 "  --strict               do not recover from compile errors: a file with missing headers/unknown types is not analysed\n"
                 "  --strict-externs       calls to functions without a body or a model stop the analysis (default: assumed opaque, listed as an assumption)\n"
                 "  --seed-bytes L=HEX     start the attacker-controlled bytes of taint label L from these hex bytes (a valid message instead of zeros), e.g. network=01000000010 0...\n"
                 "  --seed-value N=V       start the named scalar input N from V (decimal or 0x hex), e.g. in_len=20. --seed-bytes only\n"
                 "                         reaches 8-bit inputs, so an entry taking (pointer, length) gets its buffer seeded and its LENGTH\n"
                 "                         left at 0, and the seed is then never read at the length it was written for. A name that matches\n"
                 "                         no input is reported, not ignored\n"
                 "  --loop-bound K[,K2,..] bounded unrolling (K1,K2,.. = iterative deepening, ascending): a basic block runs at most K times per call; runs that need more are cut. A complete exploration of the\n                         bounded program gives the verdict safe_up_to_loop_bound (longer loops were not explored)\n"
                 "  --mem-bound N          symbolic escalation pass: unrolling bound for memcpy/memset/model-fill (recv, fread, ...) calls whose length is not a compile-time constant (default 256). A call needing\n                         more than this many bytes unrolled reports incomplete:symbolic_bound_insufficient instead of being explored; raise this when a real bug needs a longer fill (e.g. network reads near 512+ bytes)\n"
                 "  --mem-expand-max N     hard cap on bytes a single memcpy/memset/string-scan physically expands, even for a compile-time-constant length (default 1048576 = 1<<20). Independent of --mem-bound\n                         above (that one is for a symbolic length). A call needing more bytes reports incomplete:unsupported; raise this when a real bug needs a single call larger than 1MB. Applies to both the\n                         primary concolic/taint engine and the symbolic escalation pass (same value, passed to both)\n"
                 "  --expose F[,F2,..]     let a harness in another file call these `static` functions. A static is private to its file, so a\n                         harness's own declaration of it binds to nothing and the target is never analysed; this makes the\n                         name bind across files. Honoured only when exactly ONE file has a static of that name, and\n                         reported either way. It is a deliberate departure from C linkage, used to reach defects that\n                         live in static helpers.\n  --noreturn F[,F2,..]   these functions never return (abort-like: a platform stop-on-failed-check, BUG): the path ends at the call, it is not a bug and nothing after it is analysed; also valid when the function has a body.\n                         `noreturn: true` in a ModelDB entry, and __attribute__((noreturn)) / [[noreturn]] in the source, do the same\n"
                 "  --untrusted-api RE[,LABEL[,OUTMAX]]  threat model: a component below the analysed code is compromised. Functions without a body or a model whose name matches RE return attacker-controlled\n                         values, returned pointers are NULL or OUTMAX-byte (default 256) objects with attacker-controlled bytes, and every non-const pointer-argument object of at most OUTMAX bytes is overwritten\n                         with attacker-controlled bytes (taint label LABEL, default `untrusted`). Add the entry harness's own inputs as usual; use --include-noarg for entries without parameters\n"
                 "  --min-coverage PCT     the verdict cannot be safe when the runs entered less than PCT % of the blocks of the functions reachable from the entry (incomplete:low_coverage); the coverage is always reported\n"
                 "                         the report also always includes conditional-branch-direction coverage (`br N%` in the scan summary, coverage.branches_reachable/branches_visited in JSON):\n"
                 "                         every core.cond_br reachable from the entry contributes a true and a false edge; 100% means every one of them was taken by some run, not merely that its block was entered\n"
                 "  --lenient-ptr-arith    do not report pointer arithmetic that leaves the object (formal UB, e.g. `if (p + len > end)` in validators); only real out-of-bounds accesses\n"                 "  --ub-continue K[,K2]   record these UB kinds and KEEP RUNNING instead of ending the run there. A deliberate,\n"
                 "                         named under-approximation for one target: use it when a real but benign UB sits on a hot\n"
                 "                         path and hides everything behind it (libxml2 leaves xmlHashedString.hashValue\n"
                 "                         indeterminate on every parse, which stopped every run at the first document). The\n"
                 "                         findings are still reported and the assumption is listed in the report.\n"
                 "  --dump-vtables FILE    write the dispatch-table registrations found (tag#field -> handler) and continue; diagnostic only\n"
                 "  --dump-linked FILE     with --link: write the linked core module\n"
                 "  --link                 treat all input files as one program: resolve calls and globals across files (internal symbols are kept apart);\n                         entries are the functions nobody in the program calls\n"
                 "  --wayland              load models/wayland.core (wl_resource_get/set_user_data) and infer the user-data struct of handle parameters\n"
                 "  --qnx                  load models/qnx.core (iofunc_devctl_default/verify, iofunc_ocb_attach) and models/qnx.yaml (iofunc_attr_init, resmgr_attach, dispatch_*): QNX resource managers, see models/interfaces/qnx_resmgr.yaml\n"
                 "  --spawn-callbacks      call the callback of pthread_create/kthread_* directly where it is created: the thread body stops being a blind spot, but no interleaving is analysed\n"
                 "  --init-fn NAME         run NAME (the project's own initialiser: module_init, _init, a constructor) before every entry; repeatable, runs in order\n"
                 "  --no-auto-ctor         do NOT run the `__attribute__((constructor))` functions of the scanned sources first (they run by default, before any --init-fn, because the loader runs them before any API call)\n"
                 "  --stop-fn NAME         NAME is a dispatch loop (dispatch_block, MsgReceive, wl_display_run): reaching it inside an --init-fn ends the initialiser\n"
                 "  --record-reads         measure the TARGET SET: which globals and which parameter-object offsets the entry's call chain reads (diagnostic; costs on the hot path)\n"
                 "  --promote-read-globals globals the entry reads but the program never wrote get an unconstrained value instead of their static initialiser (two passes; removes the global_initial_value narrowing)\n"
                 "  --no-table-select      do NOT select over a constant global's static initialiser when the index is symbolic; concretise the index instead (the pre-G2 behaviour, for comparison)\n"
                 "  --store-select         when a STORE's offset is symbolic, write one GUARDED store per in-bounds offset instead of concretising it to this run's slot (Sec.22.487; opt-in, see there)\n"
                 "  --user-data-getter F   F(handle) returns the handle's user data (void *): see --wayland; --user-data-zero: its state is zero, not attacker-influenced\n"
                 "  --linux                load models/linux.core (copy_from_user, kmalloc, kfree, ...) and models/linux.yaml\n"
                 "  --no-infer-structs     do not synthesize layouts for structs whose definition is missing (functions using them are skipped)\n"
                 "  --makefile PATH        take compile options (-I -D -include -std -fwrapv ...) from a Makefile (or the directory holding one):\n"
                 "                         `make -n` is run to get the real compiler commands (it executes what the Makefile executes outside\n"
                 "                         recipes: use --make-mode static on trees you do not trust); with no input files every file it compiles is scanned\n"
                 "  --make-target T  --make-arg A   target and extra variables for make (repeatable), e.g. --make-arg M=drivers/x --make-arg ARCH=x86\n"
                 "  --make-mode dry-run|static      static parses the Makefile without running anything (variables, include, ifeq, wildcard, ...)\n"
                 "  --compile-commands FILE         compile_commands.json (bear, cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON, ...)\n"
                 "  --extern NAME          keep this function a declaration even if the sources define it (supply its behaviour with --models / a core model)\n"
                 "  --pre FILE             preconditions for internal functions (repeatable): extra constraints merged into the generated specs, see docs\n"
                 "  --no-libc              do not link models/libc.core\n"
                 "  --no-escalate          skip the symbolic precision pass: the concolic result alone. DIAGNOSTIC -- it removes coverage and findings\n"
                 "  --model-todo FILE      merge every external function this scan CALLED with no model into FILE\n"
                 "  --check-invariant F:HEADER:EXPR   assume a candidate loop invariant at the loop header and assert it\n"
                 "                         at the back edge, then analyse normally: a reported `assert` means it is NOT\n"
                 "                         preserved\n"
                 "  --invariant-assert EXPR   assert THIS instead of the assumed candidate. The reachability probe is\n"
                 "                         `--check-invariant F:H:1 == 1 --invariant-assert \"1 != 1\"`: no assert means\n"
                 "                         the back edge is never reached and every verdict about the loop is vacuous\n"
                 "  --dump-branches FILE   write every conditional-branch direction no run took, each with the reason the SEARCH observed:\n"
                 "                         `open` (a flip was queued and the budget ran out -- the only class more budget can close),\n"
                 "                         `unsat` (the solver was asked and said no: infeasible, never coverable),\n"
                 "                         `const` (the condition was never symbolic: constant in this build/harness, e.g. sizeof(x)<8),\n"
                 "                         `unreached` (the branch never executed at all). The four COUNTS are always in the report;\n"
                 "                         this writes the individual edges. Use it before spending budget on a coverage number.\n"
                 "  --dump-loops FILE      write the loops of the functions the search budget actually went to, with the\n"
                 "                         cost evidence that selects them (JSON). An entry that reached a verdict\n"
                 "                         contributes nothing: there is nothing to buy there\n"
                 "                         (also $HLIR_MODEL_TODO). Counts and the entries that hit it are kept, so\n"
                 "                         repeated scans accumulate: the list is a work queue of models to write\n"
                 "                         next, ranked by how often each one actually got in the way.\n"
                 "  --no-field-bounds      do not give the engine the bounds the code asserts about struct members\n"
                 "  --libc-models  --models f.yaml   ModelDB documents (libc.yaml is loaded by default)\n"
                 "  --externs f.yaml       the project's own statement about its externals: model documents to load, plus a skip list where each entry carries a REASON (reported as a decision, not as an omission)\n"
                 "  --format text|json|sarif  --output FILE   combined report\n"
                 "  -v                     also print the details of safe entries\n";
  };
  bool libcModels = true, linuxApi = false, wayland = false, qnx = false, linkMode = false;
  bool discoverRegistered = false;  // --entries registered: run @main, capture the registration table (dump, M1b)
  std::string discoverArgv;         // --discover-argv "prog -c 0 -l /x": argv for @main so getopt-gated setup runs
  std::map<std::string, long> discoverPassFns;  // --discover-pass-fn F=771,G: gates forced to return a value (default 0; ptr->non-null)
  bool discoverSymbolic = false;    // --discover-symbolic: run @main through the concolic engine so DATA gates fork (direction A)
  std::set<std::string> stopFns;  // dispatch-loop entries: reaching one inside the initialiser ends it
  std::string dumpLinked, dumpVtables;
  // `--entries iface` reads the dispatch-interface models from here; a file is taken as-is, a directory as every
  // *.yaml in it. Only loaded for that mode, so no other scan pays for it or can be changed by it.
  std::string interfacesDir = HLIR_MODELS_DIR "/interfaces";
  std::string structRangesDir = HLIR_MODELS_DIR "/structs";  // declared per-struct field ranges, DESIGN.md §22.480
  std::vector<std::string> extraModels;
  std::vector<std::string> externsPaths;
  std::vector<std::string> noreturnFns;
  std::set<std::string> exposeNames;   // --expose: statics a harness is allowed to call across units (see link::linkUnits)
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&]() -> std::string { return i + 1 < argc ? argv[++i] : ""; };
    if (a == "--list") list = true;
    else if (a == "--entries") {
      std::string m = next();
      if (m == "roots") sopt.mode = scan::EntryMode::Roots;
      else if (m == "exported") sopt.mode = scan::EntryMode::Exported;
      else if (m == "all") sopt.mode = scan::EntryMode::All;
      else if (m == "iface") sopt.mode = scan::EntryMode::Iface;
      else if (m == "registered") { discoverRegistered = true; sopt.mode = scan::EntryMode::Iface; }
      else { usage(); return 2; }
    } else if (a == "--discover-symbolic") discoverSymbolic = true;
    else if (a == "--discover-argv") discoverArgv = next();
    else if (a == "--discover-pass-fn") { std::string s = next(), t; std::istringstream is(s); while (std::getline(is, t, ',')) if (!t.empty()) { size_t eq = t.find('='); if (eq == std::string::npos) discoverPassFns[t] = 0; else discoverPassFns[t.substr(0, eq)] = strtol(t.substr(eq + 1).c_str(), nullptr, 0); } }
    else if (a == "--interfaces") interfacesDir = next();
    else if (a == "--struct-ranges") structRangesDir = next();
    else if (a == "--entry") onlyNames.push_back(next());
    else if (a == "--only") sopt.only = next();
    else if (a == "--skip") sopt.skip = next();
    else if (a == "--label") sopt.label = next();
    else if (a == "--hostile") sopt.hostile = true;
    else if (a == "--buf-max") sopt.bufMax = std::stoull(next());
    else if (a == "--ctx-names") sopt.ctxNames = next();
    else if (a == "--no-ptr-fields") sopt.noPtrFields = true;
    else if (a == "--max-fields") sopt.maxFields = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--include-noarg") sopt.includeNoArg = true;
    else if (a == "--spec-dir") specDir = next();
    else if (a == "--out") outDir = next();
    else if (a == "--jobs") jobs = std::max(1u, static_cast<unsigned>(std::stoul(next())));
    else if (a == "--timeout") timeoutS = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--runs") base.taint.maxRuns = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--max-frontier") base.taint.maxFrontier = static_cast<size_t>(std::stoull(next()));
    else if (a == "--auto-seed") base.taint.autoSeed = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--max-steps") base.taint.maxSteps = std::stoull(next());
    else if (a == "--reach-target") base.taint.reachTarget = next();
    else if (a == "--auto-target") base.autoTargetRounds = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--no-libc") libc = false;
    // Diagnostic: the concolic/taint result ALONE, without the symbolic precision pass. It exists because the
    // two engines share one wall-clock budget, so a question about one of them cannot be asked while the other
    // is spending most of it (DESIGN.md §22.444). It REMOVES coverage and findings -- an entry run with it is
    // not a scan result -- so it is not in the profiles.
    else if (a == "--no-escalate") base.escalate = false;
    else if (a == "--no-field-bounds") noFieldBounds = true;
    else if (a == "--strict") lopt.recover = false;
    else if (a == "--pre") { std::string f = next(); bool pok = false; std::string t = slurp(f, pok); if (!pok) { std::cerr << "cannot read " << f << "\n"; return 2; } base.preconditions.push_back({f, t}); }
    else if (a == "--makefile") bsrc.makefile = next();
    else if (a == "--make-target") bsrc.target = next();
    else if (a == "--make-arg") bsrc.makeArgs.push_back(next());
    else if (a == "--make-mode") bsrc.mode = next();
    else if (a == "--compile-commands") bsrc.compileCommands = next();
    else if (a == "--no-infer-structs") lopt.inferStructs = false;
    else if (a == "--linux") { linuxApi = true; sopt.linuxApi = true; }
    else if (a == "--extern") lopt.externalFunctions.push_back(next());
    else if (a == "--expose") { std::istringstream ws(next()); std::string nm; while (std::getline(ws, nm, ',')) if (!nm.empty()) exposeNames.insert(nm); }
    else if (a == "--user-data-getter") lopt.userDataGetters.push_back(next());
    else if (a == "--user-data-zero") sopt.userDataZero = true;
    else if (a == "--wayland") wayland = true;
    else if (a == "--qnx") qnx = true;
    else if (a == "--spawn-callbacks") lopt.spawnCallbacks = true;
    else if (a == "--init-fn") sopt.initFunctions.push_back(next());
    else if (a == "--no-auto-ctor") autoCtor = false;
    else if (a == "--stop-fn") stopFns.insert(next());
    else if (a == "--record-reads") base.taint.recordReads = true;
    else if (a == "--promote-read-globals") base.promoteReadGlobals = true;
    else if (a == "--no-table-select") base.noTableSelect = true;
    else if (a == "--store-select") base.storeSelect = true;
    else if (a == "--seed-bytes") { std::string perr; if (!parseSeedBytes(next(), base.taint.labelSeeds, perr)) { std::cerr << "hlir-scan: --seed-bytes: " << perr << "\n"; return 2; } }
    else if (a == "--seed-value") { std::string perr; if (!parseSeedValue(next(), base.taint.valueSeeds, perr)) { std::cerr << "hlir-scan: --seed-value: " << perr << "\n"; return 2; } }
    else if (a == "--lenient-ptr-arith") lopt.lenientPointerArith = true;
    else if (a == "--ub-continue") {
      std::istringstream ws(next());
      std::string nm;
      while (std::getline(ws, nm, ',')) {
        UBKind k;
        if (nm.empty()) continue;
        if (!ubKindFromName(nm.c_str(), k)) { std::cerr << "hlir-scan: --ub-continue: unknown UB kind '" << nm << "'\n"; return 2; }
        base.ubContinue.insert(k);
      }
    }
    else if (a == "--noreturn") { std::istringstream ws(next()); std::string nm; while (std::getline(ws, nm, ',')) if (!nm.empty()) noreturnFns.push_back(nm); }
    else if (a == "--untrusted-api") {
      std::string v = next(), re = v, label = "untrusted";
      unsigned om = 256;
      std::vector<std::string> parts;
      { std::istringstream ws(v); std::string t; while (std::getline(ws, t, ',')) parts.push_back(t); }
      if (parts.size() >= 2) { re = parts[0]; label = parts[1]; }
      if (parts.size() >= 3) om = static_cast<unsigned>(std::atoi(parts[2].c_str()));
      if (parts.size() == 1) re = parts[0];
      base.untrustedApi = re; base.untrustedLabel = label; base.untrustedOutMax = om;
    }
    else if (a == "--min-coverage") base.minCoverage = std::atof(next().c_str()) / 100.0;
    else if (a == "--loop-bound") { if (!parseBounds(next(), base.loopBounds)) { std::cerr << "hlir-scan: --loop-bound expects K or K1,K2,...\n"; return 2; } }
    else if (a == "--mem-bound") base.memBound = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--mem-expand-max") { uint64_t v = std::stoull(next()); base.memExpandMax = v; base.taint.memExpandMax = v; }
    else if (a == "--dump-linked") dumpLinked = next();
    else if (a == "--dump-vtables") dumpVtables = next();
    else if (a == "--link") { linkMode = true; lopt.link = true; }
    else if (a == "--strict-externs") base.opaqueExternals = false;
    else if (a == "--libc-models") libcModels = true;
    else if (a == "--models") extraModels.push_back(next());
    else if (a == "--externs") externsPaths.push_back(next());
    else if (a == "--format") format = next();
    else if (a == "--output") output = next();
    else if (a == "--model-todo") modelTodo = next();
    else if (a == "--dump-loops") dumpLoops = next();
    else if (a == "--dump-branches") { dumpBranches = next(); base.listMissedBranches = true; }
    else if (a == "--check-invariant") checkInvariant = next();
    else if (a == "--invariant-assert") invariantAssert = next();
    else if (a == "-v") verbose = true;
    else if (a == "-h" || a == "--help") { usage(); return 0; }
    else if (a == "--") {
      // Not a real clang flag: a bare "--" is the universal CLI convention for "end of our own options, the rest is
      // passed through verbatim" (getopt, many build tools, ...), and the usage line already allows clang flags right
      // after the files with no separator. If forwarded into clangArgs, clang's own argv parser treats "--" as "every
      // following token is a filename, not an option" -- silently swallowing -I/-D/-std and turning each of their
      // arguments into its own bogus translation unit. That produces baffling, unrelated-looking parse cascades
      // (e.g. "unsupported: member of a record whose layout is invalid" all over an unrelated class) instead of the
      // real "file not found" cause. Accept and discard it so both `hlir-scan a.cpp -I inc` and the more conventional
      // `hlir-scan a.cpp -- -I inc` work the same way.
    }
    else if (a.size() > 1 && a[0] == '-') {
      lopt.clangArgs.push_back(a);
      if ((a == "-I" || a == "-D" || a == "-include" || a == "-isystem") && i + 1 < argc) lopt.clangArgs.push_back(argv[++i]);
    } else collect(a, inputs);
  }
  buildinfo::BuildDatabase bdb;
  std::vector<std::string> buildNotes;
  bool haveBuild = !bsrc.makefile.empty() || !bsrc.compileCommands.empty();
  if (haveBuild) {
    std::string berr;
    if (!buildinfo::loadBuildDatabase(bsrc, bdb, buildNotes, berr)) { std::cerr << "hlir-scan: " << berr << "\n"; for (auto &n : buildNotes) std::cerr << "  " << n << "\n"; return 2; }
    for (auto &n : buildNotes) std::cerr << "hlir-scan: " << n << "\n";
    if (inputs.empty()) inputs = bdb.files();  // scan everything the build compiles
  }
  if (inputs.empty() || (format != "text" && format != "json" && format != "sarif")) { usage(); return 2; }

  bool ok;

  // `--entries iface`: load the dispatch-interface models and point the entry selector at them plus the
  // registrations the frontend will collect below. Loaded only for this mode -- every other scan behaves exactly
  // as it did before this option existed, including when models/interfaces is missing or malformed.
  iface::InterfaceFile ifaces;
  if (sopt.mode == scan::EntryMode::Iface) {
    std::vector<std::string> files;
    struct stat st {};
    if (stat(interfacesDir.c_str(), &st) == 0 && S_ISDIR(st.st_mode)) {
      if (DIR *d = opendir(interfacesDir.c_str())) {
        while (struct dirent *de = readdir(d))
          if (endsWith(de->d_name, ".yaml")) files.push_back(interfacesDir + "/" + de->d_name);
        closedir(d);
        std::sort(files.begin(), files.end());  // a model set must not depend on readdir order
      }
    } else files.push_back(interfacesDir);
    if (files.empty()) { std::cerr << "hlir-scan: --entries iface: no interface model (*.yaml) in " << interfacesDir << "\n"; return 2; }
    for (auto &f : files) {
      bool fok = false;
      std::string text = slurp(f, fok);
      if (!fok) { std::cerr << "hlir-scan: cannot read interface model " << f << "\n"; return 2; }
      Diagnostics d;
      if (!iface::parseInterfaceFile(text, f, ifaces, d)) { std::cerr << "hlir-scan: " << d.str(); return 2; }
    }
    std::cerr << "hlir-scan: " << ifaces.interfaces.size() << " interface model(s) from " << interfacesDir << ":";
    for (auto &i : ifaces.interfaces) std::cerr << " " << i.name << "(" << i.slots.size() << " slots)";
    std::cerr << "\n";
    sopt.interfaces = &ifaces;
    sopt.vtableBindings = &globalVtableBindings;
    sopt.vtableInstances = &globalVtableInstances;
  }

  // Declared per-struct field ranges (DESIGN.md §22.480). Loaded for every scan, not only `--entries iface`:
  // what a mount path validated about a `struct super_block` is true however the entry was chosen. Keyed by
  // tag AND size, so a file for one subsystem cannot reshape another's same-named struct. Each one that
  // actually applies is named in that entry's assumptions, because every one of them narrows the analysis.
  structranges::StructRanges sranges;
  {
    std::vector<std::string> files;
    struct stat st {};
    if (stat(structRangesDir.c_str(), &st) == 0 && S_ISDIR(st.st_mode)) {
      if (DIR *d = opendir(structRangesDir.c_str())) {
        while (struct dirent *de = readdir(d))
          if (endsWith(de->d_name, ".yaml")) files.push_back(structRangesDir + "/" + de->d_name);
        closedir(d);
        std::sort(files.begin(), files.end());
      }
    } else if (stat(structRangesDir.c_str(), &st) == 0) files.push_back(structRangesDir);
    for (auto &f : files) {
      bool fok = false;
      std::string text = slurp(f, fok);
      if (!fok) { std::cerr << "hlir-scan: cannot read struct ranges " << f << "\n"; return 2; }
      Diagnostics d;
      if (!sranges.load(text, f, d)) { std::cerr << "hlir-scan: " << d.str(); return 2; }
    }
    if (!sranges.empty()) {
      std::cerr << "hlir-scan: declared field ranges for " << sranges.byKey.size() << " struct(s) from " << structRangesDir << "\n";
      sopt.structRanges = &sranges;
    }
  }

  if (libc) base.libcText = slurp(HLIR_MODELS_DIR "/libc.core", ok) + "\n" + slurp(HLIR_MODELS_DIR "/libstdcxx.core", ok);
  if (linuxApi) {
    std::string lc = slurp(HLIR_MODELS_DIR "/linux.core", ok);
    // `// hlir-extern: a b c` lines: header inlines the frontend must leave as declarations so the models above apply
    // `// hlir-override: a b c` lines: linux.core below redefines these libc.core functions with a kernel-correct
    // signature (e.g. `snprintf`/`sprintf`: variadic functions declared in a kernel header are not in a "system
    // header" the way glibc's are, so the frontend gives them an extra trailing vararg-block parameter libc.core's
    // generic model doesn't have — see docs/DESIGN.md §22.33); strip the libc.core body first so the two don't
    // collide as two definitions of the same name.
    std::set<std::string> overrides;
    std::istringstream lin(lc);
    std::string ll;
    while (std::getline(lin, ll)) {
      auto k = ll.find("hlir-extern:");
      if (k != std::string::npos && ll.rfind("//", 0) == 0) {
        std::istringstream ws(ll.substr(k + 12));
        std::string nm;
        while (ws >> nm) lopt.externalFunctions.push_back(nm);
        continue;
      }
      k = ll.find("hlir-override:");
      if (k == std::string::npos || ll.rfind("//", 0) != 0) continue;
      std::istringstream ws(ll.substr(k + 14));
      std::string nm;
      while (ws >> nm) overrides.insert(nm);
    }
    base.libcText = stripFuncBodies(base.libcText, overrides) + "\n" + lc;
    base.models.push_back({HLIR_MODELS_DIR "/linux.yaml", slurp(HLIR_MODELS_DIR "/linux.yaml", ok)});
  }
  // QNX resource managers: the devctl pre-dispatch helpers live in the SDP's libio-util, not in the sources
  // being scanned, so without these models `iofunc_devctl_default` never yields and a verified request length
  // stays unconstrained. The interface contract that says what a handler is HANDED is a separate file and is
  // loaded with every other models/interfaces/*.yaml under `--entries iface`.
  if (qnx) {
    base.libcText += "\n" + slurp(HLIR_MODELS_DIR "/qnx.core", ok);
    base.models.push_back({HLIR_MODELS_DIR "/qnx.yaml", slurp(HLIR_MODELS_DIR "/qnx.yaml", ok)});
  }
  base.taint.stopFns = stopFns.empty() ? nullptr : &stopFns;
  if (wayland) {
    std::string wc = slurp(HLIR_MODELS_DIR "/wayland.core", ok);
    base.libcText += "\n" + wc;
    std::istringstream lin(wc);
    std::string ll;
    while (std::getline(lin, ll)) {  // `// hlir-user-data-getter: a b` lines
      auto k = ll.find("hlir-user-data-getter:");
      if (k == std::string::npos || ll.rfind("//", 0) != 0) continue;
      std::istringstream ws(ll.substr(k + 22));
      std::string nm;
      while (ws >> nm) lopt.userDataGetters.push_back(nm);
    }
  }
  if (!noreturnFns.empty()) {
    std::string y = "models:\n";
    for (auto &n : noreturnFns) y += "  - function: " + n + "\n    noreturn: true\n";
    base.models.push_back({"--noreturn", y});
  }
  if (libcModels) base.models.push_back({HLIR_MODELS_DIR "/libc.yaml", slurp(HLIR_MODELS_DIR "/libc.yaml", ok)});
  for (auto &m : extraModels) {
    std::string t = slurp(m, ok);
    if (!ok) { std::cerr << "cannot read " << m << "\n"; return 2; }
    base.models.push_back({m, t});
  }
  // The project's own statement about its externals (DESIGN.md §22.379). It is read BEFORE the scan rather than
  // consulted during it: a typo in a model path or a skip entry with no reason is a project-wide input error, and
  // the one thing it may not do is turn into a quiet per-entry `unknown`.
  // `--externs` may be given more than once: a project's shared statement (the skip list for a whole family of
  // resource managers) and a module's own (its command line) are different facts with different lifetimes, and
  // forcing them into one file would mean copying the shared half per module.
  for (auto &externsPath : externsPaths) {
    std::string t = slurp(externsPath, ok);
    if (!ok) { std::cerr << "hlir-scan: --externs: cannot read " << externsPath << "\n"; return 2; }
    Diagnostics ed;
    model::ExternsFile ef;
    if (!model::loadExterns(t, externsPath, ef, ed)) { std::cerr << ed.str(); return 2; }
    for (auto &mp : ef.modelPaths) {
      std::string mt = slurp(mp, ok);
      if (!ok) {
        std::cerr << "hlir-scan: --externs: " << externsPath << " names a model file that cannot be read: " << mp << "\n";
        return 2;
      }
      base.models.push_back({mp, mt});
    }
    for (auto &sk : ef.skips) base.externSkips.push_back(sk);
    if (!ef.argv.empty()) {
      if (!base.initArgv.empty()) {
        std::cerr << "hlir-scan: --externs: " << externsPath << " states an argv and so does " << base.externsPath
                  << "; a program has one command line, so give exactly one of them\n";
        return 2;
      }
      base.initArgv = ef.argv;
    }
    base.externsPath = base.externsPath.empty() ? externsPath : base.externsPath + ", " + externsPath;
  }
  if (!outDir.empty()) { mkdirs(outDir + "/specs"); mkdirs(outDir + "/reports"); }
  std::string tmp = outDir.empty() ? "" : outDir + "/reports";
  if (tmp.empty()) {
    char buf[] = "/tmp/hlir-scan-XXXXXX";
    if (!mkdtemp(buf)) { std::cerr << "cannot create a temporary directory\n"; return 2; }
    tmp = buf;
  }

  // ---------------------------------------------------------------- discovery
  std::vector<Job> all;
  struct Skipped { std::string file, entry, why; unsigned line; };
  std::vector<Skipped> skipped;
  std::vector<std::string> fileErrors, notes;
  unsigned nfiles = 0;
  struct UnitRec { std::string path; frontend::LowerResult low; };
  std::vector<UnitRec> units;
  // entries of the given functions -> jobs. path: the file (empty with --link: taken from fileOf per function)
  // `--init-fn` names a function of the project, not of one entry: a typo makes EVERY entry come back `unknown`
  // with the reason buried in its own `incomplete` list, which across hundreds of entries reads like the scan
  // simply did not work. Check it once, here, where the whole function list is in hand, and say so loudly.
  std::set<std::string> initSeen;
  std::set<std::string> autoCtors;  // see --no-auto-ctor
  auto noteInitFns = [&](const std::vector<frontend::FunctionInfo> &fns) {
    for (auto &f : fns) {
      if (std::find(sopt.initFunctions.begin(), sopt.initFunctions.end(), f.name) != sopt.initFunctions.end()) initSeen.insert(f.name);
      // The frontend writes each `__attribute__((constructor))` down as a wrapper function (Frontend.cpp, and
      // Sec.22.488 for why): in a real process the loader has already run these before any API call, so they go
      // FIRST, ahead of whatever --init-fn the user named for the library's own API sequence. Sorted by name,
      // which is sorted by the priority the name encodes.
      if (autoCtor && f.name.rfind("__hlir_ctor.", 0) == 0) autoCtors.insert(f.name);
    }
    // Prepend them HERE, not after the job loop: scan::discover() below writes each entry's `init:` list into
    // the spec it generates, so a list amended afterwards would be amended too late and the prologue would
    // silently not run -- which is exactly the failure `init:` exists to remove.
    for (auto it = autoCtors.rbegin(); it != autoCtors.rend(); ++it) {
      if (std::find(sopt.initFunctions.begin(), sopt.initFunctions.end(), *it) != sopt.initFunctions.end()) continue;
      sopt.initFunctions.insert(sopt.initFunctions.begin(), *it);
      initSeen.insert(*it);
    }
  };
  auto addJobs = [&](const std::string &path0, const std::vector<frontend::FunctionInfo> &fns, const std::vector<frontend::FunctionInfo> &allFns,
                     const std::shared_ptr<const std::string> &core, const std::map<std::string, std::string> &fileOf) -> int {
    noteInitFns(allFns);
    std::vector<scan::Entry> entries;
    if (onlyNames.empty()) entries = scan::discover(fns, sopt);
    else
      for (auto &f : fns)
        if (std::find(onlyNames.begin(), onlyNames.end(), f.name) != onlyNames.end()) { auto e = scan::makeEntry(f, sopt, allFns); e.why = "requested"; entries.push_back(e); }
    for (auto &e : entries) {
      std::string path = path0;
      if (path.empty()) { auto it = fileOf.find(e.function); path = it == fileOf.end() ? std::string("?") : it->second; }
      if (!e.skipReason.empty()) { skipped.push_back({path, e.function, e.skipReason, e.line}); continue; }
      Job j;
      for (auto &pre : base.preconditions) {
        std::string resolved, perr;
        if (!scan::resolvePreconditionFields(pre.second, pre.first, allFns, resolved, perr)) { std::cerr << "hlir-scan: " << perr << "\n"; return 2; }
        j.pre.push_back({pre.first, resolved});
      }
      j.file = path;
      j.entry = e.function;
      j.why = e.why;
      j.line = e.line;
      j.core = core;
      j.specText = e.specText;
      std::string spath = outDir.empty() ? "" : outDir + "/specs/" + safeName(path) + "__" + e.function + ".yaml";
      if (!specDir.empty()) {
        bool sok;
        std::string t = slurp(specDir + "/" + e.function + ".yaml", sok);
        if (sok) {
          // A hand-written spec REPLACES the generated one, and the generated one is where the project-wide
          // `init:` list is injected (Scan.cpp). So writing a spec used to silently turn the prologue OFF:
          // libssh's wire entry ran with `init_functions: []` and its ELF constructor not run, while the
          // scan had just printed that it would run it. `--init-fn` and the auto-detected constructors are
          // statements about the PROJECT, not about one entry's parameters, so a per-entry spec has no
          // business dropping them -- they are merged in unless the spec states its own `init:`.
          if (!sopt.initFunctions.empty() && t.find("\ninit:") == std::string::npos && t.rfind("init:", 0) != 0) {
            std::string head = "init:\n  functions:\n";
            for (auto &n : sopt.initFunctions) head += "    - " + n + "\n";
            t = head + "\n" + t;
          }
          j.specText = t;
          spath = specDir + "/" + e.function + ".yaml";
          e.notes = {"using the user-written spec " + spath};
        }
      }
      j.specName = spath.empty() ? path + "#" + e.function + ".yaml" : spath;
      if (!outDir.empty() && specDir.empty()) { std::ofstream(spath) << "# generated by hlir-scan from " << path << ":" << e.line << " (" << e.why << ")\n" << e.specText; }
      for (auto &n : e.notes) j.notes += "  note: " + n + "\n";
      j.resultPath = tmp + "/" + safeName(path) + "__" + e.function + ".json";
      all.push_back(std::move(j));
    }
    return 0;
  };
  // A HARNESS IS NEVER IN THE BUILD DATABASE. It is our file, not the project's, so compile_commands.json has
  // no entry for it -- and without one it got no -I at all, failed on the project's first header, and (because
  // --recover is the default) was reported "ok" with nothing in it. The entry function then had no body and the
  // scan announced "0 entries" with no error anywhere above it. Both the nginx and the Fluent Bit profiles were
  // in exactly this state: saved, syntax-checked by scripts/check_profiles.py, dry-run clean, and incapable of
  // reproducing their own BASELINE.md (DESIGN.md Sec.22.455).
  //
  // The flags of another input that IS in the database are the right stand-in: these inputs are being scanned as
  // one program, and a harness is written against the same headers as the code it drives (nginx's even
  // `#include`s src/http/ngx_http_parse.c's neighbourhood). The note says whose flags were borrowed, so this is
  // visible rather than magic.
  const buildinfo::CompileCommand *neighbour = nullptr;
  std::string neighbourFile;
  if (haveBuild)
    for (auto &path : inputs)
      if (const buildinfo::CompileCommand *c = bdb.lookup(path)) { neighbour = c; neighbourFile = path; break; }
  for (auto &path : inputs) {
    bool rok;
    std::string src = slurp(path, rok);
    if (!rok) { fileErrors.push_back(path + ": cannot read"); continue; }
    frontend::LowerOptions fileOpt = lopt;
    if (haveBuild) {
      const buildinfo::CompileCommand *cc = bdb.lookup(path);
      std::string how = cc ? cc->origin : "";
      if (!cc && bdb.common()) { cc = bdb.common(); how = cc->origin + " (common flags: no per-file command)"; }
      if (!cc && neighbour) { cc = neighbour; how = "the compile command of " + neighbourFile + " (this file has none of its own)"; }
      if (cc) {
        buildinfo::FrontendFlags ff = buildinfo::frontendFlags(*cc);
        std::vector<std::string> merged = ff.clangArgs;  // the build's flags first, the command line may add or override
        merged.insert(merged.end(), lopt.clangArgs.begin(), lopt.clangArgs.end());
        fileOpt.clangArgs = merged;
        fileOpt.wrapSignedOverflow = ff.wrapSignedOverflow;
        std::ostringstream n;
        n << path << ": compile options from " << how << ": " << ff.includeDirs << " include dir(s), " << ff.defines << " define(s)" << (ff.wrapSignedOverflow ? ", signed overflow wraps (-fwrapv/-fno-strict-overflow)" : "") << "\n";
        for (auto &w : ff.warnings) n << "    warning: " << w << "\n";
        notes.push_back(n.str());
      } else notes.push_back(path + ": no compile command found for this file in the build source; only the flags given on the command line are used\n");
    }
    std::cerr << "  [lower " << (nfiles + 1) << "/" << inputs.size() << "] " << path << std::flush;
    auto _tLower0 = std::chrono::steady_clock::now();
    frontend::LowerResult low = frontend::lowerC(src, path, fileOpt);
    std::cerr << ": " << (low.ok ? "ok" : "FAILED") << ", "
               << std::chrono::duration<double>(std::chrono::steady_clock::now() - _tLower0).count() << "s\n";
    ++nfiles;
    if (!low.ok) { fileErrors.push_back(path + ": not analysed (clang errors above or unusable translation unit)\n" + low.diagnostics); continue; }
    {
      size_t nlow = 0;
      for (auto &f : low.functions) nlow += f.lowered;
      std::ostringstream n;
      bool any = false;
      if (!low.missingHeaders.empty()) {
        any = true;
        n << path << ": " << low.missingHeaders.size() << " header(s) not found, treated as empty:";
        for (size_t i = 0; i < low.missingHeaders.size() && i < 12; ++i) n << " " << low.missingHeaders[i];
        if (low.missingHeaders.size() > 12) n << " ...";
        n << "\n";
      }
      if (!low.assumedTypes.empty()) {
        any = true;
        n << path << ": " << low.assumedTypes.size() << " unknown type name(s) given a stub typedef (fixed-width names keep their width, others are opaque structs):";
        for (size_t i = 0; i < low.assumedTypes.size() && i < 12; ++i) n << " " << low.assumedTypes[i];
        if (low.assumedTypes.size() > 12) n << " ...";
        n << "\n";
      }
      if (!low.inferredStructs.empty()) {
        any = true;
        n << path << ": " << low.inferredStructs.size() << " struct(s) without a definition were given a layout inferred from the code's member accesses (offsets, sizes and field types are guesses):\n";
        for (auto &t : low.inferredStructs) n << "    " << t << "\n";
      }
      if (nlow != low.functions.size()) {
        any = true;
        n << path << ": " << nlow << "/" << low.functions.size() << " functions lowered; the others are only declared:\n";
        for (auto &f : low.functions)
          if (!f.lowered) n << "    @" << f.name << ": " << f.skipReason << "\n";
      }
      if (any) notes.push_back(n.str());
    }
    if (linkMode) { units.push_back({path, std::move(low)}); continue; }
    // single-file scan: no renaming happens, so the frontend's names are already the final ones
    base.containerOfWaived += low.containerOfWaived;
    base.spawnCallbacks += low.spawnCallbacksEmitted;
    if (base.containerOfFirstSite.empty()) base.containerOfFirstSite = low.containerOfFirstSite;
    for (auto &kv : low.vtableBindings) globalVtableBindings[kv.first].insert(kv.second.begin(), kv.second.end());
    for (auto &kv : low.vtableInstances) globalVtableInstances.insert(kv);
    auto core = std::make_shared<const std::string>(low.core);
    int jrc = addJobs(path, low.functions, low.functions, core, {});
    if (jrc) return jrc;
  }
  if (linkMode) {
    std::vector<link::Unit> lus;
    for (auto &u : units) lus.push_back({u.path, u.low.core, u.low.internalTokens, u.low.addrTakenFunctions, u.low.addrTakenCTypes, u.low.indirectCallCTypes, u.low.dlsymNames});
    link::Result lr = link::linkUnits(lus, link::definedFunctionNames(base.libcText), exposeNames);
    // Say what --expose did. Silence here would be the worst outcome: a name that was NOT honoured leaves the
    // harness calling an undefined declaration, which looks like an ordinary opaque external in the report.
    {
      std::set<std::string> amb(lr.exposeAmbiguous.begin(), lr.exposeAmbiguous.end());
      for (auto &n : lr.exposeApplied)
        std::cerr << "hlir-scan: --expose " << n << ": kept its name; other units now bind to it (this is NOT C linkage)\n";
      for (auto &n : amb)
        std::cerr << "hlir-scan: --expose " << n << ": IGNORED -- more than one unit has a static of that name, so there is no\n"
                     "           single entity to expose. The call stays unresolved.\n";
      for (auto &n : exposeNames)
        if (!amb.count(n) && std::find(lr.exposeApplied.begin(), lr.exposeApplied.end(), n) == lr.exposeApplied.end())
          std::cerr << "hlir-scan: --expose " << n << ": no unit has a static symbol of that name (already visible, or misspelt)\n";
    }
    std::vector<frontend::FunctionInfo> allFns;
    std::map<std::string, std::string> fileOf;  // linked function name -> the file it comes from
    for (size_t k = 0; k < units.size(); ++k) {
      for (auto f : units[k].low.functions) {
        for (auto &c : f.callees) c = link::linkedName(lr, k, c);
        f.name = link::linkedName(lr, k, f.name);
        fileOf[f.name] = units[k].path;
        // A function the frontend could not lower is emitted as a body-less declaration and so ends up opaque like a
        // genuine missing external. Record it (linked name -> reason) so the report tells the two apart: the fix for
        // this one is a compile flag or frontend support, not a model. See AnalysisOptions::notLoweredFns.
        if (!f.lowered) base.notLoweredFns[f.name] = f.skipReason.empty() ? std::string("unsupported construct") : f.skipReason;
        allFns.push_back(std::move(f));
      }
      // The same rename must be applied to the registrations: `static long foo_ioctl()` becomes a per-unit name,
      // and the entry selector matches against linked names. A plain union is right -- two units each registering
      // a different handler in the same slot are both telling the truth (unlike fieldAsserts, where disagreement
      // means one claim must be weakened).
      for (auto &kv : units[k].low.vtableBindings)
        globalVtableBindings[link::linkedName(lr, k, kv.first)].insert(kv.second.begin(), kv.second.end());
      // the per-table grouping needs the same rename on the handler names, and a per-unit prefix on the instance
      // key: two units may each define a `file_operations` on the same line of different files -- the key already
      // carries the file, but statics of the same name in different units must not collide either.
      for (auto &kv : units[k].low.vtableInstances) {
        frontend::VtableInstance vi;
        vi.tag = kv.second.tag;
        for (auto &sl : kv.second.slots) vi.slots[sl.first] = link::linkedName(lr, k, sl.second);
        globalVtableInstances[kv.first] = std::move(vi);
      }
    }
    // a function whose address another file takes (a handler table there) is a callback, wherever it is defined
    {
      std::set<std::string> taken;
      for (size_t k = 0; k < units.size(); ++k)
        for (auto &t : units[k].low.addrTakenFunctions) taken.insert(link::linkedName(lr, k, t.first));
      // a unit that converts the address to another type (no addrTakenCTypes entry) makes it callable through any type
      std::set<std::string> escaped;
      for (size_t k = 0; k < units.size(); ++k)
        for (auto &t : units[k].low.addrTakenFunctions)
          if (!units[k].low.addrTakenCTypes.count(t.first)) escaped.insert(link::linkedName(lr, k, t.first));
      for (auto &f : allFns) {
        if (taken.count(f.name)) f.addrTaken = true;
        if (escaped.count(f.name)) f.cType.clear();
      }
    }
    // a function that another file calls is not a root any more
    std::map<std::string, unsigned> crossCallers;
    for (auto &f : allFns)
      for (auto &c : f.callees)
        if (c != f.name && fileOf.count(c) && fileOf[c] != fileOf[f.name]) ++crossCallers[c];
    for (auto &f : allFns) f.callers += crossCallers[f.name];
    for (auto &n : lr.notes) notes.push_back("link: " + n + "\n");
    {
      std::set<std::string> defd;
      for (auto &f : allFns) defd.insert(f.name);
      std::string un;
      unsigned nun = 0;
      for (auto &n : lr.unresolved) if (!defd.count(n)) { if (nun++ < 40) un += " " + n; }
      notes.push_back("link: " + std::to_string(units.size()) + " unit(s) linked, " + std::to_string(nun) + " function(s) still undefined (library functions, other modules; ModelDB / opaque assumption):" + un + (nun > 40 ? " ..." : "") + "\n");
    }
    {  // a function whose body does not verify (a frontend gap) must not make the whole program unusable: it becomes an external
      std::set<std::string> demoted;
      // WHY each one was demoted. The name alone is not actionable: a demoted function silently becomes
      // an opaque external, so the scan still "succeeds" while the thing under test is gone (measured on
      // CVE-2012-2812, where exif_entry_get_value was demoted and the run reported findings from the
      // harness only). DESIGN.md Sec.22.469.
      std::map<std::string, std::string> why;
      for (int round = 0; round < 25; ++round) {
        Diagnostics d;
        auto m = parseModule(lr.core + "\n" + base.libcText, "linked.core", d);
        bool good = m && !d.hasErrors() && verifyModule(*m, {}, d);
        if (good) break;
        std::set<std::string> bad;
        std::string msg = d.str();
        for (size_t p = 0; (p = msg.find("[@", p)) != std::string::npos; ) {
          size_t e = msg.find_first_of(",]", p + 2);
          if (e == std::string::npos) break;
          bad.insert(msg.substr(p + 2, e - p - 2));
          p = e;
        }
        for (auto it = bad.begin(); it != bad.end();) it = demoted.count(*it) ? bad.erase(it) : std::next(it);
        for (auto &b : bad) {
          size_t at = msg.find("[@" + b);
          size_t ls = at == std::string::npos ? std::string::npos : msg.rfind('\n', at);
          size_t le = at == std::string::npos ? std::string::npos : msg.find('\n', at);
          if (at != std::string::npos)
            why[b] = msg.substr(ls == std::string::npos ? 0 : ls + 1,
                                (le == std::string::npos ? msg.size() : le) - (ls == std::string::npos ? 0 : ls + 1));
        }
        if (bad.empty()) { notes.push_back("link: the linked module does not verify and no function can be blamed:\n" + msg.substr(0, 600) + "\n"); break; }
        lr.core = demoteFunctions(lr.core, bad);
        demoted.insert(bad.begin(), bad.end());
      }
      if (!demoted.empty()) {
        std::string l;
        for (auto &n : demoted) {
          l += "\n    @" + n;
          auto w = why.find(n);
          if (w != why.end() && !w->second.empty()) l += "   <- " + w->second.substr(0, 300);
        }
        notes.push_back("link: " + std::to_string(demoted.size()) +
                        " function(s) whose lowered body does not verify are treated as external (opaque)."
                        " THE SCAN NO LONGER COVERS THEM -- if one of these is what you meant to test, the"
                        " result is about the harness:" + l + "\n");
      }
    }
    if (discoverRegistered) {  // --entries registered: run @main, bind the captured handlers, then scan as iface
      auto disc = discoverRegisteredEntries(lr.core, base.libcText, base.models, discoverArgv, discoverPassFns,
                                            discoverSymbolic, base.wallSeconds);
      for (auto &kv : disc) globalVtableBindings[kv.first].insert(kv.second.begin(), kv.second.end());
    }
    {  // whole-program used-fields: a field only read via a cross-unit call (no body visible in the unit that declared the
       // pointer to it) is still "used" once every unit's own view is combined (see pruneUnusedLinkFields above)
      std::set<std::string> globalFieldUses, globalNullTested;
      for (auto &u : units) {
        globalFieldUses.insert(u.low.fieldUses.begin(), u.low.fieldUses.end());
        globalNullTested.insert(u.low.fieldNullTests.begin(), u.low.fieldNullTests.end());
        // bounds the code asserts about its own members: the assertion is almost never in the unit that declares
        // the handler, so only the union is usable. Keep the WEAKER claim when two units disagree, for the same
        // reason AssertBoundFinder does: over-constraining hides defects (DESIGN.md §22.358).
        base.containerOfWaived += u.low.containerOfWaived;
        base.spawnCallbacks += u.low.spawnCallbacksEmitted;
        if (base.containerOfFirstSite.empty()) base.containerOfFirstSite = u.low.containerOfFirstSite;
        for (auto &kv : u.low.fieldAsserts) {
          auto it = globalAsserts.find(kv.first);
          if (it == globalAsserts.end()) { globalAsserts[kv.first] = kv.second; continue; }
          frontend::AssertedBound &a = it->second;
          if (kv.second.hasHi && a.hasHi) a.hi = std::max(a.hi, kv.second.hi); else if (!kv.second.hasHi) a.hasHi = false;
          if (kv.second.hasLo && a.hasLo) a.lo = std::min(a.lo, kv.second.lo); else if (!kv.second.hasLo) a.hasLo = false;
        }
      }
      for (auto &kv : globalAsserts) {
        if (noFieldBounds) break;
        FieldBound b;
        b.hasLo = kv.second.hasLo; b.hasHi = kv.second.hasHi;
        b.lo = kv.second.lo;       b.hi = kv.second.hi;
        b.bits = kv.second.bits;   b.isSigned = kv.second.isSigned;
        globalFieldBounds[kv.first] = b;
      }
      if (getenv("HLIR_DEBUG_FIELDBOUNDS"))
        for (auto &kv : globalFieldBounds)
          std::cerr << "fieldbound " << kv.first << " lo=" << (kv.second.hasLo ? std::to_string(kv.second.lo) : "-")
                    << " hi=" << (kv.second.hasHi ? std::to_string(kv.second.hi) : "-") << " bits=" << kv.second.bits << "\n";
      pruneUnusedLinkFields(allFns, globalFieldUses);
      markNullTestedLinkFields(allFns, globalNullTested);
    }
    if (!dumpLinked.empty()) std::ofstream(dumpLinked) << lr.core;
    auto core = std::make_shared<const std::string>(lr.core);
    int jrc = addJobs("", allFns, allFns, core, fileOf);
    if (jrc) return jrc;
  }

  // A `--entry NAME` that matched no function is an ERROR, not a quiet omission (DESIGN.md §22.441).
  //
  // scan-profiles/expat asked for four entries and got one: `harness_expat_split` where the harness defines
  // `harness_expat_parse_split`, and two more like it. Every acceptance gate passed, because `entries: ">0"`
  // is true of one entry out of four, and three quarters of the declared attack surface -- the split-buffer
  // path, namespaces, and parameter-entity parsing -- was never scanned at all. That is the same class of
  // failure as the three in docs/SCAN_SETUP_CHECKLIST.md: the scan runs, reports, and measures something
  // other than what was asked, with nothing in the output saying so.
  //
  // A name that WAS found and then skipped for a stated reason is not missing: the skip is printed.
  if (!onlyNames.empty()) {
    std::vector<std::string> missing;
    for (auto &n : onlyNames) {
      bool got = false;
      for (auto &j : all) got = got || j.entry == n;
      for (auto &sk : skipped) got = got || sk.entry == n;
      if (!got) missing.push_back(n);
    }
    if (!missing.empty()) {
      std::cerr << "hlir-scan: " << missing.size() << " of " << onlyNames.size()
                << " requested entry name(s) are not a function in this program:";
      for (auto &n : missing) std::cerr << " " << n;
      std::cerr << "\n  A --entry that matches nothing silently shrinks the scan to the names that do match.\n";
      return 2;
    }
  }

  // `--dump-vtables FILE`: the handler registrations found, one `tag#field <TAB> @function` line per binding,
  // sorted. Diagnostic only -- nothing in a normal scan reads this file, and whether it is written changes no
  // verdict. It exists so a run can be cross-checked against the sources (`grep -rn 'struct file_operations.*= {'`)
  // before the entry selector is allowed to depend on it (DESIGN.md §22.359).
  if (!dumpVtables.empty()) {
    std::map<std::string, std::set<std::string>> bySlot;  // tag#field -> handlers
    for (auto &kv : globalVtableBindings)
      for (auto &slot : kv.second) bySlot[slot].insert(kv.first);
    std::ofstream o(dumpVtables);
    size_t n = 0;
    for (auto &kv : bySlot)
      for (auto &fn : kv.second) { o << kv.first << "\t@" << fn << "\n"; ++n; }
    // ... and the same registrations grouped by the TABLE they belong to. A module registers many tables of one
    // type, so "some function is in a `file_operations#open`" does not pair that `open` with a given `ioctl`;
    // this does, which is what resolving a session constructor needs (DESIGN.md §22.368 §7).
    o << "\n# by table instance\n";
    for (auto &kv : globalVtableInstances) {
      o << kv.first << "\n";
      for (auto &sl : kv.second.slots) o << "\t" << sl.first << "\t@" << sl.second << "\n";
    }
    std::cerr << "hlir-scan: " << n << " vtable binding(s) in " << bySlot.size() << " slot(s), "
              << globalVtableInstances.size() << " table instance(s) -> " << dumpVtables << "\n";
  }

  // `--entries iface` coverage: how much of what this code registers the model set actually describes. Printed
  // unconditionally for that mode, because the failure this guards against is SILENT -- a subsystem whose tables
  // no model names yields zero entries and then exits 0, looking exactly like a clean scan. The unmodelled tags
  // are the list of interfaces worth modelling next, which is what bounds this mode's usefulness.
  if (sopt.mode == scan::EntryMode::Iface) {
    std::map<std::string, size_t> modelled, unmodelled;
    for (auto &kv : globalVtableBindings)
      for (auto &key : kv.second) {
        size_t h = key.find('#');
        if (h == std::string::npos) continue;
        std::string tag = key.substr(0, h);
        const iface::InterfaceModel *m = ifaces.byStruct(tag);
        ((m && m->slot(key.substr(h + 1))) ? modelled : unmodelled)[tag]++;
      }
    size_t nm = 0;
    std::cerr << "hlir-scan: iface entries from";
    for (auto &kv : modelled) { nm += kv.second; std::cerr << " " << kv.first << "(" << kv.second << ")"; }
    if (modelled.empty()) std::cerr << " nothing";
    std::cerr << " -> " << all.size() << " entries\n";
    std::vector<std::pair<size_t, std::string>> rest;
    for (auto &kv : unmodelled) rest.push_back({kv.second, kv.first});
    std::sort(rest.rbegin(), rest.rend());
    if (!rest.empty()) {
      size_t tot = 0;
      for (auto &r : rest) tot += r.first;
      std::cerr << "hlir-scan: " << tot << " registration(s) in " << rest.size() << " struct(s) no model describes, not scanned:";
      for (size_t k = 0; k < rest.size() && k < 10; ++k) std::cerr << " " << rest[k].second << "(" << rest[k].first << ")";
      if (rest.size() > 10) std::cerr << " ...";
      std::cerr << "\n";
    }
    if (nm == 0)
      std::cerr << "hlir-scan: WARNING: --entries iface found no registration this model set describes, so nothing was scanned.\n"
                   "           Either these files register no modelled interface, or the interface is missing from " << interfacesDir
                << ". Use --dump-vtables to see what was found.\n";
  }

  // Constructors run first, ahead of any --init-fn: the loader runs before the program does. They were
  // prepended in noteInitFns (see there for why it has to happen that early); this only says so out loud.
  if (!autoCtors.empty()) {
    std::cerr << "hlir-scan: " << autoCtors.size() << " ELF constructor(s) run before every entry (--no-auto-ctor to skip):";
    for (auto &n : autoCtors) std::cerr << " " << n.substr(n.find('.', 12) + 1);
    std::cerr << "\n";
  }

  // A `--init-fn` nobody defines is a project-wide input error, not a per-entry one: every entry would come back
  // `unknown` with the reason buried in its own `incomplete` list. Fail here instead, once, before any work.
  {
    std::string missing;
    for (auto &n : sopt.initFunctions)
      if (!initSeen.count(n)) missing += (missing.empty() ? "" : ", ") + n;
    if (!missing.empty()) {
      std::cerr << "hlir-scan: --init-fn names no function of these sources: " << missing
                << "\n           The initialiser must be IN the scanned set (with --link, in the link set): running a function "
                   "that is only declared would do nothing, and a prologue that silently does nothing is exactly what "
                   "`init:` exists to remove. Use --list to see what was found.\n";
      return 2;
    }
  }

  if (list) {
    for (auto &j : all) std::cout << j.file << ":" << j.line << "  @" << j.entry << "  [" << j.why << "]\n" << j.notes;
    for (auto &s : skipped) std::cout << s.file << ":" << s.line << "  @" << s.entry << "  skipped: " << s.why << "\n";
    for (auto &e : fileErrors) std::cerr << e << "\n";
    std::cout << all.size() << " entries (" << skipped.size() << " skipped) in " << nfiles << " file(s)\n";
    return fileErrors.empty() ? 0 : 2;
  }

  // ---------------------------------------------------------------- pre-parse: once per distinct `core` text, before
  // any job sharing it is forked. A `--link` program's text can be hundreds of MB; parsing (and verifying) it
  // dominates a single entry's analysis time, and with `jobs` entries sharing the same `--link` program that cost
  // was previously paid once per entry (once per forked worker, since each only inherited the *text*, not an
  // already-parsed Module) instead of once for the whole scan. See docs/DESIGN.md §22.12/§22.13 for the measurements
  // that motivated this. `fork()` gives every worker its own copy-on-write view of the Module built here, so parsing
  // it in THIS (parent) process before the loop below starts forking is what makes the sharing free — a worker that
  // later appends its own harness (`parseModuleInto` in `analyzeEntry`) only mutates its own copy-on-write pages.
  //
  // Failure here just means a job keeps its `parsedBase` unset and falls back to parsing its own `core` text inside
  // its worker, exactly as before this pre-parse pass existed — this is purely an optimisation, never a new way for
  // a scan to fail or to report a different diagnostic than it would have without it.
  {
    std::unordered_map<const std::string *, std::shared_ptr<Module>> parsed;
    size_t distinct = 0;
    for (auto &j : all)
      if (j.core && !parsed.count(j.core.get())) { parsed[j.core.get()] = nullptr; ++distinct; }
    parsed.clear();
    if (distinct > 0)
      std::cerr << "hlir-scan: parsing " << distinct << " distinct source blob(s) before forking workers"
                    " (this is the one-time --link lowering/parse cost; no per-entry progress until it's done)\n";
    size_t doneBlobs = 0;
    for (auto &j : all) {
      if (!j.core) continue;
      auto it = parsed.find(j.core.get());
      if (it == parsed.end()) {
        auto t0 = std::chrono::steady_clock::now();
        std::string text = *j.core + (base.libcText.empty() ? "" : "\n" + base.libcText);
        Diagnostics pd;
        auto m = parseModule(text, j.file, pd);
        bool ok = m && verifyModule(*m, {}, pd);
        size_t nFuncs = ok ? m->functions.size() : 0;
        if (ok) it = parsed.emplace(j.core.get(), std::shared_ptr<Module>(m.release())).first;
        else it = parsed.emplace(j.core.get(), nullptr).first;  // leave unset; the worker will redo (and report) this itself
        double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        std::cerr << "  [parse " << ++doneBlobs << "/" << distinct << "] " << text.size() << " bytes"
                   << (ok ? ", " + std::to_string(nFuncs) + " functions: ok" : ": FAILED (workers will redo it)")
                   << ", " << secs << "s\n";
      }
      if (it->second) j.parsedBase = it->second;
    }
  }

  // ---- --check-invariant: instrument the loop, then let the ordinary pipeline decide it.
  //
  // The whole point of doing this HERE rather than in a standalone tool is that everything the check needs
  // is already set up: the real harness builds the objects the loop compares against, the ModelDB gives the
  // externals semantics, an unmatched indirect call is opaque instead of fatal, and a violation comes back
  // as a normal finding with a witness and a replay.
  std::string invMessage;
  if (!checkInvariant.empty()) {
    size_t c1 = checkInvariant.find(':'), c2 = checkInvariant.find(':', c1 + 1);
    if (c1 == std::string::npos || c2 == std::string::npos) {
      std::cerr << "hlir-scan: --check-invariant wants FUNCTION:HEADER:EXPR\n";
      return 2;
    }
    std::string ifn = checkInvariant.substr(0, c1);
    std::string ihdr = checkInvariant.substr(c1 + 1, c2 - c1 - 1);
    std::string iexpr = checkInvariant.substr(c2 + 1);
    if (!ihdr.empty() && ihdr[0] == '^') ihdr = ihdr.substr(1);
    // Only the PARSED module is instrumented, never `j.core`. The worker inherits the parsed module
    // copy-on-write and appends its own harness to it; the text is what a worker falls back to when the
    // pre-parse failed, and it is the unit's text WITHOUT the ModelDB -- printing the parsed module back
    // into it duplicates every libc definition and the worker's parse fails with no report at all.
    std::set<const Module *> seenMods;
    unsigned done = 0;
    for (auto &j : all) {
      if (!j.parsedBase) {
        std::cerr << "hlir-scan: --check-invariant needs the pre-parsed module, which this run does not have\n";
        return 2;
      }
      if (!seenMods.insert(j.parsedBase.get()).second) continue;
      InvariantInstrumentation ins =
          instrumentInvariant(*j.parsedBase, ifn, ihdr, iexpr, false, invariantAssert,
                              sopt.label.empty() ? std::string("network") : sopt.label);
      if (!ins.error.empty()) {
        if (ins.error.rfind("no function body", 0) == 0 || ins.error.find("has no loop") != std::string::npos)
          continue;  // this program does not define it
        std::cerr << "hlir-scan: --check-invariant: " << ins.error << "\n";
        return 2;
      }
      invMessage = ins.assertMessage;
      Diagnostics vd;
      if (!verifyModule(*j.parsedBase, {}, vd)) {
        std::cerr << "hlir-scan: the instrumented module does not verify:\n" << vd.str();
        return 2;
      }
      ++done;
    }
    if (!done) {
      std::cerr << "hlir-scan: --check-invariant: no analysed unit defines @" << ifn << " with a loop ^" << ihdr << "\n";
      return 2;
    }
    std::cerr << "hlir-scan: invariant instrumented at @" << ifn << " ^" << ihdr << ": " << iexpr << "\n";
  }


  // ---------------------------------------------------------------- run: a pool of forked workers
  size_t nextJob = 0, running = 0, finished = 0;
  std::vector<Job *> active;
  auto launch = [&](Job &j) {
    std::cout.flush();
    std::cerr.flush();
    pid_t pid = fork();
    if (pid == 0) {
      int rc = workerMain(j, base);
      _exit(rc);
    }
    j.pid = pid;
    j.started = std::chrono::steady_clock::now();
    if (pid < 0) { j.done = true; j.status = -1; ++finished; return; }
    active.push_back(&j);
    ++running;
  };
  base.wallSeconds = std::max(1.0, timeoutS * 0.7);  // the engines stop themselves and keep their findings; the kill at --timeout is the backstop
  std::cerr << "hlir-scan: " << all.size() << " entries, " << jobs << " worker(s), " << timeoutS << "s per entry\n";
  while (finished < all.size()) {
    while (running < jobs && nextJob < all.size()) launch(all[nextJob++]);
    for (size_t k = 0; k < active.size();) {
      Job &j = *active[k];
      int st = 0;
      pid_t r = waitpid(j.pid, &st, WNOHANG);
      bool elapsed = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - j.started).count() >= static_cast<long>(timeoutS);
      if (r == 0 && elapsed) { kill(j.pid, SIGKILL); waitpid(j.pid, &st, 0); j.timedOut = true; r = j.pid; }
      if (r == j.pid) {
        j.done = true;
        j.status = st;
        ++finished;
        --running;
        double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - j.started).count();
        std::string verdict = "no_result";
        if (j.timedOut) verdict = "timeout";
        else if (WIFSIGNALED(j.status)) verdict = "crashed";
        else {
          bool rok = false;
          std::string text = slurp(j.resultPath, rok);
          report::Report one;
          std::string err;
          if (rok && report::fromJson(text, one, err) && !one.entries.empty()) verdict = vname(one.entries[0].verdict);
        }
        std::cerr << "  [" << finished << "/" << all.size() << "] @" << j.entry << " (" << j.file << "): "
                   << verdict << ", " << secs << "s\n";
        active.erase(active.begin() + static_cast<long>(k));
      } else ++k;
    }
    if (finished < all.size()) std::this_thread::sleep_for(std::chrono::milliseconds(20));
  }

  // ---------------------------------------------------------------- collect
  report::Report combined;
  combined.tool = "hlir-scan";
  unsigned nBug = 0, nUnknown = 0, nSafe = 0, nBounded = 0;
  for (auto &j : all) {
    bool rok = false;
    std::string text = slurp(j.resultPath, rok);
    report::Report one;
    std::string err;
    if (j.timedOut) j.result = inconclusive(j, "timeout", "the worker was stopped after " + std::to_string(timeoutS) + "s (raise --timeout)");
    else if (WIFSIGNALED(j.status)) j.result = inconclusive(j, "crashed", "the worker died with signal " + std::to_string(WTERMSIG(j.status)));
    else if (rok && report::fromJson(text, one, err) && !one.entries.empty()) j.result = one.entries[0];
    else j.result = inconclusive(j, "no_result", "the worker produced no readable report" + (err.empty() ? "" : ": " + err));
    j.result.function = j.entry;
    if (outDir.empty()) std::remove(j.resultPath.c_str());
    if (j.result.verdict == report::Verdict::Bug) ++nBug;
    else if (j.result.verdict == report::Verdict::Unknown) ++nUnknown;
    else if (j.result.verdict == report::Verdict::SafeUpToLoopBound) ++nBounded;
    else ++nSafe;
    combined.entries.push_back(j.result);
  }
  if (outDir.empty()) rmdir(tmp.c_str());

  std::string body;
  if (format == "json") body = report::toJson(combined);
  else if (format == "sarif") body = report::toSarif(combined);
  else {
    std::ostringstream o;
    o << "scan summary\n";
    for (size_t i = 0; i < all.size(); ++i) {
      auto &j = all[i];
      auto &r = combined.entries[i];
      std::set<std::string> kinds;
      unsigned confirmed = 0;
      for (auto &f : r.findings) { kinds.insert(f.kind); confirmed += f.replay == report::ReplayStatus::Confirmed; }
      std::string ks;
      for (auto &k : kinds) ks += (ks.empty() ? "" : ",") + k;
      o << "  " << (r.verdict == report::Verdict::Bug ? "BUG    " : r.verdict == report::Verdict::Unknown ? "UNKNOWN" : r.verdict == report::Verdict::SafeUpToLoopBound ? "bounded" : "safe   ") << "  " << j.file << ":" << j.line << "  @" << j.entry
        << "  [" << j.why << "]";
      if (!r.findings.empty()) o << "  " << r.findings.size() << " finding(s) (" << confirmed << " replay-confirmed): " << ks;
      for (auto &inc : r.incomplete) o << "  incomplete:" << inc.code;
      if (r.coverage.measured) {
        char cb[32]; std::snprintf(cb, sizeof cb, "%.0f%%", 100.0 * r.coverage.blockRatio()); o << "  cov " << cb;
        char bb[32]; std::snprintf(bb, sizeof bb, "%.0f%%", 100.0 * r.coverage.branchRatio()); o << " br " << bb;
      }
      o << "  " << r.metrics.secondsTotal << "s\n";
    }
    for (auto &s : skipped) o << "  skipped  " << s.file << ":" << s.line << "  @" << s.entry << "  " << s.why << "\n";
    o << "\n" << all.size() << " entries analysed: " << nBug << " with bugs, " << nUnknown << " inconclusive, " << nSafe << " safe under the assumptions";
    if (nBounded) o << ", " << nBounded << " safe up to the loop bound";
    o << "; " << skipped.size() << " skipped, " << nfiles << " file(s)\n";
    {  // the dry-run list: external functions that were actually CALLED with no model behind them, ranked.
       // The static list of unmodelled declarations says what COULD be hit; this says what was, which is the
       // worklist for "which model to write next" (DESIGN.md §22.373). An opaque call returns an unconstrained
       // value and has NO EFFECT ON MEMORY -- so one that is meant to fill a caller's buffer leaves it zeroed and
       // every later check of that buffer is decided on a state the program never has.
      std::map<std::string, uint64_t> opaque;
      for (auto &e : combined.entries)
        for (auto &c : e.opaqueCalls) opaque[c.first] += c.second;
      if (!opaque.empty()) {
        std::vector<std::pair<std::string, uint64_t>> v(opaque.begin(), opaque.end());
        std::sort(v.begin(), v.end(), [](auto &a, auto &b) { return a.second > b.second; });
        std::set<std::string> skipped_;
        for (auto &sk : base.externSkips) skipped_.insert(sk.function);
        size_t nSkipped = 0;
        for (auto &kv : opaque) nSkipped += skipped_.count(kv.first) ? 1 : 0;
        o << "\nunmodelled external functions actually called (" << v.size() << "), most-called first --"
             " each returns an unconstrained value and writes nothing";
        if (nSkipped) o << "; " << nSkipped << " marked [skip] were examined and judged not to contribute (--externs)";
        o << ":\n";
        for (size_t i = 0; i < v.size() && i < 25; ++i)
          o << "  " << v[i].second << "x  " << v[i].first << (skipped_.count(v[i].first) ? "  [skip]" : "") << "\n";
        if (v.size() > 25) o << "  ... and " << (v.size() - 25) << " more\n";
      }
    }
    {  // call depth: of the findings (stack at the failing operation) and of the deepest run of each entry
      std::map<unsigned, unsigned> byDepth;
      std::vector<std::pair<unsigned, std::string>> deepest;
      std::vector<unsigned> runDepth;
      for (auto &e : combined.entries) {
        if (e.metrics.maxCallDepth) runDepth.push_back(e.metrics.maxCallDepth);
        for (auto &f : e.findings) {
          if (f.callStack.empty()) continue;
          ++byDepth[static_cast<unsigned>(f.callStack.size())];
          std::string chain = f.kind + (f.replay == report::ReplayStatus::Confirmed ? " [confirmed]" : "") + ": ";
          for (size_t i = 0; i < f.callStack.size(); ++i) chain += (i ? " -> " : "") + f.callStack[i];
          deepest.push_back({static_cast<unsigned>(f.callStack.size()), chain});
        }
      }
      if (!byDepth.empty()) {
        unsigned total = 0;
        for (auto &kv : byDepth) total += kv.second;
        o << "call depth of findings (frames from the entry function to the failing operation), " << total << " finding(s):";
        for (auto &kv : byDepth) o << "  " << kv.first << ":" << kv.second;
        o << "\n";
        std::sort(deepest.begin(), deepest.end(), [](auto &a, auto &b) { return a.first > b.first; });
        for (size_t i = 0; i < deepest.size() && i < 3; ++i) o << "  deepest " << deepest[i].first << ": " << deepest[i].second << "\n";
      }
      if (!runDepth.empty()) {
        std::sort(runDepth.begin(), runDepth.end());
        o << "deepest call stack reached per entry: median " << runDepth[runDepth.size() / 2] << ", 90th percentile " << runDepth[runDepth.size() * 9 / 10] << ", max " << runDepth.back() << " (" << runDepth.size() << " entries)\n";
      }
    }
    for (auto &e : fileErrors) o << "file error: " << e << "\n";
    for (auto &n : notes) o << "note: " << n;
    for (size_t i = 0; i < all.size(); ++i) {
      auto &r = combined.entries[i];
      if (r.verdict == report::Verdict::SafeUnderAssumptions && !verbose) continue;
      report::Report one;
      one.entries.push_back(r);
      o << "\n" << all[i].notes << report::toText(one);
    }
    body = o.str();
  }
  // ---- the loop inventory for the invariant experiment (--dump-loops). Written from the PARENT, which
  // already holds every job's parsed Module (the pre-parse pass above) and every job's result.
  // ---- the uncovered conditional edges (--dump-branches). Written from the PARENT out of the combined report,
  // so one file covers every entry and the classification is the engine's, not a reading of the source.
  if (!dumpBranches.empty()) {
    std::ofstream o(dumpBranches);
    if (!o) {
      std::cerr << "hlir-scan: cannot write " << dumpBranches << "\n";
    } else {
      size_t total = 0;
      for (auto &r : combined.entries) {
        const report::Coverage &c = r.coverage;
        if (!c.measured) continue;
        o << "# @" << r.function << "  branches " << c.branchesVisited << "/" << c.branchesReachable
          << "  not covered: open=" << c.missOpen << " unsat=" << c.missUnsat << " const=" << c.missConst
          << " unreached=" << c.missUnreached << " global_init=" << c.missGlobalInit << "\n";
        // Grouped by reason, because the reason is the only thing that decides what to do next: `open` is a
        // budget or a search-guidance question, `global_init` is an `init:`/G2 question and NOT a budget one
        // (DESIGN.md Sec.22.465), `unsat` and `const` are not questions at all, and `unreached` points upstream
        // of the edge. This list is exhaustive BY CONTRACT: a class missing from it is dropped from the dump
        // silently while the header still counts it, which is how `global_init` rows vanished the first time.
        for (const char *why : {"open", "global_init", "unsat", "const", "unreached"})
          for (auto &b : c.branchesMissed) {
            if (b.why != why) continue;
            ++total;
            o << why << "\t" << (b.file.empty() ? "<model>" : b.file) << ":" << b.line << ":" << b.column
              << "\t" << (b.dir ? "true" : "false") << "\t@" << b.function << "\n";
          }
      }
      // The cap is no longer 400 and is no longer a literal: DESIGN.md Sec.22.445 raised it to 50000 with
      // HLIR_MAX_MISSED_BRANCHES, and a message that names a stale number is worse than no message -- it
      // tells the reader the dump is a 400-entry sample when it is complete, which is exactly the wrong
      // conclusion to draw from a coverage dump. Ask for the real cap and only say "capped" when it bit.
      const size_t cap = hlir::driver::maxMissedBranchesPerEntry();
      std::cerr << "hlir-scan: " << total << " uncovered conditional edge(s) -> " << dumpBranches
                << (total >= cap ? ("  (capped at " + std::to_string(cap) + " per entry; raise with "
                                    "HLIR_MAX_MISSED_BRANCHES)") : std::string())
                << "\n";
    }
  }
  if (!dumpLoops.empty()) {
    std::ostringstream js;
    js << "{\n  \"tool\": \"hlir-scan --dump-loops\",\n  \"loops\": [\n";
    size_t emitted = 0, skippedEntries = 0, considered = 0;
    for (auto &j : all) {
      if (!j.parsedBase) continue;
      const report::EntryReport &r = j.result;
      // (1) an entry that reached a verdict has nothing to buy.
      bool openQuestion = r.verdict == report::Verdict::Unknown || !r.incomplete.empty();
      if (!openQuestion) { ++skippedEntries; continue; }
      std::map<std::string, const report::EntryReport::FrontierSite *> fs;
      for (auto &s2 : r.frontier) fs[s2.function] = &s2;
      std::string inc;
      for (auto &i : r.incomplete) inc += (inc.empty() ? "" : ",") + i.code;
      for (auto &fn : j.parsedBase->functions) {
        if (fn->isDeclaration()) continue;
        auto it = fs.find(fn->name);
        if (it == fs.end()) continue;  // the search never spent a flip here
        const auto *st = it->second;
        for (const Loop &ls : loopsOf(*fn)) {
          ++considered;
          // (2) a real share of the budget, and (3) not already handled exactly.
          bool selected = st->share >= 0.05 && !st->library && !st->foldCandidate && ls.checks > 0;
          js << (emitted++ ? ",\n" : "") << "    {"
             << "\"entry\": \"" << jesc(r.function) << "\", \"entry_verdict\": \""
             << report::verdictName(r.verdict) << "\", \"incomplete\": \"" << jesc(inc) << "\""
             << ", \"function\": \"" << jesc(fn->name) << "\", \"header\": \"" << jesc(ls.header->name) << "\""
             << ", \"file\": \"" << jesc(ls.file) << "\", \"line\": " << ls.line
             << ", \"blocks\": " << ls.body.size() << ", \"calls\": " << ls.calls
             << ", \"checks\": " << ls.checks << ", \"nested\": " << (ls.nested ? "true" : "false")
             << ", \"fn_share\": " << st->share << ", \"fn_flippable_pcs\": " << st->flippablePcs
             << ", \"fn_per_call\": " << st->perCall << ", \"fn_calls\": " << st->calls
             << ", \"fn_library\": " << (st->library ? "true" : "false")
             << ", \"fn_fold_candidate\": " << (st->foldCandidate ? "true" : "false")
             << ", \"selected\": " << (selected ? "true" : "false")
             << ", \"source\": \"" << jesc(sourceWindow(ls.file, ls.line, 6, 40)) << "\"}";
        }
      }
    }
    js << "\n  ],\n  \"note\": \"selected = the entry reached no verdict AND the loop's function holds >=5% of "
          "the flippable path conditions AND it is not a library/fold candidate AND the loop contains at least "
          "one UB check. Entries that already reached a verdict contribute nothing.\"\n}\n";
    std::ofstream o(dumpLoops);
    o << js.str();
    std::cerr << "hlir-scan: " << considered << " loop(s) in budget-carrying functions, " << emitted
              << " recorded, " << skippedEntries << " entr(ies) skipped (already decided) -> " << dumpLoops << "\n";
  }

  // ---- the unmodelled-external work queue (--model-todo).
  //
  // `opaque_calls` already says, per entry, which bodyless external a run actually CALLED -- the number that
  // says which model to write next, as opposed to the static list of what COULD be hit. It is also the thing
  // that quietly decides results: §22.388's `aresx_sztoui` cleared taint on every digit conversion, and
  // linking it moved c-ares CVE-2023-31130's detection threshold from 10000 runs to 100. Per scan it is easy
  // to skim past; accumulated across scans it is a ranked backlog.
  //
  // Merge rather than overwrite: each scan only sees the externals of ITS targets, and the queue is useful
  // exactly because it remembers the others. Indirect-call placeholders are left out: nobody can model those.
  if (!modelTodo.empty()) {
    std::map<std::string, std::pair<uint64_t, std::set<std::string>>> todo;  // name -> (calls, entries)
    {
      std::ifstream in(modelTodo);
      for (std::string line; std::getline(in, line);) {
        if (line.size() < 3 || line[0] != '|') continue;  // only our own table rows
        std::vector<std::string> col;
        for (size_t i = 1, j; i <= line.size(); i = j + 1) {
          j = line.find('|', i);
          if (j == std::string::npos) break;
          std::string c = line.substr(i, j - i);
          size_t a2 = c.find_first_not_of(" \t"), b2 = c.find_last_not_of(" \t");
          col.push_back(a2 == std::string::npos ? std::string() : c.substr(a2, b2 - a2 + 1));
        }
        if (col.size() < 3 || col[0].empty() || col[0] == "function" || col[0][0] == '-') continue;
        uint64_t n = 0;
        try { n = std::stoull(col[1]); } catch (...) { continue; }
        auto &e = todo[col[0]];
        e.first += n;
        std::istringstream ws(col[2]);
        for (std::string w; ws >> w;) e.second.insert(w);
      }
    }
    for (size_t i = 0; i < combined.entries.size(); ++i)
      for (auto &oc : combined.entries[i].opaqueCalls) {
        if (oc.first.rfind("__hlir_unknown_indirect", 0) == 0) continue;
        auto &e = todo[oc.first];
        e.first += oc.second;
        e.second.insert(combined.entries[i].function);
      }
    std::vector<std::pair<std::string, std::pair<uint64_t, std::set<std::string>>>> rows(todo.begin(), todo.end());
    std::sort(rows.begin(), rows.end(), [](const auto &a, const auto &b) {
      return a.second.first != b.second.first ? a.second.first > b.second.first : a.first < b.first;
    });
    std::ofstream t(modelTodo);
    t << "# Unmodelled external functions, ranked\n\n"
         "Each row is a function some scan CALLED and had no body or model for, so the engine assumed it\n"
         "opaque: arbitrary untainted result, no effect on memory, no effect on taint. That assumption is named\n"
         "in every report it affects, and it is not free -- an opaque call on a taint path CUTS the taint and\n"
         "the search stops being able to reason past it.\n\n"
         "Accumulated by `hlir-scan --model-todo FILE`; re-running merges, so counts are across scans.\n"
         "`calls` is how often it was actually reached, which is the ranking that matters -- not how many\n"
         "declarations exist. Not every row deserves a model: some are genuinely irrelevant, and\n"
         "`models/externs/*.yaml` is where that judgement gets recorded with a reason.\n\n"
         "| function | calls | seen in entries |\n|---|---|---|\n";
    for (auto &r : rows) {
      std::string where;
      size_t shown = 0;
      for (auto &w : r.second.second) {
        if (shown++ == 8) { where += " ..."; break; }
        where += (where.empty() ? "" : " ") + w;
      }
      t << "| " << r.first << " | " << r.second.first << " | " << where << " |\n";
    }
    std::cerr << "hlir-scan: " << rows.size() << " unmodelled external(s) in " << modelTodo << "\n";
  }
  if (output.empty()) std::cout << body;
  else std::ofstream(output) << body;
  if (!outDir.empty()) {
    std::ofstream(outDir + "/scan.json") << report::toJson(combined);
    std::ofstream(outDir + "/scan.sarif") << report::toSarif(combined);
  }
  if (!fileErrors.empty() && all.empty()) return 2;
  return nBug ? 1 : (nUnknown ? 3 : 0);
}

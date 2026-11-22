// Tests for the C frontend: every test/c/*.c is lowered to core (must pass the verifier WITH UB-check coverage),
// linked with the core libc models and run on the interpreter according to its `// RUN:` directives (same syntax as
// test/semantics/*.core).
#include <dirent.h>

#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/driver/Pipeline.h"
#include "hlir/frontend/Frontend.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"

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
  auto low = frontend::lowerC(text, name, {});
  CHECK(low.ok, name << ": lowering failed:\n" << low.diagnostics);
  if (!low.ok) return;
  Diagnostics d0;
  auto alone = parseModule(low.core, name, d0);
  CHECK(alone != nullptr, name << ": generated core does not parse: " << d0.str());
  if (!alone) return;
  VerifyOptions vo;
  vo.checkCoverage = true;
  Diagnostics d2;
  CHECK(verifyModule(*alone, vo, d2), name << ": generated core fails verification: " << d2.str());
  Diagnostics d;
  auto mod = parseModule(low.core + "\n" + slurp(HLIR_MODELS_DIR "/libc.core") + "\n" + slurp(HLIR_MODELS_DIR "/libstdcxx.core"), name, d);
  CHECK(mod != nullptr, name << ": cannot link with libc.core: " << d.str());
  if (!mod) return;
  std::istringstream in(text);
  std::string line;
  while (std::getline(in, line)) {
    auto p = line.find("// RUN:");
    if (p != std::string::npos) runDirective(*mod, name, trim(line.substr(p + 7)));
  }
}

// ---------------------------------------------------------------- entry analysis of C sources (test/c/entry/*.c)
//   // ENTRY: f            function to analyse
//   // SPEC: x.yaml        entry spec next to the source
//   // MODELS: libc        also load models/libc.yaml
//   // EXPECT: safe | bug <ub_kind>
static std::string directive(const std::string &text, const std::string &key) {
  auto p = text.find("// " + key + ":");
  if (p == std::string::npos) return "";
  auto e = text.find('\n', p);
  return trim(text.substr(p + key.size() + 4, e - p - key.size() - 4));
}

static void runEntryFile(const std::string &dir, const std::string &name) {
  std::string text = slurp(dir + "/" + name);
  auto low = frontend::lowerC(text, name, {});
  CHECK(low.ok, name << ": lowering failed:\n" << low.diagnostics);
  if (!low.ok) return;
  driver::AnalysisOptions opt;
  opt.coreText = low.core;
  opt.coreName = name;
  opt.libcText = slurp(HLIR_MODELS_DIR "/libc.core");
  opt.entry = directive(text, "ENTRY");
  std::string spec = directive(text, "SPEC");
  opt.specText = slurp(dir + "/" + spec);
  opt.specName = spec;
  if (directive(text, "MODELS") == "libc") opt.models.push_back({HLIR_MODELS_DIR "/libc.yaml", slurp(HLIR_MODELS_DIR "/libc.yaml")});
  auto out = driver::analyzeEntry(opt);
  CHECK(out.ok, name << ": analysis input error: " << out.error);
  if (!out.ok) return;
  std::string expect = directive(text, "EXPECT");
  auto &e = out.entry;
  if (expect == "safe") {
    CHECK(e.verdict == report::Verdict::SafeUnderAssumptions, name << ": expected safe, got " << report::verdictName(e.verdict) << "\n" << report::toText({"hlir", "0.1", {e}}));
    return;
  }
  std::string kind = expect.rfind("bug ", 0) == 0 ? expect.substr(4) : "";
  CHECK(!kind.empty(), name << ": bad EXPECT line '" << expect << "'");
  CHECK(e.verdict == report::Verdict::Bug, name << ": expected a bug, got " << report::verdictName(e.verdict));
  bool found = false, confirmed = false;
  for (auto &f : e.findings)
    if (f.kind == kind) { found = true; confirmed |= f.replay == report::ReplayStatus::Confirmed; }
  CHECK(found, name << ": no finding of kind " << kind << "\n" << report::toText({"hlir", "0.1", {e}}));
  CHECK(confirmed, name << ": the " << kind << " finding is not replay-confirmed");
}

int main() {
  std::vector<std::string> files;
  if (DIR *d = opendir(HLIR_C_TEST_DIR)) {
    while (auto *e = readdir(d)) {
      std::string n = e->d_name;
      if (n.size() > 2 && n.substr(n.size() - 2) == ".c") files.push_back(n);
    }
    closedir(d);
  }
  std::sort(files.begin(), files.end());
  CHECK(!files.empty(), "no C test files in " << HLIR_C_TEST_DIR);
  for (auto &f : files) runFile(HLIR_C_TEST_DIR, f);
  std::vector<std::string> cppFiles;
  if (DIR *d = opendir(HLIR_CPP_TEST_DIR)) {
    while (auto *e = readdir(d)) {
      std::string n = e->d_name;
      if (n.size() > 4 && n.substr(n.size() - 4) == ".cpp") cppFiles.push_back(n);
    }
    closedir(d);
  }
  std::sort(cppFiles.begin(), cppFiles.end());
  for (auto &f : cppFiles) runFile(HLIR_CPP_TEST_DIR, f);
  std::vector<std::string> efiles;
  if (DIR *d = opendir(HLIR_C_TEST_DIR "/entry")) {
    while (auto *e = readdir(d)) {
      std::string n = e->d_name;
      if (n.size() > 2 && n.substr(n.size() - 2) == ".c") efiles.push_back(n);
    }
    closedir(d);
  }
  std::sort(efiles.begin(), efiles.end());
  CHECK(!efiles.empty(), "no entry tests in " HLIR_C_TEST_DIR "/entry");
  for (auto &f : efiles) runEntryFile(HLIR_C_TEST_DIR "/entry", f);
  std::cout << "c_tests: " << g_pass << " passed, " << g_fail << " failed (" << files.size() << " C + " << cppFiles.size() << " C++ programs, " << efiles.size() << " entry analyses)\n";
  return g_fail ? 1 : 0;
}

// hlir-run: concretely interpret a `core` function.
//   hlir-run file.core --entry f [--arg N]... [--env name=N]... [--ub=report|wrap|assume] [--trace] [--max-steps N] [--detect-nontermination]
// Exit status: 0 returned, 1 UB / assertion failure, 3 infeasible/unsupported/limits, 2 usage or input error.
#include <fstream>
#include <iostream>
#include <sstream>

#ifdef HLIR_WITH_FRONTEND
#include "hlir/frontend/Frontend.h"
#endif
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "llvm/ADT/SmallString.h"

using namespace hlir;

static bool parseInt(const std::string &s, int64_t &v) {
  try { size_t n; v = std::stoll(s, &n, 0); return n == s.size(); } catch (...) { return false; }
}

int main(int argc, char **argv) {
  std::string path, entry;
  bool libc = false;
  std::vector<int64_t> rawArgs;
  TableEnv env;
  RunConfig cfg;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto val = [&]() -> std::string { return i + 1 < argc ? argv[++i] : ""; };
    if (a == "--entry") entry = val();
    else if (a == "--arg") { int64_t v; std::string s = val(); if (s == "true") v = 1; else if (s == "false") v = 0; else if (!parseInt(s, v)) { std::cerr << "bad --arg " << s << "\n"; return 2; } rawArgs.push_back(v); }
    else if (a == "--env") { std::string kv = val(); auto eq = kv.find('='); int64_t v; if (eq == std::string::npos || !parseInt(kv.substr(eq + 1), v)) { std::cerr << "bad --env " << kv << "\n"; return 2; } env.set(kv.substr(0, eq), v); }
    else if (a == "--ub=report") cfg.ub = UBMode::Report;
    else if (a == "--ub=wrap") cfg.ub = UBMode::Wrap;
    else if (a == "--ub=assume") cfg.ub = UBMode::AssumeAbsent;
    else if (a == "--trace") cfg.trace = true;
    else if (a == "--max-steps") { int64_t v; if (!parseInt(val(), v)) return 2; cfg.maxSteps = static_cast<uint64_t>(v); }
    else if (a == "--detect-nontermination") cfg.detectNonTermination = true;
    else if (a == "--libc") libc = true;
    else if (!a.empty() && a[0] == '-') { std::cerr << "unknown option " << a << "\n"; return 2; }
    else path = a;
  }
  if (path.empty() || entry.empty()) { std::cerr << "usage: hlir-run file.core --entry f [--arg N]... [--env name=N]... [--ub=report|wrap|assume] [--trace] [--detect-nontermination]\n"; return 2; }

  std::ifstream in(path);
  if (!in) { std::cerr << "cannot open " << path << "\n"; return 2; }
  std::stringstream ss;
  ss << in.rdbuf();
  if (path.size() > 2 && path.substr(path.size() - 2) == ".c") {  // C source: lower to core first
#ifdef HLIR_WITH_FRONTEND
    auto low = frontend::lowerC(ss.str(), path, {});
    std::cerr << low.diagnostics;
    if (!low.ok) return 2;
    ss.str(low.core);
    ss.seekp(0, std::ios::end);
#else
    std::cerr << "built without the C frontend (needs libclang-cpp-dev)\n";
    return 2;
#endif
  }
  if (libc) { std::ifstream m(HLIR_MODELS_DIR "/libc.core"); ss << "\n" << m.rdbuf(); std::ifstream x(HLIR_MODELS_DIR "/libc_exact.core"); ss << "\n" << x.rdbuf(); std::ifstream cx(HLIR_MODELS_DIR "/libstdcxx.core"); ss << "\n" << cx.rdbuf(); }
  Diagnostics diags;
  auto mod = parseModule(ss.str(), path, diags);
  if (!mod || !verifyModule(*mod, {}, diags)) { std::cerr << diags.str(); return 2; }

  const Function *f = mod->findFunction(entry);
  if (!f) { std::cerr << "unknown function @" << entry << "\n"; return 2; }
  std::vector<llvm::APInt> args;
  for (size_t i = 0; i < rawArgs.size() && i < f->paramTys.size(); ++i) {
    const Type *t = f->paramTys[i];
    args.emplace_back(t->isBool() ? 1 : t->width(), static_cast<uint64_t>(rawArgs[i]), /*isSigned=*/true);
  }

  RunResult r = Interpreter(*mod).run(entry, args, env, cfg);
  for (auto &e : r.trace) std::cout << "  trace: @" << e.function << " " << e.text << "\n";
  std::cout << "status: " << runStatusName(r.status) << "\n";
  if (r.returnValue) {
    llvm::SmallString<40> s;
    r.returnValue->toStringSigned(s);
    std::cout << "return: " << std::string(s) << "\n";
  }
  if (r.ub) {
    std::cout << "ub: " << ubKindName(r.ub->kind) << " in @" << r.ub->function << " ^" << r.ub->block << " (" << r.ub->op << ")\n";
    if (r.ub->loc.valid()) std::cout << "  at " << r.ub->loc.file << ":" << r.ub->loc.line << ":" << r.ub->loc.col << "\n";
    if (!r.ub->origin.empty()) std::cout << "  origin: " << r.ub->origin << "\n";
    if (!r.ub->detail.empty()) std::cout << "  " << r.ub->detail << "\n";
  }
  if (!r.message.empty()) std::cout << "message: " << r.message << "\n";
  if (r.zeroProgressLoopObserved) {
    std::cout << "non_termination: proven -- loop header ^" << r.zeroProgressLoopHeader << " in @" << r.zeroProgressLoopFunction
               << " repeats with zero relevant writes and no new nondet draw between visits (docs/DESIGN.md Sec.22.326)\n";
  }
  std::cout << "steps: " << r.steps << "\n";
  switch (r.status) {
    case RunStatus::Returned: return 0;
    case RunStatus::UB: case RunStatus::AssertFailed: return 1;
    case RunStatus::BadInput: return 2;
    default: return 3;
  }
}

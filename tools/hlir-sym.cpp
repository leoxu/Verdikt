// hlir-sym: symbolic execution of a `core` function with a solver, then replay of every finding on the concrete
// interpreter. Usage: hlir-sym file.core --entry f [--range i=lo:hi ...] [--solver z3|enum] [--ub=report|wrap|assume]
//                                       [--max-paths N] [--no-replay]
// Exit: 0 no findings (and exploration complete), 1 findings, 2 input error, 3 incomplete / replay mismatch.
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/Symbolic.h"

using namespace hlir;

int main(int argc, char **argv) {
  std::string file, entry, solverName = "z3";
  std::vector<std::string> ranges;
  SymConfig cfg;
  bool replay = true, libc = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&]() -> std::string { return i + 1 < argc ? argv[++i] : ""; };
    if (a == "--entry") entry = next();
    else if (a == "--range") ranges.push_back(next());
    else if (a == "--solver") solverName = next();
    else if (a == "--ub=wrap") cfg.ub = UBMode::Wrap;
    else if (a == "--ub=assume") cfg.ub = UBMode::AssumeAbsent;
    else if (a == "--ub=report") cfg.ub = UBMode::Report;
    else if (a == "--max-paths") cfg.maxPaths = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--max-steps") cfg.maxSteps = std::stoull(next());
    else if (a == "--no-replay") replay = false;
    else if (a == "--libc") libc = true;
    else if (!a.empty() && a[0] != '-') file = a;
    else { std::cerr << "unknown option " << a << "\n"; return 2; }
  }
  if (file.empty() || entry.empty()) { std::cerr << "usage: hlir-sym file.core --entry f [--range i=lo:hi] [--solver z3|enum]\n"; return 2; }
  std::ifstream in(file);
  if (!in) { std::cerr << "cannot read " << file << "\n"; return 2; }
  std::stringstream ss;
  ss << in.rdbuf();
  if (libc) { std::ifstream m(HLIR_MODELS_DIR "/libc.core"); ss << "\n" << m.rdbuf(); }
  Diagnostics d;
  auto mod = parseModule(ss.str(), file, d);
  if (!mod || d.hasErrors() || !verifyModule(*mod, {}, d)) { std::cerr << d.str(); return 2; }
  const Function *f = mod->findFunction(entry);
  if (!f) { std::cerr << "unknown function @" << entry << "\n"; return 2; }

  std::vector<SymArg> args(f->paramTys.size());
  for (auto &r : ranges) {  // i=lo:hi (signed)
    auto eq = r.find('='), colon = r.find(':');
    if (eq == std::string::npos || colon == std::string::npos) { std::cerr << "bad --range " << r << "\n"; return 2; }
    size_t idx = std::stoul(r.substr(0, eq));
    if (idx >= args.size()) { std::cerr << "--range index out of range\n"; return 2; }
    unsigned w = f->paramTys[idx]->isBool() ? 1 : f->paramTys[idx]->width();
    args[idx].isSigned = true;
    args[idx].lo = llvm::APInt(w, std::stoll(r.substr(eq + 1, colon - eq - 1)), true);
    args[idx].hi = llvm::APInt(w, std::stoll(r.substr(colon + 1)), true);
  }

  std::unique_ptr<smt::Solver> solver = solverName == "enum" ? smt::makeEnumSolver(22) : smt::makeZ3ProcessSolver();
  if (!solver) { std::cerr << "cannot start solver '" << solverName << "'\n"; return 2; }
  smt::TermManager tm;
  SymbolicExecutor ex(*mod, tm, *solver);
  SymResult r = ex.run(entry, args, cfg);

  int rc = 0;
  std::cout << "paths: " << r.pathsExplored << ", solver queries: " << r.solverQueries << ", complete: " << (r.complete ? "yes" : "no") << "\n";
  if (!r.complete) { std::cout << "note: " << r.note << "\n"; rc = 3; }
  Interpreter interp(*mod);
  for (auto &fd : r.findings) {
    if (rc == 0) rc = 1;
    std::cout << (fd.ub ? std::string("UB ") + ubKindName(fd.ub->kind) : "assertion failed: " + fd.message);
    if (fd.loc.valid()) std::cout << " at " << fd.loc.file << ":" << fd.loc.line << ":" << fd.loc.col;
    if (fd.ub) std::cout << " in @" << fd.ub->function << " (" << fd.ub->op << ")";
    std::cout << "\n  witness: (";
    for (size_t i = 0; i < fd.args.size(); ++i) std::cout << (i ? ", " : "") << fd.args[i].getSExtValue();
    std::cout << ")";
    if (!fd.nondets.empty()) {
      std::cout << " nondets: [";
      for (size_t i = 0; i < fd.nondets.size(); ++i) std::cout << (i ? ", " : "") << fd.nondets[i].getSExtValue();
      std::cout << "]";
    }
    if (replay) {
      SeqEnv env(fd.nondets);
      RunConfig rcfg;
      rcfg.ub = cfg.ub;
      RunResult rr = interp.run(entry, fd.args, env, rcfg);
      bool ok = fd.ub ? (rr.status == RunStatus::UB && rr.ub && rr.ub->kind == fd.ub->kind) : rr.status == RunStatus::AssertFailed;
      std::cout << "\n  replay: " << (ok ? "reproduced" : std::string("NOT reproduced (") + runStatusName(rr.status) + ")");
      if (!ok) rc = 3;
    }
    std::cout << "\n";
  }
  if (r.findings.empty() && r.complete) std::cout << "no findings\n";
  return rc;
}

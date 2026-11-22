// hlir-entry: taint entry specification -> legal initial states -> harness -> analysis.
//   hlir-entry --spec s.yaml file.core --entry f [--libc] [--seeds] [--emit-harness] [--analyze] [--solver z3|enum]
// Exit: 0 ok (and no findings with --analyze), 1 findings, 2 input/spec error (incl. contradictory spec), 3 incomplete/replay mismatch.
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/entry/HarnessGen.h"
#include "hlir/entry/SeedSolver.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/Symbolic.h"

using namespace hlir;

static std::string slurp(const std::string &p, bool &ok) {
  std::ifstream in(p);
  ok = static_cast<bool>(in);
  std::stringstream ss;
  ss << in.rdbuf();
  return ss.str();
}

static void printModel(const entry::Seed &s) {
  for (auto &kv : s.model) std::cout << "    " << kv.first << " = " << kv.second.getSExtValue() << "\n";
}

int main(int argc, char **argv) {
  std::string spec, file, fn, solverName = "z3";
  bool libc = false, seeds = false, emit = false, analyze = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&]() -> std::string { return i + 1 < argc ? argv[++i] : ""; };
    if (a == "--spec") spec = next();
    else if (a == "--entry") fn = next();
    else if (a == "--solver") solverName = next();
    else if (a == "--libc") libc = true;
    else if (a == "--seeds") seeds = true;
    else if (a == "--emit-harness") emit = true;
    else if (a == "--analyze") analyze = true;
    else if (!a.empty() && a[0] != '-') file = a;
    else { std::cerr << "unknown option " << a << "\n"; return 2; }
  }
  if (spec.empty() || file.empty() || fn.empty()) { std::cerr << "usage: hlir-entry --spec s.yaml file.core --entry f [--libc] [--seeds] [--emit-harness] [--analyze]\n"; return 2; }
  bool ok;
  std::string specText = slurp(spec, ok);
  if (!ok) { std::cerr << "cannot read " << spec << "\n"; return 2; }
  std::string text = slurp(file, ok);
  if (!ok) { std::cerr << "cannot read " << file << "\n"; return 2; }
  if (libc) text += "\n" + slurp(HLIR_MODELS_DIR "/libc.core", ok) + "\n" + slurp(HLIR_MODELS_DIR "/libstdcxx.core", ok);

  Diagnostics d;
  entry::EntryFile ef;
  if (!entry::parseEntrySpec(specText, spec, ef, d)) { std::cerr << d.str(); return 2; }
  const entry::EntrySpec *es = ef.find(fn);
  if (!es) { std::cerr << "no taint entry for @" << fn << " in " << spec << "\n"; return 2; }
  auto mod = parseModule(text, file, d);
  if (!mod || d.hasErrors() || !verifyModule(*mod, {}, d)) { std::cerr << d.str(); return 2; }

  smt::TermManager tm;
  entry::InitPlan plan;
  if (!entry::buildInitPlan(*mod, ef, *es, tm, plan, d)) { std::cerr << d.str(); return 2; }
  if (!d.all().empty()) std::cerr << d.str();

  std::unique_ptr<smt::Solver> solver = solverName == "enum" ? smt::makeEnumSolver(22) : smt::makeZ3ProcessSolver();
  if (!solver) { std::cerr << "cannot start solver '" << solverName << "'\n"; return 2; }
  entry::SeedSolver ss(tm, *solver, plan);

  entry::Seed legal = ss.legality();
  std::cout << "C_init: " << plan.constraints.size() << " constraints, " << smt::satResultName(legal.result) << "\n";
  if (legal.result == smt::SatResult::Unsat) {
    std::cout << "the specification is contradictory; conflicting constraints:\n";
    for (auto &c : legal.core) std::cout << "  " << c << "\n";
    return 2;
  }
  if (legal.result != smt::SatResult::Sat) { std::cout << "solver returned unknown\n"; return 3; }

  if (seeds) {
    entry::Seed m0 = ss.benign();
    std::cout << "M0 (benign seed):\n";
    printModel(m0);
    std::cout << "boundary seeds:\n";
    for (auto &s : ss.boundary()) {
      std::cout << "  " << s.label << ": " << smt::satResultName(s.result);
      if (s.result == smt::SatResult::Unsat) {
        std::cout << "  (conflicts:";
        for (auto &c : s.core) std::cout << " " << c;
        std::cout << ")";
      }
      std::cout << "\n";
    }
  }
  std::string harness = entry::generateHarness(plan);
  if (emit) std::cout << harness;
  if (!analyze) return 0;

  auto full = parseModule(text + "\n" + harness, file + "+harness", d);
  if (!full || d.hasErrors() || !verifyModule(*full, {}, d)) { std::cerr << "generated harness does not verify:\n" << d.str(); return 2; }
  smt::TermManager tm2;
  SymbolicExecutor ex(*full, tm2, *solver);
  SymConfig cfg;
  cfg.maxPaths = 2000;
  std::string hn = entry::harnessName(plan);
  SymResult r = ex.run(hn, {}, cfg);
  int rc = 0;
  std::cout << "paths: " << r.pathsExplored << ", complete: " << (r.complete ? "yes" : "no") << (r.overApprox ? ", over-approximated memory" : "") << "\n";
  if (!r.complete) { std::cout << "note: " << r.note << "\n"; rc = 3; }
  Interpreter interp(*full);
  for (auto &f : r.findings) {
    if (rc == 0) rc = 1;
    std::cout << (f.ub ? std::string("UB ") + ubKindName(f.ub->kind) : "assertion failed: " + f.message);
    if (f.ub) std::cout << " in @" << f.ub->function << " (" << f.ub->op << ")";
    if (f.loc.valid()) std::cout << " at " << f.loc.file << ":" << f.loc.line << ":" << f.loc.col;
    std::cout << "\n  inputs (nondets in order):";
    for (auto &v : f.nondets) std::cout << " " << v.getSExtValue();
    SeqEnv env(f.nondets, f.inputs);
    RunResult rr = interp.run(hn, {}, env);
    bool same = f.ub ? (rr.status == RunStatus::UB && rr.ub && rr.ub->kind == f.ub->kind) : rr.status == RunStatus::AssertFailed;
    std::cout << "\n  replay: " << (same ? "reproduced" : std::string("NOT reproduced (") + runStatusName(rr.status) + ")") << "\n";
    if (!same) rc = 3;
  }
  if (r.findings.empty() && r.complete) std::cout << "no findings\n";
  return rc;
}

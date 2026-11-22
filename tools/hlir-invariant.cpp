// hlir-invariant: is a candidate loop invariant INDUCTIVE?
//
// This is the verifier half of the LLM loop-invariant pipeline (docs/LLM_GUIDED_SE.md §3 second layer, §3.5).
// Checking a candidate is cheap and sound, which is the entire reason that pipeline is worth building: a
// proposer may be wrong ninety-nine times out of a hundred and the wrong ones never reach a verdict.
//
//   hlir-invariant module.core --function F --loop ^header --inv "tlen <= caplen && tptr >= in"
//
// What it does. The loop is OUTLINED into a fresh function that starts from an ARBITRARY state: every local
// of the enclosing function is re-created and filled with a `core.nondet`, so nothing is assumed about how
// the loop was entered. The candidate is then assumed, the body runs once, and the candidate is asserted
// again at the back edge. If the assertion cannot fail, the candidate is inductive.
//
// Four things this deliberately reports instead of folding into a yes/no, because each one is a different
// claim and conflating them is how a verifier starts lying:
//
//   inductive       -- the assert was REACHED and cannot fail
//   not_inductive   -- a counterexample exists (printed)
//   vacuous         -- no path reached the assert at all. An invariant nothing can exercise is not proven,
//                      it is untested; without this check a loop whose body always traps would "pass".
//   incomplete      -- a limit or an Unknown solver answer cut the exploration. NOT a proof.
//
// Signedness is taken from the IR, never from the candidate's text: a name is resolved to its `alloca`, and
// the comparison's signedness comes from how the ORIGINAL function compares that variable. Where the
// evidence is ambiguous, BOTH readings must be inductive -- the over-strict direction, which can only cost
// a rejection, never buy a false acceptance.
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include <memory>
#include <cstring>
#include <stdexcept>
#include <algorithm>

#include "hlir/entry/HarnessGen.h"
#include "hlir/entry/InitPlan.h"
#include "hlir/entry/Spec.h"
#include "hlir/ir/InvariantCheck.h"
#include "hlir/ir/Loops.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Printer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Symbolic.h"
#include "hlir/smt/Solver.h"
#include "hlir/support/Diagnostics.h"

using namespace hlir;

int main(int argc, char **argv) {
  std::string file, fname, loopName, inv, modelsPath;
  unsigned maxPaths = 4000, loopBound = 0;
  uint64_t maxSteps = 400000;
  bool printIr = false, ptrHavocSame = false;
  unsigned objSize = 64;
  std::string specPath;
  auto usage = [&] {
    std::cerr << "usage: hlir-invariant module.core --function F --loop HEADER --inv \"EXPR\"\n"
                 "       [--models libc.core] [--max-paths N] [--max-steps N] [--print-ir] [--list]\n"
                 "       [--ptr-havoc distinct|same]  how arbitrary pointer locals are built; `same` assumes\n"
                 "                                    they all point into ONE object (an under-approximation,\n"
                 "                                    printed with the verdict)\n";
    return 2;
  };
  bool list = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&]() -> std::string { return i + 1 < argc ? argv[++i] : ""; };
    if (a == "--function") fname = next();
    else if (a == "--loop") loopName = next();
    else if (a == "--inv") inv = next();
    else if (a == "--models") modelsPath = next();
    else if (a == "--max-paths") maxPaths = std::stoul(next());
    else if (a == "--max-steps") maxSteps = std::stoull(next());
    else if (a == "--print-ir") printIr = true;
    else if (a == "--ptr-havoc") ptrHavocSame = next() == "same";
    else if (a == "--obj-size") objSize = std::stoul(next());
    else if (a == "--spec") specPath = next();
    else if (a == "--list") list = true;
    else if (a[0] == '-') return usage();
    else file = a;
  }
  if (file.empty() || fname.empty()) return usage();

  std::ifstream in(file);
  if (!in) { std::cerr << "cannot read " << file << "\n"; return 2; }
  std::stringstream ss;
  ss << in.rdbuf();
  std::string text = ss.str();
  if (!modelsPath.empty()) {
    std::ifstream mi(modelsPath);
    std::stringstream ms;
    ms << mi.rdbuf();
    text += "\n" + ms.str();
  }
  Diagnostics d;
  auto mod = parseModule(text, file, d);
  if (!mod) { std::cerr << d.str(); return 2; }
  Function *f = mod->findFunction(fname);
  if (!f || f->isDeclaration()) { std::cerr << "no function body @" << fname << "\n"; return 2; }

  auto loops = loopsOf(*f);
  if (list || loopName.empty()) {
    std::cout << "@" << fname << ": " << loops.size() << " loop(s)\n";
    for (auto &lp : loops)
      std::cout << "  ^" << lp.header->name << "  " << lp.file << ":" << lp.line << "  blocks=" << lp.body.size()
                << " checks=" << lp.checks << " calls=" << lp.calls << (lp.nested ? " nested" : "") << "\n";
    return loopName.empty() && !list ? 2 : 0;
  }
  std::string want = loopName[0] == '^' ? loopName.substr(1) : loopName;
  const Loop *loop = nullptr;
  for (auto &lp : loops)
    if (lp.header->name == want) loop = &lp;
  if (!loop) { std::cerr << "@" << fname << " has no loop with header ^" << want << " (try --list)\n"; return 2; }
  if (inv.empty()) return usage();

  struct Outcome { std::string verdict, detail; unsigned paths = 0; bool reached = false, fallback = false; };
  auto runOnce = [&](bool signedMode) -> Outcome {
    Outcome o;
    // Re-parse for each reading: instrumentInvariant mutates the module, and the two readings are two
    // different programs.
    Diagnostics pd;
    auto m = parseModule(text, file, pd);
    if (!m) { o.verdict = "build_error"; o.detail = pd.str(); return o; }
    InvariantInstrumentation ins = instrumentInvariant(*m, fname, want, inv, signedMode, "", "network");
    if (!ins.error.empty()) {
      o.verdict = ins.error.rfind("candidate:", 0) == 0 ? "unparseable" : "build_error";
      o.detail = ins.error;
      return o;
    }
    o.fallback = ins.usedSignednessFallback;
    if (printIr) {
      Function *pf = m->findFunction(fname);
      (void)pf; std::cerr << moduleToString(*m);
    }
    Diagnostics vd;
    if (!verifyModule(*m, {}, vd)) { o.verdict = "build_error"; o.detail = vd.str(); return o; }

    Function *f2 = m->findFunction(fname);
    bool anyPtrParam = false;
    for (Type *t : f2->paramTys) anyPtrParam |= t->isPtr();
    std::string runFn = fname;
    std::unique_ptr<Module> full;
    smt::TermManager tm;
    if (anyPtrParam || (!f2->paramTys.empty() && !specPath.empty())) {
      if (specPath.empty()) {
        o.verdict = "needs_spec";
        o.detail = "@" + fname + " takes pointer parameters; pass --spec (hlir-scan --entry " + fname + " --out DIR)";
        return o;
      }
      std::ifstream si(specPath);
      std::stringstream sst;
      sst << si.rdbuf();
      Diagnostics sd;
      entry::EntryFile ef;
      if (!entry::parseEntrySpec(sst.str(), specPath, ef, sd)) { o.verdict = "spec_error"; o.detail = sd.str(); return o; }
      const entry::EntrySpec *es = ef.find(fname);
      if (!es) { o.verdict = "spec_error"; o.detail = "no entry for @" + fname + " in " + specPath; return o; }
      entry::InitPlan plan;
      if (!entry::buildInitPlan(*m, ef, *es, tm, plan, sd)) { o.verdict = "spec_error"; o.detail = sd.str(); return o; }
      std::string harness = entry::generateHarness(plan);
      std::string mtext;
      { llvm::raw_string_ostream rs(mtext); printModule(*m, rs); }
      Diagnostics hd;
      full = parseModule(mtext + "\n" + harness, "instrumented+harness", hd);
      if (!full || hd.hasErrors() || !verifyModule(*full, {}, hd)) {
        o.verdict = "build_error";
        o.detail = "generated harness does not verify: " + hd.str();
        return o;
      }
      runFn = entry::harnessName(plan);
    }
    const Module &rm = full ? *full : *m;
    const Block *chk = nullptr;
    if (Function *ff = const_cast<Module &>(rm).findFunction(fname))
      for (auto &bb : ff->blocks)
        if (bb->name == "iv_check") chk = bb.get();
    auto solver = smt::makeZ3ProcessSolver();
    if (!solver) { o.verdict = "no_solver"; return o; }
    smt::TermManager tm2;
    SymbolicExecutor ex(rm, tm2, *solver);
    SymConfig cfg;
    cfg.ub = UBMode::AssumeAbsent;
    cfg.maxPaths = maxPaths;
    cfg.maxSteps = maxSteps;
    SymResult r = ex.run(runFn, {}, cfg);
    o.paths = r.pathsExplored;
    o.reached = chk && r.blocksVisited.count(chk) != 0;
    for (auto &fi : r.findings)
      if (fi.status == RunStatus::AssertFailed) {
        o.verdict = "not_inductive";
        o.detail = "counterexample on path " + std::to_string(fi.path);
        return o;
      }
    if (!r.complete) { o.verdict = "incomplete"; o.detail = r.reason + (r.note.empty() ? "" : ": " + r.note); return o; }
    if (!o.reached) {
      o.verdict = "vacuous";
      o.detail = "no path reached the back edge (" + std::to_string(r.pathsExplored) + " path(s), " +
                 std::to_string(r.blocksVisited.size()) + " block(s) visited)";
      return o;
    }
    o.verdict = "inductive";
    return o;
  };

  std::cout << "@" << fname << " ^" << want << "  (" << loop->file << ":" << loop->line
            << ", blocks=" << loop->body.size() << ", checks=" << loop->checks << ")\n";
  std::cout << "candidate: " << inv << "\n";
  if (ptrHavocSame)
    std::cout << "ASSUMPTION: --ptr-havoc same -- every pointer local is taken to point into ONE object.\n"
                 "            This NARROWS the states considered, so an `inductive` verdict here is weaker\n"
                 "            than one without it and must be carried with the invariant.\n";
  Outcome u = runOnce(false);
  std::cout << "  unsigned reading: " << u.verdict << (u.detail.empty() ? "" : "  (" + u.detail + ")")
            << "  paths=" << u.paths << "\n";
  if (!u.fallback || u.verdict == "unparseable" || u.verdict == "build_error") {
    std::cout << "verdict: " << u.verdict << "\n";
    return u.verdict == "inductive" ? 0 : 1;
  }
  Outcome s2 = runOnce(true);
  std::cout << "  signed reading:   " << s2.verdict << (s2.detail.empty() ? "" : "  (" + s2.detail + ")")
            << "  paths=" << s2.paths << "\n";
  bool both = u.verdict == "inductive" && s2.verdict == "inductive";
  std::cout << "verdict: " << (both ? "inductive" : (u.verdict == s2.verdict ? u.verdict : "ambiguous_signedness"))
            << "\n";
  return both ? 0 : 1;
}

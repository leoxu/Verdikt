#include <chrono>
#include "hlir/semantics/Symbolic.h"

#include <set>

#include "Machine.h"
#include "SymbolicDomain.h"

namespace hlir {

SymResult SymbolicExecutor::run(const std::string &function, const std::vector<SymArg> &argSpecs, const SymConfig &cfg) {
  SymResult res;
  auto bad = [&](std::string why, const char *code = "input_error") {
    res.complete = false;
    res.reason = code;
    res.note = std::move(why);
    return res;
  };
  const Function *f = mod_.findFunction(function);
  if (!f) return bad("unknown function @" + function, "unknown_function");
  if (f->isDeclaration()) return bad("@" + function + " is only declared, it has no body");
  if (argSpecs.size() > f->paramTys.size()) return bad("more argument specs than parameters");
  std::vector<unsigned> widths;
  for (const Type *t : f->paramTys) {
    if (t->isPtr()) return bad("pointer parameters require the memory model", "pointer_param");
    widths.push_back(t->isBool() ? 1 : t->width());
  }

  // Argument variables and their input constraints (shared by every path).
  std::vector<smt::TermRef> argVars;
  std::vector<smt::TermRef> init;
  for (size_t i = 0; i < widths.size(); ++i) {
    const std::string &pn = f->entry()->args[i]->name;
    smt::TermRef v = tm_.bvVar("arg." + (pn.empty() ? "p" + std::to_string(i) : pn), widths[i]);
    argVars.push_back(v);
    if (i < argSpecs.size()) {
      const SymArg &s = argSpecs[i];
      if (s.lo) init.push_back(tm_.mkCmp(s.isSigned ? smt::Kind::Sle : smt::Kind::Ule, tm_.bvConst(s.lo->zextOrTrunc(widths[i])), v));
      if (s.hi) init.push_back(tm_.mkCmp(s.isSigned ? smt::Kind::Sle : smt::Kind::Ule, v, tm_.bvConst(s.hi->zextOrTrunc(widths[i]))));
    }
  }
  res.argVars = argVars;

  RunConfig rc;
  rc.ub = cfg.ub;
  if (cfg.wallSeconds > 0) rc.deadline = std::chrono::steady_clock::now() + std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(cfg.wallSeconds));
  rc.maxSteps = cfg.maxSteps;
  rc.maxCallDepth = cfg.maxCallDepth;
  rc.loopBound = cfg.loopBound;
  rc.memBound = cfg.memBound;
  rc.memExpandMax = cfg.memExpandMax;
  rc.tableSelect = cfg.tableSelect;
  rc.storeSelect = cfg.storeSelect;
  rc.models = cfg.models;
  rc.prologueFns = cfg.prologueFns;
  rc.stopFns = cfg.stopFns;
  // The initialiser runs once for the whole pass, not once per path: without this the symbolic pass pays for it on
  // every path AND forks inside it. Measured on sound/core round 49e: `symbolic_time_budget` went from 5 entries to
  // 33 once the initialiser was being run at all. Pinning path 0's initialisation is the narrowing §22.368 §5
  // already states ("one complete, self-consistent execution"), and `project_init` names it in the report.
  Memory<SymbolicDomain>::Cache prologueCache;
  if (cfg.prologueFns && !cfg.prologueFns->empty()) rc.prologueCache = &prologueCache;
  // The harness's declared setup region, cached for the whole pass (DESIGN.md §22.442), exactly as the
  // initialiser above is. This pass replays every path from the entry, so an uncached region is paid for once
  // per PATH -- which is why §22.441 measured the markers as a cost here and a win in the concolic engine.
  // SymbolicDomain refuses to fork inside the region (see setSetupRegion), so no queued schedule can ever
  // index a decision that a restoring path does not make.
  SetupState<SymbolicDomain> setupCache;
  rc.setupCache = &setupCache;
  rc.coverage = true;  // merged into SymResult::blocksVisited below; cheap (a hash-set insertion per block transition)

  struct SessionGuard { smt::Solver &s; explicit SessionGuard(smt::Solver &x) : s(x) { s.beginSession(); } ~SessionGuard() { s.endSession(); } } sessionGuard(solver_);
  QueryCache cache;
  std::vector<SymbolicDomain::Schedule> work{{}};
  std::set<std::pair<const Op *, int>> sites;
  uint64_t queries = 0;

  const auto t0 = std::chrono::steady_clock::now();
  while (!work.empty()) {
    if (res.pathsExplored >= cfg.maxPaths) { res.complete = false; res.note = "path limit reached"; res.reason = "path_limit"; break; }
    if (cfg.wallSeconds > 0 && std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() >= cfg.wallSeconds) {
      res.complete = false; res.note = "time budget exhausted"; res.reason = "time_budget"; break;
    }
    SymbolicDomain::Schedule sched = std::move(work.back());
    work.pop_back();

    SymbolicDomain *domp = nullptr;
    unsigned pathIdx = res.pathsExplored;
    SymbolicDomain::Hooks hooks;
    hooks.onFork = [&](const SymbolicDomain::Schedule &alt) { work.push_back(alt); };
    hooks.onFinding = [&](const Finding &fd, const smt::Assignment &asg) {
      if (!sites.insert({fd.site, fd.ub ? static_cast<int>(fd.ub->kind) : -1}).second) return;
      SymFinding sf;
      sf.status = fd.status;
      sf.ub = fd.ub;
      sf.message = fd.message;
      sf.loc = fd.loc;
      sf.frontierOnly = fd.frontierOnly;
      sf.cmpOnlyPtr = fd.cmpOnlyPtr;
      sf.inPrologue = fd.inPrologue;
      sf.path = pathIdx;
      for (auto *v : argVars) {
        auto it = asg.find(v->name);
        sf.args.push_back(it == asg.end() ? llvm::APInt(v->sort.width, 0) : it->second);
      }
      for (auto *v : domp->nondetVars()) {
        auto it = asg.find(v->name);
        sf.nondets.push_back(it == asg.end() ? llvm::APInt(v->sort.width, 0) : it->second);
        sf.nondetNames.push_back(v->name);
      }
      for (auto &kv : asg)
        if (kv.first.rfind("in.", 0) == 0) sf.inputs.emplace(kv.first, kv.second);
      res.findings.push_back(std::move(sf));
    };

    SymbolicDomain dom(tm_, solver_, cache, std::move(hooks), std::move(sched));
    dom.setDeadline(rc.deadline);
    domp = &dom;
    for (auto *v : argVars) dom.addInputVar(v);
    for (auto *c : init) dom.constrain(c);

    TableEnv env;
    Machine<SymbolicDomain> m(dom, mod_, env, rc);
    std::vector<smt::TermRef> argTerms(argVars.begin(), argVars.end());
    RunResult rr = m.run(*f, argTerms);
    ++res.pathsExplored;
    res.setupSecRestore += rr.secSetupRestore;
    for (const Block *b : rr.blocksVisited) res.blocksVisited.insert(b);  // counts even a cut/infeasible path's real prefix
    if (m.memory().overApprox()) res.overApprox = true;
    queries += dom.queries();
    if (dom.boundInsufficient()) { res.complete = false; res.note = dom.boundWhat(); res.reason = "bound_insufficient"; }
    if (dom.incomplete()) { res.complete = false; res.note = "solver returned unknown"; res.reason = "solver_unknown"; }
    if (dom.dead()) continue;

    switch (rr.status) {
      case RunStatus::Unsupported: case RunStatus::StepLimit: case RunStatus::DepthLimit:
        res.complete = false;
        res.note = rr.message;
        res.reason = rr.status == RunStatus::StepLimit ? (rr.message.find("time budget") != std::string::npos ? "time_budget" : "step_limit") : rr.status == RunStatus::DepthLimit ? "depth_limit" : "unsupported";
        break;
      case RunStatus::LoopBound: ++res.loopCut; continue;  // cut at the bound: a real execution we did not follow further
      case RunStatus::Infeasible: continue;  // not a real execution
      default: break;
    }
    if (cfg.collectPaths) {
      SymPath p;
      p.status = rr.status;
      p.pc = dom.pc();
      if (m.returned()) p.returnValue = *m.returned();
      res.paths.push_back(std::move(p));
    }
  }
  res.solverQueries = queries;
  res.setupSeen = setupCache.state != SetupCache::State::Empty || setupCache.capturedOps > 0;
  res.setupReused = setupCache.state == SetupCache::State::Valid;
  res.setupRefusal = setupCache.refusal;
  res.setupOps = setupCache.capturedOps;
  res.setupSkips = setupCache.skips;
  res.setupObjects = setupCache.objects;
  return res;
}

}  // namespace hlir

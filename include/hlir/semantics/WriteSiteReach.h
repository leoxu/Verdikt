// §3.3b step 2 (docs/LLM_ASSISTED_TRIAGE_DESIGN.md Sec.3.3b, docs/DESIGN.md Sec.22.329/22.330): turns a
// `WriteSite` candidate (Sec.22.329's `findWriteSites`) into a REAL `--reach-target`-biased taint-concolic run
// instead of just a list of locations to read by hand.
//
// Mechanism: reuse the existing forward engine exactly the way hlir-scan's own `--reach-target` already works
// (TaintConfig::reachTarget, lib/semantics/Taint.cpp) -- no new backward solver. Two steps:
//   1. Mutate the module in place: insert `core.assert (stored_value != targetValue)` right after the
//      candidate's `core.store`, so the assertion is violated exactly when the search manages to make that
//      write deposit `targetValue` -- the existing AssertFailed/replay-confirm machinery (same as any
//      hand-written `core.assert`) does the rest.
//   2. Run `TaintExecutor::run` with `cfg.reachTarget` set to the candidate's own function, so the frontier
//      prioritises flips in functions closer to it (ReachTarget.h) instead of coverage order -- the same bias
//      `hlir-scan --reach-target <fn>` applies, because it is the identical code path.
//
// Deliberately narrow: only scalar (int/bool), not pointer-typed, stored values are supported (a pointer-typed
// write site is a dangling/aliasing question, not a "reaches this value" question -- out of scope here); only
// one target value per call (a range needs one `reachWriteSite` call per endpoint, same as any binary-search use
// of `taint:value,range:`). Never claims a finding the engine did not itself confirm by replay (honest-triage
// discipline carried over from every other piece of this project): `confirmed` requires both
// `RunStatus::AssertFailed` and `SymFinding::confirmed == true`.
#pragma once
#include <algorithm>
#include <string>

#include "hlir/ir/IR.h"
#include "hlir/semantics/Symbolic.h"
#include "hlir/semantics/Taint.h"
#include "hlir/semantics/WriteSites.h"
#include "hlir/smt/Solver.h"
#include "hlir/smt/Term.h"

namespace hlir {

// Inserts `core.assert (stored_value != targetValue)` immediately after `site.storeOp`, in `site.storeOp`'s own
// block, mutating `m` in place. Returns the new assert Op, or nullptr if the site can't be targeted this way
// (not found in its block any more, or the stored value isn't a scalar int/bool -- see file comment).
inline Op *injectWriteSiteAssert(Module &m, const WriteSite &site, int64_t targetValue,
                                  const std::string &msg = "reach-write-site: candidate value reached") {
  if (!site.storeOp || site.storeOp->operands.empty() || !site.storeOp->parent) return nullptr;
  Block *blk = site.storeOp->parent;
  size_t pos = blk->ops.size();
  for (size_t i = 0; i < blk->ops.size(); ++i)
    if (blk->ops[i].get() == site.storeOp) { pos = i; break; }
  if (pos == blk->ops.size()) return nullptr;  // storeOp not actually in its own recorded parent block any more

  Value *storedVal = site.storeOp->operands[0];
  if (!storedVal->ty || storedVal->ty->isPtr() || storedVal->ty->isVoid()) return nullptr;  // scalar-only, see file comment

  Builder b(m);
  b.setInsertionPoint(blk);
  b.setLoc(site.loc);
  size_t before = blk->ops.size();
  Value *targetConst = b.constInt(storedVal->ty, targetValue);
  Value *neq = b.icmp("ne", storedVal, targetConst);
  Op *assertOp = b.create(Opc::Assert, {neq});
  assertOp->setAttr("msg", Attr::string(msg));
  // Builder::create always appends at the END of the block; splice the ops it just appended (the const + icmp +
  // assert, `before`..end) into position right after the store instead, preserving the block's original tail
  // (the store's own successors) after them.
  std::rotate(blk->ops.begin() + static_cast<long>(pos) + 1, blk->ops.begin() + static_cast<long>(before), blk->ops.end());
  return assertOp;
}

struct WriteSiteReachResult {
  bool injected = false;            // false: injectWriteSiteAssert bailed (see its own doc comment)
  bool confirmed = false;           // true: AssertFailed, replay-confirmed -- targetValue IS reachable at this site
  TaintResult taint;                // full underlying run (findings, stats, note/reason on why not confirmed)
};

// Full step-2 pipeline for one candidate: inject, bias the search at `site.fn`, run from `entry`, and report
// whether the engine itself confirmed targetValue is reachable there. `cfg.reachTarget` is overwritten with
// `site.fn->name` regardless of what the caller passed in (that is the whole point of this function).
//
// `seed0` is the initial concrete assignment the run starts from -- the SAME parameter `TaintExecutor::run`
// itself takes, defaulting to empty (the all-zero-ish default) exactly like every other caller in this
// codebase that doesn't pass one. On a real entry with non-trivial preconditions (anything an `entry::SeedSolver`
// benign seed -- "M0" -- would be needed for), leaving this at `{}` can mean the run never gets past the
// harness's own precondition checks before reaching anything the search is trying to bias toward; pass the
// benign seed's `model` (converted the same way `testEntry()`/hlir-scan's own entry runs already do) when one
// exists. Confirmed to matter in practice, not just in theory: validating this against brotli's real IR
// (docs/DESIGN.md Sec.22.331) silently produced zero tainted branches with the default empty seed, purely
// because this parameter didn't exist yet for the caller to supply the entry's own benign seed through.
inline WriteSiteReachResult reachWriteSite(Module &m, smt::TermManager &tm, smt::Solver &solver, const WriteSite &site,
                                            const std::string &entry, int64_t targetValue, TaintConfig cfg = {},
                                            const std::map<std::string, llvm::APInt> &seed0 = {}) {
  WriteSiteReachResult res;
  Op *assertOp = injectWriteSiteAssert(m, site, targetValue);
  if (!assertOp || !site.fn) { res.taint.note = "write-site could not be targeted (non-scalar store, or site not found in its block)"; return res; }
  res.injected = true;
  const std::string injectedMsg = assertOp->attr("msg")->s;  // SymFinding carries no Op*, so match by the unique msg we just set
  cfg.reachTarget = site.fn->name;
  TaintExecutor ex(m, tm, solver);
  res.taint = ex.run(entry, seed0, cfg);
  for (auto &f : res.taint.findings)
    if (f.status == RunStatus::AssertFailed && f.message == injectedMsg && f.confirmed && *f.confirmed) { res.confirmed = true; break; }
  return res;
}

}  // namespace hlir

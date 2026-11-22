// hlir-wp-probe: backward-WP P0 measurement gate (docs/BACKWARD_WP_P0_PLAN.md).
//
// P0 measures whether DESIGN §2.1's relevance filter holds; it SOLVES NOTHING (no smt, no loop summaries, no alias
// resolution). It answers one question with numbers: for each UB candidate, how many *variables to model* does its
// violation condition depend on (|S|), and what do those variables bottom out in (root class -- seam ②)?
//
// Pipeline (DESIGN §4, §6):
//   step 0  parse a --dump-linked `core` module (proves the dump round-trips through ir::parseModule)
//   step 1  enumerate every isCheck op  = the enumerable denominator (DESIGN §1.2), independent of forward coverage
//   step 2  seed the backward slice from each check's operands, with the pointer base/offset split for CheckOob
//   step 3  walk SSA def chains back to roots, stopping at Load/Call/Nondet/Param/Global/loop-carried; classify
//   step 4  aggregate |S| and root-class / stop-reason histograms
//
// KEY FIDELITY CHOICE (seam ②, and why P0 needs the slice not just |S|): a root is counted toward |S| only if it is
// a *variable to model* -- Param / LoopCarried / Load / CallRet / Nondet. Constants, a global's (fixed) address and
// an alloca's (known) size are NOT variables, so they do not inflate |S|. A check whose S is empty is a free safety
// candidate for P1. The per-class histogram is printed so every bucketing choice here is auditable and re-bucketable.
//
// What is DEFERRED to a labelled step-3b (not done here): the path-condition guards on the way to the check (DESIGN
// §4.3 CondBr conjunction). This tool computes the violation condition's *data* dependency, which is the dominant
// term in DESIGN's motivating example (S = {cnt}); branch guards can only ADD roots, so |S| here is a lower bound.
//
//   hlir-wp-probe [--list] [--solve] file.core
//
// P0 (default) depends on hlir_ir only. P1 (--solve) additionally links hlir_smt: it builds each numeric check's
// violation condition V as an SMT term over the backward cone, with every root (param/load/call/nondet/loop-carried)
// a FRESH UNCONSTRAINED bit-vector. That is the DESIGN §3.4 over-approximation and it makes UNSAT sound: an
// unconstrained root ranges over at least the real reachable values, so V UNSAT => the violation is impossible on
// every path => the site is SAFE (bucket 1, a genuine safety proof). SAT => a bucket-2/3 candidate (expected often,
// since path guards were dropped). This is P1's UNSAT pruning; it solves nothing about loops or aliasing.
#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "hlir/ir/IR.h"
#include "hlir/ir/Loops.h"
#include "hlir/ir/Ops.h"
#include "hlir/ir/Parser.h"
#include "hlir/smt/Solver.h"
#include "hlir/smt/Term.h"
// The engine's ONE definition of the integer-UB violation conditions (DESIGN §4.1: no second definition). TermOps is
// its SMT value domain (Val == smt::TermRef); ubViolations builds V over it exactly as the interpreter builds it over
// APInts. Private lib/semantics headers, included header-only (no hlir_semantics link): the tool is the one place
// allowed to reach across modules.
#include "semantics/TermOps.h"
#include "semantics/UBConditions.h"

using namespace hlir;

namespace {

// Root classes a backward slice can bottom out in.
enum class Root { Param, LoopCarried, Load, CallRet, Nondet, Const, GlobalPtr, ObjectBase, Unknown };
const char *rootName(Root r) {
  switch (r) {
    case Root::Param: return "param";
    case Root::LoopCarried: return "loop_carried";
    case Root::Load: return "load";
    case Root::CallRet: return "call_ret";
    case Root::Nondet: return "nondet";
    case Root::Const: return "const";
    case Root::GlobalPtr: return "global_ptr";
    case Root::ObjectBase: return "object_base";
    case Root::Unknown: return "unknown";
  }
  return "?";
}
// Does this root class count as a "variable to model" (toward |S|)?  Const / GlobalPtr(address) / ObjectBase(identity)
// are known or structural, not variables.
bool countsTowardS(Root r) {
  return r == Root::Param || r == Root::LoopCarried || r == Root::Load || r == Root::CallRet || r == Root::Nondet;
}

// Per-check result.
struct Slice {
  std::set<const Value *> sVars;          // distinct roots that count toward |S|
  std::map<Root, unsigned> classHist;     // every root reached, by class (incl. non-S for transparency)
  bool hitLoopCarried = false;
};

// A function's control-flow + local-slot helper.
struct CFG {
  // (block, argIndex) -> incoming values
  std::map<std::pair<const Block *, unsigned>, std::vector<const Value *>> incoming;
  std::set<const Block *> loopHeaders;
  std::set<const Block *> entry;
  const Block *entryBlock = nullptr;
  std::vector<Loop> loops;
  std::map<const Op *, const Block *> opBlock;   // op -> its block (for loop membership)
  std::map<const Op *, unsigned> opPos;          // op -> its index within its block (for intra-block ordering)
  std::map<const Block *, std::vector<const Block *>> preds;  // CFG predecessors (for reach/φ VC-gen)

  // edge (p -> b) is a loop back-edge: b is a loop header and p is one of that loop's latches.
  bool isBackEdge(const Block *p, const Block *b) const {
    for (const Loop &lp : loops)
      if (lp.header == b && lp.latches.count(p)) return true;
    return false;
  }

  // Can `from` reach `to` following successors, never passing through `avoid`? (used to tell whether an in-loop store
  // reaches a load within the same iteration -- i.e. before looping back through the header.)
  bool reachesAvoiding(const Block *from, const Block *to, const Block *avoid) const {
    std::set<const Block *> seen;
    std::vector<const Block *> wl{from};
    seen.insert(from);
    while (!wl.empty()) {
      const Block *x = wl.back(); wl.pop_back();
      if (const Op *t = x->terminator())
        for (const Succ &s : t->succs) {
          if (!s.dest || s.dest == avoid) continue;
          if (s.dest == to) return true;
          if (seen.insert(s.dest).second) wl.push_back(s.dest);
        }
    }
    return false;
  }

  // P2 soundness gate: does some in-loop store to `slot` reach `loadOp` within the same iteration (so the load does
  // NOT read the loop-header value)? If yes, the slot symbol must not be shared across the guard and this load.
  bool inLoopStoreReachesLoad(const Value *slot, const Op *loadOp, const Block *loadBlk) const {
    auto sit = stores.find(slot);
    if (sit == stores.end()) return false;
    for (const Loop &lp : loops) {
      if (!lp.body.count(loadBlk)) continue;
      for (const Op *st : sit->second) {
        auto bit = opBlock.find(st);
        if (bit == opBlock.end() || !lp.body.count(bit->second)) continue;  // pre-loop init store: fine
        const Block *stBlk = bit->second;
        if (stBlk == loadBlk) {
          auto sp = opPos.find(st), lpn = opPos.find(loadOp);
          if (sp != opPos.end() && lpn != opPos.end() && sp->second < lpn->second) return true;  // store before load
        } else if (reachesAvoiding(stBlk, loadBlk, lp.header)) {
          return true;  // store in another in-loop block reaches the load without re-entering the header
        }
      }
    }
    return false;
  }

  // --- step 3a: local alloca promotion (the IR is deliberately non-SSA; Frontend.cpp:4). An alloca is "promotable"
  // when its pointer is used ONLY as the direct pointer operand of a load/store (op0 of Load, op1 of Store) -- never
  // passed to a call, stored as a value, offset, compared or returned. Those are exactly the per-local scalar slots
  // the frontend emits. For such a slot a `load` is really the reaching `store`'s value, so the slice forwards through
  // it; without this every scalar (params, loop counters, accumulators) masquerades as a memory `load` root.
  std::set<const Value *> promotable;                        // alloca result values that are promotable
  std::map<const Value *, std::vector<const Op *>> stores;   // slot -> its store ops
  std::map<const Block *, std::set<const Block *>> dom;       // dominators: dom[b] = blocks that dominate b
  bool dominates(const Block *a, const Block *b) const {
    auto it = dom.find(b);
    return it != dom.end() && it->second.count(a) != 0;
  }

  // ---- P2 accumulator summary helpers (pure IR structure) ----
  // Is `st` a self-increment store `slot = load(slot) + c` with c a constant? If so set c.
  bool selfAddConst(const Op *st, const Value *slot, long &c) const {
    if (!st || st->operands.empty()) return false;
    const Value *sv = st->operands[0];                       // the stored value
    if (sv->kind != Value::OpResult || !sv->defOp || sv->defOp->opc != Opc::Add) return false;
    const Op &add = *sv->defOp;
    if (add.operands.size() < 2) return false;
    auto isLoadOfSlot = [&](const Value *v) {
      return v->kind == Value::OpResult && v->defOp && v->defOp->opc == Opc::Load &&
             !v->defOp->operands.empty() && v->defOp->operands[0] == slot;
    };
    auto constOf = [&](const Value *v, long &out) {
      if (v->kind == Value::OpResult && v->defOp && v->defOp->opc == Opc::Const) { out = v->defOp->constVal.getSExtValue(); return true; }
      return false;
    };
    if (isLoadOfSlot(add.operands[0]) && constOf(add.operands[1], c)) return true;
    if (isLoadOfSlot(add.operands[1]) && constOf(add.operands[0], c)) return true;
    return false;
  }
  // Like selfAddConst but also accepts `slot = load(slot) - c` (lowered as core.sub), returning the SIGNED step (−c).
  // So a down-counter `dn--` reports c = −1.
  bool selfStepConst(const Op *st, const Value *slot, long &c) const {
    if (selfAddConst(st, slot, c)) return true;
    if (!st || st->operands.empty()) return false;
    const Value *sv = st->operands[0];
    if (sv->kind != Value::OpResult || !sv->defOp || sv->defOp->opc != Opc::Sub || sv->defOp->operands.size() < 2) return false;
    const Op &sub = *sv->defOp;
    auto isLoadOfSlot = [&](const Value *v) {
      return v->kind == Value::OpResult && v->defOp && v->defOp->opc == Opc::Load &&
             !v->defOp->operands.empty() && v->defOp->operands[0] == slot;
    };
    const Value *k = sub.operands[1];
    if (isLoadOfSlot(sub.operands[0]) && k->kind == Value::OpResult && k->defOp && k->defOp->opc == Opc::Const) {
      c = -(long)k->defOp->constVal.getSExtValue(); return true;     // slot = slot - const  ->  step = -const
    }
    return false;
  }
  // The pre-loop store VALUE of `slot` (the single store outside lp.body), or null. Unlike constInit it keeps a symbolic
  // value (e.g. a bounded call result), used as the down-counter's initial value dn0 in the coupled-counter bound.
  const Value *preLoopInitValue(const Value *slot, const Loop &lp) const {
    auto sit = stores.find(slot);
    if (sit == stores.end()) return nullptr;
    const Value *val = nullptr; int n = 0;
    for (const Op *st : sit->second) {
      auto bit = opBlock.find(st);
      if (bit == opBlock.end() || lp.body.count(bit->second)) continue;   // want a store OUTSIDE the loop
      if (st->operands.empty()) continue;
      ++n; val = st->operands[0];
    }
    return n == 1 ? val : nullptr;        // exactly one pre-loop init, so dn0 is well-defined
  }
  // The header guards the body on `dn != 0` (so the body runs at most dn0 times): the header's condBr tests load(dn)
  // against 0 and the body is on the nonzero side. Handles ne/eq and >0 / 0< forms.
  bool guardsNonzero(const Loop &lp, const Value *dn) const {
    const Op *t = lp.header->terminator();
    if (!t || t->opc != Opc::CondBr || t->operands.empty() || t->succs.size() < 2) return false;
    bool bodyT = lp.body.count(t->succs[0].dest), bodyF = lp.body.count(t->succs[1].dest);
    if (bodyT == bodyF) return false;
    const Value *cond = t->operands[0];
    if (!cond || !cond->defOp) return false;
    auto isDn = [&](const Value *x) {
      return x && x->defOp && x->defOp->opc == Opc::Load && !x->defOp->operands.empty() && x->defOp->operands[0] == dn;
    };
    // `while (dn)` lowers to `i2b(load(dn))` (true iff dn != 0), not an icmp. Body on the true side => runs while dn!=0.
    if (cond->defOp->opc == Opc::I2B && !cond->defOp->operands.empty() && isDn(cond->defOp->operands[0]))
      return bodyT;
    if (cond->defOp->opc != Opc::ICmp || cond->defOp->operands.size() < 2) return false;
    const Op &cmp = *cond->defOp;
    auto isZero = [&](const Value *x) {
      return x && x->defOp && x->defOp->opc == Opc::Const && x->defOp->constVal.getSExtValue() == 0;
    };
    bool dnA = isDn(cmp.operands[0]) && isZero(cmp.operands[1]);   // cmp(dn, 0)
    bool dnB = isDn(cmp.operands[1]) && isZero(cmp.operands[0]);   // cmp(0, dn)
    if (!dnA && !dnB) return false;
    const std::string &p = cmp.pred;
    bool trueMeansNonzero;
    if (p == "ne") trueMeansNonzero = true;
    else if (p == "eq") trueMeansNonzero = false;
    else if ((p == "ugt" || p == "sgt") && dnA) trueMeansNonzero = true;   // dn > 0
    else if ((p == "ult" || p == "slt") && dnB) trueMeansNonzero = true;   // 0 < dn
    else return false;
    return bodyT ? trueMeansNonzero : !trueMeansNonzero;
  }
  // The loop's unit DOWN-counter used as its bound: a promotable slot whose only in-loop store is `dn = dn - 1`
  // (dominating the single latch) with a single pre-loop init, and whose header guards the body on `dn != 0`. The body
  // then runs at most dn0 times. Returns the slot and sets dn0val (its initial-value Value), or null.
  const Value *downCounter(const Loop &lp, const Value *&dn0val) const {
    if (lp.latches.size() != 1) return nullptr;
    const Block *latch = *lp.latches.begin();
    for (const Value *slot : promotable) {
      auto sit = stores.find(slot);
      if (sit == stores.end()) continue;
      int inLoop = 0; const Op *dec = nullptr;
      for (const Op *st : sit->second) {
        auto bit = opBlock.find(st);
        if (bit == opBlock.end() || !lp.body.count(bit->second)) continue;
        ++inLoop; dec = st;
      }
      long c;
      if (inLoop != 1 || !dec || !selfStepConst(dec, slot, c) || c != -1) continue;   // exactly one in-loop store, `-1`
      auto ib = opBlock.find(dec);
      if (ib == opBlock.end() || !dominates(ib->second, latch)) continue;             // every iteration
      if (!guardsNonzero(lp, slot)) continue;
      const Value *v = preLoopInitValue(slot, lp);
      if (!v) continue;
      dn0val = v;
      return slot;
    }
    return nullptr;
  }
  // The pre-loop constant init of `slot` (a store outside lp.body whose value is a constant), or false.
  bool constInit(const Value *slot, const Loop &lp, long &init0) const {
    auto sit = stores.find(slot);
    if (sit == stores.end()) return false;
    for (const Op *st : sit->second) {
      auto bit = opBlock.find(st);
      if (bit == opBlock.end() || lp.body.count(bit->second)) continue;  // want a store OUTSIDE the loop
      if (st->operands.empty()) continue;
      const Value *v = st->operands[0];
      if (v->kind == Value::OpResult && v->defOp && v->defOp->opc == Opc::Const) { init0 = v->defOp->constVal.getSExtValue(); return true; }
    }
    return false;
  }
  // The loop's induction variable: a promotable slot with constant init, a single in-loop store `iv = iv + 1` whose
  // block dominates the single latch (so it runs every iteration). Returns the slot (and its init), or null.
  const Value *inductionVar(const Loop &lp, long &iv0) const {
    if (lp.latches.size() != 1) return nullptr;             // need one back-edge so "once per iteration" is well-defined
    const Block *latch = *lp.latches.begin();
    for (const Value *slot : promotable) {
      auto sit = stores.find(slot);
      if (sit == stores.end()) continue;
      int inLoop = 0; const Op *incr = nullptr; long c = 0;
      bool ok = true;
      for (const Op *st : sit->second) {
        auto bit = opBlock.find(st);
        if (bit == opBlock.end() || !lp.body.count(bit->second)) continue;
        ++inLoop; incr = st;
        long cc; if (!selfAddConst(st, slot, cc) || cc != 1) { ok = false; break; }
        c = cc;
      }
      if (!ok || inLoop != 1 || c != 1) continue;           // exactly one in-loop store, `+1`
      auto ib = opBlock.find(incr);
      if (ib == opBlock.end() || !dominates(ib->second, latch)) continue;  // runs every iteration
      if (!constInit(slot, lp, iv0)) continue;
      return slot;
    }
    return nullptr;
  }
  // Is `slot` a non-negative constant-step accumulator in lp (every in-loop store is `slot = slot + nonneg_const`)?
  // Sets C = the max step and init0 = the pre-loop constant init.
  bool accumulator(const Value *slot, const Loop &lp, long &C, long &init0) const {
    auto sit = stores.find(slot);
    if (sit == stores.end()) return false;
    int inLoop = 0; C = 0;
    for (const Op *st : sit->second) {
      auto bit = opBlock.find(st);
      if (bit == opBlock.end() || !lp.body.count(bit->second)) continue;
      ++inLoop; long c;
      if (!selfAddConst(st, slot, c) || c < 0) return false;  // must be slot += nonneg const
      if (c > C) C = c;
    }
    return inLoop >= 1 && constInit(slot, lp, init0);
  }

  // Is `v` loop-invariant in `lp` -- the same value on every iteration? Constants always; a block-arg defined OUTSIDE
  // the body (a param / pre-loop value, never a loop-carried body/header arg); an op computed outside the body whose
  // operands are all invariant. A Load is treated as NOT invariant (its memory may change across iterations). Used to
  // admit a SYMBOLIC but fixed accumulator step `cnt += s`. Bounded recursion guards against malformed IR.
  bool loopInvariant(const Value *v, const Loop &lp, int depth = 0) const {
    if (!v || depth > 64) return false;
    if (v->kind == Value::BlockArg) return v->defBlock && !lp.body.count(v->defBlock);
    if (v->kind == Value::OpResult && v->defOp) {
      if (v->defOp->opc == Opc::Const) return true;
      if (v->defOp->opc == Opc::Load) {
        // The non-SSA frontend keeps params/locals in allocas, so an invariant like a parameter appears as a load. A
        // load of a promotable slot with NO store inside the body reads the same (pre-loop) value every iteration.
        const Value *ptr = v->defOp->operands.empty() ? nullptr : v->defOp->operands[0];
        if (!ptr || !promotable.count(ptr)) return false;
        auto sit = stores.find(ptr);
        if (sit != stores.end())
          for (const Op *st : sit->second) {
            auto bit = opBlock.find(st);
            if (bit != opBlock.end() && lp.body.count(bit->second)) return false;  // stored inside the loop: may change
          }
        return true;
      }
      auto bit = opBlock.find(v->defOp);
      if (bit != opBlock.end() && lp.body.count(bit->second)) return false;  // computed inside the loop
      for (const Value *op : v->defOp->operands)
        if (!loopInvariant(op, lp, depth + 1)) return false;
      return true;
    }
    return false;
  }
  // Like accumulator() but for a LOOP-INVARIANT (possibly symbolic) step: exactly ONE in-loop store `slot = slot + s`
  // that dominates the single latch (runs every iteration, unconditionally), with `s` loop-invariant and non-const
  // (const is accumulator()'s job). Then the in-loop header value obeys the EXACT relation cnt == init0 + s·(iv − iv0).
  const Value *symStepAccumulator(const Value *slot, const Loop &lp, long &init0) const {
    if (lp.latches.size() != 1 || !constInit(slot, lp, init0)) return nullptr;
    auto sit = stores.find(slot);
    if (sit == stores.end()) return nullptr;
    const Op *only = nullptr; int inLoop = 0;
    for (const Op *st : sit->second) {
      auto bit = opBlock.find(st);
      if (bit == opBlock.end() || !lp.body.count(bit->second)) continue;
      ++inLoop; only = st;
    }
    if (inLoop != 1 || !only) return nullptr;
    auto ib = opBlock.find(only);
    if (ib == opBlock.end() || !dominates(ib->second, *lp.latches.begin())) return nullptr;  // every iteration
    if (only->operands.empty()) return nullptr;
    const Value *sv = only->operands[0];
    if (sv->kind != Value::OpResult || !sv->defOp || sv->defOp->opc != Opc::Add || sv->defOp->operands.size() < 2) return nullptr;
    const Op &add = *sv->defOp;
    auto isLoadOfSlot = [&](const Value *x) {
      return x->kind == Value::OpResult && x->defOp && x->defOp->opc == Opc::Load &&
             !x->defOp->operands.empty() && x->defOp->operands[0] == slot;
    };
    const Value *step = nullptr;
    if (isLoadOfSlot(add.operands[0])) step = add.operands[1];
    else if (isLoadOfSlot(add.operands[1])) step = add.operands[0];
    if (!step || (step->kind == Value::OpResult && step->defOp && step->defOp->opc == Opc::Const)) return nullptr;  // const: accumulator()'s job
    return loopInvariant(step, lp) ? step : nullptr;
  }
  // A STRUCTURAL constant upper bound on a step value `s`, independent of its (per-iteration) value: a zero-extension
  // from a narrow type (s < 2^k), an AND with a constant mask (s <= mask), or a URem by a constant (s <= m-1). These
  // need no range analysis -- the bound is read off the op. Sets M. (The probe has no interval domain, so this is the
  // soundly-decidable slice of "the step is bounded".)
  bool stepBound(const Value *s, long &M) const {
    if (!s || s->kind != Value::OpResult || !s->defOp) return false;
    const Op &d = *s->defOp;
    if (d.opc == Opc::ZExt && !d.operands.empty() && d.operands[0]->ty && d.operands[0]->ty->isInt()) {
      unsigned k = d.operands[0]->ty->width();
      if (k > 0 && k < 63) { M = (1L << k) - 1; return true; }
    }
    if (d.opc == Opc::And && d.operands.size() >= 2)
      for (int k = 0; k < 2; ++k) {
        const Value *c = d.operands[k];
        if (c->kind == Value::OpResult && c->defOp && c->defOp->opc == Opc::Const) { M = c->defOp->constVal.getZExtValue(); return true; }
      }
    if (d.opc == Opc::URem && d.operands.size() >= 2) {
      const Value *m = d.operands[1];
      if (m->kind == Value::OpResult && m->defOp && m->defOp->opc == Opc::Const) {
        long mm = m->defOp->constVal.getSExtValue();
        if (mm > 0) { M = mm - 1; return true; }
      }
    }
    return false;
  }
  // Interval-delta accumulator: every in-loop store is `slot = slot + s` where each step s has a structural constant
  // upper bound (stepBound). Each iteration then adds at most M, so slot <= init0 + M·(iv − iv0) -- sound even for
  // conditional or multiple stores (the <= form; an iteration with no/guard-failed store only adds less). Sets M = max.
  bool intervalAccumulator(const Value *slot, const Loop &lp, long &M, long &init0) const {
    auto sit = stores.find(slot);
    if (sit == stores.end() || !constInit(slot, lp, init0)) return false;
    int inLoop = 0; M = 0;
    for (const Op *st : sit->second) {
      auto bit = opBlock.find(st);
      if (bit == opBlock.end() || !lp.body.count(bit->second)) continue;
      ++inLoop;
      if (st->operands.empty()) return false;
      const Value *sv = st->operands[0];
      if (sv->kind != Value::OpResult || !sv->defOp || sv->defOp->opc != Opc::Add || sv->defOp->operands.size() < 2) return false;
      const Op &add = *sv->defOp;
      auto isLoadOfSlot = [&](const Value *x) {
        return x->kind == Value::OpResult && x->defOp && x->defOp->opc == Opc::Load &&
               !x->defOp->operands.empty() && x->defOp->operands[0] == slot;
      };
      const Value *step = isLoadOfSlot(add.operands[0]) ? add.operands[1]
                        : isLoadOfSlot(add.operands[1]) ? add.operands[0] : nullptr;
      long m;
      if (!step || !stepBound(step, m)) return false;   // a single unbounded step defeats the whole bound
      if (m > M) M = m;
    }
    return inLoop >= 1;
  }

  // step 3b: for each block, the branch guards that are NECESSARY to reach it -- (condition value, must-be-true).
  // A guard c=true holds for block B when some dominator D of B ends in `condBr c, T, F` and only the T side can
  // reach B (F cannot). Conjoining these with V is sound (a guard is necessary for reaching the check, so it holds
  // on every real violation) and strictly tightens V -> more UNSAT safety proofs (e.g. a bounds-checked access).
  std::map<const Block *, std::vector<std::pair<const Value *, bool>>> pathGuards;

  bool inSameLoop(const Block *a, const Block *b) const {    // a and b share some loop body
    for (const Loop &lp : loops)
      if (lp.body.count(a) && lp.body.count(b)) return true;
    return false;
  }

  static std::string swapPred(const std::string &p) {       // a P b  <=>  b swapPred(P) a
    if (p == "ult") return "ugt"; if (p == "ugt") return "ult"; if (p == "ule") return "uge"; if (p == "uge") return "ule";
    if (p == "slt") return "sgt"; if (p == "sgt") return "slt"; if (p == "sle") return "sge"; if (p == "sge") return "sle";
    return p;                                                // eq, ne are symmetric
  }
  static std::string negPred(const std::string &p) {        // !(a P b)
    if (p == "ult") return "uge"; if (p == "uge") return "ult"; if (p == "ule") return "ugt"; if (p == "ugt") return "ule";
    if (p == "slt") return "sge"; if (p == "sge") return "slt"; if (p == "sle") return "sgt"; if (p == "sgt") return "sle";
    if (p == "eq") return "ne"; if (p == "ne") return "eq";
    return p;
  }
  // Resolve a value through promotable single-store loads to its stored value, so two loads of the same local compare
  // equal (used to match a return value against a dominating guard on the same local).
  const Value *promoted(const Value *v) const {
    std::set<const Value *> seen;
    while (v && v->kind == Value::OpResult && v->defOp && v->defOp->opc == Opc::Load && !v->defOp->operands.empty()) {
      const Value *slot = v->defOp->operands[0];
      if (!promotable.count(slot)) break;
      auto it = stores.find(slot);
      if (it == stores.end() || it->second.size() != 1 || it->second[0]->operands.empty()) break;
      const Value *nv = it->second[0]->operands[0];
      if (!nv || !seen.insert(nv).second) break;
      v = nv;
    }
    return v;
  }
  // An upper bound on `rv` implied by the guards that dominate `block` (step-3b): `rv <= M`. Matches a dominating guard
  // `rv </<= const` (rv compared after promotion, on either side, with the guard's required polarity). This is where a
  // range check INSIDE a callee -- `if (n <= 16) return n;` -- gives the return value its bound.
  bool guardUpperBound(const Value *rv, const Block *block, long &M) const {
    auto it = pathGuards.find(block);
    if (it == pathGuards.end()) return false;
    const Value *pr = promoted(rv);
    bool found = false; M = 0;
    for (const auto &g : it->second) {
      const Value *cond = g.first;
      if (!cond || !cond->defOp || cond->defOp->opc != Opc::ICmp || cond->defOp->operands.size() < 2) continue;
      const Op &cmp = *cond->defOp;
      auto cst = [&](const Value *x, long &c) {
        if (x && x->defOp && x->defOp->opc == Opc::Const) { c = (long)x->defOp->constVal.getSExtValue(); return true; }
        return false;
      };
      std::string p = cmp.pred;
      long c;
      if (promoted(cmp.operands[0]) == pr && cst(cmp.operands[1], c)) { /* rv p c */ }
      else if (promoted(cmp.operands[1]) == pr && cst(cmp.operands[0], c)) { p = swapPred(p); /* rv p c */ }
      else continue;
      if (!g.second) p = negPred(p);                         // guard requires the condition false
      long ub;
      if (p == "ult" || p == "slt") ub = c - 1;              // rv < c
      else if (p == "ule" || p == "sle") ub = c;             // rv <= c
      else continue;
      if (!found || ub < M) { M = ub; found = true; }
    }
    return found;
  }
};

CFG buildCFG(const Function &f) {
  CFG cfg;
  if (f.entry()) cfg.entry.insert(f.entry());
  cfg.loops = loopsOf(f);
  for (const Loop &lp : cfg.loops) cfg.loopHeaders.insert(lp.header);
  for (const auto &bup : f.blocks) {
    const Block *pred = bup.get();
    for (unsigned i = 0; i < pred->ops.size(); ++i) { cfg.opBlock[pred->ops[i].get()] = pred; cfg.opPos[pred->ops[i].get()] = i; }
    const Op *term = pred->terminator();
    if (!term) continue;
    for (const Succ &s : term->succs) {
      const Block *dst = s.dest;
      if (!dst) continue;
      for (unsigned i = 0; i < s.args.size(); ++i)
        cfg.incoming[{dst, i}].push_back(s.args[i]);
    }
  }

  // Promotability: classify every alloca by how its pointer is used across the whole function.
  std::set<const Value *> allocas, disqualified;
  std::map<const Value *, std::vector<const Op *>> storesOf;
  for (const auto &bup : f.blocks)
    for (const auto &oup : bup->ops)
      if (oup->opc == Opc::Alloca && oup->result) allocas.insert(oup->result.get());
  for (const auto &bup : f.blocks) {
    for (const auto &oup : bup->ops) {
      const Op &op = *oup;
      for (unsigned i = 0; i < op.operands.size(); ++i) {
        const Value *v = op.operands[i];
        if (!v || !allocas.count(v)) continue;
        // Real data uses that break promotion: a call arg, a ptr_add base, a stored value, a return, a compare...
        // NOT disqualifying: load(op0) / store(op1) themselves, and pointer-reading ANNOTATIONS (every Check op, plus
        // lifetime / obj_size / obj_alive) -- those read the slot for verification but never let it escape.
        bool ok = (op.opc == Opc::Load && i == 0) || (op.opc == Opc::Store && i == 1) || isCheck(op.opc) ||
                  op.opc == Opc::LifetimeEnd || op.opc == Opc::ObjSize || op.opc == Opc::ObjAlive;
        if (!ok) disqualified.insert(v);
      }
      if (op.opc == Opc::Store && op.operands.size() >= 2 && allocas.count(op.operands[1]))
        storesOf[op.operands[1]].push_back(&op);
    }
  }
  for (const Value *a : allocas)
    if (!disqualified.count(a)) { cfg.promotable.insert(a); cfg.stores[a] = storesOf[a]; }

  // ---- step 3b: path guards (dominators + CFG reachability) ----
  std::vector<const Block *> order;
  for (const auto &bup : f.blocks) order.push_back(bup.get());
  for (const Block *p : order)
    if (const Op *t = p->terminator())
      for (const Succ &s : t->succs)
        if (s.dest) cfg.preds[s.dest].push_back(p);
  auto &preds = cfg.preds;
  const Block *entry = f.entry();
  cfg.entryBlock = entry;
  if (entry && !order.empty()) {
    std::set<const Block *> universe(order.begin(), order.end());
    std::map<const Block *, std::set<const Block *>> &dom = cfg.dom;
    for (const Block *b : order) dom[b] = (b == entry) ? std::set<const Block *>{entry} : universe;
    for (bool changed = true; changed;) {
      changed = false;
      for (const Block *b : order) {
        if (b == entry) continue;
        std::set<const Block *> nd;
        bool first = true;
        for (const Block *p : preds[b]) {
          if (first) { nd = dom[p]; first = false; }
          else { std::set<const Block *> t; std::set_intersection(nd.begin(), nd.end(), dom[p].begin(), dom[p].end(), std::inserter(t, t.begin())); nd.swap(t); }
        }
        nd.insert(b);
        if (nd != dom[b]) { dom[b] = std::move(nd); changed = true; }
      }
    }
    auto canReach = [&](const Block *target) {  // blocks that can reach `target` (backward walk)
      std::set<const Block *> R{target};
      std::vector<const Block *> wl{target};
      while (!wl.empty()) {
        const Block *x = wl.back(); wl.pop_back();
        for (const Block *p : preds[x]) if (R.insert(p).second) wl.push_back(p);
      }
      return R;
    };
    for (const Block *b : order) {
      std::set<const Block *> reach = canReach(b);
      for (const Block *d : dom[b]) {
        if (d == b) continue;
        const Op *t = d->terminator();
        if (!t || t->opc != Opc::CondBr || t->operands.empty() || t->succs.size() < 2) continue;
        bool tR = t->succs[0].dest && reach.count(t->succs[0].dest);
        bool fR = t->succs[1].dest && reach.count(t->succs[1].dest);
        if (tR && !fR) cfg.pathGuards[b].push_back({t->operands[0], true});
        else if (fR && !tR) cfg.pathGuards[b].push_back({t->operands[0], false});
      }
    }
  }
  return cfg;
}

// Backward data-dependency slice from `seeds`, accumulating roots into `out`.
void slice(const std::vector<const Value *> &seeds, const CFG &cfg, Slice &out) {
  std::set<const Value *> seen;
  std::function<void(const Value *)> go = [&](const Value *v) {
    if (!v || !seen.insert(v).second) return;

    if (v->kind == Value::BlockArg) {
      if (cfg.entry.count(v->defBlock)) {                 // entry arg = function parameter
        out.classHist[Root::Param]++;
        out.sVars.insert(v);
      } else if (cfg.loopHeaders.count(v->defBlock)) {    // loop-header arg = loop-carried (DESIGN §4.4: stop)
        out.classHist[Root::LoopCarried]++;
        out.sVars.insert(v);
        out.hitLoopCarried = true;
      } else {                                            // non-loop merge: follow to every predecessor's incoming value
        auto it = cfg.incoming.find({v->defBlock, v->index});
        if (it == cfg.incoming.end() || it->second.empty()) { out.classHist[Root::Unknown]++; out.sVars.insert(v); return; }
        for (const Value *in : it->second) go(in);
      }
      return;
    }
    if (v->kind != Value::OpResult || !v->defOp) { out.classHist[Root::Unknown]++; out.sVars.insert(v); return; }

    const Op &d = *v->defOp;
    switch (d.opc) {
      case Opc::Const: out.classHist[Root::Const]++; return;                    // known, not a variable
      case Opc::GlobalAddr: case Opc::FuncAddr: out.classHist[Root::GlobalPtr]++; return;  // fixed address
      case Opc::Alloca: out.classHist[Root::ObjectBase]++; return;             // identity; size is a const attr
      case Opc::HeapAlloc:                                                     // pointer identity is structural; its
        out.classHist[Root::ObjectBase]++; return;                            // SIZE is seeded explicitly for CheckOob
      case Opc::Load: {
        // step 3a: forward through a promotable local slot instead of stopping at a spurious memory root.
        const Value *ptr = d.operands.empty() ? nullptr : d.operands[0];
        if (ptr && cfg.promotable.count(ptr)) {
          auto sit = cfg.stores.find(ptr);
          const std::vector<const Op *> &sts = (sit != cfg.stores.end()) ? sit->second : std::vector<const Op *>{};
          const Block *loadBlk = v->defOp ? cfg.opBlock.count(v->defOp) ? cfg.opBlock.at(v->defOp) : nullptr : nullptr;
          // loop-carried if a store to this slot lives in a loop that also contains the load (DESIGN §4.4 stop).
          bool carried = false;
          for (const Op *st : sts) {
            auto bit = cfg.opBlock.find(st);
            if (bit != cfg.opBlock.end() && loadBlk && cfg.inSameLoop(bit->second, loadBlk)) { carried = true; break; }
          }
          if (carried) { out.classHist[Root::LoopCarried]++; out.sVars.insert(v); out.hitLoopCarried = true; return; }
          if (sts.empty()) { out.classHist[Root::Nondet]++; out.sVars.insert(v); return; }  // read before any write
          for (const Op *st : sts) if (st->operands.size() >= 1) go(st->operands[0]);        // forward each reaching store's value
          return;
        }
        out.classHist[Root::Load]++; out.sVars.insert(v); return;                            // genuine memory read
      }
      case Opc::Call: out.classHist[Root::CallRet]++; out.sVars.insert(v); return;
      case Opc::Nondet: out.classHist[Root::Nondet]++; out.sVars.insert(v); return;
      default:
        // Pure computation (arith / cmp / select / casts / extract / concat / ptr_add / ptr_diff / ...): recurse into
        // operands. This is the DESIGN §4.3 "x = e -> wp = Q[e/x]" substitution at the data level.
        for (const Value *op : d.operands) go(op);
        return;
    }
  };
  for (const Value *s : seeds) go(s);
}

// Follow a pointer value back through ptr_add/ptr_diff to its base object, collecting the OFFSET operands (which carry
// the real index dependency) and, for a HeapAlloc base, its symbolic size operand. Mirrors V ≡ off + w > size(base).
void seedPointer(const Value *ptr, std::vector<const Value *> &seeds) {
  std::set<const Value *> seen;
  std::function<void(const Value *)> go = [&](const Value *v) {
    if (!v || !seen.insert(v).second) return;
    if (v->kind == Value::OpResult && v->defOp) {
      const Op &d = *v->defOp;
      if (d.opc == Opc::PtrAdd || d.opc == Opc::PtrDiff) {
        if (!d.operands.empty()) go(d.operands[0]);            // base: keep walking to the root object
        for (unsigned i = 1; i < d.operands.size(); ++i) seeds.push_back(d.operands[i]);  // offset(s): real dependency
        return;
      }
      if (d.opc == Opc::IntToPtr && !d.operands.empty()) {     // pointer synthesised from an integer expression:
        seeds.push_back(d.operands[0]);                        // the whole integer is the dependency
        return;
      }
      if (d.opc == Opc::HeapAlloc && !d.operands.empty())
        seeds.push_back(d.operands[0]);                        // size(base) for a heap object is a dependency
      // alloca/global base: size/address known -> contributes nothing to S
    }
  };
  go(ptr);
}

// A copy-class library call left un-lowered (not turned into the MemCpy intrinsic): the index of its explicit length
// argument, or -1. The length drives the bounds violation (DESIGN §2.1's canonical memcpy case), so it is the seed.
// Name-based for P0 (ir-only); the real tool would ask the ModelProvider (DESIGN §4.1). dst is arg 0 in all of these.
int memCallLenArg(const std::string &name) {
  if (name == "memcpy" || name == "memmove" || name == "memset" || name == "memccpy") return 2;
  if (name == "strncpy" || name == "strncat" || name == "strlcpy" || name == "strlcat" || name == "bcopy") return 2;
  return -1;
}

// A UB candidate: an isCheck op, a Mem* intrinsic, or a recognised copy-class call. Carries how to seed its slice.
struct Candidate {
  const Op *op;
  std::string kind;      // label for the histogram
  bool numeric;          // sliced for |S| (clean numeric V) vs merely counted (memory-state/provenance)
};

bool recognise(const Op &op, Candidate &c) {
  if (isCheck(op.opc)) {
    c = {&op, opInfo(op.opc).name,
         op.opc == Opc::CheckOob || op.opc == Opc::CheckPtrArith || op.opc == Opc::CheckDiv ||
             op.opc == Opc::CheckShift || op.opc == Opc::CheckSAddOvf || op.opc == Opc::CheckSSubOvf ||
             op.opc == Opc::CheckSMulOvf || op.opc == Opc::CheckSNegOvf || op.opc == Opc::CheckFieldOob};
    return true;  // non-numeric kinds (Null/Uaf/Free/ConstWrite/Uninit/Align/PtrCmp = memory-state/provenance) counted, not sliced
  }
  if (op.opc == Opc::MemCpy || op.opc == Opc::MemMove || op.opc == Opc::MemSet) {
    c = {&op, opInfo(op.opc).name, true};
    return true;
  }
  if (op.opc == Opc::Call && memCallLenArg(op.sym) >= 0) {
    c = {&op, "call:" + op.sym, true};
    return true;
  }
  return false;
}

// Slice seeds for a candidate (DESIGN §4.2 violation conditions).
std::vector<const Value *> seedsFor(const Candidate &c) {
  std::vector<const Value *> seeds;
  const Op &op = *c.op;
  const auto &o = op.operands;
  switch (op.opc) {
    case Opc::CheckOob:                                  // off + w > size(base) : offset (+ heap size), via the base walk
      if (!o.empty()) seedPointer(o[0], seeds);
      break;
    case Opc::CheckPtrArith:                             // overflow of base+off : the offset is the dependency
      if (o.size() >= 2) seeds.push_back(o[1]);
      break;
    case Opc::CheckDiv: case Opc::CheckShift:            // divisor / shift amount drive it (both operands seeded)
    case Opc::CheckSAddOvf: case Opc::CheckSSubOvf: case Opc::CheckSMulOvf:
      for (const Value *v : o) seeds.push_back(v);
      break;
    case Opc::CheckSNegOvf:
    case Opc::CheckFieldOob:                              // index into a fixed-size array field (bound is a const attr)
      if (!o.empty()) seeds.push_back(o[0]);
      break;
    case Opc::MemCpy: case Opc::MemMove: case Opc::MemSet:   // n > size(dst) [∨ n > size(src)] : length (+ base heap sizes)
      if (o.size() >= 3) seeds.push_back(o[2]);
      if (o.size() >= 1) seedPointer(o[0], seeds);
      if ((op.opc == Opc::MemCpy || op.opc == Opc::MemMove) && o.size() >= 2) seedPointer(o[1], seeds);
      break;
    case Opc::Call: {                                       // recognised copy-class library call
      int li = memCallLenArg(op.sym);
      if (li >= 0 && (unsigned)li < o.size()) seeds.push_back(o[li]);
      if (!o.empty()) seedPointer(o[0], seeds);            // dst is arg 0
      break;
    }
    default: break;
  }
  return seeds;
}

// A structural constant upper bound on a value, read off its defining op with no range analysis: a constant, a zext
// from a narrow type (< 2^k), an AND with a constant mask (<= mask), or a URem by a constant (<= m-1). Sets M.
static bool structuralUpperBound(const Value *v, long &M) {
  if (!v || v->kind != Value::OpResult || !v->defOp) return false;
  const Op &d = *v->defOp;
  if (d.opc == Opc::Const) { M = (long)d.constVal.getZExtValue(); return true; }
  if (d.opc == Opc::ZExt && !d.operands.empty() && d.operands[0]->ty && d.operands[0]->ty->isInt()) {
    unsigned k = d.operands[0]->ty->width();
    if (k > 0 && k < 63) { M = (1L << k) - 1; return true; }
  }
  if (d.opc == Opc::And && d.operands.size() >= 2)
    for (int k = 0; k < 2; ++k) {
      const Value *c = d.operands[k];
      if (c->kind == Value::OpResult && c->defOp && c->defOp->opc == Opc::Const) { M = (long)c->defOp->constVal.getZExtValue(); return true; }
    }
  if (d.opc == Opc::URem && d.operands.size() >= 2) {
    const Value *m = d.operands[1];
    if (m->kind == Value::OpResult && m->defOp && m->defOp->opc == Opc::Const) {
      long mm = (long)m->defOp->constVal.getSExtValue();
      if (mm > 0) { M = mm - 1; return true; }
    }
  }
  return false;
}
// One return site's contribution to the return summary: an exact constant (`r == val`, so a sentinel like -1 is kept
// precisely) or a structural upper bound (`r <= val`). The caller constrains the call result to the DISJUNCTION over
// sites -- sound, since r is always exactly one of the returns.
struct RetDisjunct { bool isConst; long val; };
// Interprocedural return summary (validate-then-use): per-return-site constraints. A return of a constant becomes an
// exact `r == c` disjunct (a sentinel is kept, not widened), a structurally-bounded return (`x & 7`, a byte) a `r <= M`
// disjunct. One unbounded return defeats the whole summary. The caller's own branch on the result (`if (r >= 0) ...`,
// captured by step-3b) then excludes the sentinel disjunct and leaves the bounded one -- so `c = classify(x); if (c>=0)
// buf[c]` proves SAFE. Strictly generalises the old single `r <= max`: a sentinel return no longer makes M vacuous.
static bool returnDisjuncts(const Function &f, const CFG &cfg, std::vector<RetDisjunct> &out) {
  if (f.isDeclaration()) return false;
  out.clear();
  bool any = false;
  for (auto &b : f.blocks) {
    const Op *t = b->terminator();
    if (!t || t->opc != Opc::Return) continue;
    if (t->operands.empty()) return false;
    const Value *rv = t->operands[0];
    if (rv->kind == Value::OpResult && rv->defOp && rv->defOp->opc == Opc::Const) {
      out.push_back({true, (long)rv->defOp->constVal.getSExtValue()});
    } else {
      long ms, mg;
      bool hs = structuralUpperBound(rv, ms);                   // bound from the return EXPRESSION (x & 7, a byte)
      bool hg = cfg.guardUpperBound(rv, b.get(), mg);           // bound from a GUARD dominating this return (if n<=16)
      if (hs && hg) out.push_back({false, std::min(ms, mg)});
      else if (hs) out.push_back({false, ms});
      else if (hg) out.push_back({false, mg});
      else return false;                                        // an unbounded return defeats the whole summary
    }
    any = true;
  }
  return any;
}

// ---------------------------------------------------------------- P1 (--solve): build V as an SMT term, check UNSAT.
// Every root is a FRESH UNCONSTRAINED bit-vector (DESIGN §3.4): it ranges over at least the real reachable values, so
// V UNSAT => the violation is impossible on every path => SAFE (bucket 1). SAT => a bucket-2/3 candidate. The pure
// computation cone is evaluated faithfully (shared Values share a term via memo, so i-i etc. is exact).
struct Solver1 {
  const CFG &cfg;
  smt::TermManager &tm;
  unsigned pw;
  std::map<const Value *, smt::TermRef> memo;
  std::map<const Value *, unsigned> freshId;
  unsigned counter = 0;

  unsigned fnIdx = 0;                                     // distinguishes same-numbered roots across functions
  const std::map<std::string, std::vector<RetDisjunct>> *retDisjuncts = nullptr;  // callee name -> per-return-site constraints
  const std::map<std::string, std::map<unsigned, long>> *paramBounds = nullptr;  // fn name -> (param idx -> upper bound)
  std::string fnName;                                    // the function being analysed, to look up its param bounds
  smt::TermRef fresh(const Value *v, unsigned w) {
    unsigned id;
    auto it = freshId.find(v);
    if (it == freshId.end()) { id = counter++; freshId[v] = id; } else id = it->second;
    return tm.bvVar("f" + std::to_string(fnIdx) + "r" + std::to_string(id) + "_" + std::to_string(w), w);
  }
  unsigned widthOf(const Value *v) {
    if (v->ty && v->ty->isPtr()) return pw;
    if (v->ty && v->ty->isBool()) return 1;
    if (v->ty && v->ty->isInt()) return v->ty->width() ? v->ty->width() : pw;
    return pw;
  }
  smt::TermRef zextTo(smt::TermRef t, unsigned from, unsigned to) {
    return from == to ? t : (from < to ? tm.mkZExt(t, to) : tm.mkExtract(t, to - 1, 0));
  }

  // ---- φ-aware VC-gen (DESIGN §4.3): a non-loop block-arg (an SSA phi) is a fresh var constrained by, per incoming
  // edge, `edgeReached(P→B) ⟹ r == value_from_P`. That recovers the control relationship a compound guard carries
  // (`i>=0 && i<10` short-circuits into a block-arg whose value is `t4 ? t8 : false`). Sound: each implication is a
  // true fact, and r keeps a free fallback. `side` holds these constraints; the solver asserts them with V.
  std::vector<smt::TermRef> side;
  std::map<const Block *, smt::TermRef> reachMemo;
  std::set<const Block *> reachStack;
  std::set<const Value *> accEmitted;   // accumulator slots whose invariant was already asserted
  std::set<const Value *> exitEmitted;  // slots whose post-loop exit-value bound was already asserted
  std::set<const Value *> loEmitted;    // monotone slots whose in-loop lower bound was already asserted
  std::set<const Value *> dcEmitted;    // up-counters whose coupled down-counter bound was already asserted

  // P2 accumulator summary: when `slot` is a non-negative constant-step accumulator in a loop that also has a unit-
  // step induction variable `iv`, assert the sound bound  slot ≤ init0 + C·(iv − iv0)  over their shared symbols.
  // With the loop guard `iv < N` (step 3b), this bounds the accumulator by trip-count × step. Emitted once per slot.
  void emitAccInvariant(const Value *slot, unsigned w, const Block *loadBlk) {
    if (!accEmitted.insert(slot).second) return;
    for (const Loop &lp : cfg.loops) {
      if (!lp.body.count(loadBlk)) continue;
      long iv0;
      const Value *iv = cfg.inductionVar(lp, iv0);
      if (!iv || iv == slot) continue;
      // The shared symbol for a slot is keyed by the slot at its VALUE width (what loads of it use), NOT the pointer
      // width widthOf(slot) would give -- otherwise the iv symbol here would not match the guard's iv symbol.
      unsigned ivW = ivWidth(iv, w);
      smt::TermRef cntSym = fresh(slot, w);
      smt::TermRef ivSym = zextTo(fresh(iv, ivW), ivW, w);
      smt::TermRef trip = tm.mkBin(smt::Kind::BvSub, ivSym, tm.bvConst(w, (uint64_t)iv0));   // iv − iv0
      long C, cnt0, init0;
      if (cfg.accumulator(slot, lp, C, cnt0)) {
        smt::TermRef rhs = tm.mkBin(smt::Kind::BvAdd, tm.bvConst(w, (uint64_t)cnt0),
                                    tm.mkBin(smt::Kind::BvMul, tm.bvConst(w, (uint64_t)C), trip));
        side.push_back(tm.mkCmp(smt::Kind::Ule, cntSym, rhs));   // cnt ≤ cnt0 + C·(iv − iv0)  (constant non-neg step)
        return;
      }
      // Symbolic but loop-invariant step `cnt += s`, single unconditional store: the header value is EXACTLY
      // cnt0 + s·(iv − iv0). `s` shares its symbol (termOf) with any guard that bounds it, so a surrounding bound on s
      // (e.g. `if (s <= M)`) then bounds cnt by the trip count. An unbounded s (acc_sym) stays sat -- correctly.
      if (const Value *step = cfg.symStepAccumulator(slot, lp, init0)) {
        smt::TermRef s = zextTo(termOf(step), widthOf(step), w);
        smt::TermRef rhs = tm.mkBin(smt::Kind::BvAdd, tm.bvConst(w, (uint64_t)init0), tm.mkBin(smt::Kind::BvMul, s, trip));
        side.push_back(tm.mkEq(cntSym, rhs));                    // cnt == init0 + s·(iv − iv0)  (exact modular relation)
        return;
      }
      // Interval delta: a per-iteration-varying step with a structural constant bound M (a byte `len += buf[i]`, a
      // masked `cnt += x & 0xF`). Each iteration adds at most M -> cnt <= init0 + M·(iv − iv0) (<=, conditional-safe).
      long M;
      if (cfg.intervalAccumulator(slot, lp, M, init0)) {
        smt::TermRef rhs = tm.mkBin(smt::Kind::BvAdd, tm.bvConst(w, (uint64_t)init0),
                                    tm.mkBin(smt::Kind::BvMul, tm.bvConst(w, (uint64_t)M), trip));
        side.push_back(tm.mkCmp(smt::Kind::Ule, cntSym, rhs));   // cnt ≤ init0 + M·(iv − iv0)
        return;
      }
    }
  }

  // P2 in-loop lower bound: a unit-step induction var or a non-negative constant-step accumulator never drops below its
  // constant init `init0` (both start there and only ever add a non-negative amount). Assert `init0 <=s S` (SIGNED) for
  // the shared symbol, so an access whose only unsafe case is a NEGATIVE index -- a signed counter sign-extended into
  // the pointer offset, giving the `slt(offset,0)` disjunct of the oob V -- is discharged. The step-3b guard `i < N`
  // already supplies the upper bound; this is the missing lower half. Gated on init0 >= 0 (so the signed constant is
  // real) and on the monotonicity inductionVar/accumulator already verify (a conditionally-stepped slot is rejected).
  void emitMonotoneLowerBound(const Value *slot, unsigned w, const Block *loadBlk) {
    if (!loEmitted.insert(slot).second) return;
    for (const Loop &lp : cfg.loops) {
      if (!lp.body.count(loadBlk)) continue;
      long init0, C, cnt0, iv0;
      bool mono = false;
      if (cfg.inductionVar(lp, iv0) == slot) { init0 = iv0; mono = true; }
      else if (cfg.accumulator(slot, lp, C, cnt0)) { init0 = cnt0; mono = true; }
      if (!mono || init0 < 0) continue;
      side.push_back(tm.mkCmp(smt::Kind::Sle, tm.bvConst(w, (uint64_t)init0), fresh(slot, w)));  // init0 <=s S
      return;
    }
  }

  // P2 coupled-counter invariant: `while (dn) { up += C; dn--; }` -- the up-counter and the down-counter are coupled,
  // so the body runs at most dn0 (the down-counter's initial value) times, giving up <= up0 + C*dn0. When dn0 is itself
  // bounded (a constant, a structurally-bounded value, or a bounded-returning call via the interprocedural summary),
  // the indexed access `buf[up]` proves SAFE even though the loop guard is on dn, not up. The canonical length-bounded
  // byte copy. Sound with break exits (<=) and for any non-negative up step.
  void emitDownCounterBound(const Value *up, unsigned w, const Block *loadBlk) {
    if (!dcEmitted.insert(up).second) return;
    for (const Loop &lp : cfg.loops) {
      if (!lp.body.count(loadBlk)) continue;
      long up0, C, iv0;
      if (cfg.inductionVar(lp, iv0) == up) { up0 = iv0; C = 1; }
      else if (!cfg.accumulator(up, lp, C, up0)) continue;       // up must be a non-neg const-step counter of lp
      const Value *dn0val = nullptr;
      const Value *dn = cfg.downCounter(lp, dn0val);
      if (!dn || dn == up || !dn0val) continue;
      smt::TermRef U = fresh(up, w);
      smt::TermRef d0 = zextTo(termOf(dn0val), widthOf(dn0val), w);
      smt::TermRef rhs = tm.mkBin(smt::Kind::BvAdd, tm.bvConst(w, (uint64_t)up0),
                                  tm.mkBin(smt::Kind::BvMul, tm.bvConst(w, (uint64_t)C), d0));
      side.push_back(tm.mkCmp(smt::Kind::Ule, U, rhs));          // up <= up0 + C*dn0
      return;
    }
  }

  // The shared-symbol width of an induction/accumulator slot: the VALUE width its loads use (alloca size), not the
  // pointer width -- matches emitAccInvariant so the symbols coincide.
  unsigned ivWidth(const Value *iv, unsigned w) {
    unsigned ivW = (iv->defOp && iv->defOp->opc == Opc::Alloca) ? (unsigned)(iv->defOp->intAttr("size") * 8) : w;
    return ivW ? ivW : w;
  }
  // Every store to `slot` is either in the loop body or a pre-loop init that dominates the header -- so after the loop
  // nothing overwrites the exit value. (A post-loop re-store would make the exit-value bound unsound.)
  bool storesConfinedToLoop(const Value *slot, const Loop &lp) {
    auto sit = cfg.stores.find(slot);
    if (sit == cfg.stores.end()) return false;
    for (const Op *st : sit->second) {
      auto bit = cfg.opBlock.find(st);
      const Block *sb = bit == cfg.opBlock.end() ? nullptr : bit->second;
      if (!sb || (!lp.body.count(sb) && !cfg.dominates(sb, lp.header))) return false;
    }
    return true;
  }
  // The STRICT upper bound N (width w) from a loop header guard `iv < N` (counting up). Returns null for a non-strict
  // guard (`iv <= N` exits at N+1, a different bound), a guard not on this iv, or a switch/other terminator. Handles iv
  // on either side and the guard-true-edge being either the body or the exit.
  smt::TermRef headerUpperBound(const Loop &lp, const Value *iv, unsigned w) {
    const Op *t = lp.header->terminator();
    if (!t || t->opc != Opc::CondBr || t->operands.empty() || t->succs.size() < 2) return nullptr;
    bool bodyT = lp.body.count(t->succs[0].dest), bodyF = lp.body.count(t->succs[1].dest);
    if (bodyT == bodyF) return nullptr;                         // ambiguous: both or neither successor is the body
    const Value *cond = t->operands[0];
    if (!cond || !cond->defOp || cond->defOp->opc != Opc::ICmp || cond->defOp->operands.size() < 2) return nullptr;
    const Op &cmp = *cond->defOp;
    const Value *a = cmp.operands[0], *b = cmp.operands[1];
    auto isIv = [&](const Value *x) {
      return x && x->defOp && x->defOp->opc == Opc::Load && !x->defOp->operands.empty() && x->defOp->operands[0] == iv;
    };
    const std::string &p = cmp.pred;
    const Value *N = nullptr;
    // Want the continue-into-body condition to be exactly `iv < N` (strict), so the exit value is <= N.
    if (isIv(a) && !isIv(b)) {                                  // cond = (iv P N)
      if (bodyT ? (p == "ult" || p == "slt") : (p == "uge" || p == "sge")) N = b;
    } else if (isIv(b) && !isIv(a)) {                          // cond = (N P iv)
      if (bodyT ? (p == "ugt" || p == "sgt") : (p == "ule" || p == "sle")) N = a;
    }
    return N ? zextTo(termOf(N), widthOf(N), w) : nullptr;
  }
  // P2 post-loop exit value (DESIGN §4.4 follow-up): `slot` is loaded AFTER its loop (header dominates loadBlk, loadBlk
  // outside the body), so it reads the loop's EXIT value. For a unit-step induction counter iv with const init iv0 and
  // guard `iv < N`, the exit value obeys  iv0 ≤ ivExit ≤ umax(N, iv0)  -- sound for any number of `break` exits (every
  // +1 is guarded by iv<N) and for zero iterations (umax folds to iv0). If `slot` is instead a constant-step
  // accumulator of that loop, its exit value obeys  slot ≤ cnt0 + C·(ivExit − iv0)  with ivExit bounded as above, i.e.
  // the trip-count bound -- the `process(buf, cnt)` length idiom. Returns the slot's shared symbol, or null if no match.
  smt::TermRef postLoopExitSym(const Value *slot, unsigned w, const Block *loadBlk) {
    for (const Loop &lp : cfg.loops) {
      if (lp.body.count(loadBlk) || !cfg.dominates(lp.header, loadBlk)) continue;  // must read the loop's exit value
      long iv0; const Value *iv = cfg.inductionVar(lp, iv0);
      if (!iv || !storesConfinedToLoop(iv, lp)) continue;      // iv must not be overwritten after the loop
      smt::TermRef N = headerUpperBound(lp, iv, w);
      if (!N) continue;
      unsigned ivW = ivWidth(iv, w);
      smt::TermRef ivSym = zextTo(fresh(iv, ivW), ivW, w);
      smt::TermRef c0 = tm.bvConst(w, (uint64_t)iv0);
      smt::TermRef ub = tm.mkIte(tm.mkCmp(smt::Kind::Ule, c0, N), N, c0);          // umax(N, iv0)
      auto boundIv = [&] {
        if (!exitEmitted.insert(iv).second) return;
        side.push_back(tm.mkCmp(smt::Kind::Ule, c0, ivSym));                       // iv0 ≤ ivExit
        side.push_back(tm.mkCmp(smt::Kind::Ule, ivSym, ub));                       // ivExit ≤ umax(N, iv0)
      };
      if (iv == slot) { boundIv(); return ivSym; }                                // the counter itself, used after the loop
      long C, cnt0;
      if (storesConfinedToLoop(slot, lp) && cfg.accumulator(slot, lp, C, cnt0)) {
        boundIv();
        if (exitEmitted.insert(slot).second) {
          smt::TermRef cntSym = fresh(slot, w);
          smt::TermRef rhs = tm.mkBin(smt::Kind::BvAdd, tm.bvConst(w, (uint64_t)cnt0),
                                      tm.mkBin(smt::Kind::BvMul, tm.bvConst(w, (uint64_t)C),
                                               tm.mkBin(smt::Kind::BvSub, ivSym, tm.bvConst(w, (uint64_t)iv0))));
          side.push_back(tm.mkCmp(smt::Kind::Ule, cntSym, rhs));                   // cnt ≤ cnt0 + C·(ivExit − iv0)
        }
        return fresh(slot, w);
      }
    }
    return nullptr;
  }

  // The branch condition of p's terminator for the edge p->b (Bool), or null if it cannot be encoded precisely
  // (a switch: skip rather than risk an unsound selector).
  smt::TermRef edgeGuard(const Block *p, const Block *b) {
    const Op *t = p ? p->terminator() : nullptr;
    if (!t) return tm.boolConst(true);
    if (t->opc == Opc::CondBr && !t->operands.empty() && t->succs.size() >= 2) {
      bool isT = t->succs[0].dest == b, isF = t->succs[1].dest == b;
      smt::TermRef c = tm.toBool(termOf(t->operands[0]));
      if (isT && !isF) return c;
      if (isF && !isT) return tm.mkNot(c);
      return tm.boolConst(true);  // both/neither: no constraint
    }
    if (t->opc == Opc::Br) return tm.boolConst(true);  // unconditional
    return nullptr;                                     // switch / other: cannot encode soundly
  }
  // Path condition to reach block b (Bool). Used as the antecedent of a φ implication, so it must UNDER-approximate
  // "b is reached": a too-permissive reach would wrongly force r==v (unsound). Hence every fallback is `false` and an
  // unencodable (switch) pred edge is skipped, never made `true`. entry is always reached; cycles break to false.
  smt::TermRef reachOf(const Block *b) {
    if (b == cfg.entryBlock) return tm.boolConst(true);
    auto m = reachMemo.find(b);
    if (m != reachMemo.end()) return m->second;
    if (!reachStack.insert(b).second) return tm.boolConst(false);  // in a cycle: under-approximate
    smt::TermRef acc = nullptr;
    auto pit = cfg.preds.find(b);
    if (pit != cfg.preds.end())
      for (const Block *p : pit->second) {
        if (cfg.isBackEdge(p, b)) continue;
        smt::TermRef g = edgeGuard(p, b);
        if (!g) continue;                             // unencodable edge: drop it (reach stays an under-approx)
        smt::TermRef er = tm.mkAnd(reachOf(p), g);
        acc = acc ? tm.mkOr(acc, er) : er;
      }
    smt::TermRef res = acc ? acc : tm.boolConst(false);  // no encodable forward edge -> treat as not-reached (sound)
    reachStack.erase(b);
    reachMemo[b] = res;
    return res;
  }

  smt::TermRef termOf(const Value *v) {
    auto m = memo.find(v);
    if (m != memo.end()) return m->second;
    smt::TermRef r = build(v);
    memo[v] = r;
    return r;
  }
  smt::TermRef build(const Value *v) {
    unsigned w = widthOf(v);
    if (v->kind == Value::BlockArg) {
      const Block *B = v->defBlock;
      if (B == cfg.entryBlock) {                          // a parameter: free, but bounded if the interprocedural
        smt::TermRef P = fresh(v, w);                     // param summary found every (in-module) call site bounded
        if (paramBounds) {
          auto it = paramBounds->find(fnName);
          if (it != paramBounds->end()) {
            auto jt = it->second.find(v->index);
            unsigned long long cap = (w >= 64) ? ~0ull : ((1ull << w) - 1);
            if (jt != it->second.end() && (unsigned long long)jt->second < cap)
              side.push_back(tm.mkCmp(smt::Kind::Ule, P, tm.bvConst(w, (uint64_t)jt->second)));
          }
        }
        return P;
      }
      if (cfg.loopHeaders.count(B)) return fresh(v, w);   // loop-carried: free
      // φ: fresh var constrained per incoming edge. Skip if any pred edge is unencodable (switch) -> stay fresh/sound.
      auto pit = cfg.preds.find(B);
      if (pit == cfg.preds.end()) return fresh(v, w);
      smt::TermRef r = fresh(v, w);
      memo[v] = r;                                         // memoise before recursing (incoming values may cycle back)
      for (const Block *p : pit->second) {
        if (cfg.isBackEdge(p, B)) continue;               // loop back-edge value: leave r free for it
        const Op *t = p->terminator();
        if (!t) continue;
        const Value *vin = nullptr;                        // the value p passes for this arg index
        for (const Succ &s : t->succs)
          if (s.dest == B && v->index < s.args.size()) { vin = s.args[v->index]; break; }
        smt::TermRef g = edgeGuard(p, B);
        if (!vin || !g) continue;                          // unencodable edge: drop its constraint (r stays free there)
        smt::TermRef er = tm.mkAnd(reachOf(p), g);         // reached B via this edge => r == value from p
        side.push_back(tm.mkImplies(er, tm.mkEq(r, termOf(vin))));
      }
      return r;
    }
    if (v->kind != Value::OpResult || !v->defOp) return fresh(v, w);
    const Op &d = *v->defOp;
    auto bin = [&](smt::Kind k) { return tm.mkBin(k, termOf(d.operands[0]), termOf(d.operands[1])); };
    switch (d.opc) {
      case Opc::Const: return tm.bvConst(d.constVal);
      case Opc::Add: return bin(smt::Kind::BvAdd);
      case Opc::Sub: return bin(smt::Kind::BvSub);
      case Opc::Mul: return bin(smt::Kind::BvMul);
      case Opc::And: return bin(smt::Kind::BvAnd);
      case Opc::Or: return bin(smt::Kind::BvOr);
      case Opc::Xor: return bin(smt::Kind::BvXor);
      case Opc::Shl: return bin(smt::Kind::BvShl);
      case Opc::LShr: return bin(smt::Kind::BvLshr);
      case Opc::AShr: return bin(smt::Kind::BvAshr);
      case Opc::UDiv: return bin(smt::Kind::BvUdiv);
      case Opc::SDiv: return bin(smt::Kind::BvSdiv);
      case Opc::URem: return bin(smt::Kind::BvUrem);
      case Opc::SRem: return bin(smt::Kind::BvSrem);
      case Opc::Neg: return tm.mkUn(smt::Kind::BvNeg, termOf(d.operands[0]));
      case Opc::Not: return tm.mkUn(smt::Kind::BvNot, termOf(d.operands[0]));
      case Opc::ZExt: return tm.mkZExt(termOf(d.operands[0]), w);
      case Opc::SExt: return tm.mkSExt(termOf(d.operands[0]), w);
      case Opc::Trunc: return tm.mkExtract(termOf(d.operands[0]), w - 1, 0);
      case Opc::Select:
        return tm.mkIte(tm.toBool(termOf(d.operands[0])), termOf(d.operands[1]), termOf(d.operands[2]));
      case Opc::ICmp: {
        smt::TermRef a = termOf(d.operands[0]), b = termOf(d.operands[1]);
        smt::TermRef r = d.pred == "eq" ? tm.mkEq(a, b)
                       : d.pred == "ne" ? tm.mkNot(tm.mkEq(a, b))
                       : d.pred == "ult" ? tm.mkCmp(smt::Kind::Ult, a, b)
                       : d.pred == "ule" ? tm.mkCmp(smt::Kind::Ule, a, b)
                       : d.pred == "ugt" ? tm.mkCmp(smt::Kind::Ult, b, a)
                       : d.pred == "uge" ? tm.mkCmp(smt::Kind::Ule, b, a)
                       : d.pred == "slt" ? tm.mkCmp(smt::Kind::Slt, a, b)
                       : d.pred == "sle" ? tm.mkCmp(smt::Kind::Sle, a, b)
                       : d.pred == "sgt" ? tm.mkCmp(smt::Kind::Slt, b, a)
                       : d.pred == "sge" ? tm.mkCmp(smt::Kind::Sle, b, a)
                       : (smt::TermRef) nullptr;
        return r ? tm.fromBool(r) : fresh(v, w);
      }
      case Opc::Load: {                                   // forward a promotable local slot with a single reaching store
        const Value *ptr = d.operands.empty() ? nullptr : d.operands[0];
        if (ptr && cfg.promotable.count(ptr)) {
          auto it = cfg.stores.find(ptr);
          if (it != cfg.stores.end()) {
            if (it->second.size() == 1 && it->second[0]->operands.size() >= 1)
              return termOf(it->second[0]->operands[0]);
            // P2 loop summary: a slot stored inside a loop that also contains this load is a loop-carried variable
            // (induction / accumulator). Give ALL its in-loop loads ONE symbol keyed by the slot, so the loop guard
            // `i < n` -- captured by step-3b as a necessary reach condition -- constrains the access's `i`. Sound:
            // within one check's cone every load of the slot is the same (current-iteration) value.
            const Block *loadBlk = cfg.opBlock.count(v->defOp) ? cfg.opBlock.at(v->defOp) : nullptr;
            if (loadBlk) {
              bool carried = false;
              for (const Op *st : it->second) {
                auto bit = cfg.opBlock.find(st);
                if (bit != cfg.opBlock.end() && cfg.inSameLoop(bit->second, loadBlk)) { carried = true; break; }
              }
              // Share the one per-slot symbol ONLY when this load reads the loop-HEADER value (no in-loop store reaches
              // it before the back-edge). Otherwise the guard (which bounds the header value) does not apply to this
              // load, and sharing would be unsound -- e.g. `while(i<10){ i=i+1; a[i] }` reaches a[10].
              if (carried && !cfg.inLoopStoreReachesLoad(ptr, v->defOp, loadBlk)) {
                emitAccInvariant(ptr, w, loadBlk);        // P2: if `ptr` is a constant-step accumulator, bound it by C·iv
                emitMonotoneLowerBound(ptr, w, loadBlk);  // P2: iv/accumulator >= its const init (kills negative-index case)
                emitDownCounterBound(ptr, w, loadBlk);    // P2: coupled down-counter bound  up <= up0 + C·dn0
                return fresh(ptr, w);
              }
              // P2 post-loop exit value: a use of the loop's induction counter / accumulator AFTER the loop. Bound it by
              // the trip count so a post-loop check on the final value (a length) can prove safe.
              if (!carried) { if (smt::TermRef s = postLoopExitSym(ptr, w, loadBlk)) return s; }
            }
          }
        }
        return fresh(v, w);                               // real memory read, or a non-loop multi-store slot: unconstrained
      }
      case Opc::Call: {                                   // interprocedural return summary: result in the callee's disjunction
        smt::TermRef R = fresh(v, w);
        if (retDisjuncts) {
          auto it = retDisjuncts->find(d.sym);
          if (it != retDisjuncts->end() && !it->second.empty()) {
            unsigned long long cap = (w >= 64) ? ~0ull : ((1ull << w) - 1);
            smt::TermRef acc = nullptr;
            bool vacuous = false;
            for (const RetDisjunct &rd : it->second) {
              if (!rd.isConst && (unsigned long long)rd.val >= cap) { vacuous = true; break; }  // r <= max: no constraint
              smt::TermRef dis = rd.isConst ? tm.mkEq(R, tm.bvConst(w, (uint64_t)rd.val))
                                            : tm.mkCmp(smt::Kind::Ule, R, tm.bvConst(w, (uint64_t)rd.val));
              acc = acc ? tm.mkOr(acc, dis) : dis;
            }
            if (acc && !vacuous) side.push_back(acc);   // r == c1 ∨ r <= M2 ∨ ...  (sound: r is exactly one return)
          }
        }
        return R;
      }
      default: return fresh(v, w);                        // Nondet / HeapAlloc / PtrAdd(as int) / ...: unconstrained
    }
  }

  // Offset and object-size terms for a pointer (width pw). Follows ptr_add to the base; alloca -> const size,
  // heap -> its size operand, anything else -> fresh (unknown pointee size: sound, SAT-leaning).
  void ptrInfo(const Value *ptr, smt::TermRef &offset, smt::TermRef &size) {
    offset = tm.bvConst(pw, 0);
    size = nullptr;
    std::set<const Value *> seen;
    std::function<void(const Value *)> go = [&](const Value *v) {
      if (!v || !seen.insert(v).second) return;
      if (v->kind == Value::OpResult && v->defOp) {
        const Op &d = *v->defOp;
        if (d.opc == Opc::PtrAdd) {
          for (unsigned i = 1; i < d.operands.size(); ++i) {
            const Value *k = d.operands[i];
            offset = tm.mkBin(smt::Kind::BvAdd, offset, zextTo(termOf(k), widthOf(k), pw));
          }
          if (!d.operands.empty()) go(d.operands[0]);
          return;
        }
        if (d.opc == Opc::Alloca) { size = tm.bvConst(pw, (uint64_t)d.intAttr("size", 0)); return; }
        if (d.opc == Opc::HeapAlloc && !d.operands.empty()) { size = zextTo(termOf(d.operands[0]), widthOf(d.operands[0]), pw); return; }
      }
      size = fresh(v, pw);  // global / loaded pointer / int_to_ptr: unknown size
    };
    go(ptr);
    if (!size) size = fresh(ptr, pw);
  }

  // The violation predicate V (Bool) for a numeric candidate, or nullptr if this kind is not solved.
  smt::TermRef violation(const Candidate &c) {
    const Op &op = *c.op;
    const auto &o = op.operands;
    auto ugt = [&](smt::TermRef a, smt::TermRef b) { return tm.mkCmp(smt::Kind::Ult, b, a); };  // a >u b
    switch (op.opc) {
      // ---- pointer / memory side (ubViolations returns false for these; the engine does them in Memory.h) ----
      case Opc::CheckOob: {
        if (o.empty()) return nullptr;
        smt::TermRef off, size;
        ptrInfo(o[0], off, size);
        unsigned wacc = (unsigned)op.intAttr("w", 1);
        smt::TermRef hi = tm.mkBin(smt::Kind::BvAdd, off, tm.bvConst(pw, wacc));  // off + w
        return tm.mkOr(ugt(hi, size), tm.mkCmp(smt::Kind::Slt, off, tm.bvConst(pw, 0)));  // off+w > size ∨ off < 0
      }
      case Opc::MemCpy: case Opc::MemMove: case Opc::MemSet: {
        if (o.size() < 3) return nullptr;
        smt::TermRef n = zextTo(termOf(o[2]), widthOf(o[2]), pw);
        smt::TermRef offD, sizeD;
        ptrInfo(o[0], offD, sizeD);
        smt::TermRef v = ugt(n, sizeD);
        if (op.opc != Opc::MemSet) { smt::TermRef offS, sizeS; ptrInfo(o[1], offS, sizeS); v = tm.mkOr(v, ugt(n, sizeS)); }
        return v;
      }
      case Opc::Call: {  // recognised copy-class library call: n > size(dst)
        int li = memCallLenArg(op.sym);
        if (li < 0 || (unsigned)li >= o.size() || o.empty()) return nullptr;
        smt::TermRef n = zextTo(termOf(o[li]), widthOf(o[li]), pw);
        smt::TermRef offD, sizeD;
        ptrInfo(o[0], offD, sizeD);
        return ugt(n, sizeD);
      }
      case Opc::CheckPtrArith: {
        // Engine (Memory.h): V = (base.off + delta >u size(base)) ∧ notNull ∧ sizeIsReal. Dropping the two guard
        // conjuncts is a sound over-approximation (a weaker V: UNSAT of it still implies the real V is UNSAT => safe).
        if (o.size() < 2) return nullptr;
        smt::TermRef baseOff, size;
        ptrInfo(o[0], baseOff, size);
        smt::TermRef newOff = tm.mkBin(smt::Kind::BvAdd, baseOff, zextTo(termOf(o[1]), widthOf(o[1]), pw));
        return ugt(newOff, size);
      }
      // ---- integer side: reuse the engine's ONE definition (div / shift / overflow family / field_oob) ----
      default: {
        TermOps td(tm);
        std::vector<smt::TermRef> a;
        for (const Value *v : o) a.push_back(termOf(v));
        std::vector<UBViolation<TermOps>> out;
        if (!ubViolations(td, op, a, out) || out.empty()) return nullptr;  // ptr_arith etc.: not handled here
        smt::TermRef v = nullptr;  // violated if ANY listed UB kind fires
        for (auto &uv : out) v = v ? td.or_(v, uv.cond) : uv.cond;
        return tm.toBool(v);  // out conds are width-1 bv; assert them as Bool
      }
    }
  }
};

// "file:line" keyed by basename, for matching a check loc against forward coverage regardless of path spelling.
static std::string basenameLine(const std::string &file, unsigned line) {
  auto sl = file.find_last_of('/');
  return (sl == std::string::npos ? file : file.substr(sl + 1)) + ":" + std::to_string(line);
}
// Minimal extractor for hlir-scan's coverage.covered_lines (a flat JSON array of "file:line" strings, one array per
// report entry). Avoids a JSON dependency -- the field is machine-generated with no escaped quotes in its entries. The
// returned set is keyed by basename:line so it matches the probe's own loc printing. This is the forward engine's
// POSITIVE coverage; a backward SAFE proof whose line is absent is the seam③ uncovered-bucket (safe on code forward
// never executed). See docs/BACKWARD_WP_DESIGN.md §3.3.
static std::set<std::string> loadCoveredLines(const std::string &jsonPath) {
  std::set<std::string> out;
  std::ifstream f(jsonPath);
  if (!f) { std::cerr << "hlir-wp-probe: cannot open --forward-coverage " << jsonPath << "\n"; return out; }
  std::stringstream ss; ss << f.rdbuf();
  const std::string s = ss.str(), key = "\"covered_lines\"";
  for (size_t pos = 0; (pos = s.find(key, pos)) != std::string::npos;) {
    size_t lb = s.find('[', pos), rb = (lb == std::string::npos) ? std::string::npos : s.find(']', lb);
    if (lb == std::string::npos || rb == std::string::npos) break;
    for (size_t i = lb; i < rb;) {
      size_t q1 = s.find('"', i);
      if (q1 == std::string::npos || q1 > rb) break;
      size_t q2 = s.find('"', q1 + 1);
      if (q2 == std::string::npos || q2 > rb) break;
      std::string fl = s.substr(q1 + 1, q2 - q1 - 1);           // "file:line"
      auto c = fl.rfind(':');
      if (c != std::string::npos) {
        unsigned ln = (unsigned)strtoul(fl.c_str() + c + 1, nullptr, 10);
        out.insert(basenameLine(fl.substr(0, c), ln));
      }
      i = q2 + 1;
    }
    pos = rb + 1;
  }
  return out;
}

}  // namespace

int main(int argc, char **argv) {
  std::string path, fcovPath;
  bool list = false, solve = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--list") list = true;
    else if (a == "--solve") solve = true;
    else if ((a == "--forward-coverage" || a == "--fcov") && i + 1 < argc) fcovPath = argv[++i];
    else if (!a.empty() && a[0] == '-') { std::cerr << "unknown option " << a << "\n"; return 2; }
    else path = a;
  }
  if (path.empty()) { std::cerr << "usage: hlir-wp-probe [--list] [--solve] [--forward-coverage scan.json] file.core\n"; return 2; }
  // seam③ uncovered-bucket: forward's covered-lines set (from hlir-scan --format json). Empty / unset -> no tagging.
  std::set<std::string> coveredLines;
  if (!fcovPath.empty()) coveredLines = loadCoveredLines(fcovPath);
  const bool fcov = !coveredLines.empty();

  std::ifstream in(path);
  if (!in) { std::cerr << "cannot open " << path << "\n"; return 2; }
  std::stringstream ss;
  ss << in.rdbuf();

  Diagnostics diags;
  auto mod = parseModule(ss.str(), path, diags);           // step 0
  if (!mod) { std::cerr << "parse failed:\n" << diags.str(); return 1; }

  unsigned long denom = 0, inLoop = 0, numericN = 0, nonNumericN = 0, emptyS = 0, withLoopCarried = 0;
  std::map<std::string, unsigned long> byKind;
  std::map<unsigned, unsigned long> sHist;                 // |S| -> count (numeric checks)
  std::map<Root, unsigned long> rootHist;                  // root class -> count (over all numeric checks)
  // P1 (--solve) tallies
  unsigned long slvSafe = 0, slvSat = 0, slvUnknown = 0, slvUnsupported = 0;
  unsigned long slvSafeUncov = 0, slvSafeCov = 0;   // seam③ uncovered-bucket: SAFE on a line forward did / did not execute

  smt::TermManager tm;
  std::unique_ptr<smt::Solver> solver;
  if (solve) {
    solver = smt::makeZ3NativeSolver(10000);
    if (!solver) solver = smt::makeZ3ProcessSolver("z3", 10000);
    if (!solver) { std::cerr << "hlir-wp-probe --solve: no Z3 solver available\n"; return 1; }
  }
  // Interprocedural return summaries (computed once over the whole module): callee -> sound upper bound on its return
  // value. At a `core.call`, the result is constrained <= this instead of fresh, so a check indexing with a bounded-
  // returning callee proves SAFE without inlining.
  std::map<std::string, std::vector<RetDisjunct>> retDisjuncts;
  for (const auto &fup : mod->functions) {
    if (fup->isDeclaration()) continue;
    CFG cfg = buildCFG(*fup);                                   // need its pathGuards for guard-derived return bounds
    std::vector<RetDisjunct> ds;
    if (returnDisjuncts(*fup, cfg, ds)) retDisjuncts[fup->name] = std::move(ds);
  }
  // Interprocedural parameter summaries: a param's sound upper bound, for an INTERNAL (all callers in-module) function
  // that is not address-taken (no indirect callers) and whose EVERY direct call site passes a structurally-bounded
  // argument for that param. The meet over those call sites is then the meet over ALL callers -> sound.
  std::map<std::string, std::map<unsigned, long>> paramBounds;
  {
    std::set<std::string> addrTaken;
    for (const auto &fp : mod->functions)
      for (const auto &b : fp->blocks)
        for (const auto &op : b->ops)
          if (op->opc == Opc::FuncAddr) addrTaken.insert(op->sym);
    for (const auto &fp : mod->functions) {
      const Function &F = *fp;
      if (F.isDeclaration() || !F.internal || addrTaken.count(F.name)) continue;
      unsigned np = F.paramTys.size();
      std::vector<long> bnd(np, 0);
      std::vector<char> ok(np, 1);
      bool anyCall = false;
      for (const auto &gp : mod->functions)
        for (const auto &b : gp->blocks)
          for (const auto &op : b->ops)
            if (op->opc == Opc::Call && op->sym == F.name) {
              anyCall = true;
              for (unsigned i = 0; i < np; ++i) {
                if (!ok[i]) continue;
                long m;
                if (i >= op->operands.size() || !structuralUpperBound(op->operands[i], m)) ok[i] = 0;
                else if (m > bnd[i]) bnd[i] = m;
              }
            }
      if (!anyCall) continue;
      for (unsigned i = 0; i < np; ++i)
        if (ok[i]) paramBounds[F.name][i] = bnd[i];
    }
  }
  unsigned fnCounter = 0;

  for (const auto &fup : mod->functions) {
    const Function &f = *fup;
    if (f.isDeclaration()) continue;
    CFG cfg = buildCFG(f);
    std::set<const Block *> loopBlocks;
    for (const Loop &lp : loopsOf(f))
      for (const Block *b : lp.body) loopBlocks.insert(b);
    Solver1 s1{cfg, tm, mod->ctx.ptrWidth()};
    s1.fnIdx = fnCounter++;
    s1.retDisjuncts = &retDisjuncts;
    s1.paramBounds = &paramBounds;
    s1.fnName = f.name;

    for (const auto &bup : f.blocks) {
      const Block &b = *bup;
      bool bInLoop = loopBlocks.count(&b) != 0;
      for (const auto &oup : b.ops) {
        const Op &op = *oup;
        Candidate cand;
        if (!recognise(op, cand)) continue;
        ++denom;
        ++byKind[cand.kind];
        if (bInLoop) ++inLoop;

        if (!cand.numeric) { ++nonNumericN; continue; }
        ++numericN;
        Slice sl;
        slice(seedsFor(cand), cfg, sl);
        unsigned Scount = (unsigned)sl.sVars.size();   // distinct variables-to-model (DESIGN §2.1 |S|)
        ++sHist[Scount];
        for (const auto &kv : sl.classHist)
          if (countsTowardS(kv.first)) rootHist[kv.first] += kv.second;
        if (Scount == 0) ++emptyS;
        if (sl.hitLoopCarried) ++withLoopCarried;

        const char *verdict = nullptr;   // P1: UNSAT=safe / SAT=candidate / unknown / unsupported
        int uncov = -1;                  // seam③: for a SAFE verdict with --forward-coverage, 1=uncovered / 0=covered
        if (solve) {
          smt::TermRef V = s1.violation(cand);
          if (V) {  // step 3b: conjoin the path guards necessary to reach this check's block (sound, tightens V)
            auto git = cfg.pathGuards.find(&b);
            if (git != cfg.pathGuards.end())
              for (const auto &g : git->second) {
                smt::TermRef gc = tm.toBool(s1.termOf(g.first));
                V = tm.mkAnd(V, g.second ? gc : tm.mkNot(gc));
              }
          }
          if (!V) { ++slvUnsupported; verdict = "unsupported"; }
          else {
            solver->push();
            for (smt::TermRef sc : s1.side) solver->assertTerm(sc);  // φ phi-equations (accumulated, all valid facts)
            solver->assertTerm(V);
            smt::SatResult r = solver->check();
            solver->pop();
            if (r == smt::SatResult::Unsat) {
              ++slvSafe; verdict = "SAFE(unsat)";
              if (fcov) {   // seam③ uncovered-bucket: did any forward run execute this check's line?
                uncov = coveredLines.count(basenameLine(op.loc.file, op.loc.line)) ? 0 : 1;
                if (uncov) ++slvSafeUncov; else ++slvSafeCov;
              }
            }
            else if (r == smt::SatResult::Sat) { ++slvSat; verdict = "sat(candidate)"; }
            else { ++slvUnknown; verdict = "unknown"; }
          }
        }

        if (list) {
          std::cout << cand.kind << "\t@" << f.name << "\t" << op.loc.file << ":" << op.loc.line
                    << "\t|S|=" << Scount;
          for (const auto &kv : sl.classHist) std::cout << " " << rootName(kv.first) << ":" << kv.second;
          if (bInLoop) std::cout << " in-loop";
          if (verdict) std::cout << "  " << verdict;
          if (uncov == 1) std::cout << " [uncovered]";       // forward never executed this line; backward proved it safe
          else if (uncov == 0) std::cout << " [covered]";
          std::cout << "\n";
        }
      }
    }
  }

  std::cout << "\n=== hlir-wp-probe P0 (steps 1-4) ===\n";
  std::cout << "module: " << path << "\n";
  std::cout << "denominator (isCheck candidates): " << denom << "   (in-loop: " << inLoop << ")\n";
  std::cout << "  numeric (sliced): " << numericN << "   non-numeric (uninit/align, not sliced): " << nonNumericN << "\n";
  std::cout << "by UBKind:\n";
  for (const auto &kv : byKind) std::cout << "  " << kv.first << ": " << kv.second << "\n";

  std::cout << "\n--- the P0 gate numbers (numeric checks) ---\n";
  std::cout << "empty S (free safety candidate for P1): " << emptyS << " / " << numericN << "\n";
  std::cout << "checks whose S hits a loop-carried root:  " << withLoopCarried << "\n";
  std::cout << "|S| distribution:\n";
  for (const auto &kv : sHist) std::cout << "  |S|=" << kv.first << ": " << kv.second << "\n";
  std::cout << "root-class histogram (variables to model, seam ②):\n";
  for (const auto &kv : rootHist) std::cout << "  " << rootName(kv.first) << ": " << kv.second << "\n";

  if (solve) {
    std::cout << "\n--- P1 UNSAT pruning (--solve; roots = fresh unconstrained, so UNSAT is a sound safety proof) ---\n";
    std::cout << "SAFE (bucket 1, violation UNSAT):     " << slvSafe << "\n";
    if (fcov) {
      std::cout << "  of which UNCOVERED-BUCKET (SAFE on a line no forward run executed): " << slvSafeUncov
                << "   [backward's unique payoff: safe on code the forward search never reached]\n";
      std::cout << "  of which forward also covered:      " << slvSafeCov << "\n";
    }
    std::cout << "candidate (SAT, needs path/alias/P2):  " << slvSat << "\n";
    std::cout << "unknown (solver timeout):              " << slvUnknown << "\n";
    std::cout << "unsupported (no V built):               " << slvUnsupported << "\n";
  }
  return 0;
}

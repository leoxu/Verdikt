// Reaching-definitions-style candidate write-site search (docs/DESIGN.md Sec.22.326-22.328,
// docs/LLM_ASSISTED_TRIAGE_DESIGN.md Sec.3.3b): given a pointer-typed Value read at some anchor site (e.g. the
// `core.load` that feeds a suspicious `if (A) ...` condition), find every `core.store` -- in the anchor's own
// function and transitively through direct calls -- whose target address structurally denotes the SAME
// stack/global object at the SAME offset, so each candidate can be fed to the existing `--reach-target`/
// `where:`/`taint:value,range:` machinery instead of hand-deriving the answer by reading code (the brotli 55-byte
// trigger's original derivation, see Sec.22.314/322).
//
// This is a pure, static, structural analysis over the IR graph -- it never runs anything, so it has no access to
// concrete values; "the same object" means the same `core.alloca`/`core.global_addr` op or the same formal
// parameter position, not the same runtime address (that is the concolic engine's job once a candidate is handed
// to it). Deliberately conservative: anything it cannot resolve (a pointer computed through a call's return value,
// an indirect/function-pointer call -- not expressible as `core.call` in this IR, see Sec.22.327's note that
// core.call is always direct here -- or arithmetic that is not a plain alloca/global/param + core.ptr_add chain)
// is a bail (no site claimed from that path), never a guess.
#pragma once
#include <map>
#include <set>
#include <string>
#include <vector>

#include "hlir/ir/IR.h"
#include "hlir/support/Loc.h"
#include "llvm/ADT/SmallString.h"

namespace hlir {

struct WriteSite {
  const Function *fn = nullptr;
  const Op *storeOp = nullptr;
  Loc loc;
};

// What a pointer Value structurally denotes, resolved within the single function it was computed in.
struct Origin {
  enum Kind { Alloca, Param, Global, Unknown } kind = Unknown;
  const Op *allocaOp = nullptr;  // Kind::Alloca: identity is the defining core.alloca op itself
  unsigned paramIndex = 0;       // Kind::Param: position in the owning function's own parameter list
  const Op *globalOp = nullptr;  // Kind::Global: identity is the defining core.global_addr op
  bool operator==(const Origin &o) const {
    if (kind != o.kind) return false;
    switch (kind) {
      case Alloca: return allocaOp == o.allocaOp;
      case Param: return paramIndex == o.paramIndex;
      case Global: return globalOp == o.globalOp;
      default: return false;
    }
  }
};

namespace detail {

// A structural (not value) key for comparing two expressions found WITHIN THE SAME function -- e.g. two
// `core.ptr_add` offsets that are both "the current `tree_type` loop variable" rather than both a literal
// constant. Not meaningful across two different functions (their Value*/Op* identities never coincide), which is
// exactly why offset-key comparison below is only ever done on values resolved inside the same function.
inline std::string canonicalKey(const Value *v, int fuel = 32) {
  if (!v || fuel <= 0) return "?";
  if (v->kind == Value::BlockArg) return "arg" + std::to_string(v->index);
  const Op *def = v->defOp;
  if (!def) return "?";
  if (def->opc == Opc::Const) {
    llvm::SmallString<32> s;
    def->constVal.toStringSigned(s);
    return "c" + std::string(s);
  }
  std::string s = std::to_string(static_cast<int>(def->opc)) + "(";
  for (auto *a : def->operands) s += canonicalKey(a, fuel - 1) + ",";
  return s + ")";
}

struct Resolved {
  Origin origin;
  std::string offsetKey = "0";  // "0" = the object's own address; else a canonicalKey-derived string
};

// Walks a pointer Value's def chain backward: core.load (spill-reload) passes through to what was loaded;
// core.ptr_add accumulates an offset key onto the base's; core.alloca/core.global_addr/a function parameter
// (Value::BlockArg of the entry block) are the three kinds of terminal origin. Anything else -- most importantly
// a value computed from a core.call's result, or from integer arithmetic that isn't a plain address computation
// -- is Origin::Unknown (a deliberate bail, not a best-effort guess).
inline Resolved resolveOrigin(const Value *v, int fuel = 32) {
  if (!v || fuel <= 0) return {};
  if (v->kind == Value::BlockArg && v->defBlock && v->defBlock->parent && v->defBlock == v->defBlock->parent->entry()) {
    Origin o;
    o.kind = Origin::Param;
    o.paramIndex = v->index;
    return {o, "0"};
  }
  const Op *def = v->defOp;
  if (!def) return {};
  switch (def->opc) {
    case Opc::Alloca: {
      Origin o;
      o.kind = Origin::Alloca;
      o.allocaOp = def;
      return {o, "0"};
    }
    case Opc::GlobalAddr: {
      Origin o;
      o.kind = Origin::Global;
      o.globalOp = def;
      return {o, "0"};
    }
    case Opc::Load:
      return def->operands.empty() ? Resolved{} : resolveOrigin(def->operands[0], fuel - 1);
    case Opc::PtrAdd: {
      if (def->operands.size() < 2) return {};
      Resolved base = resolveOrigin(def->operands[0], fuel - 1);
      if (base.origin.kind == Origin::Unknown) return {};
      const Value *offVal = def->operands[1];
      std::string offKey;
      if (offVal->defOp && offVal->defOp->opc == Opc::Const) {
        llvm::SmallString<32> s;
        offVal->defOp->constVal.toStringSigned(s);
        offKey = "c" + std::string(s);
      } else {
        offKey = canonicalKey(offVal);
      }
      base.offsetKey = base.offsetKey == "0" ? offKey : base.offsetKey + "+" + offKey;
      return base;
    }
    default:
      return {};
  }
}

// The identity a formal parameter has INSIDE its own function's body. The frontend's -O0 lowering always spills
// every incoming parameter to a fresh local `core.alloca` at function entry (`%v = core.alloca; core.store
// %param, %v`) before any real use -- so the raw BlockArg Value is referenced exactly once (that spill store) and
// every actual use in the function body goes through `core.load %v` instead, which resolveOrigin resolves to
// Origin::Alloca(v), never Origin::Param. A bare `Origin::Param(i)` tag therefore matches nothing when the callee
// is scanned for its own stores/calls on real (frontend-compiled) code -- it only works on hand-written IR that
// skips the spill, which is why this was first caught on brotli's real IR (docs/DESIGN.md Sec.22.331) rather than
// in a hand-written unit test. Fixed by resolving through the spill here, once, when a parameter identity is
// pushed into a callee's worklist item, instead of leaving a Param tag for the callee's own body to never match.
inline Origin paramOriginInCallee(const Function &callee, unsigned paramIndex) {
  Origin fallback;
  fallback.kind = Origin::Param;
  fallback.paramIndex = paramIndex;
  const Block *entry = callee.entry();
  if (!entry || paramIndex >= entry->args.size()) return fallback;
  const Value *arg = entry->args[paramIndex].get();
  for (auto &opPtr : entry->ops) {
    const Op &op = *opPtr;
    if (op.opc != Opc::Store || op.operands.size() < 2 || op.operands[0] != arg) continue;
    const Op *addrDef = op.operands[1]->defOp;
    if (addrDef && addrDef->opc == Opc::Alloca) {
      Origin o;
      o.kind = Origin::Alloca;
      o.allocaOp = addrDef;
      return o;
    }
  }
  return fallback;  // not spilled (e.g. hand-written IR, or an optimised build) -- Param(i) is the real identity
}

}  // namespace detail

// Finds every `core.store` reachable from `anchorFn` (by direct calls, same forward-reachability notion as
// ReachTarget.h's computeTargetDistance) whose address, resolved within its own function, denotes the same
// underlying object and offset as `anchorAddr` (resolved within `anchorFn`).
//
// Identity is threaded through call edges by two rules, both deliberately narrow (no partial-offset arithmetic
// across a call boundary is attempted -- that's a documented limit, not a bug):
//   1. an actual argument resolving to (tracked origin, offset "0") -- the whole object is passed through
//      unchanged -- continues the search into the callee with the SAME offset still being hunted for, now
//      relative to the callee's own formal parameter (the common, dominant real-world shape: a struct pointer
//      threaded through several functions, each doing its own field access locally -- this is exactly how
//      brotli's `BrotliDecoderState* s` is passed through DecodeXxxBlockSwitch -> ...Internal ->
//      DecodeBlockTypeAndLength, Sec.22.322).
//   2. an actual argument resolving to EXACTLY (tracked origin, tracked offset) -- the caller already computed a
//      pointer straight at the target field and handed that off -- continues into the callee hunting for offset
//      "0" relative to its formal parameter (the callee receives a direct pointer to the field).
// Any other partial-offset pass-through is not tracked (bailed on silently -- that call edge is just not
// followed), which only under- not over-reports candidates.
inline std::vector<WriteSite> findWriteSites(const Module &m, const Function &anchorFn, const Value *anchorAddr, unsigned maxHops = 4096) {
  std::vector<WriteSite> out;
  detail::Resolved anchor = detail::resolveOrigin(anchorAddr);
  if (anchor.origin.kind == Origin::Unknown) return out;

  struct WorkItem {
    const Function *fn;
    Origin origin;
    std::string offsetKey;
  };
  std::vector<WorkItem> work{{&anchorFn, anchor.origin, anchor.offsetKey}};
  std::set<std::pair<const Function *, std::string>> seen;

  auto originKey = [](const Origin &o) -> std::string {
    switch (o.kind) {
      case Origin::Alloca: return "A" + std::to_string(reinterpret_cast<uintptr_t>(o.allocaOp));
      case Origin::Param: return "P" + std::to_string(o.paramIndex);
      case Origin::Global: return "G" + std::to_string(reinterpret_cast<uintptr_t>(o.globalOp));
      default: return "?";
    }
  };

  unsigned hops = 0;
  while (!work.empty() && hops++ < maxHops) {
    WorkItem cur = std::move(work.back());
    work.pop_back();
    if (!cur.fn || cur.fn->isDeclaration()) continue;
    if (!seen.insert({cur.fn, originKey(cur.origin) + "@" + cur.offsetKey}).second) continue;

    for (auto &b : cur.fn->blocks) {
      for (auto &opPtr : b->ops) {
        const Op &op = *opPtr;
        if (op.opc == Opc::Store && op.operands.size() >= 2) {
          detail::Resolved r = detail::resolveOrigin(op.operands[1]);
          if (r.origin == cur.origin && r.offsetKey == cur.offsetKey) out.push_back({cur.fn, &op, op.loc});
        } else if (op.opc == Opc::Call) {
          const Function *callee = m.findFunction(op.sym);
          if (!callee || callee->isDeclaration()) continue;
          for (size_t i = 0; i < op.operands.size() && i < callee->paramTys.size(); ++i) {
            detail::Resolved r = detail::resolveOrigin(op.operands[i]);
            if (r.origin != cur.origin) continue;
            Origin po = detail::paramOriginInCallee(*callee, static_cast<unsigned>(i));
            if (r.offsetKey == "0") work.push_back({callee, po, cur.offsetKey});       // rule 1
            else if (r.offsetKey == cur.offsetKey) work.push_back({callee, po, "0"});  // rule 2
          }
        }
      }
    }
  }
  return out;
}

}  // namespace hlir

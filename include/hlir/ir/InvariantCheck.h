// Instrument a loop with a candidate invariant, so that an ordinary analysis decides it.
//
// The transformation is in place and deliberately small (DESIGN.md §22.425 explains why it has to be):
//
//   * a PREHEADER on every edge entering the loop header from outside, which makes the locals the loop
//     WRITES arbitrary and then `core.assume`s the candidate. A pointer among them becomes "its current
//     value plus an arbitrary offset" -- anything else stops it being a pointer, and keeping the object is
//     the assumption C already requires for the loop's own pointer arithmetic to be defined;
//   * the back edge goes to a block that `core.assert`s the candidate and returns.
//
// So one iteration runs from an arbitrary state satisfying the candidate, and the assert fails exactly when
// the candidate is not preserved. Everything BEFORE the loop still runs, which is the point: the pointers
// and struct fields the loop compares against are real objects built by whatever harness drives the entry.
//
// What the verdict then means: the candidate holds on the states REACHABLE FROM THE ENTRY, not on every
// state satisfying it. Weaker than textbook inductiveness, on the same footing as every other HLIR verdict,
// and it carries the entry's assumptions.
//
// `taintLabel` is NOT optional in practice. A `core.nondet` with no taint label is kept fully CONCRETE
// (TaintDomain::nondet), so an untainted havoc gives the loop-carried variable ONE fixed value that the
// search cannot flip -- and if that value fails the loop guard, the loop never runs and every candidate
// comes back "preserved" for a reason that has nothing to do with the candidate. That is exactly what made
// tcpdump's `while (li >= 2)` option walk look like its back edge was unreachable.
//
// Signedness comes from the IR and never from the candidate's text: a name resolves to its `core.alloca`,
// and a comparison takes its signedness from whichever operand the function itself is decisive about. When
// neither is, `signedFallback` picks the reading and `usedSignednessFallback` says so, because the caller
// then has to require BOTH readings -- the over-strict direction, which can cost a rejection but never buy
// a false acceptance.
#pragma once
#include <string>

#include "hlir/ir/IR.h"

namespace hlir {

struct InvariantInstrumentation {
  std::string error;                     // non-empty: nothing was changed
  bool usedSignednessFallback = false;
  const Block *checkBlock = nullptr;     // the back edge's block; "was it reached" is what tells vacuity
  std::string assertMessage;             // the message the assert carries, to recognise the finding
};

// Mutates `m`. `header` is the loop header's block name (no '^').
//
// `assertExpr` defaults to `expr`; giving a DIFFERENT one is what makes a reachability probe possible, and
// that probe is not optional. Assuming the candidate and asserting the same candidate cannot distinguish
// "preserved" from "the back edge was never reached" -- and the obvious probe, assuming an always-false
// candidate, is broken by construction: `core.assume false` kills the path in the preheader, before the
// loop. The probe that works is assume TRUE, assert FALSE: if that assertion does not fire, nothing reaches
// the back edge and every verdict about this loop is vacuous.
InvariantInstrumentation instrumentInvariant(Module &m, const std::string &function, const std::string &header,
                                             const std::string &expr, bool signedFallback = false,
                                             const std::string &assertExpr = "", const std::string &taintLabel = "");

}  // namespace hlir

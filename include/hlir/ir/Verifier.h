// STABLE. Structural + type verifier for `core` modules.
#pragma once
#include "hlir/ir/IR.h"
#include "hlir/support/Diagnostics.h"

namespace hlir {

struct VerifyOptions {
  // Every op that can trigger UB must be dominated by the matching core.check.* (or carry `waived="reason"`).
  // Enabled for modules produced by lowering (DESIGN.md §18.4); off for hand-written fragments.
  bool checkCoverage = false;
};

// Returns true iff no errors were reported.
bool verifyModule(const Module &m, const VerifyOptions &opts, Diagnostics &diags);

// Like `verifyModule`, except the (expensive) per-function structural+type check only runs for
// `m.functions[fromIndex..]` — for when the functions before `fromIndex` already went through a `verifyModule`/
// `verifyNewFunctions` call of their own (e.g. a `--link` program's base parsed+verified once and shared across
// several entries, each then appending and verifying only its own harness; see tools/hlir-scan.cpp and
// docs/DESIGN.md §22.15). The duplicate-function-name check still scans every function (cheap: a set of names,
// not the structural+type work `FuncVerifier` does per function) — a new function colliding with an
// already-verified one is still an error. Returns true iff no errors were reported.
bool verifyNewFunctions(const Module &m, size_t fromIndex, const VerifyOptions &opts, Diagnostics &diags);

}  // namespace hlir

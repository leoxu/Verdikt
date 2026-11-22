// STABLE. Parser for the `core` textual IR.
#pragma once
#include <memory>
#include <string>

#include "hlir/ir/IR.h"
#include "hlir/support/Diagnostics.h"

namespace hlir {

// Returns null (and fills `diags`) on a syntax/structure error. Does not run the verifier.
std::unique_ptr<Module> parseModule(const std::string &text, const std::string &bufferName, Diagnostics &diags,
                                    unsigned ptrWidth = 64);

// Parses `text` and appends its functions/declarations into an already-parsed `mod`, reusing its Context (so the
// new functions' Type* pointers are interned in the same table as the existing ones, not a disjoint copy from a
// second Module). Returns false (and fills `diags`) on a syntax/structure error; `mod` may hold a partial set of
// newly-added functions in that case, same as a `parseModule` caller discarding a null result.
//
// For appending a small harness onto an already-parsed large program: re-parsing `baseText + harness` as one string
// re-derives the same `mod.functions` the first parse already produced, at the cost of walking the (potentially huge)
// base text a second time. A duplicate `core.declare` for a function `mod` already defines with a real body is
// harmless — `Module::findFunction` returns the first match by iteration order, and the real definition was added
// first — this is the same tolerance the single-string-concatenation path already relied on.
bool parseModuleInto(Module &mod, const std::string &text, const std::string &bufferName, Diagnostics &diags);

}  // namespace hlir

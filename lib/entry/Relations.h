// Private. Compiles a relation string ("len >= 0 => (size_t)len <= size(src)") to a Bool term over the entry's inputs.
// All values are normalised to 64 bits (sign- or zero-extended according to their C type), comparisons are signed only
// when both sides are signed, like C's usual arithmetic conversions.
#pragma once
#include <string>

#include "hlir/entry/InitPlan.h"

namespace hlir::entry {

// Resolves a C-like type name to width/signedness.
bool lookupTypeName(const std::string &name, unsigned &width, bool &isSigned);

// Returns nullptr and sets `err` on failure.
smt::TermRef compileRelation(const std::string &text, const std::vector<PlannedParam> &params, smt::TermManager &tm,
                             std::string &err);

}  // namespace hlir::entry

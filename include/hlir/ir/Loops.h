// Natural loops of a `core` function.
//
// An edge u -> v is a BACK EDGE iff v DOMINATES u, and the loop's body is v plus every block that reaches u
// without passing through v. Nothing cheaper is correct: "a branch to an earlier block in the list" is only
// valid if the block list is in reverse postorder, which the lowering does not promise. On tcpdump's
// `clnp_print` that shortcut reported 61 loops, nearly all of them if-join blocks whose predecessors
// happened to be emitted later -- and for anything that then tries to PROVE something about each "loop",
// that error is in the worst direction: a property of a non-loop is vacuously true and counts as a success.
#pragma once
#include <cstddef>
#include <set>
#include <string>
#include <vector>

#include "hlir/ir/IR.h"

namespace hlir {

struct Loop {
  const Block *header = nullptr;
  std::set<const Block *> body;       // includes the header
  std::set<const Block *> latches;    // blocks in `body` with an edge back to `header`
  std::string file;                   // first source line of the body, for reporting
  unsigned line = 0;
  size_t calls = 0, checks = 0;       // core.call / core.check.* ops in the body
  bool nested = false;                // the header lies inside another loop's body
};

// Every natural loop of `f`, headers in block order. A `goto` into the middle of a loop would make the body
// too large, never make a loop disappear.
std::vector<Loop> loopsOf(const Function &f);

}  // namespace hlir

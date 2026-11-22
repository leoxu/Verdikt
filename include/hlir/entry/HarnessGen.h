// STABLE. Generates the entry harness (DESIGN.md §21.9) as ordinary `core` text: nondet inputs, the named legality
// assumptions, parameter objects, and the call. Because it is plain core, the interpreter, symbolic execution and replay
// need no special support: run `__hlir_entry_<f>` like any other function. Append the text to the module's text (or
// parse it separately) before use.
#pragma once
#include <map>
#include <string>

#include "hlir/entry/InitPlan.h"

namespace hlir::entry {

std::string harnessName(const InitPlan &plan);
// `paramObjId`, when given, is filled with each non-scalar parameter's runtime memory-object id: Memory numbers
// objects in allocation order from 1 and the harness allocates before the entry runs, so this is exactly the `<id>`
// in the `in.o<id>+<off>` names that witness bytes are keyed by. It cannot be guessed from the parameter's position,
// because a parameter whose pointer fields are synthesised allocates sub-objects of its own in between (DESIGN.md
// §22.351: that guess silently attributed one parameter's bytes to another, so a confirmed finding could print a
// witness that does not reach it).
std::string generateHarness(const InitPlan &plan, std::map<std::string, unsigned> *paramObjId = nullptr);

}  // namespace hlir::entry

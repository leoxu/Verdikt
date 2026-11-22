// Linking of lowered units: merges the `core` modules of several C files into one program (DESIGN.md §9, cross-file calls).
// Pure text logic: no clang and no IR dependency. The frontend reports which symbols have internal linkage in a unit
// (`static` functions/variables, string literals); same-named internal symbols of different units are renamed apart
// (`name.u<unit>`), declarations are resolved against definitions, and globals that several units mention get the largest
// size any of them gives (an `extern int a[];` next to the real definition).
#pragma once
#include <map>
#include <set>
#include <string>
#include <vector>

#include "hlir/support/IndirectCall.h"

namespace hlir::link {

struct Unit {
  std::string name;                          // file name, for messages
  std::string core;                          // the unit's `core` text
  std::vector<std::string> internalTokens;   // symbols (no '@') with internal linkage in this unit
  // functions whose address is taken in this unit (name, core signature `(ptr, i32) -> i32`): indirect-call candidates of the program
  std::vector<std::pair<std::string, std::string>> addrTaken;
  // name -> C type key (frontend::LowerResult::addrTakenCTypes) of the addrTaken functions that can only be called through
  // their own C type; a function missing here is a candidate of every call with its core signature
  std::map<std::string, std::string> addrTakenCTypes;
  // dispatcher name -> C type key of the calls through it (frontend::LowerResult::indirectCallCTypes)
  std::map<std::string, std::string> indirectCallCTypes;
  // symbols this unit asks dlsym for by string literal (frontend::LowerResult::dlsymNames)
  std::set<std::string> dlsymNames;
};

using hlir::cTypesCompatible;  // hlir/support/IndirectCall.h
using hlir::indirectTypeTag;

struct Result {
  std::string core;                          // the linked module
  // internal symbols that had to be renamed: renames[unit][old] = new
  std::vector<std::map<std::string, std::string>> renames;
  std::vector<std::string> notes;            // duplicate definitions, stubs added, ...
  std::vector<std::string> unresolved;       // functions that are called/declared but defined in no unit
  // indirect-call dispatchers generated: `@__hlir_indirect.<sig>` -> the (linked) names of the functions it can reach
  std::map<std::string, std::vector<std::string>> dispatchers;
  // `dlsym(h, "name")` sites: the names that resolved to a function of the linked program, and the names that did not
  // (no unit defines them -- `@__hlir_dlsym.<name>` is left external and the call through the result stays opaque).
  std::vector<std::string> dlsymResolved, dlsymUnresolved;
  // `exposed` names that were honoured (kept their name so other units bind to them), and those that were not because
  // more than one unit has an internal symbol of that name.
  std::vector<std::string> exposeApplied, exposeAmbiguous;
};

// `modelDefs`: names `core.func @name {` defined in ModelDB text appended after linking (libc.core/linux.core/...). An
// internal symbol colliding by plain name with one of these (e.g. a kernel header's own real, non-`__always_inline`
// `static inline` fallback body compiled for real, happening to be named the same as a generic libc model function such
// as `isdigit`) is renamed apart exactly like a same-named internal symbol of another unit — the model text is appended
// as plain text after linking and is otherwise invisible to this collision check.
// `exposed`: base names the caller asserts should bind ACROSS units even though they have internal (`static`) linkage.
// This is a deliberate departure from C linkage, and it exists because a harness cannot otherwise reach a `static`
// function at all: the harness's own `extern` declaration makes the name "seen" in a second unit, which is exactly the
// condition that triggers the rename, so the call binds to nothing and the target is never analysed. A large share of
// defects -- CVE-2025-24928's `xmlSnprintfElements` among them -- live in static helpers.
//
// It is honoured only when EXACTLY ONE unit has that name as an internal symbol. With two, there are two distinct
// entities and no answer to "which one did you mean"; the name is renamed as usual and the caller is told through
// `exposeAmbiguous` rather than being given an arbitrary pick.
Result linkUnits(const std::vector<Unit> &units, const std::set<std::string> &modelDefs = {},
                 const std::set<std::string> &exposed = {});

// Names of `core.func @name {` definitions (bodies, not bare `core.declare`s) in a `core` text blob — used to build the
// `modelDefs` set above from ModelDB text (libc.core/linux.core/...) before it is appended to a linked module.
std::set<std::string> definedFunctionNames(const std::string &text);

// Indirect calls: the frontend lowers `fp(args)` in link mode to `core.call @__hlir_indirect.<sig>(fp, args)` (declared). The linker
// defines each such function as a pointer-comparison chain over the address-taken functions of ALL units with that signature; a
// pointer that matches none is a function of some module we do not have: `@__hlir_unknown_indirect.<sig>(args)` (external, opaque).

// The name `fn` of unit `unit` has in the linked module.
std::string linkedName(const Result &r, size_t unit, const std::string &fn);

}  // namespace hlir::link

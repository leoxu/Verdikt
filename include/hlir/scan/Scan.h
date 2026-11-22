// Entry discovery and entry-spec generation for `hlir-scan` (DESIGN.md §21: "auto-discovery fills the same structures
// as a hand-written spec"). Pure logic over frontend::FunctionInfo, no clang and no analysis engine: the generated
// YAML is exactly what a user would write, so it can be dumped, edited and fed back to hlir-taint.
#pragma once
#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include <set>

#include "hlir/frontend/Frontend.h"
#include "hlir/iface/Interface.h"
#include "hlir/scan/StructRanges.h"

namespace hlir::scan {

enum class EntryMode {
  Roots,     // not static and not called from the same file, plus address-taken functions (handler tables, callbacks)
  Exported,  // every non-static function, plus address-taken functions
  All,       // every function defined in the file
  // Only the handlers the code registers in a slot of a MODELLED dispatch interface. The other three modes answer
  // "which functions could be called from outside this file", which for a kernel module or a resmgr over-answers
  // badly: 336 of round 42's 499 confirmed findings (67%) came from internal helpers that happened to look like
  // roots. The attack surface of these targets is not a guess -- it is `file_operations`' nine slots, resmgr's
  // io_funcs table, a wayland request vtable -- so it is read off the interface model instead (DESIGN.md §22.360).
  Iface,
};

struct Options {
  EntryMode mode = EntryMode::Roots;
  std::string label = "network";     // taint label of the attacker-controlled parameters
  std::string only, skip;            // ECMAScript regexes on the function name (empty = no filter)
  bool includeNoArg = false;         // functions without attacker-controlled parameters are skipped by default
  bool hostile = false;              // no length<->buffer relations: a length parameter is independent of its buffer's size
  uint64_t bufMax = 256;             // upper bound of a byte-buffer parameter (the lower bound is 1)
  uint64_t maxObj = 4096;            // default max_obj of the generated specs; raised (up to maxObjLimit) when a parameter or field object needs more
  uint64_t maxObjLimit = 1u << 20;   // objects bigger than this are not created at all
  unsigned maxFields = 128;          // objects created for pointer fields per parameter (shallow fields first; the rest stay NULL)
  bool userDataZero = false;         // user-data state of handle parameters is zero (default: attacker-influenced, an over-approximation)
  bool noPtrFields = false;          // leave pointer fields of input structs zero (the old behaviour)
  // true for `--linux` scans: Linux syscall arguments declared `struct sockaddr *` are, by a kernel-wide
  // convention the kernel's own comments document (e.g. net/unix/af_unix.c's unix_mkname_bsd), always backed by
  // a real allocation of at least sizeof(struct sockaddr_storage) bytes regardless of the declared pointee type
  // -- isSockaddrLike()'s synthesized size uses this as its lower bound (not just sizeof(declared struct)) only
  // when this is true, since that guarantee does not generally hold for arbitrary userspace code taking a
  // sockaddr-shaped pointer (DESIGN.md §22.144: raising the bound unconditionally would trade one direction of
  // false positive for the opposite direction of false negative in userspace scans).
  bool linuxApi = false;
  // Whole-program bounds the code asserts about its own integer members (frontend::LowerResult::fieldAsserts,
  // unioned over every --link unit and keyed by ScalarFieldInfo::fieldKey). They become `where:` preconditions on
  // the parameter objects the harness synthesises -- the invariant a kernel writes down in `snd_BUG_ON(...)` is one
  // no name heuristic can reach (DESIGN.md §22.358). Null for a non-link scan.
  const std::map<std::string, frontend::AssertedBound> *assertBounds = nullptr;
  // parameters whose name matches are kernel/driver context objects, not attacker input: pointee initialised legally,
  // not tainted (e.g. <driver>'s `g`, QNX's `ctp`/`ocb`)
  std::string ctxNames = "^(g|ctx|ctp|dev|device|ocb|self|priv|drv|handle|state|this|gpu|vm|ch|tsg|as|mod|sess)$";
  // EntryMode::Iface only: the dispatch interfaces whose slots are the attack surface, and the registrations the
  // frontend found while lowering (function name -> {"file_operations#unlocked_ioctl", ...}; see
  // frontend::LowerResult::vtableBindings, whose keys hlir-scan has already rewritten to post-link names). Both
  // null in the other modes, which never consult them.
  // `init:` -- the project's own initialiser(s), run before every entry (DESIGN.md §22.368, Spec.h InitSpec).
  // Emitted verbatim into each generated spec so it can be read, diffed and overridden by hand like everything
  // else the generator decides. Empty = none, which is today's behaviour: the globals a handler reads hold their
  // static initialisers, a state it is never really called in.
  std::vector<std::string> initFunctions;
  const iface::InterfaceFile *interfaces = nullptr;
  // Declared per-struct field ranges (models/structs/*.yaml, DESIGN.md §22.480): what the mount path or the
  // subsystem validated about an object the handler is HANDED, which the synthesised object otherwise knows
  // nothing about. A narrowing, named in every entry it touches.
  const structranges::StructRanges *structRanges = nullptr;
  const std::map<std::string, std::set<std::string>> *vtableBindings = nullptr;
  // Per-TABLE registrations (frontend::LowerResult::vtableInstances, post-link names). `vtableBindings` says a
  // function is in some table's slot; this says WHICH table, which is the one fact needed to pair a handler with
  // the constructor of its own session -- a module registers many tables of one type (DESIGN.md §22.371).
  const std::map<std::string, frontend::VtableInstance> *vtableInstances = nullptr;
};

// The modelled slot a function is registered in, as `<interface>.<slot>` ("" when it is registered nowhere, or only
// in tables no interface model describes). A function bound to several modelled slots reports the first in sorted
// order, so the answer does not depend on map iteration order.
std::string ifaceSlotOf(const std::string &function, const Options &opt);

// The same lookup, handing back the contract itself: the slot the function is registered in, and (when `model` is
// non-null) the interface that slot belongs to. Null when the function is registered in no modelled slot.
const iface::Slot *ifaceSlotFor(const std::string &function, const Options &opt, const iface::InterfaceModel **model = nullptr);

struct Entry {
  std::string function;
  unsigned line = 0;
  std::string why;                   // root | exported | callback | all
  bool lowered = true;               // false: the function itself could not be lowered
  std::string specText;              // YAML for hlir-taint / the entry module
  std::vector<std::string> notes;    // modelling decisions the user may want to review
  std::string skipReason;            // non-empty: discovered but not analysable (e.g. nothing to taint)
};

// All entries of one translation unit, in source order; `skipReason` explains the ones that should not be run.
std::vector<Entry> discover(const std::vector<frontend::FunctionInfo> &fns, const Options &opt);

// A preconditions file may name struct members instead of byte offsets:  where: [ { field: lastErr, range: [-9, 0] } ].
// Rewrites each `field: NAME` (flow style, on its own line) into `offset: N, type: T` using the member table of the
// function's pointer parameter, keeping every line number. false + err when a name is unknown or not in flow style.
bool resolvePreconditionFields(const std::string &text, const std::string &path, const std::vector<frontend::FunctionInfo> &fns, std::string &out, std::string &err);

// Spec for one function (also used for --entries given by name).
// `all` = every function of the same translation unit (the possible targets of function-pointer fields).
Entry makeEntry(const frontend::FunctionInfo &fn, const Options &opt, const std::vector<frontend::FunctionInfo> &all = {});

}  // namespace hlir::scan

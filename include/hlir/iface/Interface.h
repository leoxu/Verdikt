// The call contract of a well-known dispatch interface: what a handler hanging off `file_operations`,
// `resmgr_io_funcs_t` or a wayland request vtable is actually handed (DESIGN.md §22.357).
//
// Why this layer exists: the scanner's generic parameter synthesis knows a handler's TYPES and nothing else, so it
// invents a `struct file` field by field and marks the whole thing attacker-controlled. Neither is true -- the file
// was built by the kernel, its `private_data` by the driver's own `.open`, and only `cmd`/`arg`/the user buffer are
// the attacker's. That gap is the measured dominant source of false findings across 42 kernel rounds, and unlike
// the per-struct heuristics (sibling counts, base/cursor/limit) it cannot be recovered from declarations: it lives
// in an interface contract that is written down once and reused by every driver.
//
// This is NOT a behaviour model. `models/*.core` replaces a FUNCTION BODY; an interface model replaces the
// PARAMETER SYNTHESIS of a handler. The two are loaded from different places on purpose.
//
// The model is consumed by the spec generator (lib/scan), which lowers it into the ordinary entry-spec DSL
// (`taint:`, `size:`, `where:`, `from_call:`). Nothing here reaches the engine directly, so a generated spec can be
// read, diffed and overridden by hand -- and every narrowing the contract asserts is reported as an assumption.
#pragma once
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "hlir/support/Diagnostics.h"

namespace hlir::iface {

// Closed vocabulary. Adding a role is a deliberate act: an open-ended set degenerates into writing a rule per
// function, which is exactly what this layer exists to avoid.
enum class Role {
  Session,      // the object the ctor slot created: synthesised by CALLING that slot, never field by field
  SessionOut,   // the ctor slot's output parameter
  KernelOwned,  // built by the kernel before the handler runs: taint none, constructor invariants assumed
  UserAddr,     // a userspace address: passing it on is fine, DEREFERENCING it directly is a finding
  // Attacker-controlled data. On a scalar that is the value itself; on a POINTER it is a legal, kernel-side object
  // whose CONTENTS are the attacker's -- the shape a dispatcher produces when it has already done the
  // copy_from_user for its handlers (ALSA's seq `ioctl_handler.func(client, &buf)`), as opposed to UserAddr, where
  // the pointer itself belongs to another address space. This is what generic synthesis does for a non-context
  // pointer anyway, so `value` on a pointer narrows nothing; it states that the widest model is the right one.
  Value,
  Out,          // written by the callee
};

enum class Dir { In, Out, InOut };

struct ParamContract {
  std::string name;
  Role role = Role::Value;
  Dir dir = Dir::In;
  std::string sizeFrom;  // this buffer's length is the value of that parameter ("" = none)
  // `size: { min, max }` -- how many bytes the object behind this pointer really has, when its DECLARED type does
  // not say. The motivating case is a QNX resmgr message: `io_devctl_t *msg` is a 16-byte union, but what the
  // handler is handed is the receive buffer (`resmgr_attr.msg_max_size` bytes) whose first 16 bytes happen to be
  // that union and whose tail is the request payload -- `_DEVCTL_DATA(msg->i)` is literally `(char *)&msg->i + 16`.
  // Sized by its type, every payload access is out of bounds before the handler has done anything, which is a fact
  // about the declaration and not about the code.
  //
  // This is the one place in the contract vocabulary that can WIDEN rather than narrow (a `max` above
  // `sizeof(*p)`), so it is held to the same discipline as every narrowing: the spec generator names it in
  // `assumptions` whenever it departs from the declared size. `size_from` stays the right key when a sibling
  // PARAMETER carries the length; this one is for a length the interface fixes and the signature cannot express.
  std::optional<uint64_t> sizeMin, sizeMax;
  unsigned line = 0;
};

// One slot of the interface: a named field of the vtable struct, and what its handler is handed.
struct Slot {
  std::string name;                    // the vtable field (`unlocked_ioctl`)
  std::vector<ParamContract> params;   // in the handler's parameter order
  std::string success;                 // a condition the prologue/ctor result must satisfy ("" = none)
  unsigned line = 0;
};

struct InterfaceModel {
  std::string name;                    // `file_operations`
  std::string structTag;               // the C struct tag whose initialisers are instances of this interface
  std::string label;                   // default taint label for the attacker-controlled parameters
  // The functions that WOULD have to run before any slot for the module's globals to hold the values a handler
  // really sees: `module_init` allocates them and registers the vtable, and until it has run every global still
  // holds its static initialiser (usually zero), which is a state no handler is ever called in.
  //
  // NOT EXECUTED. This field is parsed, carried, and named in the report -- nothing runs it. An earlier version of
  // this comment described budget accounting and a "dropped when it does not pay for itself" heuristic; none of
  // that exists, and a key whose comment promises behaviour it does not have is worse than no key at all, because
  // it makes a reader of the yaml believe initialisation happened (DESIGN.md §22.368 §1). What the engine really
  // does is stated by the `global_initial_value` assumption G1 emits (§22.362, lib/driver/Pipeline.cpp): "module_init
  // and the other internal initialisers are not executed, and the branch is taken concretely without a fork, so the
  // opposite edge is not explored either".
  //
  // Executing it is designed in DESIGN.md §22.368 (all-or-nothing, stop functions, backtrack-and-flip past exit
  // paths, snapshot reuse) and not yet implemented. Until it is, declaring a prologue has exactly one effect: the
  // entries of that interface carry an assumption saying it was declared and not run.
  std::vector<std::string> prologue;
  // The session object threaded through every slot, and the slots that create and release it.
  std::string sessionParam, sessionCtor, sessionDtor, sessionHandle;
  // `attacker_in_body: true` -- the attacker data of THIS interface does not arrive through any parameter.
  // A filesystem is handed the VFS's own object graph (super_block, inode, dentry, folio); the mounted image,
  // which is the attack, arrives mid-body through `sb_bread()`, whose model makes `bh->b_data` attacker-
  // controlled (DESIGN.md §22.475). Without this flag every such slot is skipped by the `tainted == 0` rule as
  // "no attacker-controlled parameter", which was true and beside the point: on fs/isofs it skipped 20 of 25
  // registrations, `zisofs_read_folio` and `rock_ridge_symlink_read_folio` among them (§22.477).
  //
  // It only suppresses that skip. It grants no taint and narrows nothing, and every entry kept by it says so.
  bool attackerInBody = false;
  std::vector<Slot> slots;
  std::string sequence;                // the legal call order, for the sequence harness (not used by Phase A)
  unsigned line = 0;

  const Slot *slot(const std::string &n) const {
    for (auto &s : slots)
      if (s.name == n) return &s;
    return nullptr;
  }
};

struct InterfaceFile {
  std::vector<InterfaceModel> interfaces;

  const InterfaceModel *byStruct(const std::string &tag) const {
    for (auto &i : interfaces)
      if (i.structTag == tag) return &i;
    return nullptr;
  }
};

// Reads one `models/interfaces/*.yaml`. `file` is used for diagnostics only.
bool parseInterfaceFile(const std::string &text, const std::string &file, InterfaceFile &out, Diagnostics &diags);

const char *roleName(Role r);

}  // namespace hlir::iface

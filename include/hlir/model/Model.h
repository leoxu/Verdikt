// STABLE. ModelDB: data-driven semantics of functions that have no body in the analysed module (libc, system calls,
// third-party libraries) — DESIGN.md §9.2, §20.4/20.8. A model says what a call does to values, memory and taint:
// what it returns, which memory it fills with attacker-controlled input, which memory it copies or fills, how taint flows
// through it (or is cleared), and which arguments are security sinks. The execution engines interpret these records, so
// the same model works for the interpreter, symbolic execution and the taint-selective engine.
//
// YAML form (see models/libc.yaml):
//   models:
//     - function: recv
//       returns: { nondet: { min: -1, max: arg2, default: arg2, tainted: network } }   # also: value, arg, null, alloc, strlen
//       source:  [ { label: network, ptr: arg1, size: ret } ]
//     - function: strcpy
//       copy:    [ { dst: arg0, src: arg1, size: "strlen(arg1)+1" } ]
//       returns: { arg: 0 }
//     - function: atoi
//       flow:    [ { from: arg0_pointee, to: ret, size: "strlen(arg0)+1" } ]
//     - function: iofunc_attr_init                                  # writes the caller's struct; we do not model what into
//       fills_unknown: [ { ptr: arg0, size: 72 } ]
//     - function: html_escape
//       flow:    [ { clear: ret_pointee } ]
//     - function: system
//       sink:    [ { kind: command_exec, arg: arg0_pointee } ]
//     - function: RtosCWrapStopOnFailedProgrammingCheck
//       noreturn: true            # the path ends at the call (it is not a bug and nothing after it is analysed)
// References: argK (the value), argK_pointee (memory the pointer argument points to), ret, or an integer.
// Sizes: an integer, argK, ret (negative results count as 0), strlen(argK), strlen(argK)+1.
#pragma once
#include <cstdint>
#include <map>
#include <memory>
#include <regex>
#include <optional>
#include <string>
#include <vector>

#include "hlir/support/Diagnostics.h"

namespace hlir::model {

struct Ref {
  enum Kind { None, Arg, ArgPointee, Ret, RetPointee, Const } kind = None;
  unsigned index = 0;     // Arg / ArgPointee
  int64_t value = 0;      // Const
};

struct Size {
  enum Kind { None, Const, Arg, Ret, Strlen, StrlenPlus1 } kind = None;
  unsigned index = 0;     // Arg / Strlen: which argument
  uint64_t value = 0;     // Const
};

struct ReturnSpec {
  enum Kind { Unspecified, Nondet, Const, Arg, Null, Alloc, Strlen, Opaque } kind = Unspecified;  // Opaque: unknown function — an unconstrained untainted integer, or a possibly-NULL 4096-byte zeroed object for pointers
  int64_t value = 0;                 // Const
  unsigned arg = 0;                  // Arg / Strlen (the string argument)
  std::optional<Ref> min, max;       // Nondet: inclusive signed bounds (Const or Arg)
  std::optional<Ref> dflt;           // Nondet: value used by concolic runs that have no seed for it (Const or Arg); default 0
  std::string taintLabel;            // Nondet: non-empty = the value is attacker controlled
  Size allocSize;                    // Alloc
  bool zeroed = false, mayFail = true;
};

struct SourceSpec { std::string label; Ref ptr; Size size; };            // writes attacker-controlled bytes (ptr: argK, or ret for a returned buffer)
// Writes bytes we do not know and nobody controls (DESIGN.md §22.377). The third answer to "what did this external
// do to my buffer", next to `source` (the attacker wrote it) and `fill` (it holds this exact byte): the real
// library wrote SOMETHING there, and the analysis has no idea what. The bytes are symbolic, so they decide no
// branch concretely, and they carry the reserved harness label, so a finding decided only by them is the
// analysis's own invention and is reported as such -- exactly like the synthesis frontier (§22.364). Saying
// nothing instead (the opaque fallback) claims the buffer still holds whatever it held, which is the "the attr
// stayed zero" failure that made a whole QNX scan vacuously safe.
struct FillUnknownSpec { Ref ptr; Size size; };
// The external's returned object has a POINTER FIELD, and what it points at is the real payload
// (DESIGN.md §22.475). `source`/`fills_unknown` write the bytes of an object we already have; this writes a
// pointer INTO one, to a fresh object of a stated size whose bytes are the attacker's.
//
// Without it a kernel filesystem cannot be scanned at all: `sb_bread()` returns a `struct buffer_head *` and
// every on-disk byte is reached through `bh->b_data`. As an opaque external the buffer_head is a zeroed blob,
// `b_data` reads NULL, and the parser either dies on a synthesised null_deref or never runs -- measured on
// fs/isofs, where `isofs_readdir` reached 1% of its blocks, `rock_ridge_symlink_read_folio` 0%, and 8 of 19
// entries were vacuously safe with `checks queried == 0`.
//
// The size is STATED, not invented. That is the whole difference from the synthesis frontier (§22.364), which
// also materialises an object on demand but has to make its size up and therefore sets `sizeInvented` and
// suppresses every bounds verdict about it. A disk block is 512..4096 real bytes; saying so is what makes an
// overrun of it a finding instead of an artefact, and that is the only reason this mechanism is worth having.
struct PointsToSpec {
  Ref base;                 // Ret or Arg: the object that HOLDS the pointer field
  uint64_t offset = 0;      // byte offset of the pointer field inside that object
  Size size;                // size of the object the field is made to point to
  std::string label;        // non-empty: the pointee's bytes are attacker-controlled with this label
  bool unknown = false;     // instead: bytes nobody controls (fills_unknown semantics)
  bool zeroed = false;      // neither: a zeroed object (the callee gave us a blank buffer)
};
struct CopySpec { Ref dst, src; Size size; };                           // memcpy semantics (values and taint)
struct FillSpec { Ref ptr; Ref value; Size size; };                     // memset semantics
struct FlowSpec {                                                       // taint-only data flow
  Ref from, to;
  Size size;                                                            // bytes of pointee operands (default: 1 byte / the value)
  bool clear = false;                                                   // sanitizer: remove taint from `to`
};
struct SinkSpec { std::string kind; Ref arg; };                         // tainted data reaching `arg` is a finding

struct CallModel {
  std::string function;
  ReturnSpec ret;
  std::vector<SourceSpec> sources;
  std::vector<CopySpec> copies;
  std::vector<FillSpec> fills;
  std::vector<FillUnknownSpec> fillsUnknown;
  std::vector<PointsToSpec> pointsTo;
  std::vector<FlowSpec> flows;
  std::vector<SinkSpec> sinks;
  bool noreturn = false;             // `noreturn: true`: the call never returns (abort, exit, a platform stop-on-failed-check): the path ends there. Implies override
  bool overrideBody = false;         // `override: true`: use this model even if the module defines a body for the function (header inlines of an API)
  std::string file;
  unsigned line = 0;
};

// A project's own statement about the externals it calls (DESIGN.md §22.379): `--externs <project>/externs.yaml`.
//
// It exists because of a distinction the report could not previously make. "This external has no model" covers
// two very different situations: one nobody has looked at yet, and one somebody looked at and judged not to
// matter. Lumped together, the first hides inside the second -- the list is long, everybody stops reading it, and
// the one entry that would have changed a verdict goes unnoticed. A skip is a CLAIM about the program ("this
// function contributes nothing to the state the entries read"), so it is written down, with its reason, by the
// person making it, and the report prints it as a decision rather than as an omission.
//
// YAML form:
//   argv: [ io-<driver>, -c, "0", -l, /proc/boot/libnvgpio-hal.so ]   # how the program is really started
//   models: [ ../../models/qnx.yaml ]      # model documents, resolved relative to THIS file
//   skip:
//     - function: NvOsDebugPrintStr
//       reason: logging; writes nothing the caller owns
struct ExternsFile {
  struct Skip { std::string function, reason; unsigned line = 0; };
  std::vector<std::string> modelPaths;  // already resolved against the externs file's own directory
  std::vector<Skip> skips;
  // The command line the program is really started with, `argv[0]` first (DESIGN.md §22.380). An initialiser that
  // is `main` reads it, and with no statement here the harness can only invent one -- which it did, as a single
  // program name and no options, i.e. the claim "this program is started with no arguments". For anything that
  // requires an option that is false, and it was false silently: a resource manager whose `-c` is mandatory
  // returned at its first check and its whole initialiser was skipped. This is not a guess a tool can make; it is
  // a fact about how the program is launched, so the project states it, next to the other facts in this file.
  std::vector<std::string> argv;
  std::string path;
};
// Parses one externs document. `path` is used for diagnostics and to resolve the model paths. Errors leave `out`
// untouched and return false.
bool loadExterns(const std::string &yamlText, const std::string &path, ExternsFile &out, Diagnostics &diags);

// What the engines consume: a lookup by function name. Other providers (an in-memory table, a federated DB) can replace
// ModelDB without touching the engines.
class ModelProvider {
 public:
  virtual ~ModelProvider() = default;
  virtual const CallModel *lookup(const std::string &function) const = 0;
  // Untrusted API (a compromised component): a function without an explicit model whose name matches is hostile. `label` is the taint
  // label of everything it returns or writes, `outMax` the largest object (bytes) whose contents it may overwrite through a pointer
  // argument and the size of the object a returned pointer points to. See ModelDB::setUntrusted.
  virtual bool untrusted(const std::string &, std::string &, unsigned &) const { return false; }
};

class ModelDB final : public ModelProvider {
 public:
  // Adds the models of one YAML document. Errors (with file:line) leave the DB unchanged.
  bool load(const std::string &yamlText, const std::string &path, Diagnostics &diags);
  const CallModel *lookup(const std::string &function) const override;
  bool has(const std::string &function) const { return models_.count(function) != 0; }  // a real model, ignoring the fallback
  // Functions without a model get the "opaque" model: they return an arbitrary untainted value and have no effect on
  // memory or taint. Unsound for functions that do write through their arguments; the pipeline lists the affected
  // functions in the report's assumptions.
  void setOpaqueFallback(bool on) { opaque_ = on; }
  // Threat model "the component behind these functions is compromised" (e.g. the GPU driver core below a server): calls to functions that
  // have no body and no explicit model, and whose name matches `pattern` (ECMAScript, searched), return a fully attacker-controlled value
  // (labelled `label`), a returned pointer is NULL or a `outMax`-byte object with attacker-controlled bytes, and every pointer argument to a
  // non-const object of at most `outMax` bytes has its contents overwritten with attacker-controlled bytes (a hostile callee may write
  // through any out-parameter). Larger objects (the callee's own state is reached through a big struct) are not modified.
  bool setUntrusted(const std::string &pattern, const std::string &label, unsigned outMax, std::string &err);
  bool untrusted(const std::string &function, std::string &label, unsigned &outMax) const override;
  size_t size() const { return models_.size(); }
  const std::map<std::string, CallModel> &all() const { return models_; }

 private:
  std::map<std::string, CallModel> models_;
  bool opaque_ = false;
  std::shared_ptr<std::regex> utRe_;
  std::string utLabel_ = "untrusted";
  unsigned utOut_ = 256;
  mutable std::map<std::string, bool> utCache_;
  CallModel opaqueModel_ = [] { CallModel m; m.function = "<opaque>"; m.ret.kind = ReturnSpec::Opaque; return m; }();
};

}  // namespace hlir::model

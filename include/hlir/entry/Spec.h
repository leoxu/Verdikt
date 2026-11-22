// STABLE. Taint entry specification (DESIGN.md §21.2): which functions are analysis entry points, which of their
// parameters the attacker controls, and the legal value domain of each. The on-disk form is YAML (a subset parsed
// in-tree); other front ends (source annotations, auto-discovery) can fill the same structures.
#pragma once
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "hlir/support/Diagnostics.h"

namespace hlir::entry {

// A restriction on a value of a given integer type: a range, a set, or one value.
struct BoundSpec {
  std::string type;                  // int32_t, uint8_t, size_t, ... (width and signedness of the value)
  std::optional<int64_t> lo, hi;
  std::vector<int64_t> enumValues;
  std::optional<int64_t> value;
  unsigned line = 0;
  std::string file;                  // the file the constraint was written in ("" = the entry spec itself)
};
// `elements`: every element of the integer array a pointer parameter points to satisfies the bound (only the first `count`
// elements when `count` names a parameter or is a number; at most as many as fit in the object).
struct ElementsSpec : BoundSpec { std::string count; };
// `where`: the integer at a byte offset of the pointee object (a struct member such as `lastErr`) satisfies the bound.
struct WhereSpec : BoundSpec { uint64_t offset = 0; };

// A pointer stored inside the object a pointer parameter points to: the harness allocates a legal object for it and
// stores its address at `offset`, so code that follows pointer fields of its input (ctx->ops->fn, req->buf) runs on valid
// memory instead of dereferencing NULL. `funcptr` fields hold the address of one of `targets` (any of them). `self` fields
// point back into the object that holds them (at byte `target`): the next/prev links of an empty intrusive list head.
struct FieldSpec {
  uint64_t offset = 0;
  std::string kind = "buffer";       // buffer | funcptr | self
  uint64_t at = 0;                   // buffer: the stored pointer is the object's address + at (container_of: it points at an embedded member)
  uint64_t target = 0;               // self: offset (inside the holding object) the pointer points to
  std::string taint = "none";        // none | pointee: attacker-controlled content of the pointed-to object
  // What the bytes of the pointed-to object ARE before anything writes them (DESIGN.md §22.381).
  //   zero     a concrete zero fill -- the default, and what every synthesised object was before §22.381
  //   unknown  symbolic and harness-labelled: nobody knows what is in there, so every field reads as a free
  //            value. NOT attacker data: a finding that rests only on such a byte is `harness_only`, exactly
  //            like one resting on the synthesis frontier, because it is the same kind of invention.
  // `zero` is a NARROWING (a real driver-built object is not full of zeroes, and a module's own validity gate
  // -- `attr->magic == MAGIC` -- can then never pass); `unknown` is a WIDENING (the object can be in states its
  // constructor could never build). Both are named in the report's assumptions; neither is silent.
  std::string content;               // "" = unstated (inherit from the parent object, else zero) | zero | unknown
  std::optional<uint64_t> sizeMin, sizeMax;
  // buffer: instead of a free/fixed size (sizeMin/sizeMax), the object's real size is read from an integer sibling
  // field at this byte offset in the SAME parent object (`size: {from_field: {offset: ..., type: ...}}`) -- the
  // common "pointer + length" struct idiom (e.g. `struct el { uint8_t *data; size_t len; }`), where independently
  // synthesising `data`'s size and `len` lets the harness produce an object whose real constructor could never
  // build (see DESIGN.md's relations-DSL-gap root-cause family). Mutually exclusive with sizeMin/sizeMax and with
  // `fields` (a dynamically-sized buffer's own size isn't known until the harness runs, so its contents can't be
  // pointer-field-linked).
  std::optional<uint64_t> sizeFromOffset;
  std::string sizeFromType;          // size.from_field.type: a Relations.cpp lookupTypeName() name, e.g. "size_t"
  // size.from_field.elem: the sibling field holds an ELEMENT count, not a byte count, and one element is this many
  // bytes -- the real allocation is `<field> * elem`. 1 (the default) is the plain byte-count form. This is what
  // lets an array of structs be sized by its count field: FreeType's `TT_FaceRec { FT_UShort num_tables;
  // TT_Table dir_tables; }` with sizeof(TT_TableRec) == 32, where `limit = entry + face->num_tables` walks
  // `num_tables` elements off a one-element object without it (DESIGN.md §22.352).
  uint64_t sizeFromElem = 1;
  // buffer: instead of allocating its own object, this field's pointer is one-past-the-end of an EARLIER sibling
  // field's allocation (`same_alloc: {offset: <sibling's own offset>}`) -- the base/end, start/end, bottom/top
  // pointer-pair idiom (a cursor and a boundary into the same buffer; see DESIGN.md's relations-DSL "two pointers
  // must share one allocation" gap: NFS xdr_stream's p/end, QuickJS BCReaderState, Duktape valstack_top/bottom are
  // all this shape). The sibling must appear earlier in the same `fields:` list and be a plain buffer field (not
  // itself same_alloc/size.from_field). Mutually exclusive with size/at/fields/owned/nullable.
  std::optional<uint64_t> sameAllocOffset;
  // same_alloc.pos: where in the sibling's allocation this pointer lands. "end" (the default, and the only form
  // before §22.354) is one-past-the-end -- a `limit`/`end` boundary. "inside" is a free offset in [0, size] chosen
  // like any other input -- a `cursor`/`cur`/`pos` that has already advanced some unknown distance into the buffer.
  // Both are derived from the sibling's own allocation, so neither can ever disagree with it about which object it
  // is in; only "end" additionally pins the exact distance.
  bool sameAllocInside = false;
  // the pointer may be NULL (a 1-bit input decides, see PlannedField::isNull). Applies to every field kind: on a
  // `funcptr` field it means the field can hold NULL as well as any of `targets`, which is what an optional callback
  // ("if (stream->read) stream->read(...) else ...") really looks like. The generator emits it only when the code
  // itself tests that field for NULL -- see Scan.cpp and DESIGN.md §22.353.
  std::optional<bool> nullable;
  std::vector<std::string> targets;  // funcptr
  // `where`: preconditions on integers INSIDE the object this field points at, by byte offset -- the same thing
  // ParamSpec::where states about a parameter's own pointee, one level down. What needs it is the count of an
  // INLINE fixed array: `CFF_PrivateRec { FT_Fixed blue_values[14]; FT_Byte num_blue_values; }` is walked as
  // `for (i = 0; i < num_blue_values; i += 2) blues->zone[blues->count++] = ...`, and a synthesised private_dict
  // leaves the count free to 255 although the real parser caps it at 14 (DESIGN.md §22.356).
  std::vector<WhereSpec> where;
  std::vector<FieldSpec> fields;     // pointer fields inside the pointed-to object
  bool owned = false;                // buffer: the object is a heap allocation the callee owns (it may free it)
  // buffer: the pointee is shared memory / an mmap'd device register / a DMA buffer a real second actor (attacker
  // process, hardware) can change between two reads with no store in between -- the double-fetch/TOCTOU shape. MVP:
  // explicit declaration only, no auto-detection; the harness marks the allocated object markExternallyMutable()
  // (Memory.h) so each non-pointer core.load against it gets its own fresh value instead of a cached one (Machine.h
  // Opc::Load). See DESIGN.md's "external memory" relations-DSL gap.
  bool externallyMutable = false;
  unsigned line = 0;
};

struct ParamSpec {
  std::string name;
  std::string taint = "none";        // none | value | pointee | both
  std::string content;               // "" = zero | zero | unknown: the pointee object's bytes before anything writes them (see FieldSpec::content)
  std::string kind;                  // pointers: buffer (default) | cstring
  std::string type;                  // C-like type name giving signedness/width hints: int, size_t, uint8_t, ...
  std::optional<int64_t> lo, hi;     // range [lo, hi]
  std::optional<uint64_t> sizeMin, sizeMax;  // pointee object size in bytes
  // buffer: instead of a free/fixed size (sizeMin/sizeMax), the object's real size is the value of an EARLIER
  // top-level scalar parameter (`size: {from_param: {name: ...}}`) -- the cross-parameter "pointer + length" idiom
  // (e.g. `int foo(size_t klen, const void *key)`), as opposed to `FieldSpec::sizeFromOffset`'s "length lives in a
  // sibling field of the SAME pointee object" idiom. The named parameter must appear earlier in the function's
  // parameter list and be a plain (non-pointer) scalar; this mirrors the existing earlier-only lookup `elements.count`
  // already does against `out.params` in InitGen.cpp, not a new ordering restriction. Mutually exclusive with
  // sizeMin/sizeMax. See DESIGN.md's relations-DSL "cross-top-level-parameter size relation" gap.
  std::optional<std::string> sizeFromParam;
  std::optional<bool> nullable;
  std::vector<int64_t> enumValues;   // legal values when the parameter is an enum
  std::vector<FieldSpec> fields;     // pointer parameters: pointer fields of the pointee object
  uint64_t at = 0;                   // pointer parameters: the argument is the object's address + at (container_of on the parameter)
  std::vector<ElementsSpec> elements;
  std::vector<WhereSpec> where;
  std::string overrideFile;          // the file that last overrode range/enum/size (a preconditions file), "" = none
  unsigned overrideLine = 0;
  bool owned = false;                // pointer parameters: the object is a heap allocation owned by the callee, which may free it (kfree(arg), free callbacks)
  bool externallyMutable = false;    // pointer parameters, kind: buffer: see FieldSpec::externallyMutable
  std::optional<int64_t> value;      // fixed value of a non-tainted scalar
  // kind: vector only: element width in bits (8/16/32/64); default 32 (int) when omitted.
  std::optional<unsigned> elemBits;
  // kind: map only: key/value width in bits (8/16/32/64) each; default 32 (int) when omitted.
  std::optional<unsigned> keyBits, valBits;
  unsigned line = 0;
};

struct Relation {
  std::string text;                  // e.g. "len >= 0 => (size_t)len <= size(src)"
  unsigned line = 0;
  std::string file;                  // "" = the entry spec itself
};

// `setup:` -- the session constructor to run before the entry (DESIGN.md §22.368 §7).
//
// A handler is handed a per-fd object the module's own `.open` built: `file->private_data`, a QNX OCB, a device
// context. Synthesising that object field by field produces one whose fields are individually legal and jointly
// impossible -- the §22.365 root cause -- and the interface contract today says exactly that, in the report:
// "running that constructor is not implemented, so it degrades to kernel-owned untainted state". This runs it.
//
// `function` is resolved against the module; it must take the session object as one of its parameters.
// `session_param` names the parameter of THIS entry that is the session; `ctor_param` names the parameter of the
// constructor that is the same object. The constructor's OTHER parameters are given zeroed objects of their
// pointee size (scalars 0): they are the kernel-owned context the real caller passes, not attacker input, and
// that narrowing is named in the report.
struct SetupSpec {
  std::string function;
  std::string sessionParam;   // parameter of the entry
  std::string ctorParam;      // parameter of the constructor holding the same object
  std::string success;        // e.g. "ret == 0": assumed after the call ("" = no condition)
  unsigned line = 0;
};

struct EntrySpec {
  std::string function;
  std::string label = "entry";       // taint label carried to the interpreter (network, file, ...)
  std::vector<ParamSpec> params;
  std::vector<Relation> relations;   // empty = hostile mode; contract / trusted_len modes list their relation here
  // Narrowings the spec ASSERTS rather than derives, in the words of whoever asserted them -- today the interface
  // contract a generated spec was lowered from ("'file' is the session object .open built, modelled as untainted
  // kernel state"). They constrain nothing by themselves: every one is already expressed by the params above. They
  // exist so the report can NAME the narrowing, the same discipline `same_alloc`, `where` and `nullable` follow --
  // a narrowing that is wrong HIDES a defect, so it may never be invisible (DESIGN.md §22.361).
  std::vector<Relation> assumptions;
  SetupSpec setup;
  unsigned line = 0;
};

struct SpecDefaults {
  uint64_t maxObj = 4096;            // upper bound of a parameter pointee object
  bool nullable = false;
  bool benignSeed = true;
};

// `init:` -- the project's own initialiser(s), run before the entry (DESIGN.md §22.368).
//
// A handler is never called in the state the scanner starts it in: every global still holds its static initialiser
// (usually zero) because the thing that sets them -- `module_init` for a Linux driver, `main` for a server or a
// QNX resource manager, a `constructor`/`_init` for a shared library -- has not run. G1 (§22.362) measured what
// that costs: a branch decided by such a global produces a false finding on the edge the real module would never
// take AND a silent coverage loss on the edge it would, at the same time, and it can surface as any finding kind.
//
// This says which function(s) to run first. It is deliberately the ONLY key in `init:` for now: stop functions,
// the backtrack-and-flip repair past `exit()` paths, and per-configuration prologues are all designed in §22.368
// and none of them has a consumer yet. A key that is parsed and does nothing is exactly the mistake
// `InterfaceModel::prologue` made -- it had a comment describing budget accounting that never existed -- so the
// schema does not grow until the code behind it does.
//
// Current restriction, enforced with an error rather than silently: each named function must take NO parameters.
// `module_init`, `_init` and `__attribute__((constructor))` bodies all qualify; `main(int, char **)` does not, and
// servers are the next step (§22.368 step 4), which is also where stop functions become necessary because a
// server's `main` never returns.
struct InitSpec {
  std::vector<std::string> functions;   // run in this order, before the entry
  unsigned line = 0;
};

struct EntryFile {
  std::string path;
  SpecDefaults defaults;
  InitSpec init;
  std::vector<EntrySpec> entries;
  const EntrySpec *find(const std::string &function) const {
    for (auto &e : entries)
      if (e.function == function) return &e;
    return nullptr;
  }
};

// Preconditions: extra constraints for entries that already have a spec (generated by hlir-scan or written by hand), kept in a
// file of their own so that the spec can be regenerated:
//   preconditions:
//     - function: BZ2_hbMakeCodeLengths
//       params:
//         alphaSize: { range: [0, 258] }
//         freq: { elements: { type: int32_t, range: [0, 8388607], count: alphaSize } }
//         s:    { where: [ { offset: 5096, type: int32_t, range: [-9, 0] } ] }
//       relations: [ "(size_t)alphaSize <= size(len)" ]
// A parameter that is not in the entry is an error (it would silently do nothing). Constraint names start with `pre.` and
// point at this file, so the report lists them as preconditions.
bool applyPreconditions(const std::string &text, const std::string &path, EntryFile &file, Diagnostics &diags);

// Returns false (with diagnostics carrying spec file:line) if the text is not a valid specification.
bool parseEntrySpec(const std::string &text, const std::string &path, EntryFile &out, Diagnostics &diags);

}  // namespace hlir::entry

// C frontend: C source -> `core` text (DESIGN.md §18). The only interface is text in, text out: the result is parsed
// by hlir::ir like any hand-written core file, so the frontend can be replaced without touching the rest.
// Clang is a private dependency of lib/frontend (no clang header appears here).
#pragma once
#include <cstdint>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

namespace hlir::frontend {

struct LowerOptions {
  // Call a thread/work creation callback directly, where the creation happens (`pthread_create`, `kthread_*`).
  // Without it the callback is never executed and the whole thread body is a blind spot; with it the analysis
  // pretends the thread ran to completion at that point, which is a sequencing narrowing the report names.
  bool spawnCallbacks = false;
  std::vector<std::string> clangArgs;  // extra flags, e.g. -DNAME=1, -Iinclude
  // Keep going when some function uses an unsupported construct: those functions are only declared in the output
  // (callers then hit an unmodelled external call = incomplete analysis) and the reasons stay in `diagnostics`.
  bool partial = false;
  // Keep going when the source does not compile cleanly (missing headers, unknown types/macros, ...), the way a scanner
  // has to on code whose build environment is not available: includes that cannot be found are skipped (treated as
  // empty), unknown type names get a stub typedef (fixed-width names like u32/uint8_t/NvU32 their real width, anything
  // else an opaque struct), implicit function declarations are accepted, and every function whose body still contains
  // errors is skipped (declared only). Implies `partial`. Everything assumed is listed in the result.
  // Functions that stay declarations even when the sources define them (header inlines such as the kernel's copy_from_user):
  // a model written in core (models/linux.core) or in the ModelDB supplies their behaviour, with its own UB checks.
  std::vector<std::string> externalFunctions;
  // Accessors `void *get(H *handle)` whose result the code converts to `struct T *` (wl_resource_get_user_data): the scanner
  // then models a handle parameter as an object holding a pointer to a T at offset 0 (a core model implements the accessor).
  std::vector<std::string> userDataGetters;
  // Link mode (hlir-scan --link): this unit will be merged with others. Every access to a global that is only declared here
  // (defined in another file) first calls `@__hlir_init.G`, which the defining unit provides, so initialised data is seen.
  bool link = false;
  // Do not check pointer arithmetic by itself (forming a pointer more than one past the end of an object is undefined behaviour
  // in ISO C): only the memory accesses are checked. Validators write `if (p + len > end) return` on purpose and compilers do not
  // exploit it in practice, so with this option the findings are the accesses that really go out of bounds.
  bool lenientPointerArith = false;
  // Source language: "c", "c++", or "" = by file extension (.cc .cpp .cxx .c++ .C .cp are C++).
  std::string language;
  bool wrapSignedOverflow = false;  // -fwrapv / -fno-strict-overflow: signed overflow wraps, no overflow checks are emitted
  bool recover = false;
  bool inferStructs = true;  // recover: give structs whose definition is missing a layout inferred from how the code uses their members
};

// What the scanner needs to know about a function defined in the translation unit's main file (no clang types).
// A scalar member that is the element count (or byte length) of a sibling INLINE fixed array of the same struct:
// `CFF_PrivateRec { FT_Fixed blue_values[14]; FT_Byte num_blue_values; }`. The array is not a pointer field, so none
// of the size-from-field machinery reaches it; what the harness needs instead is a precondition saying the count
// cannot exceed the array -- otherwise `for (i = 0; i < num_blue_values; i++) ... zone[count++]` walks off an object
// whose real producer caps the count (DESIGN.md §22.356). `hi` is that inclusive upper bound.
struct InlineCountInfo {
  uint64_t offset = 0;
  unsigned bits = 0;
  bool isSigned = false;
  uint64_t hi = 0;
};

// A pointer stored inside the struct a pointer parameter points to (flattened over embedded structs and arrays).
struct PtrFieldInfo {
  uint64_t offset = 0;          // bytes from the start of the pointee struct
  std::string kind;             // struct | handle (pointer to a never-defined type) | bytes | int | func | pointer | other | self
  uint64_t selfTarget = 0;      // self: byte offset (inside the object that holds the field) of the list head it points back to
  uint64_t at = 0;              // struct: the field points `at` bytes into the object (container_of: it designates an embedded member)
  bool viaContainerOf = false;  // `at` came from a recognised container_of hint (vs. the default 0 of "no hint") -- `at`
                                 // alone can't tell a real offset-0 container_of apart from no hint at all, since 0 is
                                 // both the sentinel and a legitimate offset (the member is the struct's first field)
  uint64_t pointeeSize = 0;     // struct: sizeof; bytes/int: element size
  std::string structName;
  std::string funcSig;          // func: core signature text, e.g. "(ptr, i32) -> i32" (matches FunctionInfo::sig)
  std::string funcCType;        // func: C type key of the pointer (matches FunctionInfo::cType), "" if unknown
  bool cyclic = false;          // struct: the pointee type is already being expanded (self-referential links)
  // func: some visible code tests THIS field for NULL (`if (s->read)`, `s->read == NULL`, `!s->read`, ...), so a real
  // object of this type demonstrably can hold NULL here and the synthesised field must be allowed to as well. Without
  // this every call through the field dispatches into some real function with unsynthesised state -- FreeType's
  // `FT_StreamRec.read` is NULL for a memory stream and tested in 13 places, and forcing it non-NULL sent every
  // `FT_Stream_Read*` into the gzip reader and capped the whole sfnt/truetype surface (DESIGN.md §22.353).
  bool nullTested = false;
  // This field lies inside a UNION, and the walk took the union's FIRST arm to reach it (DESIGN.md §22.484).
  // A union overlays its members, so there is no single pointer layout and the collector used to skip unions
  // whole -- which for `struct folio`, whose outermost member IS an anonymous union, meant the parameter
  // contributed no pointer fields at all and everything an address_space_operations handler reached through
  // `folio->mapping` was synthesis-frontier guesswork. Taking one arm is a CHOICE and may be the wrong one, so
  // it is carried out to the report rather than made silently.
  bool viaUnionArm = false;
  // struct, pointer array (`robj **argv`): the pointee is an array of a few element pointers, `children` are those slots.
  // lenOffset/lenBits/lenSigned: a sibling count field (`argc`, `n_items`, ...) in the same struct, offset >= 0 when found
  bool ptrArray = false;
  // bytes/int: this pointer is a second view into the allocation of the SIBLING pointer field at this byte offset of
  // the same struct -- the (base, cursor, limit) idiom, where all of them walk one buffer. Synthesising them as
  // independent objects makes every `while (cur < limit)` a comparison of unrelated pointers: 11 confirmed
  // `ptr_cmp_diff_obj` at FreeType's psobjs.c:286 from `PS_ParserRec { FT_Byte *cursor, *base, *limit; }`, and the
  // same family recurs across the kernel rounds. -1 = no pairing. `aliasEnd` tells the two roles apart: a `limit`/
  // `end` is one-past-the-end of the allocation, a `cursor` is somewhere inside it (DESIGN.md §22.354).
  int64_t aliasOffset = -1;
  bool aliasEnd = false;
  // struct: the counts of inline fixed arrays inside the pointee (see InlineCountInfo), as `where:` preconditions
  std::vector<InlineCountInfo> inlineCounts;
  int64_t lenOffset = -1;
  unsigned lenBits = 0;
  bool lenSigned = true;
  // the sibling names a COUNT OF ELEMENTS, not a number of bytes, so the real allocation is `len * pointeeSize`.
  // Always true for an array of wider integers (`unsigned short *contours` with `n_contours`), where the two
  // readings differ and only the count-shaped spellings are accepted at all -- see findSiblingLenField.
  bool lenIsCount = false;
  unsigned arraySlots = 0;
  std::vector<PtrFieldInfo> children;  // struct: its own pointer fields (depth-limited)
  // --link only: this field was kept despite not being read/written anywhere in its own file's visible AST, because the
  // used-fields check (below) cannot see other units yet when this is computed. `fieldKey` ("<path>:<line>:<col>" of the
  // field's declaration) lets a later, whole-program pass decide for real and prune it back out if it is unused everywhere.
  // Non-link scans never set this: they keep the original immediate-drop behaviour and never reach pruning at all.
  bool pendingLinkUse = false;
  std::string fieldKey;
};

// An integer member of the struct a pointer parameter points to (embedded structs flattened: "hdr.len").
struct ScalarFieldInfo {
  std::string name;
  uint64_t offset = 0;          // bytes
  unsigned bits = 0;
  bool isSigned = false;
};

// A bound the PROGRAM ITSELF states about an integer member, harvested from an assertion macro
// (`BUG_ON`/`WARN_ON`/`snd_BUG_ON`/`assert`/`FT_ASSERT`): `snd_BUG_ON(dp->max_synthdev > SNDRV_SEQ_OSS_MAX_SYNTH_DEVS)`
// says that in a correct kernel the member is at most that constant, and the kernel writes this down in a place a
// name heuristic can never reach (DESIGN.md §22.358).
//
// Two things make this safe to use, and both are load-bearing:
//  - It becomes a `where:` PRECONDITION, which constrains only the INITIAL synthesised state. It therefore says
//    "the object did not START in a state the program calls broken", NOT "the program can never reach that state":
//    code that drives the object there is still found, which is exactly the class syzkaller reports as WARN_ON hits.
//  - Only ASSERTION MACROS are harvested, never an ordinary `if (x) return -EINVAL`. An assertion states an internal
//    invariant; an error return VALIDATES ATTACKER INPUT, and assuming that away would hide the bugs we look for.
//
// Keyed by `assertKey(tag, sizeof(record), byte offset)` rather than by the member's declaration location: the bound
// then applies to EVERY object of that type the harness builds -- the parameter's own pointee and, just as
// importantly, the sub-objects behind its pointer fields -- without any per-field bookkeeping being carried up from
// the frontend. A kernel struct has hundreds of members, and recording a key for each of them on each of its
// hundreds of pointer fields is not affordable. The record size is part of the key so that two unrelated types that
// happen to share a tag cannot borrow each other's invariants.
struct AssertedBound {
  bool hasLo = false, hasHi = false;
  int64_t lo = 0, hi = 0;       // inclusive
  uint64_t offset = 0;          // byte offset of the member inside its record (also encoded in the key)
  unsigned bits = 0;
  bool isSigned = false;
};

// "<tag>#<record size>@<byte offset>"; empty tag (an anonymous record) yields "" and is never recorded.
std::string assertKey(const std::string &tag, uint64_t recordSize, uint64_t offset);

struct ParamInfo {
  std::string name;
  std::string cType;            // as written, e.g. "const struct req *"
  std::string kind;             // int | bool | ptr | other
  unsigned bits = 0;            // int/bool
  bool isSigned = false;
  // kind == ptr:
  std::string pointee;          // void | int | struct | pointer | function | other
  unsigned pointeeBits = 0;     // pointee == int
  bool pointeeIsChar = false;   // pointee == int: the plain `char` type (C strings), not unsigned char / uint8_t
  uint64_t pointeeSize = 0;     // sizeof(*p); 0 for void/function
  bool pointeeConst = false;
  std::string structName;
  bool structHasPointers = false;
  std::vector<ScalarFieldInfo> scalarFields;  // pointee == struct: its integer members (for preconditions that name a field)
  std::vector<InlineCountInfo> inlineCounts;  // pointee == struct: counts of its inline fixed arrays (see InlineCountInfo)
  bool opaqueHandle = false;             // declared void* (a handle typedef) but the code reveals the struct behind it: library-owned state, not caller data
  bool freed = false;                    // the function passes this parameter to free()/kfree()/*_free(): the caller must hand over a heap object
  // shared, not copied: many functions in one file commonly take the same struct pointer (e.g. `struct amdgpu_device
  // *adev` in ~150 functions of one real kernel file) and collectPtrFieldsCached hands back the identical tree for
  // all of them -- a plain vector copy per parameter turned that into tens of GB of RSS on kernel-sized structs
  // (thousands of pointer fields) walked at --link scale. Always non-null (default-constructed to an empty vector).
  std::shared_ptr<std::vector<PtrFieldInfo>> ptrFields = std::make_shared<std::vector<PtrFieldInfo>>();  // pointee == struct
  std::string udStruct;                  // passed to a user-data getter whose result is converted to `struct udStruct *`
  bool udOwned = false;                  // the code frees a `struct udStruct *` (the user data is a heap object the callee owns)
  uint64_t udSize = 0;                   // sizeof(struct udStruct)
  std::shared_ptr<std::vector<PtrFieldInfo>> udPtrFields = std::make_shared<std::vector<PtrFieldInfo>>();  // its pointer fields
  uint64_t at = 0;                       // pointee == struct: the argument points `at` bytes into the object (container_of on the parameter)
  bool viaContainerOf = false;           // `at` came from a recognised container_of hint -- see PtrFieldInfo::viaContainerOf
  // pointee == struct and the struct is `std::basic_string<char>`/`<wchar_t>` (libstdc++): the scanner emits `kind:
  // string`/`kind: wstring` instead of the generic byte-buffer layout, see lib/scan/Scan.cpp and IMPLEMENTATION_PLAN
  // "std::string 不变式建模" (entry-parameter synthesis follow-up).
  bool isStdString = false;
  unsigned stdStringCharBits = 0;        // 8 (char) or 32 (wchar_t)
  // pointee == struct and the struct is `std::vector<T>` with T a scalar (arithmetic, non-bool) type: `kind: vector`
  // instead of the generic byte-buffer layout, see lib/scan/Scan.cpp and IMPLEMENTATION_PLAN "std::vector/std::map
  // 入口参数合成自洽化".
  bool isStdVector = false;
  unsigned stdVectorElemBits = 0;        // T's width in bits (8/16/32/64)
  // pointee == struct and the struct is `std::map<K,V>` with K, V scalar (arithmetic, non-bool, <=8 byte) types and
  // the default comparator/allocator: `kind: map` (modelling only 0 or 1 entries -- see the "StdMap" comment in
  // InitPlan.h and IMPLEMENTATION_PLAN for why).
  bool isStdMap = false;
  unsigned stdMapKeyBits = 0, stdMapValBits = 0;
};
struct FunctionInfo {
  std::string name, file;
  std::string display;          // readable name (C++: ns::Class::method); `name` is the core symbol (the mangled name in C++)
  unsigned line = 0;
  bool isStatic = false;
  bool addrTaken = false;       // referenced other than as the callee of a call (handler tables, callbacks)
  unsigned callers = 0;         // calls from other functions of the same file
  std::vector<std::string> callees;
  std::string returnType;
  std::string sig;              // core signature text (matches PtrFieldInfo::funcSig), "" if it has none
  // C type key when the function's address only flows as its own type (LowerResult::addrTakenCTypes): a function pointer
  // field of another C type cannot hold it. "" = may be called through any type with its signature
  std::string cType;
  std::vector<ParamInfo> params;
  bool lowered = true;          // false if this function hit an unsupported construct or a compile error
  std::string skipReason;       // why it was not lowered
};

struct VtableInstance {
  std::string tag;                             // the struct tag (file_operations, _resmgr_io_funcs, ...)
  std::map<std::string, std::string> slots;    // vtable field -> the function registered in it
};

struct LowerResult {
  bool ok = false;
  std::string core;         // the `core` module text (when ok)
  std::string diagnostics;  // clang errors and "unsupported construct" messages
  std::vector<std::string> missingHeaders;  // recover: includes that were not found and skipped
  std::vector<std::string> assumedTypes;    // recover: unknown type names that got a stub typedef
  std::vector<std::string> inferredStructs; // recover: "struct X { type a; type b; /* guessed */ ... }" synthesized from member accesses
  // Core symbols (without the '@') with internal linkage in this unit: static functions and variables, string literals and their
  // init functions. A linker must keep same-named symbols of different units apart (hlir::link).
  // Functions whose address is taken in this unit (name, core signature text `(ptr, i32) -> i32`): the candidates of indirect
  // calls of the whole program (hlir::link builds `@__hlir_indirect.<sig>` dispatchers from them).
  std::vector<std::pair<std::string, std::string>> addrTakenFunctions;
  // name -> C type key (hlir/support/IndirectCall.h) of the addrTakenFunctions whose address only ever flows as a
  // compatible type (no cast to an incompatible function pointer type, to `void *` or an integer, no union store): a call
  // through a pointer whose key is not cTypesCompatible cannot reach them (C11 6.3.2.3p8; kCFI traps it in the kernel).
  // Functions missing here match every call of their signature.
  std::map<std::string, std::string> addrTakenCTypes;
  // link mode: dispatcher name `__hlir_indirect.<sig>.t<hash>` -> the C type key of the pointer the call goes through
  std::map<std::string, std::string> indirectCallCTypes;
  // Symbol names this unit asks `dlsym` for with a STRING LITERAL (`dlsym(h, "ssl_connect")`). The call is lowered to
  // `@__hlir_dlsym.<name>`, which hlir::link defines once it can see the whole program's symbol table: a name some unit
  // defines resolves to that function's address (and becomes an indirect-call candidate), a name nothing defines stays
  // an opaque external. A computed name cannot be resolved and is not collected here.
  std::set<std::string> dlsymNames;
  std::vector<std::string> internalTokens;
  std::vector<FunctionInfo> functions;  // every function defined in the main file (filled even if lowering failed)
  // --link only: every field this unit's AST can see read or written anywhere in it (any function with a body visible here,
  // not just functions reachable from a particular entry): the keys `PtrFieldInfo::fieldKey` can match against, so a field
  // read only via a call into a *different* unit (no body visible from here) is still recognised as used once all units'
  // sets are combined. Empty for non-link scans (not computed; unused).
  std::set<std::string> fieldUses;
  // --link only: the same keys, for fields this unit's AST can see tested for NULL anywhere in it (see
  // PtrFieldInfo::nullTested). A field set and tested in a unit other than the one that declares the pointer to it --
  // the normal case for `FT_StreamRec.read` -- is only recognised once all units' sets are combined.
  std::set<std::string> fieldNullTests;
  // --link only: bounds this unit's assertion macros state about integer members, keyed like the sets above.
  std::map<std::string, AssertedBound> fieldAsserts;
  // How many `container_of(p, T, member)` expressions this unit lowered with their pointer-arithmetic check waived,
  // and where the first one is. The idiom routinely computes a pointer BEFORE the object (an empty
  // `list_for_each_entry` is exactly that) and never dereferences it, so the arithmetic check alone would report a
  // defect that cannot happen -- but waiving a check is a NARROWING, and §22.361 says a narrowing may not be
  // invisible, so the count is carried out to the report (DESIGN.md §22.368). The DEREFERENCE check is untouched.
  // How many thread/work-creation calls had their callback emitted as a direct call (`--spawn-callbacks`,
  // DESIGN.md §22.372). A WIDENING in coverage and a NARROWING in sequencing, so it is named in the report.
  unsigned spawnCallbacksEmitted = 0;
  unsigned containerOfWaived = 0;
  std::string containerOfFirstSite;
  // Handlers this unit registers in a dispatch table: function name -> the slots its address was written to, keyed
  // `<record tag>#<field>` (`file_operations#unlocked_ioctl`). Both static initialisers and run-time assignments
  // are recorded; the key is stable across units so hlir-scan can union it in --link mode. Unlike fieldUses this
  // is computed for every scan, because a single-file scan can use `--entries iface` too. hlir::iface matches the
  // key against an interface model to decide which functions are the module's real entries (DESIGN.md §22.359).
  std::map<std::string, std::set<std::string>> vtableBindings;
  // One dispatch-table INSTANCE: `slots[field] = function`. Keyed by a stable, readable identity
  // (`file_operations@snd_ctl_f_ops (sound/core/control.c:2270)`). `vtableBindings` above says a function is in
  // some table's slot; this says WHICH table, which is what pairs an `open` with the `ioctl` of the same device
  // -- a module registers many tables of one type (sound/core alone has 14 `file_operations`), so without it a
  // session constructor cannot be resolved at all (DESIGN.md §22.368 §7).
  std::map<std::string, VtableInstance> vtableInstances;
};

// `fileName` is only used for locations and diagnostics; the text comes from `source`.
LowerResult lowerC(const std::string &source, const std::string &fileName, const LowerOptions &opt = {});

}  // namespace hlir::frontend

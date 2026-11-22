// STABLE. The result of type-driven initialisation (DESIGN.md §21.4): for one taint entry, the symbolic inputs, the
// objects to create, and the named legality constraints C_init. It is solver-agnostic (smt terms) and is the single
// source for both the seed solver and the generated harness.
#pragma once
#include <optional>
#include <string>
#include <vector>

#include "hlir/entry/Spec.h"
#include "hlir/ir/IR.h"
#include "hlir/smt/Term.h"

namespace hlir::entry {

// A free input of the entry: becomes a core.nondet in the harness and a variable in the constraints.
struct InitVar {
  smt::TermRef var;        // bit-vector variable; its name is the nondet name
  std::string taint;       // "" = untainted input (e.g. a size), else the entry label
  // The harness's own structural choices -- "is this optional pointer absent?" above all -- are NOT attacker data, so
  // they must not carry a taint label; but a `core.nondet` with no label is kept fully CONCRETE (TaintDomain::nondet),
  // which means the branch that tests the choice is not a branch at all and the explorer can never take the other
  // side. `promote` is the engine's existing name for "symbolic although untainted" (TaintConfig::promote): the driver
  // passes these names through so both configurations of a nullable pointer get explored, while nothing downstream
  // mistakes the choice for attacker-controlled data (DESIGN.md §22.353). What makes that last clause true is the
  // reserved `harness` label and TaintDomain::isAttackerControlled -- `TVal::tainted()` alone cannot express it,
  // since it means "has a symbolic term" (DESIGN.md §22.363).
  bool promote = false;
};

// A bound on an integer that lives in the memory of a parameter object (see ElementsSpec / WhereSpec). The harness loads the
// value, so it can only be stated there: one `core.assume` per constraint, named `name`.
struct PlannedBound {
  unsigned width = 0;
  bool isSigned = true;
  std::optional<int64_t> lo, hi, value;
  std::vector<int64_t> enumValues;
  std::string name;                  // pre.<param>.where@file:line / pre.<param>.elements@file:line
};
struct PlannedElements : PlannedBound {
  unsigned elemBytes = 0;
  smt::TermRef count = nullptr;      // number of leading elements (a parameter's value or a constant); null = all that fit
  bool countSigned = true;
  unsigned countWidth = 0;
};
struct PlannedWhere : PlannedBound { uint64_t offset = 0; };

// A pointer field of a parameter's pointee (see FieldSpec): one more object for the harness to create and link.
struct PlannedField {
  enum Kind { Buffer, FuncPtr, Self } kind = Buffer;
  uint64_t target = 0;               // Self: the pointer points to parent + target
  uint64_t at = 0;                   // Buffer: the stored pointer is the new object + at
  std::string name;                  // <param>.<offset>[.<offset>...]: names the object and its inputs
  uint64_t offset = 0;
  bool tainted = false;              // content of the pointed-to object is attacker controlled
  smt::TermRef size = nullptr;       // Buffer: bit-vector (ptr width) variable or constant (unused when sizeFromOffset is set)
  smt::TermRef isNull = nullptr;     // when nullable: 1-bit variable (1 = NULL)
  smt::TermRef selector = nullptr;   // FuncPtr: 8-bit variable choosing one of `targets`
  uint64_t sizeLo = 0, sizeHi = 0;
  // Buffer: instead of `size`, the harness reads the real allocation size from an integer sibling field at this byte
  // offset in the parent object (see FieldSpec::sizeFromOffset) -- constructed, not just constrained, so the buffer
  // object and its length field can never disagree.
  std::optional<uint64_t> sizeFromOffset;
  unsigned sizeFromWidth = 0;
  bool sizeFromSigned = false;
  uint64_t sizeFromElem = 1;         // Buffer: the sibling field is an ELEMENT count; one element is this many bytes
                                     // (see FieldSpec::sizeFromElem). 1 = the plain byte-count form.
  // Buffer: instead of allocating its own object, this field is a one-past-the-end view into an earlier sibling
  // field's allocation (same `fields` list, same nesting level) -- the base/end, start/end, bottom/top pointer-pair
  // idiom (see FieldSpec::sameAllocOffset). Index into that sibling list. Mutually exclusive with size/sizeFromOffset/at/fields.
  std::optional<size_t> sameAllocIndex;
  // same_alloc.pos: inside -> this pointer lands `sameAllocOff` bytes into the sibling's object instead of exactly
  // one-past-its-end (a cursor that has already advanced, see FieldSpec::sameAllocInside). The offset is an input of
  // its own, constrained to [0, sibling size]; it is promoted, not tainted -- where a cursor happens to stand is the
  // harness's structural choice, not attacker data (same reasoning as InitVar::promote).
  bool sameAllocInside = false;
  smt::TermRef sameAllocOff = nullptr;
  // preconditions on integers inside this field's own object, one level below the parameter's (see FieldSpec::where)
  std::vector<PlannedWhere> wheres;
  std::vector<std::string> targets;
  std::vector<PlannedField> fields;  // pointer fields inside the pointed-to object
  bool owned = false;                // Buffer: a heap object the callee owns (may free)
  bool externallyMutable = false;    // Buffer: see FieldSpec::externallyMutable / Memory::markExternallyMutable()
  // Buffer: the object's bytes start out symbolic and harness-labelled instead of zero (`content: unknown`,
  // FieldSpec::content, DESIGN.md §22.381). Inherited from the parent object unless the field is tainted: what
  // lives behind a pointer of a driver-built session is driver-built too.
  bool unknownContent = false;
  unsigned line = 0;
};

struct PlannedParam {
  // StdString: `std::basic_string<char>` (kind: string) or `std::basic_string<wchar_t>` (kind: wstring) passed by
  // reference/pointer. Synthesised with a self-consistent libstdc++ SSO layout (see HarnessGen.cpp) instead of the
  // generic "every field an independent symbol" path: the pointee object is a fixed-size (ABI-determined) container
  // whose `_M_p`/`_M_string_length`/union fields are derived from two free variables (`strLen`, `strHeap`) rather
  // than each being its own unconstrained symbol.
  //
  // StdVector: `std::vector<T>` (kind: vector) with a scalar (arithmetic, non-bool) element type T, passed by
  // reference/pointer. libstdc++'s `_Vector_impl` is three pointers (`_M_start`/`_M_finish`/`_M_end_of_storage`) whose
  // real invariant is `_M_start <= _M_finish <= _M_end_of_storage` and `_M_finish - _M_start` a multiple of
  // sizeof(T); synthesised from one free variable (`vecLen`, the element count) instead of three independent pointer
  // symbols, so `_M_finish`/`_M_end_of_storage` are always derived from `_M_start` and never dangle or disagree.
  //
  // StdMap: `std::map<K,V>` (kind: map) with scalar (arithmetic, non-bool, <=8 byte) K and V and the default
  // comparator/allocator, passed by reference/pointer. See IMPLEMENTATION_PLAN "std::vector/std::map 入口参数合成自洽化"
  // for why this is a deliberately narrowed approximation: libstdc++'s red-black tree (`bits/stl_tree.h`) has a far
  // richer invariant (parent/child/color consistency, key ordering per the comparator, black-height balance) than a
  // field-independent or even a three-pointer synthesis could express without touching the comparator itself; rather
  // than attempt a general symbolic red-black tree, this models exactly the two shapes a real libstdc++ `_Rb_tree`
  // can be in without needing any key comparison at all -- an empty tree, or a tree with exactly one (black, root)
  // node -- chosen by one free, tainted variable (`mapHasElem`: unlike StdString's `strHeap`, this choice changes
  // observable behaviour, so it has to be attacker-influenced data, not an untainted internal detail -- see
  // InitGen.cpp), with the node's key/value content tainted too. This covers the common "attacker-controlled map
  // with 0 or 1 entries" and "an out-parameter map the callee populates" shapes; it does not cover an
  // attacker-supplied map with >=2 entries (see the limits section of that doc).
  enum Kind { Scalar, Buffer, CString, StdString, StdVector, StdMap } kind = Scalar;
  std::string name;
  bool isBool = false;     // core `bool` parameter (a 1-bit input)
  bool isSigned = true;    // scalars: signedness used by ranges / relations / BVA seeds
  unsigned width = 0;      // scalars
  bool tainted = false;    // the value (scalars) or the content (buffers) is attacker controlled
  smt::TermRef value = nullptr;      // Scalar: variable (tainted) or constant (untainted)
  smt::TermRef size = nullptr;       // Buffer/CString/StdString: bit-vector (ptr width) variable or constant
  smt::TermRef isNull = nullptr;     // Buffer/CString when nullable: 1-bit variable (1 = NULL)
  uint64_t sizeLo = 0, sizeHi = 0;   // possible sizes
  std::vector<int64_t> enumValues;
  std::vector<PlannedField> fields;  // pointer fields of the pointee object
  uint64_t at = 0;                   // the argument is the object + at
  bool owned = false;                // a heap object the callee owns (may free), not a borrowed parameter object
  bool externallyMutable = false;    // Buffer/CString: see FieldSpec::externallyMutable / Memory::markExternallyMutable()
  bool unknownContent = false;       // Buffer/CString: see PlannedField::unknownContent / ParamSpec::content
  std::vector<PlannedElements> elements;
  std::vector<PlannedWhere> wheres;
  unsigned line = 0;
  // StdString only:
  smt::TermRef strLen = nullptr;     // bit-vector (ptr width), tainted: the string's content length in elements
  smt::TermRef strHeap = nullptr;    // 1-bit, untainted: 1 = heap representation chosen, 0 = SSO (local buffer)
  unsigned charWidth = 8;            // 8 = char (std::string), 32 = wchar_t on Linux/gcc (std::wstring)
  // StdVector only:
  smt::TermRef vecLen = nullptr;     // bit-vector (ptr width), tainted: the element count
  unsigned elemWidth = 32;           // element width in bits (8/16/32/64); content is raw bits (int or float alike)
  // StdMap only:
  smt::TermRef mapHasElem = nullptr; // 1-bit, tainted when the parameter is: 1 = one (black, root) node, 0 = empty
                                      // tree (tainted, unlike StdString's strHeap: this changes observable behaviour,
                                      // see InitGen.cpp)
  smt::TermRef mapKey = nullptr;     // bit-vector (keyWidth), tainted: the sole node's key, when mapHasElem
  smt::TermRef mapVal = nullptr;     // bit-vector (valWidth), tainted: the sole node's value, when mapHasElem
  unsigned keyWidth = 32, valWidth = 32;  // 8/16/32/64 each
};

struct InitConstraint {
  std::string name;        // init.<param>.<kind>@<spec file>:<line>
  smt::TermRef term;       // Bool
};

// Soft preferences that make the first seed "benign" (typical, legal values) rather than an arbitrary corner.
struct SoftConstraint {
  std::string name;
  smt::TermRef term;       // Bool
  int weight;
};

struct InitPlan {
  std::string function;
  std::string label;
  std::string specFile;
  unsigned specLine = 0;
  Type *retTy = nullptr;
  std::vector<PlannedParam> params;     // in function parameter order
  std::vector<InitVar> vars;            // every free input, in a stable order
  std::vector<InitConstraint> constraints;
  std::vector<SoftConstraint> soft;
  unsigned ptrWidth = 64;
  // C++: when `function` is a non-static member function and its class has a usable constructor (a body in the
  // module, `this` plus only scalar/bool extra parameters — covering both a true default constructor and one whose
  // extra parameters all have default argument values, such as `XMLDocument(bool = true, Whitespace = ...)`;
  // `core` does not carry default-argument values, so each extra parameter is passed 0/false, not the value the
  // source declares), its mangled symbol and extra parameter types (excluding `this`); the harness calls it on the
  // `this` object instead of leaving it zeroed memory. `ctorFunction` is "" when `function` is not a method, the
  // class has no such constructor in the module (e.g. a plain aggregate/POD type, or every constructor takes a
  // pointer/object parameter), or more than one candidate ties for fewest extra parameters (ambiguous).
  std::string ctorFunction;
  std::vector<Type *> ctorExtraParamTys;
  // The project's own initialiser(s) (`init:` in the spec, EntryFile::init), resolved against the module: the
  // harness calls them, in order, immediately before the entry. Placed there and not at the top of the harness on
  // purpose -- Memory numbers objects in allocation order and `paramObjId` relies on the parameters being numbered
  // first, so an initialiser that allocates would otherwise shift every witness name by however many objects it
  // happened to create (the §22.351 failure: a confirmed finding printing a witness that does not reach it).
  // Nothing an initialiser does depends on our synthetic parameter objects, so the order is free to be chosen this
  // way. DESIGN.md §22.368.
  // The session constructor to run before the entry (`setup:`, DESIGN.md §22.368 §7), resolved against the module.
  // `ctorParamIdx` is the constructor parameter that receives the entry's session object; the others get zeroed
  // objects of their pointee size, which is a narrowing the report names.
  struct SetupCall {
    std::string function;
    size_t sessionParamIdx = 0;   // index into InitPlan::params
    size_t ctorParamIdx = 0;      // index into the constructor's parameter list
    std::vector<Type *> ctorParamTys;
    Type *retTy = nullptr;
    std::string success;          // assumed after the call ("" = none)
    bool valid = false;
  };
  SetupCall setup;

  struct PrologueCall {
    std::string function;
    Type *retTy = nullptr;  // void is represented the same way the entry's own return type is
    // An initialiser may take parameters -- `main(int argc, char **argv)` is the case that matters, because for a
    // server or a QNX resource manager `main` IS the initialiser. They are synthesised as the shape a program is
    // really started with (argc = 1, argv = { "prog", NULL }), which is a narrowing the report names: a module
    // that branches on its command line is analysed for one command line.
    std::vector<Type *> paramTys;
  };
  std::vector<PrologueCall> prologue;
  // The command line the initialiser is run with, argv[0] first (model::ExternsFile::argv, DESIGN.md §22.380).
  // Empty = none stated, and the harness falls back to a single program name with no options -- which it then has
  // to NAME as the narrowing it is.
  std::vector<std::string> argv;
};

// Builds the plan for `spec` against the function's signature in `m`. Errors (unknown parameter, unsupported kind,
// unparsable relation, ...) are reported with the spec location.
bool buildInitPlan(const Module &m, const EntryFile &file, const EntrySpec &spec, smt::TermManager &tm, InitPlan &out,
                   Diagnostics &diags);

}  // namespace hlir::entry

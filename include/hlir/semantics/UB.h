// STABLE. Kinds of undefined behaviour / violations the semantics can detect (DESIGN.md §17.5).
// The kind is a property of the executed core.check.* op; the *condition* lives in one place
// (lib/semantics/UBConditions.h) and is shared by the interpreter and the SMT encoder.
#pragma once

namespace hlir {

enum class UBKind {
  SignedOverflow,
  DivByZero,
  DivOverflow,      // INT_MIN / -1
  ShiftRange,       // shift amount >= width
  ShiftNegative,    // left shift of a negative signed value
  ShiftOverflow,    // signed left shift whose result is not representable
  OobRead,
  OobWrite,
  PtrArithOob,
  FieldOob,          // index out of a fixed-size struct-field array's own declared bound (narrower than OobWrite/OobRead)
  UseAfterFree,
  UseAfterScope,
  DoubleFree,
  InvalidFree,
  NullDeref,
  UninitRead,
  Misaligned,
  ConstWrite,
  PtrCmpDiffObj,
  InvalidEnumOrBool,
  Unsequenced,
  UnreachableReached,
  VaArgTypeMismatch,
  TaintedSink,      // attacker-controlled data reaches a security sink (not undefined behaviour: a data-flow finding)
  TaintedLoopBound, // attacker-controlled value governs a loop's iteration count AND no constant cap bounds it (uncontrolled resource consumption / DoS: a warning; suppressed when a dominating guard or narrow type bounds the count -- see Machine.h loopInvariant / TaintDomain::taintLoopWarn)
  TaintedIndex,     // attacker-controlled value used as a memory index with no constant upper bound (unbounded indexing risk: a warning)
};

const char *ubKindName(UBKind k);                // stable snake_case name, e.g. "div_by_zero"
bool ubKindFromName(const char *name, UBKind &k);
// Warning-severity data-flow findings (TaintedLoopBound / TaintedIndex): reported as warnings, they never turn a
// verdict into `bug` (which stays reserved for replay-confirmed undefined behaviour). Every other kind is an error.
bool ubKindIsWarning(UBKind k);

}  // namespace hlir

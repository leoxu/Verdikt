#include "hlir/semantics/UB.h"

#include <cstring>

namespace hlir {

namespace {
const struct { UBKind k; const char *n; } kNames[] = {
    {UBKind::SignedOverflow, "signed_overflow"},   {UBKind::DivByZero, "div_by_zero"},
    {UBKind::DivOverflow, "div_overflow"},         {UBKind::ShiftRange, "shift_range"},
    {UBKind::ShiftNegative, "shift_negative"},     {UBKind::ShiftOverflow, "shift_overflow"},
    {UBKind::OobRead, "oob_read"},                 {UBKind::OobWrite, "oob_write"},
    {UBKind::PtrArithOob, "ptr_arith_oob"},        {UBKind::FieldOob, "field_oob"},
    {UBKind::UseAfterFree, "use_after_free"},
    {UBKind::UseAfterScope, "use_after_scope"},    {UBKind::DoubleFree, "double_free"},
    {UBKind::InvalidFree, "invalid_free"},         {UBKind::NullDeref, "null_deref"},
    {UBKind::UninitRead, "uninit_read"},           {UBKind::Misaligned, "misaligned"},
    {UBKind::ConstWrite, "const_write"},           {UBKind::PtrCmpDiffObj, "ptr_cmp_diff_obj"},
    {UBKind::InvalidEnumOrBool, "invalid_enum_or_bool"}, {UBKind::Unsequenced, "unsequenced"},
    {UBKind::UnreachableReached, "unreachable_reached"}, {UBKind::VaArgTypeMismatch, "va_arg_type_mismatch"}, {UBKind::TaintedSink, "tainted_sink"},
    {UBKind::TaintedLoopBound, "tainted_loop_bound"}, {UBKind::TaintedIndex, "tainted_index"},
};
}  // namespace

const char *ubKindName(UBKind k) {
  for (auto &e : kNames)
    if (e.k == k) return e.n;
  return "?";
}

bool ubKindFromName(const char *name, UBKind &k) {
  for (auto &e : kNames)
    if (std::strcmp(e.n, name) == 0) { k = e.k; return true; }
  return false;
}

bool ubKindIsWarning(UBKind k) {
  return k == UBKind::TaintedLoopBound || k == UBKind::TaintedIndex;
}

}  // namespace hlir

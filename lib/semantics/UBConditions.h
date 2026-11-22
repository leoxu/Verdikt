// Private. The ONE definition of when each core.check.* is violated, generic over the value domain.
// The concrete interpreter evaluates these on APInts; the SMT encoder evaluates the same code on terms.
#pragma once
#include <vector>

#include "hlir/ir/IR.h"
#include "Pred.h"
#include "hlir/semantics/UB.h"

namespace hlir {

template <class D>
struct UBViolation {
  UBKind kind;
  typename D::Val cond;  // width-1 value; true == the check is violated
};

// `a` are the already-evaluated operands of the check op. Returns one entry per distinct UB kind the op can raise.
// Pointer/memory checks are not handled here yet (arrive with the memory model, P4); returns false for them.
template <class D>
bool ubViolations(D &d, const Op &op, const std::vector<typename D::Val> &a, std::vector<UBViolation<D>> &out) {
  using Val = typename D::Val;
  auto wd = [&](const Val &v) { return d.width(v); };
  switch (op.opc) {
    case Opc::CheckDiv: {
      unsigned w = wd(a[0]);
      out.push_back({UBKind::DivByZero, d.icmp(Pred::Eq, a[1], d.zero(w))});
      if (op.hasAttr("signed"))
        out.push_back({UBKind::DivOverflow, d.and_(d.icmp(Pred::Eq, a[0], d.smin(w)), d.icmp(Pred::Eq, a[1], d.allOnes(w)))});
      return true;
    }
    case Opc::CheckShift: {
      unsigned w = wd(a[0]);
      Val tooBig = d.icmp(Pred::Uge, a[1], d.constant(llvm::APInt(w, w)));
      out.push_back({UBKind::ShiftRange, tooBig});
      if (op.hasAttr("signed_left")) {
        out.push_back({UBKind::ShiftNegative, d.icmp(Pred::Slt, a[0], d.zero(w))});
        Val r = d.shl(a[0], a[1]);
        Val lost = d.icmp(Pred::Ne, d.ashr(r, a[1]), a[0]);
        out.push_back({UBKind::ShiftOverflow, d.and_(d.not_(tooBig), lost)});
      }
      return true;
    }
    case Opc::CheckSAddOvf: case Opc::CheckSSubOvf: case Opc::CheckSMulOvf: {
      // Exact check by computing in twice the width and comparing with the sign-extended narrow result.
      unsigned w = wd(a[0]);
      Val x = d.sext(a[0], 2 * w), y = d.sext(a[1], 2 * w), wide, narrow;
      if (op.opc == Opc::CheckSAddOvf) { wide = d.add(x, y); narrow = d.add(a[0], a[1]); }
      else if (op.opc == Opc::CheckSSubOvf) { wide = d.sub(x, y); narrow = d.sub(a[0], a[1]); }
      else { wide = d.mul(x, y); narrow = d.mul(a[0], a[1]); }
      out.push_back({UBKind::SignedOverflow, d.icmp(Pred::Ne, wide, d.sext(narrow, 2 * w))});
      return true;
    }
    case Opc::CheckSNegOvf: {
      unsigned w = wd(a[0]);
      out.push_back({UBKind::SignedOverflow, d.icmp(Pred::Eq, a[0], d.smin(w))});
      return true;
    }
    case Opc::CheckFieldOob: {
      // a[0] is the index into a fixed-size array field; the field's declared element count is the 'n' attribute
      // (a compile-time constant from the C type, not derived from the backing object's allocation size -- this is
      // deliberately independent of core.check.oob / Memory.h's CheckOob, which only bounds the whole backing
      // object and cannot see an individual field's own array length; see DESIGN.md P1 gap fix).
      unsigned w = wd(a[0]);
      uint64_t n = static_cast<uint64_t>(op.intAttr("n"));
      Val nv = d.constant(llvm::APInt(w, n));
      out.push_back({UBKind::FieldOob, d.icmp(Pred::Uge, a[0], nv)});
      return true;
    }
    default:
      return false;
  }
}

}  // namespace hlir

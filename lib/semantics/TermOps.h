// Private. Pure SMT-term construction for the core operators (no path state): shared by SymbolicDomain and the taint
// domain, so both build exactly the same terms. Values are bit-vector terms (bool = 1-bit vector).
#pragma once
#include <string>

#include "Pred.h"
#include "hlir/smt/Term.h"
#include "llvm/ADT/SmallString.h"

namespace hlir {

class TermOps {
 public:
  using Val = smt::TermRef;
  explicit TermOps(smt::TermManager &tm) : tm_(tm) {}
  smt::TermManager &tm() { return tm_; }

  // arrays (QF_ABV): memory objects with symbolic offsets
  Val arrConst(unsigned idxWidth, Val elem) { return tm_.mkConstArray(idxWidth, elem); }
  Val arrVar(const std::string &name, unsigned idxWidth, unsigned elemWidth) { return tm_.arrVar(name, idxWidth, elemWidth); }
  Val arrSelect(Val a, Val i) { return tm_.mkSelect(a, i); }
  Val arrStore(Val a, Val i, Val v) { return tm_.mkStore(a, i, v); }

  // ---- values
  static unsigned width(Val v) { return v->sort.width; }
  Val constant(const llvm::APInt &v) { return tm_.bvConst(v); }
  Val zero(unsigned w) { return tm_.bvConst(llvm::APInt(w, 0)); }
  Val allOnes(unsigned w) { return tm_.bvConst(llvm::APInt::getAllOnes(w)); }
  Val smin(unsigned w) { return tm_.bvConst(llvm::APInt::getSignedMinValue(w)); }

  Val add(Val a, Val b) { return tm_.mkBin(smt::Kind::BvAdd, a, b); }
  Val sub(Val a, Val b) { return tm_.mkBin(smt::Kind::BvSub, a, b); }
  Val mul(Val a, Val b) { return tm_.mkBin(smt::Kind::BvMul, a, b); }
  Val udiv(Val a, Val b) { return tm_.mkBin(smt::Kind::BvUdiv, a, b); }
  Val sdiv(Val a, Val b) { return tm_.mkBin(smt::Kind::BvSdiv, a, b); }
  Val urem(Val a, Val b) { return tm_.mkBin(smt::Kind::BvUrem, a, b); }
  Val srem(Val a, Val b) { return tm_.mkBin(smt::Kind::BvSrem, a, b); }
  Val shl(Val a, Val b) { return tm_.mkBin(smt::Kind::BvShl, a, b); }
  Val lshr(Val a, Val b) { return tm_.mkBin(smt::Kind::BvLshr, a, b); }
  Val ashr(Val a, Val b) { return tm_.mkBin(smt::Kind::BvAshr, a, b); }
  Val xor_(Val a, Val b) { return tm_.mkBin(smt::Kind::BvXor, a, b); }
  // 1-bit and/or/not are kept as SMT booleans so path conditions stay readable and cheap for the solver.
  Val and_(Val a, Val b) { return width(a) == 1 ? tm_.fromBool(tm_.mkAnd(tm_.toBool(a), tm_.toBool(b))) : tm_.mkBin(smt::Kind::BvAnd, a, b); }
  Val or_(Val a, Val b) { return width(a) == 1 ? tm_.fromBool(tm_.mkOr(tm_.toBool(a), tm_.toBool(b))) : tm_.mkBin(smt::Kind::BvOr, a, b); }
  Val not_(Val a) { return width(a) == 1 ? tm_.fromBool(tm_.mkNot(tm_.toBool(a))) : tm_.mkUn(smt::Kind::BvNot, a); }
  Val neg(Val a) { return tm_.mkUn(smt::Kind::BvNeg, a); }
  Val zext(Val a, unsigned w) { return tm_.mkZExt(a, w); }
  Val sext(Val a, unsigned w) { return tm_.mkSExt(a, w); }
  Val trunc(Val a, unsigned w) { return tm_.mkExtract(a, w - 1, 0); }
  Val extract(Val a, unsigned hi, unsigned lo) { return tm_.mkExtract(a, hi, lo); }
  Val concat(Val hi, Val lo) { return tm_.mkConcat(hi, lo); }

  Val icmp(Pred p, Val a, Val b) {
    using smt::Kind;
    smt::TermRef r = nullptr;
    switch (p) {
      case Pred::Eq: r = tm_.mkEq(a, b); break;
      case Pred::Ne: r = tm_.mkNot(tm_.mkEq(a, b)); break;
      case Pred::Ult: r = tm_.mkCmp(Kind::Ult, a, b); break;
      case Pred::Ule: r = tm_.mkCmp(Kind::Ule, a, b); break;
      case Pred::Ugt: r = tm_.mkCmp(Kind::Ult, b, a); break;
      case Pred::Uge: r = tm_.mkCmp(Kind::Ule, b, a); break;
      case Pred::Slt: r = tm_.mkCmp(Kind::Slt, a, b); break;
      case Pred::Sle: r = tm_.mkCmp(Kind::Sle, a, b); break;
      case Pred::Sgt: r = tm_.mkCmp(Kind::Slt, b, a); break;
      case Pred::Sge: r = tm_.mkCmp(Kind::Sle, b, a); break;
    }
    return tm_.fromBool(r);
  }
  Val select(Val c, Val a, Val b) { return tm_.mkIte(tm_.toBool(c), a, b); }

  std::string str(Val v, bool isBool = false) {
    if (v->kind == smt::Kind::BvConst) {
      if (isBool) return v->value.getBoolValue() ? "true" : "false";
      llvm::SmallString<40> s;
      v->value.toStringSigned(s);
      return std::string(s);
    }
    return "<sym#" + std::to_string(v->id) + ">";
  }

 protected:
  smt::TermManager &tm_;
};

}  // namespace hlir

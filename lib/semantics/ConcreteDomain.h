// Private. Concrete value domain: bit-vectors as llvm::APInt, bool = width 1.
//
// The arithmetic here follows SMT-LIB's total-function conventions exactly (division by zero, oversized shifts),
// because the symbolic domain must agree bit-for-bit (DESIGN.md §18.3). Whether such an operation is *undefined*
// in the source language is decided by the explicit core.check.* ops, never here.
#pragma once
#include <optional>
#include <string>

#include "Pred.h"
#include "hlir/semantics/Env.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"

namespace hlir {

struct ConcreteDomain {
  using Val = llvm::APInt;

  // Memory-model support (see Memory.h). Concrete execution is exact: it never approximates.
  static constexpr bool kExact = true;
  static constexpr bool kArrays = false;
  // Evidence only: answer "is this symbolic" / "what concrete value does it carry" WITHOUT the
  // concretisation side effect constValue() has on the concolic domain (it counts a followed tainted
  // pointer, which would make the concretized_pointer assumption count reads that are only being
  // reported). Used by Memory::objEvidence (DESIGN.md §22.369).
  static bool isSymbolicVal(const Val &) { return false; }
  static std::optional<llvm::APInt> peekVal(const Val &v) { return v; }
  static std::optional<llvm::APInt> constValue(const Val &v) { return v; }
  static bool same(const Val &a, const Val &b) { return a == b; }
  static bool asIte(const Val &, Val &, Val &, Val &) { return false; }
  static Val fresh(const std::string &, unsigned w) { return llvm::APInt(w, 0); }
  static Val input(Env &env, const std::string &name, unsigned w) { return env.input(name, w); }  // indeterminate bytes read as 0
  static Val harnessInput(Env &env, const std::string &name, unsigned w) { return env.input(name, w); }

  // Instrumentation hooks (no-ops here; the taint domain uses them to classify functions and build its slice).
  static constexpr bool kTaint = false;
  static bool isTainted(const Val &) { return false; }
  static void noteSelectedAddress() {}  // see TaintDomain::noteSelectedAddress (DESIGN.md Sec.22.487)
  static bool isAttackerControlled(const Val &) { return false; }
  static bool onlyFrontier(const Val &) { return false; }
  static void beginOp(const Op &) {}
  static void setSetupRegion(bool) {}
  static std::optional<Val> freezeVal(const Val &v) { return v; }
  static void onCall(const Function &) {}
  static void onReturn(const Function &, const Val *) {}
  static void noteStore(const Val &) {}
  static void noteKill() {}
  static Val modelInput(Env &env, const std::string &name, unsigned w, const std::string &, const std::optional<llvm::APInt> & = std::nullopt) { return env.input(name, w); }
  static Val opaqueDerived(const Val &cur, const std::vector<Val> &, const std::string &) { return cur; }
  static Val clearTaint(const Val &v) { return v; }
  template <class MakeFinding> static void taintSink(const Val &, MakeFinding &&) {}

  static unsigned width(const Val &v) { return v.getBitWidth(); }
  static Val constant(const llvm::APInt &v) { return v; }
  static Val zero(unsigned w) { return llvm::APInt(w, 0); }
  static Val allOnes(unsigned w) { return llvm::APInt::getAllOnes(w); }
  static Val smin(unsigned w) { return llvm::APInt::getSignedMinValue(w); }

  static Val add(const Val &a, const Val &b) { return a + b; }
  static Val sub(const Val &a, const Val &b) { return a - b; }
  static Val mul(const Val &a, const Val &b) { return a * b; }
  static Val and_(const Val &a, const Val &b) { return a & b; }
  static Val or_(const Val &a, const Val &b) { return a | b; }
  static Val xor_(const Val &a, const Val &b) { return a ^ b; }
  static Val not_(const Val &a) { return ~a; }
  static Val neg(const Val &a) { return -a; }

  // SMT-LIB: bvudiv x 0 = all ones; bvurem x 0 = x.
  static Val udiv(const Val &a, const Val &b) { return b.isZero() ? allOnes(a.getBitWidth()) : a.udiv(b); }
  static Val urem(const Val &a, const Val &b) { return b.isZero() ? a : a.urem(b); }
  // SMT-LIB bvsdiv/bvsrem (defined through unsigned division of magnitudes):
  //   sdiv x 0 = (x >= 0 ? -1 : 1);  smin / -1 = smin;  srem x 0 = x;  x % -1 = 0.
  static Val sdiv(const Val &a, const Val &b) {
    unsigned w = a.getBitWidth();
    if (b.isZero()) return a.isNegative() ? llvm::APInt(w, 1) : allOnes(w);
    if (b.isAllOnes()) return -a;  // wraps for smin
    return a.sdiv(b);
  }
  static Val srem(const Val &a, const Val &b) {
    if (b.isZero()) return a;
    if (b.isAllOnes()) return zero(a.getBitWidth());
    return a.srem(b);
  }

  // SMT-LIB: shifting by >= width gives 0 (shl, lshr) or the sign fill (ashr).
  static Val shl(const Val &a, const Val &s) { return s.uge(a.getBitWidth()) ? zero(a.getBitWidth()) : a.shl(s); }
  static Val lshr(const Val &a, const Val &s) { return s.uge(a.getBitWidth()) ? zero(a.getBitWidth()) : a.lshr(s); }
  static Val ashr(const Val &a, const Val &s) {
    if (s.uge(a.getBitWidth())) return a.isNegative() ? allOnes(a.getBitWidth()) : zero(a.getBitWidth());
    return a.ashr(s);
  }

  static Val zext(const Val &a, unsigned w) { return a.zext(w); }
  static Val sext(const Val &a, unsigned w) { return a.sext(w); }
  static Val trunc(const Val &a, unsigned w) { return a.trunc(w); }
  static Val extract(const Val &a, unsigned hi, unsigned lo) { return a.extractBits(hi - lo + 1, lo); }
  static Val concat(const Val &hi, const Val &lo) { return hi.concat(lo); }

  // Result has width 1.
  static Val icmp(Pred p, const Val &a, const Val &b) {
    bool r = false;
    switch (p) {
      case Pred::Eq: r = a == b; break;
      case Pred::Ne: r = a != b; break;
      case Pred::Ult: r = a.ult(b); break;
      case Pred::Ule: r = a.ule(b); break;
      case Pred::Ugt: r = a.ugt(b); break;
      case Pred::Uge: r = a.uge(b); break;
      case Pred::Slt: r = a.slt(b); break;
      case Pred::Sle: r = a.sle(b); break;
      case Pred::Sgt: r = a.sgt(b); break;
      case Pred::Sge: r = a.sge(b); break;
    }
    return llvm::APInt(1, r);
  }
  static Val select(const Val &c, const Val &a, const Val &b) { return c.getBoolValue() ? a : b; }

  // Concrete execution always knows which way a branch goes. (A symbolic domain needs a different driver that forks.)
  static bool decide(const Val &cond) { return cond.getBoolValue(); }
  // `cond` (width 1) true means a property is violated on this path. `mkFinding` describes it for domains that record
  // findings; concrete execution only needs the answer.
  template <class MakeFinding>
  static bool violated(const Val &cond, MakeFinding &&) { return cond.getBoolValue(); }
  // Adds `cond` to the path's assumptions; false if the path becomes infeasible.
  static bool assume(const Val &cond) { return cond.getBoolValue(); }
  static bool assumeConcretisation(const Val &cond) { return cond.getBoolValue(); }
  static Val nondet(Env &env, const Op &op, unsigned width) { return env.nondet(op, width); }

  static std::string str(const Val &v, bool isBool = false) {
    if (isBool) return v.getBoolValue() ? "true" : "false";
    llvm::SmallString<40> s;
    v.toStringSigned(s);
    return std::string(s);
  }
};

}  // namespace hlir

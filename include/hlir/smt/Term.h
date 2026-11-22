// STABLE. Solver-independent SMT terms (QF_BV with booleans), hash-consed, with built-in evaluation.
// This is the only term representation the rest of the system sees; solvers (z3, cvc5, enumeration ...) live behind
// smt::Solver and never leak their own types (docs/ARCHITECTURE.md §3).
//
// Semantics are exactly SMT-LIB's FixedSizeBitVectors theory, including the total-function conventions for division
// by zero and oversized shifts. `evalTerm` is an independent implementation of that theory, used both for constant
// folding and as the oracle in the interpreter == eval == solver consistency tests.
#pragma once
#include <deque>
#include <map>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "llvm/ADT/APInt.h"

namespace hlir::smt {

struct Sort {
  bool isBool = false;
  unsigned width = 0;     // bit-vector width (the element width for arrays); 0 for Bool
  bool isArray = false;   // (Array (_ BitVec idxWidth) (_ BitVec width))
  unsigned idxWidth = 0;
  static Sort boolean() { return {true, 0, false, 0}; }
  static Sort bv(unsigned w) { return {false, w, false, 0}; }
  static Sort array(unsigned idxW, unsigned elemW) { return {false, elemW, true, idxW}; }
  bool isBv() const { return !isBool && !isArray; }
  bool operator==(const Sort &o) const { return isBool == o.isBool && width == o.width && isArray == o.isArray && idxWidth == o.idxWidth; }
  bool operator!=(const Sort &o) const { return !(*this == o); }
};

enum class Kind : uint8_t {
  // leaves
  BoolConst, BvConst, Var,
  // boolean
  Not, And, Or, Ite /* cond ? a : b, over BV or Bool */, Eq /* over BV, result Bool */,
  // bit-vector comparisons (result Bool); the other orderings are expressed by swapping operands / negation
  Ult, Ule, Slt, Sle,
  // bit-vector arithmetic / bitwise (same width in, same width out)
  BvAdd, BvSub, BvMul, BvUdiv, BvUrem, BvSdiv, BvSrem, BvAnd, BvOr, BvXor, BvShl, BvLshr, BvAshr, BvNot, BvNeg,
  // width changing
  ZExt, SExt, Extract, Concat,
  // arrays (QF_ABV): Select(arr, idx) -> element; Store(arr, idx, val) -> arr; ConstArray(val) -> arr (all elements equal)
  Select, Store, ConstArray,
};
const char *kindName(Kind k);

class Term {
 public:
  Kind kind;
  Sort sort;
  std::vector<const Term *> args;
  llvm::APInt value;      // BoolConst (width 1) / BvConst
  std::string name;       // Var
  unsigned hi = 0, lo = 0;  // Extract; ZExt/SExt use `hi` as the target width
  uint32_t id = 0;        // unique inside the owning TermManager; creation order is a topological order
  uint32_t mgr = 0;       // serial number of the owning TermManager (unique for the life of the process): (mgr, id) names a term forever

  bool isConst() const { return kind == Kind::BoolConst || kind == Kind::BvConst; }
  bool isTrue() const { return kind == Kind::BoolConst && value.getBoolValue(); }
  bool isFalse() const { return kind == Kind::BoolConst && !value.getBoolValue(); }
};
using TermRef = const Term *;

// Owns and interns terms. Structurally equal terms are the same pointer. Not thread-safe.
class TermManager {
 public:
  TermManager();
  ~TermManager();
  TermManager(const TermManager &) = delete;
  TermManager &operator=(const TermManager &) = delete;

  // leaves
  TermRef boolConst(bool b);
  TermRef bvConst(const llvm::APInt &v);
  TermRef bvConst(unsigned width, uint64_t v) { return bvConst(llvm::APInt(width, v)); }
  TermRef bvVar(const std::string &name, unsigned width);  // same name+width => same term; same name, other width => asserts

  // boolean
  TermRef mkNot(TermRef a);
  TermRef mkAnd(TermRef a, TermRef b);
  TermRef mkAnd(const std::vector<TermRef> &v);
  TermRef mkOr(TermRef a, TermRef b);
  TermRef mkImplies(TermRef a, TermRef b) { return mkOr(mkNot(a), b); }
  TermRef mkIte(TermRef c, TermRef a, TermRef b);
  TermRef mkEq(TermRef a, TermRef b);
  TermRef mkCmp(Kind k, TermRef a, TermRef b);  // Ult/Ule/Slt/Sle

  // bit-vector
  TermRef mkBin(Kind k, TermRef a, TermRef b);  // BvAdd .. BvAshr
  TermRef mkUn(Kind k, TermRef a);              // BvNot, BvNeg
  TermRef mkZExt(TermRef a, unsigned toWidth);
  TermRef mkSExt(TermRef a, unsigned toWidth);
  TermRef mkExtract(TermRef a, unsigned hi, unsigned lo);
  TermRef mkConcat(TermRef hi, TermRef lo);

  // arrays
  TermRef arrVar(const std::string &name, unsigned idxWidth, unsigned elemWidth);
  TermRef mkConstArray(unsigned idxWidth, TermRef elem);
  TermRef mkSelect(TermRef arr, TermRef idx);
  TermRef mkStore(TermRef arr, TermRef idx, TermRef val);

  // Bridges between the interpreter's "bool = 1-bit vector" convention and SMT Bool.
  TermRef toBool(TermRef bv1);    // bv1 == #b1, simplified
  TermRef fromBool(TermRef b);    // ite(b, #b1, #b0), simplified

  uint32_t serial() const { return serial_; }
  size_t size() const { return all_.size(); }
  const std::vector<TermRef> &variables() const { return vars_; }

 private:
  TermRef intern(Term &&t);
  uint32_t serial_;
  struct Impl;
  std::unique_ptr<Impl> impl_;
  std::deque<Term> all_;
  std::vector<TermRef> vars_;
};

// A value assignment for variables, keyed by variable name.
using Assignment = std::map<std::string, llvm::APInt>;

// Evaluates a term under an assignment (variables missing from it evaluate to 0; array variables are all-zero arrays).
// Bool results are width-1. The root must not be array-sorted (use Select to look inside an array).
llvm::APInt evalTerm(TermRef t, const Assignment &a);

// Applies one operator to already-evaluated arguments (the exact SMT-LIB semantics). Used for constant folding.
llvm::APInt evalApply(Kind k, unsigned hi, unsigned lo, unsigned resultWidth, const std::vector<llvm::APInt> &args);

// Collects the variables occurring in `t`.
void collectVars(TermRef t, std::vector<TermRef> &out);

// Same result as collectVars(t, out), but every term node visited along the way (not just `t` itself) is memoized
// into `memo`, keyed by node identity. Safe to reuse `memo` across many calls with different roots over the same
// TermManager (terms are immutable and hash-consed, so a node's variable set never changes): a shared memo turns
// repeated calls over overlapping DAGs (e.g. successive loop-unrolled path conditions, which share long common
// prefixes) from O(sum of per-root reachable subgraph sizes) into O(total distinct subgraph size), since each node
// is only ever expanded once. Plain collectVars (above) stays as-is for call sites that only ever ask once per term.
void collectVarsMemo(TermRef t, std::unordered_map<TermRef, std::vector<TermRef>> &memo);

}  // namespace hlir::smt

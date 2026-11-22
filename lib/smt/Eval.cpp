// Independent implementation of the SMT-LIB FixedSizeBitVectors semantics. Division and remainder are written from
// the standard's definitions (via unsigned division of magnitudes), deliberately NOT sharing code with the
// interpreter's ConcreteDomain: agreement between the two is a test, not an assumption.
#include <cassert>
#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "hlir/smt/Term.h"

namespace hlir::smt {

using llvm::APInt;

const char *kindName(Kind k) {
  switch (k) {
    case Kind::BoolConst: return "bool";
    case Kind::BvConst: return "bv";
    case Kind::Var: return "var";
    case Kind::Not: return "not";
    case Kind::And: return "and";
    case Kind::Or: return "or";
    case Kind::Ite: return "ite";
    case Kind::Eq: return "=";
    case Kind::Ult: return "bvult";
    case Kind::Ule: return "bvule";
    case Kind::Slt: return "bvslt";
    case Kind::Sle: return "bvsle";
    case Kind::BvAdd: return "bvadd";
    case Kind::BvSub: return "bvsub";
    case Kind::BvMul: return "bvmul";
    case Kind::BvUdiv: return "bvudiv";
    case Kind::BvUrem: return "bvurem";
    case Kind::BvSdiv: return "bvsdiv";
    case Kind::BvSrem: return "bvsrem";
    case Kind::BvAnd: return "bvand";
    case Kind::BvOr: return "bvor";
    case Kind::BvXor: return "bvxor";
    case Kind::BvShl: return "bvshl";
    case Kind::BvLshr: return "bvlshr";
    case Kind::BvAshr: return "bvashr";
    case Kind::BvNot: return "bvnot";
    case Kind::BvNeg: return "bvneg";
    case Kind::ZExt: return "zero_extend";
    case Kind::SExt: return "sign_extend";
    case Kind::Extract: return "extract";
    case Kind::Concat: return "concat";
    case Kind::Select: return "select";
    case Kind::Store: return "store";
    case Kind::ConstArray: return "const-array";
  }
  return "?";
}

static APInt bit(bool b) { return APInt(1, b ? 1 : 0); }

// bvudiv / bvurem per the standard: division by zero gives all ones / the dividend.
static APInt bvudiv(const APInt &s, const APInt &t) { return t.isZero() ? APInt::getAllOnes(s.getBitWidth()) : s.udiv(t); }
static APInt bvurem(const APInt &s, const APInt &t) { return t.isZero() ? s : s.urem(t); }

static APInt bvsdiv(const APInt &s, const APInt &t) {
  bool ms = s.isNegative(), mt = t.isNegative();
  if (!ms && !mt) return bvudiv(s, t);
  if (ms && !mt) return -bvudiv(-s, t);
  if (!ms && mt) return -bvudiv(s, -t);
  return bvudiv(-s, -t);
}
static APInt bvsrem(const APInt &s, const APInt &t) {
  bool ms = s.isNegative(), mt = t.isNegative();
  if (!ms && !mt) return bvurem(s, t);
  if (ms && !mt) return -bvurem(-s, t);
  if (!ms && mt) return bvurem(s, -t);
  return -bvurem(-s, -t);
}

// Shift amounts >= width: shl/lshr give 0, ashr gives the sign fill. Done bit by bit-free: via the shift amount as unsigned.
static APInt shiftBy(Kind k, const APInt &s, const APInt &t) {
  unsigned w = s.getBitWidth();
  bool big = t.uge(w);
  switch (k) {
    case Kind::BvShl: return big ? APInt(w, 0) : s.shl(t.getZExtValue());
    case Kind::BvLshr: return big ? APInt(w, 0) : s.lshr(t.getZExtValue());
    default: return big ? (s.isNegative() ? APInt::getAllOnes(w) : APInt(w, 0)) : s.ashr(t.getZExtValue());
  }
}

APInt evalApply(Kind k, unsigned hi, unsigned lo, unsigned resultWidth, const std::vector<APInt> &a) {
  switch (k) {
    case Kind::Not: return bit(!a[0].getBoolValue());
    case Kind::And: { bool r = true; for (auto &x : a) r = r && x.getBoolValue(); return bit(r); }
    case Kind::Or: { bool r = false; for (auto &x : a) r = r || x.getBoolValue(); return bit(r); }
    case Kind::Ite: return a[0].getBoolValue() ? a[1] : a[2];
    case Kind::Eq: return bit(a[0] == a[1]);
    case Kind::Ult: return bit(a[0].ult(a[1]));
    case Kind::Ule: return bit(a[0].ule(a[1]));
    case Kind::Slt: return bit(a[0].slt(a[1]));
    case Kind::Sle: return bit(a[0].sle(a[1]));
    case Kind::BvAdd: return a[0] + a[1];
    case Kind::BvSub: return a[0] - a[1];
    case Kind::BvMul: return a[0] * a[1];
    case Kind::BvUdiv: return bvudiv(a[0], a[1]);
    case Kind::BvUrem: return bvurem(a[0], a[1]);
    case Kind::BvSdiv: return bvsdiv(a[0], a[1]);
    case Kind::BvSrem: return bvsrem(a[0], a[1]);
    case Kind::BvAnd: return a[0] & a[1];
    case Kind::BvOr: return a[0] | a[1];
    case Kind::BvXor: return a[0] ^ a[1];
    case Kind::BvShl: case Kind::BvLshr: case Kind::BvAshr: return shiftBy(k, a[0], a[1]);
    case Kind::BvNot: return ~a[0];
    case Kind::BvNeg: return -a[0];
    case Kind::ZExt: return a[0].zext(resultWidth);
    case Kind::SExt: return a[0].sext(resultWidth);
    case Kind::Extract: return a[0].extractBits(hi - lo + 1, lo);
    case Kind::Concat: return a[0].concat(a[1]);
    case Kind::BoolConst: case Kind::BvConst: case Kind::Var: case Kind::Select: case Kind::Store: case Kind::ConstArray: break;
  }
  assert(false && "evalApply on a leaf");
  return APInt(1, 0);
}

namespace {

// Array values: a default element plus point overrides (index widths up to 64 bits).
struct ArrV {
  APInt dflt;
  std::map<uint64_t, APInt> m;
  APInt at(const APInt &i) const {
    auto it = m.find(i.getZExtValue());
    return it == m.end() ? dflt : it->second;
  }
};
struct EV {
  APInt bv;
  std::shared_ptr<ArrV> arr;
};

}  // namespace

APInt evalTerm(TermRef root, const Assignment &asg) {
  std::unordered_map<const Term *, EV> memo;
  // Iterative post-order: terms are created after their arguments, so ids are a topological order.
  std::vector<TermRef> stack{root};
  while (!stack.empty()) {
    TermRef t = stack.back();
    if (memo.count(t)) { stack.pop_back(); continue; }
    bool ready = true;
    for (auto *c : t->args)
      if (!memo.count(c)) { stack.push_back(c); ready = false; }
    if (!ready) continue;
    stack.pop_back();
    switch (t->kind) {
      case Kind::BoolConst: case Kind::BvConst: memo.emplace(t, EV{t->value, nullptr}); break;
      case Kind::Var: {
        if (t->sort.isArray) {
          auto a = std::make_shared<ArrV>();
          a->dflt = APInt(t->sort.width, 0);
          memo.emplace(t, EV{APInt(1, 0), a});
          break;
        }
        auto it = asg.find(t->name);
        unsigned w = t->sort.width;
        memo.emplace(t, EV{it == asg.end() ? APInt(w, 0) : it->second.zextOrTrunc(w), nullptr});
        break;
      }
      case Kind::ConstArray: {
        auto a = std::make_shared<ArrV>();
        a->dflt = memo.at(t->args[0]).bv;
        memo.emplace(t, EV{APInt(1, 0), a});
        break;
      }
      case Kind::Store: {
        auto a = std::make_shared<ArrV>(*memo.at(t->args[0]).arr);
        a->m[memo.at(t->args[1]).bv.getZExtValue()] = memo.at(t->args[2]).bv;
        memo.emplace(t, EV{APInt(1, 0), a});
        break;
      }
      case Kind::Select: memo.emplace(t, EV{memo.at(t->args[0]).arr->at(memo.at(t->args[1]).bv), nullptr}); break;
      case Kind::Ite:
        if (t->sort.isArray) { memo.emplace(t, memo.at(t->args[0]).bv.getBoolValue() ? memo.at(t->args[1]) : memo.at(t->args[2])); break; }
        [[fallthrough]];
      default: {
        std::vector<APInt> av;
        for (auto *c : t->args) av.push_back(memo.at(c).bv);
        memo.emplace(t, EV{evalApply(t->kind, t->hi, t->lo, t->sort.isBool ? 1 : t->sort.width, av), nullptr});
      }
    }
  }
  assert(!root->sort.isArray && "evalTerm of an array-sorted term");
  return memo.at(root).bv;
}

void collectVars(TermRef root, std::vector<TermRef> &out) {
  std::unordered_map<const Term *, bool> seen;
  std::vector<TermRef> stack{root};
  while (!stack.empty()) {
    TermRef t = stack.back();
    stack.pop_back();
    if (!seen.emplace(t, true).second) continue;
    if (t->kind == Kind::Var) out.push_back(t);
    for (auto *c : t->args) stack.push_back(c);
  }
}

// Iterative post-order DP: a node's variable set is the union of its args' (already-memoized) sets, plus itself if
// it's a Var. Each node is expanded (the union computed) at most once per call to a fresh root that doesn't share
// `memo` with a prior caller -- when `memo` is reused across many roots over the same overlapping DAG (the intended
// use), a node already resolved by an earlier root is just a lookup. (A node can still be pushed as an unexpanded
// child more than once by distinct parents before its first expansion completes; the `memo.count(t)` guards make
// any repeat expansion a harmless no-op on top of the first `emplace`, bounded by edge count, not node count
// squared.)
void collectVarsMemo(TermRef root, std::unordered_map<TermRef, std::vector<TermRef>> &memo) {
  if (memo.count(root)) return;
  std::vector<std::pair<TermRef, bool>> stack{{root, false}};
  while (!stack.empty()) {
    auto [t, expanded] = stack.back();
    stack.pop_back();
    if (memo.count(t)) continue;
    if (!expanded) {
      stack.push_back({t, true});
      for (auto *c : t->args)
        if (!memo.count(c)) stack.push_back({c, false});
      continue;
    }
    std::vector<TermRef> v;
    std::unordered_set<TermRef> dedup;
    if (t->kind == Kind::Var) { v.push_back(t); dedup.insert(t); }
    for (auto *c : t->args)
      for (auto *x : memo.at(c))
        if (dedup.insert(x).second) v.push_back(x);
    memo.emplace(t, std::move(v));
  }
}

}  // namespace hlir::smt

#include <atomic>
#include "hlir/smt/Term.h"

#include <cassert>
#include <functional>
#include <unordered_map>
#include <unordered_set>

#include "llvm/ADT/Hashing.h"

namespace hlir::smt {

using llvm::APInt;

// Hash-consing identity: two terms are the same iff kind, sort, arguments (already interned, so compared by pointer),
// hi/lo, the value of a constant and the name of a variable all agree. Hashed and compared field by field: this used to
// be a std::string key built with to_string/concatenation for every term constructed, which made interning (and the
// allocations it caused) the largest single cost of the concolic interpreter (docs/DESIGN.md Sec.22.337).
static bool hasValue(Kind k) { return k == Kind::BoolConst || k == Kind::BvConst; }

struct TermHash {
  size_t operator()(TermRef t) const {
    llvm::hash_code h = llvm::hash_combine(static_cast<unsigned>(t->kind), t->sort.isBool, t->sort.width, t->sort.isArray, t->sort.idxWidth,
                                           t->hi, t->lo, llvm::hash_combine_range(t->args.begin(), t->args.end()));
    if (hasValue(t->kind)) h = llvm::hash_combine(h, llvm::hash_value(t->value));
    if (t->kind == Kind::Var) h = llvm::hash_combine(h, llvm::hash_value(t->name));
    return static_cast<size_t>(h);
  }
};

struct TermEq {
  bool operator()(TermRef a, TermRef b) const {
    if (a->kind != b->kind || a->sort != b->sort || a->hi != b->hi || a->lo != b->lo || a->args != b->args) return false;
    if (hasValue(a->kind) && !(a->value.getBitWidth() == b->value.getBitWidth() && a->value == b->value)) return false;
    if (a->kind == Kind::Var && a->name != b->name) return false;
    return true;
  }
};

struct TermManager::Impl {
  std::unordered_set<TermRef, TermHash, TermEq> table;
  std::unordered_map<std::string, TermRef> varsByName;
};

static std::atomic<uint32_t> g_managerSerial{0};
TermManager::TermManager() : serial_(++g_managerSerial), impl_(new Impl) {}
TermManager::~TermManager() = default;

TermRef TermManager::intern(Term &&t) {
  auto it = impl_->table.find(&t);  // probed with the candidate itself: no key is materialised
  if (it != impl_->table.end()) return *it;
  t.id = static_cast<uint32_t>(all_.size());
  t.mgr = serial_;
  all_.push_back(std::move(t));
  TermRef r = &all_.back();
  impl_->table.insert(r);
  return r;
}

static Term make(Kind k, Sort s, std::vector<TermRef> args = {}) {
  Term t;
  t.kind = k;
  t.sort = s;
  t.args = std::move(args);
  return t;
}

TermRef TermManager::boolConst(bool b) {
  Term t = make(Kind::BoolConst, Sort::boolean());
  t.value = APInt(1, b ? 1 : 0);
  return intern(std::move(t));
}

TermRef TermManager::bvConst(const APInt &v) {
  Term t = make(Kind::BvConst, Sort::bv(v.getBitWidth()));
  t.value = v;
  return intern(std::move(t));
}

TermRef TermManager::bvVar(const std::string &name, unsigned width) {
  auto it = impl_->varsByName.find(name);
  if (it != impl_->varsByName.end()) {
    assert(it->second->sort.width == width && "variable redeclared with a different width");
    return it->second;
  }
  Term t = make(Kind::Var, Sort::bv(width));
  t.name = name;
  TermRef r = intern(std::move(t));
  impl_->varsByName.emplace(name, r);
  vars_.push_back(r);
  return r;
}

// Folds `k(args)` when every argument is constant. Returns nullptr otherwise.
static TermRef foldConst(TermManager &m, Kind k, Sort s, unsigned hi, unsigned lo, const std::vector<TermRef> &args) {
  std::vector<APInt> vals;
  for (auto *a : args) {
    if (!a->isConst()) return nullptr;
    vals.push_back(a->value);
  }
  APInt r = evalApply(k, hi, lo, s.isBool ? 1 : s.width, vals);
  return s.isBool ? m.boolConst(r.getBoolValue()) : m.bvConst(r);
}

// ---------------------------------------------------------------- boolean
TermRef TermManager::mkNot(TermRef a) {
  assert(a->sort.isBool);
  if (a->isConst()) return boolConst(!a->value.getBoolValue());
  if (a->kind == Kind::Not) return a->args[0];
  return intern(make(Kind::Not, Sort::boolean(), {a}));
}

TermRef TermManager::mkAnd(TermRef a, TermRef b) {
  assert(a->sort.isBool && b->sort.isBool);
  if (a->isFalse() || b->isFalse()) return boolConst(false);
  if (a->isTrue()) return b;
  if (b->isTrue()) return a;
  if (a == b) return a;
  if (a->id > b->id) std::swap(a, b);  // canonical operand order
  return intern(make(Kind::And, Sort::boolean(), {a, b}));
}

TermRef TermManager::mkAnd(const std::vector<TermRef> &v) {
  TermRef r = boolConst(true);
  for (auto *t : v) r = mkAnd(r, t);
  return r;
}

TermRef TermManager::mkOr(TermRef a, TermRef b) {
  assert(a->sort.isBool && b->sort.isBool);
  if (a->isTrue() || b->isTrue()) return boolConst(true);
  if (a->isFalse()) return b;
  if (b->isFalse()) return a;
  if (a == b) return a;
  if (a->id > b->id) std::swap(a, b);
  return intern(make(Kind::Or, Sort::boolean(), {a, b}));
}

TermRef TermManager::mkIte(TermRef c, TermRef a, TermRef b) {
  assert(c->sort.isBool && a->sort == b->sort);
  if (c->isTrue()) return a;
  if (c->isFalse()) return b;
  if (a == b) return a;
  if (c->kind == Kind::Not) return mkIte(c->args[0], b, a);
  if (a->sort.isBool) {  // boolean ite as connectives keeps the term language small for solvers/printers
    if (a->isTrue() && b->isFalse()) return c;
    if (a->isFalse() && b->isTrue()) return mkNot(c);
  }
  return intern(make(Kind::Ite, a->sort, {c, a, b}));
}

TermRef TermManager::mkEq(TermRef a, TermRef b) {
  assert(!a->sort.isBool && a->sort == b->sort);
  if (a == b) return boolConst(true);
  if (TermRef f = foldConst(*this, Kind::Eq, Sort::boolean(), 0, 0, {a, b})) return f;
  if (a->id > b->id) std::swap(a, b);
  return intern(make(Kind::Eq, Sort::boolean(), {a, b}));
}

TermRef TermManager::mkCmp(Kind k, TermRef a, TermRef b) {
  assert(k == Kind::Ult || k == Kind::Ule || k == Kind::Slt || k == Kind::Sle);
  assert(a->sort == b->sort && !a->sort.isBool);
  if (TermRef f = foldConst(*this, k, Sort::boolean(), 0, 0, {a, b})) return f;
  if (a == b) return boolConst(k == Kind::Ule || k == Kind::Sle);
  return intern(make(k, Sort::boolean(), {a, b}));
}

// ---------------------------------------------------------------- bit-vector
static bool isConstVal(TermRef t, uint64_t v) { return t->kind == Kind::BvConst && t->value == v; }
static bool isAllOnes(TermRef t) { return t->kind == Kind::BvConst && t->value.isAllOnes(); }

TermRef TermManager::mkBin(Kind k, TermRef a, TermRef b) {
  assert(a->sort == b->sort && !a->sort.isBool);
  Sort s = a->sort;
  if (TermRef f = foldConst(*this, k, s, 0, 0, {a, b})) return f;
  bool comm = k == Kind::BvAdd || k == Kind::BvMul || k == Kind::BvAnd || k == Kind::BvOr || k == Kind::BvXor;
  if (comm && a->id > b->id) std::swap(a, b);
  switch (k) {
    case Kind::BvAdd: if (isConstVal(a, 0)) return b; if (isConstVal(b, 0)) return a; break;
    case Kind::BvSub: if (isConstVal(b, 0)) return a; if (a == b) return bvConst(APInt(s.width, 0)); break;
    case Kind::BvMul:
      if (isConstVal(a, 0) || isConstVal(b, 0)) return bvConst(APInt(s.width, 0));
      if (isConstVal(a, 1)) return b;
      if (isConstVal(b, 1)) return a;
      break;
    case Kind::BvAnd:
      if (isConstVal(a, 0) || isConstVal(b, 0)) return bvConst(APInt(s.width, 0));
      if (isAllOnes(a)) return b;
      if (isAllOnes(b)) return a;
      if (a == b) return a;
      break;
    case Kind::BvOr:
      if (isConstVal(a, 0)) return b;
      if (isConstVal(b, 0)) return a;
      if (isAllOnes(a) || isAllOnes(b)) return bvConst(APInt::getAllOnes(s.width));
      if (a == b) return a;
      break;
    case Kind::BvXor:
      if (isConstVal(a, 0)) return b;
      if (isConstVal(b, 0)) return a;
      if (a == b) return bvConst(APInt(s.width, 0));
      break;
    case Kind::BvShl: case Kind::BvLshr: case Kind::BvAshr: if (isConstVal(b, 0)) return a; break;
    default: break;
  }
  return intern(make(k, s, {a, b}));
}

TermRef TermManager::mkUn(Kind k, TermRef a) {
  assert(k == Kind::BvNot || k == Kind::BvNeg);
  if (TermRef f = foldConst(*this, k, a->sort, 0, 0, {a})) return f;
  if (a->kind == k) return a->args[0];  // ~~x, --x
  return intern(make(k, a->sort, {a}));
}

TermRef TermManager::mkZExt(TermRef a, unsigned w) {
  assert(w >= a->sort.width);
  if (w == a->sort.width) return a;
  if (TermRef f = foldConst(*this, Kind::ZExt, Sort::bv(w), w, 0, {a})) return f;
  Term t = make(Kind::ZExt, Sort::bv(w), {a});
  t.hi = w;
  return intern(std::move(t));
}

TermRef TermManager::mkSExt(TermRef a, unsigned w) {
  assert(w >= a->sort.width);
  if (w == a->sort.width) return a;
  if (TermRef f = foldConst(*this, Kind::SExt, Sort::bv(w), w, 0, {a})) return f;
  Term t = make(Kind::SExt, Sort::bv(w), {a});
  t.hi = w;
  return intern(std::move(t));
}

TermRef TermManager::mkExtract(TermRef a, unsigned hi, unsigned lo) {
  assert(hi >= lo && hi < a->sort.width);
  if (lo == 0 && hi + 1 == a->sort.width) return a;
  if (TermRef f = foldConst(*this, Kind::Extract, Sort::bv(hi - lo + 1), hi, lo, {a})) return f;
  Term t = make(Kind::Extract, Sort::bv(hi - lo + 1), {a});
  t.hi = hi;
  t.lo = lo;
  return intern(std::move(t));
}

TermRef TermManager::mkConcat(TermRef hi, TermRef lo) {
  Sort s = Sort::bv(hi->sort.width + lo->sort.width);
  if (TermRef f = foldConst(*this, Kind::Concat, s, 0, 0, {hi, lo})) return f;
  return intern(make(Kind::Concat, s, {hi, lo}));
}

// ---------------------------------------------------------------- arrays
TermRef TermManager::arrVar(const std::string &name, unsigned idxW, unsigned elemW) {
  auto it = impl_->varsByName.find(name);
  if (it != impl_->varsByName.end()) {
    assert(it->second->sort == Sort::array(idxW, elemW) && "array variable redeclared with a different sort");
    return it->second;
  }
  Term t = make(Kind::Var, Sort::array(idxW, elemW));
  t.name = name;
  TermRef r = intern(std::move(t));
  impl_->varsByName.emplace(name, r);
  return r;  // array variables are not listed in variables(): models are read through Select
}

TermRef TermManager::mkConstArray(unsigned idxW, TermRef elem) {
  assert(elem->sort.isBv());
  return intern(make(Kind::ConstArray, Sort::array(idxW, elem->sort.width), {elem}));
}

TermRef TermManager::mkSelect(TermRef a, TermRef i) {
  assert(a->sort.isArray && i->sort.isBv() && i->sort.width == a->sort.idxWidth);
  // read-over-write with constant indices, and reads of constant arrays
  TermRef cur = a;
  for (;;) {
    if (cur->kind == Kind::ConstArray) return cur->args[0];
    if (cur->kind == Kind::Store) {
      TermRef si = cur->args[1];
      if (si == i) return cur->args[2];
      if (si->kind == Kind::BvConst && i->kind == Kind::BvConst) { cur = cur->args[0]; continue; }  // distinct constants
    }
    break;
  }
  return intern(make(Kind::Select, Sort::bv(a->sort.width), {cur, i}));
}

TermRef TermManager::mkStore(TermRef a, TermRef i, TermRef v) {
  assert(a->sort.isArray && i->sort.isBv() && i->sort.width == a->sort.idxWidth && v->sort.isBv() && v->sort.width == a->sort.width);
  if (a->kind == Kind::Store && a->args[1] == i) a = a->args[0];  // overwritten store
  return intern(make(Kind::Store, a->sort, {a, i, v}));
}

// ---------------------------------------------------------------- bridges
TermRef TermManager::toBool(TermRef t) {
  assert(!t->sort.isBool && t->sort.width == 1);
  if (t->kind == Kind::BvConst) return boolConst(t->value.getBoolValue());
  if (t->kind == Kind::Ite && t->args[1]->kind == Kind::BvConst && t->args[2]->kind == Kind::BvConst) {
    bool a = t->args[1]->value.getBoolValue(), b = t->args[2]->value.getBoolValue();
    if (a && !b) return t->args[0];
    if (!a && b) return mkNot(t->args[0]);
  }
  return mkEq(t, bvConst(1, 1));
}

TermRef TermManager::fromBool(TermRef b) {
  assert(b->sort.isBool);
  if (b->isConst()) return bvConst(1, b->value.getBoolValue());
  if (b->kind == Kind::Eq && b->args[0]->sort.width == 1) {  // (= t #b1) back to t
    if (isConstVal(b->args[1], 1)) return b->args[0];
    if (isConstVal(b->args[0], 1)) return b->args[1];
  }
  return mkIte(b, bvConst(1, 1), bvConst(1, 0));
}

}  // namespace hlir::smt

// Private. The memory model, written once and generic over the value domain D (DESIGN.md §17.4, §19.5).
//
// Block + offset with provenance: a pointer is (obj, off); obj = 0 is null. Objects are never reused, so use-after-free
// is always detectable. Contents are byte cells {byte, init, prov}; a pointer written to memory leaves `prov` fragments
// so it survives memcpy and is recovered on load.
//
// The same code serves both domains:
//  * concrete: every obj/off/size is a constant, so every access resolves exactly;
//  * symbolic: constants resolve exactly too; `ite` pointers (e.g. a heap_alloc that may fail) become guarded
//    accesses over their candidate objects; symbolic offsets / unknown objects are over-approximated (loads return a
//    fresh value, stores forget the object's contents) and `overApprox()` is set. A concrete run cannot be
//    approximate: it records an error instead and the machine reports Unsupported.
// The conditions of all memory core.check.* ops live in violations(): the single definition shared by both domains.
#pragma once
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "Pred.h"
#include "UBConditions.h"
#include "hlir/semantics/Interpreter.h"

namespace hlir {

enum class ObjKind { Stack, Heap, Global, Param };

template <class D>
struct PtrV {
  typename D::Val obj{}, off{};
};

template <class D>
class Memory {
 public:
  using Val = typename D::Val;
  using Ptr = PtrV<D>;
  static constexpr unsigned kIdWidth = 32;
  // Default hard cap on how many bytes a single core.memcpy/core.memset (or cstrlen/readBytes/mapBytes/cstringBytes
  // scan) will physically expand into per-byte cell operations. Independent of `bound_`/setBound() (RunConfig::memBound /
  // SymConfig::memBound): that one bounds the *unrolling* of a *symbolic* length, this one bounds the absolute byte
  // count even when the length is a compile-time constant. Configurable via setMaxExpand() (RunConfig::memExpandMax);
  // the default here matches the previous hardcoded constant exactly, so behaviour is unchanged unless a caller opts in.
  static constexpr uint64_t kMaxExpandDefault = 1u << 20;

  Memory(D &d, unsigned ptrWidth) : d_(d), pw_(ptrWidth) {}
  // Where the bytes of an input object come from (named input variables / the environment).
  void setInputSource(std::function<Val(const std::string &)> f) { inputFn_ = std::move(f); }
  // Bytes of an object materialised past the synthesis frontier: the harness's own invention, symbolic but not
  // attacker data. See Obj::frontier and lazyFrontier().
  void setFrontierSource(std::function<Val(const std::string &)> f) { frontierFn_ = std::move(f); }
  // Selection over a constant table's static initialiser instead of concretising a symbolic index
  // (constTableTargets). On by default because it is EXACT -- it cannot turn a falsifiable condition
  // unfalsifiable the way promoting the table to an unconstrained value does.
  void setTableSelect(bool on) { tableSelect_ = on; }
  uint64_t tableSelects() const { return tableSelects_; }
  // The same idea on the write side (symStoreTargets): a store at a symbolic offset becomes one
  // guarded write per in-bounds offset instead of a write to the slot this run happened to take.
  // OPT-IN (hlir-scan --store-select) until the snprintf_chain_oob divergence in Sec.22.487 is
  // explained: it closes the branch the read side closes, and it also turned one existing fixture's
  // replay-confirmed oob_write into `not_reproduced`, which is a wrong answer and not a slower one.
  void setStoreSelect(bool on) { storeSelect_ = on; }
  uint64_t storeSelects() const { return storeSelects_; }
  // The most recently allocated object's content is attacker/caller supplied: every byte is initialised and free.
  void markInputContent() { objs_.back().inputContent = true; }
  // `content: unknown` (DESIGN.md §22.381): the object's bytes are nobody's -- not the attacker's, not a zero
  // fill. They come from the SAME source as the synthesis frontier's (frontierFn_, symbolic and harness-labelled),
  // so a finding decided only by them is `harness_only` through the existing onlyFrontier() machinery. What this
  // is NOT is a frontier object: its size is the spec's, real, and bounds checks against it stay on.
  void markUnknownContent() { objs_.back().unknownContent = true; }
  // The most recently allocated object is externally mutable (declared via spec, MVP: no auto-detection). See Obj::extMut.
  void markExternallyMutable() { objs_.back().extMut = true; }
  // True iff any candidate object `p` may denote was markExternallyMutable(). False (not just "no") when `p`'s
  // pointer is symbolic/unresolved: the caller (Machine.h) then falls back to the existing load() path unchanged,
  // same as it already does for a symbolic pointer.
  bool mayBeExternallyMutable(const Ptr &p) {
    std::vector<Target> ts;
    if (!targets(p, ts)) return false;
    for (auto &t : ts) if (t.o && t.o->extMut) return true;
    return false;
  }

  bool failed() const { return !error_.empty(); }
  const std::string &error() const { return error_; }
  bool overApprox() const { return overApprox_; }
  unsigned ptrWidth() const { return pw_; }

  Ptr nullPtr() { return {idVal(0), d_.zero(pw_)}; }
  Val boolVal(bool b) { return d_.constant(llvm::APInt(1, b)); }

  // ---------------------------------------------------------------- allocation and lifetime
  Ptr alloc(ObjKind kind, Val size, uint64_t align, bool isConst, bool zeroInit) {
    Obj o;
    o.id = static_cast<uint32_t>(objs_.size() + 1);
    o.kind = kind;
    o.size = size;
    o.alive = boolVal(true);
    o.align = align ? align : 1;
    o.isConst = isConst;
    o.zeroInit = zeroInit;
    o.siteFn = siteFn_;
    o.siteLoc = siteLoc_;
    lastId_ = o.id;
    objs_.push_back(std::move(o));
    return {idVal(lastId_), d_.zero(pw_)};
  }
  uint32_t lastId() const { return lastId_; }
  // The machine points this at the op it is about to execute, so an allocation made anywhere below -- including
  // inside a model handler -- is stamped with its real site without threading a parameter through every call.
  void setAllocSite(const Function *f, const Loc *l) { siteFn_ = f; siteLoc_ = l; }
  void nameLastObject(std::string n) {
    if (lastId_ >= 1 && lastId_ <= objs_.size()) objs_[lastId_ - 1].specName = std::move(n);
  }
  bool hasObject(uint32_t id) const { return id >= 1 && id <= objs_.size(); }

  // Writes made from inside an `@__hlir_init.*` body replay a static initialiser; they are not the program running.
  // See Obj::progWritten.
  void setInStaticInit(bool b) { inStaticInit_ = b; }

  // Does `name` name a global the program has not written and that is not `const`? A const global cannot be changed
  // by `module_init` either, so reading its initial value asserts nothing. An unknown name answers false: a global
  // that was never created was never read.
  bool globalIsPristine(const std::string &name) const {
    auto it = globals_.find(name);
    if (it == globals_.end()) return false;
    const Obj &o = objs_[it->second - 1];
    return !o.progWritten && !o.isConst;
  }

  // Global objects are created on first use, zero-initialised.
  Ptr global(const std::string &name, uint64_t size, bool isConst) {
    auto it = globals_.find(name);
    if (it != globals_.end()) return {idVal(it->second), d_.zero(pw_)};
    Ptr p = alloc(ObjKind::Global, d_.constant(llvm::APInt(pw_, size)), 8, isConst, /*zeroInit=*/true);
    globals_.emplace(name, lastId_);
    return p;
  }

  // free / lifetime_end: the candidate objects of `p` stop being alive.
  void kill(const Ptr &p) {
    bool single = d_.constValue(p.obj).has_value();
    for (uint32_t id : candidates(p.obj)) {
      Obj &o = objs_[id - 1];
      o.alive = single ? boolVal(false) : d_.select(d_.icmp(Pred::Eq, p.obj, idVal(id)), boolVal(false), o.alive);
    }
  }
  void killId(uint32_t id) {
    if (id >= 1 && id <= objs_.size()) { objs_[id - 1].alive = boolVal(false); if (writeLog_) writeLog_->insert(id); }
  }

  // ---------------------------------------------------------------- metadata (ite over candidate objects)
  Val sizeOf(const Ptr &p) { return meta(p.obj, [](Obj &o) { return o.size; }, d_.zero(pw_)); }
  Val aliveOf(const Ptr &p) { return meta(p.obj, [](Obj &o) { return o.alive; }, boolVal(false)); }
  Val isHeap(const Ptr &p) { return kindIs(p, ObjKind::Heap); }
  Val isStack(const Ptr &p) { return kindIs(p, ObjKind::Stack); }
  Val isConstObj(const Ptr &p) { return meta(p.obj, [&](Obj &o) { return boolVal(o.isConst); }, boolVal(false)); }
  Val alignOf(const Ptr &p) { return meta(p.obj, [&](Obj &o) { return d_.constant(llvm::APInt(pw_, o.align)); }, d_.constant(llvm::APInt(pw_, 1))); }
  Val isNull(const Ptr &p) { return d_.icmp(Pred::Eq, p.obj, idVal(0)); }

  // "This object's `size` is something we measured, not something we made up." False only past the synthesis
  // frontier (see lazyFrontier()), where the object is a stand-in for a struct the engine never looked at and its
  // size is the arbitrary kFrontierObjBytes. The two bounds checks in violations(), and oobCond(), are therefore
  // not asked out there: the frontier assumption already says in the report that nothing beyond it is bounded by
  // its real struct, and reporting an overrun of a number we invented would be reporting our own invention.
  // An unknown or null object answers true -- null has its own `notNull` guard and that must not change.
  // "<tag>#<record size>@<byte offset>" for a read inside an object materialised past the synthesis frontier, when
  // the IR told us what record it stands for. Empty otherwise -- including for every object the InitPlan built,
  // which already carries its `where:` preconditions. Single-target, constant-offset reads only: with the object or
  // the offset in doubt there is no one field to name.
  std::string frontierFieldKey(const Ptr &p) {
    std::vector<Target> ts;
    if (!targets(p, ts) || ts.size() != 1) return {};
    Target &t = ts[0];
    if (!t.coff || !t.o->frontier || t.o->pointeeKey.empty() || *t.coff < t.o->pointeeBase) return {};
    return t.o->pointeeKey + "@" + std::to_string(*t.coff - t.o->pointeeBase);
  }
  uint32_t objIdOf(const Ptr &p) { auto c = d_.constValue(p.obj); return c ? static_cast<uint32_t>(c->getZExtValue()) : 0; }

  Val sizeIsReal(const Ptr &p) { return meta(p.obj, [&](Obj &o) { return boolVal(!o.sizeInvented); }, boolVal(true)); }

  // core.ptr_to_int: address = id << 32 | offset (see PtrToInt in Machine.h for why). `p.obj` is usually a constant
  // (objects get concrete ids at allocation time), but a pointer merged from two branches (e.g. loaded back from a
  // field that was conditionally written) can have a symbolic `obj` — an `ite` over a few candidate ids. Build the
  // same `id << 32 | offset` value as an ite-chain over those candidates instead of requiring a single constant id.
  // Returns nullopt when the cast isn't representable (any nonzero candidate id needs a 64-bit pointer width).
  std::optional<Val> ptrToIntVal(const Ptr &p, unsigned width) {
    auto id = d_.constValue(p.obj);
    if (id) {
      if (!id->isZero() && pw_ != 64) return std::nullopt;
      Val off = p.off;
      if (!id->isZero()) off = d_.or_(d_.constant(llvm::APInt(pw_, id->getZExtValue() << 32)), d_.and_(off, d_.constant(llvm::APInt(pw_, 0xffffffffu))));
      return width <= pw_ ? d_.trunc(off, width) : d_.zext(off, width);
    }
    std::vector<uint32_t> ids = candidates(p.obj);
    for (uint32_t cid : ids) if (cid != 0 && pw_ != 64) return std::nullopt;
    Val result = p.off;  // default: obj is null (id 0), or an id outside the enumerated candidates
    for (uint32_t cid : ids) {
      Val shifted = d_.or_(d_.constant(llvm::APInt(pw_, static_cast<uint64_t>(cid) << 32)), d_.and_(p.off, d_.constant(llvm::APInt(pw_, 0xffffffffu))));
      result = d_.select(d_.icmp(Pred::Eq, p.obj, idVal(cid)), shifted, result);
    }
    return width <= pw_ ? d_.trunc(result, width) : d_.zext(result, width);
  }

  // ---------------------------------------------------------------- data access
  // Bytes are read and written through "targets": (object, offset) pairs a pointer may denote. An object keeps sparse cells
  // for constant offsets; the first access with a symbolic offset (only domains with kArrays) converts it, once, to SMT
  // arrays {data, init, prov, pidx} indexed by offset, after which every access to it goes through the arrays.

  // Little-endian load of `bytes` bytes as an integer of 8*bytes bits.
  Val load(const Ptr &p, unsigned bytes) {
    std::vector<Target> ts;
    if (!targets(p, ts, /*forRead=*/true)) { inexact("load through a symbolic pointer"); return d_.fresh("mem.sym", 8 * bytes); }
    if (ts.empty()) { error_ = "access through a null or invalid pointer"; return d_.zero(8 * bytes); }
    auto one = [&](Target &t) {
      Val r = rdByte(t, bytes - 1);
      for (unsigned k = bytes - 1; k-- > 0;) r = d_.concat(r, rdByte(t, k));
      return r;
    };
    Val r = one(ts.back());
    for (size_t i = ts.size() - 1; i-- > 0;) r = d_.select(*ts[i].guard, one(ts[i]), r);
    return r;
  }
  void store(const Ptr &p, Val v, unsigned bytes) {
    std::vector<Target> ts;
    if (!storeTargets(p, ts, bytes)) { inexact("store through a symbolic pointer"); havoc(p.obj); return; }
    if (ts.empty()) { error_ = "access through a null or invalid pointer"; return; }
    for (auto &t : ts)
      for (unsigned k = 0; k < bytes; ++k) wr(t, k, {d_.extract(v, 8 * k + 7, 8 * k), boolVal(true), idVal(0), pidxVal(0)});
  }

  // `pointeeKey`: "<tag>#<record size>" of the record this pointer points to, empty when the IR could not say.
  // It is an IDENTITY, not an extent -- see the frontend comment where it is emitted.
  Ptr loadPtr(const Ptr &p, const std::string &pointeeKey = {}) {
    unsigned bytes = pw_ / 8;
    std::vector<Target> ts;
    if (!targets(p, ts)) { inexact("pointer load through a symbolic pointer"); return {d_.fresh("mem.symptr.obj", kIdWidth), d_.fresh("mem.symptr.off", pw_)}; }
    if (ts.empty()) { error_ = "access through a null or invalid pointer"; return nullPtr(); }
    if (ts.size() == 1)
      if (auto q = lazyFrontier(ts[0], bytes, pointeeKey)) return *q;
    auto one = [&](Target &t) {
      Val off = rdByte(t, bytes - 1);
      for (unsigned k = bytes - 1; k-- > 0;) off = d_.concat(off, rdByte(t, k));
      // the bytes must be the fragments 1..n of one pointer; anything else is an integer (obj 0)
      Val prov = rdProv(t, 0), ok = d_.icmp(Pred::Eq, rdPidx(t, 0), pidxVal(1));
      for (unsigned k = 1; k < bytes; ++k) {
        ok = d_.and_(ok, d_.icmp(Pred::Eq, rdProv(t, k), prov));
        ok = d_.and_(ok, d_.icmp(Pred::Eq, rdPidx(t, k), pidxVal(k + 1)));
      }
      return Ptr{d_.select(ok, prov, idVal(0)), off};
    };
    Ptr r = one(ts.back());
    for (size_t i = ts.size() - 1; i-- > 0;) {
      Ptr q = one(ts[i]);
      r.obj = d_.select(*ts[i].guard, q.obj, r.obj);
      r.off = d_.select(*ts[i].guard, q.off, r.off);
    }
    return r;
  }
  void storePtr(const Ptr &p, const Ptr &q) {
    unsigned bytes = pw_ / 8;
    std::vector<Target> ts;
    if (!storeTargets(p, ts, bytes)) { inexact("pointer store through a symbolic pointer"); havoc(p.obj); return; }
    if (ts.empty()) { error_ = "access through a null or invalid pointer"; return; }
    for (auto &t : ts)
      for (unsigned k = 0; k < bytes; ++k) wr(t, k, {d_.extract(q.off, 8 * k + 7, 8 * k), boolVal(true), q.obj, pidxVal(k + 1)});
  }

  // Is any byte of [p, p+bytes) uninitialised? (width-1 value)
  Val uninitCond(const Ptr &p, unsigned bytes) {
    std::vector<Target> ts;
    if (!targets(p, ts) || ts.empty()) return boolVal(false);  // approximated reads are assumed initialised
    auto one = [&](Target &t) {
      Val c = boolVal(false);
      for (unsigned k = 0; k < bytes; ++k) c = d_.or_(c, d_.not_(rdInit(t, k)));
      return c;
    };
    Val r = one(ts.back());
    for (size_t i = ts.size() - 1; i-- > 0;) r = d_.select(*ts[i].guard, one(ts[i]), r);
    return r;
  }

  // memcpy / memmove (the source is snapshotted first, so overlap behaves like memmove). A symbolic length is unrolled up to
  // the configured bound, each byte guarded by `i < n`; the domain is told to assert n <= bound (unwind assertion).
  void copy(const Ptr &dst, const Ptr &src, Val n) {
    std::vector<Target> dt, st;
    if (!targets(dst, dt) || !targets(src, st) || dt.size() != 1 || st.size() != 1) {
      inexact("memcpy/memmove through a symbolic or multi-object pointer");
      havoc(dst.obj);
      return;
    }
    bulk(dt[0], &st[0], nullptr, n);
  }
  void set(const Ptr &dst, Val byte, Val n) {
    fillWith(dst, n, [&](uint64_t) { return byte; });
  }
  // Writes byteAt(i) to dst[i] for i < n (a symbolic n is unrolled to the bound, like memset).
  void fillWith(const Ptr &dst, Val n, const std::function<Val(uint64_t)> &byteAt) {
    std::vector<Target> dt;
    if (!targets(dst, dt) || dt.size() != 1) {
      inexact("memset/fill through a symbolic or multi-object pointer");
      havoc(dst.obj);
      return;
    }
    bulk(dt[0], nullptr, byteAt, n);
  }
  // Length of the NUL-terminated string at p (concrete bytes only; domains with symbolic bytes report an error).
  Val cstrlen(const Ptr &p) {
    std::vector<Target> ts;
    if (!targets(p, ts) || ts.size() != 1) { inexact("string length of a symbolic pointer"); return d_.zero(pw_); }
    for (uint64_t k = 0; k < maxExpand_; ++k) {
      auto c = d_.constValue(rdByte(ts[0], k));
      if (!c) { error_ = "string length needs concrete bytes"; return d_.zero(pw_); }
      if (c->isZero()) return d_.constant(llvm::APInt(pw_, k));
    }
    error_ = "unterminated string";
    return d_.zero(pw_);
  }
  // The `n` bytes at p (n concrete); for domains that track taint.
  bool readBytes(const Ptr &p, Val n, std::vector<Val> &out) {
    std::vector<Target> ts;
    auto len = d_.constValue(n);
    if (!len || !targets(p, ts) || ts.size() != 1 || len->getZExtValue() > maxExpand_) { inexact("byte range of a symbolic pointer or length"); return false; }
    for (uint64_t k = 0; k < len->getZExtValue(); ++k) out.push_back(rdByte(ts[0], k));
    return true;
  }
  // Replaces each byte b_k of the range by f(b_k, k) (keeping initialisation and provenance).
  template <class F>
  bool mapBytes(const Ptr &p, Val n, F f) {
    std::vector<Target> ts;
    auto len = d_.constValue(n);
    if (!len || !targets(p, ts) || ts.size() != 1 || len->getZExtValue() > maxExpand_) { inexact("byte range of a symbolic pointer or length"); return false; }
    for (uint64_t k = 0; k < len->getZExtValue(); ++k) {
      Val b = rdByte(ts[0], k);
      wr(ts[0], k, {f(b, k), rdInit(ts[0], k), rdProv(ts[0], k), rdPidx(ts[0], k)});
    }
    return true;
  }
  // Bytes of the NUL-terminated string at p including the terminator (concrete terminator position).
  bool cstringBytes(const Ptr &p, std::vector<Val> &out) {
    std::vector<Target> ts;
    if (!targets(p, ts) || ts.size() != 1) { inexact("string at a symbolic pointer"); return false; }
    for (uint64_t k = 0; k < maxExpand_; ++k) {
      Val b = rdByte(ts[0], k);
      out.push_back(b);
      auto c = d_.constValue(b);
      if (!c) { error_ = "string scan needs concrete bytes"; return false; }
      if (c->isZero()) return true;
    }
    return true;
  }
  void setBound(uint64_t b) { bound_ = b; }
  void setMaxExpand(uint64_t b) { maxExpand_ = b; }
  void setLazyFrontier(bool on) { lazyFrontier_ = on; }



  // The checks a formatted write of `bytes` bytes into `p` owes, in exactly the form violations() builds for
  // core.check.null / core.check.uaf / core.check.oob (DESIGN.md §22.439). The folded printf writes from C++
  // rather than by running the model's body, so without this it would be the one write in the engine that is
  // not checked -- and it is a write into a caller-supplied buffer, which is the whole reason sprintf is
  // dangerous. Kept next to violations() so the two cannot drift apart unnoticed.
  void accessViolations(const Ptr &p, Val bytes, bool write, std::vector<UBViolation<D>> &out) {
    Val nn = d_.not_(isNull(p));
    out.push_back({UBKind::NullDeref, isNull(p)});
    Val dead = d_.and_(d_.not_(aliveOf(p)), nn);
    out.push_back({UBKind::UseAfterFree, d_.and_(dead, d_.not_(isStack(p)))});
    out.push_back({UBKind::UseAfterScope, d_.and_(dead, isStack(p))});
    Val size = sizeOf(p);
    Val ok = d_.and_(d_.icmp(Pred::Ule, p.off, size), d_.icmp(Pred::Ule, bytes, d_.sub(size, p.off)));
    out.push_back({write ? UBKind::OobWrite : UBKind::OobRead,
                   d_.and_(d_.and_(d_.not_(ok), nn), sizeIsReal(p))});
  }

  // ---------------------------------------------------------------- UB conditions of the memory core.check.* ops
  // ps: pointer operands, is: integer operands (in operand order). Returns false for ops that are not memory checks.
  bool violations(const Op &op, const std::vector<Ptr> &ps, const std::vector<Val> &is, std::vector<UBViolation<D>> &out) {
    auto notNull = [&](const Ptr &p) { return d_.not_(isNull(p)); };
    switch (op.opc) {
      case Opc::CheckNull:
        out.push_back({UBKind::NullDeref, isNull(ps[0])});
        return true;
      case Opc::CheckUaf: {
        Val dead = d_.and_(d_.not_(aliveOf(ps[0])), notNull(ps[0]));
        Val stack = isStack(ps[0]);
        out.push_back({UBKind::UseAfterFree, d_.and_(dead, d_.not_(stack))});
        out.push_back({UBKind::UseAfterScope, d_.and_(dead, stack)});
        return true;
      }
      case Opc::CheckOob: {
        const Attr *a = op.attr("access");
        bool write = a && a->s == "w";
        bool rmw = a && a->s == "rw";   // one access that is both (a[i] += x): see LV::rmw in the frontend
        Val size = sizeOf(ps[0]), off = ps[0].off;
        Val w = d_.constant(llvm::APInt(pw_, static_cast<uint64_t>(op.intAttr("w"))));
        Val ok = d_.and_(d_.icmp(Pred::Ule, off, size), d_.icmp(Pred::Ule, w, d_.sub(size, off)));
        Val bad = d_.and_(d_.and_(d_.not_(ok), notNull(ps[0])), sizeIsReal(ps[0]));
        // A read-modify-write out of bounds is BOTH halves of one access. The two entries below carry the
        // SAME condition, so in practice only the first can ever be reported: the engine continues a path
        // only where a check passed, which refutes the second. That is exactly why the order matters --
        // the WRITE goes first, so the finding is named after the more severe half, which is also what the
        // advisory and the fix commit call it. Before this, `a[i] += x` out of bounds was reported as
        // oob_read and was invisible to any class filter selecting oob_write (DESIGN.md Sec.22.470).
        if (rmw) out.push_back({UBKind::OobWrite, bad});
        out.push_back({rmw ? UBKind::OobRead : (write ? UBKind::OobWrite : UBKind::OobRead), bad});
        return true;
      }
      case Opc::CheckPtrArith: {
        // Arithmetic on a null base pointer is null_deref's territory (there is always a core.check.null right
        // after a resulting pointer gets used), not ptr_arith_oob's: a null pointer's "object" has no real size to
        // measure the new offset against, so sizeOf() falls back to 0 and *any* nonzero `is[0]` looks like it
        // overflows -- flagging that as ptr_arith_oob is both the wrong finding kind (misleadingly implies a real,
        // sized object was exceeded) and, when the null is one arm of an opaque external call's "NULL or an object"
        // return (lib/semantics/Machine.h's `ReturnSpec::Opaque`), redundant with the null_deref already reported
        // for the null arm elsewhere. Guarded the same way CheckOob already guards its own OOB condition above.
        Val newOff = d_.add(ps[0].off, is[0]);
        out.push_back({UBKind::PtrArithOob, d_.and_(d_.and_(d_.icmp(Pred::Ugt, newOff, sizeOf(ps[0])), notNull(ps[0])),
                                                   sizeIsReal(ps[0]))});
        return true;
      }
      case Opc::CheckFree: {
        Val heap = isHeap(ps[0]);
        out.push_back({UBKind::DoubleFree, d_.and_(d_.and_(heap, notNull(ps[0])), d_.not_(aliveOf(ps[0])))});
        Val badOff = d_.icmp(Pred::Ne, ps[0].off, d_.zero(pw_));
        out.push_back({UBKind::InvalidFree, d_.or_(d_.or_(isNull(ps[0]), d_.not_(heap)), badOff)});
        return true;
      }
      case Opc::CheckUninit:
        out.push_back({UBKind::UninitRead, uninitCond(ps[0], static_cast<unsigned>(op.intAttr("w")))});
        return true;
      case Opc::CheckAlign: {
        uint64_t a = static_cast<uint64_t>(op.intAttr("a"));
        Val av = d_.constant(llvm::APInt(pw_, a));
        Val bad = d_.icmp(Pred::Ne, d_.and_(ps[0].off, d_.constant(llvm::APInt(pw_, a - 1))), d_.zero(pw_));
        out.push_back({UBKind::Misaligned, d_.and_(notNull(ps[0]), d_.or_(bad, d_.icmp(Pred::Ult, alignOf(ps[0]), av)))});
        return true;
      }
      case Opc::CheckConstWrite:
        out.push_back({UBKind::ConstWrite, isConstObj(ps[0])});
        return true;
      case Opc::CheckPtrCmp:
        out.push_back({UBKind::PtrCmpDiffObj, d_.not_(d_.icmp(Pred::Eq, ps[0].obj, ps[1].obj))});
        return true;
      default:
        return false;
    }
  }

  // Equivalent of CheckOob's "out of bounds" condition (the Opc::CheckOob case above), but for a *dynamic* access
  // width `w` instead of a compile-time-constant IR attribute. Declarative ModelDB effects (source:/copy:/fill: in
  // Machine.h's execModel, e.g. recv/read/getenv/strcpy/memcpy/memset for modules that only declare them) write or
  // read a length that is itself a runtime Val (often derived from a call argument), so they cannot emit a
  // `core.check.oob {w=<const>}` IR instruction the way hand-written core.func bodies (memcpy, fgets, ...) do --
  // those are the only callers of this helper. Pure addition: does not touch CheckOob/violations()/bulk()/wr(),
  // so existing behaviour for every hand-written core.func body and every other check is unchanged.
  // The bytes of a CONSTANT C string a pointer denotes, when the pointer denotes exactly one object at a known
  // offset and every byte up to the terminator is concrete. False (and `out` is meaningless) otherwise.
  //
  // This exists for the char-class intrinsics (DESIGN.md §22.385). `strchr("0123456789abcdef", c)` with a
  // symbolic `c` has a closed form -- a chain of selects, no branches -- but running it as the loop the model
  // spells out costs up to 34 FLIPPABLE branches per call, and a text parser calls it once or twice per input
  // character. Measured on c-ares: 1856902 of 2111991 flippable path conditions (88%) were inside @strchr.
  //
  // Reads no cell that does not already exist: an unwritten offset means the content is not a constant the
  // program wrote, and materialising a symbolic byte here would both answer "no" and leave that byte behind.
  bool constBytes(const Ptr &p, std::vector<uint8_t> &out, size_t cap) {
    std::vector<Target> ts;
    if (!targets(p, ts) || ts.size() != 1) return false;
    Target &t = ts[0];
    if (!t.coff || t.guard || t.o->arr) return false;          // array mode keeps no per-byte cells
    if (t.o->inputContent || t.o->unknownContent || t.o->frontier || t.o->havocked) return false;
    auto sz = D::peekVal(t.o->size);
    if (!sz || D::isSymbolicVal(t.o->size)) return false;
    const uint64_t size = sz->getZExtValue();
    for (uint64_t k = *t.coff; k < size; ++k) {
      if (out.size() >= cap) return false;
      Val b;
      auto it = t.o->cells.find(k);
      if (it != t.o->cells.end()) b = it->second.byte;
      else if (t.o->zeroInit) b = d_.zero(8);
      else return false;
      if (D::isSymbolicVal(b)) return false;
      auto cv = D::peekVal(b);
      if (!cv) return false;
      uint8_t v = static_cast<uint8_t>(cv->getZExtValue());
      if (v == 0) return true;                                  // the terminator: `out` is the whole string
      out.push_back(v);
    }
    return false;                                               // no terminator inside the object
  }

  // Exactly `n` concrete bytes starting at `p`, with no terminator rule: memchr and friends scan a fixed
  // count and do not stop at a NUL, so constBytes() -- which ends at the first zero -- cannot serve them.
  // Same preconditions otherwise: one object, known offset, no guard, not array mode, not attacker/unknown
  // content, concrete size, and every byte in range already concrete. Deliberately does NOT create cells:
  // an offset nothing ever wrote is not a program constant.
  bool constBytesN(const Ptr &p, uint64_t n, std::vector<uint8_t> &out) {
    std::vector<Target> ts;
    if (!targets(p, ts) || ts.size() != 1) return false;
    Target &t = ts[0];
    if (!t.coff || t.guard || t.o->arr) return false;
    if (t.o->inputContent || t.o->unknownContent || t.o->frontier || t.o->havocked) return false;
    auto sz = D::peekVal(t.o->size);
    if (!sz || D::isSymbolicVal(t.o->size)) return false;
    const uint64_t size = sz->getZExtValue();
    if (*t.coff > size || n > size - *t.coff) return false;      // the read must be in bounds
    out.clear();
    out.reserve(n);
    for (uint64_t k = 0; k < n; ++k) {
      Val b;
      auto it = t.o->cells.find(*t.coff + k);
      if (it != t.o->cells.end()) b = it->second.byte;
      else if (t.o->zeroInit) b = d_.zero(8);
      else return false;
      if (D::isSymbolicVal(b)) return false;
      auto cv = D::peekVal(b);
      if (!cv) return false;
      out.push_back(static_cast<uint8_t>(cv->getZExtValue()));
    }
    return true;
  }

  Val oobCond(const Ptr &p, Val w) {
    Val size = sizeOf(p), off = p.off;
    Val ok = d_.and_(d_.icmp(Pred::Ule, off, size), d_.icmp(Pred::Ule, w, d_.sub(size, off)));
    return d_.and_(d_.and_(d_.not_(ok), d_.not_(isNull(p))), sizeIsReal(p));
  }

 private:
  struct Cell {
    Val byte{}, init{}, prov{};
    uint8_t pidx = 0;  // 1-based index of this byte inside a pointer fragment, 0 = plain data
  };
  struct Obj {
    uint32_t id = 0;
    ObjKind kind = ObjKind::Heap;
    Val size{}, alive{};
    uint64_t align = 1;
    bool isConst = false, zeroInit = false, havocked = false, inputContent = false;
    bool unknownContent = false;  // see markUnknownContent(): symbolic, harness-labelled, real size
    // Global objects only (DESIGN.md §22.362): some byte of this global was written by the PROGRAM, as opposed to
    // by the `@__hlir_init.G()` that replays its static initialiser. While this is false the global still holds the
    // value it was born with -- the static initialiser's, or zero -- which is an assumption about the whole module
    // having not run, not a fact about this entry. Object granularity on purpose: a partial write marks the whole
    // object written, so the measurement built on this UNDER-counts rather than over-claims.
    bool progWritten = false;
    // Param objects only (the harness's own): byte offsets some store has already reached. The harness writes every
    // pointer field the spec NAMES while it builds the object, so an offset missing here is one the spec never named
    // -- the synthesis frontier (DESIGN.md §22.364). It cannot be read off `cells`: array mode clears those.
    std::set<uint64_t> wrOff;
    // Globals only: the byte offsets G2 replaced with an unconstrained value because the program never wrote
    // them (promoteUnwrittenGlobal, DESIGN.md §22.374). Empty unless --promote-read-globals ran, which is what
    // keeps lazyFrontier()'s global branch (§22.382) from changing anything for a scan that did not ask for it.
    std::set<uint64_t> promotedOffs;
    bool wrUnknown = false;  // a write, or a havoc, landed where we could not place it: treat the whole object as written
    // Set only on the blank object lazyFrontier() materialises past the synthesis frontier. Two inventions, not one:
    // its `size` is kFrontierObjBytes because we had to pick something (see sizeIsReal(): a bounds verdict measured
    // against an invented size is an invented verdict), and its CONTENT was never read from anywhere either, so its
    // unwritten bytes are an unknown the harness chose rather than the concrete 0 of a zero-initialised allocation
    // (see fresh(): they come from frontierFn_, symbolic and harness-labelled, and count as initialised).
    bool frontier = false;
    // ... but the size is a separate question from the content. When the IR told us the pointee's real size
    // (`pointee_size` on the load, DESIGN.md §22.365) the object is laid out exactly like one the harness itself
    // synthesises -- real size, pointer at offset 0 -- and its bounds checks are real checks again. This stays
    // true only for the case where nothing told us: a `void *`, or a field whose record type is incomplete here.
    bool sizeInvented = false;
    // "<tag>#<record size>" of the record this object stands for, when the IR could say (Obj::frontier only). It is
    // how a run-time-materialised object is matched against the invariants the program states about that struct.
    // `pointeeBase` is where inside this object the record starts -- the pointer is handed out at the midpoint, so
    // a member at record offset 4 lives at byte 2052 and the key has to be built from the difference.
    std::string pointeeKey;
    uint64_t pointeeBase = 0;
    // Declared externally-mutable (shared memory / mmap'd device registers / DMA buffers): a real second actor
    // (attacker process, hardware) can change the bytes between two loads with no store in between. The default
    // cells cache (below) is correct for ordinary memory but wrong for this: it would let two loads at the same
    // offset collapse onto the same symbolic value, hiding the TOCTOU window. See mayBeExternallyMutable() (public,
    // below): Opc::Load (Machine.h) checks it and skips the cache for this object's non-pointer loads.
    bool extMut = false;
    // Where this object was created, for ObjEvidence::stableKey (DESIGN.md §22.375). Pointers into the IR, which
    // outlives every run, so this costs two stores per allocation and no string work at all on the hot path.
    const Function *siteFn = nullptr;
    const Loc *siteLoc = nullptr;
    // The name the harness gave this object (`name=` on core.heap_alloc): the spec's own path for a parameter
    // object, e.g. "file->private_data". It beats both the record type and the site, because it is what the
    // person reading the report wrote.
    std::string specName;
    std::map<uint64_t, Cell> cells;
    bool arr = false;           // array representation (domains with kArrays only)
    Val data{}, init{}, prov{}, pidx{};
  };
  // A table bigger than this would put one select node per byte into every read of it; the tables this
  // is for (character-class bitmaps, state tables) are tens of bytes, not thousands.
  static constexpr uint64_t kMaxTableSelect = 512;
  // Lower than the read side on purpose: a selected store REWRITES every cell of the object, so its
  // cost is paid per store rather than once per chain. See symStoreTargets.
  static constexpr uint64_t kMaxStoreSelect = 64;

  struct Target {
    Obj *o;
    Val off;                          // byte offset of the access (a term in symbolic domains)
    std::optional<uint64_t> coff;     // the offset if it is a constant
    std::optional<Val> guard;         // "this is the object" (none for the last/only target)
  };

  struct CellV {
    Val byte, init, prov, pidx;  // pidx: 1-based fragment index inside a stored pointer, 0 = plain data (8 bits)
  };

  Val pidxVal(unsigned v) { return d_.constant(llvm::APInt(8, v)); }

  // copy (src != null) or fill (byte) of `n` bytes
  void bulk(Target dst, Target *src, const std::function<Val(uint64_t)> &byteAt, Val n) {
    auto len = d_.constValue(n);
    uint64_t count = 0;
    std::optional<Val> sym;
    if (len && len->getActiveBits() <= 63) {
      count = len->getZExtValue();
      if (count > maxExpand_) { inexact("memcpy/memset of a very large length"); havocTarget(dst); return; }
      // A CONCRETISED length is not a constant one. In the concolic domain constValue() hands back this run's
      // concrete value for a tainted length and counts the concretisation, so `count` is how many bytes THIS run
      // copies -- but the shadow would then record "byte i = src[i]" with no mention of n at all, while the
      // destination object's SIZE keeps its dependence on n. The solver is later asked a question that mixes the
      // two and can answer it by picking an n the copy contradicts.
      //
      // Measured on test/c/scan/probes/strlen_symlen_nul.c -- `malloc(len+1); memcpy(buf,in,len); buf[len]=0;` --
      // strlen() reported oob_read at offset 3 with a witness of in_len = 2. That witness does not reach offset 3:
      // in_len = 2 means buf[2] is the NUL and strlen stops there. The path condition said "bytes 0,1,2 are
      // non-zero", which constrained three unguarded copies of src and said nothing about in_len, so in_len was
      // free to be 2 while the check `3 >= in_len + 1` was solved (DESIGN.md Sec.22.457).
      //
      // Guarding each write with `i < n` puts the dependence back: "buf[2] != 0" now implies 2 < in_len, which
      // contradicts 3 >= in_len + 1. The same loop below does this for the array domains already.
      // Tagged as a CONCRETISATION, not a branch the program took: it must bind safety queries (that is the fix
      // above) but must not bind a branch flip, or the next input is forced to keep this very length and the
      // search collapses -- see PcEntry::concretisation and DESIGN.md Sec.22.467.
      if (d_.isSymbolicVal(n)) d_.assumeConcretisation(d_.icmp(Pred::Eq, n, d_.constant(llvm::APInt(d_.width(n), count))));
    } else {
      if constexpr (D::kArrays) {
        count = bound_;
        Val within = d_.icmp(Pred::Ule, n, d_.constant(llvm::APInt(d_.width(n), bound_)));
        d_.unwind(within, "memcpy/memset length exceeds the unrolling bound");
        sym = n;
      } else {
        inexact("memcpy/memset with a symbolic length");
        havocTarget(dst);
        return;
      }
    }
    std::vector<CellV> snap;
    for (uint64_t i = 0; i < count; ++i) {
      if (src) snap.push_back({rdByte(*src, i), rdInit(*src, i), rdProv(*src, i), rdPidx(*src, i)});
      else snap.push_back({byteAt(i), boolVal(true), idVal(0), pidxVal(0)});
    }
    for (uint64_t i = 0; i < count; ++i) {
      Target t = dst;
      if (sym) t.guard = d_.icmp(Pred::Ult, d_.constant(llvm::APInt(d_.width(n), i)), n);
      wr(t, i, snap[i]);
    }
  }
  Val idVal(uint32_t id) { return d_.constant(llvm::APInt(kIdWidth, id)); }

  void inexact(const std::string &why) {
    if (D::kExact) { if (error_.empty()) error_ = why + " (not representable exactly)"; }
    else overApprox_ = true;
  }

  // Candidate objects (ids, no null) a pointer's obj term can denote; sets `exact` false when unknown (=> all objects).
  void collect(Val obj, std::set<uint32_t> &out, bool &exact, int depth = 0) {
    if (auto c = d_.constValue(obj)) {
      uint64_t id = c->getZExtValue();
      if (id >= 1 && id <= objs_.size()) out.insert(static_cast<uint32_t>(id));
      return;
    }
    Val c, a, b;
    if (depth < 16 && d_.asIte(obj, c, a, b)) { collect(a, out, exact, depth + 1); collect(b, out, exact, depth + 1); return; }
    exact = false;
  }
  std::vector<uint32_t> candidates(Val obj, bool *exactOut = nullptr) {
    std::set<uint32_t> s;
    bool exact = true;
    collect(obj, s, exact);
    if (!exact) for (auto &o : objs_) s.insert(o.id);
    if (exactOut) *exactOut = exact;
    return {s.begin(), s.end()};
  }

  template <class F>
  Val meta(Val obj, F getter, Val dflt) {
    if (auto c = d_.constValue(obj)) {
      uint64_t id = c->getZExtValue();
      return id >= 1 && id <= objs_.size() ? getter(objs_[id - 1]) : dflt;
    }
    Val r = dflt;
    for (uint32_t id : candidates(obj)) r = d_.select(d_.icmp(Pred::Eq, obj, idVal(id)), getter(objs_[id - 1]), r);
    return r;
  }
  Val kindIs(const Ptr &p, ObjKind k) { return meta(p.obj, [&](Obj &o) { return boolVal(o.kind == k); }, boolVal(false)); }


  // Resolves a pointer to the objects it may denote. Fails (false) when no representation exists: an unknown object, or
  // a symbolic offset in a domain without arrays.
  // G2's remaining half (DESIGN.md Sec.22.465): a SYMBOLIC index into a CONSTANT table.
  //
  // Without this, `auto off = d_.constValue(p.off)` below concretises the index to the slot THIS
  // run happened to take, and the value read back carries no taint. The condition built from it is
  // then not symbolic at all, so the branch is classified `const` and its other edge is never
  // explored. Measured on nginx's `usual[]` bitmap (ngx_http_parse.c) and reproduced minimally:
  // `usual[ch >> 5] & 1U` gave br 3/4 with const=1, while the same test with a constant index and a
  // symbolic shift gave 4/4.
  //
  // The fix is SELECTION OVER THE KNOWN INITIAL VALUES, one guarded target per in-bounds offset,
  // which load() already folds into a select chain. That is exact: it models what the program
  // actually reads. It is deliberately NOT the other thing G2 could do -- promoting the table to an
  // unconstrained value (Sec.22.374) -- because that over-approximates: Sec.22.465 measured
  // `tabfp`'s `unsat` degrading into `open` once the table stopped being falsifiable, and an
  // unconstrained table manufactures findings the program cannot produce.
  //
  // Restricted to `isConst` objects on purpose. A const table cannot be stored through, so widening
  // targets() here cannot change what a store does, and its contents are the static initialiser for
  // the whole run. A non-const global that merely has not been written yet is the OTHER half of
  // G2 and stays with --promote-read-globals.
  bool constTableTargets(const Ptr &p, std::vector<Target> &out) {
    if (!tableSelect_ || !D::isTainted(p.off)) return false;
    bool exact = true;
    std::set<uint32_t> ids;
    collect(p.obj, ids, exact);
    if (!exact || ids.size() != 1) return false;
    Obj &o = objs_[*ids.begin() - 1];
    // `isConst` ALONE was the first gate written here, and it excluded the very case G2 exists for:
    // nginx's table is `static uint32_t usual[]`, not `static const`. A lookup table is defined by
    // nothing ever writing it, not by the qualifier -- which is exactly what G1's `progWritten`
    // already tracks (DESIGN.md Sec.22.362).
    if (o.kind != ObjKind::Global || !(o.isConst || !o.progWritten)) return false;
    if (o.havocked || o.wrUnknown || o.unknownContent || o.inputContent || !o.promotedOffs.empty())
      return false;
    auto n = d_.constValue(o.size);
    if (!n) return false;
    uint64_t sz = n->getZExtValue();
    if (sz == 0 || sz > kMaxTableSelect) return false;
    for (uint64_t k = 0; k < sz; ++k) {
      Target t{&o, p.off, k, std::nullopt};
      if (k + 1 < sz) t.guard = d_.icmp(Pred::Eq, p.off, d_.constant(llvm::APInt(pw_, k)));
      out.push_back(std::move(t));
    }
    ++tableSelects_;
    return true;
  }

  // A STORE at a symbolic offset, the dual of constTableTargets (DESIGN.md Sec.22.487).
  //
  // Without this, `targets()` below concretises the offset to the slot THIS run took and the write
  // lands there alone. Everything downstream then reads an untainted byte out of every OTHER slot,
  // so a condition built from one is not symbolic, the branch is filed `const`, and its other edge
  // is never explored -- the same mechanism Sec.22.465 fixed for reads, one direction later.
  // Minimal: `tab[src[0] & 15] = 1; if (tab[3])` gave 5/6 branches with const=1.
  //
  // The shape differs from the read side in one way that matters. A read's select chain ends in an
  // UNGUARDED fallback target, because some slot must supply the value. A store has no fallback: an
  // offset outside the object writes nothing (the out-of-bounds check reports it separately), so
  // EVERY target here carries its guard, and `wr()` turns each one into ite(off == k, new, old).
  // An unguarded last target is exactly the "scatter a single write across the whole table" bug the
  // read-side comment warned about, and it is the reason this is a separate function rather than a
  // flag on constTableTargets.
  //
  // Only for domains without SMT arrays. With arrays a symbolic offset is already exact (one
  // arrStore at a symbolic index), so selecting here would pay O(size) terms for nothing. The cost
  // is why the cap is 64 bytes rather than the read side's 512: a read of a 512-byte table builds
  // one select chain, while a store into a 64-byte object rewrites 64 cells, and a loop of such
  // stores multiplies that by the trip count.
  bool symStoreTargets(const Ptr &p, std::vector<Target> &out, unsigned bytes) {
    if constexpr (D::kArrays) {
      return false;
    } else {
      if (!storeSelect_ || !D::isTainted(p.off)) return false;
      bool exact = true;
      std::set<uint32_t> ids;
      collect(p.obj, ids, exact);
      if (!exact || ids.size() != 1) return false;
      Obj &o = objs_[*ids.begin() - 1];
      if (o.isConst) return false;  // a write here is a defect, not a thing to model precisely
      if (o.havocked || o.wrUnknown || o.unknownContent || !o.promotedOffs.empty()) return false;
      auto n = d_.constValue(o.size);
      if (!n) return false;
      uint64_t sz = n->getZExtValue();
      if (sz == 0 || sz > kMaxStoreSelect || bytes == 0 || bytes > sz) return false;
      // THIS RUN's offset must itself be in bounds, and the reason is a regression the fixture
      // `snprintf_chain_oob.c` caught: `p += snprintf(...)` walks a tainted pointer PAST an 8-byte
      // buffer and the write there is the defect. Every guard below is `off == k` for an in-bounds
      // k, so when the concrete offset is outside, no guard holds and the write silently lands
      // nowhere -- the engine's concrete state stops matching the program it is executing, and the
      // witness it then solves does not replay (verdict bug -> unknown, replay confirmed ->
      // not_reproduced). A store that is out of bounds on this run is a DEFECT to report, not a
      // shape to model precisely, so it goes back to the concretising path that reports it.
      auto cur = D::peekVal(p.off);
      if (!cur || cur->getActiveBits() > 63) return false;
      uint64_t c0 = cur->getZExtValue();
      if (c0 + bytes > sz) return false;
      for (uint64_t k = 0; k + bytes <= sz; ++k)  // k + bytes > sz is an out-of-bounds write, not a target
        out.push_back(Target{&o, p.off, k, d_.icmp(Pred::Eq, p.off, d_.constant(llvm::APInt(pw_, k)))});
      if (out.empty()) return false;
      // The escalation gate (Pipeline.cpp) runs the symbolic pass when the concolic engine had to
      // concretise a tainted address. This store WAS one of those before selection took it over, so
      // it still has to answer that question -- otherwise a strictly more precise memory model
      // silently removes a whole pass. Measured on snprintf_chain_oob.c: without this line the
      // replay-confirmed oob_write became `not_reproduced` and the verdict bug -> unknown, because
      // the witness that reproduces it is the SYMBOLIC pass's, and that pass no longer ran.
      d_.noteSelectedAddress();
      ++storeSelects_;
      return true;
    }
  }

  // Targets for a write of `bytes` bytes. Selection first; otherwise the ordinary (concretising) path.
  bool storeTargets(const Ptr &p, std::vector<Target> &out, unsigned bytes) {
    return symStoreTargets(p, out, bytes) || targets(p, out);
  }

  // `forRead`: only a LOAD may be resolved by selection over a TABLE (constTableTargets), whose last
  // target is deliberately unguarded -- store() would write that one unconditionally. A store at a
  // symbolic offset goes through storeTargets/symStoreTargets above, where every target is guarded.
  bool targets(const Ptr &p, std::vector<Target> &out, bool forRead = false) {
    if (forRead && constTableTargets(p, out)) return true;
    auto off = d_.constValue(p.off);
    bool exact = true;
    std::set<uint32_t> ids;
    collect(p.obj, ids, exact);
    if (!exact) {
      if constexpr (D::kArrays) { for (auto &o : objs_) ids.insert(o.id); }  // any object (guards select among them)
      else return false;
    }
    if (!off) {
      if constexpr (!D::kArrays) return false;
    } else if (off->getActiveBits() > 63) {
      return false;
    }
    std::vector<uint32_t> v(ids.begin(), ids.end());
    for (size_t i = 0; i < v.size(); ++i) {
      Target t{&objs_[v[i] - 1], p.off, off ? std::optional<uint64_t>(off->getZExtValue()) : std::nullopt, std::nullopt};
      if (i + 1 < v.size()) t.guard = d_.icmp(Pred::Eq, p.obj, idVal(v[i]));
      out.push_back(std::move(t));
    }
    return true;
  }

  bool arrayMode(const Target &t) const {
    if constexpr (D::kArrays) return t.o->arr || !t.coff;
    else return false;
  }
  Val offAt(const Target &t, uint64_t k) { return k ? d_.add(t.off, d_.constant(llvm::APInt(pw_, k))) : t.off; }

  Cell fresh(Obj &o, uint64_t off) {
    Cell c;
    c.prov = idVal(0);
    if (o.frontier && frontierFn_) { c.byte = frontierFn_("fr.o" + std::to_string(o.id) + "+" + std::to_string(off)); c.init = boolVal(true); }
    // The "in." prefix is load-bearing, not cosmetic: Taint.cpp/Symbolic.cpp copy only variables whose name
    // starts with "in." into the replay environment, so without it every finding behind a session gate would
    // solve correctly and then fail to replay -- the gate would be open in the solver's model and shut again in
    // the concrete re-run, and the finding would be filed `replay_no_ub` forever.
    else if (o.unknownContent && frontierFn_) { c.byte = frontierFn_("in.un.o" + std::to_string(o.id) + "+" + std::to_string(off)); c.init = boolVal(true); }
    else if (o.zeroInit) { c.byte = d_.zero(8); c.init = boolVal(true); }
    else if (o.inputContent && inputFn_) { c.byte = inputFn_("in.o" + std::to_string(o.id) + "+" + std::to_string(off)); c.init = boolVal(true); }
    else {
      c.byte = d_.fresh("mem.o" + std::to_string(o.id) + "+" + std::to_string(off), 8);
      c.init = boolVal(o.havocked);
    }
    return c;
  }
  Cell &cellRead(Obj &o, uint64_t off) {
    auto it = o.cells.find(off);
    if (it == o.cells.end()) it = o.cells.emplace(off, fresh(o, off)).first;
    return it->second;
  }

  // Cells -> arrays (once per object). Unwritten offsets keep the object's default content.
  void ensureArr(Obj &o) {
    if constexpr (D::kArrays) {
      if (o.arr) return;
      std::string id = std::to_string(o.id);
      if (o.frontier) o.data = d_.arrVar("fr.o" + id, pw_, 8);
      else if (o.unknownContent) o.data = d_.arrVar("in.un.o" + id, pw_, 8);
      else if (o.zeroInit) o.data = d_.arrConst(pw_, d_.zero(8));
      else if (o.inputContent) o.data = d_.arrVar("in.o" + id, pw_, 8);
      else o.data = d_.arrVar("mem.o" + id, pw_, 8);
      o.init = d_.arrConst(pw_, boolVal(o.zeroInit || o.inputContent || o.frontier || o.unknownContent));
      o.prov = d_.arrConst(pw_, idVal(0));
      o.pidx = d_.arrConst(pw_, pidxVal(0));
      for (auto &kv : o.cells) {
        Val i = d_.constant(llvm::APInt(pw_, kv.first));
        o.data = d_.arrStore(o.data, i, kv.second.byte);
        o.init = d_.arrStore(o.init, i, kv.second.init);
        o.prov = d_.arrStore(o.prov, i, kv.second.prov);
        o.pidx = d_.arrStore(o.pidx, i, pidxVal(kv.second.pidx));
      }
      o.cells.clear();
      o.arr = true;
    }
  }

  Val rdByte(Target &t, uint64_t k) {
    if constexpr (D::kArrays) {
      if (arrayMode(t)) {
        ensureArr(*t.o);
        Val i = offAt(t, k);
        if (t.o->inputContent) d_.noteInputRead(t.o->id, i);
        return d_.arrSelect(t.o->data, i);
      }
    }
    return cellRead(*t.o, *t.coff + k).byte;
  }
  Val rdInit(Target &t, uint64_t k) {
    if constexpr (D::kArrays) {
      if (arrayMode(t)) { ensureArr(*t.o); return d_.arrSelect(t.o->init, offAt(t, k)); }
    }
    return cellRead(*t.o, *t.coff + k).init;
  }
  Val rdProv(Target &t, uint64_t k) {
    if constexpr (D::kArrays) {
      if (arrayMode(t)) { ensureArr(*t.o); return d_.arrSelect(t.o->prov, offAt(t, k)); }
    }
    return cellRead(*t.o, *t.coff + k).prov;
  }
  Val rdPidx(Target &t, uint64_t k) {
    if constexpr (D::kArrays) {
      if (arrayMode(t)) { ensureArr(*t.o); return d_.arrSelect(t.o->pidx, offAt(t, k)); }
    }
    return pidxVal(cellRead(*t.o, *t.coff + k).pidx);
  }

  // Writes byte `k` of the access; with a guard the old value survives when the guard is false.
  void wr(Target &t, uint64_t k, const CellV &nc) {
    Obj &o = *t.o;
    if (writeLog_) writeLog_->insert(o.id);  // see setWriteLog
    if (o.kind == ObjKind::Global && !inStaticInit_) o.progWritten = true;
    if (o.kind == ObjKind::Param) {
      if (t.coff) o.wrOff.insert(*t.coff + k);
      else o.wrUnknown = true;
    }
    if constexpr (D::kArrays) {
      if (arrayMode(t)) {
        ensureArr(o);
        Val i = offAt(t, k);
        Val nd = d_.arrStore(o.data, i, nc.byte), ni = d_.arrStore(o.init, i, nc.init), np = d_.arrStore(o.prov, i, nc.prov), nx = d_.arrStore(o.pidx, i, nc.pidx);
        if (t.guard) {
          nd = d_.select(*t.guard, nd, o.data); ni = d_.select(*t.guard, ni, o.init);
          np = d_.select(*t.guard, np, o.prov); nx = d_.select(*t.guard, nx, o.pidx);
        }
        o.data = nd; o.init = ni; o.prov = np; o.pidx = nx;
        return;
      }
    }
    uint64_t off = *t.coff + k;
    uint8_t px = 0;
    if (auto c = d_.constValue(nc.pidx)) px = static_cast<uint8_t>(c->getZExtValue());
    if constexpr (D::kTaint) {
      auto old = o.cells.find(off);
      if (old != o.cells.end() && d_.isTainted(old->second.byte) && !d_.isTainted(nc.byte)) d_.noteKill();
    }
    if (!t.guard) { o.cells.insert_or_assign(off, Cell{nc.byte, nc.init, nc.prov, px}); return; }
    Cell old = cellRead(o, off);
    Cell c;
    c.byte = d_.select(*t.guard, nc.byte, old.byte);
    c.init = d_.select(*t.guard, nc.init, old.init);
    c.prov = d_.select(*t.guard, nc.prov, old.prov);
    c.pidx = px == old.pidx ? px : 0;
    o.cells.insert_or_assign(off, c);
  }

  // ---------------------------------------------------------------- the synthesis frontier (DESIGN.md §22.364)
  //
  // Pointer-field synthesis is finite: the spec NAMES a pointer, the harness builds it an object and stores it.
  // A pointer the spec does not name is read out of blank object content, which has no provenance -- and a pointer
  // without provenance is obj 0, i.e. NULL. That is not a cautious default, it is a WIDENING: it cannot hide a
  // defect, it manufactures one. `rmidi->card->number` (rawmidi.c:627) faulted because `file -> private_data ->
  // substream -> rmidi` used up the budget, and the real driver's `.open` had of course built `card`. Synthesis is
  // otherwise careful never to invent NULL -- only a field some visible body actually NULL-tests may be null
  // (§22.353) -- and the frontier bypassed that discipline for every pointer at once: 14 of the 19 confirmed
  // null_deref of the sound/core round were this one cause.
  //
  // So build the object on demand instead, the textbook lazy initialisation: the frontier stops being a place and
  // becomes a budget, and only the chains the program actually walks are ever materialised. The stored-back write
  // matters -- without it a second load of the same field would get a DIFFERENT object and every `a->b == a->b`
  // would be false.
  //
  // This replaces a widening with a NARROWING (beyond the frontier a pointer is now never NULL), which can hide a
  // defect and therefore has to be NAMED in the report, like `nullable` and `same_alloc` before it -- Pipeline.cpp
  // says so under `synthesis_frontier`. The trade is sound because the engine has no information either way out
  // there: it never looked at that struct, so it has no `nullTested` evidence to honour, and the memory is the
  // harness's own invention rather than anything the program allocated.
  //
  // Deliberately NOT applied to `content: input` objects: those are `taint: pointee`, where the stored word really
  // is attacker data and NULL really is one of the values the attacker may put there.
  std::optional<Ptr> lazyFrontier(Target &t, unsigned bytes, const std::string &pointeeKey) {
    if (!lazyFrontier_ || !t.coff || t.o->havocked) return std::nullopt;
    // A PROMOTED GLOBAL's pointer field (DESIGN.md §22.382). G2 replaces the bytes of a global the entry reads
    // and the program never wrote with unconstrained 8-bit values -- which is right for an integer field and
    // useless for a pointer one: a pointer is only a pointer here if its bytes carry provenance (loadPtr's
    // rdProv/rdPidx test), and invented bytes carry none, so the load yields obj 0 and the field reads NULL no
    // matter what the solver picks. Measured on <driver>: `hal_ctx = gpio_attr_dir->hal_ctx` out of the promoted
    // `s_AttrInfo`, then `if (hal_ctx == NULL) goto fail` -- the handler's own command dispatcher was
    // unreachable for this reason alone, after the session gate (§22.381) had already been opened.
    //
    // So promotion gets the same treatment the frontier gives a param object: materialise one. The guard is
    // deliberately narrow -- every byte of the load must be one G2 itself promoted, and the program must not
    // have written the global since. Without --promote-read-globals `promotedOffs` is empty and nothing here
    // fires, so a scan that did not ask for promotion is bit-for-bit unchanged.
    bool promotedGlobal = false;
    if (t.o->kind == ObjKind::Global) {
      if (t.o->progWritten || t.o->isConst || t.o->promotedOffs.empty()) return std::nullopt;
      for (unsigned k = 0; k < bytes; ++k)
        if (!t.o->promotedOffs.count(*t.coff + k)) return std::nullopt;
      promotedGlobal = true;
    } else if (t.o->kind != ObjKind::Param) {
      return std::nullopt;
    }
    if (!promotedGlobal) {
      if (t.o->inputContent || t.o->wrUnknown) return std::nullopt;
      for (unsigned k = 0; k < bytes; ++k)
        if (t.o->wrOff.count(*t.coff + k)) return std::nullopt;  // the spec named this field: its choice stands, NULL included
    }
    if (lazyMade_ >= kLazyBudget) return std::nullopt;          // also what terminates `while (p) p = p->next` out here
    ++lazyMade_;
    const uint32_t srcId = t.o->id;
    const uint64_t srcOff = *t.coff;
    const Val srcTOff = t.off;
    // The pointer lands in the MIDDLE of the blank object, not at its start. Where inside its allocation an unknown
    // pointer points is exactly as unknown as the allocation itself, and offset 0 is the one answer that is wrong
    // for every backwards-walking idiom there is: `(void)*(--s.top)` on a by-value `mark_stack_t` (libyaml's POP,
    // test/c/scan/aggregate_rvalue.c) turned into a confirmed ptr_arith_oob the moment `top` stopped being NULL.
    // Midpoint is a concrete stand-in for "unknown", and it is covered by the same named assumption as the rest of
    // the frontier: out here nothing is bounded by its real struct, in either direction. sizeInvented (below) is
    // what keeps that stand-in out of the verdicts -- `&mixer->slots[chn]` for chn < 31 on a 72-byte slot walks
    // 2232 bytes and would otherwise overrun the 2048 of slack, which is a fact about kFrontierObjBytes and
    // nothing else (16 of the sound/core round-44 confirmed ptr_arith_oob were exactly this). The midpoint still
    // earns its place for everything that reads rather than judges: it keeps a backwards walk inside the object.
    Ptr q = alloc(ObjKind::Param, d_.constant(llvm::APInt(pw_, kFrontierObjBytes)), 16, false, /*zeroInit=*/false);
    q.off = d_.constant(llvm::APInt(pw_, kFrontierObjBytes / 2));
    objs_[lastId_ - 1].frontier = true;
    objs_[lastId_ - 1].sizeInvented = true;  // the record's size is not the allocation's: see loadPtr's `pointeeKey`
    objs_[lastId_ - 1].pointeeKey = pointeeKey;
    objs_[lastId_ - 1].pointeeBase = kFrontierObjBytes / 2;
    Target st{&objs_[srcId - 1], srcTOff, srcOff, std::nullopt};  // re-fetched: alloc() may have moved objs_
    // The store-back is what makes `a->b == a->b` true, but it is OUR write, not the program's. Letting wr()
    // set progWritten would tell §22.362's measurement that the module had written this global -- the exact
    // opposite of what is true out here, and it would also stop any further field of the same global from being
    // materialised. Restored, not suppressed, so a real program write still flips it.
    const bool wasProgWritten = objs_[srcId - 1].progWritten;
    for (unsigned k = 0; k < bytes; ++k)
      wr(st, k, {d_.extract(q.off, 8 * k + 7, 8 * k), boolVal(true), q.obj, pidxVal(k + 1)});
    if (promotedGlobal) {
      objs_[srcId - 1].progWritten = wasProgWritten;
      for (unsigned k = 0; k < bytes; ++k) objs_[srcId - 1].promotedOffs.erase(srcOff + k);  // now a real pointer, not a free byte
    }
    return q;
  }

  // Forget the contents of every object `obj` might denote (over-approximation of a write we cannot place).
  void havoc(Val obj) {
    for (uint32_t id : candidates(obj)) havocObj(objs_[id - 1]);
  }
  void havocTarget(Target &t) { havocObj(*t.o); }
  void havocObj(Obj &o) {
    if (writeLog_) writeLog_->insert(o.id);  // see setWriteLog
    // forgetting the contents is not a program write, but it does mean we no longer know the initial value is
    // still there -- the measurement must not claim this global is pristine afterwards (see Obj::progWritten)
    if (o.kind == ObjKind::Global) o.progWritten = true;
    if (o.kind == ObjKind::Param) o.wrUnknown = true;  // same reasoning, for the frontier: we no longer know what is here
    if constexpr (D::kArrays) {
      ensureArr(o);
      o.data = d_.freshArr("mem.havoc.o" + std::to_string(o.id), pw_, 8);
      o.init = d_.arrConst(pw_, boolVal(true));
      o.prov = d_.arrConst(pw_, idVal(0));
      o.pidx = d_.arrConst(pw_, pidxVal(0));
      return;
    }
    o.cells.clear();
    o.havocked = true;
    o.zeroInit = false;
  }

 public:
  // ---------------------------------------------------------------- prologue snapshot (DESIGN.md §22.368)
  //
  // The project initialiser the harness runs before the entry does not depend on the entry's inputs: it produces
  // the same state on every run, so executing it once per run is pure waste. Measured on sound/core round 49c:
  // the median run went from 381 to 34587 steps, and the concolic fuzzer's run count for `snd_pcm_oss_ioctl` fell
  // from 20000 to 2240 -- the budget went to re-running initialisation instead of exploring the handler. `sec_solve`
  // did not move, so this is interpreter time, not solver time.
  //
  // What has to be preserved across the restore is the OBJECT NUMBERING. Memory numbers objects in allocation
  // order and witness names are keyed by that id (§22.351: a mis-numbered witness points at bytes that do not
  // reach the finding). The harness allocates the entry's parameter objects BEFORE the prologue, so everything the
  // prologue creates has an id above `base` and a snapshot can simply be the tail -- the parameters keep their ids
  // and, importantly, keep the per-run contents the fuzzer chose for them.
  //
  // Globals are the exception: one may already exist below `base` (the harness itself touches a few, e.g. the
  // uncaught-exception cell), and the prologue writes it. Those are saved by index and written back.
  struct Snapshot {
    size_t base = 0;                              // objs_.size() when the prologue started
    std::vector<Obj> tail;                        // objects the prologue created (ids base+1 ..)
    std::vector<std::pair<size_t, Obj>> preGlobals;  // globals below `base` the prologue may have changed
    std::map<std::string, uint32_t> globals;      // name -> id, as it stood when the prologue finished
    uint32_t lastId = 0;
    bool valid = false;
  };

  struct Cache : PrologueCache {
    Snapshot snap;
  };

  // How much of what a snapshot holds is SYMBOLIC (DESIGN.md §22.438). A setup region that leaves symbolic bytes
  // behind cannot simply be replayed: the restored cell keeps the concrete side the capturing run chose, so a
  // later flip of that variable would change the solver's model and not the memory, and the run would quietly
  // explore nothing. Counting it is how the engine decides to refuse, and the count is what the report prints.
  // An array-representation object counts as one, since its bytes are not enumerable.
  static unsigned symbolicBytesIn(const Snapshot &s) {
    unsigned n = 0;
    auto scan = [&](const Obj &o) {
      if (D::isSymbolicVal(o.size)) ++n;
      if (o.arr) { if (D::isSymbolicVal(o.data)) ++n; return; }
      for (auto &kv : o.cells)
        if (D::isSymbolicVal(kv.second.byte) || D::isSymbolicVal(kv.second.prov)) ++n;
    };
    for (const Obj &o : s.tail) scan(o);
    for (auto &kv : s.preGlobals) scan(kv.second);
    return n;
  }

  // Replace every symbolic value a snapshot holds with the concrete value the capturing run computed for it
  // (DESIGN.md §22.438). This is what makes a declared setup region replayable: after it, restoring the snapshot
  // cannot disagree with anything the solver later decides, because none of those bytes is a question any more.
  // It is an under-approximation -- the frozen bytes are no longer explored -- and the caller reports it.
  // Returns false when something cannot be frozen (an array-representation object has no enumerable bytes), in
  // which case the snapshot is left as it was and the region must simply run every time.
  bool freezeSnapshot(Snapshot &s, unsigned &frozen) {
    frozen = 0;
    auto one = [&](Val &v) -> bool {
      if (!D::isSymbolicVal(v)) return true;
      auto f = d_.freezeVal(v);
      if (!f) return false;
      v = *f;
      ++frozen;
      return true;
    };
    auto scan = [&](Obj &o) -> bool {
      if (!one(o.size)) return false;
      if (o.arr) return !D::isSymbolicVal(o.data);  // array mode: bytes are a term, not cells -- nothing to freeze
      for (auto &kv : o.cells)
        if (!one(kv.second.byte) || !one(kv.second.prov) || !one(kv.second.init)) return false;
      return true;
    };
    for (Obj &o : s.tail) if (!scan(o)) return false;
    for (auto &kv : s.preGlobals) if (!scan(kv.second)) return false;
    return true;
  }

  // Diagnostic for the count above: WHICH object, and which byte. Without it a refusal says only that the region
  // is not replayable, which is the one thing a harness author cannot act on. HLIR_DEBUG_SETUP prints it.
  std::vector<std::string> symbolicWhereIn(const Snapshot &s, unsigned max = 24) const {
    std::vector<std::string> out;
    auto scan = [&](const Obj &o) {
      if (out.size() >= max) return;
      std::string key = stableKeyOf(o);
      if (key.empty()) key = "obj#" + std::to_string(o.id);
      if (D::isSymbolicVal(o.size)) out.push_back(key + " : symbolic SIZE");
      if (o.arr) { if (D::isSymbolicVal(o.data)) out.push_back(key + " : symbolic array contents"); return; }
      for (auto &kv : o.cells) {
        if (out.size() >= max) return;
        if (D::isSymbolicVal(kv.second.byte)) out.push_back(key + " +" + std::to_string(kv.first));
        else if (D::isSymbolicVal(kv.second.prov)) out.push_back(key + " +" + std::to_string(kv.first) + " (provenance)");
      }
    };
    for (const Obj &o : s.tail) scan(o);
    for (auto &kv : s.preGlobals) scan(kv.second);
    return out;
  }

  // ---------------------------------------------------------------- evidence (DESIGN.md §22.369)
  //
  // Read-only, side-effect free: every value is inspected with D::peekVal/isSymbolicVal, never constValue(), which
  // on the concolic domain counts a concretised pointer and would make the `concretized_pointer` assumption
  // include reads that are merely being reported.
  // A name for an object that survives a second pass (DESIGN.md §22.375). Preference order:
  //   1. the record type the IR attributed to it -- "<tag>#<record size>", already computed for frontier objects.
  //      Type beats site: two allocation sites of the same struct are the same piece of state to a reader.
  //   2. the allocation SITE -- function plus source line. A property of the program, not of this run.
  // Both carry the byte size, because the same site under a different configuration can allocate a different
  // object, and silently merging those two would be a claim we cannot support. Empty when neither is available:
  // the caller then keeps the raw id, which at least does not pretend to be comparable.
  std::string stableKeyOf(const Obj &o) const {
    std::string sz;
    if (auto c = D::peekVal(o.size))
      if (!D::isSymbolicVal(o.size)) sz = "#" + std::to_string(c->getZExtValue());
    if (!o.specName.empty()) return o.specName;
    if (!o.pointeeKey.empty()) return o.pointeeKey;  // already of the form "<tag>#<size>"
    if (!o.siteFn || !o.siteLoc || !o.siteLoc->valid()) return {};
    std::string file = o.siteLoc->file;
    size_t slash = file.find_last_of('/');
    if (slash != std::string::npos) file = file.substr(slash + 1);
    return o.siteFn->name + "@" + file + ":" + std::to_string(o.siteLoc->line) + sz;
  }

  ObjEvidence objEvidence(uint32_t id, unsigned maxBytes = 24) const {
    ObjEvidence e;
    if (id < 1 || id > objs_.size()) return e;
    const Obj &o = objs_[id - 1];
    e.id = id;
    switch (o.kind) {
      case ObjKind::Param:  e.kind = "param"; break;
      case ObjKind::Global: e.kind = "global"; break;
      case ObjKind::Stack:  e.kind = "stack"; break;
      default:              e.kind = "heap"; break;
    }
    for (auto &kv : globals_)
      if (kv.second == id) { e.name = kv.first; break; }
    if (auto c = D::peekVal(o.size)) { e.sizeKnown = !D::isSymbolicVal(o.size); e.size = c->getZExtValue(); }
    e.progWritten = o.progWritten;
    e.frontier = o.frontier;
    e.inputContent = o.inputContent;
    e.unknownContent = o.unknownContent;
    e.stableKey = stableKeyOf(o);
    // Array representation keeps no per-byte cells, so the bytes cannot be enumerated; say so rather than
    // reporting "all zero", which would be a lie in the direction that matters.
    if (o.arr) { e.truncated = true; return e; }
    for (auto &kv : o.cells) {
      if (D::isSymbolicVal(kv.second.byte)) { ++e.symbolicBytes; continue; }
      auto c = D::peekVal(kv.second.byte);
      if (!c || c->isZero()) continue;
      if (e.nonZero.size() >= maxBytes) { e.truncated = true; break; }
      e.nonZero.push_back({kv.first, static_cast<uint8_t>(c->getZExtValue() & 0xff)});
    }
    return e;
  }

  // Every global the run actually touched: one the program wrote, or one some read materialised cells for. A
  // global nothing ever looked at is not evidence, and a kernel module has thousands of them.
  std::vector<ObjEvidence> globalEvidence(unsigned maxBytes = 24, size_t maxObjs = 64) const {
    std::vector<ObjEvidence> out;
    for (auto &kv : globals_) {
      if (kv.second < 1 || kv.second > objs_.size()) continue;
      const Obj &o = objs_[kv.second - 1];
      if (o.kind != ObjKind::Global) continue;
      if (!o.progWritten && o.cells.empty() && !o.arr) continue;
      if (out.size() >= maxObjs) break;
      out.push_back(objEvidence(kv.second, maxBytes));
    }
    return out;
  }

  // The single object a pointer denotes, with its byte offset when that is concrete. Returns id 0 when the pointer
  // is symbolic enough to denote several objects -- in which case there is no single number to report.
  void pointerEvidence(const Ptr &p, uint32_t &obj, bool &offKnown, int64_t &off, bool &offSym) const {
    obj = 0; offKnown = false; off = 0; offSym = D::isSymbolicVal(p.off);
    if (auto o = D::peekVal(p.obj)) {
      uint64_t id = o->getZExtValue();
      if (id >= 1 && id <= objs_.size() && !D::isSymbolicVal(p.obj)) obj = static_cast<uint32_t>(id);
    }
    if (auto c = D::peekVal(p.off)) {
      offKnown = !offSym;
      off = c->getBitWidth() <= 64 ? c->getSExtValue() : 0;
    }
  }

  // G2 (DESIGN.md §22.362 follow-up, §22.374): a global the PROGRAM never wrote still holds what its static
  // initialiser gave it, and a handler is never called in that state -- the module's own init would have set it.
  // Promoting it to an unconstrained value removes that narrowing. It is a WIDENING (the branch it gates becomes
  // explorable in both directions instead of being decided concretely with no fork), so it cannot hide a defect.
  //
  // Restricted to `offs`, the TARGET SET: the offsets this entry's call chain actually reads. Promoting every
  // unwritten global would make thousands of them symbolic; the entries measured on sound/core read two or three.
  // The bytes are `harness`-labelled, not attacker data -- nobody outside chooses an uninitialised global's value.
  //
  // Returns false when the global does not exist here or the program DID write it (then its value is the
  // program's, not an artefact of the module not having run, and §22.362 already excludes it).
  template <class MkByte>
  bool promoteUnwrittenGlobal(const std::string &name, const std::set<uint64_t> &offs, MkByte mk) {
    auto it = globals_.find(name);
    if (it == globals_.end() || it->second < 1 || it->second > objs_.size()) return false;
    Obj &o = objs_[it->second - 1];
    if (o.kind != ObjKind::Global || o.progWritten || o.isConst || o.arr) return false;
    uint64_t size = 0;
    if (auto c = D::peekVal(o.size)) size = c->getZExtValue();
    bool any = false;
    for (uint64_t off : offs) {
      if (size && off >= size) continue;
      Cell c;
      c.prov = idVal(0);
      c.byte = mk(name + "+" + std::to_string(off));
      c.init = boolVal(true);
      o.cells[off] = std::move(c);
      o.promotedOffs.insert(off);
      any = true;
    }
    return any;
  }

  size_t objectCount() const { return objs_.size(); }

  // While a log is attached, every object this memory WRITES is recorded (by id). It is what tells a setup-region
  // snapshot which objects that already existed it has to save: §22.438's first version saved the objects the
  // region CREATED plus the globals, and silently lost the harness's own stack slots -- the `alloca` holding
  // libxml2's `xmlSchemaPtr schema` is written inside the region and created before it, so every restored run
  // read an uninitialised pointer and carried on. With `--ub-continue uninit_read` set, as it is for libxml2,
  // that did not even stop the run: it just analysed a different program and reported less.
  void setWriteLog(std::set<uint32_t> *log) { writeLog_ = log; }

  // `alsoSave`: ids of objects BELOW `base` that must be saved too (the ones a write log recorded). Globals are
  // always saved, as they always were.
  Snapshot snapshotSince(size_t base, const std::set<uint32_t> *alsoSave = nullptr) const {
    Snapshot s;
    s.base = base;
    s.lastId = lastId_;
    s.globals = globals_;
    for (size_t i = base; i < objs_.size(); ++i) s.tail.push_back(objs_[i]);
    for (size_t i = 0; i < base && i < objs_.size(); ++i)
      if (objs_[i].kind == ObjKind::Global || (alsoSave && alsoSave->count(objs_[i].id)))
        s.preGlobals.push_back({i, objs_[i]});
    s.valid = true;
    return s;
  }

  // Does a RESTORED setup region actually equal a region that ran again (DESIGN.md §22.441)?
  //
  // This is the question §22.440's two defects were: a snapshot that silently lost the harness's own stack
  // slots, and markers that were only honoured when a cache was attached. Both were found by noticing a
  // finding had gone missing and working backwards. That is the wrong way round -- a checkpoint whose
  // restored state differs from a fresh run is a bug BY DEFINITION, and the engine can say so itself.
  // `HLIR_SETUP_VERIFY=1` runs the region again instead of restoring it and calls this.
  //
  // `cached` is the snapshot taken (and FROZEN) by the capturing run; `fresh` is one taken the same way by a
  // later run. Differences are reported, not fixed: the caller prints them. Freezing is itself a difference
  // the caller is told about separately, so a cell that is concrete here and symbolic there is reported --
  // it is exactly the case where a restored run explores something a fresh one would not.
  std::vector<std::string> diffSnapshots(const Snapshot &cached, const Snapshot &fresh,
                                         unsigned max = 24) const {
    std::vector<std::string> out;
    auto add = [&](const std::string &m) { if (out.size() < max) out.push_back(m); };
    if (cached.base != fresh.base)
      add("the region started at a different object count (" + std::to_string(cached.base) + " vs " +
          std::to_string(fresh.base) + ")");
    if (cached.tail.size() != fresh.tail.size())
      add("the region created a different number of objects (" + std::to_string(cached.tail.size()) + " vs " +
          std::to_string(fresh.tail.size()) + ")");
    if (cached.lastId != fresh.lastId)
      add("lastId " + std::to_string(cached.lastId) + " vs " + std::to_string(fresh.lastId));
    if (cached.globals != fresh.globals) add("the global name->id table differs");
    auto objDiff = [&](const char *where, const Obj &a, const Obj &b) {
      std::string key = stableKeyOf(a);
      if (key.empty()) key = "obj#" + std::to_string(a.id);
      key = std::string(where) + " " + key;
      if (a.id != b.id) { add(key + ": id " + std::to_string(a.id) + " vs " + std::to_string(b.id)); return; }
      if (a.kind != b.kind) add(key + ": kind differs");
      if (!D::same(a.size, b.size)) add(key + ": size differs");
      if (!D::same(a.alive, b.alive)) add(key + ": liveness differs");
      if (a.arr != b.arr) { add(key + ": array representation on one side only"); return; }
      if (a.arr) { if (!D::same(a.data, b.data)) add(key + ": array contents differ"); return; }
      if (a.cells.size() != b.cells.size())
        add(key + ": " + std::to_string(a.cells.size()) + " written cell(s) vs " +
            std::to_string(b.cells.size()));
      for (auto &kv : a.cells) {
        if (out.size() >= max) return;
        auto it = b.cells.find(kv.first);
        if (it == b.cells.end()) { add(key + " +" + std::to_string(kv.first) + ": written only in the cached run"); continue; }
        if (!D::same(kv.second.byte, it->second.byte)) add(key + " +" + std::to_string(kv.first) + ": byte differs");
        else if (!D::same(kv.second.prov, it->second.prov)) add(key + " +" + std::to_string(kv.first) + ": provenance differs");
        else if (!D::same(kv.second.init, it->second.init)) add(key + " +" + std::to_string(kv.first) + ": initialisedness differs");
        else if (kv.second.pidx != it->second.pidx) add(key + " +" + std::to_string(kv.first) + ": pointer-fragment index differs");
      }
      for (auto &kv : b.cells)
        if (!a.cells.count(kv.first)) add(key + " +" + std::to_string(kv.first) + ": written only in the fresh run");
    };
    for (size_t i = 0; i < cached.tail.size() && i < fresh.tail.size(); ++i)
      objDiff("created", cached.tail[i], fresh.tail[i]);
    // The pre-existing objects each run saved. A DIFFERENT SET is itself the defect §22.440 fixed, so the
    // asymmetry is reported before the contents are compared.
    std::map<size_t, const Obj *> ca, fa;
    for (auto &kv : cached.preGlobals) ca[kv.first] = &kv.second;
    for (auto &kv : fresh.preGlobals) fa[kv.first] = &kv.second;
    for (auto &kv : ca) {
      auto it = fa.find(kv.first);
      if (it == fa.end()) add("pre-existing object at slot " + std::to_string(kv.first) +
                              " was saved by the cached run only");
      else objDiff("pre-existing", *kv.second, *it->second);
    }
    for (auto &kv : fa)
      if (!ca.count(kv.first)) add("pre-existing object at slot " + std::to_string(kv.first) +
                                   " was saved by the fresh run only");
    return out;
  }

  // Returns false (changing nothing) when the live memory cannot accept this snapshot -- the object numbering below
  // `base` must be the one the snapshot was taken against, or ids would shift. That cannot happen with a harness
  // generated from the same plan, but a silent mismatch here would corrupt every witness, so it is checked.
  bool restoreSnapshot(const Snapshot &s) {
    if (!s.valid || objs_.size() < s.base) return false;
    objs_.resize(s.base);
    for (auto &kv : s.preGlobals) {
      if (kv.first >= objs_.size()) return false;
      objs_[kv.first] = kv.second;
    }
    for (auto &o : s.tail) objs_.push_back(o);
    globals_ = s.globals;
    lastId_ = s.lastId;
    return true;
  }


 private:
  D &d_;
  unsigned pw_;
  std::vector<Obj> objs_;
  std::map<std::string, uint32_t> globals_;
  bool inStaticInit_ = false;  // see setInStaticInit
  uint32_t lastId_ = 0;
  const Function *siteFn_ = nullptr;
  const Loc *siteLoc_ = nullptr;
  uint64_t bound_ = 256;  // unrolling bound for symbolic-length memcpy/memset
  // synthesis frontier (see lazyFrontier()): on by default; the budget is per Memory, i.e. per run, and doubles as
  // the termination guard for a walk that never meets a NULL out there.
  std::set<uint32_t> *writeLog_ = nullptr;  // see setWriteLog
  bool lazyFrontier_ = true;
  unsigned lazyMade_ = 0;
  static constexpr unsigned kLazyBudget = 64;
  static constexpr uint64_t kFrontierObjBytes = 4096;  // the same blank object an opaque external returns
  uint64_t maxExpand_ = kMaxExpandDefault;  // see setMaxExpand(); default matches the previous hardcoded kMaxExpand
  std::function<Val(const std::string &)> inputFn_;
  std::function<Val(const std::string &)> frontierFn_;
  bool tableSelect_ = true;     // see constTableTargets (DESIGN.md Sec.22.465 / G2)
  uint64_t tableSelects_ = 0;   // how many reads were resolved that way, for the report
  bool storeSelect_ = false;    // OPT-IN, see symStoreTargets / DESIGN.md Sec.22.487
  uint64_t storeSelects_ = 0;   // how many writes were resolved that way
  std::string error_;
  bool overApprox_ = false;
};

}  // namespace hlir

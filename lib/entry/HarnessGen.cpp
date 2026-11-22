#include "hlir/entry/HarnessGen.h"

#include <algorithm>
#include <map>
#include <sstream>

#include "llvm/ADT/SmallString.h"

namespace hlir::entry {

using smt::Kind;
using smt::TermRef;

// Bytes given to a constructor parameter that is not the session: an inode, a device, a context the real caller
// owns. Zeroed, and big enough that the constructor's own field reads stay inside it.
static constexpr uint64_t kSetupCtxBytes = 512;
static constexpr uint64_t kInitArgvNameBytes = 32;  // argv[0]: a zeroed program-name buffer

std::string harnessName(const InitPlan &plan) { return "__hlir_entry_" + plan.function; }

namespace {

std::string tyOf(const smt::Sort &s) { return s.isBool ? "bool" : "i" + std::to_string(s.width); }

class Emitter {
 public:
  std::ostringstream o;

  // How many `core.heap_alloc`s this harness has emitted so far. Memory assigns object ids in allocation order
  // starting at 1, and the harness runs before the entry itself, so this counter IS the runtime object id of the
  // allocation about to be emitted -- which is what `in.o<id>+<off>` witness byte names are keyed by. Every
  // heap_alloc below must bump it through `alloc()`, or the ids drift (DESIGN.md §22.351).
  unsigned allocs = 0;
  unsigned alloc() { return ++allocs; }

  std::string fresh() { return "%h" + std::to_string(n_++); }
  void bindVar(const std::string &name, const std::string &value) { vars_[name] = value; }

  std::string emit(TermRef t) {
    auto it = memo_.find(t);
    if (it != memo_.end()) return it->second;
    std::string r = emitNew(t);
    memo_[t] = r;
    return r;
  }

  std::string constant(const llvm::APInt &v, const std::string &ty) {
    llvm::SmallString<40> s;
    v.toStringSigned(s);
    std::string r = fresh();
    o << "  " << r << " = core.const " << std::string(s) << " : " << ty << "\n";
    return r;
  }

 private:
  std::string bin(const char *op, TermRef t) {
    std::string a = emit(t->args[0]), b = emit(t->args[1]), r = fresh();
    o << "  " << r << " = core." << op << " " << a << ", " << b << " : " << tyOf(t->sort) << "\n";
    return r;
  }
  std::string cmp(const char *pred, TermRef a0, TermRef b0) {
    std::string a = emit(a0), b = emit(b0), r = fresh();
    o << "  " << r << " = core.icmp " << pred << " " << a << ", " << b << " : bool\n";
    return r;
  }
  std::string emitNew(TermRef t) {
    switch (t->kind) {
      case Kind::BoolConst: return constant(t->value, "bool");
      case Kind::BvConst: return constant(t->value, tyOf(t->sort));
      case Kind::Var: return vars_.at(t->name);
      case Kind::Not: { std::string a = emit(t->args[0]), r = fresh(); o << "  " << r << " = core.not " << a << " : bool\n"; return r; }
      case Kind::And: return bin("and", t);
      case Kind::Or: return bin("or", t);
      case Kind::Ite: {
        std::string c = emit(t->args[0]), a = emit(t->args[1]), b = emit(t->args[2]), r = fresh();
        o << "  " << r << " = core.select " << c << ", " << a << ", " << b << " : " << tyOf(t->sort) << "\n";
        return r;
      }
      case Kind::Eq: return cmp("eq", t->args[0], t->args[1]);
      case Kind::Ult: return cmp("ult", t->args[0], t->args[1]);
      case Kind::Ule: return cmp("ule", t->args[0], t->args[1]);
      case Kind::Slt: return cmp("slt", t->args[0], t->args[1]);
      case Kind::Sle: return cmp("sle", t->args[0], t->args[1]);
      case Kind::BvAdd: return bin("add", t);
      case Kind::BvSub: return bin("sub", t);
      case Kind::BvMul: return bin("mul", t);
      case Kind::BvUdiv: return bin("udiv", t);
      case Kind::BvUrem: return bin("urem", t);
      case Kind::BvSdiv: return bin("sdiv", t);
      case Kind::BvSrem: return bin("srem", t);
      case Kind::BvAnd: return bin("and", t);
      case Kind::BvOr: return bin("or", t);
      case Kind::BvXor: return bin("xor", t);
      case Kind::BvShl: return bin("shl", t);
      case Kind::BvLshr: return bin("lshr", t);
      case Kind::BvAshr: return bin("ashr", t);
      case Kind::BvNot: case Kind::BvNeg: {
        std::string a = emit(t->args[0]), r = fresh();
        o << "  " << r << " = core." << (t->kind == Kind::BvNot ? "not" : "neg") << " " << a << " : " << tyOf(t->sort) << "\n";
        return r;
      }
      case Kind::ZExt: case Kind::SExt: {
        std::string a = emit(t->args[0]), r = fresh();
        o << "  " << r << " = core." << (t->kind == Kind::ZExt ? "zext" : "sext") << " " << a << " : " << tyOf(t->sort) << "\n";
        return r;
      }
      case Kind::Extract: {
        std::string a = emit(t->args[0]), r = fresh();
        o << "  " << r << " = core.extract " << a << " {hi=" << t->hi << ", lo=" << t->lo << "} : " << tyOf(t->sort) << "\n";
        return r;
      }
      case Kind::Concat: return bin("concat", t);
      case Kind::Select: case Kind::Store: case Kind::ConstArray: break;  // arrays never occur in entry constraints
    }
    return "?";
  }

  int n_ = 0;
  std::map<TermRef, std::string> memo_;
  std::map<std::string, std::string> vars_;
};

}  // namespace

namespace {

// allocates the objects behind the pointer fields of `parent` and stores their addresses into it
// defined below, after boundCond: one `core.assume` per precondition on an integer inside `obj`
void emitWheres(Emitter &e, const InitPlan &plan, const std::vector<PlannedWhere> &wheres, const std::string &obj);

void emitFields(Emitter &e, const InitPlan &plan, const std::string &parent, const std::vector<PlannedField> &fields) {
  auto &o = e.o;
  const std::string ptrTy = "i" + std::to_string(plan.ptrWidth);
  // same_alloc (the base/end, start/end, bottom/top pointer-pair idiom): a sibling field reuses the raw allocation
  // pointer and the size term of an earlier field in this same list instead of allocating an independent object, so
  // the two pointers are provably into the same allocation (see InitGen.cpp's planFields / PlannedField::sameAllocIndex).
  // Keyed by index into `fields`; only the plain-Buffer branch below fills these in.
  std::vector<std::string> allocPtrByIdx(fields.size()), sizeByIdx(fields.size());
  for (size_t fi = 0; fi < fields.size(); ++fi) {
    const PlannedField &f = fields[fi];
    std::string val;
    if (f.kind == PlannedField::Self) {  // points back into the holding object (empty intrusive list)
      if (f.target == 0) val = parent;
      else {
        std::string toff = e.constant(llvm::APInt(plan.ptrWidth, f.target), ptrTy);
        val = e.fresh();
        o << "  " << val << " = core.ptr_add " << parent << ", " << toff << " : ptr\n";
      }
    } else if (f.kind == PlannedField::FuncPtr) {
      // select chain over the targets: selector 0 -> targets[0], ...
      val = e.fresh();
      o << "  " << val << " = core.func_addr @" << f.targets.back() << " : ptr\n";
      for (size_t i = f.targets.size() - 1; i-- > 0;) {
        std::string idx = e.constant(llvm::APInt(8, i), "i8"), c = e.fresh(), fa = e.fresh(), sel = e.fresh();
        o << "  " << c << " = core.icmp eq " << e.emit(f.selector) << ", " << idx << " : bool\n";
        o << "  " << fa << " = core.func_addr @" << f.targets[i] << " : ptr\n";
        o << "  " << sel << " = core.select " << c << ", " << fa << ", " << val << " : ptr\n";
        val = sel;
      }
    } else if (f.sameAllocIndex) {
      // same_alloc: this field is a pure view into a sibling's already-allocated object (one-past-the-end of it,
      // the base/end idiom) -- no heap_alloc of its own, so the two pointers can never disagree about which
      // allocation they share (that's the whole point: a write that advances this pointer past the sibling's real
      // end is then a real OOB write against the SAME object, not two independently-sized objects that happen to
      // be adjacent by luck of the allocator).
      const std::string &sibPtr = allocPtrByIdx[*f.sameAllocIndex];
      const std::string &sibSize = sizeByIdx[*f.sameAllocIndex];
      // `pos: inside` lands a cursor at its own offset into that same object instead of exactly at its end. The
      // offset is clamped to the sibling's real size HERE rather than asserted in the plan, because that size is not
      // always a plan-time term -- with size.from_field it is read out of the parent object at run time. Clamping
      // keeps `cursor <= limit` true by construction however big the object turns out to be (DESIGN.md §22.354).
      std::string delta = sibSize;
      if (f.sameAllocInside && f.sameAllocOff) {
        std::string raw = e.emit(f.sameAllocOff), fits = e.fresh(), cl = e.fresh();
        o << "  " << fits << " = core.icmp ult " << raw << ", " << sibSize << " : bool\n";
        o << "  " << cl << " = core.select " << fits << ", " << raw << ", " << sibSize << " : " << ptrTy << "\n";
        delta = cl;
      }
      val = e.fresh();
      o << "  " << val << " = core.ptr_add " << sibPtr << ", " << delta << " : ptr\n";
    } else {
      std::string size;
      if (f.sizeFromOffset) {
        // the object's real size is whatever the sibling length field actually holds -- read it from the parent's
        // own (already-allocated) bytes instead of picking an independent value, so the two can never disagree
        // (same "derive, don't just constrain" discipline as std::vector's three-pointer synthesis).
        std::string soff = e.constant(llvm::APInt(plan.ptrWidth, *f.sizeFromOffset), ptrTy), saddr = e.fresh(), raw = e.fresh();
        o << "  " << saddr << " = core.ptr_add " << parent << ", " << soff << " : ptr\n";
        o << "  " << raw << " = core.load " << saddr << " : i" << f.sizeFromWidth << "\n";
        if (f.sizeFromWidth < plan.ptrWidth) { size = e.fresh(); o << "  " << size << " = core." << (f.sizeFromSigned ? "sext" : "zext") << " " << raw << " : " << ptrTy << "\n"; }
        else if (f.sizeFromWidth > plan.ptrWidth) { size = e.fresh(); o << "  " << size << " = core.trunc " << raw << " : " << ptrTy << "\n"; }
        else size = raw;
        // `elem`: the sibling holds an element count, so the real allocation is count * sizeof(element) -- an array
        // of structs sized by its own count field (DESIGN.md §22.352). The multiply is done at pointer width, the
        // same width the allocation itself uses, so it wraps exactly the way the real `n * sizeof(T)` would.
        if (f.sizeFromElem > 1) {
          std::string es = e.constant(llvm::APInt(plan.ptrWidth, f.sizeFromElem), ptrTy), scaled = e.fresh();
          o << "  " << scaled << " = core.mul " << size << ", " << es << " : " << ptrTy << "\n";
          // ...but never zero elements. The field is synthesised as a non-NULL pointer, and a 0-byte object would
          // turn every access through it into an out-of-bounds report. One element is also exactly what this field
          // got before `elem` existed, so the floor can only improve on the previous behaviour, never regress it.
          std::string isz = e.fresh(), clamped = e.fresh();
          o << "  " << isz << " = core.icmp ult " << scaled << ", " << es << " : bool\n";
          o << "  " << clamped << " = core.select " << isz << ", " << es << ", " << scaled << " : " << ptrTy << "\n";
          size = clamped;
        }
      } else {
        size = e.emit(f.size);
      }
      val = e.fresh();
      e.alloc();
      o << "  " << val << " = core.heap_alloc " << size << " {kind=\"param\"" << (f.owned ? ", owned" : "")
        << (f.externallyMutable ? ", externally_mutable" : "")
        << ", content=\"" << (f.tainted ? "input" : f.unknownContent ? "unknown" : "zero") << "\"";
      if (f.tainted) o << ", taint=\"" << plan.label << "\"";
      o << ", name=\"" << f.name << "\"} : ptr\n";
      allocPtrByIdx[fi] = val;
      sizeByIdx[fi] = size;
      emitWheres(e, plan, f.wheres, val);  // against the allocation, before `at` shifts the stored pointer
      emitFields(e, plan, val, f.fields);
      if (f.at) {  // container_of: the pointer designates an embedded member, not the start of the object
        std::string aoff = e.constant(llvm::APInt(plan.ptrWidth, f.at), ptrTy), inner = e.fresh();
        o << "  " << inner << " = core.ptr_add " << val << ", " << aoff << " : ptr\n";
        val = inner;
      }
    }
    if (f.isNull) {
      std::string isn = e.fresh(), z = e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy), np = e.fresh(), sel = e.fresh();
      o << "  " << isn << " = core.i2b " << e.emit(f.isNull) << " : bool\n";
      o << "  " << np << " = core.int_to_ptr " << z << " : ptr\n";
      o << "  " << sel << " = core.select " << isn << ", " << np << ", " << val << " : ptr\n";
      val = sel;
    }
    std::string off = e.constant(llvm::APInt(plan.ptrWidth, f.offset), ptrTy), q = e.fresh();
    o << "  " << q << " = core.ptr_add " << parent << ", " << off << " : ptr\n";
    o << "  core.store " << val << ", " << q << "\n";
  }
}

// bool value: `v` (an integer of the bound's type) satisfies the bound
std::string boundCond(Emitter &e, const PlannedBound &b, const std::string &v) {
  auto &o = e.o;
  const std::string ty = "i" + std::to_string(b.width);
  std::string acc;
  auto conj = [&](const std::string &c) {
    if (acc.empty()) { acc = c; return; }
    std::string r = e.fresh();
    o << "  " << r << " = core.and " << acc << ", " << c << " : bool\n";
    acc = r;
  };
  auto cmp = [&](const char *pred, const std::string &a, const std::string &c) {
    std::string r = e.fresh();
    o << "  " << r << " = core.icmp " << pred << " " << a << ", " << c << " : bool\n";
    return r;
  };
  auto k = [&](int64_t x) { return e.constant(llvm::APInt(b.width, static_cast<uint64_t>(x), true), ty); };
  if (b.value) conj(cmp("eq", v, k(*b.value)));
  if (!b.enumValues.empty()) {
    std::string any;
    for (int64_t x : b.enumValues) {
      std::string c = cmp("eq", v, k(x));
      if (any.empty()) any = c;
      else { std::string r = e.fresh(); o << "  " << r << " = core.or " << any << ", " << c << " : bool\n"; any = r; }
    }
    conj(any);
  }
  if (b.lo) {
    conj(cmp(b.isSigned ? "sle" : "ule", k(*b.lo), v));
    bool unsignedMax = !b.isSigned && b.hi && *b.hi == -1;  // SIZE_MAX spelled as -1
    if (b.hi && !unsignedMax) conj(cmp(b.isSigned ? "sle" : "ule", v, k(*b.hi)));
  }
  if (acc.empty()) acc = cmp("eq", v, v);
  return acc;
}

// Preconditions on the integers inside one synthesised object -- a parameter's pointee, or (DESIGN.md §22.356) the
// object behind one of its pointer fields. The value is loaded from the object, because its content IS the input;
// each constraint becomes one named assumption, which the engines repair a violating seed against.
void emitWheres(Emitter &e, const InitPlan &plan, const std::vector<PlannedWhere> &wheres, const std::string &obj) {
  auto &o = e.o;
  const std::string ptrTy = "i" + std::to_string(plan.ptrWidth);
  for (auto &w : wheres) {
    std::string off = e.constant(llvm::APInt(plan.ptrWidth, w.offset), ptrTy), q = e.fresh(), v = e.fresh();
    o << "  " << q << " = core.ptr_add " << obj << ", " << off << " : ptr\n";
    o << "  " << v << " = core.load " << q << " : i" << w.width << "\n";
    std::string cond = boundCond(e, w, v);  // emits its own ops: evaluate before streaming the assume line
    o << "  core.assume " << cond << " {name=\"" << w.name << "\"}\n";
  }
}

// Preconditions on the integers inside a parameter object: values are loaded from the object (its content is the
// attacker's input) and each constraint becomes one named assumption. The engines repair a seed that violates one.
void emitPreconditions(Emitter &e, const InitPlan &plan, const PlannedParam &p, const std::string &obj) {
  auto &o = e.o;
  const std::string ptrTy = "i" + std::to_string(plan.ptrWidth);
  emitWheres(e, plan, p.wheres, obj);
  for (auto &el : p.elements) {
    uint64_t n = std::min<uint64_t>(p.sizeHi / el.elemBytes, 1024);
    std::string size = p.sizeLo == p.sizeHi ? "" : e.emit(p.size);
    std::string cnt;
    if (el.count) {
      cnt = e.emit(el.count);
      if (el.countWidth && el.countWidth < plan.ptrWidth) {
        std::string x = e.fresh();
        o << "  " << x << " = core." << (el.countSigned ? "sext" : "zext") << " " << cnt << " : " << ptrTy << "\n";
        cnt = x;
      }
    }
    std::string acc;
    for (uint64_t i = 0; i < n; ++i) {
      std::string guard;
      auto andG = [&](const std::string &c) {
        if (guard.empty()) { guard = c; return; }
        std::string r = e.fresh();
        o << "  " << r << " = core.and " << guard << ", " << c << " : bool\n";
        guard = r;
      };
      std::string off = e.constant(llvm::APInt(plan.ptrWidth, i * el.elemBytes), ptrTy);
      if (!size.empty()) {  // symbolic object size: element i exists only if it fits
        std::string need = e.constant(llvm::APInt(plan.ptrWidth, (i + 1) * el.elemBytes), ptrTy), fits = e.fresh(), zero = e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy), safe = e.fresh();
        o << "  " << fits << " = core.icmp ule " << need << ", " << size << " : bool\n";
        o << "  " << safe << " = core.select " << fits << ", " << off << ", " << zero << " : " << ptrTy << "\n";
        andG(fits);
        off = safe;
      }
      if (!cnt.empty()) {
        std::string idx = e.constant(llvm::APInt(plan.ptrWidth, i), ptrTy), in = e.fresh();
        o << "  " << in << " = core.icmp " << (el.countSigned ? "slt" : "ult") << " " << idx << ", " << cnt << " : bool\n";
        andG(in);
      }
      std::string q = e.fresh(), v = e.fresh();
      o << "  " << q << " = core.ptr_add " << obj << ", " << off << " : ptr\n";
      o << "  " << v << " = core.load " << q << " : i" << el.width << "\n";
      std::string ok = boundCond(e, el, v), term = ok;
      if (!guard.empty()) {  // not (element considered) or satisfies the bound
        std::string ng = e.fresh();
        term = e.fresh();
        o << "  " << ng << " = core.not " << guard << " : bool\n";
        o << "  " << term << " = core.or " << ng << ", " << ok << " : bool\n";
      }
      if (acc.empty()) acc = term;
      else { std::string r = e.fresh(); o << "  " << r << " = core.and " << acc << ", " << term << " : bool\n"; acc = r; }
    }
    if (!acc.empty()) o << "  core.assume " << acc << " {name=\"" << el.name << "\"}\n";
  }
}

// Writes a self-consistent libstdc++ `std::basic_string<CharT>` layout into `obj` (already allocated, zero-filled,
// `plan.params[...].size` bytes). Two free variables drive it: `p.strLen` (content length) and `p.strHeap` (1 = heap
// representation, 0 = SSO / local buffer) — see InitGen.cpp for the `sso_or_heap` legality constraint tying them
// together (SSO requires length <= local capacity). This replaces independently-symbolic `_M_p`/`_M_string_length`/
// union fields with values derived from those two variables, so no reachable state has (e.g.) a short length claimed
// together with a local-buffer pointer that does not actually point at the local buffer.
void emitStdStringContent(Emitter &e, const InitPlan &plan, const PlannedParam &p, const std::string &obj) {
  auto &o = e.o;
  const std::string ptrTy = "i" + std::to_string(plan.ptrWidth);
  const unsigned charBytes = p.charWidth / 8;
  const unsigned ptrBytes = plan.ptrWidth / 8;
  const unsigned localCap = 15 / charBytes;
  const std::string elemTy = "i" + std::to_string(p.charWidth);

  std::string len = e.emit(p.strLen);
  std::string heapBitV = e.emit(p.strHeap);
  std::string heapBool = e.fresh();
  o << "  " << heapBool << " = core.i2b " << heapBitV << " : bool\n";

  // Heap branch: a fresh tainted allocation of (length+1) elements (room for the trailing NUL libstdc++ always
  // maintains), always created (whether or not this branch is the one selected) — the same pattern already used for
  // nullable fields/parameters below (allocate unconditionally, `core.select` which address survives).
  std::string lenBytes = len;
  if (charBytes != 1) {
    std::string cb = e.constant(llvm::APInt(plan.ptrWidth, charBytes), ptrTy), m = e.fresh();
    o << "  " << m << " = core.mul " << len << ", " << cb << " : " << ptrTy << "\n";
    lenBytes = m;
  }
  std::string oneElem = e.constant(llvm::APInt(plan.ptrWidth, charBytes), ptrTy), heapSize = e.fresh();
  o << "  " << heapSize << " = core.add " << lenBytes << ", " << oneElem << " : " << ptrTy << "\n";
  std::string heapBuf = e.fresh();
  e.alloc();
  o << "  " << heapBuf << " = core.heap_alloc " << heapSize << " {kind=\"param\", content=\"input\", taint=\"" << plan.label
    << "\", name=\"" << p.name << ".heap\"} : ptr\n";
  {  // NUL terminator at heapBuf[length]
    std::string q = e.fresh(), z = e.constant(llvm::APInt(p.charWidth, 0), elemTy);
    o << "  " << q << " = core.ptr_add " << heapBuf << ", " << lenBytes << " : ptr\n";
    o << "  core.store " << z << ", " << q << "\n";
  }

  // SSO branch: write tainted content directly into obj's local-buffer region (offset 2*ptrBytes), localCap+1
  // elements, with element `len` forced to NUL (libstdc++'s invariant, same as the cstring kind's terminator) and
  // elements beyond that left as unconstrained content (never read by correct code on this branch).
  std::string localOff = e.constant(llvm::APInt(plan.ptrWidth, 2ull * ptrBytes), ptrTy), localAddr = e.fresh();
  o << "  " << localAddr << " = core.ptr_add " << obj << ", " << localOff << " : ptr\n";
  for (unsigned i = 0; i <= localCap; ++i) {
    std::string eoff = e.constant(llvm::APInt(plan.ptrWidth, static_cast<uint64_t>(i) * charBytes), ptrTy), addr = e.fresh();
    o << "  " << addr << " = core.ptr_add " << localAddr << ", " << eoff << " : ptr\n";
    std::string nd = e.fresh();
    o << "  " << nd << " = core.nondet {name=\"sso." << i << "." << p.name << "\", taint=\"" << plan.label << "\"} : " << elemTy << "\n";
    std::string idxC = e.constant(llvm::APInt(plan.ptrWidth, i), ptrTy), isEnd = e.fresh();
    o << "  " << isEnd << " = core.icmp eq " << idxC << ", " << len << " : bool\n";
    std::string zeroElem = e.constant(llvm::APInt(p.charWidth, 0), elemTy), val = e.fresh();
    o << "  " << val << " = core.select " << isEnd << ", " << zeroElem << ", " << nd << " : " << elemTy << "\n";
    o << "  core.store " << val << ", " << addr << "\n";
  }
  // Fix up the first ptrBytes of that same region to hold the capacity (== length: an exact-fit allocation, still a
  // legal libstdc++ state) when the heap branch is chosen; a no-op (reads back exactly what it just wrote) on the
  // SSO branch, where those bytes are part of the character content written above.
  {
    std::string ld = e.fresh();
    o << "  " << ld << " = core.load " << localAddr << " : " << ptrTy << "\n";
    std::string capVal = e.fresh();
    o << "  " << capVal << " = core.select " << heapBool << ", " << len << ", " << ld << " : " << ptrTy << "\n";
    o << "  core.store " << capVal << ", " << localAddr << "\n";
  }

  // `_M_p` (offset 0): the heap buffer, or the local buffer's own address.
  std::string ptrVal = e.fresh();
  o << "  " << ptrVal << " = core.select " << heapBool << ", " << heapBuf << ", " << localAddr << " : ptr\n";
  std::string off0 = e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy), q0 = e.fresh();
  o << "  " << q0 << " = core.ptr_add " << obj << ", " << off0 << " : ptr\n";
  o << "  core.store " << ptrVal << ", " << q0 << "\n";
  // `_M_string_length` (offset ptrBytes): the same in both branches.
  std::string offL = e.constant(llvm::APInt(plan.ptrWidth, ptrBytes), ptrTy), qL = e.fresh();
  o << "  " << qL << " = core.ptr_add " << obj << ", " << offL << " : ptr\n";
  o << "  core.store " << len << ", " << qL << "\n";
}

// Writes a self-consistent libstdc++ `std::vector<T>` layout into `obj` (already allocated, `plan.params[...].size`
// == 3*ptrBytes). One free variable, `p.vecLen` (the element count), drives all three pointers: `_M_start` is a
// fresh tainted allocation of `vecLen` elements, `_M_finish` and `_M_end_of_storage` are both `_M_start +
// vecLen*elemBytes` -- so `_M_start <= _M_finish == _M_end_of_storage` and `_M_finish - _M_start` is exactly a
// multiple of sizeof(T) hold unconditionally, by construction, instead of being three independent symbols that can
// disagree (see IMPLEMENTATION_PLAN "std::vector/std::map 入口参数合成自洽化").
void emitStdVectorContent(Emitter &e, const InitPlan &plan, const PlannedParam &p, const std::string &obj) {
  auto &o = e.o;
  const std::string ptrTy = "i" + std::to_string(plan.ptrWidth);
  const unsigned elemBytes = p.elemWidth / 8;
  const unsigned ptrBytes = plan.ptrWidth / 8;

  std::string lenElems = e.emit(p.vecLen);
  std::string lenBytes = lenElems;
  if (elemBytes != 1) {
    std::string eb = e.constant(llvm::APInt(plan.ptrWidth, elemBytes), ptrTy), m = e.fresh();
    o << "  " << m << " = core.mul " << lenElems << ", " << eb << " : " << ptrTy << "\n";
    lenBytes = m;
  }
  // Always allocate at least one element's worth (the same "+1 element" trick as the std::string heap branch: it
  // sidesteps relying on core.heap_alloc's behaviour for a literal 0-byte request) -- the extra tail byte(s) are
  // never addressed by correct code since `_M_end_of_storage` stops exactly at `_M_start + lenBytes`.
  std::string oneElem = e.constant(llvm::APInt(plan.ptrWidth, elemBytes), ptrTy), allocSize = e.fresh();
  o << "  " << allocSize << " = core.add " << lenBytes << ", " << oneElem << " : " << ptrTy << "\n";
  std::string start = e.fresh();
  e.alloc();
  o << "  " << start << " = core.heap_alloc " << allocSize << " {kind=\"param\", content=\"input\", taint=\"" << plan.label
    << "\", name=\"" << p.name << ".data\"} : ptr\n";
  std::string finish = e.fresh();
  o << "  " << finish << " = core.ptr_add " << start << ", " << lenBytes << " : ptr\n";

  std::string off0 = e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy), q0 = e.fresh();
  o << "  " << q0 << " = core.ptr_add " << obj << ", " << off0 << " : ptr\n";
  o << "  core.store " << start << ", " << q0 << "\n";       // _M_start
  std::string off1 = e.constant(llvm::APInt(plan.ptrWidth, ptrBytes), ptrTy), q1 = e.fresh();
  o << "  " << q1 << " = core.ptr_add " << obj << ", " << off1 << " : ptr\n";
  o << "  core.store " << finish << ", " << q1 << "\n";      // _M_finish
  std::string off2 = e.constant(llvm::APInt(plan.ptrWidth, 2ull * ptrBytes), ptrTy), q2 = e.fresh();
  o << "  " << q2 << " = core.ptr_add " << obj << ", " << off2 << " : ptr\n";
  o << "  core.store " << finish << ", " << q2 << "\n";      // _M_end_of_storage: exact-fit capacity (== _M_finish)
}

// Writes a self-consistent libstdc++ `std::map<K,V>` layout into `obj` (already allocated, `plan.params[...].size`
// == ptrBytes + 40, the `_Rb_tree_header` embedded at offset `ptrBytes`; see InitPlan.h "StdMap" and
// IMPLEMENTATION_PLAN "std::vector/std::map 入口参数合成自洽化" for why only 0 or 1 nodes are modelled). One free
// untainted variable, `p.mapHasElem`, chooses between the two real libstdc++ `_Rb_tree` shapes that need no key
// comparison at all:
//   empty:    _M_header = { color=red, parent=NULL,  left=&_M_header, right=&_M_header }, node_count=0
//   1 node:   _M_header = { color=red, parent=&node, left=&node,      right=&node      }, node_count=1
//             node      = { color=black, parent=&_M_header, left=NULL, right=NULL, key, value }
// Both are real states `_Rb_tree_header()`'s constructor (and, for the second, one `_M_insert_` call) actually
// produce -- not an invented approximation of the ABI, a genuine subset of it.
void emitStdMapContent(Emitter &e, const InitPlan &plan, const PlannedParam &p, const std::string &obj) {
  auto &o = e.o;
  const std::string ptrTy = "i" + std::to_string(plan.ptrWidth);
  const unsigned ptrBytes = plan.ptrWidth / 8;
  const unsigned keyBytes = p.keyWidth / 8, valBytes = p.valWidth / 8;
  // pair<const K, V> layout (plain struct, standard layout rules): second is placed at the first offset >= keyBytes
  // that is a multiple of valBytes (both are powers of two <= 8, as enforced in InitGen.cpp, so this matches the
  // real Itanium ABI rule without needing a record layout query).
  const unsigned secondOff = ((keyBytes + valBytes - 1) / valBytes) * valBytes;
  const unsigned pairAlign = std::max(keyBytes, valBytes);
  const unsigned pairSize = ((secondOff + valBytes + pairAlign - 1) / pairAlign) * pairAlign;
  const unsigned nodeBase = 4 * ptrBytes;  // sizeof(_Rb_tree_node_base): color(+pad) + parent + left + right
  const unsigned nodeAlign = std::max<unsigned>(ptrBytes, pairAlign);
  const unsigned nodeSize = ((nodeBase + pairSize + nodeAlign - 1) / nodeAlign) * nodeAlign;

  std::string headerAddr = e.fresh();
  {
    std::string off = e.constant(llvm::APInt(plan.ptrWidth, ptrBytes), ptrTy);
    o << "  " << headerAddr << " = core.ptr_add " << obj << ", " << off << " : ptr\n";
  }
  std::string hasElemV = e.emit(p.mapHasElem), hasElem = e.fresh();
  o << "  " << hasElem << " = core.i2b " << hasElemV << " : bool\n";

  // The node is always allocated (whether or not this branch is selected: the same "allocate unconditionally, select
  // which address survives" pattern as nullable fields and the std::string heap branch) and always holds the same
  // fixed, real libstdc++ "newly-inserted root" fields -- only whether the header links to it differs.
  std::string nodeSz = e.constant(llvm::APInt(plan.ptrWidth, nodeSize), ptrTy);
  std::string node = e.fresh();
  e.alloc();
  o << "  " << node << " = core.heap_alloc " << nodeSz << " {kind=\"param\", content=\"zero\", name=\"" << p.name << ".node\"} : ptr\n";
  auto storeAt = [&](const std::string &base, uint64_t off, const std::string &val) {
    std::string o64 = e.constant(llvm::APInt(plan.ptrWidth, off), ptrTy), q = e.fresh();
    o << "  " << q << " = core.ptr_add " << base << ", " << o64 << " : ptr\n";
    o << "  core.store " << val << ", " << q << "\n";
  };
  storeAt(node, 0, e.constant(llvm::APInt(plan.ptrWidth, 1), ptrTy));              // node._M_color = black (_S_black)
  storeAt(node, ptrBytes, headerAddr);                                            // node._M_parent = &_M_header
  storeAt(node, 2ull * ptrBytes, e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy)); // node._M_left = NULL
  storeAt(node, 3ull * ptrBytes, e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy)); // node._M_right = NULL
  std::string keyV = e.emit(p.mapKey), valV = e.emit(p.mapVal);
  storeAt(node, nodeBase, keyV);
  storeAt(node, nodeBase + secondOff, valV);

  // _M_header.{parent,left,right}/_M_node_count: select between the empty and one-node shapes.
  std::string zeroPtr = e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy);
  std::string nullPtr = e.fresh();  // a real `ptr`-typed NULL (core.select's arms, unlike core.store's value, must agree in type)
  o << "  " << nullPtr << " = core.int_to_ptr " << zeroPtr << " : ptr\n";
  std::string parentV = e.fresh();
  o << "  " << parentV << " = core.select " << hasElem << ", " << node << ", " << nullPtr << " : ptr\n";
  std::string leftRightV = e.fresh();
  o << "  " << leftRightV << " = core.select " << hasElem << ", " << node << ", " << headerAddr << " : ptr\n";
  std::string one = e.constant(llvm::APInt(plan.ptrWidth, 1), ptrTy), countV = e.fresh();
  o << "  " << countV << " = core.select " << hasElem << ", " << one << ", " << zeroPtr << " : " << ptrTy << "\n";

  storeAt(obj, ptrBytes, e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy));  // _M_header._M_color = red (_S_red), always
  storeAt(obj, 2ull * ptrBytes, parentV);       // _M_header._M_parent
  storeAt(obj, 3ull * ptrBytes, leftRightV);    // _M_header._M_left
  storeAt(obj, 4ull * ptrBytes, leftRightV);    // _M_header._M_right
  storeAt(obj, 5ull * ptrBytes, countV);        // _M_node_count
}

}  // namespace

std::string generateHarness(const InitPlan &plan, std::map<std::string, unsigned> *paramObjId) {
  Emitter e;
  auto &o = e.o;
  o << "// Generated entry harness for @" << plan.function << " (origin: " << plan.specFile << ":" << plan.specLine << ")\n";
  o << "core.func @" << harnessName(plan) << "() -> " << plan.retTy->str() << " {\n^entry:\n";
  const std::string ptrTy = "i" + std::to_string(plan.ptrWidth);

  // 1. free inputs
  for (auto &v : plan.vars) {
    std::string r = e.fresh();
    o << "  " << r << " = core.nondet {name=\"" << v.var->name << "\"";
    if (!v.taint.empty()) o << ", taint=\"" << v.taint << "\"";
    o << "} : i" << v.var->sort.width << "\n";
    e.bindVar(v.var->name, r);
  }
  // 2. legality assumptions, named after the specification lines they come from
  for (auto &c : plan.constraints) {
    std::string t = e.emit(c.term);
    o << "  core.assume " << t << " {name=\"" << c.name << "\"}\n";
  }
  // 3. parameter objects and call arguments
  std::vector<std::string> args, argTys;
  for (auto &p : plan.params) {
    if (p.kind == PlannedParam::Scalar) {
      std::string v = p.value->kind == Kind::Var ? e.emit(p.value) : e.emit(p.value);
      if (p.isBool) {
        std::string b = e.fresh();
        o << "  " << b << " = core.i2b " << v << " : bool\n";
        v = b;
      }
      args.push_back(v);
      continue;
    }
    std::string size = e.emit(p.size);
    std::string obj = e.fresh();
    unsigned objId = e.alloc();
    if (paramObjId) (*paramObjId)[p.name] = objId;
    // StdString/StdVector/StdMap: every byte of the fixed-size object is about to be overwritten by the matching
    // emitStdXContent below with values derived from the kind's own free variables, so start from an untainted zero
    // fill rather than wasting a symbolic byte per offset on content nothing ever reads (and that would otherwise
    // reintroduce the very "every field independently symbolic" problem these kinds exist to avoid).
    bool zeroFill = p.kind == PlannedParam::StdString || p.kind == PlannedParam::StdVector || p.kind == PlannedParam::StdMap || !p.tainted;
    // ...and of those, the ones the spec says nobody initialised to anything knowable get symbolic,
    // harness-labelled bytes instead of a zero fill (`content: unknown`, DESIGN.md §22.381). The std::X kinds are
    // excluded by construction: their layout is about to be overwritten by a self-consistent one.
    bool unknownFill = zeroFill && p.unknownContent && p.kind != PlannedParam::StdString &&
                       p.kind != PlannedParam::StdVector && p.kind != PlannedParam::StdMap;
    o << "  " << obj << " = core.heap_alloc " << size << " {kind=\"param\"" << (p.owned ? ", owned" : "")
      << (p.externallyMutable ? ", externally_mutable" : "")
      << ", content=\"" << (!zeroFill ? "input" : unknownFill ? "unknown" : "zero") << "\"";
    if (!zeroFill) o << ", taint=\"" << plan.label << "\"";
    o << ", name=\"" << p.name << "\"} : ptr\n";
    if (p.kind == PlannedParam::CString && p.tainted) {
      // the last byte of the object, or an earlier one, is NUL: size == k+1 implies byte[k] == 0 for every candidate k
      std::string zero8 = e.constant(llvm::APInt(8, 0), "i8");
      std::string name = "init." + p.name + ".cstring@" + plan.specFile + ":" + std::to_string(p.line);
      for (uint64_t k = p.sizeLo - 1; k < p.sizeHi; ++k) {
        std::string off = e.constant(llvm::APInt(plan.ptrWidth, k), ptrTy), q = e.fresh(), b = e.fresh(), isz = e.fresh();
        o << "  " << q << " = core.ptr_add " << obj << ", " << off << " : ptr\n";
        o << "  " << b << " = core.load " << q << " : i8\n";
        o << "  " << isz << " = core.icmp eq " << b << ", " << zero8 << " : bool\n";
        if (p.sizeLo == p.sizeHi) {
          o << "  core.assume " << isz << " {name=\"" << name << "\"}\n";
        } else {
          std::string sk = e.constant(llvm::APInt(plan.ptrWidth, k + 1), ptrTy), eq = e.fresh(), ne = e.fresh(), ok = e.fresh();
          o << "  " << eq << " = core.icmp eq " << size << ", " << sk << " : bool\n";
          o << "  " << ne << " = core.not " << eq << " : bool\n";
          o << "  " << ok << " = core.or " << ne << ", " << isz << " : bool\n";
          o << "  core.assume " << ok << " {name=\"" << name << "\"}\n";
        }
      }
    }
    bool constructed = p.name == "this" && !plan.ctorFunction.empty();
    if (constructed) {
      // run the class's real constructor on `this` instead of the generic field-linking heuristic below: the
      // constructor body sets up whatever invariants (vptr, sentinel nodes, ...) the class actually relies on. Extra
      // parameters beyond `this` (default-argument ones `core` does not carry a value for) are passed 0/false.
      std::string call = "core.call @" + plan.ctorFunction + "(" + obj;
      for (Type *t : plan.ctorExtraParamTys) {
        std::string z = e.fresh();
        o << "  " << z << " = core.const " << (t->isBool() ? "false : bool" : "0 : i" + std::to_string(t->width())) << "\n";
        call += ", " + z;
      }
      o << "  " << call << ")\n";
      {  // same top-of-call-stack "uncaught exception" safety net as the real entry call below
        std::string eo = e.fresh(), ev = e.fresh(), ok = e.fresh();
        o << "  " << eo << " = core.global_addr @__hlir_exc_obj {size=8} : ptr\n  " << ev << " = core.load " << eo << " {waived=\"object known\"} : ptr\n  "
          << ok << " = core.is_null " << ev << " : bool\n  core.assume " << ok << " {terminates=\"uncaught_exception\"}\n";
      }
    } else {
      emitFields(e, plan, obj, p.fields);  // before a possible NULL replaces the pointer
      emitPreconditions(e, plan, p, obj);
      if (p.kind == PlannedParam::StdString) emitStdStringContent(e, plan, p, obj);
      else if (p.kind == PlannedParam::StdVector) emitStdVectorContent(e, plan, p, obj);
      else if (p.kind == PlannedParam::StdMap) emitStdMapContent(e, plan, p, obj);
    }
    if (p.at) {
      std::string aoff = e.constant(llvm::APInt(plan.ptrWidth, p.at), ptrTy), inner = e.fresh();
      o << "  " << inner << " = core.ptr_add " << obj << ", " << aoff << " : ptr\n";
      obj = inner;
    }
    if (p.isNull) {
      std::string isn = e.fresh(), z = e.constant(llvm::APInt(plan.ptrWidth, 0), ptrTy), np = e.fresh(), sel = e.fresh();
      o << "  " << isn << " = core.i2b " << e.emit(p.isNull) << " : bool\n";
      o << "  " << np << " = core.int_to_ptr " << z << " : ptr\n";
      o << "  " << sel << " = core.select " << isn << ", " << np << ", " << obj << " : ptr\n";
      obj = sel;
    }
    args.push_back(obj);
  }
  // 3a-bis. the session constructor (`setup:`, DESIGN.md §22.368 §7).
  //
  // Emitted AFTER the entry's parameter objects -- it needs the session object they contain -- and BEFORE the
  // project initialiser, which is where the real order puts it only in the sense that both precede the handler;
  // what actually matters here is object numbering: the parameters keep ids 1..N and everything this call
  // allocates comes after, so `paramObjId` and every `in.o<id>+<off>` witness name stay valid (§22.351).
  //
  // The constructor's OTHER parameters get zeroed objects of their pointee size. They are the kernel-owned context
  // the real caller passes (an inode, a device), not attacker input; synthesising them as attacker data would
  // taint the whole session. That is a narrowing, and the report names it.
  if (plan.setup.valid && plan.setup.sessionParamIdx < args.size()) {
    std::vector<std::string> cargs;
    for (size_t i = 0; i < plan.setup.ctorParamTys.size(); ++i) {
      if (i == plan.setup.ctorParamIdx) { cargs.push_back(args[plan.setup.sessionParamIdx]); continue; }
      const Type *ct = plan.setup.ctorParamTys[i];
      if (ct->isPtr()) {
        // NOTE: `constant()` EMITS its own `core.const` line, so it must be called before the line that uses it,
        // never inlined into one -- doing that splices the constant into the middle of the heap_alloc.
        std::string csz = e.constant(llvm::APInt(plan.ptrWidth, kSetupCtxBytes), ptrTy);
        std::string obj = e.fresh();
        e.alloc();
        o << "  " << obj << " = core.heap_alloc " << csz
          << " {kind=\"param\", content=\"zero\", name=\"setup.ctx" << i << "\"} : ptr\n";
        cargs.push_back(obj);
      } else if (ct->isBool()) {
        std::string zc = e.constant(llvm::APInt(8, 0), "i8");
        std::string b = e.fresh();
        o << "  " << b << " = core.i2b " << zc << " : bool\n";
        cargs.push_back(b);
      } else {
        unsigned w = ct->width() ? ct->width() : 32;
        cargs.push_back(e.constant(llvm::APInt(w, 0), "i" + std::to_string(w)));
      }
    }
    std::string ccall = "core.call @" + plan.setup.function + "(";
    for (size_t i = 0; i < cargs.size(); ++i) ccall += (i ? ", " : "") + cargs[i];
    ccall += ")";
    if (plan.setup.retTy && !plan.setup.retTy->isVoid()) {
      std::string r = e.fresh();
      o << "  " << r << " = " << ccall << " : " << plan.setup.retTy->str() << "\n";
      // `success:` -- the constructor failed means it built nothing, so there is no session to hand the entry and
      // nothing after this point is a statement about the program. Assumed, and named in the report.
      if (plan.setup.success == "ret == 0" && plan.setup.retTy->width()) {
        std::string z = e.constant(llvm::APInt(plan.setup.retTy->width(), 0), plan.setup.retTy->str());
        std::string ok = e.fresh();  // z is emitted by the line above, before this one uses it
        o << "  " << ok << " = core.icmp eq " << r << ", " << z << " : bool\n";
        o << "  core.assume " << ok << " {name=\"setup.success\"}\n";
      }
    } else {
      o << "  " << ccall << "\n";
    }
  }

  // 3b. the project's own initialiser(s), immediately before the entry (InitPlan::prologue, DESIGN.md §22.368).
  //
  // A handler is never called in the state we start it in: until `module_init` (or `_init`, or a constructor) has
  // run, every global still holds its static initialiser. Running it here is not an approximation of anything --
  // it is the program's own code, executed.
  //
  // AFTER the parameter objects on purpose. Memory numbers objects in allocation order from 1 and `paramObjId`
  // relies on the parameters coming first, so an initialiser that allocates would otherwise shift every witness
  // name by however many objects it happened to create -- the §22.351 failure, where a confirmed finding printed a
  // witness that does not reach it. Nothing an initialiser does reads our synthetic parameter objects, so the
  // order costs nothing.
  // Bracketed by markers so the engine can take a snapshot of what the initialiser produced and skip re-running it
  // on every later run of the same entry (Memory::Snapshot, DESIGN.md §22.368). Explicit markers rather than
  // "the last prologue call returned" because the engine must not have to infer where a textual section ends.
  if (!plan.prologue.empty()) o << "  core.trace {event=\"hlir.prologue.begin\"}\n";
  for (auto &pc : plan.prologue) {
    // An initialiser with parameters is `main(int argc, char **argv)`: for a server or a QNX resource manager that
    // IS the initialiser. Synthesised as the shape a program is really started with -- argc = 1 and an argv of two
    // pointer slots, the second a NULL terminator, the first pointing at a short zeroed name buffer. A module that
    // branches on its command line is therefore analysed for ONE command line, which the report names.
    std::vector<std::string> pargs;
    const size_t argc = plan.argv.size();
    for (size_t i = 0; i < pc.paramTys.size(); ++i) {
      const Type *pt = pc.paramTys[i];
      if (pt->isPtr()) {
        if (argc) {
          // The project stated how the program is started (§22.380), so build THAT argv: one NUL-terminated
          // object per word, and a vector of argc+1 slots whose last one is the NULL the standard requires
          // (getopt and every hand-rolled parser stop there).
          std::vector<std::string> slots;
          for (size_t k = 0; k < argc; ++k) {
            const std::string &w = plan.argv[k];
            std::string sz = e.constant(llvm::APInt(plan.ptrWidth, w.size() + 1), ptrTy);
            std::string obj = e.fresh();
            e.alloc();
            o << "  " << obj << " = core.heap_alloc " << sz << " {kind=\"param\", content=\"zero\", name=\"init.argv"
              << k << "\"} : ptr\n";
            for (size_t b = 0; b < w.size(); ++b) {
              std::string off = e.constant(llvm::APInt(plan.ptrWidth, b), ptrTy);
              std::string ch = e.constant(llvm::APInt(8, static_cast<uint64_t>(static_cast<unsigned char>(w[b]))), "i8");
              std::string q = e.fresh();
              o << "  " << q << " = core.ptr_add " << obj << ", " << off << " : ptr\n";
              o << "  core.store " << ch << ", " << q << " {waived=\"harness-owned\"}\n";
            }
            slots.push_back(obj);
          }
          std::string vsz = e.constant(llvm::APInt(plan.ptrWidth, (argc + 1) * (plan.ptrWidth / 8)), ptrTy);
          std::string vec = e.fresh();
          e.alloc();
          o << "  " << vec << " = core.heap_alloc " << vsz << " {kind=\"param\", content=\"zero\", name=\"init.argv\"} : ptr\n";
          for (size_t k = 0; k < slots.size(); ++k) {
            std::string off = e.constant(llvm::APInt(plan.ptrWidth, k * (plan.ptrWidth / 8)), ptrTy);
            std::string q = e.fresh();
            o << "  " << q << " = core.ptr_add " << vec << ", " << off << " : ptr\n";
            o << "  core.store " << slots[k] << ", " << q << " {waived=\"harness-owned\"}\n";
          }
          pargs.push_back(vec);
          continue;
        }
        std::string nm = e.constant(llvm::APInt(plan.ptrWidth, kInitArgvNameBytes), ptrTy);
        std::string nameObj = e.fresh();
        e.alloc();
        o << "  " << nameObj << " = core.heap_alloc " << nm << " {kind=\"param\", content=\"zero\", name=\"init.argv0\"} : ptr\n";
        std::string vsz = e.constant(llvm::APInt(plan.ptrWidth, 2 * (plan.ptrWidth / 8)), ptrTy);
        std::string vec = e.fresh();
        e.alloc();
        o << "  " << vec << " = core.heap_alloc " << vsz << " {kind=\"param\", content=\"zero\", name=\"init.argv\"} : ptr\n";
        o << "  core.store " << nameObj << ", " << vec << " {waived=\"harness-owned\"}\n";
        pargs.push_back(vec);
      } else if (pt->isBool()) {
        std::string zc = e.constant(llvm::APInt(8, 0), "i8");
        std::string b = e.fresh();
        o << "  " << b << " = core.i2b " << zc << " : bool\n";
        pargs.push_back(b);
      } else {
        unsigned w = pt->width() ? pt->width() : 32;
        // argc: the stated word count, or 1 when nothing was stated
        pargs.push_back(e.constant(llvm::APInt(w, i == 0 ? (argc ? argc : 1) : 0), "i" + std::to_string(w)));
      }
    }
    std::string pcall = "core.call @" + pc.function + "(";
    for (size_t i = 0; i < pargs.size(); ++i) pcall += (i ? ", " : "") + pargs[i];
    pcall += ")";
    if (pc.retTy && !pc.retTy->isVoid()) {
      std::string r = e.fresh();
      o << "  " << r << " = " << pcall << " : " << pc.retTy->str() << "\n";
    } else {
      o << "  " << pcall << "\n";
    }
  }
  if (!plan.prologue.empty()) o << "  core.trace {event=\"hlir.prologue.end\"}\n";
  // The point where the entry begins: everything before it is setup (parameter objects, the session constructor,
  // the project initialiser). The engine promotes target-set globals here, after init has had its chance to write
  // them and before the handler can read them (DESIGN.md §22.374).
  o << "  core.trace {event=\"hlir.entry.begin\"}\n";
  std::string call = "core.call @" + plan.function + "(";
  for (size_t i = 0; i < args.size(); ++i) call += (i ? ", " : "") + args[i];
  call += ")";
  // the harness is the top of the call stack: an exception that is still in flight after the real entry function
  // returns had no matching `catch` anywhere (every function it (or anything it called) passed through either
  // handled it or propagated it further — see Frontend.cpp "跨函数异常传播"/IMPLEMENTATION_PLAN), so this is
  // where "uncaught, full stop" becomes this project's pre-existing `terminateProgram`-style outcome: branchless,
  // same mechanism, just a real (not unconditionally false) assumed condition. A no-op for a program that never
  // touches the (C++-only) in-flight-exception globals at all — the load is always null, the assume always holds.
  std::string eo = e.fresh(), ev = e.fresh(), ok = e.fresh();
  std::string guard = "  " + eo + " = core.global_addr @__hlir_exc_obj {size=8} : ptr\n  " + ev + " = core.load " + eo + " {waived=\"object known\"} : ptr\n  " +
                       ok + " = core.is_null " + ev + " : bool\n  core.assume " + ok + " {terminates=\"uncaught_exception\"}\n";
  if (plan.retTy->isVoid()) {
    o << "  " << call << "\n" << guard << "  core.return\n}\n";
  } else {
    o << "  %ret = " << call << " : " << plan.retTy->str() << "\n" << guard << "  core.return %ret\n}\n";
  }
  return o.str();
}

}  // namespace hlir::entry

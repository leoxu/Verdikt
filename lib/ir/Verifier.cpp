#include "hlir/ir/Verifier.h"

#include <algorithm>
#include <functional>
#include <set>
#include <unordered_map>

#include "llvm/ADT/SmallString.h"

namespace hlir {
namespace {

class FuncVerifier {
 public:
  FuncVerifier(const Module &m, const Function &f, const VerifyOptions &o, Diagnostics &d)
      : m_(m), f_(f), opts_(o), diags_(d), ctx_(const_cast<Module &>(m).ctx) {}

  void run() {
    if (!f_.retTy) { err(nullptr, nullptr, "function has no return type"); return; }
    if (f_.isDeclaration()) return;
    buildIndex();
    if (!checkStructure()) return;  // CFG-dependent checks need well-formed blocks
    computeDominators();
    for (auto &b : f_.blocks)
      for (size_t i = 0; i < b->ops.size(); ++i) {
        checkOp(*b, *b->ops[i], i);
        checkUses(*b, *b->ops[i], i);
        if (opts_.checkCoverage) checkCoverage(*b, *b->ops[i], i);
      }
  }

 private:
  // ---------------------------------------------------------------- diagnostics
  void err(const Block *b, const Op *op, const std::string &msg) {
    std::string c = "@" + f_.name;
    if (b) c += ", ^" + (b->name.empty() ? std::string("?") : b->name);
    if (op) c += ", core." + std::string(opInfo(op->opc).name);
    Loc l = op ? op->loc : Loc{};
    diags_.error(msg, l, c);
  }

  // ---------------------------------------------------------------- structure & CFG
  void buildIndex() {
    for (size_t bi = 0; bi < f_.blocks.size(); ++bi) {
      bidx_[f_.blocks[bi].get()] = bi;
      for (size_t oi = 0; oi < f_.blocks[bi]->ops.size(); ++oi) opIdx_[f_.blocks[bi]->ops[oi].get()] = oi;
    }
  }

  bool checkStructure() {
    bool ok = true;
    for (auto &b : f_.blocks) {
      if (b->ops.empty()) { err(b.get(), nullptr, "block is empty (missing terminator)"); ok = false; continue; }
      for (size_t i = 0; i < b->ops.size(); ++i) {
        bool term = isTerminator(b->ops[i]->opc);
        if (i + 1 == b->ops.size() && !term) { err(b.get(), b->ops[i].get(), "block does not end with a terminator"); ok = false; }
        if (i + 1 != b->ops.size() && term) { err(b.get(), b->ops[i].get(), "terminator in the middle of a block"); ok = false; }
      }
      for (auto &s : b->ops.back()->succs)
        if (!s.dest || !bidx_.count(s.dest)) { err(b.get(), b->ops.back().get(), "branch target is not a block of this function"); ok = false; }
    }
    return ok;
  }

  void computeDominators() {
    size_t n = f_.blocks.size();
    std::vector<std::vector<size_t>> preds(n);
    for (size_t i = 0; i < n; ++i)
      for (auto &s : f_.blocks[i]->ops.back()->succs) preds[bidx_[s.dest]].push_back(i);
    // reverse post-order from entry
    std::vector<size_t> post;
    std::vector<char> seen(n, 0);
    std::function<void(size_t)> dfs = [&](size_t u) {
      seen[u] = 1;
      for (auto &s : f_.blocks[u]->ops.back()->succs) {
        size_t v = bidx_[s.dest];
        if (!seen[v]) dfs(v);
      }
      post.push_back(u);
    };
    dfs(0);
    reachable_ = seen;
    std::vector<size_t> rpo(post.rbegin(), post.rend());
    std::vector<size_t> rpoNum(n, 0);
    for (size_t i = 0; i < rpo.size(); ++i) rpoNum[rpo[i]] = i;
    const size_t kUndef = static_cast<size_t>(-1);
    idom_.assign(n, kUndef);
    idom_[0] = 0;
    auto intersect = [&](size_t a, size_t b) {
      while (a != b) {
        while (rpoNum[a] > rpoNum[b]) a = idom_[a];
        while (rpoNum[b] > rpoNum[a]) b = idom_[b];
      }
      return a;
    };
    bool changed = true;
    while (changed) {
      changed = false;
      for (size_t k = 1; k < rpo.size(); ++k) {
        size_t b = rpo[k], nd = kUndef;
        for (size_t p : preds[b]) {
          if (!seen[p] || idom_[p] == kUndef) continue;
          nd = nd == kUndef ? p : intersect(p, nd);
        }
        if (nd != kUndef && idom_[b] != nd) { idom_[b] = nd; changed = true; }
      }
    }
  }

  bool dominates(size_t a, size_t b) const {
    while (true) {
      if (a == b) return true;
      if (b == 0 || idom_[b] == static_cast<size_t>(-1)) return false;
      b = idom_[b];
    }
  }

  // ---------------------------------------------------------------- uses (SSA)
  void checkUses(const Block &b, const Op &op, size_t pos) {
    size_t bi = bidx_[&b];
    if (!reachable_[bi]) return;
    op.forEachUse([&](const Value *v) {
      if (!v) { err(&b, &op, "null operand"); return; }
      if (v->kind == Value::Placeholder || !v->ty) { err(&b, &op, "operand with unresolved type/definition"); return; }
      if (v->kind == Value::BlockArg) {
        const Block *db = v->defBlock;
        if (!db || !bidx_.count(db)) { err(&b, &op, "operand is a block argument of another function"); return; }
        if (!dominates(bidx_[db], bi)) err(&b, &op, "use of block argument %" + v->name + " not dominated by its block");
        return;
      }
      const Op *d = v->defOp;
      if (!d || !opIdx_.count(d)) { err(&b, &op, "operand defined outside this function"); return; }
      size_t dbi = bidx_[d->parent];
      if (dbi == bi) {
        if (opIdx_[d] >= pos) err(&b, &op, "use of %" + v->name + " before its definition");
      } else if (!dominates(dbi, bi)) {
        err(&b, &op, "definition of %" + v->name + " does not dominate this use");
      }
    });
  }

  // ---------------------------------------------------------------- per-op rules
  bool isScalar(const Type *t) const { return t && (t->isInt() || t->isBool() || t->isPtr()); }
  bool intOrBool(const Type *t) const { return t && (t->isInt() || t->isBool()); }

  void checkSuccArgs(const Block &b, const Op &op, const Succ &s) {
    if (!s.dest) return;
    if (s.args.size() != s.dest->args.size()) {
      err(&b, &op, "branch to ^" + s.dest->name + " passes " + std::to_string(s.args.size()) + " argument(s), block expects " +
                       std::to_string(s.dest->args.size()));
      return;
    }
    for (size_t i = 0; i < s.args.size(); ++i)
      if (s.args[i] && s.args[i]->ty && s.args[i]->ty != s.dest->args[i]->ty)
        err(&b, &op, "branch argument " + std::to_string(i) + " has type " + s.args[i]->ty->str() + ", block expects " +
                         s.dest->args[i]->ty->str());
  }

  void checkOp(const Block &b, const Op &op, size_t) {
    auto E = [&](const std::string &m) { err(&b, &op, m); };
    // operand sanity first (types may be null for broken input)
    for (auto *v : op.operands)
      if (!v || !v->ty) return;  // reported by checkUses (when reachable); avoid null derefs here
    for (auto &s : op.succs)
      for (auto *v : s.args)
        if (!v || !v->ty) return;
    const auto &o = op.operands;
    Type *rt = op.resultType();
    unsigned pw = ctx_.ptrWidth();
    auto nops = [&](size_t n) {
      if (o.size() != n) { E("expected " + std::to_string(n) + " operand(s), got " + std::to_string(o.size())); return false; }
      return true;
    };
    auto needRes = [&](bool want) {
      if (want && !rt) { E("missing result"); return false; }
      if (!want && rt) { E("unexpected result"); return false; }
      return true;
    };
    auto sizeInt = [&](const Type *t) { return t->isInt() && t->width() == pw; };

    switch (op.opc) {
      case Opc::Const:
        if (!nops(0) || !needRes(true)) return;
        if (!intOrBool(rt)) E("const must have an integer or bool type");
        else if (op.constVal.getBitWidth() != (rt->isBool() ? 1u : rt->width())) E("constant width does not match its type");
        break;
      case Opc::Add: case Opc::Sub: case Opc::Mul: case Opc::UDiv: case Opc::SDiv: case Opc::URem: case Opc::SRem:
      case Opc::Shl: case Opc::LShr: case Opc::AShr:
        if (!nops(2) || !needRes(true)) return;
        if (!o[0]->ty->isInt() || o[0]->ty != o[1]->ty) E("operands must be integers of the same type");
        else if (rt != o[0]->ty) E("result type must equal the operand type");
        break;
      case Opc::And: case Opc::Or: case Opc::Xor:
        if (!nops(2) || !needRes(true)) return;
        if (!intOrBool(o[0]->ty) || o[0]->ty != o[1]->ty) E("operands must be integers (or bools) of the same type");
        else if (rt != o[0]->ty) E("result type must equal the operand type");
        break;
      case Opc::Not:
        if (!nops(1) || !needRes(true)) return;
        if (!intOrBool(o[0]->ty)) E("operand must be an integer or bool");
        else if (rt != o[0]->ty) E("result type must equal the operand type");
        break;
      case Opc::Neg:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isInt()) E("operand must be an integer");
        else if (rt != o[0]->ty) E("result type must equal the operand type");
        break;
      case Opc::ZExt: case Opc::SExt:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isInt() || !rt->isInt() || rt->width() <= o[0]->ty->width()) E("extension must go from an integer to a strictly wider integer");
        break;
      case Opc::Trunc:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isInt() || !rt->isInt() || rt->width() >= o[0]->ty->width()) E("trunc must go from an integer to a strictly narrower integer");
        break;
      case Opc::Extract: {
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isInt() || !rt->isInt()) { E("extract requires integer operand and result"); return; }
        if (!op.hasAttr("hi") || !op.hasAttr("lo")) { E("extract requires 'hi' and 'lo' attributes"); return; }
        int64_t hi = op.intAttr("hi"), lo = op.intAttr("lo");
        if (lo < 0 || hi < lo || hi >= static_cast<int64_t>(o[0]->ty->width())) E("extract range out of bounds");
        else if (rt->width() != static_cast<unsigned>(hi - lo + 1)) E("extract result width must be hi-lo+1");
        break;
      }
      case Opc::Concat:
        if (!nops(2) || !needRes(true)) return;
        if (!o[0]->ty->isInt() || !o[1]->ty->isInt() || !rt->isInt() || rt->width() != o[0]->ty->width() + o[1]->ty->width())
          E("concat result width must be the sum of operand widths");
        break;
      case Opc::ICmp:
        if (!nops(2) || !needRes(true)) return;
        if (!intOrBool(o[0]->ty) || o[0]->ty != o[1]->ty) E("icmp operands must be integers (or bools) of the same type");
        if (!rt->isBool()) E("icmp result must be bool");
        break;
      case Opc::PtrCmp:
        if (!nops(2) || !needRes(true)) return;
        if (!o[0]->ty->isPtr() || !o[1]->ty->isPtr()) E("ptr_cmp operands must be pointers");
        if (!rt->isBool()) E("ptr_cmp result must be bool");
        break;
      case Opc::Select:
        if (!nops(3) || !needRes(true)) return;
        if (!o[0]->ty->isBool()) E("select condition must be bool");
        else if (o[1]->ty != o[2]->ty || rt != o[1]->ty) E("select arms and result must have the same type");
        break;
      case Opc::B2I:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isBool() || !rt->isInt()) E("b2i must go from bool to an integer");
        break;
      case Opc::FOp: {  // floating point on bit patterns: {k="add|sub|mul|div|rem|neg|cmp.<pred>|sitofp|uitofp|fptosi|fptoui|fpext|fptrunc", fw=<float width of the operands>, rw=<float width of a float result>}
        if (!needRes(true)) return;
        const Attr *k = op.attr("k");
        if (!k) { E("fop requires a k attribute"); break; }
        for (auto *x : o) if (!x->ty->isInt()) E("fop operands must be integers (bit patterns)");
        if (!rt->isInt() && !rt->isBool()) E("fop result must be an integer or bool");
        break;
      }
      case Opc::I2B:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isInt() || !rt->isBool()) E("i2b must go from an integer to bool");
        break;
      case Opc::Br:
        if (!nops(0) || op.succs.size() != 1) { E("br requires exactly one successor"); return; }
        checkSuccArgs(b, op, op.succs[0]);
        break;
      case Opc::CondBr:
        if (!nops(1) || op.succs.size() != 2) { E("cond_br requires a condition and two successors"); return; }
        if (!o[0]->ty->isBool()) E("cond_br condition must be bool");
        checkSuccArgs(b, op, op.succs[0]);
        checkSuccArgs(b, op, op.succs[1]);
        break;
      case Opc::Switch: {
        if (!nops(1) || op.succs.empty()) { E("switch requires a scrutinee and a default successor"); return; }
        if (!o[0]->ty->isInt()) { E("switch scrutinee must be an integer"); return; }
        if (op.caseVals.size() + 1 != op.succs.size()) { E("switch case/successor count mismatch"); return; }
        unsigned w = o[0]->ty->width();
        std::set<std::string> seen;
        for (auto &cv : op.caseVals) {
          if (w < 64 && !cv.isSignedIntN(w) && !(cv.isNonNegative() && cv.getActiveBits() <= w)) E("switch case value does not fit the scrutinee type");
          llvm::SmallString<16> s;
          cv.trunc(std::min(w, 64u)).toStringUnsigned(s);
          if (!seen.insert(std::string(s)).second) E("duplicate switch case value");
        }
        for (auto &s : op.succs) checkSuccArgs(b, op, s);
        break;
      }
      case Opc::Return: {
        if (f_.retTy->isVoid()) { if (!nops(0)) return; }
        else {
          if (!nops(1)) return;
          if (o[0]->ty != f_.retTy) E("return type " + o[0]->ty->str() + " does not match function return type " + f_.retTy->str());
        }
        break;
      }
      case Opc::Unreachable:
        nops(0);
        break;
      case Opc::Call: {
        const Function *callee = m_.findFunction(op.sym);
        if (!callee) { E("call to undeclared function @" + op.sym); return; }
        if (o.size() != callee->paramTys.size()) { E("call to @" + op.sym + " has " + std::to_string(o.size()) + " argument(s), expected " + std::to_string(callee->paramTys.size())); return; }
        for (size_t i = 0; i < o.size(); ++i)
          if (o[i]->ty != callee->paramTys[i]) E("argument " + std::to_string(i) + " of call to @" + op.sym + " has type " + o[i]->ty->str() + ", expected " + callee->paramTys[i]->str());
        if (callee->retTy->isVoid() && rt) E("call to void function @" + op.sym + " must not have a result");
        if (rt && rt != callee->retTy) E("call result type " + rt->str() + " does not match @" + op.sym + " return type " + callee->retTy->str());
        break;
      }
      case Opc::Alloca:
        if (!nops(0) || !needRes(true)) return;
        if (!rt->isPtr()) E("alloca result must be ptr");
        if (op.intAttr("size", 0) <= 0) E("alloca requires a positive 'size' attribute");
        if (op.hasAttr("align") && (op.intAttr("align") <= 0 || (op.intAttr("align") & (op.intAttr("align") - 1)))) E("alloca 'align' must be a power of two");
        break;
      case Opc::HeapAlloc:
        if (!nops(1) || !needRes(true)) return;
        if (!sizeInt(o[0]->ty)) E("heap_alloc size must be i" + std::to_string(pw));
        if (!rt->isPtr()) E("heap_alloc result must be ptr");
        break;
      case Opc::Free: case Opc::LifetimeEnd:
        if (!nops(1) || !needRes(false)) return;
        if (!o[0]->ty->isPtr()) E("operand must be a pointer");
        break;
      case Opc::GlobalAddr:
        if (!nops(0) || !needRes(true)) return;
        if (!rt->isPtr()) E("global_addr result must be ptr");
        break;
      case Opc::FuncAddr:
        if (!nops(0) || !needRes(true)) return;
        if (!rt->isPtr()) E("func_addr result must be ptr");
        if (!m_.findFunction(op.sym)) E("func_addr of undeclared function @" + op.sym);
        break;
      case Opc::Load:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isPtr()) E("load address must be a pointer");
        if (!isScalar(rt)) E("load result must be an integer, bool or pointer");
        break;
      case Opc::Store:
        if (!nops(2) || !needRes(false)) return;
        if (!isScalar(o[0]->ty)) E("stored value must be an integer, bool or pointer");
        if (!o[1]->ty->isPtr()) E("store address must be a pointer");
        break;
      case Opc::PtrAdd:
        if (!nops(2) || !needRes(true)) return;
        if (!o[0]->ty->isPtr() || !sizeInt(o[1]->ty) || !rt->isPtr()) E("ptr_add requires (ptr, i" + std::to_string(pw) + ") -> ptr");
        break;
      case Opc::PtrDiff:
        if (!nops(2) || !needRes(true)) return;
        if (!o[0]->ty->isPtr() || !o[1]->ty->isPtr() || !sizeInt(rt)) E("ptr_diff requires (ptr, ptr) -> i" + std::to_string(pw));
        break;
      case Opc::IsNull:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isPtr() || !rt->isBool()) E("is_null requires ptr -> bool");
        break;
      case Opc::ObjSize:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isPtr() || !sizeInt(rt)) E("obj_size requires ptr -> i" + std::to_string(pw));
        break;
      case Opc::ObjAlive:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isPtr() || !rt->isBool()) E("obj_alive requires ptr -> bool");
        break;
      case Opc::MemCpy: case Opc::MemMove:
        if (!nops(3) || !needRes(false)) return;
        if (!o[0]->ty->isPtr() || !o[1]->ty->isPtr() || !sizeInt(o[2]->ty)) E("requires (ptr, ptr, i" + std::to_string(pw) + ")");
        break;
      case Opc::MemSet:
        if (!nops(3) || !needRes(false)) return;
        if (!o[0]->ty->isPtr() || !(o[1]->ty->isInt() && o[1]->ty->width() == 8) || !sizeInt(o[2]->ty)) E("memset requires (ptr, i8, i" + std::to_string(pw) + ")");
        break;
      case Opc::PtrToInt:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isPtr() || !rt->isInt()) E("ptr_to_int requires ptr -> integer");
        break;
      case Opc::IntToPtr:
        if (!nops(1) || !needRes(true)) return;
        if (!o[0]->ty->isInt() || !rt->isPtr()) E("int_to_ptr requires integer -> ptr");
        break;
      case Opc::Assume: case Opc::Assert:
        if (!nops(1) || !needRes(false)) return;
        if (!o[0]->ty->isBool()) E("condition must be bool");
        break;
      case Opc::Nondet:
        if (!nops(0) || !needRes(true)) return;
        if (!isScalar(rt)) E("nondet result must be an integer, bool or pointer");
        break;
      case Opc::Havoc:
        if (!nops(2) || !needRes(false)) return;
        if (!o[0]->ty->isPtr() || !sizeInt(o[1]->ty)) E("havoc requires (ptr, i" + std::to_string(pw) + ")");
        break;
      case Opc::Trace:
        needRes(false);
        break;
      case Opc::CheckNull: case Opc::CheckUaf: case Opc::CheckFree: case Opc::CheckConstWrite:
        if (!nops(1) || !needRes(false)) return;
        if (!o[0]->ty->isPtr()) E("operand must be a pointer");
        break;
      case Opc::CheckOob: case Opc::CheckUninit:
        if (!nops(1) || !needRes(false)) return;
        if (!o[0]->ty->isPtr()) E("operand must be a pointer");
        if (op.intAttr("w", 0) <= 0) E("requires a positive 'w' (access width in bytes) attribute");
        break;
      case Opc::CheckAlign:
        if (!nops(1) || !needRes(false)) return;
        if (!o[0]->ty->isPtr()) E("operand must be a pointer");
        if (op.intAttr("a", 0) <= 0) E("requires a positive 'a' (alignment) attribute");
        break;
      case Opc::CheckPtrArith:
        if (!nops(2) || !needRes(false)) return;
        if (!o[0]->ty->isPtr() || !sizeInt(o[1]->ty)) E("check.ptr_arith requires (ptr, i" + std::to_string(pw) + ")");
        break;
      case Opc::CheckSAddOvf: case Opc::CheckSSubOvf: case Opc::CheckSMulOvf: case Opc::CheckDiv: case Opc::CheckShift:
        if (!nops(2) || !needRes(false)) return;
        if (!o[0]->ty->isInt() || o[0]->ty != o[1]->ty) E("operands must be integers of the same type");
        break;
      case Opc::CheckSNegOvf:
        if (!nops(1) || !needRes(false)) return;
        if (!o[0]->ty->isInt()) E("operand must be an integer");
        break;
      case Opc::CheckFieldOob:
        if (!nops(1) || !needRes(false)) return;
        if (!o[0]->ty->isInt()) E("operand must be an integer");
        if (op.intAttr("n", 0) <= 0) E("requires a positive 'n' (declared array length) attribute");
        break;
      case Opc::CheckPtrCmp:
        if (!nops(2) || !needRes(false)) return;
        if (!o[0]->ty->isPtr() || !o[1]->ty->isPtr()) E("operands must be pointers");
        break;
      case Opc::NumOpcodes:
        break;
    }
  }

  // ---------------------------------------------------------------- UB-check coverage (DESIGN.md §18.4)
  unsigned accessBytes(const Type *t) const {
    if (t->isBool()) return 1;
    if (t->isPtr()) return ctx_.ptrWidth() / 8;
    return (t->width() + 7) / 8;
  }

  bool hasDominatingCheck(const Block &b, size_t pos, Opc kind, const std::vector<const Value *> &args, unsigned minWidth) const {
    auto matches = [&](const Op &c) {
      if (c.opc != kind || c.operands.size() != args.size()) return false;
      for (size_t i = 0; i < args.size(); ++i)
        if (c.operands[i] != args[i]) return false;
      if (minWidth && c.intAttr("w", 0) < static_cast<int64_t>(minWidth)) return false;
      return true;
    };
    size_t bi = bidx_.at(&b);
    for (size_t i = 0; i < pos; ++i)
      if (matches(*b.ops[i])) return true;
    while (bi != 0 && idom_[bi] != static_cast<size_t>(-1)) {
      bi = idom_[bi];
      for (auto &op : f_.blocks[bi]->ops)
        if (matches(*op)) return true;
    }
    return false;
  }

  void checkCoverage(const Block &b, const Op &op, size_t pos) {
    if (!reachable_[bidx_[&b]] || op.hasAttr("waived")) return;
    for (auto *v : op.operands)
      if (!v || !v->ty) return;
    auto need = [&](Opc kind, std::vector<const Value *> args, unsigned w = 0) {
      if (!hasDominatingCheck(b, pos, kind, args, w))
        err(&b, &op, std::string("missing dominating core.") + opInfo(kind).name + " (or waived=\"reason\")");
    };
    const auto &o = op.operands;
    switch (op.opc) {
      case Opc::Load:
        need(Opc::CheckNull, {o[0]});
        need(Opc::CheckUaf, {o[0]});
        need(Opc::CheckOob, {o[0]}, accessBytes(op.resultType()));
        break;
      case Opc::Store:
        need(Opc::CheckNull, {o[1]});
        need(Opc::CheckUaf, {o[1]});
        need(Opc::CheckOob, {o[1]}, accessBytes(o[0]->ty));
        break;
      case Opc::Free: need(Opc::CheckFree, {o[0]}); break;
      case Opc::UDiv: case Opc::SDiv: case Opc::URem: case Opc::SRem: need(Opc::CheckDiv, {o[0], o[1]}); break;
      case Opc::Shl: case Opc::LShr: case Opc::AShr: need(Opc::CheckShift, {o[0], o[1]}); break;
      case Opc::Add: if (op.hasAttr("sov")) need(Opc::CheckSAddOvf, {o[0], o[1]}); break;
      case Opc::Sub: if (op.hasAttr("sov")) need(Opc::CheckSSubOvf, {o[0], o[1]}); break;
      case Opc::Mul: if (op.hasAttr("sov")) need(Opc::CheckSMulOvf, {o[0], o[1]}); break;
      case Opc::Neg: if (op.hasAttr("sov")) need(Opc::CheckSNegOvf, {o[0]}); break;
      case Opc::PtrAdd: need(Opc::CheckPtrArith, {o[0], o[1]}); break;
      default: break;
    }
  }

  const Module &m_;
  const Function &f_;
  const VerifyOptions &opts_;
  Diagnostics &diags_;
  Context &ctx_;
  std::unordered_map<const Block *, size_t> bidx_;
  std::unordered_map<const Op *, size_t> opIdx_;
  std::vector<size_t> idom_;
  std::vector<char> reachable_;
};

}  // namespace

bool verifyModule(const Module &m, const VerifyOptions &opts, Diagnostics &diags) {
  return verifyNewFunctions(m, 0, opts, diags);
}

bool verifyNewFunctions(const Module &m, size_t fromIndex, const VerifyOptions &opts, Diagnostics &diags) {
  std::set<std::string> names;
  for (auto &f : m.functions)
    if (!names.insert(f->name).second) diags.error("duplicate function @" + f->name);
  for (size_t i = fromIndex; i < m.functions.size(); ++i) FuncVerifier(m, *m.functions[i], opts, diags).run();
  return !diags.hasErrors();
}

}  // namespace hlir

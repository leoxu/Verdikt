#include "hlir/ir/InvariantCheck.h"

#include <algorithm>
#include <cctype>
#include <cstring>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include "hlir/ir/Loops.h"
#include "hlir/ir/Ops.h"

namespace hlir {
namespace {

struct Local {               // one `core.alloca` of the function under study
  Op *alloca = nullptr;
  std::string name;
  Type *elem = nullptr;      // from the loads/stores that use it
  int signedEvidence = 0;    // <0 unsigned, >0 signed, 0 none
  bool ambiguous = false;
};

// ---- the locals of a function, with their element type and how the function itself compares them.
std::map<std::string, Local> localsOf(Function &f, Context &ctx) {
  std::map<Value *, Local *> byVal;
  std::map<std::string, Local> out;
  for (auto &b : f.blocks)
    for (auto &op : b->ops) {
      if (op->opc != Opc::Alloca || !op->result) continue;
      const Attr *n = op->attr("name");
      if (!n || n->s.empty()) continue;
      Local &l = out[n->s];
      l.alloca = op.get();
      l.name = n->s;
      byVal[op->result.get()] = &l;
    }
  // element type: the first load/store that touches the slot
  std::map<Value *, Local *> loadedFrom;  // loaded value -> the local it came from
  for (auto &b : f.blocks)
    for (auto &op : b->ops) {
      if (op->opc == Opc::Load && !op->operands.empty()) {
        auto it = byVal.find(op->operands[0]);
        if (it == byVal.end()) continue;
        if (!it->second->elem) it->second->elem = op->resultType();
        if (op->result) loadedFrom[op->result.get()] = it->second;
      } else if (op->opc == Opc::Store && op->operands.size() >= 2) {
        auto it = byVal.find(op->operands[1]);
        if (it != byVal.end() && !it->second->elem) it->second->elem = op->operands[0]->ty;
      }
    }
  // signedness: how the ORIGINAL function compares the loaded value, and which extension it uses
  for (auto &b : f.blocks)
    for (auto &op : b->ops) {
      int sign = 0;
      if (op->opc == Opc::ICmp && !op->pred.empty()) sign = op->pred[0] == 's' ? 1 : (op->pred[0] == 'u' ? -1 : 0);
      else if (op->opc == Opc::SExt) sign = 1;
      else if (op->opc == Opc::ZExt) sign = -1;
      if (!sign) continue;
      for (Value *v : op->operands) {
        auto it = loadedFrom.find(v);
        if (it == loadedFrom.end()) continue;
        Local &l = *it->second;
        if (l.signedEvidence && l.signedEvidence != sign) l.ambiguous = true;
        l.signedEvidence = sign;
      }
    }
  for (auto &kv : out)
    if (!kv.second.elem) kv.second.elem = ctx.intTy(32);
  return out;
}

// ---------------------------------------------------------------- the candidate's expression
//
// A deliberately small C-like grammar over the function's OWN local names. The tool, not the candidate,
// decides every width and every signedness: a name becomes a load of its alloca at the alloca's own element
// type, and a comparison takes its signedness from `Local::signedEvidence`. Writing the candidate as IR
// instead would hand those two choices back to whoever wrote it, and they are exactly the two it gets wrong.
struct ExprC {
  Builder &b;
  Context &ctx;
  std::map<std::string, Local> &locals;
  std::map<std::string, Value *> &slots;  // local name -> the alloca in the CHECK function
  bool signedMode;                        // reading used when a local's evidence is ambiguous
  std::string err;
  std::string s;
  size_t p = 0;

  void ws() { while (p < s.size() && isspace((unsigned char)s[p])) ++p; }
  bool eat(const char *t) {
    ws();
    size_t n = strlen(t);
    if (s.compare(p, n, t) != 0) return false;
    // do not let "<" eat the "<" of "<="
    if ((t[n - 1] == '<' || t[n - 1] == '>' || t[n - 1] == '!' || t[n - 1] == '=') && p + n < s.size() && s[p + n] == '=')
      return false;
    p += n;
    return true;
  }
  [[noreturn]] void fail(const std::string &m) { throw std::runtime_error(m + " at offset " + std::to_string(p)); }

  struct V { Value *v; std::string name; };  // `name` empty for non-variable operands
  bool usedFallback = false;   // a comparison where NEITHER operand had decisive evidence in the IR

  // -1 unsigned, +1 signed, 0 = the IR does not say
  int evidence(const std::string &name) const {
    auto it = locals.find(name);
    if (it == locals.end() || it->second.ambiguous) return 0;
    return it->second.signedEvidence;
  }
  bool isSigned(const std::string *name) {
    if (name) {
      int e = evidence(*name);
      if (e) return e > 0;
    }
    return signedMode;
  }
  // A comparison takes its signedness from whichever operand the IR is decisive about. Only when NEITHER is
  // does the reading fall back -- and then the candidate has to hold under BOTH, which is the over-strict
  // direction: it can cost a rejection, never buy a false acceptance.
  bool cmpSigned(const V &a, const V &c) {
    int ea = a.name.empty() ? 0 : evidence(a.name);
    int ec = c.name.empty() ? 0 : evidence(c.name);
    if (ea && ec && ea != ec) { usedFallback = true; return signedMode; }
    if (ea) return ea > 0;
    if (ec) return ec > 0;
    usedFallback = true;
    return signedMode;
  }

  V primary() {
    ws();
    if (eat("(")) { V r = expr(); if (!eat(")")) fail("expected ')'"); return r; }
    if (p < s.size() && (isdigit((unsigned char)s[p]))) {
      size_t q = p;
      long long n = strtoll(s.c_str() + p, nullptr, 0);
      while (q < s.size() && (isalnum((unsigned char)s[q]) || s[q] == 'x' || s[q] == 'X')) ++q;
      p = q;
      return {b.constInt(ctx.intTy(64), n), ""};
    }
    if (p < s.size() && (isalpha((unsigned char)s[p]) || s[p] == '_')) {
      size_t q = p;
      while (q < s.size() && (isalnum((unsigned char)s[q]) || s[q] == '_')) ++q;
      std::string nm = s.substr(p, q - p);
      p = q;
      auto sl = slots.find(nm);
      if (sl == slots.end()) fail("'" + nm + "' is not a local of this function");
      Type *t = locals[nm].elem;
      Op *ld = b.create(Opc::Load, {sl->second}, t);
      return {ld->result.get(), nm};
    }
    fail("expected a value");
  }
  V unary() {
    ws();
    if (eat("!")) { V a = unary(); return {b.unop(Opc::Not, a.v), ""}; }
    if (eat("-")) { V a = unary(); return {b.unop(Opc::Neg, a.v), ""}; }
    return primary();
  }
  // widen two integer operands to a common width, using the signedness the IR showed for each
  void unify(V &a, V &b2) {
    if (a.v->ty->isPtr() || b2.v->ty->isPtr()) return;
    unsigned wa = a.v->ty->isBool() ? 1 : a.v->ty->width(), wb = b2.v->ty->isBool() ? 1 : b2.v->ty->width();
    if (wa == wb) return;
    V &nar = wa < wb ? a : b2;
    Type *to = ctx.intTy(std::max(wa, wb));
    nar.v = b.cast(isSigned(nar.name.empty() ? nullptr : &nar.name) ? Opc::SExt : Opc::ZExt, nar.v, to);
  }
  V mul() {
    V a = unary();
    for (;;) {
      ws();
      Opc o;
      if (eat("*")) o = Opc::Mul;
      else if (eat("/")) o = Opc::UDiv;
      else if (eat("%")) o = Opc::URem;
      else return a;
      V c = unary();
      unify(a, c);
      a = {b.binop(o, a.v, c.v), ""};
    }
  }
  V add() {
    V a = mul();
    for (;;) {
      ws();
      bool plus = eat("+");
      if (!plus && !eat("-")) return a;
      V c = mul();
      if (a.v->ty->isPtr() && !c.v->ty->isPtr()) {
        if (!plus) c = {b.unop(Opc::Neg, c.v), ""};
        a = {b.ptrAdd(a.v, c.v), ""};
        continue;
      }
      if (a.v->ty->isPtr() && c.v->ty->isPtr() && !plus) {
        Op *d = b.create(Opc::PtrDiff, {a.v, c.v}, ctx.sizeTy());
        a = {d->result.get(), ""};
        continue;
      }
      unify(a, c);
      a = {b.binop(plus ? Opc::Add : Opc::Sub, a.v, c.v), ""};
    }
  }
  V cmp() {
    V a = add();
    ws();
    std::string pr;
    if (eat("<=")) pr = "le";
    else if (eat(">=")) pr = "ge";
    else if (eat("==")) pr = "eq";
    else if (eat("!=")) pr = "ne";
    else if (eat("<")) pr = "lt";
    else if (eat(">")) pr = "gt";
    else return a;
    V c = add();
    if (a.v->ty->isPtr() || c.v->ty->isPtr()) {
      if (!a.v->ty->isPtr() || !c.v->ty->isPtr()) fail("comparing a pointer with an integer");
      Op *o = b.create(Opc::PtrCmp, {a.v, c.v}, ctx.boolTy());
      o->pred = pr;
      return {o->result.get(), ""};
    }
    unify(a, c);
    bool sg = cmpSigned(a, c);
    std::string full = pr == "eq" || pr == "ne" ? pr : (sg ? "s" : "u") + pr;
    return {b.icmp(full, a.v, c.v), ""};
  }
  V andE() {
    V a = cmp();
    while (eat("&&")) { V c = cmp(); a = {b.binop(Opc::And, a.v, c.v), ""}; }
    return a;
  }
  V expr() {
    V a = andE();
    while (eat("||")) { V c = andE(); a = {b.binop(Opc::Or, a.v, c.v), ""}; }
    return a;
  }
  Value *compile(const std::string &text) {
    s = text;
    p = 0;
    V r = expr();
    ws();
    if (p != s.size()) fail("trailing text");
    if (!r.v->ty->isBool()) fail("the candidate must be a condition, not a value");
    return r.v;
  }
};


}  // namespace

InvariantInstrumentation instrumentInvariant(Module &m, const std::string &function, const std::string &header,
                                             const std::string &expr, bool signedFallback,
                                             const std::string &assertExpr, const std::string &taintLabel) {
  InvariantInstrumentation out;
  out.assertMessage = "loop invariant does not hold at the back edge";
  Function *f = m.findFunction(function);
  if (!f || f->isDeclaration()) { out.error = "no function body @" + function; return out; }
  const Loop *loop = nullptr;
  auto loops = loopsOf(*f);
  for (auto &lp : loops)
    if (lp.header->name == header) loop = &lp;
  if (!loop) { out.error = "@" + function + " has no loop with header ^" + header; return out; }

  Context &ctx = m.ctx;
  auto locals = localsOf(*f, ctx);
  std::map<std::string, Value *> slots;
  std::map<Value *, std::string> slotName;
  for (auto &kv : locals)
    if (kv.second.alloca && kv.second.alloca->result) {
      slots[kv.first] = kv.second.alloca->result.get();
      slotName[kv.second.alloca->result.get()] = kv.first;
    }

  // Locals DECLARED INSIDE the loop are a fresh object each iteration, so they are not loop-carried and
  // must not be havoc'd -- and their `core.alloca` does not dominate the preheader, so trying would not even
  // verify. C scoping guarantees a local declared in an enclosing scope has its alloca in a block that
  // dominates the header.
  std::set<std::string> declaredInLoop;
  for (const Block *bb : loop->body)
    for (auto &op : bb->ops)
      if (op->opc == Opc::Alloca && op->result) {
        auto sn = slotName.find(op->result.get());
        if (sn != slotName.end()) declaredInLoop.insert(sn->second);
      }

  // the locals the loop WRITES: those are the ones that must become arbitrary
  std::set<std::string> loopWrites;
  for (const Block *bb : loop->body)
    for (auto &op : bb->ops)
      if (op->opc == Opc::Store && op->operands.size() >= 2) {
        auto sn = slotName.find(op->operands[1]);
        if (sn != slotName.end() && !declaredInLoop.count(sn->second)) loopWrites.insert(sn->second);
      }

  Block *hdrBlock = const_cast<Block *>(loop->header);
  Block *pre = f->addBlock("iv_pre");
  Block *chk = f->addBlock("iv_check");
  for (auto &ar : hdrBlock->args) {
    pre->addArg(ar->ty, ar->name);
    chk->addArg(ar->ty, ar->name);
  }

  Builder b(m);
  b.setInsertionPoint(pre);
  for (auto &nm : loopWrites) {
    auto sl = slots.find(nm);
    if (sl == slots.end()) continue;
    Type *et = locals[nm].elem;
    if (et->isPtr()) {
      Op *cur = b.create(Opc::Load, {sl->second}, ctx.ptrTy());
      cur->setAttr("waived", Attr::string("invariant check"));
      Op *off = b.create(Opc::Nondet, {}, ctx.sizeTy());
      off->setAttr("name", Attr::string("iv.off." + nm));
      if (!taintLabel.empty()) off->setAttr("taint", Attr::string(taintLabel));
      Op *pa = b.create(Opc::PtrAdd, {cur->result.get(), off->result.get()}, ctx.ptrTy());
      pa->setAttr("waived", Attr::string("invariant check: an arbitrary position in the object it is in"));
      Op *st = b.create(Opc::Store, {pa->result.get(), sl->second}, nullptr);
      st->setAttr("waived", Attr::string("invariant check"));
    } else {
      Op *nd = b.create(Opc::Nondet, {}, et);
      nd->setAttr("name", Attr::string("iv." + nm));
      if (!taintLabel.empty()) nd->setAttr("taint", Attr::string(taintLabel));
      Op *st = b.create(Opc::Store, {nd->result.get(), sl->second}, nullptr);
      st->setAttr("waived", Attr::string("invariant check"));
    }
  }
  {
    ExprC ec{b, ctx, locals, slots, signedFallback};
    Value *v = nullptr;
    try { v = ec.compile(expr); }
    catch (const std::exception &e) { out.error = std::string("candidate: ") + e.what(); return out; }
    out.usedSignednessFallback = ec.usedFallback;
    b.create(Opc::Assume, {v});
    std::vector<Value *> args;
    for (auto &ar : pre->args) args.push_back(ar.get());
    b.br(hdrBlock, args);
  }
  b.setInsertionPoint(chk);
  {
    ExprC ec{b, ctx, locals, slots, signedFallback};
    Value *v = nullptr;
    try { v = ec.compile(assertExpr.empty() ? expr : assertExpr); }
    catch (const std::exception &e) { out.error = std::string("candidate: ") + e.what(); return out; }
    Op *as = b.create(Opc::Assert, {v});
    as->setAttr("msg", Attr::string(out.assertMessage));
    // The check block ends the call. Getting the RETURN TYPE wrong here is not cosmetic: `core.return` of an
    // i64 from a function declared `-> ptr` passed the verifier, and the caller then treated an integer as a
    // pointer -- which is how `0 == 0` came back as a violated invariant in @tok2strbuf (a `-> ptr`
    // function) while being correctly `inductive` everywhere else.
    Type *rt = f->retTy;
    if (rt->isVoid()) b.ret();
    else if (rt->isPtr()) b.ret(b.cast(Opc::IntToPtr, b.constInt(ctx.sizeTy(), 0), ctx.ptrTy()));
    else b.ret(b.constInt(rt, 0));
  }

  // rewire: edges into the header go to ^iv_pre from outside the loop, to ^iv_check from inside it
  for (auto &bb : f->blocks) {
    if (bb.get() == pre || bb.get() == chk) continue;
    Op *t = bb->terminator();
    if (!t) continue;
    bool inLoop = loop->body.count(bb.get()) != 0;
    for (auto &sc : t->succs)
      if (sc.dest == hdrBlock) sc.dest = inLoop ? chk : pre;
  }
  out.checkBlock = chk;
  return out;
}

}  // namespace hlir

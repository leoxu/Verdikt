#include "hlir/ir/IR.h"

#include <cassert>

namespace hlir {

// ---------------------------------------------------------------- Types
std::string Type::str() const {
  switch (kind_) {
    case Void: return "void";
    case Bool: return "bool";
    case Ptr: return "ptr";
    case Int: return "i" + std::to_string(width_);
  }
  return "?";
}

Type *Context::voidTy() {
  if (!void_) void_.reset(new Type(Type::Void, 0));
  return void_.get();
}
Type *Context::boolTy() {
  if (!bool_) bool_.reset(new Type(Type::Bool, 1));
  return bool_.get();
}
Type *Context::ptrTy() {
  if (!ptr_) ptr_.reset(new Type(Type::Ptr, 0));
  return ptr_.get();
}
Type *Context::intTy(unsigned width) {
  auto &slot = ints_[width];
  if (!slot) slot.reset(new Type(Type::Int, width));
  return slot.get();
}

// ---------------------------------------------------------------- Op
const Attr *Op::attr(const std::string &name) const {
  for (auto &p : attrs)
    if (p.first == name) return &p.second;
  return nullptr;
}
void Op::setAttr(const std::string &name, Attr a) {
  for (auto &p : attrs)
    if (p.first == name) { p.second = std::move(a); return; }
  attrs.emplace_back(name, std::move(a));
}
int64_t Op::intAttr(const std::string &name, int64_t dflt) const {
  const Attr *a = attr(name);
  return a && (a->kind == Attr::Int || a->kind == Attr::Bool) ? a->i : dflt;
}

// ---------------------------------------------------------------- Block / Function / Module
Value *Block::addArg(Type *t, std::string n) {
  auto v = std::make_unique<Value>(Value::BlockArg, t);
  v->name = std::move(n);
  v->defBlock = this;
  v->index = static_cast<unsigned>(args.size());
  args.push_back(std::move(v));
  return args.back().get();
}

Op *Block::append(std::unique_ptr<Op> op) {
  op->parent = this;
  if (op->result) {
    op->result->defOp = op.get();
    op->result->defBlock = this;
  }
  ops.push_back(std::move(op));
  return ops.back().get();
}

Op *Block::terminator() const {
  if (ops.empty() || !isTerminator(ops.back()->opc)) return nullptr;
  return ops.back().get();
}

Block *Function::addBlock(std::string n) {
  auto b = std::make_unique<Block>(std::move(n));
  b->parent = this;
  blocks.push_back(std::move(b));
  return blocks.back().get();
}

Function *Module::findFunction(const std::string &name) const {
  for (auto &f : functions)
    if (f->name == name) return f.get();
  return nullptr;
}

Function *Module::addFunction(std::string name, std::vector<Type *> params, Type *ret) {
  Function *f = addDeclaration(std::move(name), std::move(params), ret);
  Block *entry = f->addBlock("entry");
  for (size_t i = 0; i < f->paramTys.size(); ++i) entry->addArg(f->paramTys[i], "arg" + std::to_string(i));
  return f;
}

Function *Module::addDeclaration(std::string name, std::vector<Type *> params, Type *ret) {
  auto f = std::make_unique<Function>();
  f->name = std::move(name);
  f->paramTys = std::move(params);
  f->retTy = ret;
  f->parent = this;
  functions.push_back(std::move(f));
  return functions.back().get();
}

// ---------------------------------------------------------------- Builder
Op *Builder::create(Opc opc, std::vector<Value *> operands, Type *resTy) {
  assert(block_ && "no insertion point");
  auto op = std::make_unique<Op>(opc);
  op->operands = std::move(operands);
  op->loc = loc_;
  if (resTy && !resTy->isVoid()) op->result = std::make_unique<Value>(Value::OpResult, resTy);
  return block_->append(std::move(op));
}

Value *Builder::constInt(Type *ty, int64_t v) {
  unsigned w = ty->isBool() ? 1 : ty->width();
  return constInt(ty, llvm::APInt(w, static_cast<uint64_t>(v), /*isSigned=*/true));
}
Value *Builder::constInt(Type *ty, const llvm::APInt &v) {
  Op *op = create(Opc::Const, {}, ty);
  op->constVal = v;
  return op->result.get();
}
Value *Builder::constBool(bool v) { return constInt(ctx_.boolTy(), v ? 1 : 0); }

Value *Builder::binop(Opc opc, Value *a, Value *b) { return create(opc, {a, b}, a->ty)->result.get(); }
Value *Builder::unop(Opc opc, Value *a) { return create(opc, {a}, a->ty)->result.get(); }
Value *Builder::cast(Opc opc, Value *a, Type *to) { return create(opc, {a}, to)->result.get(); }
Value *Builder::icmp(const std::string &pred, Value *a, Value *b) {
  Op *op = create(Opc::ICmp, {a, b}, ctx_.boolTy());
  op->pred = pred;
  return op->result.get();
}
Value *Builder::select(Value *c, Value *a, Value *b) { return create(Opc::Select, {c, a, b}, a->ty)->result.get(); }

Op *Builder::br(Block *dest, std::vector<Value *> args) {
  Op *op = create(Opc::Br, {});
  op->succs.push_back({dest, std::move(args)});
  return op;
}
Op *Builder::condBr(Value *c, Block *t, std::vector<Value *> targs, Block *f, std::vector<Value *> fargs) {
  Op *op = create(Opc::CondBr, {c});
  op->succs.push_back({t, std::move(targs)});
  op->succs.push_back({f, std::move(fargs)});
  return op;
}
Op *Builder::ret(Value *v) { return create(Opc::Return, v ? std::vector<Value *>{v} : std::vector<Value *>{}); }
Op *Builder::unreachable() { return create(Opc::Unreachable, {}); }

Value *Builder::call(const std::string &callee, std::vector<Value *> args, Type *resTy) {
  Op *op = create(Opc::Call, std::move(args), resTy);
  op->sym = callee;
  return op->result.get();
}
Value *Builder::load(Value *ptr, Type *ty, int64_t align) {
  Op *op = create(Opc::Load, {ptr}, ty);
  op->setAttr("align", Attr::integer(align));
  return op->result.get();
}
Op *Builder::store(Value *v, Value *ptr, int64_t align) {
  Op *op = create(Opc::Store, {v, ptr});
  op->setAttr("align", Attr::integer(align));
  return op;
}
Value *Builder::ptrAdd(Value *p, Value *off) { return create(Opc::PtrAdd, {p, off}, ctx_.ptrTy())->result.get(); }
Op *Builder::check(Opc kind, std::vector<Value *> operands) { return create(kind, std::move(operands)); }

}  // namespace hlir

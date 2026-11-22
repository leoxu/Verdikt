// Lightweight SSA IR framework shared by the `core` (and later `hl`) dialects.
// Values are SSA; control flow is explicit blocks with block arguments (no phi).
// Every Op carries a Loc and free-form attributes (including `origin`) so that
// provenance survives all lowering steps (DESIGN.md §3).
#pragma once

#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "hlir/ir/Ops.h"
#include "hlir/support/Loc.h"
#include "llvm/ADT/APInt.h"

namespace hlir {

class Block;
class Function;
class Module;
class Op;

// ---------------------------------------------------------------- Types
class Type {
 public:
  enum Kind { Void, Bool, Int, Ptr };
  Kind kind() const { return kind_; }
  unsigned width() const { return width_; }  // Int only (Bool == 1 bit logically)
  bool isVoid() const { return kind_ == Void; }
  bool isBool() const { return kind_ == Bool; }
  bool isInt() const { return kind_ == Int; }
  bool isPtr() const { return kind_ == Ptr; }
  std::string str() const;

 private:
  friend class Context;
  Type(Kind k, unsigned w) : kind_(k), width_(w) {}
  Kind kind_;
  unsigned width_;
};

class Context {
 public:
  explicit Context(unsigned ptrWidth = 64) : ptrWidth_(ptrWidth) {}
  Type *voidTy();
  Type *boolTy();
  Type *ptrTy();
  Type *intTy(unsigned width);
  Type *sizeTy() { return intTy(ptrWidth_); }
  unsigned ptrWidth() const { return ptrWidth_; }

 private:
  unsigned ptrWidth_;
  std::unique_ptr<Type> void_, bool_, ptr_;
  std::map<unsigned, std::unique_ptr<Type>> ints_;
};

// ---------------------------------------------------------------- Attributes
struct Attr {
  enum Kind { Int, Str, Bool, Ident } kind = Int;
  int64_t i = 0;
  std::string s;
  static Attr integer(int64_t v) { Attr a; a.kind = Int; a.i = v; return a; }
  static Attr string(std::string v) { Attr a; a.kind = Str; a.s = std::move(v); return a; }
  static Attr boolean(bool v) { Attr a; a.kind = Bool; a.i = v; return a; }
  static Attr ident(std::string v) { Attr a; a.kind = Ident; a.s = std::move(v); return a; }
};

// ---------------------------------------------------------------- Values
class Value {
 public:
  enum Kind { OpResult, BlockArg, Placeholder };
  Value(Kind k, Type *t) : kind(k), ty(t) {}
  Kind kind;
  Type *ty;           // null for placeholders until resolved
  std::string name;   // without '%'; may be empty (printer auto-names)
  Op *defOp = nullptr;
  Block *defBlock = nullptr;  // for BlockArg, and the owning block of defOp
  unsigned index = 0;         // BlockArg index
};

struct Succ {
  Block *dest = nullptr;
  std::vector<Value *> args;
};

// ---------------------------------------------------------------- Op
class Op {
 public:
  explicit Op(Opc o) : opc(o) {}

  Opc opc;
  std::vector<Value *> operands;
  std::unique_ptr<Value> result;  // null if the op has no result
  std::vector<std::pair<std::string, Attr>> attrs;
  std::vector<Succ> succs;              // terminators (switch: cases..., default last)
  std::vector<llvm::APInt> caseVals;    // switch: size == succs.size()-1
  llvm::APInt constVal{1, 0};           // Const
  std::string sym;                      // Call/GlobalAddr/FuncAddr: symbol name
  std::string pred;                     // ICmp/PtrCmp predicate
  Loc loc;
  Block *parent = nullptr;

  Type *resultType() const { return result ? result->ty : nullptr; }
  const Attr *attr(const std::string &name) const;
  void setAttr(const std::string &name, Attr a);
  bool hasAttr(const std::string &name) const { return attr(name) != nullptr; }
  int64_t intAttr(const std::string &name, int64_t dflt = 0) const;

  // Visit every Value* slot this op uses (operands and successor arguments).
  template <class F> void forEachUse(F &&f) {
    for (auto &v : operands) f(v);
    for (auto &s : succs)
      for (auto &v : s.args) f(v);
  }
  template <class F> void forEachUse(F &&f) const {
    for (auto *v : operands) f(v);
    for (auto &s : succs)
      for (auto *v : s.args) f(v);
  }
};

// ---------------------------------------------------------------- Block / Function / Module
class Block {
 public:
  explicit Block(std::string n = "") : name(std::move(n)) {}
  std::string name;
  Function *parent = nullptr;
  std::vector<std::unique_ptr<Value>> args;
  std::vector<std::unique_ptr<Op>> ops;

  Value *addArg(Type *t, std::string name = "");
  Op *append(std::unique_ptr<Op> op);
  Op *terminator() const;  // last op if it is a terminator, else null
};

class Function {
 public:
  std::string name;
  std::vector<Type *> paramTys;
  Type *retTy = nullptr;
  std::vector<std::unique_ptr<Block>> blocks;  // blocks[0] is the entry block
  Module *parent = nullptr;
  // Internal (C `static` / internal linkage): every caller is within this module, so an interprocedural analysis sees
  // all call sites. An external function may be called by code not in the module with arbitrary arguments.
  bool internal = false;
  bool isDeclaration() const { return blocks.empty(); }
  Block *entry() const { return blocks.empty() ? nullptr : blocks[0].get(); }
  Block *addBlock(std::string name = "");
};

class Module {
 public:
  explicit Module(unsigned ptrWidth = 64) : ctx(ptrWidth) {}
  Context ctx;
  std::vector<std::unique_ptr<Function>> functions;

  Function *findFunction(const std::string &name) const;
  // Defines a function with an entry block whose arguments are the parameters.
  Function *addFunction(std::string name, std::vector<Type *> params, Type *ret);
  Function *addDeclaration(std::string name, std::vector<Type *> params, Type *ret);
};

// ---------------------------------------------------------------- Builder
class Builder {
 public:
  explicit Builder(Module &m) : mod_(m), ctx_(m.ctx) {}
  void setInsertionPoint(Block *b) { block_ = b; }
  void setLoc(Loc l) { loc_ = std::move(l); }
  Block *block() const { return block_; }
  Context &ctx() { return ctx_; }

  // Generic creation. `resTy == nullptr` => no result.
  Op *create(Opc opc, std::vector<Value *> operands, Type *resTy = nullptr);

  Value *constInt(Type *ty, int64_t v);
  Value *constInt(Type *ty, const llvm::APInt &v);
  Value *constBool(bool v);
  Value *binop(Opc opc, Value *a, Value *b);
  Value *unop(Opc opc, Value *a);
  Value *cast(Opc opc, Value *a, Type *to);  // zext/sext/trunc/b2i/i2b/ptr_to_int/int_to_ptr
  Value *icmp(const std::string &pred, Value *a, Value *b);
  Value *select(Value *c, Value *a, Value *b);
  Op *br(Block *dest, std::vector<Value *> args = {});
  Op *condBr(Value *c, Block *t, std::vector<Value *> targs, Block *f, std::vector<Value *> fargs);
  Op *ret(Value *v = nullptr);
  Op *unreachable();
  Value *call(const std::string &callee, std::vector<Value *> args, Type *resTy);
  Value *load(Value *ptr, Type *ty, int64_t align = 1);
  Op *store(Value *v, Value *ptr, int64_t align = 1);
  Value *ptrAdd(Value *p, Value *off);
  Op *check(Opc kind, std::vector<Value *> operands);

 private:
  Module &mod_;
  Context &ctx_;
  Block *block_ = nullptr;
  Loc loc_;
};

}  // namespace hlir

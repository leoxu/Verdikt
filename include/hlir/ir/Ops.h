// `core` dialect opcodes (DESIGN.md §18.3, §18.4).
#pragma once
#include <cstdint>
#include <string_view>

namespace hlir {

enum class Opc : uint8_t {
  // values / arithmetic (total functions; wrapping; no UB — UB is expressed by core.check.*)
  Const, Add, Sub, Mul, UDiv, SDiv, URem, SRem, And, Or, Xor, Not, Neg, Shl, LShr, AShr,
  ZExt, SExt, Trunc, Extract, Concat, ICmp, Select, B2I, I2B, FOp,
  // control flow
  Br, CondBr, Switch, Return, Unreachable, Call,
  // memory / objects
  Alloca, HeapAlloc, Free, GlobalAddr, FuncAddr, Load, Store, PtrAdd, PtrDiff, PtrCmp,
  IsNull, ObjSize, ObjAlive, LifetimeEnd, MemCpy, MemMove, MemSet, PtrToInt, IntToPtr,
  // verification / nondeterminism
  Assume, Assert, Nondet, Havoc, Trace,
  // explicit UB checks
  CheckNull, CheckUaf, CheckOob, CheckPtrArith, CheckFree, CheckUninit, CheckAlign,
  CheckConstWrite, CheckSAddOvf, CheckSSubOvf, CheckSMulOvf, CheckSNegOvf, CheckDiv,
  CheckShift, CheckPtrCmp,
  // field-level array-bound check (DESIGN.md P1 gap fix): a narrow, additive check emitted only at
  // `structField[idx]` subscripts on a fixed-size array field, independent of core.check.oob's
  // whole-object bound (see lib/frontend/Frontend.cpp's ArraySubscriptExpr lowering).
  CheckFieldOob,
  NumOpcodes
};

// How an op is written/parsed in the textual form.
enum class OpFormat : uint8_t {
  Generic,  // %r = core.x %a, %b {attrs} : type
  Const,    // %r = core.const 5 : i32
  Pred,     // %r = core.icmp slt %a, %b : bool
  Br, CondBr, Switch, Ret,
  Call,     // %r = core.call @f(%a) : type
  Sym,      // %r = core.global_addr @g : ptr
};

struct OpInfo {
  const char *name;  // without the "core." prefix
  bool terminator;
  bool hasResult;    // call is special: result iff callee returns non-void
  OpFormat format;
};

const OpInfo &opInfo(Opc opc);
bool opcFromName(std::string_view name, Opc &out);
inline bool isTerminator(Opc o) { return opInfo(o).terminator; }
inline bool isCheck(Opc o) { return o >= Opc::CheckNull && o <= Opc::CheckFieldOob; }

}  // namespace hlir

#include "hlir/ir/Ops.h"

#include <cstring>

namespace hlir {

namespace {
constexpr OpInfo G(const char *n, bool res) { return {n, false, res, OpFormat::Generic}; }
constexpr OpInfo T(const char *n, OpFormat f) { return {n, true, false, f}; }

const OpInfo kInfo[] = {
    {"const", false, true, OpFormat::Const},
    G("add", true), G("sub", true), G("mul", true), G("udiv", true), G("sdiv", true),
    G("urem", true), G("srem", true), G("and", true), G("or", true), G("xor", true),
    G("not", true), G("neg", true), G("shl", true), G("lshr", true), G("ashr", true),
    G("zext", true), G("sext", true), G("trunc", true), G("extract", true), G("concat", true),
    {"icmp", false, true, OpFormat::Pred}, G("select", true), G("b2i", true), G("i2b", true), G("fop", true),
    T("br", OpFormat::Br), T("cond_br", OpFormat::CondBr), T("switch", OpFormat::Switch),
    T("return", OpFormat::Ret), {"unreachable", true, false, OpFormat::Generic},
    {"call", false, false, OpFormat::Call},
    G("alloca", true), G("heap_alloc", true), G("free", false),
    {"global_addr", false, true, OpFormat::Sym}, {"func_addr", false, true, OpFormat::Sym},
    G("load", true), G("store", false), G("ptr_add", true), G("ptr_diff", true),
    {"ptr_cmp", false, true, OpFormat::Pred}, G("is_null", true), G("obj_size", true),
    G("obj_alive", true), G("lifetime_end", false), G("memcpy", false), G("memmove", false),
    G("memset", false), G("ptr_to_int", true), G("int_to_ptr", true),
    G("assume", false), G("assert", false), G("nondet", true), G("havoc", false), G("trace", false),
    G("check.null", false), G("check.uaf", false), G("check.oob", false),
    G("check.ptr_arith", false), G("check.free", false), G("check.uninit", false),
    G("check.align", false), G("check.const_write", false), G("check.sadd_ovf", false),
    G("check.ssub_ovf", false), G("check.smul_ovf", false), G("check.sneg_ovf", false),
    G("check.div", false), G("check.shift", false), G("check.ptr_cmp", false),
    G("check.field_oob", false),
};
static_assert(sizeof(kInfo) / sizeof(kInfo[0]) == static_cast<size_t>(Opc::NumOpcodes),
              "OpInfo table out of sync with Opc");
}  // namespace

const OpInfo &opInfo(Opc opc) { return kInfo[static_cast<size_t>(opc)]; }

bool opcFromName(std::string_view name, Opc &out) {
  for (size_t i = 0; i < static_cast<size_t>(Opc::NumOpcodes); ++i)
    if (name == kInfo[i].name) {
      out = static_cast<Opc>(i);
      return true;
    }
  return false;
}

}  // namespace hlir

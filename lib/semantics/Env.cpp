#include "hlir/semantics/Env.h"

namespace hlir {

llvm::APInt TableEnv::nondet(const Op &nondetOp, unsigned width) {
  if (const Attr *n = nondetOp.attr("name")) {
    auto it = values_.find(n->s);
    if (it != values_.end()) return llvm::APInt(width, static_cast<uint64_t>(it->second), /*isSigned=*/true);
  }
  return llvm::APInt(width, 0);
}

}  // namespace hlir

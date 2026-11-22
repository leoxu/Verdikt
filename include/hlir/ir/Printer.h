// STABLE. Textual form of `core` IR (format version 1).
#pragma once
#include <string>

#include "hlir/ir/IR.h"
#include "llvm/Support/raw_ostream.h"

namespace hlir {

constexpr int kCoreTextVersion = 1;

void printModule(const Module &m, llvm::raw_ostream &os);
std::string moduleToString(const Module &m);

}  // namespace hlir

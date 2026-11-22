// STABLE. Source of everything the program does not determine itself (DESIGN.md §17.6):
// nondeterministic values, later also input bytes, allocation failure, scheduling.
#pragma once
#include <map>
#include <string>

#include "hlir/ir/IR.h"
#include "llvm/ADT/APInt.h"

namespace hlir {

class Env {
 public:
  virtual ~Env() = default;
  // Value for a core.nondet op of the given bit width (bool is width 1). `nondetOp` carries attrs such as name/taint.
  virtual llvm::APInt nondet(const Op &nondetOp, unsigned width) = 0;
  // Content byte of an entry-parameter object (core.heap_alloc {kind="param", content="input"}), named
  // "in.o<obj>+<offset>". Symbolic execution names the same bytes identically, so a model replays exactly.
  virtual llvm::APInt input(const std::string & /*name*/, unsigned width) { return llvm::APInt(width, 0); }
};

// Deterministic environment: named values from a table, everything else 0.
class TableEnv final : public Env {
 public:
  TableEnv() = default;
  explicit TableEnv(std::map<std::string, int64_t> values) : values_(std::move(values)) {}
  void set(const std::string &name, int64_t v) { values_[name] = v; }
  llvm::APInt nondet(const Op &nondetOp, unsigned width) override;

 private:
  std::map<std::string, int64_t> values_;
};

}  // namespace hlir

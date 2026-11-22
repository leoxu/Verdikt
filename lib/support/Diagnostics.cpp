#include "hlir/support/Diagnostics.h"

namespace hlir {

std::string Diag::str() const {
  std::string s;
  if (loc.valid()) s += loc.file + ":" + std::to_string(loc.line) + ":" + std::to_string(loc.col) + ": ";
  s += severity == Error ? "error: " : severity == Warning ? "warning: " : "note: ";
  s += message;
  if (!context.empty()) s += " [" + context + "]";
  return s;
}

std::string Diagnostics::str() const {
  std::string s;
  for (auto &d : diags_) s += d.str() + "\n";
  return s;
}

}  // namespace hlir

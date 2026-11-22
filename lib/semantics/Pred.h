// Private. Comparison predicates shared by the domains.
#pragma once
#include <string>

namespace hlir {

enum class Pred { Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge };

inline bool predFromString(const std::string &s, Pred &p) {
  static const struct { const char *n; Pred p; } t[] = {{"eq", Pred::Eq},   {"ne", Pred::Ne},   {"ult", Pred::Ult},
                                                         {"ule", Pred::Ule}, {"ugt", Pred::Ugt}, {"uge", Pred::Uge},
                                                         {"slt", Pred::Slt}, {"sle", Pred::Sle}, {"sgt", Pred::Sgt},
                                                         {"sge", Pred::Sge}};
  for (auto &e : t)
    if (s == e.n) { p = e.p; return true; }
  return false;
}

}  // namespace hlir

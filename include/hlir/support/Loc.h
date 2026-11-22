// STABLE. Source location shared by every module (IR ops, reports, SMT naming).
#pragma once
#include <string>

namespace hlir {

struct Loc {
  std::string file;
  unsigned line = 0, col = 0;
  bool valid() const { return line != 0; }
};

}  // namespace hlir

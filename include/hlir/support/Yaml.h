// STABLE. A small YAML subset reader (no third-party dependency): block mappings and sequences, flow `{}`/`[]`,
// plain and quoted scalars, `#` comments. Every node remembers its 1-based source line so constraints can point back
// at the specification (DESIGN.md §21.5).
#pragma once
#include <string>
#include <utility>
#include <vector>

#include "hlir/support/Diagnostics.h"

namespace hlir::yaml {

struct YNode {
  enum Kind { Null, Scalar, Map, Seq } kind = Null;
  std::string scalar;
  std::vector<std::pair<std::string, YNode>> map;
  std::vector<YNode> seq;
  unsigned line = 0;

  const YNode *get(const std::string &key) const {
    for (auto &kv : map)
      if (kv.first == key) return &kv.second;
    return nullptr;
  }
  bool isScalar() const { return kind == Scalar; }
};

bool parseYaml(const std::string &text, const std::string &file, YNode &out, Diagnostics &diags);

}  // namespace hlir::yaml

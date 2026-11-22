// STABLE. Uniform error reporting for parsers, verifiers, front ends, spec loaders.
// Modules return Diagnostics instead of printing or throwing, so callers decide how to surface them.
#pragma once
#include <string>
#include <utility>
#include <vector>

#include "hlir/support/Loc.h"

namespace hlir {

struct Diag {
  enum Severity { Error, Warning, Note };
  Severity severity = Error;
  std::string message;
  Loc loc;               // source location, if known
  std::string context;   // e.g. "in @f, block ^entry"
  std::string str() const;
};

class Diagnostics {
 public:
  void error(std::string msg, Loc loc = {}, std::string ctx = "") {
    diags_.push_back({Diag::Error, std::move(msg), std::move(loc), std::move(ctx)});
    ++errors_;
  }
  void warning(std::string msg, Loc loc = {}, std::string ctx = "") {
    diags_.push_back({Diag::Warning, std::move(msg), std::move(loc), std::move(ctx)});
  }
  bool hasErrors() const { return errors_ != 0; }
  const std::vector<Diag> &all() const { return diags_; }
  std::string str() const;  // all diagnostics, one per line

 private:
  std::vector<Diag> diags_;
  unsigned errors_ = 0;
};

}  // namespace hlir

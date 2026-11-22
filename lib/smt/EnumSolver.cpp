#include <algorithm>
#include "hlir/smt/Solver.h"

namespace hlir::smt {

namespace {

bool hasArray(TermRef root) {
  std::vector<TermRef> stack{root};
  std::vector<bool> seen;
  while (!stack.empty()) {
    TermRef t = stack.back();
    stack.pop_back();
    if (t->id < seen.size() && seen[t->id]) continue;
    if (t->id >= seen.size()) seen.resize(t->id + 1, false);
    seen[t->id] = true;
    if (t->sort.isArray) return true;
    for (auto *c : t->args) stack.push_back(c);
  }
  return false;
}

class EnumSolver final : public Solver {
 public:
  explicit EnumSolver(unsigned maxBits) : maxBits_(maxBits) { frames_.emplace_back(); }

  void push() override { frames_.emplace_back(); }
  void pop() override { if (frames_.size() > 1) frames_.pop_back(); }
  void assertTerm(TermRef t, const std::string &name) override { frames_.back().push_back({t, name}); }

  SatResult check() override {
    ++checks_;
    model_.clear();
    std::vector<TermRef> vars;
    for (auto &f : frames_)
      for (auto &a : f) {
        if (hasArray(a.t)) return SatResult::Unknown;  // arrays cannot be enumerated
        collectVars(a.t, vars);
      }
    std::sort(vars.begin(), vars.end(), [](TermRef x, TermRef y) { return x->id < y->id; });
    vars.erase(std::unique(vars.begin(), vars.end()), vars.end());
    unsigned bits = 0;
    for (auto *v : vars) bits += v->sort.width;
    if (bits > maxBits_) return SatResult::Unknown;
    for (uint64_t n = 0; n < (uint64_t(1) << bits); ++n) {
      Assignment asg;
      unsigned off = 0;
      for (auto *v : vars) {
        asg.emplace(v->name, llvm::APInt(v->sort.width, n >> off));
        off += v->sort.width;
      }
      bool ok = true;
      for (auto &f : frames_) {
        for (auto &a : f)
          if (!evalTerm(a.t, asg).getBoolValue()) { ok = false; break; }
        if (!ok) break;
      }
      if (ok) { model_ = std::move(asg); return SatResult::Sat; }
    }
    return SatResult::Unsat;
  }

  std::vector<llvm::APInt> values(const std::vector<TermRef> &vars) override {
    std::vector<llvm::APInt> r;
    for (auto *v : vars) r.push_back(evalTerm(v, model_));
    return r;
  }
  std::vector<std::string> unsatCore() override {
    std::vector<std::string> r;
    for (auto &f : frames_)
      for (auto &a : f)
        if (!a.name.empty()) r.push_back(a.name);
    return r;
  }
  std::string name() const override { return "enum"; }
  uint64_t checkCount() const override { return checks_; }

 private:
  struct Asserted { TermRef t; std::string name; };
  unsigned maxBits_;
  std::vector<std::vector<Asserted>> frames_;
  Assignment model_;
  uint64_t checks_ = 0;
};

}  // namespace

std::unique_ptr<Solver> makeEnumSolver(unsigned maxBits) { return std::make_unique<EnumSolver>(maxBits); }

}  // namespace hlir::smt

#include "hlir/entry/SeedSolver.h"

namespace hlir::entry {

using smt::Kind;
using smt::SatResult;
using smt::TermRef;

Seed SeedSolver::solve(const std::string &label, const std::vector<std::pair<std::string, TermRef>> &extra, bool soft) {
  Seed s;
  s.label = label;
  sol_.push();
  for (auto &c : plan_.constraints) sol_.assertTerm(c.term, c.name);
  for (auto &e : extra) sol_.assertTerm(e.second, e.first);
  s.result = sol_.check();
  if (s.result == SatResult::Unsat) s.core = sol_.unsatCore();
  if (s.result == SatResult::Sat && soft) {
    // Layered stand-in for assert-soft: keep each preference (heaviest first) only if the problem stays satisfiable.
    unsigned pushed = 0;
    for (auto &p : plan_.soft) {
      sol_.push();
      ++pushed;
      sol_.assertTerm(p.term);
      if (sol_.check() != SatResult::Sat) { sol_.pop(); --pushed; }
    }
    // Re-check UNCONDITIONALLY, not only when a preference survived.
    //
    // A rejected preference leaves the solver's last check() at UNSAT, and values() then has no model to
    // read: Z3 returns all zeros and sets an error nobody looks at. So when EVERY preference is rejected
    // (`pushed == 0`) the old `if (pushed)` skipped the re-check, s.result kept the Sat from the first
    // check above, and M0 came back "satisfiable" with every input at zero -- silently, because the
    // result still said Sat.
    //
    // The one soft constraint on a tainted buffer is `size(buf) <= 64` (InitGen.cpp's benign.size), so
    // this fired for any `--seed-value len=N` with N >= 65: the preference contradicts the spec's own
    // `len <= size(buf)` relation, is correctly rejected, and the seed silently became zero. Every
    // entry of the libarchive profile died that way -- ar's member header is 68 bytes, cpio's newc
    // header 110 -- with `blocks_visited 0` and nothing naming the cause (DESIGN.md Sec.22.461).
    s.result = sol_.check();
    if (s.result == SatResult::Sat) {
      std::vector<TermRef> vars;
      for (auto &v : plan_.vars) vars.push_back(v.var);
      auto vals = sol_.values(vars);
      for (size_t i = 0; i < vars.size(); ++i) s.model.emplace(vars[i]->name, vals[i]);
    }
    for (unsigned i = 0; i < pushed; ++i) sol_.pop();
  } else if (s.result == SatResult::Sat) {
    std::vector<TermRef> vars;
    for (auto &v : plan_.vars) vars.push_back(v.var);
    auto vals = sol_.values(vars);
    for (size_t i = 0; i < vars.size(); ++i) s.model.emplace(vars[i]->name, vals[i]);
  }
  sol_.pop();
  return s;
}

Seed SeedSolver::legality() { return solve("legality", {}, false); }
Seed SeedSolver::benign() { return solve("benign", {}, true); }
Seed SeedSolver::benignWith(const std::vector<std::pair<std::string, smt::TermRef>> &extra) { return solve("benign", extra, true); }

std::vector<Seed> SeedSolver::boundary() {
  std::vector<Seed> out;
  auto add = [&](const std::string &label, TermRef t) {
    out.push_back(solve(label, {{"seed." + label, t}}, false));
  };
  for (auto &p : plan_.params) {
    if (p.kind == PlannedParam::Scalar) {
      if (!p.tainted || p.isBool) continue;
      const unsigned w = p.width;
      std::vector<std::pair<std::string, llvm::APInt>> cands;
      if (p.isSigned) {
        llvm::APInt mn = llvm::APInt::getSignedMinValue(w), mx = llvm::APInt::getSignedMaxValue(w);
        cands = {{"min", mn}, {"min+1", mn + 1}, {"-1", llvm::APInt::getAllOnes(w)}, {"0", llvm::APInt(w, 0)}, {"1", llvm::APInt(w, 1)}, {"max-1", mx - 1}, {"max", mx}};
      } else {
        llvm::APInt mx = llvm::APInt::getAllOnes(w);
        cands = {{"0", llvm::APInt(w, 0)}, {"1", llvm::APInt(w, 1)}, {"max-1", mx - 1}, {"max", mx}};
        for (unsigned k : {8u, 16u, 31u, 32u})
          if (k < w) {
            llvm::APInt pw2 = llvm::APInt(w, 1).shl(k);
            cands.push_back({"2^" + std::to_string(k) + "-1", pw2 - 1});
            cands.push_back({"2^" + std::to_string(k), pw2});
            cands.push_back({"2^" + std::to_string(k) + "+1", pw2 + 1});
          }
      }
      for (auto &c : cands) add(p.name + "=" + c.first, tm_.mkEq(p.value, tm_.bvConst(c.second)));
      // relative to every buffer: size-1, size, size+1 (as 64-bit values, with the parameter's own signedness)
      for (auto &b : plan_.params) {
        if (b.kind == PlannedParam::Scalar) continue;
        TermRef x64 = w >= 64 ? p.value : (p.isSigned ? tm_.mkSExt(p.value, 64) : tm_.mkZExt(p.value, 64));
        TermRef sz = b.size->sort.width < 64 ? tm_.mkZExt(b.size, 64) : b.size;
        for (int d : {-1, 0, 1}) {
          TermRef target = tm_.mkBin(Kind::BvAdd, sz, tm_.bvConst(llvm::APInt(64, static_cast<uint64_t>(static_cast<int64_t>(d)), true)));
          add(p.name + "=size(" + b.name + ")" + (d < 0 ? "-1" : d > 0 ? "+1" : ""), tm_.mkEq(x64, target));
        }
      }
    } else if (p.size->kind == smt::Kind::Var) {
      for (uint64_t v : {p.sizeLo, p.sizeLo + 1, p.sizeHi - 1, p.sizeHi})
        add("size(" + p.name + ")=" + std::to_string(v), tm_.mkEq(p.size, tm_.bvConst(llvm::APInt(plan_.ptrWidth, v))));
    }
  }
  // drop duplicates (e.g. size.lo+1 == size.hi): keep the first label per identical model/outcome is unnecessary; labels are unique
  return out;
}

std::vector<Seed> SeedSolver::diverse(unsigned n) {
  std::vector<Seed> out;
  std::vector<std::pair<std::string, TermRef>> blocks;
  for (unsigned i = 0; i < n; ++i) {
    Seed s = solve("diverse#" + std::to_string(i), blocks, false);
    if (s.result != SatResult::Sat) { out.push_back(std::move(s)); break; }
    TermRef differs = tm_.boolConst(false);
    for (auto &v : plan_.vars) differs = tm_.mkOr(differs, tm_.mkNot(tm_.mkEq(v.var, tm_.bvConst(s.model.at(v.var->name)))));
    blocks.push_back({"block." + std::to_string(i), differs});
    out.push_back(std::move(s));
  }
  return out;
}

}  // namespace hlir::entry

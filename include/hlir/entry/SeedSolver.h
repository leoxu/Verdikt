// STABLE. Initial states from the legality constraints C_init (DESIGN.md §21.6): a satisfiability check that points
// back at the specification when it is contradictory, a benign first seed, boundary-value seeds that report why a
// boundary is not allowed, and diverse follow-up seeds.
#pragma once
#include <map>
#include <string>
#include <vector>

#include "hlir/entry/InitPlan.h"
#include "hlir/smt/Solver.h"

namespace hlir::entry {

struct Seed {
  std::string label;                         // e.g. "benign", "len=max", "diverse#2"
  smt::SatResult result = smt::SatResult::Unknown;
  std::map<std::string, llvm::APInt> model;  // value of every free input (InitPlan::vars), by variable name
  std::vector<std::string> core;             // Unsat: names of the init.* / seed.* constraints that conflict
};

class SeedSolver {
 public:
  SeedSolver(smt::TermManager &tm, smt::Solver &solver, const InitPlan &plan) : tm_(tm), sol_(solver), plan_(plan) {}

  Seed legality();                      // is C_init satisfiable? (model = any legal input; core = contradictory spec lines)
  Seed benign();                        // M0: legal and as typical as the soft preferences allow
  // M0 with `extra` asserted too (hlir-scan --seed-value): the caller's chosen starting values for named
  // scalars become part of the SAME query as C_init, so M0 still satisfies the specification. Overriding
  // them afterwards instead would let the concrete run disagree with the symbolic state -- a length
  // seeded past its buffer would make the harness read out of bounds and the scan report a defect that
  // only the seed created (DESIGN.md Sec.22.448). Unsat means the seed contradicts the spec; the caller
  // falls back to benign() and says so.
  Seed benignWith(const std::vector<std::pair<std::string, smt::TermRef>> &extra);
  std::vector<Seed> boundary();         // one seed per boundary value; Unsat ones carry the explaining core
  std::vector<Seed> diverse(unsigned n);  // successive legal models, each excluded from the next by a blocking clause

 private:
  Seed solve(const std::string &label, const std::vector<std::pair<std::string, smt::TermRef>> &extra, bool soft);
  smt::TermManager &tm_;
  smt::Solver &sol_;
  const InitPlan &plan_;
};

}  // namespace hlir::entry

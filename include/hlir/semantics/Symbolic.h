// STABLE. Path-based symbolic execution of `core` programs (DESIGN.md §19). Same instruction semantics as the concrete
// interpreter (one shared Machine), but values are SMT terms and branches fork. The solver is injected, so any
// smt::Solver backend works.
//
// Exploration is depth-first by re-execution: each path is a fresh run guided by a prefix of branch decisions. It keeps
// the engine tiny and exactly in sync with the interpreter at the cost of repeating prefix work; a query cache makes the
// repetition cheap on the solver side.
#pragma once
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "hlir/ir/IR.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/smt/Solver.h"

namespace hlir {

// One symbolic function argument: an unconstrained variable unless a range is given.
struct SymArg {
  std::optional<llvm::APInt> lo, hi;  // inclusive bounds, compared as signed if `isSigned` else unsigned
  bool isSigned = false;
};

struct SymConfig {
  UBMode ub = UBMode::Report;
  uint64_t maxSteps = 100'000;     // per path
  unsigned maxCallDepth = 64;
  unsigned maxPaths = 10'000;
  unsigned loopBound = 0;          // RunConfig::loopBound: paths that exceed it are cut (SymResult::loopCut)
  const model::ModelProvider *models = nullptr;  // semantics of external functions
  const std::set<std::string> *prologueFns = nullptr;  // see RunConfig::prologueFns (§22.368)
  const std::set<std::string> *stopFns = nullptr;      // see RunConfig::stopFns
  unsigned memBound = 256;         // unrolling bound for memcpy/memset with a symbolic length (n <= bound is asserted)
  // RunConfig::memExpandMax: hard cap on bytes a single memcpy/memset/string-scan physically expands, even for a
  // constant length. Independent of memBound above. Default matches Memory.h's kMaxExpandDefault; opt-in to raise.
  uint64_t memExpandMax = 1u << 20;
  bool tableSelect = true;  // see RunConfig::tableSelect (G2, DESIGN.md Sec.22.465)
  bool storeSelect = false;  // see RunConfig::storeSelect (DESIGN.md Sec.22.487)   // OPT-IN: --store-select
  double wallSeconds = 0;          // wall-clock budget of this run() (0 = none): stops with reason time_budget, keeping the findings so far
  bool collectPaths = false;       // fill SymResult::paths (return value + path condition of every finished path)
};

// A property violation with a satisfying input.
struct SymFinding {
  RunStatus status = RunStatus::UB;       // UB or AssertFailed
  std::optional<UBReport> ub;             // set for UB
  std::string message;                    // assertion message
  Loc loc;
  std::vector<llvm::APInt> args;          // concrete arguments reproducing it (in parameter order)
  std::vector<llvm::APInt> nondets;       // values for core.nondet ops, in execution order (feed SeqEnv to replay)
  std::map<std::string, llvm::APInt> inputs;  // entry-parameter object bytes ("in.o<obj>+<off>"), also for SeqEnv
  unsigned path = 0;                      // index of the path (symbolic) / run (taint) on which it was first found
  std::optional<bool> confirmed;          // taint executor: did the concrete interpreter reproduce it?
  std::string replayNote;                 // taint executor: what the replay did instead, when it did not reproduce the finding
  std::vector<std::string> nondetNames;   // names of the core.nondet values, parallel to `nondets` (taint executor)
  bool frontierOnly = false;              // the UB only a value invented past the synthesis frontier can produce (§22.365)
  bool cmpOnlyPtr = false;                // core.check.ptr_arith whose out-of-range pointer is only compared (§22.390)
  bool inPrologue = false;                // the UB happened inside the project initialiser, not in the entry (§22.368)
};

struct SymPath {
  RunStatus status;
  std::vector<smt::TermRef> pc;           // conjuncts of the path condition
  smt::TermRef returnValue = nullptr;     // bit-vector term (bool = 1 bit); null for void / non-returning paths
};

struct SymResult {
  std::vector<SymFinding> findings;       // one per (op, kind) site; first witness found
  std::vector<SymPath> paths;
  unsigned pathsExplored = 0;
  unsigned loopCut = 0;                   // paths cut at the loop bound
  uint64_t solverQueries = 0;
  bool complete = true;                   // false: a limit or an Unknown solver answer cut the exploration short
  bool overApprox = false;                // memory accesses with symbolic offsets/objects were over-approximated (findings need replay)
  std::string note;                       // why `complete` is false / BadInput / Unsupported details
  std::string reason;                     // machine-readable code for `note`: unknown_function, pointer_param, path_limit, solver_unknown, unsupported, step_limit, depth_limit
  std::vector<smt::TermRef> argVars;      // the symbolic variables standing for the arguments
  std::set<const Block *> blocksVisited;  // union over every path explored, incl. cut/infeasible ones (their prefix is real)
  // Harness-declared setup region (DESIGN.md §22.442): this pass replays every path from the entry, so without a
  // cache it pays for the region once PER PATH. Reported, because "the region ran once" is an assumption about
  // what was explored, not a speed note.
  bool setupSeen = false;
  bool setupReused = false;
  std::string setupRefusal;
  uint64_t setupOps = 0;       // interpreter steps the region cost when it was captured
  unsigned setupSkips = 0;     // paths that restored it instead of running it
  unsigned setupObjects = 0;
  double setupSecRestore = 0;
};

class SymbolicExecutor {
 public:
  SymbolicExecutor(const Module &m, smt::TermManager &tm, smt::Solver &solver) : mod_(m), tm_(tm), solver_(solver) {}
  // `args` may be shorter than the parameter list; missing entries are unconstrained.
  SymResult run(const std::string &function, const std::vector<SymArg> &args = {}, const SymConfig &cfg = {});

 private:
  const Module &mod_;
  smt::TermManager &tm_;
  smt::Solver &solver_;
};

// Deterministic nondet values taken from a list in order (then 0): replays SymFinding::nondets.
class SeqEnv final : public Env {
 public:
  explicit SeqEnv(std::vector<llvm::APInt> v, std::map<std::string, llvm::APInt> inputs = {})
      : vals_(std::move(v)), inputs_(std::move(inputs)) {}
  llvm::APInt input(const std::string &name, unsigned width) override {
    auto it = inputs_.find(name);
    return it == inputs_.end() ? llvm::APInt(width, 0) : it->second.zextOrTrunc(width);
  }
  llvm::APInt nondet(const Op &, unsigned width) override {
    if (next_ < vals_.size()) return vals_[next_++].zextOrTrunc(width);
    return llvm::APInt(width, 0);
  }

 private:
  std::vector<llvm::APInt> vals_;
  std::map<std::string, llvm::APInt> inputs_;
  size_t next_ = 0;
};

}  // namespace hlir

// STABLE. Taint-selective concolic execution of `core` programs (DESIGN.md §20).
//
// The program runs concretely from a seed. Only values that depend on tainted inputs (core.nondet {taint=...}, entry
// parameter object bytes, or promoted environment values) get SMT terms; everything else stays concrete and never
// reaches the solver. A tainted branch becomes a path constraint, a tainted failing-check condition becomes a query;
// the driver then solves queries (findings, replayed on the interpreter) and flips tainted branches to reach new paths.
//
// Typical use: run an entry harness (hlir::entry::generateHarness) with the benign seed M0.
#pragma once
#include <map>
#include <set>
#include <string>
#include <vector>

#include "hlir/semantics/Symbolic.h"

namespace hlir {

struct TaintConfig {
  const std::map<std::string, FieldBound> *fieldBounds = nullptr;  // see RunConfig::fieldBounds
  const std::set<std::string> *prologueFns = nullptr;              // see RunConfig::prologueFns
  const std::set<std::string> *stopFns = nullptr;                  // see RunConfig::stopFns
  bool recordReads = false;                                        // see RunConfig::recordReads
  const std::map<std::string, std::set<uint64_t>> *promoteGlobals = nullptr;  // see RunConfig::promoteGlobals
  UBMode ub = UBMode::Report;
  std::set<UBKind> ubContinue;        // see RunConfig::ubContinue (--ub-continue)
  uint64_t maxSteps = 1'000'000;      // per run
  unsigned maxCallDepth = 64;
  // RunConfig::memExpandMax: hard cap on bytes a single memcpy/memset/string-scan physically expands, even for a
  // constant length. Independent of loopBound/maxSteps above. Default matches Memory.h's kMaxExpandDefault (same
  // default as SymConfig::memExpandMax); opt-in to raise (hlir-scan --mem-expand-max). Reaches the primary
  // concolic/taint engine, unlike SymConfig's own field which only reaches the symbolic escalation pass.
  uint64_t memExpandMax = 1u << 20;
  bool tableSelect = true;  // see RunConfig::tableSelect (G2, DESIGN.md Sec.22.465)
  bool storeSelect = false;  // see RunConfig::storeSelect (DESIGN.md Sec.22.487)   // OPT-IN: --store-select
  unsigned loopBound = 0;             // RunConfig::loopBound: runs that exceed it are cut (counted in TaintResult::loopCut)
  unsigned maxRuns = 20000;           // concolic iterations (runs are cheap: the wall-clock budget is what normally ends the exploration)
  // How many pending branch flips the search may hold. Past this the least promising are DISCARDED, which bounds
  // memory but also means the exploration stops being exhaustive -- so a run that drops any is reported
  // `incomplete: frontier_dropped` and can no longer conclude `safe` (DESIGN.md §22.383). Raising it is not
  // uniformly better: with the same run budget a larger frontier spreads it thinner (measured on c-ares
  // CVE-2023-31130: 20000 misses, 100000 finds it, no cap at all misses again).
  size_t maxFrontier = 20000;
  std::set<std::string> promote;      // core.nondet names that become symbolic inputs although untainted ("size.src", ...)
  bool promoteAll = false;            // promote every nondet (the "symbolic environment" mode)
  std::string inputLabel = "input";   // taint label of entry-parameter object bytes
  const model::ModelProvider *models = nullptr;  // semantics of external functions (sources, flows, sinks, ...)
  bool replay = true;                 // confirm each finding on the concrete interpreter
  unsigned fastTimeoutMs = 0;         // timeout layering: try each query at this limit first (0 = use the solver's own limit) ...
  unsigned slowTimeoutMs = 0;         // ... and retry Unknown answers at this one
  // Initial bytes of the attacker-controlled input a model source produces, per taint label: the n-th distinct 8-bit input of the
  // label (in the order the run first creates them) starts at labelSeeds[label][n] (later ones, and names the solver assigns, keep
  // their own values). Lets a run start from a valid message instead of all zeros so it reaches the deep parsing code.
  std::map<std::string, std::vector<uint8_t>> labelSeeds;
  // Starting value of a NAMED scalar entry parameter (hlir-scan --seed-value NAME=VALUE), by the name the
  // spec gives it, e.g. `in_len`. labelSeeds above only reaches 8-bit inputs -- it is a byte stream for a
  // buffer -- so an entry whose contract is (pointer, length) got its buffer seeded and its LENGTH left
  // at 0, and the seed was then never read at the length it was written for. That cost three rounds of
  // the Fluent Bit in_forward scan before it was noticed (DESIGN.md Sec.22.448).
  //
  // The driver turns these into EXTRA CONSTRAINTS ON THE M0 QUERY, not into an override applied after
  // it, so the first run's concrete state still satisfies C_init. Overriding afterwards would let a
  // length be seeded past its own buffer, and the harness would then read out of bounds -- a `finding`
  // the seed invented. A seed the spec contradicts is dropped and reported; so is a name that matches
  // no scalar parameter.
  std::map<std::string, uint64_t> valueSeeds;
  // Probe budget for the AUTOMATIC seed (DESIGN.md §22.385). 0 = off. The seed decides only what the first run's
  // attacker bytes are -- it adds no constraint and weakens no verdict -- but where the search starts is what
  // decides whether a parser is ever entered at all. An explicit labelSeeds entry for the same label wins.
  unsigned autoSeed = 0;
  double wallSeconds = 0;             // wall-clock budget of this run() (0 = none): the engine stops itself and keeps what it found (reason time_budget)
  unsigned dropPcsAboveDepth = 0;     // regression aid: discard path constraints created at call depth >= N (1 = in every callee; 0 = keep all)
  // Target-guided search (hlir-scan --reach-target): name of a function to prioritise reaching, empty = off (default
  // coverage-guided order, unchanged). When set, the search frontier's priority additionally prefers flips in
  // functions closer to this one in the call graph (see hlir/semantics/ReachTarget.h); ties still break by freshness
  // then insertion order exactly as before. Branches in functions the target can never be reached from keep running,
  // just last -- this never excludes a path, only reorders the frontier.
  std::string reachTarget;
  // --entries registered, SYMBOLIC discovery (direction A, DESIGN REGISTERED_ENTRIES M3b-A). Running the module's
  // @main through the concolic engine (instead of one concrete Interpreter::run) lets a DATA gate that selects the
  // registration path fork -- e.g. a driver's `if (hal_ctx->num_items > 0) register_handlers(/*registers*/)`, whose
  // num_items is an unconstrained field a concrete run reads as 0. On any path that reaches a captureRegs call, the
  // Machine<D> capture hook fires (it is domain-independent) and appends to capturedRegs. These mirror the RunConfig
  // fields of the same name and are copied straight into the per-run RunConfig.
  bool bestEffortInit = false;                                     // see RunConfig::bestEffortInit
  bool forceAllocSuccess = false;                                  // see RunConfig::forceAllocSuccess
  const std::vector<RunConfig::RegCapture> *captureRegs = nullptr; // see RunConfig::captureRegs
  std::vector<RunConfig::CapturedReg> *capturedRegs = nullptr;     // see RunConfig::capturedRegs (sink, shared by all runs)
  const std::map<std::string, long> *passFns = nullptr;           // see RunConfig::passFns
  bool discoverHavoc = false;                                     // see RunConfig::discoverHavoc (makes the setup environment symbolic)
  int discoverHavocBytes = 4096;                                  // see RunConfig::discoverHavocBytes (execUntrusted outMax)
};

// Per function: how its calls were classified (DESIGN.md §20.5), inclusive of callees.
struct FunctionTaintClass {
  std::string function;
  uint64_t calls = 0;
  uint64_t inert = 0;        // no tainted op, branch, query or source
  uint64_t observer = 0;     // tainted ops / branches / queries but no taint flowing out
  uint64_t transformer = 0;  // taint flowed out (returned or stored)
  uint64_t source = 0;       // introduced taint
  uint64_t sanitizer = 0;    // overwrote tainted data with untainted data, nothing tainted flowed out
};

// A concrete value some tainted computation or query depends on (e.g. a heap object's size).
struct EnvFact {
  llvm::APInt value;
  std::string op;            // consuming op, e.g. "core.check.ptr_arith"
  std::string function;
  Loc loc;
};

struct SliceStats {
  uint64_t steps = 0;            // core ops executed in the run
  uint64_t taintedOps = 0;       // ops with at least one tainted operand (the only ones that built SMT terms)
  uint64_t pcs = 0;              // tainted path constraints (branches + assumptions + passed checks)
  uint64_t flippableBranches = 0;
  uint64_t queries = 0;          // tainted check sites
  uint64_t sources = 0;          // symbolic input variables
  uint64_t envFacts = 0;
  uint64_t concretizedPointers = 0;  // tainted addresses that were followed concretely
  uint64_t selectedAddresses = 0;    // ...and the ones resolved by selection instead (Sec.22.487)
};

struct TaintRun {
  RunStatus status = RunStatus::Returned;
  SliceStats slice;
  std::vector<EnvFact> envFacts;
  std::map<std::string, llvm::APInt> seed;
};

// One (caller, callee) call-graph edge, summed over all runs (DESIGN.md §20.5 extension for the call-graph visualisation,
// tools/hlir-taint --format dot). `tainted` is true iff some run's call across this edge was not classified "inert" by
// TaintDomain::onReturn — i.e. it introduced, observed, transformed, sanitized or propagated tainted data. This is a
// call-instance-level signal (per caller/callee pair), finer than FunctionTaintClass (per callee only) but still an
// approximation: it says tainted data was live *during* the call, not that a specific argument byte crossed the edge.
struct CallEdge {
  std::string caller, callee;
  uint64_t calls = 0;
  bool tainted = false;
};

// A place where runs ended because the program ends there (noreturn call, abort/exit/trap).
struct TerminationSite {
  std::string function, by, stack;  // function containing it; callee name or "abort"/"assume"; the callers above it
  Loc loc;
  unsigned runs = 0;
  std::map<std::string, llvm::APInt> inputs;  // entry-parameter bytes of the first run that ended here ("in.o<obj>+<off>"): a witness
};

// WHERE THE SEARCH BUDGET WENT, per function (DESIGN.md §22.392). `flippablePcs` counts the tainted branch
// conditions this function's ops produced over all runs -- i.e. the decisions the search COULD make -- and
// `queued` how many of those actually became frontier items. `calls` is the same function's call count.
//
// This exists to automate a judgement that was made by hand. §22.385 collapsed `strchr` into a closed-form
// `select` chain (Machine::charClassFast) because a frontier profile printed behind HLIR_DEBUG_FRONTIER showed
// 88% of flippable path conditions inside its model loop. That profile was computed on every run already; only
// the decision to LOOK at it depended on someone suspecting it. Now it is ranked and reported.
//
// `perCall` is the signal that matters, and it is the one that generalises past strchr: a function costing many
// INDEPENDENT flips per single call is encoding one logical decision as N sequential binary ones, and the search
// budget (counted in runs and flips, not in logical decisions) is spent enumerating an answer a solver could
// produce in one disjunction. `foldCandidate` flags that shape; it is a ranked worklist, not a proof -- whether a
// closed form exists is still a human call (the constant-haystack precondition behind charClassFast is not
// something this profile can see). Program code is never a candidate: summarising it would change WHAT is
// analysed, not how it is searched.
struct FrontierSite {
  std::string function;
  uint64_t flippablePcs = 0;  // tainted branch conditions produced here, over all runs
  uint64_t queued = 0;        // of those, the ones that became frontier items (the rest were duplicates)
  uint64_t calls = 0;         // calls to this function, over all runs
  double share = 0;           // flippablePcs / the run's total
  double perCall = 0;         // flippablePcs / calls -- the summarization signal
  bool library = false;       // every branch here lacks a source location: a model body, not program code
  bool foldCandidate = false; // library AND share AND perCall over threshold: worth a closed form
  // How the safety checks INSIDE this function were settled, over all runs (RunResult::checksByFn). A function
  // that eats the budget while `checksQueried` stays 0 is one where no flip can teach the solver anything: every
  // safety question in it is already decided by concrete values. That is a different shape from
  // `foldCandidate` -- it says nothing about a closed form, only about what the search is buying here.
  uint64_t checksReached = 0, checksQueried = 0;
};

struct TaintResult {
  std::vector<SymFinding> findings;
  std::map<std::string, NondetOrigin> nondetOrigins;  // merged over every run: what each nondet in a witness means
  // Every taint label any run actually created. Used to tell the caller that a --seed-bytes key
  // matched no input at all, which is otherwise silent (DESIGN.md Sec.22.466).
  std::set<std::string> labelsSeen;
  std::map<int, CheckStat> checks;   // UBKind -> how its checks were settled, summed over runs
  TaintReach taintReach;             // OR-ed over runs
  bool setupInfeasible = false;      // see RunResult::setupInfeasible
  std::map<std::string, uint64_t> opaqueCalls;  // see RunResult::opaqueCalls, summed over runs
  std::map<std::string, std::set<uint64_t>> reads;  // see RunResult::reads, unioned over runs
  std::map<unsigned, std::string> objKeys;          // see RunResult::objKeys
  std::map<std::string, uint64_t> unknownWrites;    // see RunResult::unknownWrites, summed over runs
  unsigned globalsPromoted = 0;
  // see RunResult, summed over runs (DESIGN.md §22.365 A1)
  uint64_t frontierFieldReads = 0, frontierBoundsApplied = 0, frontierBoundsMissing = 0, frontierBoundsInfeasible = 0;
  bool readsIncomplete = false;
  std::vector<TaintRun> runs;
  std::vector<FunctionTaintClass> functions;  // summed over all runs
  std::vector<CallEdge> callEdges;            // call graph edges exercised by any run, summed over all runs
  uint64_t solverQueries = 0;
  uint64_t termsSolved = 0;                   // SMT terms in the dependency cones that were actually sent to the solver
  bool complete = true;                       // false: run limit, unsupported op, step limit or an Unknown solver answer
  std::string note;
  std::string reason;                         // machine-readable code for `note` (see SymResult::reason; also run_limit)
  // where the time went (seconds): concrete+symbolic interpretation of runs, solver, replays of findings, path-condition cones/everything else is the rest
  double secAssert = 0, secCheck = 0;  // solver time split: building/sending the assertions vs. check-sat
  double secInterp = 0, secSolve = 0, secReplay = 0, secCone = 0;
  // Ranked by flippablePcs, descending; capped (the tail is noise). `flippablePcsTotal` is the undivided total,
  // so a caller can tell "the top function is 88% of a large number" from "88% of twelve".
  std::vector<FrontierSite> frontier;
  uint64_t flippablePcsTotal = 0;
  // THE SEARCH'S OWN YIELD (DESIGN.md Sec.22.468). `flipsQueued` branch flips were taken off the frontier and
  // asked of the solver; `flipsSolved` of them came back SAT and became a new input, `flipsUnsat` were refused.
  // A run that queues flips and gets NOTHING back has not explored a space and converged -- it has collapsed
  // onto its seed, and every direction it never reached is then recorded as "proved infeasible", which reads
  // like knowledge. Sec.22.467 was exactly this and went unnoticed because these counters existed only behind
  // HLIR_DEBUG_FRONTIER: 0 of 253 SAT, one run, and a report that said `open = 0`.
  uint64_t flipsQueued = 0, flipsSolved = 0, flipsUnsat = 0, flipsDeduped = 0;
  uint64_t flipsConcDropped = 0;  // concretisation constraints removed from flip cones (Sec.22.467)
  unsigned branchesCovered = 0;               // distinct (tainted branch, direction) pairs some run took
  unsigned loopCut = 0;                       // runs cut at the loop bound
  unsigned maxDepth = 0;                      // deepest call stack of any run (the entry harness counts 1)
  uint64_t cacheHits = 0;                     // solver queries answered from the query cache
  uint64_t escalations = 0;                   // queries that timed out at the fast limit and were retried with the slow one
  // coverage over all runs
  std::set<const Block *> blocksVisited;
  // The seed §22.385 chose, what it scored, and how many candidates it tried (empty / 0 when it did not run or
  // found nothing better than zeros). Reported as an assumption: it is a configuration, not a fact about the code.
  std::vector<uint8_t> autoSeedBytes;
  unsigned autoSeedBlocks = 0, autoSeedBaseline = 0, autoSeedProbes = 0, autoSeedKept = 0;
  std::string autoSeedAlphabet;
  std::set<std::pair<const Op *, bool>> branchesVisited;  // (cond_br op, direction taken) pairs some run took
  // Why a conditional EDGE is still not covered (`--dump-branches`, DESIGN.md §22.429). Three disjoint facts the
  // search knows and the summary numbers throw away; everything else is "the branch op never executed".
  //   flipUnsat: the solver was asked for this edge and answered UNSAT -- it is infeasible on that path prefix,
  //              and no budget will ever open it.
  //   flipOpen:  a flip for it was queued and the budget ran out before it reached the front. THIS is the real
  //              coverage gap: the only class that more budget can close.
  //   branchSymbolic: the branch op had a SYMBOLIC condition at least once. A reached branch that is not in here
  //              was decided concretely every time -- constant in this build and harness (`sizeof(x) < 8`,
  //              `LZ4_isLittleEndian()`, a length the harness passes as a literal), so it is not a search failure
  //              and does not belong in the same bucket as the rest.
  std::set<std::pair<const Op *, bool>> flipUnsat, flipOpen;
  std::set<const Op *> branchSymbolic;

  // Harness-declared deterministic setup region (DESIGN.md §22.438). `seen` is false for a harness without the
  // markers, which is every harness that predates them. When it is true and `reused` is false, `refusal` says
  // why the region had to be executed again on every run -- the thing a reader needs, since the whole point of
  // declaring the region is that it should not be.
  bool setupRegionSeen = false, setupRegionReused = false;
  std::string setupRegionRefusal;
  double setupRegionSecRestore = 0;  // wall time spent restoring it, summed over the runs that did
  uint64_t setupRegionOps = 0;     // interpreter steps the region cost the one time it ran
  uint64_t setupRegionSkips = 0;   // runs that restored it instead of executing it
  uint64_t setupRegionAllocs = 0;  // allocations inside it taken as succeeding (DESIGN.md §22.440)
  unsigned setupRegionObjects = 0, setupRegionSymbolic = 0;
  // Globals that still held their initial value when a branch read them, over all runs: the branch was decided by
  // the static initialiser (or zero) because no other function of the module ran. Name -> one representative site;
  // `globalGatedBranches` counts the decisions. A lower bound, see RunResult::globalGatedBranches (DESIGN §22.362).
  std::map<std::string, Loc> globalGatedBy;
  std::set<const Op *> globalGatedSites;
  unsigned runsReturned = 0;                  // runs that finished normally
  unsigned runsTerminated = 0;                // runs that ended at a noreturn call / abort
  std::vector<TerminationSite> terminations;
};

class TaintExecutor {
 public:
  TaintExecutor(const Module &m, smt::TermManager &tm, smt::Solver &solver) : mod_(m), tm_(tm), solver_(solver) {}
  // `entry` must take no parameters (use an entry harness). `seed` maps core.nondet / input byte names to values;
  // unlisted names are 0.
  TaintResult run(const std::string &entry, const std::map<std::string, llvm::APInt> &seed, const TaintConfig &cfg = {});

 private:
  const Module &mod_;
  smt::TermManager &tm_;
  smt::Solver &solver_;
};

}  // namespace hlir

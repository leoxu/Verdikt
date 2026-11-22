// STABLE. The analysis report (DESIGN.md §17.9, §19.12): what was found, how sure we are, and under which assumptions.
// Plain data with no dependency on the analysis engines; writers produce text, JSON and SARIF 2.1.0 from it, so engines
// and report formats can change independently.
#pragma once
#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace hlir::report {

struct Location {
  std::string file;
  unsigned line = 0, col = 0;
  bool valid() const { return line != 0; }
};

// One named value of a counterexample, printed with the source-level name and type where known ("len = -2147483648 (int)").
struct WitnessItem {
  std::string name;
  std::string value;
  std::string note;
};

enum class ReplayStatus { Confirmed, NotReproduced, Skipped };

// ---------------------------------------------------------------- evidence (DESIGN.md §22.369)
// Mirrors semantics/Interpreter.h's ObjEvidence/AccessEvidence so the report stays independent of the engine
// headers. Purpose: let a reader rebuild the state that produced the finding instead of re-deriving it.
struct EvidenceByte {
  uint64_t off = 0;
  unsigned val = 0;
};

struct EvidenceObject {
  unsigned id = 0;
  std::string kind;    // param | global | heap | stack
  std::string name;
  bool sizeKnown = false;
  uint64_t size = 0;
  bool progWritten = false;   // globals: the program wrote it; false = still the static initialiser (§22.362)
  bool frontier = false;      // invented past the synthesis frontier: no counterpart in a real execution (§22.364)
  bool inputContent = false;
  // the object's bytes were never zero and were never anyone's data: the harness invented them (`content:
  // unknown`, DESIGN.md §22.381). Its SIZE is real, unlike a `frontier` object's.
  bool unknownContent = false;
  unsigned symbolicBytes = 0;
  std::vector<EvidenceByte> nonZero;
  bool truncated = false;
};

struct EvidenceAccess {
  bool valid = false;
  unsigned obj = 0;
  std::string objName;
  bool objSizeKnown = false;
  uint64_t objSize = 0;
  bool offsetKnown = false;
  long long offset = 0;
  bool offsetSymbolic = false;
  unsigned width = 0;
  std::string access;
};

// Can this finding be reproduced by feeding a REAL program a real input?
//   real_input   nothing in it depends on state only the harness could have made
//   harness_only it rests on something the harness invented (a frontier object, the project initialiser's own
//                code, or a condition only the harness's filler can satisfy). Chasing a real-world trigger for one
//                of these is wasted work, and saying so is the whole point of the field.
enum class Reproducible { RealInput, HarnessOnly };
const char *reproducibleName(Reproducible r);

struct Finding {
  std::string id;            // stable: <kind>@<function>:<line>
  std::string kind;          // UB kind (e.g. oob_write) or "assert"
  std::string message;
  Location loc;
  std::string function;      // function containing the failing operation
  std::string op;            // e.g. core.check.oob
  std::string origin;        // the source construct the op was lowered from, if known
  // Warning-severity data-flow finding (tainted_loop_bound / tainted_index): a defensive heads-up about an
  // attacker-controlled construct, not a proven defect. A warning never turns the entry's verdict into `bug`.
  bool warning = false;
  // The site is inside the project initialiser the harness runs before the entry (`init:`, DESIGN.md §22.368). It
  // is reported with its witness, but it decides nothing about THIS entry: not its verdict, and not whether the
  // entry counts as incompletely analysed.
  bool inPrologue = false;
  std::vector<WitnessItem> witness;
  ReplayStatus replay = ReplayStatus::Skipped;
  std::string unconfirmedReason;  // for NotReproduced: a code (overapprox_memory, replay_no_ub, replay_different_ub, ...)
  std::string unconfirmedDetail;
  std::string engine;        // taint_concolic | symbolic
  std::vector<std::string> labels;  // taint labels of the entry
  // functions on the call stack at the failing operation, outermost first, the entry function first (the generated harness is not
  // listed): its length is the call depth of the finding
  std::vector<std::string> callStack;
  // The failing op is inside this function, which has no source of its own (a ModelDB body); `location` is the
  // nearest enclosing call site instead. Empty when `location` is the op's own. DESIGN.md Sec.22.471.
  std::string locFromFrame;
  EvidenceAccess access;                   // the failing access in numbers
  std::vector<EvidenceObject> objects;     // the object hit, plus every global the run touched
  Reproducible reproducible = Reproducible::RealInput;
  std::string reproducibleWhy;             // why, when it is not real_input
};

// Something the verdict depends on (DESIGN.md §17.9). `category`:
//   init (legality constraint of the entry), attacker_model, env_fact (concrete value a query depends on),
//   concretized_pointer, promoted_env, bound (max_obj, run/step limits), precision (over-approximated memory)
struct Assumption {
  std::string category;
  std::string text;
  Location loc;
};

// Why the exploration may not have covered everything.
struct Incomplete {
  std::string code;          // path_limit, run_limit, step_limit, depth_limit, solver_unknown, unsupported, spec_contradiction, ...
  std::string detail;
};

struct FunctionClass {
  std::string function;
  uint64_t calls = 0, inert = 0, observer = 0, transformer = 0, source = 0, sanitizer = 0;
};

// One (caller, callee) call-graph edge, for the taint-highlighted call-graph visualisation (--format dot). `tainted`:
// at least one call across this edge, in some run, touched tainted data (see hlir::CallEdge / TaintDomain::onReturn) —
// not merely "an argument happened to be tainted at the call site": the whole invocation (its ops, branches, queries,
// sources, taint it returned or killed) is considered, so a function that reads the tainted bytes through a pointer
// argument and never passes anything back out still marks its calling edge red.
struct CallEdge {
  std::string caller, callee;
  uint64_t calls = 0;
  bool tainted = false;
};

struct Metrics {
  uint64_t runs = 0, pathsExplored = 0, solverQueries = 0, cacheHits = 0, escalations = 0;
  uint64_t stepsFirstRun = 0, taintedOpsFirstRun = 0, pcsFirstRun = 0, queriesFirstRun = 0, solverTerms = 0;
  double secAssert = 0, secCheck = 0;
  double secInterp = 0, secSolve = 0, secReplay = 0, secCone = 0;  // taint engine: where the analysis time went
  unsigned branchesCovered = 0;  // distinct (tainted branch, direction) pairs the concolic runs took
  unsigned maxCallDepth = 0;  // deepest call stack any run reached, counted from the entry function (1 = the entry itself)
  double secondsSeed = 0, secondsAnalysis = 0, secondsTotal = 0;
  // What the SEARCH got back for its queries (DESIGN.md Sec.22.468). `flipsQueued` flips were asked of the
  // solver; `flipsSolved` became a new input. A ratio of zero means the exploration never left its seed, and
  // every uncovered direction is then filed as "proved infeasible" -- a sentence that sounds like a result.
  uint64_t flipsQueued = 0, flipsSolved = 0, flipsUnsat = 0;
  // What the program's own asserted member bounds got to do past the synthesis frontier (DESIGN.md §22.365
  // A1). See semantics::RunResult for the four meanings.
  uint64_t frontierFieldReads = 0, frontierBoundsApplied = 0, frontierBoundsMissing = 0, frontierBoundsInfeasible = 0;
};

// What the exploration actually executed, so that a `safe` verdict can be judged: how much of the code the entry can reach was entered, how
// the runs ended, and where the frontier of the exploration is. Block coverage is over the functions reachable through direct calls from
// the entry (indirect calls are resolved through the generated dispatchers).
struct TerminationSite {
  std::string function, by, stack;  // function containing the call; the noreturn callee ("abort", "assume" for a bare terminating construct); its callers
  Location loc;
  unsigned runs = 0;
  std::vector<WitnessItem> witness;  // an input of the first run that ended here (the bytes the entry's tainted objects had)
};
// One conditional edge no run took, with the reason the ENGINE observed -- never a guess from reading the source.
struct MissedBranch {
  std::string file, function;
  unsigned line = 0, column = 0;
  bool dir = false;             // the direction that was never taken
  std::string why;              // unreached | const | unsat | open
};
struct Coverage {
  bool measured = false;
  uint64_t functionsReachable = 0, functionsEntered = 0;
  uint64_t blocksReachable = 0, blocksVisited = 0;    // blocks of the reachable functions / of them entered by some run
  uint64_t blocksInEntered = 0;                       // blocks of the functions some run entered
  // Branch directions of the functions some run entered. The honest denominator for "how well was THIS
  // entry explored": branchesReachable is a STATIC call-graph closure, so for an entry that links a whole
  // subsystem it is dominated by functions the entry never plausibly calls. Redis's RESP parser reported
  // 221/3070 (7%) while reaching 71 of 546 statically reachable functions -- the 7% says almost nothing
  // about the parser and almost everything about networking.c's size (DESIGN.md Sec.22.454).
  uint64_t branchesInEntered = 0;
  // Conditional-branch *directions* (not just blocks): every `core.cond_br` reachable from the entry contributes 2 (its
  // true/false edges); `branchesVisited` is how many of those edges some run actually took. 100% means every conditional
  // jump reachable from the entry had both directions exercised by at least one run, not merely "was reached".
  uint64_t branchesReachable = 0, branchesVisited = 0;
  uint64_t runsReturned = 0, runsTerminated = 0;      // runs that finished normally / that ended at a noreturn call
  std::vector<TerminationSite> terminations;          // where runs ended because the program ends (most frequent first)
  std::vector<std::string> notEntered;                // callees of entered functions that no run entered (the frontier), capped
  uint64_t notEnteredTotal = 0;
  // Every function some run actually entered (diagnostic only, never read by a verdict). The seam③ uncovered-bucket
  // (BACKWARD_WP_DESIGN §3.3) needs the POSITIVE set: a backward SAFE proof for a check in a function NOT here is a
  // safety result on code the forward search never reached. notEntered is only the one-hop frontier, so it cannot
  // answer this; this is the exact complement of "entered" among the reachable functions.
  std::vector<std::string> enteredFunctions;
  // The source lines ("file:line") some run actually executed. Block-grain complement to enteredFunctions for the
  // seam③ uncovered-bucket: a backward SAFE proof whose line is not here is on a block no forward run visited, even
  // when the function was entered (a guarded branch the search never took). Diagnostic, never read by a verdict.
  std::vector<std::string> coveredLines;
  // Why the branch coverage is not 100% (`--dump-branches`, DESIGN.md §22.429). Without this the number alone
  // cannot be acted on: "61%" is a search failure, an infeasible edge and a constant in this build added together,
  // and only one of the three is worth spending budget on.
  uint64_t missUnreached = 0;   // the branch op never executed at all (its block was never visited)
  uint64_t missConst = 0;       // executed, but its condition was never symbolic: constant in this build/harness
  uint64_t missUnsat = 0;       // the solver was asked for this edge and said UNSAT -- no budget opens it
  uint64_t missOpen = 0;        // a flip was queued and the budget ran out first: THE real coverage gap
  uint64_t missGlobalInit = 0;  // G1 (DESIGN.md Sec.22.362/22.465) named this branch: it was decided by a global's
                                // static initial value, so more budget cannot open it -- `init:` or G2 can
  std::vector<MissedBranch> branchesMissed;  // the individual edges, capped; only filled when asked for
  double blockRatio() const { return blocksReachable ? static_cast<double>(blocksVisited) / static_cast<double>(blocksReachable) : 0; }
  double branchRatio() const { return branchesReachable ? static_cast<double>(branchesVisited) / static_cast<double>(branchesReachable) : 0; }
};

// Safe means "no bug found in a complete exploration, under the listed assumptions" — never an absolute claim.
// SafeUpToLoopBound: no bug in any execution in which every loop runs at most the bound (the only thing left incomplete).
enum class Verdict { Bug, SafeUnderAssumptions, Unknown, SafeUpToLoopBound };

// What was actually checked, and what attacker data actually reached (DESIGN.md §22.369). Descriptive on purpose:
// this is NOT a claim that the entry is safe. Read `decidedConcretely` as a WEAKENING -- a check settled without
// ever asking the solver was settled because something was already pinned, which is usually why a path was not
// explored (see the `global_initial_value` assumption, §22.362).
struct CheckSummary {
  std::string kind;
  uint64_t reached = 0, decidedConcretely = 0, queried = 0, sat = 0, unsat = 0;
};

struct TaintReachReport {
  bool memoryIndex = false, loopBound = false, allocSize = false, sink = false;
  bool any() const { return memoryIndex || loopBound || allocSize || sink; }
};

struct EntryReport {
  std::vector<CheckSummary> checks;
  TaintReachReport taintReach;
  // The project initialisers the harness ran before this entry, in order (`init:`, DESIGN.md §22.368). A
  // reproduction has to run the same ones: the globals the entry reads are whatever they left behind.
  std::vector<std::string> initFunctions;
  // The session constructor that built this entry's session object (`setup:`, DESIGN.md §22.368 §7). Empty = none
  // was run, and the session is a field-by-field synthesis.
  std::string setupFunction;
  // External functions actually called with no model behind them, and how often (DESIGN.md §22.373). Ranked, this
  // is the worklist for "which model to write next".
  std::vector<std::pair<std::string, uint64_t>> opaqueCalls;
  // Functions that are opaque ONLY because the frontend could not lower them (name -> reason), e.g. an SSE __m128
  // vector initializer. The source is present; the call is opaque anyway because a failed lowering becomes a body-less
  // declaration. Reported apart from genuine missing externals so the fix named is "compile flag / frontend support",
  // not "write a model". Intersect with opaqueCalls to annotate only those actually hit (scripts/hlir_scanlib.py).
  std::map<std::string, std::string> lowerFailures;
  // WHERE THE SEARCH BUDGET WENT (DESIGN.md §22.392), ranked. Mirrors TaintResult::FrontierSite. A function with
  // a large `share` AND a large `perCall` is spending the search on sequential enumeration of what is logically
  // one decision -- the shape §22.385 removed from `strchr` by hand. Ranked, this is the worklist for "which
  // function to give a closed form next", the counterpart of `opaqueCalls`' "which model to write next".
  struct FrontierSite {
    std::string function;
    uint64_t flippablePcs = 0, queued = 0, calls = 0;
    double share = 0, perCall = 0;
    bool library = false, foldCandidate = false;
    uint64_t checksReached = 0, checksQueried = 0;  // see TaintResult::FrontierSite
  };
  std::vector<FrontierSite> frontier;
  uint64_t flippablePcsTotal = 0;
  // Harness-declared deterministic setup region (DESIGN.md §22.438). Reported whether it worked or not: a
  // declared region that the engine refused is a setup defect the author has to see, and it looks exactly like
  // a region that was never declared unless the refusal is printed.
  struct SetupRegion {
    bool declared = false, reused = false;
    std::string refusal;
    uint64_t ops = 0, skips = 0;
    double secRestore = 0;  // what the restores cost: the number that decides whether this feature pays
    uint64_t allocsForced = 0;  // allocations inside it taken as succeeding (DESIGN.md §22.440)
    unsigned objects = 0, symbolic = 0;
  };
  SetupRegion setupRegion;
  // The TARGET SET (DESIGN.md §22.374): the memory locations this entry's call chain actually reads, so the only
  // ones whose value can change its outcome. `location` is a global's name or a parameter's (`ocb`, `msg`, ...);
  // `offsets` are the byte offsets read. An UNDER-estimate when `readsIncomplete` -- a symbolic pointer denotes no
  // single location and is skipped rather than guessed.
  struct ReadSet { std::string location; std::vector<uint64_t> offsets; };
  std::vector<ReadSet> reads;
  bool readsIncomplete = false;
  std::string function;
  std::string specFile;
  std::string label;
  Verdict verdict = Verdict::Unknown;
  std::vector<Finding> findings;           // confirmed first
  std::vector<Assumption> assumptions;
  std::vector<Incomplete> incomplete;
  std::vector<FunctionClass> functionClasses;
  std::vector<CallEdge> callEdges;  // taint-engine call graph (empty when the taint engine did not run, e.g. a pure symbolic entry)
  Metrics metrics;
  Coverage coverage;
  std::string seedSummary;                 // the benign seed M0 in source terms
};

struct Report {
  std::string tool = "hlir";
  std::string version = "0.1";
  std::vector<EntryReport> entries;
};

const char *verdictName(Verdict v);
const char *replayStatusName(ReplayStatus s);

// Decides the verdict from the findings and incompleteness (Bug > Unknown > Safe).
Verdict computeVerdict(const EntryReport &e);

std::string toText(const Report &r);
std::string toJson(const Report &r);
std::string toSarif(const Report &r);
// Graphviz DOT source of the call graph(s) exercised by the taint engine (DESIGN.md: see IMPLEMENTATION_PLAN.md "call
// graph visualisation"). One node per function seen in some entry's callEdges, one edge per (caller, callee) pair;
// edges with CallEdge::tainted=true are drawn red and bold (color=red, penwidth=2), the rest in the default color.
// Multiple entries are drawn as separate `subgraph cluster_<entry>` blocks. Empty (no "digraph" text) when no entry
// has callEdges, e.g. a report read back from JSON written before this field existed.
std::string toDot(const Report &r);

// Reads a document written by toJson (a parallel scan collects per-entry reports this way). false + err on bad input.
bool fromJson(const std::string &text, Report &out, std::string &err);

}  // namespace hlir::report

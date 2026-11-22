// STABLE. Concrete interpreter facade for `core` programs (DESIGN.md §17).
// The implementation is a Domain-generic machine instantiated with a concrete domain; this header exposes no
// domain/template details, so the engine behind it can change without affecting users.
#pragma once
#include <chrono>
#include <cstdint>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "hlir/ir/IR.h"
#include "hlir/model/Model.h"
#include "hlir/semantics/Env.h"
#include "hlir/semantics/UB.h"
#include "hlir/support/Loc.h"
#include "llvm/ADT/APInt.h"

namespace hlir {

// How core.check.* ops without an explicit `mode` attribute behave (DESIGN.md §17.5).
enum class UBMode {
  Report,        // violation => UB error state (default)
  Wrap,          // -fwrapv: signed-overflow checks are ignored; everything else reports
  AssumeAbsent,  // checks become assumptions (violation => path is infeasible)
};

// A bound the program itself states about an integer member of a named record ("<tag>#<record size>@<offset>" is
// the key), harvested from its own assertion macros by the frontend (DESIGN.md §22.358). The engine applies these
// to objects materialised past the synthesis frontier, which the InitPlan's `where:` preconditions cannot reach
// because those objects do not exist when the plan is built (§22.365). Deliberately a plain struct here rather
// than frontend::AssertedBound: the semantics layer does not depend on the frontend.
struct FieldBound {
  bool hasLo = false, hasHi = false;
  int64_t lo = 0, hi = 0;  // inclusive
  unsigned bits = 0;
  bool isSigned = false;
};

// Opaque holder for the prologue memory snapshot: see RunConfig::prologueCache.
struct PrologueCache {
  virtual ~PrologueCache() = default;
  bool valid = false;
};

// Opaque holder for the state a harness-declared deterministic setup region produced (DESIGN.md §22.438).
// The concrete type is a template over the domain, which this header cannot name; the executor allocates the
// matching one and the Machine recovers it with a checked dynamic_cast.
//
// `state` is what makes the under-approximation visible rather than silent: a region is skipped only after the
// engine has captured it AND found nothing symbolic in what it produced. Anything else lands in Refused with a
// reason, and the reason goes in the report.
struct SetupCache {
  virtual ~SetupCache() = default;
  enum class State { Empty, Valid, Refused } state = State::Empty;
  std::string refusal;        // why this region is not being reused (State::Refused only)
  unsigned symbolicRegs = 0;  // live registers at the end of the region that hold a symbolic value
  unsigned symbolicCells = 0; // bytes of the objects the region created that are symbolic
  unsigned objects = 0;       // objects the region created
  uint64_t capturedOps = 0;   // interpreter steps the region cost the one time it ran
  uint64_t skips = 0;         // runs that restored it instead of executing it
};

struct RunConfig {
  UBMode ub = UBMode::Report;
  uint64_t maxSteps = 10'000'000;
  std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();  // wall clock: checked every 1024 steps, stops the run as StepLimit("time budget exhausted")
  unsigned maxCallDepth = 512;
  // Bounded unrolling: a basic block runs at most `loopBound` times per call (0 = unlimited). The run that would enter it once more
  // ends as RunStatus::LoopBound: it is cut, not a finding, and the analysis reports that it was bounded.
  unsigned loopBound = 0;
  bool trace = false;
  bool coverage = false;  // RunResult::blocksVisited is filled (costs a set insertion per block entry)
  unsigned memBound = 256;  // symbolic execution: unrolling bound for memcpy/memmove/memset with a symbolic length
  // Hard cap on how many bytes a single memcpy/memset (or string scan) physically expands into, even when its length
  // is a compile-time constant (see Memory.h's Memory::kMaxExpandDefault / setMaxExpand()). Independent of memBound
  // above. Default matches the previous hardcoded constant; raising it is opt-in.
  uint64_t memExpandMax = 1u << 20;
  // G2 / DESIGN.md Sec.22.465: resolve a SYMBOLIC index into a CONSTANT global by selecting over its
  // static initialiser, instead of concretising the index to this run's slot (which drops the taint and
  // files the branch as `const`). On by default: it is exact, so it cannot manufacture a finding.
  bool tableSelect = true;
  // The write-side dual (Memory.h symStoreTargets, DESIGN.md Sec.22.487): a store at a symbolic
  // offset into a small object becomes one guarded write per in-bounds offset, instead of landing
  // in the slot this run took and leaving every other slot untainted. Exact, like the read side.
  bool storeSelect = false;   // OPT-IN: --store-select
  const model::ModelProvider *models = nullptr;  // semantics of functions without a body (null: such calls are Unsupported)
  // Step-1 prototype (docs/DESIGN.md Sec.22.326/22.325): when a loop header (a block reached by a control-flow
  // back-edge) is revisited in the same frame, and the dependency set of every branch decision taken since the
  // previous visit (recursively through core.load addresses, conservatively bailing on calls/block-args) was never
  // written to during that span, and no core.nondet was drawn in it either -- the next iteration is provably
  // identical, so this run cannot terminate from here. Purely diagnostic: default off, and when on it only ever
  // sets RunResult::zeroProgressLoop*; it never changes `status` or any other existing field.
  bool detectNonTermination = false;
  // UB kinds that are RECORDED and then WALKED PAST instead of ending the run (`--ub-continue`). A deliberate,
  // named under-approximation for one target: the finding is still reported and the site goes into
  // `ubContinued`, but execution goes on, so code BEHIND a benign-but-real UB can be analysed at all.
  //
  // It exists because one such site in a hot path makes a whole library unscannable. libxml2's
  // xmlParseQNameHashed leaves `xmlHashedString.hashValue` indeterminate when a name has no prefix and the
  // struct is copied out and stored; that is a genuine uninitialised read, it is on the path of EVERY parse,
  // and with the run ending there no entry of the library ever got past its first document.
  //
  // This is NOT the same as the engine deciding a UB is benign on its own (that is §22.390's compare-only
  // pointer and §22.428's pointer arithmetic, both proved from the IR). Here the CALLER asserts it, so it is
  // listed in the report's assumptions and belongs in a scan profile where it can be reviewed.
  std::set<UBKind> ubContinue;
  // Keyed "<tag>#<record size>@<byte offset>"; null when nothing was harvested. See FieldBound.
  const std::map<std::string, FieldBound> *fieldBounds = nullptr;
  // The project's own initialiser(s) the harness calls before the entry (InitPlan::prologue, DESIGN.md §22.368).
  // A UB whose site is inside one of them is a fact about INIT CODE, not about this handler's attack surface, so
  // it must not decide the entry's verdict and -- the part that actually matters -- must not stop the run: the
  // measured failure (sound/core round 49b) was one deterministic `ptr_arith_oob` in `snd_info_register` halting
  // the first run of all 87 entries, which dropped block coverage 70% and made every verdict `bug` from the same
  // init-path site. Same discipline as `frontierOnly` (§22.365): a finding whose cause is not the entry's input
  // does not get to decide the entry.
  const std::set<std::string> *prologueFns = nullptr;
  // Functions that mean "the initialiser has finished its job": a server's `main` does not return, it ends in a
  // dispatch loop (`dispatch_block`, `resmgr_block`, `MsgReceive`, `wl_display_run`, `epoll_wait`). Reaching one
  // of these INSIDE the prologue unwinds back out of the initialiser and the harness carries on with the entry --
  // which is exactly the state a handler is really called in. Outside the prologue they are ordinary calls.
  // DESIGN.md §22.368 §2.
  const std::set<std::string> *stopFns = nullptr;
  // Measurement mode (DESIGN.md §22.374): record WHICH memory locations the entry's call chain actually reads --
  // which globals, which offsets of which parameter objects. Off by default: `core.load` is the hottest op there
  // is and a normal scan must not pay for a diagnostic.
  //
  // The point is not the list for its own sake. It is the TARGET SET: the only locations whose value can change
  // this entry's outcome. It bounds what an initialiser has to get right, and it is what keeps making an
  // initialiser's output "unknown" from exploding the path count -- a field nothing reads can stay concrete.
  // G2 restricted by the target set: globals (name -> the offsets this entry reads) whose value the program never
  // set, promoted to unconstrained at the moment the entry begins. Null = off, which is today's behaviour: they
  // keep their static initialiser and every branch on them is decided with no fork (§22.362). DESIGN.md §22.374.
  const std::map<std::string, std::set<uint64_t>> *promoteGlobals = nullptr;
  bool recordReads = false;
  // Where the engine stores (and finds again) the memory state the prologue produced, so it runs once per entry
  // instead of once per run (DESIGN.md §22.368). The concrete type is `Memory<D>::Snapshot`, which this header
  // cannot name; the executor allocates the matching one and the Machine recovers it with a checked dynamic_cast,
  // falling back to re-running the prologue if it ever does not match.
  PrologueCache *prologueCache = nullptr;
  // Where the engine stores (and finds again) the state a harness-declared deterministic setup region produced,
  // so the region runs once per entry instead of once per run (DESIGN.md §22.438). Null = the feature is off,
  // which is what a harness without the markers gets.
  SetupCache *setupCache = nullptr;
  // --entries registered: a DISCOVERY run of the module's `main` that
  // captures the dispatch tables handed to registration calls (resmgr_attach, vendor_util_run_loop,
  // register_filesystem, ...). The handlers written into those tables are the real taint entries -- found by
  // RUNNING the setup chain, so it works even when the handler is passed through a parameter or stored in a heap
  // field (both of which defeat the static `--entries iface` binding).
  //
  // bestEffortInit (user directive 2026-11-18): the discovery run only has to REACH the registration calls, not
  // execute faithfully, so an unmodelled/unknown call is a no-op (default/zero result) instead of ending the run
  // as Unsupported. Taint, precise semantics and argv are irrelevant here -- the single job is "reach every
  // resmgr_attach and read the table it was handed".
  bool bestEffortInit = false;
  struct RegCapture {
    std::string function;  // the registration call to intercept, e.g. "resmgr_attach"
    int tableArg = 0;      // which argument holds the dispatch-table pointer
    int scanBytes = 256;   // scan this many bytes of the table for function pointers
  };
  const std::vector<RegCapture> *captureRegs = nullptr;
  struct CapturedReg {
    std::string function;                               // which registration call this came from
    std::vector<std::pair<int, std::string>> handlers;  // (byte offset in the table -> handler function name)
  };
  std::vector<CapturedReg> *capturedRegs = nullptr;  // sink, filled during the run
  // Discovery run only: functions forced to SUCCEED without running their body, so a semantic gate between main's
  // entry and the registration call -- a HAL version check, a hardware probe -- that the abstract run cannot pass
  // does not stop main before it registers its handlers. Maps a function name to the integer it should return
  // (a module's success code is not always 0: one driver's HAL success code is 0x303). A pointer-returning gate
  // gets a non-null object instead, so a `!= NULL` check passes. Named by the caller (--discover-pass-fn),
  // reported, module-specific. A stopgap until the discovery runs symbolically.
  const std::map<std::string, long> *passFns = nullptr;
  // Discovery run only: every heap allocation SUCCEEDS (the may_fail fork is not taken), the same choice a
  // declared setup region makes (DESIGN.md §22.440) but for the whole run. The discovery run's one job is to
  // reach the registration call; a calloc that the concrete run decides to fail (and the NULL-check that bails on
  // it, and the zeroed fields a later range-check reads) must not stop it. e.g. hal_ctx = calloc(...) succeeds
  // -> hal_ctx != NULL and num_items == 0, so both of those gates pass with no --discover-pass-fn.
  bool forceAllocSuccess = false;
  // Discovery under the CONCOLIC engine (direction A, M3b-A): an OPAQUE (or model-less) setup call is routed through
  // the same execUntrusted path a hostile external API uses -- a symbolic return and symbolic bytes written over
  // every concrete pointer argument it is handed -- instead of a concrete no-op. So a field such a call "fills"
  // (e.g. a driver: hal_ctx->num_items, written by the dlopen'd HAL through an opaque indirect call) reads symbolic, and
  // the DATA gate that selects the registration path (`if (num_items > 0) register_handlers()`) forks; the path on
  // which setup succeeds reaches the registration and the capture hook fires. Only meaningful in a symbolic domain,
  // so set only on the symbolic discovery path. Requires bestEffortInit. `discoverHavocBytes` is execUntrusted's
  // outMax: the size of a synthesised pointer-return object AND the cap above which a pointer argument's pointee is
  // too large to havoc (left untouched) -- so it must exceed the setup structs whose fields gate registration.
  bool discoverHavoc = false;
  int discoverHavocBytes = 4096;
};

enum class RunStatus {
  Returned,      // finished normally; `returnValue` is set for non-void functions
  UB,            // a core.check.* (or core.unreachable) was violated; see `ub`
  AssertFailed,  // core.assert evaluated to false
  Infeasible,    // core.assume (or an assume-mode check) evaluated to false: this execution is not a real one
  Unsupported,   // op / feature not implemented by this engine yet; `message` explains
  StepLimit,
  DepthLimit,
  LoopBound,     // cut at RunConfig::loopBound iterations of a loop
  BadInput,      // unknown entry function / wrong argument count or width
};
const char *runStatusName(RunStatus s);

// ---------------------------------------------------------------- finding evidence (DESIGN.md §22.369)
//
// What a reader -- a person or an LLM asked to write a reproduction -- needs in order to rebuild the state that
// produced a finding, instead of re-deriving the defect from the source. The witness already names the entry's
// inputs; this names the MEMORY: which object was hit, how big it is, at what offset, and for every object that
// matters whether its content is a concrete value the run chose or a symbol the solver was free to pick.
//
// It is evidence, not a verdict. In particular `ObjEvidence::frontier` marks an object the harness INVENTED past
// the synthesis frontier: a finding that depends on one has no counterpart in a real execution, which is why
// Finding::reproducibleAs exists.
struct ByteEvidence {
  uint64_t off = 0;
  uint8_t val = 0;
};

struct ObjEvidence {
  uint32_t id = 0;
  std::string kind;   // param | global | heap | stack
  std::string name;   // global symbol or parameter name; "" when the object has no name
  bool sizeKnown = false;
  uint64_t size = 0;
  // globals: the PROGRAM wrote some byte of this, as opposed to the static initialiser being replayed. False means
  // the value below is the one the global was born with -- see the `global_initial_value` assumption (§22.362).
  bool progWritten = false;
  bool frontier = false;      // content invented past the synthesis frontier (§22.364)
  bool inputContent = false;  // every byte is attacker/caller supplied
  // every byte is the harness's invention -- symbolic, harness-labelled, nobody's data (`content: unknown`,
  // DESIGN.md §22.381). Unlike `frontier`, the object's SIZE is real, so bounds verdicts against it mean something.
  bool unknownContent = false;
  unsigned symbolicBytes = 0; // bytes whose content carries a symbolic term
  std::vector<ByteEvidence> nonZero;  // concrete non-zero bytes, capped
  bool truncated = false;     // more bytes exist than are listed (cap, or array representation)
  // A key that identifies this object ACROSS RUNS (DESIGN.md §22.375). Runtime object ids are allocation-order
  // counters: the same `struct snd_pcm_runtime` is id 47 in one pass and id 51 in the next, so an id cannot be
  // compared between two passes and means nothing to a reader. The key is the object's record type when the IR
  // could say it, otherwise its allocation SITE, which is a property of the program rather than of this run.
  // Empty when neither was available.
  std::string stableKey;
};

// The failing access itself, in numbers. Without this a reader has to re-derive which object was hit and where.
struct AccessEvidence {
  bool valid = false;
  uint32_t obj = 0;
  std::string objName;
  bool objSizeKnown = false;
  uint64_t objSize = 0;
  bool offsetKnown = false;
  int64_t offset = 0;      // signed: container_of-style arithmetic lands before the object
  bool offsetSymbolic = false;
  unsigned width = 0;      // access width in bytes, when the op carries one
  std::string access;      // "r" | "w" | ""
};

struct UBReport {
  UBKind kind;
  Loc loc;                // source location of the failing op, or -- see locFromFrame -- of the call site it was attributed to
  std::string function;
  std::string block;
  std::string op;         // e.g. "core.check.div"
  std::string origin;     // the op's `origin` attribute, if any
  std::string detail;     // e.g. "operands: 5, 0"
  uint64_t step = 0;
  std::vector<std::string> callStack;  // functions on the call stack when it happened, outermost first (the entry harness is the first)
  // Set when the failing op had NO source location of its own -- it is inside a ModelDB body (`__hlir_strlen`,
  // `__hlir_cbyte`, ...), which is compiled from models/libc.core and not from a .c file. `loc` is then the
  // nearest enclosing CALL SITE in real source, and this names the function the op is actually in, so the
  // attribution is stated rather than implied.
  //
  // Without this a real defect found THROUGH a model is invisible to everything that selects by location: the
  // CVE corpus's site criterion, triage, an upstream report. Measured on libexif CVE-2012-2812, an unbounded
  // strlen() over a buffer with no NUL: the engine found it and reported it at `@__hlir_strlen` with no file,
  // so the corpus scored `site=0` and recorded a FALSE MISS. DESIGN.md Sec.22.471.
  std::string locFromFrame;
  AccessEvidence access;               // the failing access in numbers (§22.369)
  std::vector<ObjEvidence> objects;    // the object hit, plus every global the run touched
};

// Where a nondet value came from, by its name (DESIGN.md §22.369). The witness prints names like
// `snd_pcm_control_ioctl.asm5`, which tell a reader nothing; a reproduction has to reproduce these CHOICES (an
// inline asm's result, an allocation that did not fail, an unmodelled external's return value) or it takes a
// different path, so the finding must say what each one is.
struct NondetOrigin {
  std::string function;   // the function the nondet was made in
  Loc loc;                // where
  std::string what;       // "inline asm" | "external @f" | "allocation failure" | ...
};

struct TraceEvent {
  enum Kind { Call, Return, Branch, Nondet, UBEvent, Observable } kind;
  std::string function;
  std::string text;
  Loc loc;
};

// Which security-relevant constructs attacker-controlled data actually REACHED on the explored paths
// (DESIGN.md §22.369). Stated this way on purpose: it is a checkable, falsifiable fact about what was executed,
// not the unsupported claim "this entry is taint free". Read it together with the coverage fraction -- a clean
// record over 2% of an entry's blocks means almost nothing.
struct TaintReach {
  bool memoryIndex = false;     // an attacker value scaled into a pointer offset
  bool loopBound = false;       // an attacker value governs an iteration count
  bool allocSize = false;       // an attacker value is an allocation size
  bool sink = false;            // an attacker value reaches a modelled security sink
};
// NOT here on purpose: "copy length" and "indirect call target". Both are real constructs worth tracking, but
// neither has an instrumentation point in this engine today (memcpy is not interpreted as its own opcode here, and
// an indirect call is lowered into a generated dispatcher, so the target selection is an ordinary branch inside
// it). A field that is always false because nobody filled it reads exactly like a field that is false because the
// construct was never reached -- which is the silent overclaim this whole record exists to avoid. When the hooks
// exist, add them; until then the absence is visible.

// How many checks of each UB kind were reached, and how they were settled. `decidedConcretely` is the number that
// never became a solver question because the value was already concrete -- most often BECAUSE something was pinned
// (a global still at its static initialiser, a harness-chosen field). A large number here makes a clean result
// weaker, not stronger (§22.369 §4).
struct CheckStat {
  uint64_t reached = 0, decidedConcretely = 0, queried = 0, sat = 0, unsat = 0;
};

struct RunResult {
  std::map<std::string, NondetOrigin> nondetOrigins;  // see NondetOrigin
  std::map<int, CheckStat> checks;                    // UBKind -> how its checks were settled
  // The same settlement, attributed to the FUNCTION the check is in. `checks` above says which kinds were
  // queried; this says WHERE. A function whose checks are reached thousands of times and queried zero times
  // is one where the search cannot learn anything from a flip: every safety question in it is already decided
  // by concrete values (DESIGN.md §22.437). That is the measurement the budget-dilution work needs, and it
  // cannot be read off the per-kind table.
  std::map<const Function *, CheckStat> checksByFn;
  // The `setup.success` assumption was false: the session constructor cannot succeed here, so no run of this entry
  // can get past it (DESIGN.md §22.371).
  bool setupInfeasible = false;
  // External functions that were actually CALLED with no model behind them, and how often. The static list of
  // unmodelled declarations (Pipeline's `opaqueFns`) says what COULD be hit; this says what was, which is the one
  // that tells you which model to write next. DESIGN.md §22.373.
  // location -> byte offsets read. Key: "global:NAME", "obj:<id>" for a harness parameter object (the driver maps
  // those ids back to parameter names), "obj:<stable key>" for anything else, or "obj:#<id>" when the object has
  // neither a record type nor a site (DESIGN.md §22.375). Capped: a runaway loop must not turn a diagnostic into
  // a memory problem.
  std::map<std::string, std::set<uint64_t>> reads;
  // id -> ObjEvidence::stableKey, for parameter objects only (those are the ones keyed by id above). The driver
  // prefers the spec's own parameter name, falls back to this, and only then to the bare id.
  std::map<unsigned, std::string> objKeys;
  std::map<std::string, uint64_t> opaqueCalls;
  // Externals whose model said "I write this buffer" without saying what (model::FillUnknownSpec), and how often.
  // A finding that rests on those bytes rests on the analysis's own invention, so the report has to name them.
  std::map<std::string, uint64_t> unknownWrites;
  unsigned globalsPromoted = 0;  // how many unwritten globals the target set actually promoted
  bool readsIncomplete = false;  // a symbolic pointer or a cap was hit: the read set is an under-estimate
  unsigned prologueStops = 0;   // times the initialiser was unwound at a stop function (RunConfig::stopFns)
  // Wall time this run spent RESTORING a declared setup region (DESIGN.md §22.438). Measured separately from
  // interpretation on purpose: the whole claim of the feature is that restoring is cheaper than re-executing,
  // and a restore that is a deep copy of a large heap is not.
  double secSetupRestore = 0;
  // Allocations inside a declared setup region that were taken as succeeding (DESIGN.md §22.440).
  uint64_t setupAllocsForced = 0;
  TaintReach taintReach;
  RunStatus status = RunStatus::BadInput;
  std::optional<llvm::APInt> returnValue;
  std::optional<UBReport> ub;
  // UB the run RECORDED and then deliberately walked past instead of stopping: a compare-only out-of-range
  // pointer (§22.390/§22.407) or one inside the project initialiser (§22.368). Keyed "<kind>@<file>:<line>".
  // Without this a replay could not confirm such a finding at all -- the run does not end in UB, so the only
  // evidence that the input reaches it is the fact that execution walked past it here (DESIGN.md §22.418).
  std::set<std::string> ubContinued;
  std::string message;    // AssertFailed / Unsupported / BadInput details
  Loc messageLoc;
  std::vector<TraceEvent> trace;
  uint64_t steps = 0;
  unsigned maxDepth = 0;  // deepest call stack of the run (frames, the entry harness counts 1)
  // char-class lookups over a constant needle answered in closed form instead of by running the model's loop
  // (DESIGN.md §22.385). Diagnostic only: it changes how much the search has to explore, never what is legal.
  unsigned charClassFolded = 0;
  unsigned memEqFolded = 0;   // calls to @__hlir_memeq answered branch-free (DESIGN.md §22.393)
  unsigned strCmpFolded = 0;  // strcmp/strcasecmp against a literal answered branch-free (Sec.22.491)
  unsigned printfFolded = 0;  // snprintf/sprintf calls answered in closed form (DESIGN.md §22.439)
  // WHAT A1 ACTUALLY GOT TO DO (DESIGN.md §22.365). `frontierFieldReads` scalar reads named a member of an
  // object materialised past the synthesis frontier; of those, `frontierBoundsMissing` found no bound the
  // program asserts about that member (a CORPUS fact: the target never wrote the assertion), while
  // `frontierBoundsApplied` (field,object) pairs had one assumed. `frontierBoundsInfeasible` runs were then
  // stopped because the invariant contradicted the path -- the only one of the four that is A1 changing an
  // answer. Without these, a null result cannot be read: a mechanism that never fires and a mechanism that
  // fires and does not matter look identical in the findings.
  uint64_t frontierFieldReads = 0, frontierBoundsApplied = 0, frontierBoundsMissing = 0, frontierBoundsInfeasible = 0;
  std::vector<const Block *> blocksVisited;  // RunConfig::coverage: every block the run entered, in no particular order
  // RunConfig::coverage: every (core.cond_br op, direction taken) pair this run executed, in no particular order.
  std::vector<std::pair<const Op *, bool>> branchesVisited;
  // The run ended because the program ends here (a call to a noreturn function, abort/exit/trap): the status is Infeasible (not a
  // real, analysable execution) but the analysis must not read "nothing found" as "this path is fine".
  bool terminated = false;
  std::string terminatedIn, terminatedBy;  // function containing the call; what ends the program (callee name or "assume")
  std::string terminatedStack;             // the callers above `terminatedIn`, innermost first: "f (file:line) <- g (file:line)" (at most 4)
  Loc terminatedAt;
  // RunConfig::detectNonTermination (docs/DESIGN.md Sec.22.326): set when a loop header's revisit proved the next
  // iteration must replay identically -- see RunConfig::detectNonTermination's comment for the exact condition.
  // Purely informational: a false value never means "proved to terminate", only "not proved not to" (most loops
  // make real progress and are correctly never flagged; see Sec.22.322's Command/Distance candidates for real
  // examples this step-1 version still cannot flag, since they consume real per-iteration progress).
  bool zeroProgressLoopObserved = false;
  std::string zeroProgressLoopFunction, zeroProgressLoopHeader;
  // Branch conditions this run decided by reading a global the program never wrote, i.e. by that global's static
  // initialiser (or zero). `module_init` is not executed, so such a decision assumes the module never ran; the
  // branch is also taken concretely, without a fork, so the other edge is never explored. A lower bound -- the
  // walk that produces it bails rather than guesses (see Machine::pristineGlobalIn, DESIGN.md §22.362).
  std::set<const Op *> globalGatedSites;      // the core.cond_br ops so decided (distinct sites, not decisions)
  std::map<std::string, Loc> globalGatedBy;   // global name -> one representative branch site
};

class Interpreter {
 public:
  explicit Interpreter(const Module &m) : mod_(m) {}
  // Runs `function` with concrete arguments (bool = width 1). The module should have passed the verifier.
  RunResult run(const std::string &function, const std::vector<llvm::APInt> &args, Env &env, const RunConfig &cfg = {}) const;

 private:
  const Module &mod_;
};

}  // namespace hlir

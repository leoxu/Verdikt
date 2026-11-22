// STABLE. The end-to-end pipeline behind `hlir-taint`: entry spec -> legal initial state -> harness -> taint-selective
// concolic analysis -> (precision escalation) -> replay-confirmed findings -> report. It is the only place that wires the
// engines together; everything it uses is reachable through the stable interfaces of the other modules.
#pragma once
#include <map>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "hlir/report/Report.h"
#include "hlir/semantics/Taint.h"

namespace hlir { class Module; }

namespace hlir::driver {

struct AnalysisOptions {
  std::string coreText, coreName = "input.core";
  // Skip parsing+verifying `coreText` (+ libcText) here and reuse this instead — for a large `--link` program,
  // that parse dominates a single entry's analysis time (see tools/hlir-scan.cpp's HLIR_DEBUG_PARSE instrumentation
  // and the measurements in docs/DESIGN.md §22.12/§22.13). The caller is expected to have parsed+verified `coreText`
  // itself via `parseModule`. `analyzeEntry` still mutates it (appends this entry's harness via `parseModuleInto`),
  // so **each `preParsedBase` instance may be passed to at most one `analyzeEntry` call** — hlir-scan's fork-per-entry
  // worker model gives every entry its own copy-on-write view of the same parsed Module for free; reusing one
  // `shared_ptr<Module>` across multiple `analyzeEntry` calls *in the same process* would let their harnesses pile
  // up on top of each other.
  std::shared_ptr<Module> preParsedBase;
  // Fill `Coverage::branchesMissed` with the individual uncovered conditional edges (`--dump-branches`). The four
  // per-class COUNTS are always computed -- they are four integers and they are what makes a coverage number
  // actionable; only the list itself is opt-in, because a large program has thousands of edges.
  bool listMissedBranches = false;
  std::set<UBKind> ubContinue;   // --ub-continue: kinds recorded but walked past (RunConfig::ubContinue)
  std::string libcText;            // optional C library models in core (models/libc.core), appended to the module
  std::vector<std::pair<std::string, std::string>> models;  // ModelDB YAML documents: (path, text); later ones override earlier ones
  // Calls to functions that have neither a body nor a model are assumed opaque (arbitrary untainted result, no effect on
  // memory) instead of making the analysis stop with "unsupported". The affected functions are listed as an assumption.
  bool opaqueExternals = false;
  // Functions the FRONTEND could not lower (an unsupported construct -- e.g. SSE/__m128 vector initializers), keyed by
  // the LINKED name, with the reason. Such a function is emitted as a body-less declaration, so it ends up opaque just
  // like a genuine missing external -- but the two are different problems (the source IS present here; the fix is a
  // compile flag or frontend support, not a model). The report separates them so an opaque call that is really a
  // lowering failure says so instead of sending the reader to write a model for code that is right there. See
  // lib/driver/Pipeline.cpp (opaqueFns split) and scripts/hlir_scanlib.py (gate message).
  std::map<std::string, std::string> notLoweredFns;
  // The project's statement about the externals it calls (`--externs`, DESIGN.md §22.379). Only the skip list is
  // needed here: the model documents it names are loaded into `models` by the caller. Functions on it are still
  // opaque -- nothing about their SEMANTICS changes -- but the report says they were examined and judged not to
  // contribute, instead of listing them next to the ones nobody has looked at.
  std::vector<model::ExternsFile::Skip> externSkips;
  std::vector<std::string> initArgv;  // see model::ExternsFile::argv
  std::string externsPath;
  // frontend::LowerResult::containerOfWaived, summed over the units in the link set: named as an assumption when
  // nonzero (DESIGN.md §22.368).
  // frontend::LowerResult::spawnCallbacksEmitted, summed over the link set: named as an assumption when nonzero
  // (DESIGN.md §22.372). Widens coverage, narrows sequencing -- both have to be visible.
  // Two-pass G2 (DESIGN.md §22.374): pass 1 measures which globals this entry reads, pass 2 re-runs with exactly
  // those -- and only those -- promoted to unconstrained when the program never wrote them. Set by the driver on
  // the second pass; `--promote-read-globals` turns the flow on.
  const std::map<std::string, std::set<uint64_t>> *promoteGlobals = nullptr;
  bool promoteReadGlobals = false;
  // Auto-targeting (DESIGN.md §22.415): after the analysis, aim `taint.reachTarget` at functions the search never
  // entered and re-run, up to this many extra rounds. 0 = off. The target set is the coverage frontier
  // (`Coverage::notEntered`, ordered so the ones that can actually hold a defect come first), which is by
  // construction ONE CALL EDGE from explored code -- the condition under which --reach-target was measured to
  // help at all. Each round is a full analysis, so this is opt-in and bounded.
  unsigned autoTargetRounds = 0;
  unsigned spawnCallbacks = 0;
  unsigned containerOfWaived = 0;
  std::string containerOfFirstSite;
  // Threat model "a component below the analysed code is compromised": functions without a body or a model whose name matches this regex are
  // hostile (see model::ModelDB::setUntrusted). Implies opaqueExternals for every other external function. Empty = off.
  std::string untrustedApi, untrustedLabel = "untrusted";
  unsigned untrustedOutMax = 256;
  std::vector<std::pair<std::string, std::string>> preconditions;  // preconditions files (path, text), merged into the entry's spec (entry/Spec.h)
  std::string specText, specName = "spec.yaml";
  std::string entry;               // function named in the spec
  TaintConfig taint;               // run limits, environment promotion, timeout layering, ...
  bool escalate = true;            // when the concolic result may be incomplete (concretised pointers), also run the full symbolic engine
  // Iterative deepening: analyse with each bound in turn (ascending). A bug ends it; a complete result without any cut loop is exact
  // and ends it; a bound whose exploration does not finish within the budget leaves the verdict of the previous bound, marked
  // with incomplete:deeper_bound_unfinished. Overrides loopBound.
  std::vector<unsigned> loopBounds;
  unsigned loopBound = 0;          // bounded unrolling (0 = off): see RunConfig::loopBound; the verdict can become safe_up_to_loop_bound
  unsigned maxPaths = 2000;        // symbolic engine path limit
  // SymConfig::memBound (default 256, see Symbolic.h): the symbolic escalation pass's unrolling bound for
  // memcpy/memset/model-fill (e.g. recv/fread) calls whose length isn't a compile-time constant -- a call needing
  // more than this many bytes unrolled reports incomplete:symbolic_bound_insufficient rather than being explored.
  // Previously hardcoded with no CLI knob (found while ground-truth-validating curl CVE-2019-5436, whose trigger
  // needs a 516-byte recv() fill); 0 keeps SymConfig's own default.
  unsigned memBound = 0;
  // SymConfig::memExpandMax (default 1<<20, see Symbolic.h / Memory.h's kMaxExpandDefault): hard cap on bytes a
  // single memcpy/memset/string-scan the symbolic escalation pass runs physically expands, even for a constant
  // length -- independent of memBound above (that one is for a *symbolic* length). A call needing more bytes than
  // this reports incomplete:unsupported rather than being explored. Only reaches the symbolic escalation pass (see
  // KNOWN_GAPS_PRIORITIZED.md's kMaxExpand entry for the primary concolic/taint engine's own, unrelated limit).
  // 0 keeps SymConfig's own default.
  uint64_t memExpandMax = 0;
  // --no-table-select: turn OFF selection over a constant table's static initialiser (G2,
  // DESIGN.md Sec.22.465). There to make the behaviour comparable against the old one, not because
  // the old one is ever preferable -- selection is exact.
  bool noTableSelect = false;
  // --store-select: guarded selection for a store at a symbolic offset (Sec.22.487). Unlike its
  // read-side twin this is OPT-IN, because it is not yet established to be only-better: it closes
  // the `const` branch it was built for AND it made snprintf_chain_oob's replay-confirmed
  // oob_write come back `not_reproduced`. A default is a claim about every scan, and that claim
  // cannot be made while one fixture's answer gets worse.
  bool storeSelect = false;
  unsigned solverTimeoutMs = 10000;
  // Coverage gate: when > 0 and the blocks entered by the runs are less than this fraction (0..1) of the blocks of the functions reachable
  // from the entry, the verdict cannot be safe (incomplete:low_coverage). The coverage itself is always reported.
  double minCoverage = 0;
  double wallSeconds = 0;          // wall-clock budget of the whole analysis (0 = none); on expiry the findings so far are reported as incomplete:time_budget
};

struct AnalysisOutcome {
  bool ok = false;                 // false: bad input (parse/spec/verify error); `error` explains
  std::string error;
  report::EntryReport entry;       // valid when ok (a contradictory spec is ok=true with verdict unknown and incomplete[spec_contradiction])
  // What THIS pass covered, under names that survive a re-parse. analyzeEntry unions them over every pass it
  // runs and recomputes the reported coverage from the union, so a multi-pass analysis reports the whole
  // search's coverage instead of its last pass's (DESIGN.md §22.415). Not serialised: an internal carrier.
  std::set<std::string> edgeKeys;
  std::set<std::string> blockKeys;
};

AnalysisOutcome analyzeEntry(const AnalysisOptions &opt);

/// How many uncovered conditional edges --dump-branches keeps per entry (DESIGN.md Sec.22.445).
/// Reported alongside the dump so a truncated dump is never mistaken for a complete one; overridable
/// with HLIR_MAX_MISSED_BRANCHES.
size_t maxMissedBranchesPerEntry();

}  // namespace hlir::driver

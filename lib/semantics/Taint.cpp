#include <algorithm>
#include <random>
#include <limits>
#include <memory>
#include <chrono>
#include "hlir/semantics/Taint.h"

#include <deque>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "llvm/ADT/DenseSet.h"

#include "TaintDomain.h"
#include "hlir/semantics/ReachTarget.h"
#include "hlir/semantics/BarrenBranch.h"

namespace hlir {

namespace {

using smt::SatResult;
using smt::TermRef;

// Constraints connected to `target` through shared variables (transitively): the dependency cone of a query. Dropping the
// rest is sound because the current concrete run satisfies them with values the cone does not touch.
struct Cone {
  std::vector<TermRef> constraints;  // the kept ones
  std::vector<size_t> idxs;          // ...and where each came from in the run's path conditions (parallel to `constraints`)
  std::vector<TermRef> vars;
  uint64_t terms = 0;                // distinct SMT terms reachable from the kept constraints and the target
};

// Variables of a term, remembered across calls (a run asks for the cone of hundreds of query sites over the same constraints).
using VarCache = std::unordered_map<TermRef, std::vector<TermRef>>;

// Which constraints of one run mention which variable; built once per run, then every query site's cone is a walk over
// the constraints it actually depends on (instead of a pass over all of them per site).
//
// Only the first occurrence of each distinct constraint term is indexed. A loop that re-evaluates the same tainted
// branch on every iteration pushes the same hash-consed term again and again; conjunction is idempotent, so the
// repeats add nothing to a query, and the first occurrence lies inside any prefix `limit` that a repeat does. Indexing
// them all made cones carry the duplicates to the solver: on the cJSON scan 99.9% of the assumption literals sent to z3
// were repeats (7388 literals, 4 distinct, in one query), and prefixes differing only in repeat count missed the query
// cache. Deduplicating cut solver time by 67% with no finding lost (docs/DESIGN.md Sec.22.336).
struct ConeIndex {
  const std::vector<TermRef> *all = nullptr;
  std::unordered_map<TermRef, std::vector<size_t>> byVar;  // ascending constraint indices, first occurrences only
};
ConeIndex buildConeIndex(const std::vector<TermRef> &all, VarCache &varsOf) {
  ConeIndex idx;
  idx.all = &all;
  std::unordered_set<TermRef> indexed;
  for (size_t i = 0; i < all.size(); ++i) {
    if (!indexed.insert(all[i]).second) continue;
    smt::collectVarsMemo(all[i], varsOf);
    for (auto *v : varsOf.at(all[i])) idx.byVar[v].push_back(i);
  }
  return idx;
}

// The cone of `target` among the first `limit` constraints.
Cone coneOf(const ConeIndex &idx, size_t limit, TermRef target, VarCache &varsOf) {
  auto vars = [&](TermRef t) -> const std::vector<TermRef> & {
    smt::collectVarsMemo(t, varsOf);
    return varsOf.at(t);
  };
  const auto &all = *idx.all;
  std::unordered_set<size_t> kept;
  std::unordered_set<TermRef> live;
  std::vector<TermRef> queue;
  auto touch = [&](TermRef v) { if (live.insert(v).second) queue.push_back(v); };
  for (auto *v : vars(target)) touch(v);
  for (size_t qi = 0; qi < queue.size(); ++qi) {
    auto it = idx.byVar.find(queue[qi]);
    if (it == idx.byVar.end()) continue;
    for (size_t i : it->second) {
      if (i >= limit) break;
      if (!kept.insert(i).second) continue;
      for (auto *v : vars(all[i])) touch(v);
    }
  }
  std::vector<size_t> order(kept.begin(), kept.end());
  std::sort(order.begin(), order.end());
  Cone c;
  std::vector<TermRef> roots{target};
  for (size_t i : order) { c.constraints.push_back(all[i]); c.idxs.push_back(i); roots.push_back(all[i]); }
  std::unordered_set<TermRef> seen;
  std::vector<TermRef> stack(roots.begin(), roots.end());
  while (!stack.empty()) {
    TermRef t = stack.back();
    stack.pop_back();
    if (!seen.insert(t).second) continue;
    for (auto *a : t->args) stack.push_back(a);
  }
  c.terms = seen.size();
  c.vars.assign(live.begin(), live.end());
  std::sort(c.vars.begin(), c.vars.end(), [](TermRef a, TermRef b) { return a->id < b->id; });
  return c;
}

std::string idKey(const std::vector<TermRef> &v, size_t n) {
  std::string k;
  k.reserve(n * 6);
  for (size_t i = 0; i < n; ++i) { k += std::to_string(v[i]->id); k += ','; }
  return k;
}

// Identity of a path prefix as a 128-bit rolling hash of the constraint ids: the keys of all prefixes of one path (and of
// "prefix + the negated next constraint") cost O(1) each instead of a string of the whole prefix (a long run has 10^4 constraints).
// Kept as the two words themselves in a flat open-addressing set: every run inserts every prefix of its path, so the set
// is large and hot -- rendering each prefix as a 32-character hex string into an unordered_set<string> (one heap node
// per element) was ~7% of a scan once term interning was fixed (docs/DESIGN.md Sec.22.338).
struct PathHash {
  uint64_t a = 0x9e3779b97f4a7c15ULL, b = 0x243f6a8885a308d3ULL;
  PathHash add(uint64_t id) const {
    PathHash h = *this;
    h.a = (h.a ^ (id + 0x9e3779b97f4a7c15ULL)) * 0xff51afd7ed558ccdULL;
    h.a ^= h.a >> 33;
    h.b = ((h.b << 7) | (h.b >> 57)) + id * 0xc4ceb9fe1a85ec53ULL;
    h.b *= 0xd6e8feb86659fd93ULL;
    h.b ^= h.b >> 29;
    return h;
  }
  bool operator==(const PathHash &o) const { return a == o.a && b == o.b; }
};
// DenseSet traits. The two reserved keys are all-ones words; a real prefix hashing to one of them has probability 2^-127.
struct PathHashInfo {
  static PathHash getEmptyKey() { return {~0ULL, ~0ULL}; }
  static PathHash getTombstoneKey() { return {~0ULL, ~0ULL - 1}; }
  static unsigned getHashValue(const PathHash &h) { return static_cast<unsigned>(h.a ^ (h.a >> 32)); }  // `a` is already mixed
  static bool isEqual(const PathHash &x, const PathHash &y) { return x == y; }
};

}  // namespace

TaintResult TaintExecutor::run(const std::string &entry, const std::map<std::string, llvm::APInt> &seed0, const TaintConfig &cfg) {
  TaintResult res;
  auto bad = [&](std::string why, const char *code) {
    res.complete = false;
    res.reason = code;
    res.note = std::move(why);
    return res;
  };
  const Function *f = mod_.findFunction(entry);
  if (!f) return bad("unknown function @" + entry, "unknown_function");
  if (f->isDeclaration()) return bad("@" + entry + " has no body", "unknown_function");
  if (!f->paramTys.empty()) return bad("@" + entry + " must take no parameters (analyse an entry harness)", "input_error");

  RunConfig rc;
  rc.ub = cfg.ub;
  rc.ubContinue = cfg.ubContinue;
  if (cfg.wallSeconds > 0) rc.deadline = std::chrono::steady_clock::now() + std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(cfg.wallSeconds));
  rc.maxSteps = cfg.maxSteps;
  rc.maxCallDepth = cfg.maxCallDepth;
  rc.loopBound = cfg.loopBound;
  rc.memExpandMax = cfg.memExpandMax;
  rc.tableSelect = cfg.tableSelect;
  rc.storeSelect = cfg.storeSelect;
  rc.models = cfg.models;
  rc.fieldBounds = cfg.fieldBounds;
  rc.prologueFns = cfg.prologueFns;
  rc.stopFns = cfg.stopFns;
  rc.recordReads = cfg.recordReads;
  rc.promoteGlobals = cfg.promoteGlobals;
  // --entries registered symbolic discovery: the capture hook + gate-skip, shared by every concolic run (the sink
  // vector is appended to across runs; hlir-scan dedups by inserting into a set, so repeated captures are harmless).
  rc.bestEffortInit = cfg.bestEffortInit;
  rc.forceAllocSuccess = cfg.forceAllocSuccess;
  rc.captureRegs = cfg.captureRegs;
  rc.capturedRegs = cfg.capturedRegs;
  rc.passFns = cfg.passFns;
  rc.discoverHavoc = cfg.discoverHavoc;
  rc.discoverHavocBytes = cfg.discoverHavocBytes;
  // One snapshot per entry, shared by every run: the first run executes the initialiser and stores what it
  // produced, the rest restore it and skip the calls (DESIGN.md §22.368). Owned here so its lifetime covers the
  // whole run loop; `Memory<TaintDomain>::Cache` is the type the Machine expects to find behind the base pointer.
  Memory<TaintDomain>::Cache prologueCache;
  if (cfg.prologueFns && !cfg.prologueFns->empty()) rc.prologueCache = &prologueCache;
  // The same idea, but for a region the HARNESS ITSELF declares with hlir_setup_begin()/hlir_setup_end()
  // (DESIGN.md §22.438): a deterministic prefix that is not a project initialiser and whose RESULT the harness
  // keeps. Always handed over -- a harness without the markers never reaches the code that reads it, and giving
  // it unconditionally is what lets the report distinguish "no region declared" from "declared and refused".
  SetupState<TaintDomain> setupCache;
  rc.setupCache = &setupCache;
  rc.coverage = true;
  TaintDomainConfig dcfg;
  dcfg.promote = cfg.promote;
  dcfg.promoteAll = cfg.promoteAll;
  dcfg.inputLabel = cfg.inputLabel;
  dcfg.labelSeeds = cfg.labelSeeds;
  dcfg.dropPcsAboveDepth = cfg.dropPcsAboveDepth;
  dcfg.entryFunction = entry;  // --reach-target distance lookup for depth-0 branches needs the entry's real name, not "<entry>"

  const auto t0 = std::chrono::steady_clock::now();
  auto overBudget = [&] { return cfg.wallSeconds > 0 && std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() >= cfg.wallSeconds; };

  VarCache varCache;
  struct SessionGuard { smt::Solver &s; explicit SessionGuard(smt::Solver &x) : s(x) { s.beginSession(); } ~SessionGuard() { s.endSession(); } } sessionGuard(solver_);
  // Coverage-guided order: a seed made by flipping a branch whose other direction no run has taken yet goes first; ties keep
  // the order they were made in (breadth first). `covered` = (branch op, direction) pairs some run executed.
  std::set<std::pair<const Op *, bool>> covered;
  // Target-guided search (cfg.reachTarget): distances are computed once, up front, from the static call graph; `distOf`
  // below is the only place they are read. When reachTarget is empty, distOf always returns 0 for every function, so
  // `dist` never varies and WorkKey's ordering collapses to exactly (fresh, seq) -- the pre-existing default order.
  const std::map<std::string, int> targetDist = cfg.reachTarget.empty() ? std::map<std::string, int>{} : computeTargetDistance(mod_, entry, cfg.reachTarget);
  // "Nothing can go wrong down there" (DESIGN.md §22.415). A branch edge whose own region holds no `core.check.*`
  // op cannot produce a finding however it is solved, so its flips sort last. This is a DEMOTION, not a filter --
  // except that the frontier is capped, and the cap evicts the tail. That is the point: the two targets measured
  // (libyaml 99313 of 170640 queued flips dropped, tcpdump olsr 23337 of 57483) were ALREADY discarding most of
  // the queue, by arrival order. Sinking the provably barren edges makes an eviction that already happens use a
  // reason instead of a sequence number.
  //
  // OFF BY DEFAULT, and the measurement is why -- the same shape as the unsat-core tier above. On tcpdump
  // CVE-2017-13688 the detection threshold MOVED WITH THE BUDGET rather than improving:
  //
  //     runs=2000   barren=--    plain=--
  //     runs=4000   barren=HIT   plain=--      <- barren wins
  //     runs=8000   barren=--    plain=HIT     <- barren loses
  //
  // A result that flips with the budget on one target is a reordering lottery, not an improvement, and the
  // other two targets in that ladder (cfm, aoe) reproduced their known detection in NEITHER arm, so those rows
  // measure the ladder's configuration and not the engine. Left in, behind a flag, because the PROPERTY it
  // computes is a derivation rather than a guess, and because the next person should measure instead of
  // re-deriving. The honest open question is whether this belongs in the sort order at all, or only in the
  // eviction rule once the frontier is full -- which is where the 41-58% of queued flips are actually lost.
  const bool barrenOff = getenv("HLIR_BARREN_DEMOTE") == nullptr;
  const BarrenInfo barrenInfo = barrenOff ? BarrenInfo{} : computeBarrenEdges(mod_);
  // The flip of a branch taken in direction `dir` goes to the OTHER successor: `dir` true means succs[0] was taken
  // (Machine.h's CondBr), so the flip lands on succs[dir ? 1 : 0].
  auto barrenFlip = [&](const Op *site, bool dir) -> int {
    if (barrenOff || !site) return 0;
    return barrenInfo.barren.count({site, dir ? 1u : 0u}) ? 1 : 0;
  };
  // Filled after every run from RunResult::checksByFn: which functions the safety checks live in, and whether
  // any of them was ever symbolic. Reported per function in `search_budget` (DESIGN.md §22.437).
  std::map<std::string, std::pair<uint64_t, uint64_t>> checksByFn;  // function -> (reached, queried)
  auto distOf = [&](const std::string &fn) -> int {
    if (cfg.reachTarget.empty()) return 0;
    auto it = targetDist.find(fn);
    return it == targetDist.end() ? kUnreachableTargetDistance : it->second;
  };
  // Ordering, highest priority first.
  //
  // `blocker` is the one that is not a heuristic. A run that REACHED a memory-safety check and found its failure
  // condition unsatisfiable has, in the unsat core, the exact path conditions that rule the failure out -- so the
  // other direction of those branches is the only way that check could ever fail. Everything else in this key is a
  // guess about where a defect might be; this is a derivation of where it cannot not be.
  //
  // It is what coverage cannot give. Measured on c-ares CVE-2023-31130: "::.6/0" covers 74 of 122 blocks and finds
  // nothing, while "::1:2:3/0" covers 59 and is the defect -- because the '.' that buys the extra coverage takes
  // the branch that sets ipv4=1, and ipv4=1 restores endp to the full 16 bytes and makes the overflow impossible.
  // A coverage-ranked search prefers exactly the input that disables the bug. An unsat core names that branch.
  struct WorkKey {
    int blocker;  // 1: the other direction of this branch is in the unsat core of a safety check that was refuted
    int fresh;
    int barren;  // 1: the region this flip enters provably contains no UB check -- sorted last, and evicted first
    int dist;  // call-graph distance to cfg.reachTarget; always 0 when target-guided search is off
    uint64_t seq;
    bool operator<(const WorkKey &o) const {
      if (blocker != o.blocker) return blocker > o.blocker;
      if (fresh != o.fresh) return fresh > o.fresh;
      // Below `fresh` on purpose: coverage is the proxy that has been measured to work, and a barren edge can
      // still set state that a later, fruitful edge depends on. Demoting it within its coverage tier keeps that
      // path reachable while putting it where the cap bites first.
      if (barren != o.barren) return barren < o.barren;
      if (dist != o.dist) return dist < o.dist;
      return seq < o.seq;
    }
  };
  // Lazy frontier: a finished run does not solve its flip queries up front (a long path has dozens, and only a few of them ever get
  // executed within the budget); it registers them. A flip is solved when it reaches the front; if it is unsatisfiable the next
  // one is taken. A seed item (the start, or a repaired seed) is ready to run as it is.
  struct RunData {
    std::vector<TermRef> pcTerms;
    std::vector<std::pair<const Op *, bool>> pcSites;  // pcTerms[i]'s branch op and the direction THIS run took
    // pcTerms[i] is an engine-imposed concretisation, not a decision the program made (PcEntry::concretisation).
    // Kept for safety queries, dropped from flip queries.
    std::vector<char> pcConcrete;
    bool anyConcrete = false;
    ConeIndex coneIdx;
    std::map<std::string, llvm::APInt> assign;
  };
  struct WorkItem {
    std::map<std::string, llvm::APInt> seed;  // isFlip == false
    std::shared_ptr<RunData> run;             // isFlip: the run whose branch `idx` is to be flipped
    size_t idx = 0;
    bool isFlip = false;
  };
  const size_t kMaxFrontier = cfg.maxFrontier ? cfg.maxFrontier : std::numeric_limits<size_t>::max();
  std::map<WorkKey, WorkItem> work;
  // A flip is queued once, under the hash of "path prefix + the negated branch", and a later run that walks the
  // same prefix is deduped away. That dedup is older than the unsat-core tier and it silently defeated it: a core
  // nearly always blames a branch some earlier run had already queued at ordinary priority, so of 46088 queued
  // flips only 66 were ever promoted and detection did not move. Generalising the core to (branch site, direction)
  // so it would survive across runs made it WORSE, not better -- 38232 of those same 46088 flips then qualified,
  // which is not a priority tier but a coin flip, and at 14000 runs it turned a found defect into a miss. The core
  // is precise per run and must stay that way; what has to change is that a flip ALREADY in the frontier can be
  // moved to the head when a later run proves it is what blocks a safety check.
  llvm::DenseMap<PathHash, WorkKey, PathHashInfo> queuedAt;
  size_t frontierDropped = 0, frontierPeak = 0, flipsQueued = 0, flipsDeduped = 0, flipsUnsat = 0, blockerFlips = 0, relaxTried = 0, relaxQueued = 0, concDropped = 0, flipsSolved = 0;
  std::map<std::string, size_t> flipsByFn, pcsByFn, noLocByFn;
  uint64_t workSeq = 0;
  const bool guided = !getenv("HLIR_SEARCH_FIFO");  // debugging/A-B aid: plain breadth-first order
  const bool dbgDedup = getenv("HLIR_DEBUG_FRONTIER") != nullptr;
  // OFF BY DEFAULT, and the measurement is why. Both halves work -- cores come back precise (one or two real
  // program branches, e.g. the hex-digit test at inet_net_pton.c:294) and the relaxation re-solves thousands of
  // them -- but on c-ares CVE-2023-31130 neither moved the detection threshold at any budget from 500 to 14000
  // runs, while the relaxation alone cost 7546 extra solver queries per 5000 runs. The reason is in DESIGN.md
  // §22.387: on that entry EVERY memory-safety check is decided concretely (oob_write reached 124282 times,
  // queried 0), so there is no symbolic check at the defect's own site for a core to be taken of. Reasoning about
  // why a check cannot fail is worth nothing until the check is a query. Left in, behind a flag, because it is
  // the right mechanism once that is fixed -- and so the next person measures instead of re-deriving.
  const bool useBlocker = getenv("HLIR_UNSAT_CORE_GUIDE") != nullptr;
  const bool relax = useBlocker && !getenv("HLIR_NO_RELAX");
  { WorkItem w0; w0.seed = seed0; work.emplace(WorkKey{0, 1, 0, 0, workSeq++}, std::move(w0)); }
  llvm::DenseSet<PathHash, PathHashInfo> seen;  // path prefixes visited, and "prefix + negated branch" flips already queued
  std::unordered_set<std::string> seenRepair;         // assumption repairs already attempted (at most one per run)
  std::set<std::pair<const Op *, int>> sites;
  std::map<std::string, FunctionTaintClass> classes;
  std::map<std::pair<std::string, std::string>, CallEdge> edgeMap;
  Interpreter interp(mod_);
  using Clock = std::chrono::steady_clock;
  auto since = [](Clock::time_point a) { return std::chrono::duration<double>(Clock::now() - a).count(); };

  struct Cached { SatResult r; std::vector<llvm::APInt> vals; std::vector<size_t> core; };
  std::unordered_map<std::string, Cached> qcache;
  // `blockers`, when given, is filled on Unsat with the PATH-CONDITION INDICES of a subset of the cone that already
  // rules the target out -- the branches whose other direction is the only way this check could ever fail. An empty
  // result is "no information" (not every backend reports cores), never "nothing is blocking it".
  // HLIR_TRACE_SOLVE (DESIGN.md §22.444): one line per solver query -- the query's identity (the same key the
  // cache uses, so it is independent of the host) and a hash of the answer. Two runs of the same command can be
  // diffed to find the FIRST query that answered differently, which is what separates "the search diverged" from
  // "the solver diverged".
  const bool traceSolve = getenv("HLIR_TRACE_SOLVE") != nullptr;
  uint64_t solveSeq = 0;
  auto solve = [&](const Cone &c, TermRef target, smt::Assignment &model,
                   std::vector<size_t> *blockers = nullptr) -> SatResult {
    std::string key = idKey(c.constraints, c.constraints.size()) + "|" + std::to_string(target->id);
    auto hit = qcache.find(key);
    if (hit != qcache.end()) {
      ++res.cacheHits;
      if (hit->second.r == SatResult::Sat)
        for (size_t i = 0; i < c.vars.size(); ++i) model[c.vars[i]->name] = hit->second.vals[i];
      if (hit->second.r == SatResult::Unknown) { res.complete = false; res.note = "solver returned unknown"; res.reason = "solver_unknown"; }
      if (blockers) *blockers = hit->second.core;
      return hit->second.r;
    }
    if (overBudget()) { res.complete = false; res.note = "time budget exhausted"; res.reason = "time_budget"; return SatResult::Unknown; }
    ++res.solverQueries;
    res.termsSolved += c.terms;
    auto tSolve = Clock::now();
    std::vector<TermRef> terms(c.constraints.begin(), c.constraints.end());
    terms.push_back(target);
    // no query may run past the wall-clock budget: its time limit is the smaller of the configured one and what is left
    auto limitMs = [&](unsigned want) -> unsigned {
      if (cfg.wallSeconds <= 0) return want;
      double left = cfg.wallSeconds - std::chrono::duration<double>(Clock::now() - t0).count();
      unsigned leftMs = left <= 0.05 ? 50u : static_cast<unsigned>(left * 1000);
      return want ? std::min(want, leftMs) : leftMs;
    };
    unsigned baseMs = cfg.fastTimeoutMs ? cfg.fastTimeoutMs : 10000;
    solver_.setTimeoutMs(limitMs(baseMs));
    auto tChk = Clock::now();
    SatResult r = solver_.checkAssuming(terms);
    res.secCheck += since(tChk);
    if (r == SatResult::Unknown && cfg.slowTimeoutMs && cfg.slowTimeoutMs > cfg.fastTimeoutMs) {
      ++res.escalations;
      solver_.endCheckAssuming();
      solver_.setTimeoutMs(limitMs(cfg.slowTimeoutMs));
      r = solver_.checkAssuming(terms);
    }
    Cached cached{r, {}, {}};
    if (r == SatResult::Sat) {
      cached.vals = solver_.values(c.vars);
      for (size_t i = 0; i < c.vars.size(); ++i) model[c.vars[i]->name] = cached.vals[i];
    } else if (r == SatResult::Unsat && blockers) {
      // Positions in `terms` are positions in c.constraints (the target was appended last, and is not a blocker).
      for (size_t pos : solver_.unsatCoreAssumptions())
        if (pos < c.idxs.size()) cached.core.push_back(c.idxs[pos]);
    }
    if (blockers) *blockers = cached.core;
    solver_.endCheckAssuming();
    res.secSolve += since(tSolve);
    if (traceSolve) {
      uint64_t h = 1469598103934665603ull;
      auto mix = [&](uint64_t x) { h ^= x; h *= 1099511628211ull; };
      for (auto &kv : model) { for (unsigned char ch : kv.first) mix(ch); mix(kv.second.getLimitedValue()); }
      fprintf(stderr, "[solve] #%llu cone=%zu tgt=%u key=%zu -> %s model=%016llx\n",
              static_cast<unsigned long long>(solveSeq++), c.constraints.size(), target->id,
              std::hash<std::string>{}(key), r == SatResult::Sat ? "sat" : r == SatResult::Unsat ? "unsat" : "unknown",
              static_cast<unsigned long long>(h));
    }
    if (r == SatResult::Unknown) { res.complete = false; res.note = "solver returned unknown"; res.reason = "solver_unknown"; }
    qcache.emplace(std::move(key), std::move(cached));
    return r;
  };

  // -------------------------------------------------------- solver-guided seeding (DESIGN.md §22.386)
  //
  // A seed decides only what the FIRST run's attacker bytes are. It adds no constraint, excludes no state and
  // weakens no verdict -- every later run's bytes still come from the solver. What it decides is WHERE THE
  // SEARCH STARTS, and for anything that parses text the gap between "all zeros" and "a string the parser is
  // willing to walk into" is the whole game.
  //
  // THE PREVIOUS IMPLEMENTATION mutated bytes at random over an alphabet mined from the program's constants.
  // It is gone, and the reason it had to go is structural rather than a matter of better operators. Measured on
  // c-ares CVE-2023-31130 (`inet_net_pton_ipv6`), 500 probes, HLIR_DEBUG_AUTOSEED:
  //
  //     candidates containing one ':'   11 / 500
  //     candidates containing "::"       1 / 500   -- and that one was the constant run of ':' from the
  //                                                   alphabet sweep; mutation produced none, ever.
  //
  // The parser rejects a lone leading ':' outright, so across the two-byte edit ".7/9" -> "::7/9" the fitness
  // reads 39 -> 2 -> 41 branch edges: a valley, not a slope. No single-byte hill climb crosses it, and the
  // 8-slot population that was supposed to guard against exactly this had no dedup, so it held 8 copies of one
  // string. Weighted sampling, insertion operators and a token dictionary would all be a mutational fuzzer
  // rebuilt inside a symbolic executor, guessing at something the executor can derive.
  //
  // IT CAN DERIVE IT. `if (*src == ':') if (*++src != ':') goto enoent;` is one branch pair, and flipping it IS
  // the constraint src[0]==':' /\ src[1]==':'. One query. So every candidate here is VALID BY CONSTRUCTION --
  // a model of a real path condition, not a string that survived a filter -- and no alphabet has to be guessed.
  //
  // An SMT solver does not maximise coverage; it answers satisfiability. "The input with the most coverage" is
  // therefore realised as a BEST-FIRST search over runs: each node is a run, its children are the runs obtained
  // by flipping one of its branches, and nodes are expanded highest-score-first.
  //
  // Nodes are ordered by NOVELTY -- how many branch edges this run covered that no earlier run did -- and only
  // then by total coverage. Both weaker orderings were built and measured on this target first:
  //
  //   greedy ascent     derived src[0]==':' at probe 18, scored it (e=2 against an incumbent e=31) and discarded
  //                     it, so it never asked the one further question (src[1]==':') that turns e=2 into e=41.
  //   best-first by     kept that node but sorted it last, and 499 probes of better-scoring nodes arrived ahead
  //   total coverage    of it. Neither run ever produced a single candidate containing "::".
  //
  // Total coverage starves the node that matters, because the node that matters is the one the parser has just
  // rejected: it is one branch into a new region and nothing else. Novelty ranks it by what is unexplored under
  // it rather than by what it has reached, so it floats above the large population of high-scoring nodes whose
  // children only re-cover known edges. Within a node, branches are flipped deepest-first, because in a parser
  // the late branches extend the path while the early ones truncate it.
  //
  // One honest cost: these are real solver queries, so a seeding query that returns `unknown` marks the result
  // incomplete exactly as any other would. That is the conservative direction (it can only weaken a verdict,
  // never strengthen one), and it is left in place deliberately.
  if (cfg.autoSeed && !cfg.labelSeeds.count(cfg.inputLabel)) {
    const bool traceSeed = getenv("HLIR_DEBUG_AUTOSEED") != nullptr;
    auto renderSeed = [](const std::vector<uint8_t> &v) {
      std::string s;
      char hx[5];
      for (uint8_t c : v) {
        if (!c) break;
        if (c >= 0x20 && c < 0x7f) { s += static_cast<char>(c); }
        else { snprintf(hx, sizeof hx, "\\x%02x", c); s += hx; }
      }
      return s;
    };
    struct SeedStep {
      uint64_t score = 0;
      size_t novelty = 0;  // branch edges this run covered that no earlier seeding run had; the primary rank
      std::shared_ptr<RunData> rd;
      std::vector<char> flippable;
      std::set<std::pair<const Op *, bool>> edges;
      std::vector<uint8_t> bytes;  // the attacker bytes of cfg.inputLabel, in creation order; for the report only
    };
    // Run one assignment and score it. Fitness is BRANCH EDGES first, blocks second, and only over ops that
    // carry a source location: a library model's body (strchr's 34 branches per call) is not progress through
    // the program, and counting it rewards going round a lookup table.
    auto evalSeed = [&](const std::map<std::string, llvm::APInt> &sd, SeedStep &out) {
      TaintDomain pd(tm_, sd, dcfg);
      TableEnv penv;
      Machine<TaintDomain> pm(pd, mod_, penv, rc);
      RunResult pr = pm.run(*f, {});
      pd.finish();
      // The second term counts distinct SOURCE LINES, not basic blocks. Blocks are too coarse, and the seedlabel
      // fixture shows exactly how: for `if (a || b || c || d) return -1;` the lowered form gives "gate failed at
      // the last byte" and "gate passed" the SAME number of blocks (9) and the SAME number of edges (4). Only the
      // lines differ -- {6,8,11} against {6,8,11,12,13} -- because the line set is what actually says which of the
      // program's text ran. Scored by blocks, "ABC" and "ABCD" tie and the gate-passing input loses on insertion
      // order; scored by lines it wins by two.
      std::set<std::pair<const std::string *, unsigned>> seenL;
      for (const Block *b : pr.blocksVisited)
        for (auto &bop : b->ops)
          if (bop->loc.valid()) seenL.insert({&bop->loc.file, bop->loc.line});
      std::set<std::pair<const Op *, bool>> seenE;
      for (auto &e : pr.branchesVisited)
        if (e.first->loc.valid()) seenE.insert(e);
      out.score = (static_cast<uint64_t>(seenE.size()) << 32) | static_cast<uint32_t>(seenL.size());
      out.edges = std::move(seenE);
      out.rd = std::make_shared<RunData>();
      for (auto &pc : pd.pcs()) {
        out.rd->pcTerms.push_back(pc.cond);
        out.rd->pcSites.push_back({pc.site, pc.dir});
        out.flippable.push_back(pc.flippable ? 1 : 0);
      }
      out.rd->assign = pd.varValues();
      out.rd->coneIdx = buildConeIndex(out.rd->pcTerms, varCache);
      for (auto &s : pd.sources()) {
        if (s.width != 8 || s.label != cfg.inputLabel) continue;
        auto it = out.rd->assign.find(s.name);
        out.bytes.push_back(it == out.rd->assign.end() ? 0 : static_cast<uint8_t>(it->second.getZExtValue()));
      }
    };
    SeedStep root;
    evalSeed(seed0, root);
    const uint64_t baseScore = root.score;
    unsigned probes = 1;
    res.autoSeedBaseline = static_cast<unsigned>(baseScore & 0xffffffffu);
    if (traceSeed)
      fprintf(stderr, "[autoseed] base  e=%llu L=%llu pcs=%zu\n", static_cast<unsigned long long>(baseScore >> 32),
              static_cast<unsigned long long>(baseScore & 0xffffffffu), root.rd->pcTerms.size());
    std::set<std::pair<const Op *, bool>> seedCovered;
    auto rank = [&](SeedStep &st) {
      st.novelty = 0;
      for (auto &e : st.edges)
        if (!seedCovered.count(e)) ++st.novelty;
      seedCovered.insert(st.edges.begin(), st.edges.end());
    };
    auto better = [](const SeedStep &a, const SeedStep &b) {
      if (a.novelty != b.novelty) return a.novelty > b.novelty;
      return a.score > b.score;
    };
    rank(root);
    SeedStep best = root;
    std::vector<SeedStep> pool;  // nodes not yet expanded, most novel first
    pool.push_back(std::move(root));
    std::set<std::vector<uint8_t>> seenBytes;  // an expansion that reproduces an input already run teaches nothing
    std::vector<SeedStep> kept;  // every candidate that reached somewhere new; the seed is a SET, not a winner
    constexpr size_t kSeedPool = 64;
    constexpr size_t kSeedHandover = 1;  // see the handover note below: each extra seed costs one run of the search
    while (!pool.empty() && probes < cfg.autoSeed && !overBudget()) {
      SeedStep node = std::move(pool.front());
      pool.erase(pool.begin());
      for (size_t k = node.rd->pcTerms.size(); k-- > 0;) {  // deepest branch of this run first
        if (probes >= cfg.autoSeed || overBudget()) break;
        if (!node.flippable[k]) continue;
        TermRef neg = tm_.mkNot(node.rd->pcTerms[k]);
        auto tC = std::chrono::steady_clock::now();
        Cone c = coneOf(node.rd->coneIdx, k, neg, varCache);
        res.secCone += since(tC);
        smt::Assignment model;
        if (solve(c, neg, model) != SatResult::Sat) continue;
        std::map<std::string, llvm::APInt> cand = node.rd->assign;
        for (auto &kv : model) cand[kv.first] = kv.second;
        SeedStep child;
        evalSeed(cand, child);
        ++probes;
        const bool dup = !seenBytes.insert(child.bytes).second;
        rank(child);
        if (traceSeed)
          fprintf(stderr, "[autoseed] #%-4u flip@%-4zu e=%-4llu L=%-4llu n=%-4zu %s \"%s\"\n", probes, k,
                  static_cast<unsigned long long>(child.score >> 32), static_cast<unsigned long long>(child.score & 0xffffffffu),
                  child.novelty, child.score > best.score ? "BEST" : dup ? "dup " : "    ", renderSeed(child.bytes).c_str());
        if (child.score > best.score) best = child;
        if (dup) continue;
        if (child.novelty) kept.push_back(child);
        pool.push_back(std::move(child));
        std::sort(pool.begin(), pool.end(), better);
        if (pool.size() > kSeedPool) pool.resize(kSeedPool);  // bounded: the tail is what the budget was never going to reach
      }
    }
    SeedStep &cur = best;
    res.autoSeedProbes = probes;
    if (traceSeed)
      fprintf(stderr, "[autoseed] final e=%llu L=%llu (base e=%llu L=%llu) \"%s\"\n",
              static_cast<unsigned long long>(cur.score >> 32), static_cast<unsigned long long>(cur.score & 0xffffffffu),
              static_cast<unsigned long long>(baseScore >> 32), static_cast<unsigned long long>(baseScore & 0xffffffffu),
              renderSeed(cur.bytes).c_str());
    // THE SEED IS A SET, NOT A WINNER. Maximum coverage is the wrong thing to hand a search on its own, and the
    // seedvalley fixture is the proof: a broad dead end ("3442", 9 edges / 176 lines) outscores the narrow entrance
    // into the guarded region ("##z", 3 edges / 73 lines) that the defect is actually behind. Picking the single
    // best input discards the one that mattered -- which is the same mistake, one level up, that greedy ascent
    // made inside the search. So every candidate that reached somewhere no earlier one had is handed over, most
    // novel first; the frontier already consumes several starting points, and the cost of a seed that leads
    // nowhere is one run.
    std::sort(kept.begin(), kept.end(), better);
    std::vector<const SeedStep *> hand;
    for (const SeedStep &k : kept) {
      if (hand.size() >= kSeedHandover) break;
      hand.push_back(&k);
    }
    // THE HANDOVER IS BOUNDED AT ONE, and the budget is why. A seed does not add runs, it SPENDS them: every
    // candidate handed over displaces one flip the search would otherwise have taken, and the measurements say
    // the search's own frontier is the better spender. On the seedvalley fixture the zero-seed search finds the
    // defect in 8 runs; handing over 8 seeds pushed that to 32, and it did so whether the seeds replaced the zero
    // start or merely queued ahead of its flips. So exactly one seed goes first -- the best input the descent
    // found -- the zero start follows immediately behind it, and the whole feature costs one run.
    if (!hand.empty() || cur.score > baseScore) {
      work.clear();  // rebuilt below as: the seed, then the zero start, then nothing else
      // A candidate is an ASSIGNMENT, not a byte string: it fixes every attacker variable the run created, which
      // is strictly more than labelSeeds can express, and it is exactly the form the frontier already consumes.
      bool haveBest = false;
      for (const SeedStep *k : hand) {
        WorkItem wk;
        wk.seed = k->rd->assign;
        work.emplace(WorkKey{0, 1, 0, 0, workSeq++}, std::move(wk));
        haveBest |= k->bytes == cur.bytes;
      }
      if (!haveBest && cur.score > baseScore) {
        WorkItem wb;
        wb.seed = cur.rd->assign;
        work.emplace(WorkKey{0, 1, 0, 0, workSeq++}, std::move(wb));
      }
      { WorkItem wz; wz.seed = seed0; work.emplace(WorkKey{0, 1, 0, 0, workSeq++}, std::move(wz)); }  // zero start, right behind
      res.autoSeedBytes = cur.bytes;
      res.autoSeedBlocks = static_cast<unsigned>(cur.score & 0xffffffffu);
      res.autoSeedKept = static_cast<unsigned>(work.size());
      if (traceSeed)
        for (const SeedStep *k : hand)
          fprintf(stderr, "[autoseed] hand  e=%-4llu L=%-4llu n=%-4zu \"%s\"\n",
                  static_cast<unsigned long long>(k->score >> 32), static_cast<unsigned long long>(k->score & 0xffffffffu),
                  k->novelty, renderSeed(k->bytes).c_str());
    }
  }

  for (;;) {
    if (work.empty()) break;
    if (res.runs.size() >= cfg.maxRuns) { res.complete = false; res.note = "run limit reached"; res.reason = "run_limit"; break; }
    if (overBudget()) { res.complete = false; res.note = "time budget exhausted"; res.reason = "time_budget"; break; }
    std::map<std::string, llvm::APInt> seed;
    bool haveSeed = false;
    while (!work.empty() && !haveSeed) {
      if (overBudget()) break;
      WorkItem it = std::move(work.begin()->second);
      work.erase(work.begin());
      if (!it.isFlip) { seed = std::move(it.seed); haveSeed = true; break; }
      TermRef neg = tm_.mkNot(it.run->pcTerms[it.idx]);
      auto tC = Clock::now();
      Cone c = coneOf(it.run->coneIdx, it.idx, neg, varCache);
      // Drop the engine's own length concretisations from a FLIP query. The result is a starting point that is
      // then RUN, exactly like the relaxation below: the next run concretises its own lengths, so nothing here
      // is reported on the strength of this cone. Left in, the equality `len == <this run's value>` pins every
      // attacker byte feeding that length and every flip behind it comes back UNSAT (DESIGN.md Sec.22.467).
      if (it.run->anyConcrete) {
        Cone fc;
        fc.vars = c.vars;
        fc.terms = c.terms;
        for (size_t ci = 0; ci < c.constraints.size(); ++ci) {
          size_t at = c.idxs[ci];
          if (at < it.run->pcConcrete.size() && it.run->pcConcrete[at]) continue;
          fc.constraints.push_back(c.constraints[ci]);
          fc.idxs.push_back(at);
        }
        if (fc.constraints.size() != c.constraints.size()) { concDropped += c.constraints.size() - fc.constraints.size(); c = std::move(fc); }
      }
      res.secCone += since(tC);
      smt::Assignment model;
      if (solve(c, neg, model) != SatResult::Sat) {
        ++flipsUnsat;
        // Infeasible on this prefix, so this edge is not a budget problem. Recorded per EDGE, which is what a
        // coverage question asks about (`--dump-branches`).
        if (it.idx < it.run->pcSites.size() && it.run->pcSites[it.idx].first)
          res.flipUnsat.insert({it.run->pcSites[it.idx].first, !it.run->pcSites[it.idx].second});
        continue;
      }
      seed = it.run->assign;
      for (auto &kv : model) seed[kv.first] = kv.second;
      ++flipsSolved;
      haveSeed = true;
    }
    if (!haveSeed) {
      if (overBudget() && !work.empty()) { res.complete = false; res.note = "time budget exhausted"; res.reason = "time_budget"; }
      break;
    }

    TaintDomain dom(tm_, seed, dcfg);
    TableEnv env;
    Machine<TaintDomain> m(dom, mod_, env, rc);
    auto tRun = Clock::now();
    RunResult rr = m.run(*f, {});
    res.secInterp += since(tRun);
    for (auto &l : dom.labels()) res.labelsSeen.insert(l);
    res.setupRegionSecRestore += rr.secSetupRestore;
    res.setupRegionAllocs += rr.setupAllocsForced;
    res.maxDepth = std::max(res.maxDepth, rr.maxDepth);
    for (auto &kv : rr.nondetOrigins) res.nondetOrigins.insert(kv);
    for (auto &kv : rr.checksByFn)
      if (kv.first) {
        auto &a = checksByFn[kv.first->name];
        a.first += kv.second.reached;
        a.second += kv.second.queried;
      }
    for (auto &kv : rr.checks) {
      CheckStat &a = res.checks[kv.first];
      a.reached += kv.second.reached; a.decidedConcretely += kv.second.decidedConcretely; a.queried += kv.second.queried;
    }
    res.taintReach.memoryIndex |= rr.taintReach.memoryIndex;
    res.taintReach.loopBound   |= rr.taintReach.loopBound;
    res.taintReach.allocSize   |= rr.taintReach.allocSize;
    res.taintReach.sink        |= rr.taintReach.sink;
    res.setupInfeasible        |= rr.setupInfeasible;
    for (auto &kv : rr.opaqueCalls) res.opaqueCalls[kv.first] += kv.second;
    for (auto &kv : rr.reads) res.reads[kv.first].insert(kv.second.begin(), kv.second.end());
    for (auto &kv : rr.unknownWrites) res.unknownWrites[kv.first] += kv.second;
    for (auto &kv : rr.objKeys) {
      auto ins = res.objKeys.emplace(kv.first, kv.second);
      if (!ins.second && ins.first->second != kv.second) res.readsIncomplete = true;  // see RunResult::objKeys
    }
    res.readsIncomplete |= rr.readsIncomplete;
    res.globalsPromoted = std::max(res.globalsPromoted, rr.globalsPromoted);
    res.frontierFieldReads += rr.frontierFieldReads;
    res.frontierBoundsApplied += rr.frontierBoundsApplied;
    res.frontierBoundsMissing += rr.frontierBoundsMissing;
    res.frontierBoundsInfeasible += rr.frontierBoundsInfeasible;
    dom.finish();
    unsigned runIdx = static_cast<unsigned>(res.runs.size());

    TaintRun tr;
    tr.status = rr.status;
    tr.seed = seed;
    tr.slice.steps = rr.steps;
    tr.slice.taintedOps = dom.taintedOps();
    tr.slice.pcs = dom.pcs().size();
    for (auto &p : dom.pcs()) tr.slice.flippableBranches += p.flippable;
    tr.slice.queries = dom.queries().size();
    tr.slice.sources = dom.sources().size();
    tr.slice.envFacts = dom.envFacts().size();
    tr.slice.concretizedPointers = dom.concretizedPointers();
    tr.slice.selectedAddresses = dom.selectedAddresses();
    for (auto &e : dom.envFacts()) {
      EnvFact ef;
      ef.value = e.value;
      ef.op = e.op ? "core." + std::string(opInfo(e.op->opc).name) : "";
      ef.function = e.function;
      if (e.op) ef.loc = e.op->loc;
      tr.envFacts.push_back(std::move(ef));
    }
    for (auto &kv : dom.functionClasses()) {
      FunctionTaintClass &c = classes[kv.first];
      c.function = kv.first;
      c.calls += kv.second.calls; c.inert += kv.second.inert; c.observer += kv.second.observer;
      c.transformer += kv.second.transformer; c.source += kv.second.source; c.sanitizer += kv.second.sanitizer;
    }
    for (auto &kv : dom.callEdges()) {
      CallEdge &e = edgeMap[kv.first];
      e.caller = kv.first.first; e.callee = kv.first.second;
      e.calls += kv.second.calls;
      e.tainted = e.tainted || kv.second.tainted;
    }
    res.runs.push_back(tr);
    res.blocksVisited.insert(rr.blocksVisited.begin(), rr.blocksVisited.end());
    res.branchesVisited.insert(rr.branchesVisited.begin(), rr.branchesVisited.end());
    res.globalGatedSites.insert(rr.globalGatedSites.begin(), rr.globalGatedSites.end());
    for (auto &kv : rr.globalGatedBy) res.globalGatedBy.emplace(kv.first, kv.second);
    if (rr.status == RunStatus::Returned) ++res.runsReturned;
    if (rr.terminated) {
      ++res.runsTerminated;
      bool merged = false;
      for (auto &t : res.terminations)
        if (t.function == rr.terminatedIn && t.by == rr.terminatedBy && t.stack == rr.terminatedStack && t.loc.line == rr.terminatedAt.line && t.loc.file == rr.terminatedAt.file) { ++t.runs; merged = true; break; }
      if (!merged) {
        TerminationSite ts{rr.terminatedIn, rr.terminatedBy, rr.terminatedStack, rr.terminatedAt, 1, {}};
        for (auto &kv : dom.varValues())
          if (kv.first.rfind("in.", 0) == 0) ts.inputs.emplace(kv.first, kv.second);
        res.terminations.push_back(std::move(ts));
      }
    }

    if (rr.status == RunStatus::LoopBound) ++res.loopCut;  // the path up to the cut still gives constraints to flip
    switch (rr.status) {
      case RunStatus::Unsupported: case RunStatus::StepLimit: case RunStatus::DepthLimit:
        res.complete = false;
        res.note = rr.message;
        res.reason = rr.status == RunStatus::StepLimit ? (rr.message.find("time budget") != std::string::npos ? "time_budget" : "step_limit") : rr.status == RunStatus::DepthLimit ? "depth_limit" : "unsupported";
        break;
      default: break;
    }
    // A run that ends because the program ends (noreturn call) is a real execution: its branches are flipped like any other run's.
    if (rr.status == RunStatus::Infeasible && !rr.terminated) {
      // The seed violates an assumption. If that assumption talks about attacker input (a precondition on the content of a
      // parameter object), a seed that satisfies it exists unless the preconditions contradict the path: solve for one.
      if (dom.repair() && !overBudget()) {
        std::vector<TermRef> pcTermsR;
        for (auto &pc : dom.pcs()) pcTermsR.push_back(pc.cond);
        ConeIndex ridx = buildConeIndex(pcTermsR, varCache);
        TermRef want = dom.repair()->cond;
        if (seenRepair.insert(std::to_string(want->id) + ":" + idKey(pcTermsR, std::min(dom.repair()->pcCount, pcTermsR.size()))).second) {
          Cone c = coneOf(ridx, std::min(dom.repair()->pcCount, pcTermsR.size()), want, varCache);
          smt::Assignment model;
          if (solve(c, want, model) == SatResult::Sat) {
            std::map<std::string, llvm::APInt> next = dom.varValues();
            for (auto &kv : model) next[kv.first] = kv.second;
            WorkItem wi;
            wi.seed = std::move(next);
            work.emplace(WorkKey{0, 1, 0, 0, workSeq++}, std::move(wi));
          }
        }
      }
      continue;  // not a legal execution
    }

    // The full assignment this run used: witnesses and next seeds are overlays of solver models on it.
    std::map<std::string, llvm::APInt> assign = dom.varValues();
    auto addFinding = [&](const Finding &fd, const smt::Assignment &model) {
      if (!sites.insert({fd.site, fd.ub ? static_cast<int>(fd.ub->kind) : -1}).second) return;
      SymFinding sf;
      sf.status = fd.status;
      sf.ub = fd.ub;
      sf.message = fd.message;
      sf.loc = fd.loc;
      sf.frontierOnly = fd.frontierOnly;
      sf.cmpOnlyPtr = fd.cmpOnlyPtr;
      sf.inPrologue = fd.inPrologue;
      sf.path = runIdx;
      auto valueOf = [&](const std::string &n, const llvm::APInt &dflt) {
        auto it = model.find(n);
        return it == model.end() ? dflt : it->second.zextOrTrunc(dflt.getBitWidth());
      };
      for (auto &nd : dom.nondetOrder()) {
        sf.nondets.push_back(valueOf(nd.name, nd.value));
        sf.nondetNames.push_back(nd.name);
      }
      for (auto &kv : assign)
        if (kv.first.rfind("in.", 0) == 0) sf.inputs.emplace(kv.first, valueOf(kv.first, kv.second));
      if (sf.ub && ubKindIsWarning(sf.ub->kind)) {
        // A data-flow warning (DoS loop / unbounded index): the concolic run (loop) or a solved query (index)
        // already exhibits it on a concrete assignment -- there is no separate UB to reproduce by replay.
        sf.confirmed = true;
        res.findings.push_back(std::move(sf));
        return;
      }
      if (cfg.replay) {
        SeqEnv renv(sf.nondets, sf.inputs);
        RunConfig rrc = rc;
        rrc.deadline = std::chrono::steady_clock::time_point::max();  // confirming a finding must not be cut short by the budget that found it
        bool sinkFlow = sf.ub && sf.ub->kind == UBKind::TaintedSink;
        rrc.trace = sinkFlow;  // a data-flow finding is confirmed by the replay reaching the sink call
        auto tRep = Clock::now();
        RunResult rep = interp.run(entry, {}, renv, rrc);
        res.secReplay += since(tRep);
        if (sinkFlow) {
          std::string want = "sink " + sf.ub->origin.substr(sf.ub->origin.find(':') + 1) + " ";
          bool reached = false;
          for (auto &ev : rep.trace) reached |= ev.kind == TraceEvent::Observable && ev.text.rfind(want, 0) == 0;
          sf.confirmed = reached;
        } else {
          // A finding the engine deliberately walks past (compare-only pointer, prologue) can never END a run in
          // UB, so "the replay stopped here with this kind" is not the only shape of evidence that counts: the
          // run recording that it walked past THIS site is the same fact (DESIGN.md §22.418).
          const std::string contKey = sf.ub ? std::string(ubKindName(sf.ub->kind)) + "@" + sf.loc.file + ":" +
                                                  std::to_string(sf.loc.line)
                                            : std::string();
          sf.confirmed = sf.ub ? ((rep.status == RunStatus::UB && rep.ub && rep.ub->kind == sf.ub->kind) ||
                                  rep.ubContinued.count(contKey) != 0)
                               : rep.status == RunStatus::AssertFailed;
        }
        if (!*sf.confirmed) {
          // The kind alone is not diagnosable: "replay hit a different UB: ptr_arith_oob" on a printer that has
          // a dozen pointer bumps says nothing about WHICH one stopped the replay, and that is the only thing a
          // reader needs in order to tell a genuine earlier defect from a benign idiom (DESIGN.md §22.418).
          sf.replayNote = rep.status == RunStatus::UB && rep.ub
                              ? std::string("replay hit a different UB: ") + ubKindName(rep.ub->kind) +
                                    (rep.ub->loc.valid() ? " at " + rep.ub->loc.file.substr(rep.ub->loc.file.find_last_of('/') + 1) + ":" +
                                                               std::to_string(rep.ub->loc.line)
                                                         : std::string(" in @") + rep.ub->function) +
                                    (rep.ub->op.empty() ? "" : " (" + rep.ub->op + ")")
                              // ... and when it ended on something other than UB, `status` alone is just as blind:
                              // "unsupported" does not say WHICH construct, and that is the whole diagnosis.
                              : std::string("replay ended with status ") + runStatusName(rep.status) +
                                    (rep.message.empty() ? "" : ": " + rep.message) +
                                    (rep.messageLoc.valid()
                                         ? " at " + rep.messageLoc.file.substr(rep.messageLoc.file.find_last_of('/') + 1) +
                                               ":" + std::to_string(rep.messageLoc.line)
                                         : std::string());
        }
      }
      res.findings.push_back(std::move(sf));
    };

    for (auto &fd : dom.concreteFindings()) addFinding(fd, {});

    std::vector<TermRef> pcTerms;
    for (auto &p : dom.pcs()) pcTerms.push_back(p.cond);

    auto rd = std::make_shared<RunData>();  // kept alive by the frontier items that flip a branch of this run
    rd->pcTerms = pcTerms;
    for (auto &p : dom.pcs()) {
      rd->pcSites.push_back({p.site, p.dir});
      rd->pcConcrete.push_back(p.concretisation ? 1 : 0);
      rd->anyConcrete |= p.concretisation;
      if (p.flippable && p.site) res.branchSymbolic.insert(p.site);
    }
    rd->assign = assign;
    auto tCone = Clock::now();
    rd->coneIdx = buildConeIndex(rd->pcTerms, varCache);
    res.secCone += since(tCone);
    ConeIndex &coneIdx = rd->coneIdx;
    // Path conditions that an unsat core blamed for a REACHED-but-refuted safety check. Flipping one of these is
    // the only way that check can ever fail, so they go to the head of the frontier (WorkKey::blocker).
    std::set<size_t> blockingPcs;  // this run's indices (diagnostics); the lasting form is blockingSites
    for (auto &q : dom.queries()) {
      if (overBudget()) { res.complete = false; res.note = "time budget exhausted"; res.reason = "time_budget"; break; }
      auto tC1 = Clock::now();
      Cone c = coneOf(coneIdx, q.pcCount, q.bad, varCache);
      res.secCone += since(tC1);
      smt::Assignment model;
      std::vector<size_t> blk;
      SatResult qr = solve(c, q.bad, model, &blk);
      bool sat = qr == SatResult::Sat;
      if (!sat) blockingPcs.insert(blk.begin(), blk.end());
      // RELAXATION. Re-ranking a branch is a walk TOWARDS the defect, and by the time a run reaches an access and
      // learns which branch rules it out, that branch's flip has usually been taken already -- measured: 14000 runs
      // produced only 90 re-rankings, and detection did not move. So ask the question directly instead: drop the
      // constraints the core blamed and re-solve `bad` against what is left. A model of that is an input under
      // which this very access DOES go out of bounds, with the branches that prevented it released. It is not a
      // proof -- the released branches are no longer pinned, so the input may walk a different path -- which is
      // exactly why it is queued as a starting point and then RUN, not reported. The engine's own checks decide.
      if (!sat && !blk.empty() && qr == SatResult::Unsat && relax && !overBudget()) {
        std::set<size_t> drop(blk.begin(), blk.end());
        Cone rc2;
        rc2.vars = c.vars;
        rc2.terms = c.terms;
        for (size_t ci = 0; ci < c.constraints.size(); ++ci)
          if (!drop.count(c.idxs[ci])) { rc2.constraints.push_back(c.constraints[ci]); rc2.idxs.push_back(c.idxs[ci]); }
        smt::Assignment rmodel;
        ++relaxTried;
        if (solve(rc2, q.bad, rmodel) == SatResult::Sat) {
          std::map<std::string, llvm::APInt> rseed = assign;
          for (auto &kv : rmodel) rseed[kv.first] = kv.second;
          WorkItem ri;
          ri.seed = std::move(rseed);
          work.emplace(WorkKey{1, 1, 0, 0, workSeq++}, std::move(ri));  // blocker tier: this is a derived candidate
          ++relaxQueued;
        }
      }
      if (getenv("HLIR_DEBUG_CORE")) {
        size_t flip = 0;
        std::string where;
        for (size_t bi : blk)
          if (bi < dom.pcs().size()) {
            if (dom.pcs()[bi].flippable) ++flip;
            if (where.size() < 60 && dom.pcs()[bi].site)
              where += (dom.pcs()[bi].flippable ? " F@" : " x@") + std::to_string(dom.pcs()[bi].site->loc.line);
            else if (where.size() < 60)
              where += dom.pcs()[bi].flippable ? " F@?" : " x@?";
          }
        fprintf(stderr, "[core] %s at=%u cone=%zu core=%zu flippable=%zu%s\n",
                qr == SatResult::Sat ? "sat  " : qr == SatResult::Unsat ? "unsat" : "unk  ",
                q.finding.loc.line, c.constraints.size(), blk.size(), flip, where.c_str());
      }
      if (q.finding.ub) { CheckStat &cs = res.checks[static_cast<int>(q.finding.ub->kind)]; if (sat) ++cs.sat; else ++cs.unsat; }
      if (sat) addFinding(q.finding, model);
    }

    // Index-warning candidates (tainted value used as a memory index): emit a warning when the index can still
    // exceed the threshold under the path constraints -- i.e. no constant upper bound is in force. Unlike queries()
    // these add no path constraint, so they do not steer the rest of the exploration.
    for (auto &q : dom.warnQueries()) {
      if (overBudget()) { res.complete = false; res.note = "time budget exhausted"; res.reason = "time_budget"; break; }
      Cone c = coneOf(coneIdx, q.pcCount, q.bad, varCache);
      smt::Assignment model;
      if (solve(c, q.bad, model) == SatResult::Sat) addFinding(q.finding, model);
    }

    // Mark every prefix of this run's own path as visited, then flip each tainted branch not yet tried.
    for (auto &p : dom.pcs())
      if (p.flippable && p.site) covered.insert({p.site, p.dir});
    std::vector<PathHash> prefixHash(pcTerms.size() + 1);
    for (size_t i = 0; i < pcTerms.size(); ++i) prefixHash[i + 1] = prefixHash[i].add(pcTerms[i]->id);
    for (size_t i = 0; i < pcTerms.size(); ++i)
      if (dom.pcs()[i].flippable) seen.insert(prefixHash[i + 1]);
    for (size_t i = 0; i < pcTerms.size(); ++i) {
      if (!dom.pcs()[i].flippable) continue;
      ++pcsByFn[dom.pcs()[i].function];
      // A model body carries no source location (its ops come from models/libc.core, not from a .c file). That is
      // the line between "a library function whose SPECIFICATION may have a closed form" and "the program under
      // test, whose control flow is the thing being analysed and must not be summarised away".
      if (!dom.pcs()[i].site || !dom.pcs()[i].site->loc.valid()) ++noLocByFn[dom.pcs()[i].function];
      TermRef neg = tm_.mkNot(pcTerms[i]);
      const PathHash fh = prefixHash[i].add(neg->id);
      const bool blocker = guided && useBlocker && blockingPcs.count(i) != 0;
      if (!seen.insert(fh).second) {
        ++flipsDeduped;
        // Diagnostic (HLIR_DEBUG_FRONTIER): a flip dropped by the prefix dedup whose direction NO run has
        // executed. That pair is invisible in the summary -- it never reaches `flipOpen` or `flipUnsat`, so
        // Pipeline.cpp's classifier falls through to its catch-all and prints it as `open`, the label reserved
        // for "the budget ran out". It did not; the flip was never queued. Printing the site is what separates
        // "we ran out of time" from "we never asked", which the branch dump alone cannot.
        if (dbgDedup && dom.pcs()[i].site && dom.pcs()[i].site->loc.valid() &&
            !covered.count({dom.pcs()[i].site, !dom.pcs()[i].dir}))
          fprintf(stderr, "[dedup] %s:%u:%u dir=%d fn=%s hash=%llu\n", dom.pcs()[i].site->loc.file.c_str(),
                  dom.pcs()[i].site->loc.line, dom.pcs()[i].site->loc.col, !dom.pcs()[i].dir ? 1 : 0,
                  dom.pcs()[i].function.c_str(), (unsigned long long)fh.a);
        // Already queued -- but this run has just PROVED that flipping it is the only way a safety check it
        // reached can fail, which the run that queued it did not know. Move it to the head of the frontier
        // instead of dropping the knowledge with the duplicate.
        if (blocker) {
          auto at = queuedAt.find(fh);
          if (at != queuedAt.end() && at->second.blocker == 0) {
            auto it = work.find(at->second);
            if (it != work.end()) {
              WorkKey nk = at->second;
              nk.blocker = 1;
              WorkItem moved = std::move(it->second);
              work.erase(it);
              work.emplace(nk, std::move(moved));
              at->second = nk;
              ++blockerFlips;
            }
          }
        }
        continue;
      }
      bool fresh = !guided || (dom.pcs()[i].site && !covered.count({dom.pcs()[i].site, !dom.pcs()[i].dir}));
      WorkItem wi;
      wi.run = rd;
      wi.idx = i;
      wi.isFlip = true;
      // TWO SEARCH TIERS WERE BUILT HERE AND BOTH WERE REMOVED BY THEIR OWN MEASUREMENTS (Sec.22.472):
      //
      //   `loopcont` -- prefer the flip that keeps a tainted loop going, as the only lever for defects that
      //     never pose a solver question. On libtiff CVE-2018-8905 it changed nothing (oob_write still
      //     queried 0 times) and on libjpeg CVE-2013-6630 it made things WORSE: the budget went into an
      //     earlier marker loop and get_dht stopped being entered at all, turning a valid measurement into
      //     a vacuous run. The premise was wrong -- that defect needs a structural state of the LZW code
      //     table, not more iterations, and `tainted_loop_bound` marks the decode loop, not the one that
      //     builds the table.
      //   `noquery` -- demote flips in a function whose checks are reached in bulk and never queried. It
      //     demoted @pick (program code) and pushed the budget into @strstr (a model body): backwards.
      //
      // What is still true is the observation that produced them: a defect whose every access has a
      // concrete address never enters the unsat core of a refuted check, so `blocker` -- the only
      // goal-directed tier -- cannot see it. Closing that needs induction-variable analysis and a check on
      // the loop's EXTREME address, not a reordering of the frontier.
      WorkKey k{blocker ? 1 : 0, fresh ? 1 : 0,
                barrenFlip(dom.pcs()[i].site, dom.pcs()[i].dir),
                distOf(dom.pcs()[i].function), workSeq++};
      work.emplace(k, std::move(wi));
      queuedAt[fh] = k;
      if (blocker) ++blockerFlips;
      ++flipsQueued;
      ++flipsByFn[dom.pcs()[i].function];
      // The other half of the [dedup] diagnostic: a flip that WAS queued, for a direction no run has executed.
      // Together the two lines say which of the three fates a missing direction met -- queued (and then either
      // solved, left in the frontier, or dropped), deduped away, or never generated at all because its branch
      // never entered `pcs()` as flippable. Only the last is invisible everywhere else.
      if (dbgDedup && dom.pcs()[i].site && dom.pcs()[i].site->loc.valid() &&
          !covered.count({dom.pcs()[i].site, !dom.pcs()[i].dir}))
        fprintf(stderr, "[queue] %s:%u:%u dir=%d fn=%s\n", dom.pcs()[i].site->loc.file.c_str(),
                dom.pcs()[i].site->loc.line, dom.pcs()[i].site->loc.col, !dom.pcs()[i].dir ? 1 : 0,
                dom.pcs()[i].function.c_str());
    }
    frontierPeak = std::max(frontierPeak, work.size());
    while (work.size() > kMaxFrontier) { work.erase(std::prev(work.end())); ++frontierDropped; }  // the least promising flips are dropped
  }
  // MEASUREMENT FIRST (the §22.392 order): before a "no check down there" tier can be put in WorkKey, the share of
  // edges it would actually demote has to be known. Off unless asked for -- it is a whole-module static pass.
  // Whatever is still queued when the loop ends is the part of the gap more budget could have closed.
  for (auto &kv : work)
    if (kv.second.isFlip && kv.second.run && kv.second.idx < kv.second.run->pcSites.size() &&
        kv.second.run->pcSites[kv.second.idx].first)
      res.flipOpen.insert(
          {kv.second.run->pcSites[kv.second.idx].first, !kv.second.run->pcSites[kv.second.idx].second});
  // What the declared setup region actually bought (DESIGN.md §22.438).
  res.setupRegionSeen = setupCache.state != SetupCache::State::Empty || setupCache.capturedOps > 0;
  res.setupRegionReused = setupCache.state == SetupCache::State::Valid;
  res.setupRegionRefusal = setupCache.refusal;
  res.setupRegionOps = setupCache.capturedOps;
  res.setupRegionSkips = setupCache.skips;
  res.setupRegionObjects = setupCache.objects;
  res.setupRegionSymbolic = setupCache.symbolicCells + setupCache.symbolicRegs;
  if (getenv("HLIR_DEBUG_BARREN")) {
    BarrenInfo bi = computeBarrenEdges(mod_);
    fprintf(stderr, "[barren] edges=%zu barren=%zu (%.1f%%) empty_region=%zu unknown_callee=%zu\n",
            bi.edgesTotal, bi.edgesBarren, bi.edgesTotal ? 100.0 * bi.edgesBarren / bi.edgesTotal : 0.0,
            bi.edgesEmpty, bi.edgesUnknown);
  }
  if (getenv("HLIR_DEBUG_FRONTIER"))
    fprintf(stderr, "[frontier] queued=%zu deduped=%zu unsat=%zu dropped=%zu peak=%zu left=%zu runs=%zu blockers=%zu relax=%zu/%zu\n",
            flipsQueued, flipsDeduped, flipsUnsat, frontierDropped, frontierPeak, work.size(), res.runs.size(), blockerFlips, relaxQueued, relaxTried);
  if (getenv("HLIR_DEBUG_FRONTIER"))
    fprintf(stderr, "[frontier] concretisation constraints dropped from flip queries: %zu\n", concDropped);
  // Rank where the search budget went (§22.392). Computed unconditionally: `pcsByFn` / `flipsByFn` were already
  // being summed on every run, so this costs a sort of a map that is at most one entry per function. What used to
  // depend on someone setting HLIR_DEBUG_FRONTIER was never the measurement -- only the decision to look at it.
  // The search's own yield, reported unconditionally for the same reason: these numbers decided §22.467 and
  // were visible only to someone who already suspected something (TaintResult::flipsQueued).
  res.flipsQueued = flipsQueued;
  res.flipsSolved = flipsSolved;
  res.flipsUnsat = flipsUnsat;
  res.flipsDeduped = flipsDeduped;
  res.flipsConcDropped = concDropped;
  {
    for (auto &kv : pcsByFn) res.flippablePcsTotal += kv.second;
    for (auto &kv : pcsByFn) {
      FrontierSite s;
      s.function = kv.first;
      s.flippablePcs = kv.second;
      auto q = flipsByFn.find(kv.first);
      s.queued = q == flipsByFn.end() ? 0 : q->second;
      auto c = classes.find(kv.first);
      s.calls = c == classes.end() ? 0 : c->second.calls;
      s.share = res.flippablePcsTotal ? static_cast<double>(s.flippablePcs) / static_cast<double>(res.flippablePcsTotal) : 0.0;
      s.perCall = s.calls ? static_cast<double>(s.flippablePcs) / static_cast<double>(s.calls) : 0.0;
      auto nl = noLocByFn.find(kv.first);
      s.library = s.flippablePcs && nl != noLocByFn.end() && nl->second == s.flippablePcs;
      // Three tests, and dropping any one of them was measured to be wrong.
      //
      // `library` is the one that is not a heuristic: only a function with NO source location in any of its
      // branches is a model body, and only a model body may be replaced by a closed form. Summarising the program
      // under test would change what is being analysed, not how it is searched. Without this test the profile
      // flags the ENTRY -- measured on c-ares inet_net_pton_ipv6, which after the strchr fold owns 77% of the
      // frontier at 14.7 flips per call. That is the state the fold was FOR, reported as a defect.
      //
      // `share` keeps the list short: every small helper with a loop passes perCall on its own.
      //
      // `perCall` is the summarization signal: a single call costing many independent decisions is one logical
      // choice spelled as N sequential ones. @strchr on a 16-byte table measured 10.7 here (34 is its worst case,
      // when the needle misses and the whole table is walked).
      constexpr double kMinShare = 0.25, kMinPerCall = 4.0;
      s.foldCandidate = s.library && s.share >= kMinShare && s.perCall >= kMinPerCall;
      auto ck = checksByFn.find(s.function);
      if (ck != checksByFn.end()) { s.checksReached = ck->second.first; s.checksQueried = ck->second.second; }
      res.frontier.push_back(std::move(s));
    }
    std::sort(res.frontier.begin(), res.frontier.end(), [](const FrontierSite &a, const FrontierSite &b) {
      if (a.flippablePcs != b.flippablePcs) return a.flippablePcs > b.flippablePcs;
      return a.function < b.function;  // ties by name: the report has to be reproducible
    });
    if (res.frontier.size() > 16) res.frontier.resize(16);
  }
  if (getenv("HLIR_DEBUG_FRONTIER"))
    for (auto &s : res.frontier)
      fprintf(stderr, "[flips] %-28s flippable_pcs=%llu queued=%llu calls=%llu per_call=%.1f share=%.0f%%%s\n", s.function.c_str(),
              static_cast<unsigned long long>(s.flippablePcs), static_cast<unsigned long long>(s.queued),
              static_cast<unsigned long long>(s.calls), s.perCall, 100.0 * s.share, s.foldCandidate ? "  FOLD?" : "");
  res.branchesCovered = static_cast<unsigned>(covered.size());
  if (!work.empty() && res.runs.size() >= cfg.maxRuns) { res.complete = false; res.note = "run limit reached"; res.reason = "run_limit"; }
  // Discarding frontier items is a DECISION TO STOP EXPLORING, not a discovery that there is nothing left to
  // explore -- and the two leave the loop through the same `work.empty()` break (DESIGN.md §22.383). Until now
  // nothing distinguished them, so an entry whose search was culled came back `safe_under_assumptions` with an
  // empty `incomplete` list: "I gave up on most of the search" reported as "I found nothing". Measured on c-ares
  // CVE-2023-31130 (a real stack-underflow write the engine detects when handed the input): 951473 of 1129860
  // queued flips discarded, frontier emptied after 84055 of an allowed 200000 runs, verdict `safe`.
  if (res.complete && frontierDropped) {
    res.complete = false;
    res.reason = "frontier_dropped";
    res.note = std::to_string(frontierDropped) + " search branch(es) were discarded when the frontier exceeded " +
               std::to_string(kMaxFrontier) + " items (peak " + std::to_string(frontierPeak) +
               "): the exploration is not exhaustive, so `safe` is not a conclusion this run supports";
  }
  for (auto &kv : classes) res.functions.push_back(kv.second);
  for (auto &kv : edgeMap) res.callEdges.push_back(kv.second);
  return res;
}

}  // namespace hlir

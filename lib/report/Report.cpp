#include <cstdio>
#include "hlir/report/Report.h"

#include <algorithm>
#include <set>
#include <sstream>

#include "Json.h"

namespace hlir::report {

const char *verdictName(Verdict v) {
  switch (v) {
    case Verdict::Bug: return "bug";
    case Verdict::SafeUnderAssumptions: return "safe_under_assumptions";
    case Verdict::Unknown: return "unknown";
    case Verdict::SafeUpToLoopBound: return "safe_up_to_loop_bound";
  }
  return "?";
}

const char *reproducibleName(Reproducible r) {
  switch (r) {
    case Reproducible::RealInput: return "real_input";
    case Reproducible::HarnessOnly: return "harness_only";
  }
  return "real_input";
}

const char *replayStatusName(ReplayStatus s) {
  switch (s) {
    case ReplayStatus::Confirmed: return "confirmed";
    case ReplayStatus::NotReproduced: return "not_reproduced";
    case ReplayStatus::Skipped: return "skipped";
  }
  return "?";
}

Verdict computeVerdict(const EntryReport &e) {
  bool unconfirmed = false;
  for (auto &f : e.findings) {
    if (f.warning) continue;  // warnings (DoS / unbounded-index heads-ups) never make the verdict a bug
    if (f.replay == ReplayStatus::Confirmed) return Verdict::Bug;
    if (f.replay == ReplayStatus::NotReproduced) unconfirmed = true;
    if (f.replay == ReplayStatus::Skipped) return Verdict::Bug;  // replay was not requested: trust the solver
  }
  if (unconfirmed) return Verdict::Unknown;
  bool onlyBound = !e.incomplete.empty();
  for (auto &i : e.incomplete) onlyBound &= i.code == "loop_bound";
  if (onlyBound) return Verdict::SafeUpToLoopBound;
  if (!e.incomplete.empty()) return Verdict::Unknown;
  return Verdict::SafeUnderAssumptions;
}

static std::string where(const Location &l) {
  if (!l.valid()) return "";
  return l.file + ":" + std::to_string(l.line) + ":" + std::to_string(l.col);
}

std::string toText(const Report &r) {
  std::ostringstream o;
  for (auto &e : r.entries) {
    o << "== entry @" << e.function << " (" << e.specFile << ", label " << e.label << ") ==\n";
    o << "verdict: " << verdictName(e.verdict);
    if (e.verdict == Verdict::SafeUnderAssumptions) o << "  (no bug found in a complete exploration, under the assumptions below)";
    if (e.verdict == Verdict::SafeUpToLoopBound) o << "  (no bug in any execution whose loops run within the bound; longer loops were not explored)";
    o << "\n";
    unsigned nWarn = 0;
    for (auto &f : e.findings) nWarn += f.warning ? 1 : 0;
    if (nWarn) o << "warnings: " << nWarn << " (attacker-controlled loop/index, or a UB only the harness's own\n"
                    "          synthesis filler can produce; see findings, they do not affect the verdict)\n";
    if (!e.seedSummary.empty()) o << "benign seed: " << e.seedSummary << "\n";
    unsigned n = 0;
    for (auto &f : e.findings) {
      o << "\n[" << ++n << "] " << (f.warning ? "warning: " : "") << f.kind << " in @" << f.function;
      if (!f.op.empty()) o << " (" << f.op << ")";
      if (f.loc.valid()) o << " at " << where(f.loc);
      o << "\n    " << f.message << "\n";
      // State the attribution rather than let the location imply something false: the op is inside a model
      // body, the location is the call site that reached it (DESIGN.md Sec.22.471).
      if (!f.locFromFrame.empty())
        o << "    location is the CALL SITE: the failing operation is inside @" << f.locFromFrame
          << ", a modelled function with no source of its own\n";
      if (!f.origin.empty()) o << "    origin: " << f.origin << "\n";
      if (!f.callStack.empty()) {
        o << "    call chain (depth " << f.callStack.size() << "): ";
        for (size_t i = 0; i < f.callStack.size(); ++i) o << (i ? " -> " : "") << f.callStack[i];
        o << "\n";
      }
      o << "    replay: " << replayStatusName(f.replay);
      if (f.replay == ReplayStatus::NotReproduced) o << " [" << f.unconfirmedReason << "] " << f.unconfirmedDetail;
      o << "   engine: " << f.engine << "\n";
      if (!f.witness.empty()) {
        o << "    counterexample:\n";
        for (auto &w : f.witness) o << "      " << w.name << " = " << w.value << (w.note.empty() ? "" : "  (" + w.note + ")") << "\n";
      }
    }
    if (!e.incomplete.empty()) {
      o << "\nincomplete:\n";
      for (auto &i : e.incomplete) o << "  " << i.code << ": " << i.detail << "\n";
    }
    if (!e.assumptions.empty()) {
      o << "\nassumptions:\n";
      for (auto &a : e.assumptions) o << "  [" << a.category << "] " << a.text << (a.loc.valid() ? "  @ " + where(a.loc) : "") << "\n";
    }
    if (e.setupRegion.declared) {
      o << "\nsetup region: ";
      if (e.setupRegion.reused)
        o << "executed once (" << e.setupRegion.ops << " steps, " << e.setupRegion.objects
          << " objects, " << e.setupRegion.allocsForced << " allocations taken as succeeding), restored on "
          << e.setupRegion.skips << " later run(s) in " << e.setupRegion.secRestore << "s\n";
      else
        o << "declared but NOT reused -- " << e.setupRegion.refusal << "\n";
    }
    if (!e.frontier.empty()) {
      o << "\nsearch budget (flippable branch conditions by function, of " << e.flippablePcsTotal << "):\n";
      for (size_t i = 0; i < e.frontier.size() && i < 5; ++i) {
        const auto &s = e.frontier[i];
        char line[96];
        std::snprintf(line, sizeof line, "%5.1f%%  %8llu flips  %8llu queued  %6llu calls  %6.1f per call", 100.0 * s.share,
                      static_cast<unsigned long long>(s.flippablePcs), static_cast<unsigned long long>(s.queued),
                      static_cast<unsigned long long>(s.calls), s.perCall);
        o << "  @" << s.function << (s.library ? "  [model]" : "") << "\n      " << line
          << "  checks " << s.checksQueried << "/" << s.checksReached << " queried"
          << (s.foldCandidate ? "   <- FOLD CANDIDATE (a closed form would hand the solver one disjunction)" : "")
          // A function that eats the budget while nothing in it is ever QUERIED is one where a flip cannot
          // teach the solver anything: every safety question there is already decided concretely (§22.437).
          << (!s.foldCandidate && s.checksReached > 0 && s.checksQueried == 0 && s.share >= 0.10
                  ? "   <- NO QUERIED CHECK (flips here buy reordering, not reachability of a question)"
                  : "")
          << "\n";
      }
    }
    if (!e.functionClasses.empty()) {
      o << "\nfunction classes (calls: inert/observer/transformer/source/sanitizer):\n";
      for (auto &c : e.functionClasses)
        o << "  @" << c.function << ": " << c.calls << ": " << c.inert << "/" << c.observer << "/" << c.transformer << "/" << c.source << "/" << c.sanitizer << "\n";
    }
    if (e.coverage.measured) {
      const Coverage &c = e.coverage;
      char pct[32];
      std::snprintf(pct, sizeof pct, "%.1f%%", 100.0 * c.blockRatio());
      o << "\ncoverage: " << c.blocksVisited << " of " << c.blocksReachable << " blocks (" << pct << ") in the " << c.functionsReachable
        << " functions reachable from the entry; " << c.functionsEntered << " of them entered; runs: " << c.runsReturned << " returned, " << c.runsTerminated
        << " ended at a noreturn call\n";
      char bpct[32];
      std::snprintf(bpct, sizeof bpct, "%.1f%%", 100.0 * c.branchRatio());
      o << "branch coverage: " << c.branchesVisited << " of " << c.branchesReachable << " conditional-branch directions (" << bpct << ")\n";
      // What the missing part IS. Only `open` is a budget question; printing the percentage without this invites
      // "throw more runs at it" at edges no budget can ever open (DESIGN.md §22.429).
      if (c.missUnreached + c.missConst + c.missUnsat + c.missOpen + c.missGlobalInit)
        o << "  not covered: " << c.missOpen << " still queued when the budget ran out, " << c.missUnsat
          << " proved infeasible, " << c.missGlobalInit << " decided by a global's initial value, " << c.missConst
          << " constant in this build, " << c.missUnreached
          << " never reached\n";
      for (auto &t : c.terminations) {
        o << "  the program ends at " << t.by << " in @" << t.function << (t.loc.valid() ? " (" + where(t.loc) + ")" : "") << (t.stack.empty() ? "" : " <- " + t.stack) << ": " << t.runs << " run(s)\n";
        for (auto &w : t.witness) o << "      e.g. " << w.name << " = " << w.value << (w.note.empty() ? "" : "  (" + w.note + ")") << "\n";
      }
      if (!c.notEntered.empty()) {
        o << "  never entered (callees of entered functions";
        if (c.notEnteredTotal > c.notEntered.size()) o << ", " << c.notEntered.size() << " of " << c.notEnteredTotal;
        o << "):";
        for (auto &n : c.notEntered) o << " @" << n;
        o << "\n";
      }
    }
    const Metrics &m = e.metrics;
    o << "\nmetrics: " << m.runs << " concolic runs, " << m.pathsExplored << " symbolic paths, " << m.solverQueries << " solver queries (" << m.cacheHits
      << " cache hits, " << m.escalations << " timeout escalations), " << m.solverTerms << " SMT terms solved; first run: " << m.stepsFirstRun
      << " ops, " << m.taintedOpsFirstRun << " tainted, " << m.pcsFirstRun << " constraints; seed " << m.secondsSeed << "s, analysis " << m.secondsAnalysis
      << "s, total " << m.secondsTotal << "s\n";
    // The search's yield. Printed always, next to the budget it spent, because a zero here invalidates the
    // reading of every "not covered: ... proved infeasible" line above it (DESIGN.md Sec.22.468).
    if (m.flipsQueued) {
      o << "search yield: " << m.flipsSolved << " of " << m.flipsQueued << " branch flips were satisfiable ("
        << (100 * m.flipsSolved / m.flipsQueued) << "%), " << m.flipsUnsat << " refused";
      if (!m.flipsSolved)
        o << "  <- SEARCH COLLAPSED: no flip produced a new input, so this result rests on ONE execution and the"
             " `unsat` edges above are infeasible only on that single path prefix";
      o << "\n";
    }
    // A1's opportunity, not just its outcome: a zero here means the program's own invariants never reached an
    // object past the synthesis frontier, which is a different fact from "they reached it and changed nothing".
    if (m.frontierFieldReads) {
      o << "frontier invariants: " << m.frontierFieldReads << " field read(s) past the synthesis frontier, "
        << m.frontierBoundsApplied << " asserted bound(s) applied, " << m.frontierBoundsMissing
        << " read(s) with no bound the program asserts, " << m.frontierBoundsInfeasible
        << " run(s) stopped as a state the program says cannot exist\n";
    }
    if (m.secInterp + m.secSolve + m.secReplay + m.secCone > 0)
      o << "branch directions covered: " << m.branchesCovered << "; ";
      o << "concolic time: interpretation " << m.secInterp << "s, solver " << m.secSolve << "s (assertions " << m.secAssert << "s, check-sat " << m.secCheck << "s), replay " << m.secReplay << "s, cones " << m.secCone << "s\n";
  }
  return o.str();
}

static void jsonLoc(Json &j, const char *key, const Location &l) {
  j.beginObject(key).str("file", l.file).num("line", l.line).num("column", l.col).endObject();
}

std::string toJson(const Report &r) {
  Json j;
  j.beginObject().str("tool", r.tool).str("version", r.version).beginArray("entries");
  for (auto &e : r.entries) {
    j.beginObject();
    j.str("function", e.function).str("spec", e.specFile).str("label", e.label).str("verdict", verdictName(e.verdict)).str("seed", e.seedSummary);
    j.beginArray("checks");
    for (auto &c : e.checks)
      j.beginObject().str("kind", c.kind).num("reached", static_cast<double>(c.reached))
          .num("decided_concretely", static_cast<double>(c.decidedConcretely)).num("queried", static_cast<double>(c.queried))
          .num("sat", static_cast<double>(c.sat)).num("unsat", static_cast<double>(c.unsat)).endObject();
    j.endArray();
    j.beginObject("taint_reach").boolean("memory_index", e.taintReach.memoryIndex).boolean("loop_bound", e.taintReach.loopBound)
        .boolean("alloc_size", e.taintReach.allocSize).boolean("sink", e.taintReach.sink).endObject();
    j.str("setup_function", e.setupFunction);
    j.boolean("reads_incomplete", e.readsIncomplete).beginArray("reads");
    for (auto &r : e.reads) {
      // offsets as a compact string: a run of thousands of them as JSON numbers would dwarf the rest of the report
      std::string offs;
      for (size_t i = 0; i < r.offsets.size(); ++i) offs += (i ? "," : "") + std::to_string(r.offsets[i]);
      j.beginObject().str("location", r.location).str("offsets", offs).endObject();
    }
    j.endArray();
    j.beginArray("opaque_calls");
    for (auto &c : e.opaqueCalls) j.beginObject().str("function", c.first).num("calls", static_cast<double>(c.second)).endObject();
    j.endArray();
    j.beginArray("lower_failures");
    for (auto &c : e.lowerFailures) j.beginObject().str("function", c.first).str("reason", c.second).endObject();
    j.endArray();
    if (e.setupRegion.declared)
      j.beginObject("setup_region")
          .boolean("reused", e.setupRegion.reused)
          .str("refusal", e.setupRegion.refusal)
          .num("ops", static_cast<double>(e.setupRegion.ops))
          .num("skips", static_cast<double>(e.setupRegion.skips))
          .num("sec_restore", e.setupRegion.secRestore)
          .num("allocs_forced", static_cast<double>(e.setupRegion.allocsForced))
          .num("objects", static_cast<double>(e.setupRegion.objects))
          .num("symbolic", static_cast<double>(e.setupRegion.symbolic))
          .endObject();
    j.num("flippable_pcs_total", static_cast<double>(e.flippablePcsTotal)).beginArray("search_budget");
    for (auto &s : e.frontier)
      j.beginObject()
          .str("function", s.function)
          .num("flippable_pcs", static_cast<double>(s.flippablePcs))
          .num("queued", static_cast<double>(s.queued))
          .num("calls", static_cast<double>(s.calls))
          .num("share", s.share)
          .num("per_call", s.perCall)
          .boolean("library", s.library)
          .boolean("fold_candidate", s.foldCandidate)
          .num("checks_reached", static_cast<double>(s.checksReached))
          .num("checks_queried", static_cast<double>(s.checksQueried))
          .endObject();
    j.endArray();
    j.beginArray("init_functions");
    for (auto &n : e.initFunctions) j.item(n);
    j.endArray();
    j.beginArray("findings");
    for (auto &f : e.findings) {
      j.beginObject().str("id", f.id).str("kind", f.kind).boolean("warning", f.warning).boolean("in_prologue", f.inPrologue).str("message", f.message);
      j.str("reproducible_as", reproducibleName(f.reproducible));
      if (!f.reproducibleWhy.empty()) j.str("reproducible_why", f.reproducibleWhy);
      jsonLoc(j, "location", f.loc);
      j.str("function", f.function).str("op", f.op).str("origin", f.origin).str("engine", f.engine);
      if (!f.locFromFrame.empty()) j.str("loc_from_frame", f.locFromFrame);
      j.str("replay", replayStatusName(f.replay));
      if (f.replay == ReplayStatus::NotReproduced) j.str("unconfirmed_reason", f.unconfirmedReason).str("unconfirmed_detail", f.unconfirmedDetail);
      j.beginArray("call_stack");
      for (auto &c : f.callStack) j.item(c);
      j.endArray().beginArray("labels");
      for (auto &l : f.labels) j.item(l);
      j.endArray().beginArray("counterexample");
      for (auto &w : f.witness) j.beginObject().str("name", w.name).str("value", w.value).str("note", w.note).endObject();
      j.endArray();
      // the failing access in numbers, and the memory it happened in (DESIGN.md §22.369)
      if (f.access.valid) {
        j.beginObject("access").num("object", static_cast<double>(f.access.obj)).str("object_name", f.access.objName);
        if (f.access.objSizeKnown) j.num("object_size", static_cast<double>(f.access.objSize));
        if (f.access.offsetKnown) j.num("offset", static_cast<double>(f.access.offset));
        j.boolean("offset_symbolic", f.access.offsetSymbolic);
        if (f.access.width) j.num("width", static_cast<double>(f.access.width));
        if (!f.access.access.empty()) j.str("mode", f.access.access);
        j.endObject();
      }
      j.beginArray("objects");
      for (auto &o : f.objects) {
        j.beginObject().num("id", static_cast<double>(o.id)).str("kind", o.kind).str("name", o.name);
        if (o.sizeKnown) j.num("size", static_cast<double>(o.size));
        j.boolean("prog_written", o.progWritten).boolean("frontier", o.frontier).boolean("input_content", o.inputContent)
         .boolean("unknown_content", o.unknownContent);
        j.num("symbolic_bytes", static_cast<double>(o.symbolicBytes)).boolean("truncated", o.truncated);
        j.beginArray("non_zero");
        for (auto &b : o.nonZero) j.beginObject().num("off", static_cast<double>(b.off)).num("val", static_cast<double>(b.val)).endObject();
        j.endArray().endObject();
      }
      j.endArray().endObject();
    }
    j.endArray().beginArray("assumptions");
    for (auto &a : e.assumptions) {
      j.beginObject().str("category", a.category).str("text", a.text);
      jsonLoc(j, "location", a.loc);
      j.endObject();
    }
    j.endArray().beginArray("incomplete");
    for (auto &i : e.incomplete) j.beginObject().str("code", i.code).str("detail", i.detail).endObject();
    j.endArray().beginArray("function_classes");
    for (auto &c : e.functionClasses)
      j.beginObject().str("function", c.function).num("calls", static_cast<double>(c.calls)).num("inert", static_cast<double>(c.inert))
          .num("observer", static_cast<double>(c.observer)).num("transformer", static_cast<double>(c.transformer))
          .num("source", static_cast<double>(c.source)).num("sanitizer", static_cast<double>(c.sanitizer)).endObject();
    j.endArray().beginArray("call_edges");
    for (auto &c : e.callEdges)
      j.beginObject().str("caller", c.caller).str("callee", c.callee).num("calls", static_cast<double>(c.calls)).boolean("tainted", c.tainted).endObject();
    j.endArray();
    {
      const Coverage &c = e.coverage;
      j.beginObject("coverage").boolean("measured", c.measured).num("functions_reachable", static_cast<double>(c.functionsReachable))
          .num("functions_entered", static_cast<double>(c.functionsEntered)).num("blocks_reachable", static_cast<double>(c.blocksReachable))
          .num("blocks_visited", static_cast<double>(c.blocksVisited)).num("blocks_in_entered", static_cast<double>(c.blocksInEntered))
          .num("branches_in_entered", static_cast<double>(c.branchesInEntered))
          .num("branches_reachable", static_cast<double>(c.branchesReachable)).num("branches_visited", static_cast<double>(c.branchesVisited))
          .num("runs_returned", static_cast<double>(c.runsReturned)).num("runs_terminated", static_cast<double>(c.runsTerminated))
          .num("not_entered_total", static_cast<double>(c.notEnteredTotal))
          // Why the branch number is what it is. Always present: four integers, and without them the percentage
          // cannot be acted on (DESIGN.md §22.429).
          .num("branch_miss_unreached", static_cast<double>(c.missUnreached))
          .num("branch_miss_const", static_cast<double>(c.missConst))
          .num("branch_miss_unsat", static_cast<double>(c.missUnsat))
          .num("branch_miss_open", static_cast<double>(c.missOpen))
          .num("branch_miss_global_init", static_cast<double>(c.missGlobalInit))
          .beginArray("branches_missed");
      for (auto &b : c.branchesMissed) {
        j.beginObject().str("file", b.file).num("line", b.line).num("column", b.column).str("function", b.function)
            .str("direction", b.dir ? "true" : "false").str("why", b.why).endObject();
      }
      j.endArray().beginArray("terminations");
      for (auto &t : c.terminations) {
        j.beginObject().str("function", t.function).str("by", t.by).str("stack", t.stack).num("runs", t.runs);
        jsonLoc(j, "location", t.loc);
        j.beginArray("witness");
        for (auto &w : t.witness) j.beginObject().str("name", w.name).str("value", w.value).str("note", w.note).endObject();
        j.endArray().endObject();
      }
      j.endArray().beginArray("not_entered");
      for (auto &n : c.notEntered) j.item(n);
      j.endArray().beginArray("entered_functions");
      for (auto &n : c.enteredFunctions) j.item(n);
      j.endArray().beginArray("covered_lines");
      for (auto &n : c.coveredLines) j.item(n);
      j.endArray().endObject();
    }
    const Metrics &m = e.metrics;
    j.beginObject("metrics").num("runs", static_cast<double>(m.runs)).num("paths", static_cast<double>(m.pathsExplored))
        .num("solver_queries", static_cast<double>(m.solverQueries)).num("cache_hits", static_cast<double>(m.cacheHits))
        .num("escalations", static_cast<double>(m.escalations)).num("solver_terms", static_cast<double>(m.solverTerms))
        .num("steps_first_run", static_cast<double>(m.stepsFirstRun)).num("tainted_ops_first_run", static_cast<double>(m.taintedOpsFirstRun))
        .num("max_call_depth", static_cast<double>(m.maxCallDepth)).num("branches_covered", static_cast<double>(m.branchesCovered)).num("sec_interp", m.secInterp).num("sec_solve", m.secSolve).num("sec_assert", m.secAssert).num("sec_check", m.secCheck).num("sec_replay", m.secReplay).num("sec_cone", m.secCone).num("constraints_first_run", static_cast<double>(m.pcsFirstRun)).num("seconds_seed", m.secondsSeed)
        .num("seconds_analysis", m.secondsAnalysis).num("seconds_total", m.secondsTotal)
        .num("flips_queued", static_cast<double>(m.flipsQueued)).num("flips_solved", static_cast<double>(m.flipsSolved))
        .num("flips_unsat", static_cast<double>(m.flipsUnsat))
        .num("frontier_field_reads", static_cast<double>(m.frontierFieldReads))
        .num("frontier_bounds_applied", static_cast<double>(m.frontierBoundsApplied))
        .num("frontier_bounds_missing", static_cast<double>(m.frontierBoundsMissing))
        .num("frontier_bounds_infeasible", static_cast<double>(m.frontierBoundsInfeasible)).endObject();
    j.endObject();
  }
  j.endArray().endObject();
  return j.str();
}

// A DOT identifier/string literal is just a quoted string with '"' and '\' escaped; function names are HLIR identifiers
// ([A-Za-z_][A-Za-z0-9_.]*) so this never has to deal with anything fancier.
static std::string dotQuote(const std::string &s) {
  std::string o = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\') o += '\\';
    o += c;
  }
  o += '"';
  return o;
}

std::string toDot(const Report &r) {
  bool any = false;
  for (auto &e : r.entries) any |= !e.callEdges.empty();
  if (!any) return "";
  std::ostringstream o;
  o << "// generated by hlir-taint --format dot: the function call graph of the analysed entry/entries, with edges\n"
       "// the taint engine saw carry tainted data drawn in red (color=red, penwidth=2). See IMPLEMENTATION_PLAN.md,\n"
       "// \"call graph visualisation\", for exactly what \"carries tainted data\" means and its precision limits.\n";
  o << "digraph callgraph {\n  rankdir=LR;\n  node [shape=box, fontname=\"monospace\"];\n  edge [fontname=\"monospace\"];\n";
  for (auto &e : r.entries) {
    if (e.callEdges.empty()) continue;
    bool multi = r.entries.size() > 1;
    std::string indent = multi ? "    " : "  ";
    if (multi) o << "  subgraph \"cluster_" << e.function << "\" {\n    label=" << dotQuote("entry @" + e.function) << ";\n";
    std::set<std::string> nodes;
    for (auto &c : e.callEdges) { nodes.insert(c.caller); nodes.insert(c.callee); }
    for (auto &n : nodes) o << indent << dotQuote((multi ? e.function + ":" : "") + n) << " [label=" << dotQuote(n) << "];\n";
    for (auto &c : e.callEdges) {
      std::string from = dotQuote((multi ? e.function + ":" : "") + c.caller), to = dotQuote((multi ? e.function + ":" : "") + c.callee);
      o << indent << from << " -> " << to << " [label=" << dotQuote(std::to_string(c.calls) + (c.calls == 1 ? " call" : " calls"));
      if (c.tainted) o << ", color=red, fontcolor=red, penwidth=2";
      else o << ", color=\"#888888\"";
      o << "];\n";
    }
    if (multi) o << "  }\n";
  }
  o << "}\n";
  return o.str();
}

}  // namespace hlir::report

// Reads back what toJson writes (used by hlir-scan to collect the reports of its worker processes). Not a general JSON
// library: it parses the full JSON grammar into a small tree, then maps the fields of our own schema.
#include <cstdlib>

#include "hlir/report/Report.h"

namespace hlir::report {
namespace {

struct JV {
  enum K { Null, Bool, Num, Str, Arr, Obj } k = Null;
  double n = 0;
  bool b = false;
  std::string s;
  std::vector<JV> a;
  std::vector<std::pair<std::string, JV>> o;
  const JV *get(const char *key) const {
    for (auto &kv : o)
      if (kv.first == key) return &kv.second;
    return nullptr;
  }
};

struct Parser {
  const std::string &t;
  size_t i = 0;
  std::string err;
  explicit Parser(const std::string &s) : t(s) {}
  void ws() { while (i < t.size() && isspace(static_cast<unsigned char>(t[i]))) ++i; }
  bool fail(const char *m) { if (err.empty()) err = std::string(m) + " at offset " + std::to_string(i); return false; }
  bool lit(const char *w, size_t n) { if (t.compare(i, n, w) == 0) { i += n; return true; } return false; }
  bool str(std::string &out) {
    if (i >= t.size() || t[i] != '"') return fail("expected string");
    ++i;
    out.clear();
    while (i < t.size() && t[i] != '"') {
      char c = t[i++];
      if (c != '\\') { out += c; continue; }
      if (i >= t.size()) return fail("bad escape");
      char e = t[i++];
      switch (e) {
        case 'n': out += '\n'; break;
        case 'r': out += '\r'; break;
        case 't': out += '\t'; break;
        case 'b': out += '\b'; break;
        case 'f': out += '\f'; break;
        case 'u': {
          if (i + 4 > t.size()) return fail("bad \\u escape");
          unsigned v = static_cast<unsigned>(std::strtoul(t.substr(i, 4).c_str(), nullptr, 16));
          i += 4;
          if (v < 0x80) out += static_cast<char>(v);
          else if (v < 0x800) { out += static_cast<char>(0xC0 | (v >> 6)); out += static_cast<char>(0x80 | (v & 0x3F)); }
          else { out += static_cast<char>(0xE0 | (v >> 12)); out += static_cast<char>(0x80 | ((v >> 6) & 0x3F)); out += static_cast<char>(0x80 | (v & 0x3F)); }
          break;
        }
        default: out += e;
      }
    }
    if (i >= t.size()) return fail("unterminated string");
    ++i;
    return true;
  }
  bool value(JV &v) {
    ws();
    if (i >= t.size()) return fail("unexpected end");
    char c = t[i];
    if (c == '{') {
      v.k = JV::Obj;
      ++i; ws();
      if (i < t.size() && t[i] == '}') { ++i; return true; }
      for (;;) {
        ws();
        std::string key;
        if (!str(key)) return false;
        ws();
        if (i >= t.size() || t[i++] != ':') return fail("expected ':'");
        JV child;
        if (!value(child)) return false;
        v.o.emplace_back(std::move(key), std::move(child));
        ws();
        if (i < t.size() && t[i] == ',') { ++i; continue; }
        if (i < t.size() && t[i] == '}') { ++i; return true; }
        return fail("expected ',' or '}'");
      }
    }
    if (c == '[') {
      v.k = JV::Arr;
      ++i; ws();
      if (i < t.size() && t[i] == ']') { ++i; return true; }
      for (;;) {
        JV child;
        if (!value(child)) return false;
        v.a.push_back(std::move(child));
        ws();
        if (i < t.size() && t[i] == ',') { ++i; continue; }
        if (i < t.size() && t[i] == ']') { ++i; return true; }
        return fail("expected ',' or ']'");
      }
    }
    if (c == '"') { v.k = JV::Str; return str(v.s); }
    if (lit("true", 4)) { v.k = JV::Bool; v.b = true; return true; }
    if (lit("false", 5)) { v.k = JV::Bool; v.b = false; return true; }
    if (lit("null", 4)) { v.k = JV::Null; return true; }
    char *end = nullptr;
    v.n = std::strtod(t.c_str() + i, &end);
    if (end == t.c_str() + i) return fail("unexpected character");
    i = static_cast<size_t>(end - t.c_str());
    v.k = JV::Num;
    return true;
  }
};

std::string S(const JV &o, const char *k) { auto *v = o.get(k); return v && v->k == JV::Str ? v->s : ""; }
bool B(const JV &o, const char *k) { auto *v = o.get(k); return v && v->k == JV::Bool && v->b; }
double N(const JV &o, const char *k) { auto *v = o.get(k); return v && v->k == JV::Num ? v->n : 0; }
Location L(const JV &o, const char *k) {
  Location l;
  if (auto *v = o.get(k)) { l.file = S(*v, "file"); l.line = static_cast<unsigned>(N(*v, "line")); l.col = static_cast<unsigned>(N(*v, "column")); }
  return l;
}
template <class F> void each(const JV &o, const char *k, F f) {
  if (auto *v = o.get(k))
    if (v->k == JV::Arr)
      for (auto &x : v->a) f(x);
}

}  // namespace

bool fromJson(const std::string &text, Report &out, std::string &err) {
  Parser p(text);
  JV root;
  if (!p.value(root) || root.k != JV::Obj) { err = p.err.empty() ? "not a JSON object" : p.err; return false; }
  out = Report();
  out.tool = S(root, "tool");
  out.version = S(root, "version");
  each(root, "entries", [&](const JV &e) {
    EntryReport r;
    r.function = S(e, "function");
    r.specFile = S(e, "spec");
    r.label = S(e, "label");
    std::string v = S(e, "verdict");
    r.verdict = v == "bug" ? Verdict::Bug : v == "safe_under_assumptions" ? Verdict::SafeUnderAssumptions : v == "safe_up_to_loop_bound" ? Verdict::SafeUpToLoopBound : Verdict::Unknown;
    r.seedSummary = S(e, "seed");
    r.setupFunction = S(e, "setup_function");
    r.readsIncomplete = B(e, "reads_incomplete");
    each(e, "reads", [&](const JV &x) {
      EntryReport::ReadSet rs;
      rs.location = S(x, "location");
      std::string offs = S(x, "offsets");
      for (size_t i = 0, j2 = 0; i <= offs.size(); ++i)
        if (i == offs.size() || offs[i] == ',') {
          if (i > j2) rs.offsets.push_back(std::stoull(offs.substr(j2, i - j2)));
          j2 = i + 1;
        }
      r.reads.push_back(std::move(rs));
    });
    each(e, "opaque_calls", [&](const JV &c) { r.opaqueCalls.push_back({S(c, "function"), static_cast<uint64_t>(N(c, "calls"))}); });
    each(e, "lower_failures", [&](const JV &c) { r.lowerFailures[S(c, "function")] = S(c, "reason"); });
    r.flippablePcsTotal = static_cast<uint64_t>(N(e, "flippable_pcs_total"));
    if (const JV *sr = e.get("setup_region")) {
      r.setupRegion.declared = true;
      r.setupRegion.reused = B(*sr, "reused");
      r.setupRegion.refusal = S(*sr, "refusal");
      r.setupRegion.ops = static_cast<uint64_t>(N(*sr, "ops"));
      r.setupRegion.skips = static_cast<uint64_t>(N(*sr, "skips"));
      r.setupRegion.secRestore = N(*sr, "sec_restore");
      r.setupRegion.allocsForced = static_cast<uint64_t>(N(*sr, "allocs_forced"));
      r.setupRegion.objects = static_cast<unsigned>(N(*sr, "objects"));
      r.setupRegion.symbolic = static_cast<unsigned>(N(*sr, "symbolic"));
    }
    each(e, "search_budget", [&](const JV &c) {
      EntryReport::FrontierSite s;
      s.function = S(c, "function");
      s.flippablePcs = static_cast<uint64_t>(N(c, "flippable_pcs"));
      s.queued = static_cast<uint64_t>(N(c, "queued"));
      s.calls = static_cast<uint64_t>(N(c, "calls"));
      s.share = N(c, "share");
      s.perCall = N(c, "per_call");
      s.library = B(c, "library");
      s.foldCandidate = B(c, "fold_candidate");
      s.checksReached = static_cast<uint64_t>(N(c, "checks_reached"));
      s.checksQueried = static_cast<uint64_t>(N(c, "checks_queried"));
      r.frontier.push_back(std::move(s));
    });
    each(e, "init_functions", [&](const JV &n) { r.initFunctions.push_back(n.s); });
    each(e, "checks", [&](const JV &c) {
      CheckSummary cs;
      cs.kind = S(c, "kind");
      cs.reached = static_cast<uint64_t>(N(c, "reached"));
      cs.decidedConcretely = static_cast<uint64_t>(N(c, "decided_concretely"));
      cs.queried = static_cast<uint64_t>(N(c, "queried"));
      cs.sat = static_cast<uint64_t>(N(c, "sat"));
      cs.unsat = static_cast<uint64_t>(N(c, "unsat"));
      r.checks.push_back(std::move(cs));
    });
    if (auto *t = e.get("taint_reach")) {
      r.taintReach.memoryIndex = B(*t, "memory_index");
      r.taintReach.loopBound = B(*t, "loop_bound");
      r.taintReach.allocSize = B(*t, "alloc_size");
      r.taintReach.sink = B(*t, "sink");
    }
    each(e, "findings", [&](const JV &f) {
      Finding x;
      x.id = S(f, "id"); x.kind = S(f, "kind"); x.warning = B(f, "warning"); x.message = S(f, "message"); x.loc = L(f, "location");
      x.function = S(f, "function"); x.op = S(f, "op"); x.origin = S(f, "origin"); x.engine = S(f, "engine");
      std::string rp = S(f, "replay");
      x.replay = rp == "confirmed" ? ReplayStatus::Confirmed : rp == "not_reproduced" ? ReplayStatus::NotReproduced : ReplayStatus::Skipped;
      x.unconfirmedReason = S(f, "unconfirmed_reason"); x.unconfirmedDetail = S(f, "unconfirmed_detail");
      each(f, "call_stack", [&](const JV &c) { x.callStack.push_back(c.s); });
      // Entries come back from forked workers as JSON: a field the parent cannot parse does not exist
      // (the lesson of Sec.22.468).
      x.locFromFrame = S(f, "loc_from_frame");
      each(f, "labels", [&](const JV &l) { x.labels.push_back(l.s); });
      each(f, "counterexample", [&](const JV &w) { x.witness.push_back({S(w, "name"), S(w, "value"), S(w, "note")}); });
      // evidence (DESIGN.md §22.369). This round trip is not cosmetic: hlir-scan analyses each entry in a forked
      // worker and the parent re-reads the worker's JSON, so a field the reader does not know about is silently
      // dropped on the way out -- which is exactly how the first version of this landed, emitting everything and
      // reporting nothing.
      x.inPrologue = B(f, "in_prologue");
      x.reproducible = S(f, "reproducible_as") == "harness_only" ? Reproducible::HarnessOnly : Reproducible::RealInput;
      x.reproducibleWhy = S(f, "reproducible_why");
      if (auto *a = f.get("access")) {
        x.access.valid = true;
        x.access.obj = static_cast<unsigned>(N(*a, "object"));
        x.access.objName = S(*a, "object_name");
        if (a->get("object_size")) { x.access.objSizeKnown = true; x.access.objSize = static_cast<uint64_t>(N(*a, "object_size")); }
        if (a->get("offset")) { x.access.offsetKnown = true; x.access.offset = static_cast<long long>(N(*a, "offset")); }
        x.access.offsetSymbolic = B(*a, "offset_symbolic");
        x.access.width = static_cast<unsigned>(N(*a, "width"));
        x.access.access = S(*a, "mode");
      }
      each(f, "objects", [&](const JV &o) {
        EvidenceObject e;
        e.id = static_cast<unsigned>(N(o, "id"));
        e.kind = S(o, "kind");
        e.name = S(o, "name");
        if (o.get("size")) { e.sizeKnown = true; e.size = static_cast<uint64_t>(N(o, "size")); }
        e.progWritten = B(o, "prog_written");
        e.frontier = B(o, "frontier");
        e.inputContent = B(o, "input_content");
        e.unknownContent = B(o, "unknown_content");
        e.symbolicBytes = static_cast<unsigned>(N(o, "symbolic_bytes"));
        e.truncated = B(o, "truncated");
        each(o, "non_zero", [&](const JV &b) { e.nonZero.push_back({static_cast<uint64_t>(N(b, "off")), static_cast<unsigned>(N(b, "val"))}); });
        x.objects.push_back(std::move(e));
      });
      r.findings.push_back(std::move(x));
    });
    each(e, "assumptions", [&](const JV &a) { r.assumptions.push_back({S(a, "category"), S(a, "text"), L(a, "location")}); });
    each(e, "incomplete", [&](const JV &i) { r.incomplete.push_back({S(i, "code"), S(i, "detail")}); });
    each(e, "function_classes", [&](const JV &c) {
      FunctionClass fc;
      fc.function = S(c, "function");
      fc.calls = static_cast<uint64_t>(N(c, "calls")); fc.inert = static_cast<uint64_t>(N(c, "inert")); fc.observer = static_cast<uint64_t>(N(c, "observer"));
      fc.transformer = static_cast<uint64_t>(N(c, "transformer")); fc.source = static_cast<uint64_t>(N(c, "source")); fc.sanitizer = static_cast<uint64_t>(N(c, "sanitizer"));
      r.functionClasses.push_back(fc);
    });
    each(e, "call_edges", [&](const JV &c) {
      CallEdge ce;
      ce.caller = S(c, "caller"); ce.callee = S(c, "callee");
      ce.calls = static_cast<uint64_t>(N(c, "calls")); ce.tainted = B(c, "tainted");
      r.callEdges.push_back(ce);
    });
    if (auto *cv = e.get("coverage")) {
      Coverage &c = r.coverage;
      c.measured = B(*cv, "measured");
      c.functionsReachable = static_cast<uint64_t>(N(*cv, "functions_reachable")); c.functionsEntered = static_cast<uint64_t>(N(*cv, "functions_entered"));
      c.blocksReachable = static_cast<uint64_t>(N(*cv, "blocks_reachable")); c.blocksVisited = static_cast<uint64_t>(N(*cv, "blocks_visited"));
      c.blocksInEntered = static_cast<uint64_t>(N(*cv, "blocks_in_entered"));
      c.branchesInEntered = static_cast<uint64_t>(N(*cv, "branches_in_entered"));
      c.branchesReachable = static_cast<uint64_t>(N(*cv, "branches_reachable")); c.branchesVisited = static_cast<uint64_t>(N(*cv, "branches_visited"));
      c.runsReturned = static_cast<uint64_t>(N(*cv, "runs_returned")); c.runsTerminated = static_cast<uint64_t>(N(*cv, "runs_terminated"));
      c.notEnteredTotal = static_cast<uint64_t>(N(*cv, "not_entered_total"));
      c.missUnreached = static_cast<uint64_t>(N(*cv, "branch_miss_unreached"));
      c.missConst = static_cast<uint64_t>(N(*cv, "branch_miss_const"));
      c.missUnsat = static_cast<uint64_t>(N(*cv, "branch_miss_unsat"));
      c.missOpen = static_cast<uint64_t>(N(*cv, "branch_miss_open"));
      c.missGlobalInit = static_cast<uint64_t>(N(*cv, "branch_miss_global_init"));
      each(*cv, "branches_missed", [&](const JV &b) {
        MissedBranch mb;
        mb.file = S(b, "file");
        mb.function = S(b, "function");
        mb.line = static_cast<unsigned>(N(b, "line"));
        mb.column = static_cast<unsigned>(N(b, "column"));
        mb.dir = S(b, "direction") == "true";
        mb.why = S(b, "why");
        c.branchesMissed.push_back(std::move(mb));
      });
      each(*cv, "terminations", [&](const JV &t) {
        TerminationSite ts{S(t, "function"), S(t, "by"), S(t, "stack"), L(t, "location"), static_cast<unsigned>(N(t, "runs")), {}};
        each(t, "witness", [&](const JV &w) { ts.witness.push_back({S(w, "name"), S(w, "value"), S(w, "note")}); });
        c.terminations.push_back(std::move(ts));
      });
      each(*cv, "not_entered", [&](const JV &n) { c.notEntered.push_back(n.s); });
      each(*cv, "entered_functions", [&](const JV &n) { c.enteredFunctions.push_back(n.s); });
      each(*cv, "covered_lines", [&](const JV &n) { c.coveredLines.push_back(n.s); });
    }
    if (auto *m = e.get("metrics")) {
      Metrics &x = r.metrics;
      x.runs = static_cast<uint64_t>(N(*m, "runs")); x.pathsExplored = static_cast<uint64_t>(N(*m, "paths"));
      x.solverQueries = static_cast<uint64_t>(N(*m, "solver_queries")); x.cacheHits = static_cast<uint64_t>(N(*m, "cache_hits"));
      // Entries run in forked workers and come back as JSON, so a metric the parent cannot PARSE is a metric
      // that does not exist, however carefully the worker wrote it (DESIGN.md Sec.22.468).
      x.flipsQueued = static_cast<uint64_t>(N(*m, "flips_queued")); x.flipsSolved = static_cast<uint64_t>(N(*m, "flips_solved"));
      x.flipsUnsat = static_cast<uint64_t>(N(*m, "flips_unsat"));
      x.frontierFieldReads = static_cast<uint64_t>(N(*m, "frontier_field_reads"));
      x.frontierBoundsApplied = static_cast<uint64_t>(N(*m, "frontier_bounds_applied"));
      x.frontierBoundsMissing = static_cast<uint64_t>(N(*m, "frontier_bounds_missing"));
      x.frontierBoundsInfeasible = static_cast<uint64_t>(N(*m, "frontier_bounds_infeasible"));
      x.escalations = static_cast<uint64_t>(N(*m, "escalations")); x.solverTerms = static_cast<uint64_t>(N(*m, "solver_terms"));
      x.stepsFirstRun = static_cast<uint64_t>(N(*m, "steps_first_run")); x.taintedOpsFirstRun = static_cast<uint64_t>(N(*m, "tainted_ops_first_run"));
      x.pcsFirstRun = static_cast<uint64_t>(N(*m, "constraints_first_run"));
      x.maxCallDepth = static_cast<unsigned>(N(*m, "max_call_depth"));
      x.branchesCovered = static_cast<unsigned>(N(*m, "branches_covered"));
      x.secInterp = N(*m, "sec_interp"); x.secSolve = N(*m, "sec_solve"); x.secAssert = N(*m, "sec_assert"); x.secCheck = N(*m, "sec_check"); x.secReplay = N(*m, "sec_replay"); x.secCone = N(*m, "sec_cone");
      x.secondsSeed = N(*m, "seconds_seed"); x.secondsAnalysis = N(*m, "seconds_analysis"); x.secondsTotal = N(*m, "seconds_total");
    }
    out.entries.push_back(std::move(r));
  });
  return true;
}

}  // namespace hlir::report

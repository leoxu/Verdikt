#include <cstdio>
#include <cstring>
// Tests for reports and robustness (P7): report content and formats, replay-confirmation rate and reason labels over the
// CWE-style corpus, timeout layering / query cache, and the escalation path.
#include <dirent.h>

#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>

#include "hlir/driver/Pipeline.h"

using namespace hlir;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }
static bool has(const std::string &hay, const std::string &needle) { return hay.find(needle) != std::string::npos; }

// A strict little JSON parser: returns true iff `s` is exactly one valid JSON value.
struct JsonCheck {
  const std::string &s;
  size_t i = 0;
  void ws() { while (i < s.size() && isspace(static_cast<unsigned char>(s[i]))) ++i; }
  bool lit(const char *w) { size_t n = strlen(w); if (s.compare(i, n, w) == 0) { i += n; return true; } return false; }
  bool str() {
    if (i >= s.size() || s[i] != '"') return false;
    for (++i; i < s.size(); ++i) {
      if (s[i] == '\\') { ++i; continue; }
      if (s[i] == '"') { ++i; return true; }
      if (static_cast<unsigned char>(s[i]) < 0x20) return false;
    }
    return false;
  }
  bool value() {
    ws();
    if (i >= s.size()) return false;
    char c = s[i];
    if (c == '{') {
      ++i; ws();
      if (i < s.size() && s[i] == '}') { ++i; return true; }
      for (;;) {
        ws();
        if (!str()) return false;
        ws();
        if (i >= s.size() || s[i++] != ':') return false;
        if (!value()) return false;
        ws();
        if (i < s.size() && s[i] == ',') { ++i; continue; }
        if (i < s.size() && s[i] == '}') { ++i; return true; }
        return false;
      }
    }
    if (c == '[') {
      ++i; ws();
      if (i < s.size() && s[i] == ']') { ++i; return true; }
      for (;;) {
        if (!value()) return false;
        ws();
        if (i < s.size() && s[i] == ',') { ++i; continue; }
        if (i < s.size() && s[i] == ']') { ++i; return true; }
        return false;
      }
    }
    if (c == '"') return str();
    if (lit("true") || lit("false") || lit("null")) return true;
    size_t b = i;
    if (s[i] == '-') ++i;
    while (i < s.size() && (isdigit(static_cast<unsigned char>(s[i])) || s[i] == '.' || s[i] == 'e' || s[i] == 'E' || s[i] == '+' || s[i] == '-')) ++i;
    return i > b;
  }
  bool valid() { bool ok = value(); ws(); return ok && i == s.size(); }
};
static bool validJson(const std::string &s) { JsonCheck c{s}; return c.valid(); }

static driver::AnalysisOptions optionsFor(const std::string &core, const std::string &spec, const std::string &entry, bool libc) {
  driver::AnalysisOptions o;
  o.coreText = core;
  o.coreName = entry + ".core";
  o.specText = spec;
  o.specName = entry + ".yaml";
  o.entry = entry;
  if (libc) o.libcText = slurp(HLIR_MODELS_DIR "/libc.core");
  return o;
}

// ---------------------------------------------------------------- report content and formats
static void testReport() {
  std::string core = slurp(HLIR_ENTRY_DIR "/copy_if_small.core"), yaml = slurp(HLIR_ENTRY_DIR "/copy_if_small.yaml");
  auto out = driver::analyzeEntry(optionsFor(core, yaml, "copy_if_small", true));
  CHECK(out.ok, out.error);
  if (!out.ok) return;
  const report::EntryReport &e = out.entry;
  CHECK(e.verdict == report::Verdict::Bug, "verdict bug");
  CHECK(e.findings.size() == 1 && e.findings[0].replay == report::ReplayStatus::Confirmed && e.findings[0].kind == "oob_write", "one confirmed oob_write");
  if (e.findings.empty()) return;
  auto &f = e.findings[0];
  bool hasLen = false, hasSrc = false;
  for (auto &w : f.witness) {
    if (w.name == "len") { hasLen = true; CHECK(w.note == "int", "witness carries the source type: " << w.note); CHECK(w.value[0] == '-' || std::stoll(w.value) > 256, "len cannot be a legal length: " << w.value); }
    if (w.name == "src") hasSrc = true;
  }
  CHECK(hasLen && hasSrc, "counterexample is printed with parameter names");
  std::map<std::string, int> cats;
  for (auto &a : e.assumptions) ++cats[a.category];
  CHECK(cats["init"] == 2 && cats["attacker_model"] == 1 && cats["env_fact"] >= 1 && cats["bound"] == 1, "assumptions list init.*, attacker model, bounds and environment facts");
  bool initLoc = false;
  for (auto &a : e.assumptions) initLoc |= a.category == "init" && a.loc.line == 13 && a.text.find("init.rel.") == 0;
  CHECK(initLoc, "init assumptions point at their spec line");
  CHECK(e.seedSummary.find("len = 64") != std::string::npos, "the benign seed is reported in source terms: " << e.seedSummary);
  CHECK(!e.functionClasses.empty() && e.metrics.runs >= 1 && e.metrics.solverQueries >= 1, "metrics and function classes present");

  report::Report rep;
  rep.entries.push_back(e);
  std::string text = report::toText(rep), json = report::toJson(rep), sarif = report::toSarif(rep);
  CHECK(has(text, "verdict: bug") && has(text, "counterexample:") && has(text, "assumptions:"), "text report sections");
  CHECK(validJson(json), "JSON report is valid JSON");
  CHECK(validJson(sarif), "SARIF report is valid JSON");
  CHECK(has(json, "\"verdict\": \"bug\"") && has(json, "\"replay\": \"confirmed\"") && has(json, "\"assumptions\""), "JSON content");
  CHECK(has(sarif, "\"version\": \"2.1.0\"") && has(sarif, "\"ruleId\": \"oob_write\"") && has(sarif, "\"level\": \"error\"") && has(sarif, "\"partialFingerprints\""), "SARIF content");

  // hostile mode reports more findings; the attacker model assumption changes
  auto hostile = driver::analyzeEntry(optionsFor(core, yaml.substr(0, yaml.find("    relations:")), "copy_if_small", true));
  CHECK(hostile.ok && hostile.entry.findings.size() == 2, "hostile: two findings");
  bool hostileAssumption = false;
  for (auto &a : hostile.entry.assumptions) hostileAssumption |= a.category == "attacker_model" && a.text.find("hostile") == 0;
  CHECK(hostileAssumption, "hostile attacker model is listed as an assumption");

  // a clean entry is "safe under assumptions", never plain "safe"
  const char *clean = "core.func @f(i32) -> i32 {\n^entry(%x: i32):\n  %z = core.const 0 : i32\n  %c = core.icmp eq %x, %z : bool\n  %r = core.select %c, %z, %x : i32\n  core.return %r\n}\n";
  auto safe = driver::analyzeEntry(optionsFor(clean, "taint_entries:\n  - function: f\n    params:\n      x: { taint: value, type: int }\n", "f", false));
  CHECK(safe.ok && safe.entry.verdict == report::Verdict::SafeUnderAssumptions && safe.entry.findings.empty(), "clean entry: safe under assumptions");
  CHECK(has(report::toText(report::Report{"hlir", "0.1", {safe.entry}}), "under the assumptions"), "text says what 'safe' means");

  // contradictory specification: unknown + reason, no crash
  auto bad = driver::analyzeEntry(optionsFor(clean, "taint_entries:\n  - function: f\n    params:\n      x: { taint: value, type: int, range: [0, 10] }\n    relations:\n      - \"x > 20\"\n", "f", false));
  CHECK(bad.ok && bad.entry.verdict == report::Verdict::Unknown && !bad.entry.incomplete.empty() && bad.entry.incomplete[0].code == "spec_contradiction", "contradictory spec is reported, not analysed");
  CHECK(has(bad.entry.incomplete[0].detail, "init.rel.x > 20") && has(bad.entry.incomplete[0].detail, "init.x.range[0,10]"), "the contradiction names the spec lines");
  // bad input is an error, not a verdict
  auto err = driver::analyzeEntry(optionsFor(clean, "taint_entries:\n  - function: f\n    params:\n      nope: { taint: value }\n", "f", false));
  CHECK(!err.ok && has(err.error, "no parameter named 'nope'"), "spec error is returned with its message");
}

// ---------------------------------------------------------------- incompleteness is reported with a code
static void testIncomplete() {
  const char *loop =
      "core.func @f(i32) -> i32 {\n^entry(%n: i32):\n  %z = core.const 0 : i32\n  core.br ^head(%z)\n^head(%i: i32):\n  %c = core.icmp slt %i, %n : bool\n"
      "  core.cond_br %c, ^body, ^exit\n^body:\n  %one = core.const 1 : i32\n  %j = core.add %i, %one : i32\n  core.br ^head(%j)\n^exit:\n  core.return %i\n}\n";
  auto o = optionsFor(loop, "taint_entries:\n  - function: f\n    params:\n      n: { taint: value, type: int }\n", "f", false);
  o.taint.maxRuns = 5;
  auto r = driver::analyzeEntry(o);
  CHECK(r.ok && r.entry.verdict == report::Verdict::Unknown, "a loop bounded by the run limit gives verdict unknown");
  bool code = false;
  for (auto &i : r.entry.incomplete) code |= i.code == "run_limit";
  CHECK(code, "with the reason code run_limit");
  CHECK(has(report::toSarif(report::Report{"hlir", "0.1", {r.entry}}), "\"executionSuccessful\": false"), "SARIF marks the invocation unsuccessful");
}

// ---------------------------------------------------------------- corpus: detection, false positives, replay-confirmation rate
static void testCorpus() {
  std::vector<std::string> files;
  if (DIR *d = opendir(HLIR_CORPUS_DIR)) {
    while (auto *e = readdir(d)) {
      std::string n = e->d_name;
      if (n.size() > 5 && n.substr(n.size() - 5) == ".core") files.push_back(n);
    }
    closedir(d);
  }
  std::sort(files.begin(), files.end());
  int bad = 0, detected = 0, good = 0, falsePos = 0, confirmed = 0, unconfirmed = 0, unlabelled = 0, errors = 0;
  uint64_t cacheHits = 0, queries = 0;
  double seconds = 0;
  std::map<std::string, int> reasons;
  for (auto &fn : files) {
    std::string text = slurp(std::string(HLIR_CORPUS_DIR) + "/" + fn), expect, entry = "f";
    bool libc = false;
    std::istringstream ls(text);
    for (std::string line; std::getline(ls, line);) {
      if (line.rfind("// EXPECT: ", 0) == 0) expect = line.substr(11);
      else if (line == "// LIBC") libc = true;
    }
    size_t fpos = text.find("core.func @f(");
    size_t pn = text.find("^entry(%", fpos);
    std::string pname = text.substr(pn + 8, text.find(':', pn) - pn - 8);
    auto o = optionsFor(text, "taint_entries:\n  - function: f\n    label: input\n    params:\n      " + pname + ": { taint: value, type: int }\n", entry, libc);
    o.coreName = fn;
    o.taint.promoteAll = true;  // symbolic environment: allocation failure is attacker-reachable too
    o.taint.maxRuns = 300;
    auto r = driver::analyzeEntry(o);
    if (!r.ok) { std::cerr << fn << ": " << r.error; ++errors; continue; }
    seconds += r.entry.metrics.secondsTotal;
    cacheHits += r.entry.metrics.cacheHits;
    queries += r.entry.metrics.solverQueries;
    bool found = false;
    for (auto &f : r.entry.findings) {
      if (f.replay == report::ReplayStatus::Confirmed) { ++confirmed; found |= f.kind == expect; }
      else { ++unconfirmed; ++reasons[f.unconfirmedReason]; if (f.unconfirmedReason.empty()) ++unlabelled; }
    }
    if (expect == "none") {
      ++good;
      bool fp = false;
      for (auto &f : r.entry.findings) fp |= f.replay == report::ReplayStatus::Confirmed;
      if (fp) { ++falsePos; std::cerr << fn << ": false positive\n"; }
      CHECK(r.entry.verdict != report::Verdict::Bug, fn << ": good program must not get verdict bug");
    } else {
      ++bad;
      if (found) ++detected; else std::cerr << fn << ": missed " << expect << "\n";
      CHECK(r.entry.verdict == report::Verdict::Bug || !found, fn << ": verdict");
    }
  }
  double rate = confirmed + unconfirmed ? 100.0 * confirmed / (confirmed + unconfirmed) : 100.0;
  std::cout << "  corpus via hlir-taint pipeline: " << files.size() << " programs, detection " << detected << "/" << bad << ", false positives " << falsePos << "/" << good
            << ", replay-confirmation " << confirmed << "/" << (confirmed + unconfirmed) << " = " << rate << "%, " << queries << " solver queries (" << cacheHits << " cache hits), "
            << seconds << "s total, " << seconds / std::max<size_t>(files.size(), 1) << "s/program\n";
  for (auto &kv : reasons) std::cout << "    unconfirmed because " << kv.first << ": " << kv.second << "\n";
  CHECK(errors == 0, "all corpus programs analysed");
  CHECK(rate >= 90.0, "replay-confirmation rate " << rate);
  CHECK(unlabelled == 0, "every unconfirmed finding carries a reason");
  CHECK(bad > 0 && detected * 100 >= bad * 90, "detection >= 90%: " << detected << "/" << bad);
  CHECK(falsePos * 100 <= good * 5, "false positives <= 5%: " << falsePos << "/" << good);
}

// ---------------------------------------------------------------- precision escalation and timeout layering
static void testEscalation() {
  std::string core = slurp(HLIR_ENTRY_DIR "/copy_if_small.core"), yaml = slurp(HLIR_ENTRY_DIR "/copy_if_small.yaml");
  auto o = optionsFor(core, yaml, "copy_if_small", true);
  auto withEsc = driver::analyzeEntry(o);
  o.escalate = false;
  auto noEsc = driver::analyzeEntry(o);
  auto cat = [](const driver::AnalysisOutcome &r, const char *c) { int n = 0; for (auto &a : r.entry.assumptions) n += a.category == c; return n; };
  CHECK(cat(withEsc, "concretized_pointer") == 1 && withEsc.entry.metrics.pathsExplored > 0, "concretised addresses trigger the symbolic engine and are listed as an assumption");
  CHECK(cat(noEsc, "concretized_pointer") == 0 && noEsc.entry.metrics.pathsExplored == 0, "escalation can be disabled");
  CHECK(withEsc.entry.verdict == noEsc.entry.verdict && withEsc.entry.findings.size() == noEsc.entry.findings.size(), "both reach the same verdict here");

  // timeout layering: a 1ms first attempt, a generous retry; the verdict must not change
  auto l = optionsFor(core, yaml, "copy_if_small", true);
  l.taint.fastTimeoutMs = 1;
  l.taint.slowTimeoutMs = 20000;
  auto layered = driver::analyzeEntry(l);
  CHECK(layered.ok && layered.entry.verdict == report::Verdict::Bug && layered.entry.findings.size() == 1, "timeout layering keeps the verdict");
  std::cout << "  timeout layering: " << layered.entry.metrics.escalations << " escalation(s)\n";
}

// ---------------------------------------------------------------- unconfirmed findings carry a reason and downgrade the verdict
static void testUnconfirmed() {
  const char *core =
      "core.func @validate(i32) -> i32 {\n^entry(%len: i32):\n  %max = core.const 100 : i32\n  %zero = core.const 0 : i32\n  %big = core.icmp sgt %len, %max : bool\n"
      "  %neg = core.icmp slt %len, %zero : bool\n  %bad = core.or %big, %neg : bool\n  core.cond_br %bad, ^rej, ^ok\n^rej:\n  %m1 = core.const -1 : i32\n  core.return %m1\n^ok:\n  core.return %zero\n}\n"
      "core.func @f(i32) -> i32 {\n^entry(%len: i32):\n  %r = core.call @validate(%len) : i32\n  %zero = core.const 0 : i32\n  %rej = core.icmp slt %r, %zero : bool\n"
      "  core.cond_br %rej, ^out, ^go\n^out:\n  core.return %r\n^go:\n  %n = core.const 256 : i64\n  %buf = core.heap_alloc %n {fail=never} : ptr\n  %w = core.sext %len : i64\n"
      "  core.check.ptr_arith %buf, %w loc(\"v.c\":9:3)\n  core.return %zero\n}\n";
  const char *spec = "taint_entries:\n  - function: f\n    params:\n      len: { taint: value, type: int }\n";
  auto ok = driver::analyzeEntry(optionsFor(core, spec, "f", false));
  CHECK(ok.ok && ok.entry.verdict == report::Verdict::SafeUnderAssumptions, "validate protects the sink: safe under assumptions");
  auto o = optionsFor(core, spec, "f", false);
  o.taint.dropPcsAboveDepth = 1;  // regression aid: forget the callee's constraints => spurious finding
  auto r = driver::analyzeEntry(o);
  CHECK(r.ok && r.entry.verdict == report::Verdict::Unknown, "a finding that replay refutes yields verdict unknown, not bug");
  // with the callee constraint dropped the index also loses its constant bound, so a tainted_index warning appears too
  std::vector<report::Finding> ub;
  for (auto &f : r.entry.findings) if (!f.warning) ub.push_back(f);
  CHECK(ub.size() == 1 && ub[0].replay == report::ReplayStatus::NotReproduced, "it is listed as not reproduced");
  if (!ub.empty()) CHECK(ub[0].unconfirmedReason == "replay_no_ub", "with a reason label: " << ub[0].unconfirmedReason);
  bool inc = false;
  for (auto &i : r.entry.incomplete) inc |= i.code == "unconfirmed_findings";
  CHECK(inc, "and an incompleteness note");
  std::string sarif = report::toSarif(report::Report{"hlir", "0.1", {r.entry}});
  CHECK(validJson(sarif) && has(sarif, "\"level\": \"note\"") && has(sarif, "replay_no_ub"), "SARIF reports it as a note with the reason");
}

// ---------------------------------------------------------------- call-graph visualisation (--format dot)
// A small call chain f -> parse_input -> {log_message, validate -> (feeds) -> process}, where `len` is the tainted
// entry parameter: parse_input calls an unrelated, argument-free log_message() (never touches tainted data) and also
// routes `len` through validate() (an identity pass-through) into process(), which does an out-of-bounds pointer
// check on a 64-byte buffer using the (now attacker-controlled) length: a real, replay-confirmed memory-safety bug.
static void testDot() {
  const char *core =
      "core.func @log_message() -> void {\n^entry:\n  core.return\n}\n"
      "core.func @validate(i32) -> i32 {\n^entry(%len: i32):\n  core.return %len\n}\n"
      "core.func @process(i32) -> void {\n^entry(%len: i32):\n  %n = core.const 64 : i64\n  %buf = core.heap_alloc %n {fail=never} : ptr\n"
      "  %w = core.sext %len : i64\n  core.check.ptr_arith %buf, %w loc(\"demo.c\":9:3)\n  core.return\n}\n"
      "core.func @parse_input(i32) -> void {\n^entry(%len: i32):\n  core.call @log_message()\n  %r = core.call @validate(%len) : i32\n"
      "  core.call @process(%r)\n  core.return\n}\n"
      "core.func @f(i32) -> i32 {\n^entry(%len: i32):\n  core.call @parse_input(%len)\n  %zero = core.const 0 : i32\n  core.return %zero\n}\n";
  const char *spec = "taint_entries:\n  - function: f\n    params:\n      len: { taint: value, type: int }\n";
  auto out = driver::analyzeEntry(optionsFor(core, spec, "f", false));
  CHECK(out.ok, out.error);
  if (!out.ok) return;
  const report::EntryReport &e = out.entry;
  CHECK(e.verdict == report::Verdict::Bug, "the OOB check in @process is a real, replay-confirmed bug");
  CHECK(!e.findings.empty() && e.findings[0].callStack.size() >= 2 && e.findings[0].callStack.back() == "process",
        "the finding's call stack reaches @process");

  // function-level classification: log_message must stay inert (no tainted data ever reaches it)
  bool logInert = false, validateTransformer = false;
  for (auto &c : e.functionClasses) {
    if (c.function == "log_message") logInert = c.inert == c.calls && c.observer == 0 && c.transformer == 0 && c.source == 0;
    if (c.function == "validate") validateTransformer = c.transformer > 0;
  }
  CHECK(logInert, "log_message is classified inert (it never touches tainted data)");
  CHECK(validateTransformer, "validate is classified transformer (it returns the tainted length unchanged)");

  // call-graph edges: not empty, not a complete graph (some edge must be untainted), and specifically log_message's
  // incoming edge is the untainted one while parse_input -> process is tainted (the path to the actual bug).
  CHECK(!e.callEdges.empty(), "call edges were recorded");
  bool sawLogEdge = false, logEdgeTainted = true, sawProcessEdge = false, processEdgeTainted = false, sawValidateEdge = false, validateEdgeTainted = false;
  unsigned taintedEdges = 0;
  for (auto &c : e.callEdges) {
    if (c.tainted) ++taintedEdges;
    if (c.caller == "parse_input" && c.callee == "log_message") { sawLogEdge = true; logEdgeTainted = c.tainted; }
    if (c.caller == "parse_input" && c.callee == "process") { sawProcessEdge = true; processEdgeTainted = c.tainted; }
    if (c.caller == "parse_input" && c.callee == "validate") { sawValidateEdge = true; validateEdgeTainted = c.tainted; }
  }
  CHECK(sawLogEdge && !logEdgeTainted, "parse_input -> log_message is not marked tainted");
  CHECK(sawProcessEdge && processEdgeTainted, "parse_input -> process is marked tainted (it carries the bug)");
  CHECK(sawValidateEdge && validateEdgeTainted, "parse_input -> validate is marked tainted (it carries the length through)");
  CHECK(taintedEdges > 0 && taintedEdges < e.callEdges.size(), "the graph is neither empty nor all-red: " << taintedEdges << "/" << e.callEdges.size());

  // the rendered DOT text: real digraph, red attributes exactly on the tainted edges, not on log_message's edge
  report::Report rep;
  rep.entries.push_back(e);
  std::string dot = report::toDot(rep);
  CHECK(has(dot, "digraph callgraph {"), "DOT text is a digraph");
  CHECK(has(dot, "\"process\" [label=\"process\"];") || has(dot, "\"process\""), "process node is present");
  CHECK(has(dot, "\"parse_input\" -> \"process\" [label=") && has(dot, "color=red"), "a tainted edge is drawn with color=red");
  // the log_message edge line itself must not carry color=red
  {
    std::istringstream ls(dot);
    bool found = false, clean = true;
    for (std::string line; std::getline(ls, line);) {
      if (line.find("\"parse_input\" -> \"log_message\"") != std::string::npos) { found = true; clean = line.find("color=red") == std::string::npos; }
    }
    CHECK(found, "parse_input -> log_message edge is present in the DOT text");
    CHECK(clean, "and it is not colored red: " << dot);
  }
  CHECK(has(dot, "penwidth=2"), "tainted edges are also drawn bold");

  // an empty report (no callEdges, e.g. a pure-text EntryReport from before this field existed) renders no digraph
  report::EntryReport empty;
  report::Report emptyRep;
  emptyRep.entries.push_back(empty);
  CHECK(report::toDot(emptyRep).empty(), "no call edges => no DOT output");
}

// ---------------------------------------------------------------- DoS warnings: tainted loop bound / tainted index
static unsigned countWarn(const report::EntryReport &e, const std::string &kind) {
  unsigned n = 0;
  for (auto &f : e.findings) n += (f.warning && f.kind == kind) ? 1 : 0;
  return n;
}
static void testDosWarnings() {
  const char *spec = "taint_entries:\n  - function: %s\n    params:\n      k: { taint: value, type: int }\n";
  auto specFor = [&](const char *fn) { char b[256]; std::snprintf(b, sizeof b, spec, fn); return std::string(b); };

  // 1. the attacker decides how many times a loop runs: one warning at the loop's controlling branch, and since
  //    there is no undefined behaviour the verdict is not `bug`
  const char *loop =
      "core.func @loop(i32) -> i32 {\n^entry(%k: i32):\n  %z = core.const 0 : i32\n  core.br ^h(%z)\n"
      "^h(%i: i32):\n  %c = core.icmp ult %i, %k : bool loc(\"d.c\":2:3)\n  core.cond_br %c, ^b, ^x loc(\"d.c\":2:3)\n"
      "^b:\n  %one = core.const 1 : i32\n  %i2 = core.add %i, %one : i32\n  core.br ^h(%i2)\n^x:\n  core.return %i\n}\n";
  auto lo = optionsFor(loop, specFor("loop"), "loop", false);
  lo.loopBound = 4;
  auto l = driver::analyzeEntry(lo);
  CHECK(l.ok, l.error);
  CHECK(countWarn(l.entry, "tainted_loop_bound") == 1, "a tainted loop bound raises exactly one tainted_loop_bound warning");
  CHECK(l.entry.verdict != report::Verdict::Bug, "a warning alone never makes the verdict a bug, got " << report::verdictName(l.entry.verdict));
  CHECK(has(report::toText(report::Report{"hlir", "0.1", {l.entry}}), "warning: tainted_loop_bound"), "the text report labels it as a warning");
  CHECK(has(report::toSarif(report::Report{"hlir", "0.1", {l.entry}}), "\"level\": \"warning\""), "SARIF reports it at level warning");
  report::Report back;
  std::string err;
  CHECK(report::fromJson(report::toJson(report::Report{"hlir", "0.1", {l.entry}}), back, err) && !back.entries.empty() &&
            countWarn(back.entries[0], "tainted_loop_bound") == 1, "the warning flag survives a JSON round trip " << err);

  // 2. an attacker-controlled index with no bound at all: a tainted_index warning (next to the real overflow)
  const char *idx =
      "core.func @idx(i32) -> i32 {\n^entry(%k: i32):\n  %n = core.const 256 : i64\n  %buf = core.heap_alloc %n {fail=never} : ptr\n"
      "  %w = core.zext %k : i64\n  core.check.ptr_arith %buf, %w loc(\"d.c\":5:3)\n  %z = core.const 0 : i32\n  core.return %z\n}\n";
  auto ix = driver::analyzeEntry(optionsFor(idx, specFor("idx"), "idx", false));
  CHECK(ix.ok, ix.error);
  CHECK(countWarn(ix.entry, "tainted_index") == 1, "an unbounded tainted index raises a tainted_index warning");

  // 3. the same index behind a fixed-range check (k < 200): a constant upper bound is in force -> no warning, safe
  const char *chk =
      "core.func @chk(i32) -> i32 {\n^entry(%k: i32):\n  %max = core.const 200 : i32\n  %z = core.const 0 : i32\n"
      "  %big = core.icmp uge %k, %max : bool\n  core.cond_br %big, ^rej, ^ok\n^rej:\n  core.return %z\n"
      "^ok:\n  %n = core.const 256 : i64\n  %buf = core.heap_alloc %n {fail=never} : ptr\n  %w = core.zext %k : i64\n"
      "  core.check.ptr_arith %buf, %w loc(\"d.c\":9:3)\n  core.return %z\n}\n";
  auto ck = driver::analyzeEntry(optionsFor(chk, specFor("chk"), "chk", false));
  CHECK(ck.ok, ck.error);
  CHECK(countWarn(ck.entry, "tainted_index") == 0, "a constant upper bound sanitizes the index: no warning");
  CHECK(ck.entry.verdict == report::Verdict::SafeUnderAssumptions, "and the entry is safe, got " << report::verdictName(ck.entry.verdict));

  // 4. computeVerdict: a confirmed warning-only entry stays safe
  report::EntryReport e;
  report::Finding w;
  w.kind = "tainted_index"; w.warning = true; w.replay = report::ReplayStatus::Confirmed;
  e.findings.push_back(w);
  CHECK(report::computeVerdict(e) == report::Verdict::SafeUnderAssumptions, "computeVerdict ignores warnings");
}

int main() {
  testReport();
  testIncomplete();
  testUnconfirmed();
  testDot();
  testCorpus();
  testEscalation();
  testDosWarnings();
  std::cout << "report_tests: " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}

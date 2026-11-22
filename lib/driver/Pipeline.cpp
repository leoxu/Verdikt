#include "hlir/driver/Pipeline.h"

#include <cstring>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <chrono>
#include <iostream>
#include <map>
#include <set>
#include <tuple>

#include "llvm/ADT/SmallString.h"

#include "hlir/entry/HarnessGen.h"
#include "hlir/model/Model.h"
#include "hlir/entry/SeedSolver.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/Symbolic.h"
#include "hlir/semantics/BarrenBranch.h"

namespace hlir::driver {

namespace {

using Clock = std::chrono::steady_clock;
double secondsSince(Clock::time_point t) { return std::chrono::duration<double>(Clock::now() - t).count(); }

report::Location toLoc(const Loc &l) { return {l.file, l.line, l.col}; }

// "…@file:line" suffix of a constraint name -> location
report::Location specLoc(const std::string &name) {
  auto at = name.rfind('@');
  if (at == std::string::npos) return {};
  std::string rest = name.substr(at + 1);
  auto colon = rest.rfind(':');
  if (colon == std::string::npos) return {};
  try { return {rest.substr(0, colon), static_cast<unsigned>(std::stoul(rest.substr(colon + 1))), 1}; } catch (...) { return {}; }
}

std::string numStr(const llvm::APInt &v, bool isSigned) {
  llvm::SmallString<40> s;
  if (isSigned) v.toStringSigned(s); else v.toStringUnsigned(s);
  return std::string(s);
}

std::string hexByte(const llvm::APInt &v) {
  static const char *d = "0123456789abcdef";
  uint64_t x = v.getZExtValue() & 0xff;
  return std::string(1, d[x >> 4]) + d[x & 15];
}

// Source-level rendering of a counterexample: parameters by name and C type, objects by size and non-zero bytes.
struct WitnessPrinter {
  const entry::InitPlan &plan;
  const entry::EntrySpec &spec;
  // name -> what that nondet is (DESIGN.md §22.369). A witness line reading `foo.asm5 = 0` tells a reader nothing;
  // a reproduction has to reproduce these choices or it takes a different path.
  const std::map<std::string, NondetOrigin> *nondetOrigins = nullptr;
  // parameter name -> runtime memory-object id, filled from generateHarness(). Empty until the harness has been
  // generated (the seed summary prints no object bytes, so it does not need it).
  std::map<std::string, unsigned> objId;

  const entry::ParamSpec *specOf(const std::string &n) const {
    for (auto &p : spec.params)
      if (p.name == n) return &p;
    return nullptr;
  }
  std::string typeName(const entry::PlannedParam &p) const {
    if (p.isBool) return "bool";
    if (auto *s = specOf(p.name))
      if (!s->type.empty()) return s->type;
    return std::string(p.isSigned ? "i" : "u") + std::to_string(p.width);
  }

  std::vector<report::WitnessItem> print(const std::vector<std::string> &names, const std::vector<llvm::APInt> &vals,
                                         const std::map<std::string, llvm::APInt> &inputs) const {
    std::vector<report::WitnessItem> out;
    std::map<std::string, llvm::APInt> byName;
    for (size_t i = 0; i < names.size() && i < vals.size(); ++i) byName.emplace(names[i], vals[i]);
    // The SYMBOLIC engine creates the entry's parameters through SymbolicDomain's nondet path, which names them
    // `nd.<base>.<counter>` instead of the concolic `<base>` the plan uses. Every lookup below ("p.<name>",
    // "size.<name>", "null.<name>") therefore missed, and a symbolic-engine witness printed its object size as
    // blank and its scalars as anonymous `nondet` rows -- which is how tcpdump CVE-2017-12902 came back
    // `replay: confirmed` with a witness nobody could rebuild (DESIGN.md §22.417). Fold the prefixed names back
    // onto their base before anything reads them; the concolic names, when present, win.
    for (size_t i = 0; i < names.size() && i < vals.size(); ++i) {
      const std::string &n = names[i];
      if (n.rfind("nd.", 0) != 0) continue;
      size_t dot = n.rfind('.');
      if (dot == std::string::npos || dot <= 2) continue;
      if (n.find_first_not_of("0123456789", dot + 1) != std::string::npos) continue;  // tail must be the counter
      byName.emplace(n.substr(3, dot - 3), vals[i]);
    }
    for (auto &p : plan.params) {
      if (p.kind == entry::PlannedParam::Scalar) {
        if (!p.tainted) continue;
        auto it = byName.find("p." + p.name);
        if (it == byName.end()) continue;
        out.push_back({p.name, p.isBool ? (it->second.isZero() ? "false" : "true") : numStr(it->second, p.isSigned), typeName(p)});
        continue;
      }
      std::string size = p.size->kind == smt::Kind::BvConst ? numStr(p.size->value, false) : "";
      auto sz = byName.find("size." + p.name);
      if (sz != byName.end()) size = numStr(sz->second, false);
      auto nl = byName.find("null." + p.name);
      if (nl != byName.end() && !nl->second.isZero()) { out.push_back({p.name, "NULL", "pointer"}); continue; }
      std::string desc = "object of " + size + " bytes";
      // The bytes are shown for an attacker-controlled object AND for one whose content the harness invented
      // (`content: unknown`, DESIGN.md §22.381). Leaving the second out would print "object of 8 bytes" for a
      // session whose `magic` field is exactly what made the path feasible -- a witness missing the half of the
      // state a reader needs to understand why the gate opened.
      if (p.tainted || p.unknownContent) {
        // The object id comes from the harness itself (generateHarness fills `objId`). It used to be guessed as the
        // parameter's position among the buffer parameters, which is wrong as soon as an earlier parameter has
        // synthesised pointer fields: those sub-objects are allocated in between, so every later parameter's bytes
        // were looked up under some other object's name and silently rendered as "all bytes 0" -- a confirmed
        // finding could print a witness that cannot reach it (DESIGN.md §22.351, found on fs/jfs dbJoin).
        auto oi = objId.find(p.name);
        size_t id = oi == objId.end() ? 0 : oi->second;
        std::map<uint64_t, uint8_t> bytes;
        std::string prefix = (p.tainted ? "in.o" : "in.un.o") + std::to_string(id) + "+";
        for (auto &kv : inputs)
          if (kv.first.rfind(prefix, 0) == 0 && !kv.second.isZero()) bytes[std::stoull(kv.first.substr(prefix.size()))] = static_cast<uint8_t>(kv.second.getZExtValue());
        if (bytes.empty()) desc += ", all bytes 0";
        else {
          // The cap used to be 16, and that quietly made a `replay: confirmed` finding UNREPRODUCIBLE outside
          // the engine: the tcpdump CVE-2017-12902 witness had 40 non-zero bytes, so the report showed 16 and
          // "(+24 more)" and no reader -- no ASan ground-truth step -- could rebuild the input that reaches the
          // defect (DESIGN.md §22.417). A witness that cannot be replayed by hand is not evidence. The cap is
          // now 512, which covers every harness buffer we scan (`--buf-max` is tens of bytes) while still
          // bounding the line for a pathological `max_obj`-sized object.
          constexpr unsigned kMaxShown = 512;
          desc += ", non-zero bytes:";
          unsigned shown = 0;
          for (auto &b : bytes) {
            if (shown++ == kMaxShown) {
              desc += " ... (+" + std::to_string(bytes.size() - kMaxShown) + " more, WITNESS TRUNCATED)";
              break;
            }
            desc += " [" + std::to_string(b.first) + "]=" + hexByte(llvm::APInt(8, b.second));
          }
        }
      }
      out.push_back({p.name, desc, p.kind == entry::PlannedParam::CString ? "cstring" : "buffer"});
    }
    // anything else the model fixed (untracked nondets such as allocation failures)
    for (size_t i = 0; i < names.size() && i < vals.size(); ++i) {
      const std::string &n = names[i];
      if (n.rfind("p.", 0) == 0 || n.rfind("size.", 0) == 0 || n.rfind("null.", 0) == 0) continue;
      // ... and the same three under the symbolic engine's `nd.<base>.<counter>` spelling, which the fold above
      // has already printed as a typed parameter row. Without this they came out twice, once anonymously.
      if (n.rfind("nd.p.", 0) == 0 || n.rfind("nd.size.", 0) == 0 || n.rfind("nd.null.", 0) == 0) continue;
      std::string note = "nondet";
      if (nondetOrigins) {
        auto it = nondetOrigins->find(n);
        if (it != nondetOrigins->end()) {
          note = it->second.what.empty() ? std::string("nondet") : it->second.what;
          if (!it->second.function.empty()) note += " in @" + it->second.function;
          if (it->second.loc.valid()) note += " at " + it->second.loc.file + ":" + std::to_string(it->second.loc.line);
        }
      }
      out.push_back({n, numStr(vals[i], false), note});
    }
    return out;
  }
};

struct Key {
  std::string fn, op, kind;
  unsigned line;
  bool operator<(const Key &o) const { return std::tie(fn, op, kind, line) < std::tie(o.fn, o.op, o.kind, o.line); }
};

}  // namespace

static AnalysisOutcome analyzeOnce(const AnalysisOptions &opt);

size_t maxMissedBranchesPerEntry() {
  static const size_t kMaxMissed = [] {
    const char *e = getenv("HLIR_MAX_MISSED_BRANCHES");
    return e ? static_cast<size_t>(strtoul(e, nullptr, 10)) : size_t{50000};
  }();
  return kMaxMissed;
}


// What the runs executed: block coverage over the functions reachable through direct calls from the entry harness.
// `symBlocks`: block-coverage from the symbolic precision-escalation pass (empty if it did not run). The concolic engine
// follows tainted pointers concretely, so it alone can under-report coverage of an entry the symbolic pass actually
// explored; merging the two avoids a spurious `low_coverage`/`no_run_completed` on an entry that precision-escalation did
// cover.
// `edgeKeys` / `blockKeys`, when given, collect what this pass covered under names that survive a re-parse
// ("fn#blockIdx:opIdx/dir"). A multi-pass analysis (the G2 fixpoint, the loop-bound ladder, the setup fallback,
// auto-targeting) otherwise reports the LAST pass's coverage as if it were the whole search's, which understates
// every one of them -- see DESIGN.md §22.415.
static report::Coverage computeCoverage(const Module &m, const std::string &harness, const TaintResult &tr, const std::vector<TerminationSite> &sites, WitnessPrinter &wp,
                                         const std::set<const Block *> &symBlocks = {},
                                         std::set<std::string> *edgeKeys = nullptr,
                                         std::set<std::string> *blockKeys = nullptr,
                                         bool wantMissedBranches = false) {
  // Stable across re-parses: a pointer is not, and the passes do not share a Module.
  auto blockKey = [](const Block *b) {
    if (!b || !b->parent) return std::string();
    for (size_t i = 0; i < b->parent->blocks.size(); ++i)
      if (b->parent->blocks[i].get() == b) return b->parent->name + "#" + std::to_string(i);
    return std::string();
  };
  auto opKey = [&](const Op *o) {
    if (!o || !o->parent) return std::string();
    std::string bk = blockKey(o->parent);
    if (bk.empty()) return std::string();
    for (size_t i = 0; i < o->parent->ops.size(); ++i)
      if (o->parent->ops[i].get() == o) return bk + ":" + std::to_string(i);
    return std::string();
  };
  report::Coverage c;
  c.measured = true;
  const Function *h = m.findFunction(harness);
  if (!h) return c;
  // The denominator is the ENTRY's call graph, not the harness's (DESIGN.md §22.376). The harness may also call a
  // session constructor and the project's own initialiser before it calls the entry, and `main` reaches most of a
  // module: seeding the walk at the harness made every post-`init:` scan's coverage a fraction with the wrong
  // denominator (<driver> devctl: 594 reachable blocks without `init:`, 2194 with -- the same handler, a quarter of
  // the percentage). `hlir.entry.begin` is the harness's own marker for where setup ends; calls before it are
  // setup, calls after it are the entry. A helper shared by the initialiser and the handler still counts, because
  // the entry's own call graph reaches it.
  std::vector<const Function *> work;
  {
    bool afterEntry = false, sawMarker = false;
    for (auto &b : h->blocks)
      for (auto &op : b->ops) {
        if (op->opc == Opc::Trace) {
          if (const Attr *ev = op->attr("event"))
            if (ev->s == "hlir.entry.begin") { afterEntry = true; sawMarker = true; }
          continue;
        }
        if (afterEntry && op->opc == Opc::Call)
          if (const Function *g = m.findFunction(op->sym))
            if (!g->isDeclaration()) work.push_back(g);
      }
    // A harness built before the marker existed, or by a test that writes IR directly, has no setup phase to
    // exclude: fall back to the old behaviour rather than reporting an empty denominator.
    if (!sawMarker)
      for (auto &b : h->blocks)
        for (auto &op : b->ops)
          if (op->opc == Opc::Call)
            if (const Function *g = m.findFunction(op->sym))
              if (!g->isDeclaration()) work.push_back(g);
  }
  std::set<const Function *> reach(work.begin(), work.end());
  while (!work.empty()) {
    const Function *f = work.back();
    work.pop_back();
    for (auto &b : f->blocks)
      for (auto &op : b->ops)
        if (op->opc == Opc::Call)
          if (const Function *g = m.findFunction(op->sym))
            if (!g->isDeclaration() && reach.insert(g).second) work.push_back(g);
  }
  std::set<const Function *> entered;
  std::set<const Block *> visited = tr.blocksVisited;
  visited.insert(symBlocks.begin(), symBlocks.end());
  // The source lines some run actually executed (diagnostic; seam③ uncovered-bucket at BLOCK grain). entered_functions
  // is function-grain and misses a check behind a guard inside a function the search entered but never reached that
  // branch of; this is the finer signal: a backward SAFE proof whose line is not here sits in a block no run visited.
  std::set<std::string> covLines;
  // ... and the numerator has to be the same population, or a prologue block executed would be counted against a
  // denominator that no longer contains its function, and coverage could exceed 100%.
  for (const Block *b : visited)
    if (b->parent && b->parent != h && reach.count(b->parent)) {
      entered.insert(b->parent);
      ++c.blocksVisited;
      if (blockKeys) { std::string k = blockKey(b); if (!k.empty()) blockKeys->insert(k); }
      for (auto &op : b->ops)
        if (!op->loc.file.empty()) covLines.insert(op->loc.file + ":" + std::to_string(op->loc.line));
    }
  c.coveredLines.assign(covLines.begin(), covLines.end());
  // ENGINE-GENERATED symbols are excluded by the same rule DESIGN.md Sec.22.415 applied to the call
  // frontier: `@__hlir_init.str7` replays a string literal's static initialiser and `@__hlir_indirect.<sig>`
  // stands in for an indirect call -- neither is the program, and a direction never taken in one is not a
  // statement about the code under test. On Redis's sdssplitargs they were 14 of 300 directions (4.7%),
  // all classified `unreached`, sitting in the same list as real gaps (DESIGN.md Sec.22.454).
  auto engineSymbol = [](const std::string &n) {
    return n.rfind("__hlir_", 0) == 0 || n.rfind("__str.", 0) == 0 || n.find(".__init") != std::string::npos;
  };
  std::set<const Op *> condBranches;  // core.cond_br ops of the reachable functions (not the harness itself)
  for (const Function *f : reach) {
    c.blocksReachable += f->blocks.size();
    if (engineSymbol(f->name)) continue;
    for (auto &b : f->blocks)
      for (auto &op : b->ops)
        if (op->opc == Opc::CondBr) condBranches.insert(op.get());
  }
  c.branchesReachable = condBranches.size() * 2;  // each contributes a true and a false edge
  for (auto &p : tr.branchesVisited)
    if (condBranches.count(p.first)) {
      ++c.branchesVisited;
      if (edgeKeys) { std::string k = opKey(p.first); if (!k.empty()) edgeKeys->insert(k + (p.second ? "/t" : "/f")); }
    }
  // Diagnostic (HLIR_DEBUG_BRANCHES): the conditional edges inside the entry's own call graph that NO run ever
  // took. A verdict of `safe` with edges in this list is the shape that matters -- either they are genuinely
  // infeasible, or the search frontier was declared exhausted while they were still open, and the two are not
  // distinguishable from the summary numbers alone.
  // Every conditional edge no run took, classified by what the SEARCH observed about it -- not by reading the
  // source, which does not scale and is a guess. The four classes are disjoint and are checked in order of how
  // much they settle (DESIGN.md §22.429):
  //   unreached  the branch op never executed: nothing is known about its condition, the gap is upstream of it
  //   const      it executed, but its condition was never symbolic -- constant in THIS build and harness
  //              (`sizeof(x) < 8`, `LZ4_isLittleEndian()`, a length passed as a literal). Not a search failure,
  //              and it is the reason 100% is usually unattainable rather than merely unreached.
  //   unsat      the solver was asked for this edge and answered UNSAT: infeasible, no budget opens it
  //   global_init  G1 (Sec.22.362) recorded this cond_br as decided by a global's static initial value: the module's
  //              own initialiser never ran, the condition was taken concretely with no fork, and the opposite edge
  //              is therefore unreachable BY CONSTRUCTION. It used to land in `open`, which reads as "needs more
  //              budget" and sent nginx's `usual[]` gap four times the budget for nothing (Sec.22.465). The fix is
  //              `init:`/`--init-fn` (run the real initialiser) or G2 (`--promote-read-globals`), never budget.
  //              It is checked BEFORE `open` on purpose: a flip queued for such a branch degenerates (the solved
  //              model replays divergent), so `open` describes its fate and not its cause. G1's backward walk is
  //              bounded and syntactic, so this class under-reports and never steals a real budget gap it cannot see.
  //   open       a flip was queued and the budget ran out before it reached the front: THE real coverage gap
  {
    std::set<const Block *> blocksSeen = visited;
    for (const Op *b : condBranches) {
      const bool executed = tr.branchesVisited.count({b, false}) || tr.branchesVisited.count({b, true}) ||
                            (b->parent && blocksSeen.count(b->parent));
      for (bool dir : {false, true}) {
        if (tr.branchesVisited.count({b, dir})) continue;
        const char *why = !executed                           ? "unreached"
                          : tr.flipUnsat.count({b, dir})      ? "unsat"
                          : tr.globalGatedSites.count(b)      ? "global_init"
                          : tr.flipOpen.count({b, dir})       ? "open"
                          : !tr.branchSymbolic.count(b)       ? "const"
                                                              : "open";
        if (!std::strcmp(why, "unreached")) ++c.missUnreached;
        else if (!std::strcmp(why, "const")) ++c.missConst;
        else if (!std::strcmp(why, "unsat")) ++c.missUnsat;
        else if (!std::strcmp(why, "global_init")) ++c.missGlobalInit;
        else ++c.missOpen;
        // The cap used to be 400, which is smaller than the thing it exists to explain: a Fluent Bit scan
        // whose link set carries yyjson and msgpack had 3884 uncovered directions, so the dump was a
        // 10% sample in insertion order and the question "which code was never reached" could not be
        // answered from it at all (DESIGN.md §22.445). HLIR_MAX_MISSED_BRANCHES raises or lowers it; the
        // default is large enough for a whole-library link set. It is only written when --dump-branches
        // asked for it, and it is a diagnostic list, so the cost is a vector that is never read by a verdict.
        if (wantMissedBranches && c.branchesMissed.size() < maxMissedBranchesPerEntry()) {
          report::MissedBranch mb;
          mb.file = b->loc.file;
          mb.line = b->loc.line;
          mb.column = b->loc.col;
          mb.function = b->parent && b->parent->parent ? b->parent->parent->name : std::string();
          mb.dir = dir;
          mb.why = why;
          c.branchesMissed.push_back(std::move(mb));
        }
        if (getenv("HLIR_DEBUG_BRANCHES"))
          fprintf(stderr, "[br] never taken (%s): %s:%u:%u -> %s\n", why, b->loc.file.c_str(), b->loc.line,
                  b->loc.col, dir ? "true" : "false");
      }
    }
  }
  for (const Function *f : entered) c.blocksInEntered += f->blocks.size();
  for (const Op *b : condBranches)
    if (b->parent && b->parent->parent && entered.count(b->parent->parent)) c.branchesInEntered += 2;
  c.functionsReachable = reach.size();
  c.functionsEntered = entered.size();
  // The positive entered set by name (diagnostic; seam③ uncovered-bucket). Engine-generated symbols excluded as
  // elsewhere -- they are not the program's functions.
  for (const Function *f : entered)
    if (!engineSymbol(f->name)) c.enteredFunctions.push_back(f->name);
  std::sort(c.enteredFunctions.begin(), c.enteredFunctions.end());
  // The call frontier: functions one call edge away from code some run entered. ENGINE-GENERATED symbols are
  // excluded by the same rule the global target set uses above -- `@__hlir_init.strN` replays a string literal's
  // static initialiser and is not the program. Before this filter the list was mostly those: on a libyaml scan
  // all twenty shown entries were `__hlir_init.str*`, which pushed every real function past the cap and made the
  // field useless exactly where it matters (DESIGN.md §22.415).
  std::set<const Function *> frontierFns;
  for (const Function *f : entered)
    for (auto &b : f->blocks)
      for (auto &op : b->ops)
        if (op->opc == Opc::Call)
          if (const Function *g = m.findFunction(op->sym))
            if (!g->isDeclaration() && !entered.count(g) && g != h && !engineSymbol(g->name)) frontierFns.insert(g);
  c.notEnteredTotal = frontierFns.size();
  // Ordered so that the functions a defect could actually be IN come first: a never-entered function with no
  // reachable `core.check.*` is a coverage gap and nothing more, and with a cap of 20 it should not be what the
  // reader -- or the auto-target pass -- sees first. Within each group the order stays alphabetical, so the list
  // is still stable between runs.
  const auto hasCheck = computeHasCheck(m);
  std::vector<const Function *> ordered(frontierFns.begin(), frontierFns.end());
  std::stable_sort(ordered.begin(), ordered.end(), [&](const Function *a, const Function *b) {
    auto ca = hasCheck.find(a);
    auto cb = hasCheck.find(b);
    const bool va = ca != hasCheck.end() && ca->second;
    const bool vb = cb != hasCheck.end() && cb->second;
    if (va != vb) return va;
    return a->name < b->name;
  });
  for (const Function *g : ordered) {
    if (c.notEntered.size() >= 20) break;
    c.notEntered.push_back(g->name);
  }
  c.runsReturned = tr.runsReturned;
  c.runsTerminated = tr.runsTerminated;
  for (auto &t : sites) {
    report::TerminationSite r;
    r.function = t.function; r.by = t.by; r.stack = t.stack; r.runs = t.runs;
    r.loc.file = t.loc.file; r.loc.line = t.loc.line; r.loc.col = t.loc.col;
    r.witness = wp.print({}, {}, t.inputs);
    c.terminations.push_back(std::move(r));
  }
  std::stable_sort(c.terminations.begin(), c.terminations.end(), [](const report::TerminationSite &a, const report::TerminationSite &b) { return a.runs > b.runs; });
  if (c.terminations.size() > 40) c.terminations.resize(40);
  return c;
}

// Strips the generated `setup:` line from a spec: used when the session constructor turns out not to be runnable
// here, so the entry is analysed with the field-by-field session instead of not at all (DESIGN.md §22.371).
static std::string withoutSetup(const std::string &spec) {
  std::string out;
  size_t i = 0;
  while (i < spec.size()) {
    size_t e = spec.find('\n', i);
    std::string line = spec.substr(i, e == std::string::npos ? std::string::npos : e - i);
    if (line.find("setup:") == std::string::npos) out += line + "\n";
    if (e == std::string::npos) break;
    i = e + 1;
  }
  return out;
}

static AnalysisOutcome analyzeEntryPasses(const AnalysisOptions &opt, std::set<std::string> &accE, std::set<std::string> &accB) {
  // Every pass this function runs contributes to the SAME coverage union: the caller reports that union, not the
  // last pass's numbers (DESIGN.md §22.415).
  auto analyzeOnce = [&](const AnalysisOptions &o) {
    AnalysisOutcome r = ::hlir::driver::analyzeOnce(o);
    accE.insert(r.edgeKeys.begin(), r.edgeKeys.end());
    accB.insert(r.blockKeys.begin(), r.blockKeys.end());
    return r;
  };
  // Two-pass G2 (DESIGN.md §22.374): measure the read set, then re-run promoting exactly the globals in it that
  // the program never wrote. Done here, as a second visible analysis, for the same reason the session-constructor
  // fallback is: the alternative is a silent half-state.
  if (opt.promoteReadGlobals && !opt.promoteGlobals) {
    // The read set is only as complete as the pass that measured it, and promotion CHANGES which code runs: a
    // global's integer field gates a branch, promoting it opens the branch, and only then does the code behind
    // it read a second field that pass 1 never saw. One probe therefore under-promotes systematically, and in a
    // driver it under-promotes exactly the fields that matter -- a magic word first, the state behind it second.
    // Measured on <driver>: pass 1 saw 4 offsets of `s_AttrInfo` (the magic), the run after it saw 12 (the
    // magic plus `hal_ctx`), and the 8 bytes of `hal_ctx` were never promoted, so `if (hal_ctx == NULL)` closed
    // and the handler's own command dispatcher stayed unreachable (DESIGN.md §22.382).
    //
    // So iterate to a fixpoint instead: probe, promote what was read, probe again with that promotion, until the
    // set stops growing. Bounded, because each round is a full analysis -- and when nothing new appears (the
    // common case) it stops after the same two passes it always did.
    constexpr unsigned kMaxProbes = 3;
    std::map<std::string, std::set<uint64_t>> want;
    AnalysisOutcome last;
    bool grew = true;
    for (unsigned round = 0; round < kMaxProbes && grew; ++round) {
      AnalysisOptions probe = opt;
      probe.taint.recordReads = true;
      probe.escalate = false;  // the probe only needs the read set, not the precision pass
      if (round) {
        probe.promoteGlobals = &want;
        probe.preParsedBase.reset();  // a pre-parsed base may be used once; see the setup fallback
      }
      AnalysisOutcome p = analyzeOnce(probe);
      if (!p.ok) return round ? std::move(last) : std::move(p);
      last = std::move(p);
      size_t before = 0;
      for (auto &kv : want) before += kv.second.size();
      for (auto &r : last.entry.reads) {
        // engine-internal and compiler-generated objects are not the module's state
        if (r.location.rfind("global:", 0) != 0) continue;
        std::string n = r.location.substr(7);
        if (n.rfind("__hlir_", 0) == 0 || n.rfind("__str.", 0) == 0 || n.find(".__init") != std::string::npos) continue;
        want[n].insert(r.offsets.begin(), r.offsets.end());
      }
      size_t after = 0;
      for (auto &kv : want) after += kv.second.size();
      grew = after > before;
    }
    if (!want.empty()) {
      AnalysisOptions again = opt;
      again.promoteGlobals = &want;
      again.preParsedBase.reset();
      AnalysisOutcome p2 = analyzeOnce(again);
      if (p2.ok) return p2;
    }
    return last;
  }
  // All-or-nothing (§22.368 §3): a constructor that cannot complete leaves a state the program never has, so its
  // effects are discarded entirely and the entry is analysed as it would have been without one. Doing this here
  // rather than inside the run keeps the fallback a SECOND, visible analysis instead of a silent half-state.
  {
    AnalysisOptions first = opt;
    AnalysisOutcome r = opt.loopBounds.empty() ? analyzeOnce(first) : AnalysisOutcome{};
    bool infeasible = false;
    if (r.ok)
      for (auto &i : r.entry.incomplete) infeasible |= i.code == "setup_infeasible";
    if (!infeasible) {
      if (opt.loopBounds.empty()) return r;
    } else {
      AnalysisOptions again = opt;
      again.specText = withoutSetup(opt.specText);
      // `preParsedBase` may be handed to at most ONE analyzeEntry call: analyzeOnce appends this entry's harness to
      // it, so reusing it here would stack the fallback harness on top of the first one. (Measured: the fallback
      // run came back with the same 13 blocks as the run it was replacing, which is what that looks like.) Drop it
      // and pay for one re-parse -- only on the entries that actually need the fallback.
      again.preParsedBase.reset();
      AnalysisOutcome r2 = analyzeOnce(again);
      if (r2.ok) {
        // keep the reason: the user has to know the session is a synthesis again, and why
        for (auto &i : r.entry.incomplete)
          if (i.code == "setup_infeasible") r2.entry.incomplete.push_back(i);
        return r2;
      }
      return r;
    }
  }
  if (opt.loopBounds.empty()) return analyzeOnce(opt);
  const auto tStart = Clock::now();
  AnalysisOutcome best, lastUnknown;
  unsigned bestK = 0;
  std::string unfinished;  // bounds that did not complete
  for (size_t si = 0; si < opt.loopBounds.size(); ++si) {
    unsigned k = opt.loopBounds[si];
    AnalysisOptions o = opt;
    o.loopBound = k;
    if (opt.wallSeconds > 0) {
      // an equal share of what is left (time a smaller bound did not need carries over to the larger ones)
      double left = opt.wallSeconds - secondsSince(tStart);
      if (left < 1 && (best.ok || lastUnknown.ok)) break;
      o.wallSeconds = std::max(1.0, left / static_cast<double>(opt.loopBounds.size() - si));
    }
    AnalysisOutcome r = analyzeOnce(o);
    if (!r.ok) { if (best.ok || lastUnknown.ok) break; return r; }
    auto v = r.entry.verdict;
    if (v == report::Verdict::Bug || v == report::Verdict::SafeUnderAssumptions) { r.entry.metrics.secondsTotal = secondsSince(tStart); return r; }
    if (v == report::Verdict::SafeUpToLoopBound) { best = std::move(r); bestK = k; continue; }
    // Unknown: this bound did not finish (time budget, unsupported, ...). Larger bounds may still find a bug, so go on.
    unfinished += (unfinished.empty() ? "" : ", ") + std::to_string(k);
    lastUnknown = std::move(r);
  }
  AnalysisOutcome &res = best.ok ? best : lastUnknown;
  if (best.ok && !unfinished.empty())
    best.entry.incomplete.push_back({"deeper_bound_unfinished", "loop bound(s) " + unfinished + " did not complete within the budget; the verdict is the one for bound " + std::to_string(bestK)});
  if (res.ok) res.entry.metrics.secondsTotal = secondsSince(tStart);
  return res;
}

// Coverage is recomputed from the UNION of every pass, including the auto-target rounds. Before this, a
// multi-pass analysis reported its LAST pass's coverage as the whole search's, which understates all of them.
static void applyUnionCoverage(AnalysisOutcome &r, const std::set<std::string> &accE, const std::set<std::string> &accB) {
  if (!r.ok || !r.entry.coverage.measured) return;
  r.edgeKeys = accE;
  r.blockKeys = accB;
  auto &c = r.entry.coverage;
  c.branchesVisited = std::max<uint64_t>(c.branchesVisited, accE.size());
  c.blocksVisited = std::max<uint64_t>(c.blocksVisited, accB.size());
  std::set<std::string> fns;
  for (auto &k : accB) fns.insert(k.substr(0, k.find('#')));
  c.functionsEntered = std::max<uint64_t>(c.functionsEntered, fns.size());
}

AnalysisOutcome analyzeEntry(const AnalysisOptions &opt) {
  const auto tStart = Clock::now();
  std::set<std::string> accE, accB;
  // With auto-targeting on, the base pass must leave room for the rounds: the driver's per-entry watchdog is
  // sized for ONE analysis, and a base pass that spends all of it gets the worker killed before any round runs.
  AnalysisOptions base = opt;
  if (opt.autoTargetRounds && opt.wallSeconds > 0)
    base.wallSeconds = std::max(1.0, opt.wallSeconds / static_cast<double>(opt.autoTargetRounds + 1));
  AnalysisOutcome r = analyzeEntryPasses(base, accE, accB);
  // Auto-targeting: the search stopped without a defect and did not enter everything it could reach. Aim at the
  // call frontier -- functions one edge from explored code, ordered so the ones that can hold a defect come
  // first -- and run again. --reach-target has one measured rule (three targets): it helps only when the target
  // is INSIDE the region being explored. The call frontier satisfies that by construction; a hand-typed name
  // usually does not, which is why hand-typed targets so often did nothing.
  if (opt.autoTargetRounds && r.ok && opt.taint.reachTarget.empty() &&
      r.entry.verdict != report::Verdict::Bug && !r.entry.coverage.notEntered.empty()) {
    unsigned used = 0;
    for (const std::string &target : r.entry.coverage.notEntered) {
      if (used >= opt.autoTargetRounds) break;
      ++used;
      AnalysisOptions o = opt;
      o.taint.reachTarget = target;
      o.autoTargetRounds = 0;
      o.preParsedBase.reset();  // at most one analyzeEntry call per pre-parsed base
      // Share the wall-clock budget, the way the loop-bound ladder does. Without this each round asks for the
      // FULL per-entry budget, the driver's watchdog kills the worker at the first one, and the entry comes back
      // `timeout` with zero coverage -- measured on libyaml, where a 420s entry budget produced 0/0 blocks.
      if (opt.wallSeconds > 0) {
        double left = opt.wallSeconds - secondsSince(tStart);
        if (left < 1.0) break;
        o.wallSeconds = std::max(1.0, left / static_cast<double>(opt.autoTargetRounds - used + 1));
      }
      AnalysisOutcome t = analyzeEntryPasses(o, accE, accB);
      if (t.ok && t.entry.verdict == report::Verdict::Bug) {
        t.entry.assumptions.push_back({"auto_target",
                                       "the search was re-run aimed at @" + target +
                                           ", a function on the call frontier that no run had entered; this verdict "
                                           "comes from that targeted round (DESIGN.md \u00a722.415)",
                                       {}});
        applyUnionCoverage(t, accE, accB);
        return t;
      }
    }
    if (used) {
      std::string names;
      for (unsigned i = 0; i < used && i < r.entry.coverage.notEntered.size(); ++i)
        names += (names.empty() ? "" : ", ") + ("@" + r.entry.coverage.notEntered[i]);
      r.entry.assumptions.push_back({"auto_target",
                                     "re-ran the search aimed at " + std::to_string(used) +
                                         " never-entered function(s) on the call frontier (" + names +
                                         ") and none of those rounds found a defect; the reported coverage is the "
                                         "union of every round (DESIGN.md \u00a722.415)",
                                     {}});
    }
  }
  applyUnionCoverage(r, accE, accB);
  return r;
}


static AnalysisOutcome analyzeOnce(const AnalysisOptions &opt) {
  AnalysisOutcome out;
  auto tStart = Clock::now();
  Diagnostics d;
  entry::EntryFile ef;
  if (!entry::parseEntrySpec(opt.specText, opt.specName, ef, d)) { out.error = d.str(); return out; }
  for (auto &pre : opt.preconditions)
    if (!entry::applyPreconditions(pre.second, pre.first, ef, d)) { out.error = d.str(); return out; }
  const entry::EntrySpec *es = ef.find(opt.entry);
  if (!es) { out.error = "no taint entry for @" + opt.entry + " in " + opt.specName; return out; }
  // `opt.preParsedBase`: a `--link` program's text can be hundreds of MB (a real kernel subsystem); parsing it is the
  // dominant cost of analysing any one entry against it (see tools/hlir-scan.cpp's HLIR_DEBUG_PARSE measurements).
  // When the caller already parsed+verified this exact text once (hlir-scan does, before forking the per-entry
  // workers: the base Module is then inherited copy-on-write by every child instead of each re-parsing the same
  // bytes), reuse it instead of paying that cost (and the cost of even materialising `opt.coreText` into `text`,
  // a second multi-hundred-MB copy) again here.
  std::unique_ptr<Module> ownedMod;
  Module *mod = nullptr;
  if (opt.preParsedBase) {
    mod = opt.preParsedBase.get();
  } else {
    std::string text = opt.coreText + (opt.libcText.empty() ? "" : "\n" + opt.libcText);
    auto _tp0 = Clock::now();
    ownedMod = parseModule(text, opt.coreName, d);
    auto _tp0v = Clock::now();
    if (getenv("HLIR_DEBUG_PARSE")) std::cerr << "  PARSE1-parse (bare, " << text.size() << " bytes): " << secondsSince(_tp0) << "s\n";
    if (!ownedMod || d.hasErrors() || !verifyModule(*ownedMod, {}, d)) { out.error = d.str(); return out; }
    mod = ownedMod.get();
    if (getenv("HLIR_DEBUG_PARSE")) std::cerr << "  PARSE1-verify (bare): " << secondsSince(_tp0v) << "s\n";
  }
  model::ModelDB modelDb;
  for (auto &m : opt.models)
    if (!modelDb.load(m.second, m.first, d)) { out.error = d.str(); return out; }
  std::vector<std::string> opaqueFns, untrustedFns;
  std::map<std::string, std::string> lowerFail;  // opaque ONLY because the frontend could not lower it (name -> reason)
  const bool haveUntrusted = !opt.untrustedApi.empty();
  if (haveUntrusted) {
    std::string uerr;
    if (!modelDb.setUntrusted(opt.untrustedApi, opt.untrustedLabel, opt.untrustedOutMax, uerr)) { out.error = uerr; return out; }
  }
  std::set<std::string> skipNames;
  std::vector<const model::ExternsFile::Skip *> skipsUsed;
  for (auto &sk : opt.externSkips) skipNames.insert(sk.function);
  if (opt.opaqueExternals || haveUntrusted) {
    modelDb.setOpaqueFallback(true);
    for (auto &f : mod->functions)
      if (f->isDeclaration() && !modelDb.has(f->name)) {
        std::string lb;
        unsigned om;
        if (modelDb.untrusted(f->name, lb, om)) { untrustedFns.push_back(f->name); continue; }
        // A declared-and-skipped external is reported under its own heading, with the project's reason. The
        // behaviour is identical -- it is still opaque -- but "examined and judged irrelevant" and "nobody has
        // looked" are different claims and the report may not merge them (DESIGN.md §22.379).
        if (skipNames.count(f->name)) {
          for (auto &sk : opt.externSkips)
            if (sk.function == f->name) skipsUsed.push_back(&sk);
          continue;
        }
        opaqueFns.push_back(f->name);
        auto lf = opt.notLoweredFns.find(f->name);
        if (lf != opt.notLoweredFns.end()) lowerFail[f->name] = lf->second;
      }
  }
  // A skip the module never declares is a STALE claim: the function was renamed, or the list was copied from
  // another project. Saying so is the only thing that keeps such a list honest over time.
  std::vector<std::string> staleSkips;
  {
    std::set<std::string> declared;
    for (auto &f : mod->functions)
      if (f->isDeclaration()) declared.insert(f->name);
    for (auto &sk : opt.externSkips)
      if (!declared.count(sk.function)) staleSkips.push_back(sk.function);
  }
  const bool useModels = !opt.models.empty() || opt.opaqueExternals || haveUntrusted;
  smt::TermManager tm;
  entry::InitPlan plan;
  if (!entry::buildInitPlan(*mod, ef, *es, tm, plan, d)) { out.error = d.str(); return out; }
  plan.argv = opt.initArgv;  // the project's stated command line (§22.380); empty = the harness invents one

  report::EntryReport &er = out.entry;
  er.lowerFailures = lowerFail;
  er.function = opt.entry;
  er.specFile = opt.specName;
  er.label = es->label;

  // TEMP (stage-3 SMT backend perf experiment, docs/DESIGN.md -- NOT a real CLI feature, revert before shipping):
  // HLIR_BENCH_Z3_BACKEND=native swaps in makeZ3NativeSolver() instead of the default Z3Process, so the same
  // hlir-scan run can be repeated against both backends for an apples-to-apples wall-clock/query-count comparison.
  // HLIR_BENCH_Z3_EXE overrides the z3 executable (e.g. /usr/bin/z3, to version-align with the libz3.so Z3Native
  // links against) without touching every caller's "z3" literal.
  std::unique_ptr<smt::Solver> solver;
  if (const char *backend = getenv("HLIR_BENCH_Z3_BACKEND"); backend && std::string(backend) == "native") {
    solver = smt::makeZ3NativeSolver(opt.solverTimeoutMs);
  } else {
    const char *exe = getenv("HLIR_BENCH_Z3_EXE");
    solver = smt::makeZ3ProcessSolver(exe ? exe : "z3", opt.solverTimeoutMs);
  }
  if (!solver) { out.error = "cannot start z3"; return out; }

  // ---- assumptions that come from the specification itself
  for (auto &c : plan.constraints) er.assumptions.push_back({c.name.rfind("pre.", 0) == 0 ? "precondition" : "init", c.name, specLoc(c.name)});
  for (auto &pp : plan.params) {
    for (auto &w : pp.wheres) er.assumptions.push_back({"precondition", w.name, specLoc(w.name)});
    // the same, one level down: a precondition on an integer inside a synthesised FIELD object. It is a NARROWING
    // assumption (it removes states the harness could otherwise build), so it has to be visible in the report like
    // any other -- see DESIGN.md §22.356.
    std::function<void(const std::vector<entry::PlannedField> &)> fieldWheres = [&](const std::vector<entry::PlannedField> &fs) {
      for (auto &f : fs) {
        for (auto &w : f.wheres) er.assumptions.push_back({"precondition", w.name, specLoc(w.name)});
        fieldWheres(f.fields);
      }
    };
    fieldWheres(pp.fields);
    for (auto &el : pp.elements) er.assumptions.push_back({"precondition", el.name, specLoc(el.name)});
  }
  if (es->relations.empty()) er.assumptions.push_back({"attacker_model", "hostile: parameter sizes and lengths are independent (no relations in the spec)", {opt.specName, es->line, 1}});
  else er.assumptions.push_back({"attacker_model", "contract: " + std::to_string(es->relations.size()) + " relation(s) between parameters hold", {opt.specName, es->line, 1}});
  // narrowings the spec names explicitly (an interface contract it was lowered from): they constrain nothing on
  // their own, but a narrowing that is wrong hides a defect, so it has to be readable in the report (§22.361)
  for (auto &a : es->assumptions) er.assumptions.push_back({"interface_contract", a.text, {opt.specName, a.line, 1}});
  // The object tree a spec builds is FINITE: `fields:` names a pointer and the harness builds it an object. Beyond
  // that, Memory::lazyFrontier() materialises a blank object on demand rather than reading NULL out of blank content
  // (DESIGN.md §22.364). Which way round the error goes is the whole point: reading NULL could not hide a defect, it
  // MANUFACTURED one (14 of the sound/core round's 19 confirmed null_deref), whereas materialising is a NARROWING --
  // out there a pointer is now never NULL and its object is a flat 4096 bytes, so a real null deref or overrun more
  // levels down goes unseen. A narrowing that is wrong hides a defect, so it may never be invisible (§22.361).
  {
    std::function<unsigned(const std::vector<entry::PlannedField> &)> fieldDepth = [&](const std::vector<entry::PlannedField> &fs) {
      unsigned d = 0;
      for (auto &f : fs) d = std::max(d, 1u + fieldDepth(f.fields));
      return d;
    };
    unsigned depth = 0;
    for (auto &pp : plan.params) depth = std::max(depth, fieldDepth(pp.fields));
    if (depth)
      er.assumptions.push_back({"synthesis_frontier", "the spec names the pointer fields of a parameter object " + std::to_string(depth) +
                                " level(s) deep; past that a dereferenced pointer is materialised on demand as a fresh blank "
                                "object instead of being read as NULL, so out there nothing is null; that object's size is a "
                                "stand-in rather than the real struct's, so no out-of-bounds or pointer-arithmetic check is "
                                "performed against it -- an overrun more levels down goes unreported",
                                {opt.specName, es->line, 1}});
  }
  er.assumptions.push_back({"bound", "parameter objects are at most " + std::to_string(ef.defaults.maxObj) + " bytes (max_obj)", {}});
  for (auto &p : plan.params)
    if (!p.tainted && p.kind == entry::PlannedParam::Scalar && p.value->kind == smt::Kind::BvConst)
      er.assumptions.push_back({"env_fact", "untainted parameter '" + p.name + "' is fixed to " + numStr(p.value->value, p.isSigned), {opt.specName, p.line, 1}});
  if (!opt.models.empty()) er.assumptions.push_back({"model", "external functions follow the ModelDB (" + std::to_string(modelDb.size()) + " models); unlisted external calls are " + (opt.opaqueExternals ? "assumed opaque" : "unsupported"), {}});
  if (!opaqueFns.empty()) {
    std::string names;
    for (size_t i = 0; i < opaqueFns.size(); ++i) names += (i ? ", " : "") + opaqueFns[i];
    er.assumptions.push_back({"model", "functions without a body or a model are assumed opaque (arbitrary untainted result, no effect on memory or taint, pointers: NULL or a zeroed 4096-byte object): " + names, {}});
  }
  if (!lowerFail.empty()) {
    // These are IN opaqueFns above, but the cause is different and so is the fix: the source exists, the FRONTEND
    // could not lower it. Named on its own so the reader checks a compile flag (e.g. SIMD -U__SSE2__) or adds
    // frontend support, instead of writing a model for code that is right there.
    std::string names;
    for (auto &kv : lowerFail) names += (names.empty() ? "" : ", ") + kv.first + " (" + kv.second + ")";
    er.assumptions.push_back({"lowering_failure", "opaque because the frontend could not lower them (the source IS present -- this is a frontend gap, not a missing external; fix with a compile flag such as -U__SSE2__ for SIMD, or add frontend support): " + names, {}});
  }
  if (!skipsUsed.empty()) {
    std::string names;
    size_t shown = 0;
    for (auto *sk : skipsUsed) {
      if (shown >= 12) { names += ", ..."; break; }
      if (shown++) names += "; ";
      names += sk->function + " (" + sk->reason + ")";
    }
    er.assumptions.push_back({"skipped_external",
                              std::to_string(skipsUsed.size()) +
                                  " external(s) are left opaque BY DECISION, recorded in " + opt.externsPath +
                                  " with a reason each -- they return an arbitrary untainted value and write nothing. "
                                  "This is a claim about the program, not an omission: if one of them does write a "
                                  "buffer an entry later reads, every check of that buffer here is decided on a state "
                                  "the program never has. " + names,
                              {}});
  }
  if (!staleSkips.empty()) {
    std::string names;
    for (size_t i = 0; i < staleSkips.size(); ++i) names += (i ? ", " : "") + staleSkips[i];
    er.assumptions.push_back({"skipped_external",
                              "the skip list in " + opt.externsPath +
                                  " names function(s) this scan set never declares, so the claim made about them "
                                  "was not used and may be stale (renamed, or copied from another project): " + names,
                              {}});
  }
  if (!untrustedFns.empty()) {
    std::string names;
    for (size_t i = 0; i < untrustedFns.size(); ++i) names += (i ? ", " : "") + untrustedFns[i];
    er.assumptions.push_back({"attacker_model", "untrusted API (compromised component; functions matching '" + opt.untrustedApi + "'): their results, the contents of returned pointers (" +
                                  std::to_string(opt.untrustedOutMax) + " bytes, may be NULL) and of every non-const pointer-argument object of at most " + std::to_string(opt.untrustedOutMax) +
                                  " bytes are attacker-controlled (label " + opt.untrustedLabel + "): " + names, {}});
  }
  for (auto &n : opt.taint.promote) er.assumptions.push_back({"promoted_env", "'" + n + "' is treated as an attacker-controlled symbolic input", {}});
  // The global-initial-value narrowing, filled in after the runs (see below): declared here so it keeps the place
  // the other spec-level assumptions have in the list.
  const size_t globalAssumptionAt = er.assumptions.size();

  // ---- legal initial state
  auto tSeed = Clock::now();
  entry::SeedSolver ss(tm, *solver, plan);
  entry::Seed legal = ss.legality();
  if (legal.result == smt::SatResult::Unsat) {
    std::string core;
    for (auto &c : legal.core) core += (core.empty() ? "" : ", ") + c;
    er.incomplete.push_back({"spec_contradiction", "the entry specification is unsatisfiable; conflicting constraints: " + core});
    er.verdict = report::computeVerdict(er);
    out.ok = true;
    return out;
  }
  // --seed-value: the caller's starting values for named scalars go into the SAME query as C_init, so
  // M0 satisfies both. Applying them after M0 instead would let the concrete run disagree with the
  // symbolic state (DESIGN.md Sec.22.448). A name that matches no scalar parameter, and a seed the
  // specification contradicts, are both REPORTED -- silently ignoring either is how a seeded run comes
  // back with the coverage of an unseeded one and nothing says so.
  entry::Seed m0;
  bool seedValueApplied = !opt.taint.valueSeeds.empty();
  {
    std::vector<std::pair<std::string, smt::TermRef>> extra;
    std::set<std::string> matched;
    for (auto &p : plan.params) {
      if (p.kind != entry::PlannedParam::Scalar) continue;
      auto it = opt.taint.valueSeeds.find(p.name);
      if (it == opt.taint.valueSeeds.end()) continue;
      matched.insert(p.name);
      extra.push_back({"seed.value." + p.name,
                       tm.mkEq(p.value, tm.bvConst(llvm::APInt(p.width, it->second)))});
    }
    std::string unmatched;
    for (auto &kv : opt.taint.valueSeeds)
      if (!matched.count(kv.first)) unmatched += (unmatched.empty() ? "" : ", ") + kv.first;
    if (!unmatched.empty()) {
      // Both failures go in the REPORT, not only on stderr. A reader of the JSON sees the coverage and
      // the verdict; if the seed silently did nothing, those two numbers describe a different run from
      // the one the command line asked for, and nothing else would say so. A typo in the name is the
      // likelier mistake of the two, so it is the one that must not be quieter.
      fprintf(stderr, "hlir-scan: --seed-value names no scalar parameter of %s: %s  (NOT applied)\n",
              er.function.c_str(), unmatched.c_str());
      er.assumptions.push_back({"attacker_model",
                                "--seed-value named no scalar parameter and was NOT applied: " + unmatched,
                                {}});
    }
    m0 = extra.empty() ? ss.benign() : ss.benignWith(extra);
    if (!extra.empty() && m0.result != smt::SatResult::Sat) {
      fprintf(stderr, "hlir-scan: --seed-value contradicts the specification of %s; running without it\n",
              er.function.c_str());
      er.assumptions.push_back({"attacker_model", "--seed-value was dropped: it contradicts the entry's legality constraints", {}});
      m0 = ss.benign();
      seedValueApplied = false;
    }
  }
  if (m0.result != smt::SatResult::Sat) {
    er.incomplete.push_back({"solver_unknown", "no legal initial state could be computed"});
    er.verdict = report::computeVerdict(er);
    out.ok = true;
    return out;
  }
  er.metrics.secondsSeed = secondsSince(tSeed);
  WitnessPrinter wp{plan, *es, nullptr, {}};
  {
    std::vector<std::string> names;
    std::vector<llvm::APInt> vals;
    for (auto &kv : m0.model) { names.push_back(kv.first); vals.push_back(kv.second); }
    for (auto &w : wp.print(names, vals, {})) er.seedSummary += (er.seedSummary.empty() ? "" : "; ") + w.name + " = " + w.value;
    // This line is M0, the model that shows the SPEC is satisfiable. --seed-value is part of the SAME
    // query, so it IS reflected above. --seed-bytes is not: it is applied later, per 8-bit input, inside
    // TaintDomain::source(). Printing M0 under the heading "seed" with no note made a seeded run look
    // unseeded ("all bytes 0") twice during the Fluent Bit scan before anyone checked; the A/B that
    // settled it showed the seed had been applied all along (DESIGN.md Sec.22.448).
    if (!opt.taint.labelSeeds.empty() || !opt.taint.valueSeeds.empty()) {
      std::string note = "  [this is M0, the spec-feasibility model.";
      if (!opt.taint.valueSeeds.empty())
        note += seedValueApplied ? " --seed-value is part of this query, so it IS shown above."
                                 : " --seed-value was DROPPED (see assumptions), so it is NOT shown above.";
      if (!opt.taint.labelSeeds.empty()) {
        std::string over;
        for (auto &kv : opt.taint.labelSeeds)
          over += (over.empty() ? "" : ", ") + kv.first + " (" + std::to_string(kv.second.size()) + " byte(s))";
        note += " --seed-bytes is NOT shown here -- it replaces the 8-bit inputs of label(s) " + over +
                " when the run starts.";
      }
      er.seedSummary += note + "]";
    }
  }

  // ---- harness + analysis
  auto tAnalysis = Clock::now();
  std::string harness = entry::generateHarness(plan, &wp.objId);
  const std::string hn = entry::harnessName(plan);
  // Append the (small) harness onto the already-parsed `mod` instead of re-lexing/re-parsing `text` a second time
  // as `text + harness`: on a large `--link` program `text` dominates the harness by orders of magnitude, and the
  // combined-string parse paid its full cost twice for the same bytes. `parseModuleInto` reuses `mod`'s Context so
  // the new functions' Type* pointers are interned in the same table (see its doc comment in Parser.h for why a
  // duplicate `core.declare` of an already-defined function stays harmless either way).
  //
  // **Guarded by `findFunction(hn)` because `mod` can be `opt.preParsedBase`, shared across repeat calls to
  // `analyzeOnce` for the *same* entry** — iterative deepening (`analyzeEntry`'s `opt.loopBounds` loop, §21/§22.6)
  // calls `analyzeOnce` once per bound, each time with a fresh copy of `opt` that still points at the very same
  // Module. `harness`/`hn` are a pure function of `plan`, which rebuilds identically every call (only `loopBound`
  // itself differs between iterations, and that is consumed later, not here) — so the harness is only genuinely
  // missing from `mod` on the first call; parsing it again on a later one would hit the "redefinition" diagnostic
  // `parseDeclare`/`parseFunction` raise for a real duplicate (see Parser.cpp) and spuriously fail that bound.
  // `baseCount` is "how many of `mod`'s functions were already verified before this call" — either by the earlier
  // `verifyModule`/pre-parse-pass verify of the base program (first time merging this entry's harness in), or by
  // this very function body on an earlier iterative-deepening call for the same entry (§loopBounds reuses the same
  // `mod`/harness across bounds; `findFunction(hn)` below is false then, so no new functions get added at all —
  // `verifyNewFunctions` degrades to just the cheap whole-module duplicate-name scan, re-verifying nothing).
  size_t baseCount = mod->functions.size();
  bool harnessOk = true;
  if (!mod->findFunction(hn)) {
    auto _tp1 = Clock::now();
    harnessOk = parseModuleInto(*mod, harness, opt.coreName + "+harness", d);
    if (getenv("HLIR_DEBUG_PARSE")) std::cerr << "  PARSE2 (harness only, " << harness.size() << " bytes): " << secondsSince(_tp1) << "s\n";
  }
  Module *full = mod;
  // Only the newly-appended harness functions need the (expensive) structural+type check: the functions before
  // `baseCount` already went through it, either in the pre-parse pass (tools/hlir-scan.cpp, §22.13) or in the
  // `verifyModule(*ownedMod, ...)` call above when this process parsed the base itself. See
  // `verifyNewFunctions`'s doc comment (include/hlir/ir/Verifier.h) and docs/DESIGN.md §22.15 for the measurement
  // that motivated this (re-verifying all ~26000 functions of a real `--link` program cost ~20s, every entry).
  auto _tp2 = Clock::now();
  bool fullOk = harnessOk && !d.hasErrors() && verifyNewFunctions(*full, baseCount, {}, d);
  if (getenv("HLIR_DEBUG_PARSE")) std::cerr << "  VERIFY-new (" << (full->functions.size() - baseCount) << " of "
                                             << full->functions.size() << " functions): " << secondsSince(_tp2) << "s\n";
  if (!fullOk) { out.error = "generated harness does not verify:\n" + d.str(); return out; }
  smt::TermManager tm2;

  std::map<Key, report::Finding> found;
  auto addFinding = [&](const SymFinding &f, const char *engine, bool replayConfirmed, bool replayDone, const std::string &note, bool overApprox) {
    report::Finding rf;
    rf.kind = f.ub ? ubKindName(f.ub->kind) : "assert";
    rf.function = f.ub ? f.ub->function : opt.entry;
    rf.op = f.ub ? f.ub->op : "core.assert";
    rf.origin = f.ub ? f.ub->origin : "";
    rf.loc = toLoc(f.loc);
    // A UB only the harness's own frontier filler can produce is reported with its witness but never counts as a
    // defect: `warning` is exactly the field that keeps it out of the entry's verdict (DESIGN.md §22.365).
    // A UB inside the project initialiser is a fact about init code, not about this handler's attack surface, so
    // it is reported with its witness but never counts as this entry's defect (DESIGN.md §22.368, round 49b).
    rf.warning = (f.ub && ubKindIsWarning(f.ub->kind)) || f.frontierOnly || f.inPrologue || f.cmpOnlyPtr;
    rf.inPrologue = f.inPrologue;
    // ---- evidence (DESIGN.md §22.369): carry the engine's view of the failing access and of the memory it
    // happened in, so a reader can rebuild the state instead of re-deriving the defect from the source.
    if (f.ub) {
      if (getenv("HLIR_DEBUG_EVIDENCE"))
        fprintf(stderr, "[pl] kind=%s access.valid=%d obj=%u objs=%zu\n", ubKindName(f.ub->kind),
                (int)f.ub->access.valid, f.ub->access.obj, f.ub->objects.size());
      rf.access.valid = f.ub->access.valid;
      rf.access.obj = f.ub->access.obj;
      rf.access.objName = f.ub->access.objName;
      rf.access.objSizeKnown = f.ub->access.objSizeKnown;
      rf.access.objSize = f.ub->access.objSize;
      rf.access.offsetKnown = f.ub->access.offsetKnown;
      rf.access.offset = f.ub->access.offset;
      rf.access.offsetSymbolic = f.ub->access.offsetSymbolic;
      rf.access.width = f.ub->access.width;
      rf.access.access = f.ub->access.access;
      for (auto &o : f.ub->objects) {
        report::EvidenceObject e;
        e.id = o.id; e.kind = o.kind; e.name = o.name;
        e.sizeKnown = o.sizeKnown; e.size = o.size;
        e.progWritten = o.progWritten; e.frontier = o.frontier; e.inputContent = o.inputContent;
        e.unknownContent = o.unknownContent;
        e.symbolicBytes = o.symbolicBytes; e.truncated = o.truncated;
        for (auto &b : o.nonZero) e.nonZero.push_back({b.off, b.val});
        rf.objects.push_back(std::move(e));
      }
    }
    // ---- and whether a real input could ever produce it. A reader handed this evidence will otherwise write a
    // reproduction for a state the program cannot reach, and someone will spend a day chasing it.
    {
      std::string why;
      bool frontierObj = false;
      for (auto &o : rf.objects)
        if (o.frontier && (rf.access.obj == 0 || o.id == rf.access.obj)) frontierObj = true;
      if (f.inPrologue) why = "the failing operation is inside the setup code the harness runs before the entry (the project initialiser or the session constructor), not in code this entry's attacker drives";
      else if (f.cmpOnlyPtr) why = "the out-of-range pointer is never dereferenced -- every use of it is a pointer comparison or a pointer difference, the `if (p + n > end)` bound-check idiom. Forming it IS undefined behaviour (C11 6.5.6p8, and AddressSanitizer reports the same sites as invalid-pointer-pair), so it is reported; it is not a memory-safety violation, so it does not decide the verdict";
      else if (f.frontierOnly) why = "the condition is decided only by bytes the analysis invented rather than read from the program -- content past the synthesis frontier, or a buffer an external's model says it writes without saying what (see the synthesis_frontier / unknown_external_write assumption)";
      else if (frontierObj) why = "the object it accesses was materialised past the synthesis frontier: the harness invented it, including its size";
      if (!why.empty()) { rf.reproducible = report::Reproducible::HarnessOnly; rf.reproducibleWhy = why; }
    }
    rf.message = !f.ub ? "assertion failed: " + f.message
               : f.ub->kind == UBKind::TaintedSink ? "attacker-controlled data reaches a security sink (" + f.ub->origin + ")"
               : f.ub->kind == UBKind::TaintedLoopBound ? "attacker-controlled value governs a loop's iteration count with no constant upper bound in force (uncontrolled resource consumption / DoS; a dominating range check -- `if (n > C) ...` -- or a narrow type would bound it to a predictable range)"
               : f.ub->kind == UBKind::TaintedIndex ? "attacker-controlled value used as a memory index with no constant upper bound (add a fixed-range check)"
               : "undefined behaviour: " + rf.kind;
    if (f.frontierOnly)
      rf.message += " -- decided only by bytes the analysis invented rather than read from the program, not by any"
                    " input of it (the synthesis frontier, or an external that writes a buffer with contents its"
                    " model does not state: see the synthesis_frontier / unknown_external_write assumption)";
    if (f.inPrologue)
      rf.message += " -- inside the setup code the harness runs before this entry (the project initialiser and/or the"
                    " session constructor), not in the entry's own reachable code: nothing the attacker sends here can"
                    " influence it (see the project_init / session_ctor assumption)";
    rf.engine = engine;
    rf.labels = {plan.label};
    rf.witness = wp.print(f.nondetNames, f.nondets, f.inputs);
    if (f.ub) {  // the entry harness (first frame) is generated code, not part of the program's call chain
      rf.callStack = f.ub->callStack;
      rf.locFromFrame = f.ub->locFromFrame;
      // The failing op is in a model body, which has no source: take the call-site location the UBReport
      // attributed it to (Sec.22.471). `Finding::loc` is the op's own and stays empty for these.
      if (!rf.loc.valid() && f.ub->loc.valid()) rf.loc = toLoc(f.ub->loc);
      if (!rf.callStack.empty() && rf.callStack.front() == hn) rf.callStack.erase(rf.callStack.begin());
    }
    rf.id = rf.kind + "@" + rf.function + ":" + std::to_string(rf.loc.line);
    if (!replayDone) rf.replay = report::ReplayStatus::Skipped;
    else if (replayConfirmed) rf.replay = report::ReplayStatus::Confirmed;
    else {
      rf.replay = report::ReplayStatus::NotReproduced;
      rf.unconfirmedDetail = note;
      rf.unconfirmedReason = overApprox ? "overapprox_memory" : note.find("different UB") != std::string::npos ? "replay_different_ub" : "replay_no_ub";
    }
    Key k{rf.function, rf.op, rf.kind, rf.loc.line};
    auto it = found.find(k);
    if (it == found.end() || (it->second.replay != report::ReplayStatus::Confirmed && rf.replay == report::ReplayStatus::Confirmed)) found[k] = std::move(rf);
  };

  TaintExecutor tx(*full, tm2, *solver);
  TaintConfig tcfg = opt.taint;
  if (opt.noTableSelect) tcfg.tableSelect = false;  // G2 escape hatch reaches the CONCOLIC search too (that is where branches are classified)
  tcfg.storeSelect = opt.storeSelect;
  // The harness's structural choices (an optional pointer's "absent?" bit) are symbolic but carry no taint label, so
  // the engine would keep them concrete and never explore the other configuration -- see InitVar::promote.
  for (auto &v : plan.vars)
    if (v.promote && v.var) tcfg.promote.insert(v.var->name);
  // The initialiser(s) the harness calls before the entry: a UB inside them is recorded but does not stop the run
  // and does not decide this entry's verdict (RunConfig::prologueFns, DESIGN.md §22.368).
  std::set<std::string> prologueFns;
  for (auto &pc : plan.prologue) prologueFns.insert(pc.function);
  // The session constructor belongs to the same discipline: it is setup code the entry's attacker does not drive,
  // so a UB inside it must not decide this entry's verdict and must not stop the run (DESIGN.md §22.368 §7). The
  // measured cost of getting this wrong is round 49b: one deterministic UB in init code made all 87 entries `bug`
  // and stopped any of them from being analysed.
  if (plan.setup.valid) prologueFns.insert(plan.setup.function);
  if (!prologueFns.empty()) tcfg.prologueFns = &prologueFns;
  // The label the bytes of a parameter OBJECT carry. Until now this was left at TaintConfig's default "input"
  // while a scalar parameter got the label the spec declares (TaintDomain::nondet reads the harness's `taint=`
  // attribute, Memory's content bytes do not) -- so one attacker wore two labels, and `--seed-bytes <label>=...`
  // silently did nothing for every buffer, because it looks the label up by name and the name never matched.
  // Measured on c-ares CVE-2023-31130: `--seed-bytes network=<trigger>` changed nothing, `input=<trigger>` found
  // the defect on the very first run (DESIGN.md §22.384).
  if (!plan.label.empty()) tcfg.inputLabel = plan.label;
  tcfg.stopFns = opt.taint.stopFns;
  tcfg.recordReads = opt.taint.recordReads;
  tcfg.promoteGlobals = opt.promoteGlobals;
  tcfg.ubContinue = opt.ubContinue;
  if (opt.loopBound) tcfg.loopBound = opt.loopBound;
  tcfg.wallSeconds = opt.wallSeconds > 0 ? std::max(1.0, opt.wallSeconds - secondsSince(tStart)) : 0;
  if (useModels) tcfg.models = &modelDb;
  std::map<std::string, llvm::APInt> seed(m0.model.begin(), m0.model.end());
  if (getenv("HLIR_DEBUG_SEED")) { fprintf(stderr, "[seed] %zu vars:", seed.size()); size_t n=0; for (auto &kv : seed) { if (n++>=24) { fprintf(stderr, " ..."); break; } fprintf(stderr, " %s", kv.first.c_str()); } fprintf(stderr, "\n"); }
  TaintResult tr = tx.run(hn, seed, tcfg);
  // A --seed-bytes key is a TAINT LABEL, not a parameter name. Naming something that is no label used to
  // be SILENT: the run proceeded completely unseeded while the report's seed note echoed the bad name back
  // as though those bytes had been applied. The key was `input` until Sec.22.384 gave a parameter object the
  // label from --label (default `network`), so every command recorded before that change now seeds nothing.
  // Measured cost on brotli CVE-2026-111497, run 1 of the vulnerable tree: `input=` reaches 384 of 1476
  // blocks and 54 functions, `network=` reaches 646 and 90 -- and the first corpus run of that case was
  // scored a false negative on the strength of it. Same shape on libsixel CVE-2020-19668 (DESIGN.md Sec.22.466).
  for (auto &kv : tcfg.labelSeeds)
    if (!tr.labelsSeen.count(kv.first)) {
      std::string seen;
      for (auto &l : tr.labelsSeen) seen += (seen.empty() ? "" : ", ") + l;
      std::string msg = "--seed-bytes: no input carries the label `" + kv.first + "`, so its " +
                        std::to_string(kv.second.size()) + " byte(s) were NEVER APPLIED and this run is unseeded" +
                        (seen.empty() ? std::string(" (this entry created no labelled input at all)")
                                      : " -- the labels this entry actually created are: " + seen) +
                        ". The key of --seed-bytes is the taint LABEL (--label, default `network`), not a parameter name.";
      std::cerr << "hlir-scan: " << msg << "\n";
      er.assumptions.push_back({"seed", msg, {opt.specName, 1, 1}});
      // The seed note was written before the run, from the command line, and claims these bytes were
      // applied. Correct it in place rather than leaving the report holding two contradictory lines.
      er.seedSummary += "  [CORRECTION: the label `" + kv.first + "` named above matched no input; its bytes were not applied.]";
    }
  wp.nondetOrigins = &tr.nondetOrigins;  // from here on every witness line can say what its nondets are
  for (auto &f : tr.findings) addFinding(f, "taint_concolic", f.confirmed && *f.confirmed, f.confirmed.has_value(), f.replayNote, false);

  uint64_t concretized = 0, selectedAddrs = 0;
  for (auto &r : tr.runs) { concretized += r.slice.concretizedPointers; selectedAddrs += r.slice.selectedAddresses; }
  er.metrics.secAssert = tr.secAssert; er.metrics.secCheck = tr.secCheck; er.metrics.secInterp = tr.secInterp; er.metrics.secSolve = tr.secSolve; er.metrics.secReplay = tr.secReplay; er.metrics.secCone = tr.secCone;
  er.metrics.branchesCovered = tr.branchesCovered;
  er.metrics.runs = tr.runs.size();
  er.metrics.maxCallDepth = tr.maxDepth > 0 ? tr.maxDepth - 1 : 0;  // without the entry harness frame
  er.metrics.solverQueries = tr.solverQueries;
  er.metrics.cacheHits = tr.cacheHits;
  er.metrics.escalations = tr.escalations;
  er.metrics.solverTerms = tr.termsSolved;
  if (!tr.runs.empty()) {
    er.metrics.stepsFirstRun = tr.runs[0].slice.steps;
    er.metrics.taintedOpsFirstRun = tr.runs[0].slice.taintedOps;
    er.metrics.pcsFirstRun = tr.runs[0].slice.pcs;
    er.metrics.queriesFirstRun = tr.runs[0].slice.queries;
    std::set<std::string> seen;
    for (auto &e : tr.runs[0].envFacts) {
      std::string t = "value " + numStr(e.value, true) + " used by " + e.op + " in @" + e.function;
      if (seen.insert(t).second) er.assumptions.push_back({"env_fact", t, toLoc(e.loc)});
    }
  }
  for (auto &c : tr.functions) {
    report::FunctionClass fc;
    fc.function = c.function; fc.calls = c.calls; fc.inert = c.inert; fc.observer = c.observer; fc.transformer = c.transformer; fc.source = c.source; fc.sanitizer = c.sanitizer;
    er.functionClasses.push_back(fc);
  }
  for (auto &c : tr.callEdges) {
    report::CallEdge ce;
    ce.caller = c.caller; ce.callee = c.callee; ce.calls = c.calls; ce.tainted = c.tainted;
    er.callEdges.push_back(ce);
  }
  if (!tr.complete) er.incomplete.push_back({tr.reason.empty() ? "incomplete" : tr.reason, tr.note});

  er.metrics.flipsQueued = tr.flipsQueued;
  er.metrics.flipsSolved = tr.flipsSolved;
  er.metrics.flipsUnsat = tr.flipsUnsat;
  er.metrics.frontierFieldReads = tr.frontierFieldReads;
  er.metrics.frontierBoundsApplied = tr.frontierBoundsApplied;
  er.metrics.frontierBoundsMissing = tr.frontierBoundsMissing;
  er.metrics.frontierBoundsInfeasible = tr.frontierBoundsInfeasible;
  // ---- the search collapsed onto its seed (DESIGN.md Sec.22.468).
  //
  // Flips were taken off the frontier and asked of the solver, and NOT ONE came back with a new input. That is
  // not convergence: the exploration consists of a single execution, and the directions it never reached have
  // been filed as `unsat` -- "proved infeasible on this path prefix" -- which is true only of the one prefix it
  // ever had. A reader sees `open = 0` and reads it as a finished search.
  //
  // This is reported whether or not the budget ran out, because the budget is not what stopped it; but when the
  // run is already incomplete for another reason that reason is louder, so the text says which it is.
  if (tr.flipsQueued > 0 && tr.flipsSolved == 0) {
    er.incomplete.push_back(
        {"search_collapsed",
         std::to_string(tr.flipsQueued) + " branch flip(s) were queried and NONE was satisfiable, so no run after "
         "the first was ever generated: this result rests on a single execution. Directions reported as `unsat` "
         "are infeasible only on that one path prefix. A pinned value is the usual cause -- a length or size "
         "concretised into the path condition pins every input that feeds it (see Sec.22.467)"});
  }

  // ---- precision escalation: tainted pointer values were followed concretely, so paths that need a different pointer
  // value may have been missed. The full symbolic engine treats pointers symbolically (over-approximating memory).
  bool escalated = false;
  unsigned loopCut = 0;
  SymResult sr;  // default-constructed (empty blocksVisited) when escalation does not run, so computeCoverage below is unconditional
  // The gate is a PROXY, and the proxy's name is not its meaning: it asks "was there tainted
  // addressing this engine could not settle on its own", and `concretizedPointers` was the only way
  // that ever happened. Store selection (Sec.22.487) resolves some of those addresses exactly, which
  // zeroed the counter and so removed the symbolic pass from runs that had needed it -- measured on
  // snprintf_chain_oob.c, where it turned a replay-confirmed oob_write into `not_reproduced`. A more
  // precise memory model must not be able to delete a pass; selected addresses answer the proxy too.
  if ((concretized > 0 || selectedAddrs > 0) && opt.escalate) {
    escalated = true;
    er.assumptions.push_back({"concretized_pointer", "tainted addresses or lengths were followed with their concrete values by the concolic engine; the symbolic engine was run to cover the rest", {}});
    SymbolicExecutor sx(*full, tm2, *solver);
    SymConfig sc;
    // The symbolic pass only covers what following concrete pointer values may have missed; it must not burn a budget the concolic
    // pass left unused: at most a third of the total (but at least 30 s) when there is a budget.
    sc.wallSeconds = opt.wallSeconds > 0 ? std::max(1.0, std::min(opt.wallSeconds - secondsSince(tStart), std::max(30.0, opt.wallSeconds / 3))) : 0;
    sc.maxPaths = opt.maxPaths;
    sc.loopBound = opt.loopBound;
    if (opt.memBound) sc.memBound = opt.memBound;
    if (opt.memExpandMax) sc.memExpandMax = opt.memExpandMax;
    if (opt.noTableSelect) sc.tableSelect = false;
    sc.storeSelect = opt.storeSelect;
    if (useModels) sc.models = &modelDb;
    if (!prologueFns.empty()) sc.prologueFns = &prologueFns;
    sc.stopFns = opt.taint.stopFns;
    sr = sx.run(hn, {}, sc);
    er.metrics.pathsExplored = sr.pathsExplored;
    Interpreter in(*full);
    // The replay must run the SAME machine the search ran. It used to be `in.run(hn, {}, env)` with a default
    // RunConfig: no ModelDB, no prologue, no stop functions, no loop bound. With `models == nullptr` the first
    // call to any function without a body ends the run as Unsupported, so a symbolic finding whose path touches
    // one modelled libc function could never be confirmed -- it came back `replay ended with status unsupported`
    // and was dropped. tcpdump CVE-2017-12988 (`telnet_parse:445`, the exact line the fix patches) was lost that
    // way. The concolic replay in Taint.cpp has always copied its search config; this one did not (DESIGN.md
    // §22.419).
    RunConfig src;
    if (useModels) src.models = &modelDb;
    src.ubContinue = opt.ubContinue;
    if (!prologueFns.empty()) src.prologueFns = &prologueFns;
    src.stopFns = opt.taint.stopFns;
    src.loopBound = opt.loopBound;
    if (opt.memBound) src.memBound = opt.memBound;
    if (opt.memExpandMax) src.memExpandMax = opt.memExpandMax;
    if (opt.noTableSelect) src.tableSelect = false;
    src.storeSelect = opt.storeSelect;
    for (auto &f : sr.findings) {
      SeqEnv env(f.nondets, f.inputs);
      RunResult rr = in.run(hn, {}, env, src);
      bool ok = f.ub ? ((rr.status == RunStatus::UB && rr.ub && rr.ub->kind == f.ub->kind) ||
                        rr.ubContinued.count(std::string(ubKindName(f.ub->kind)) + "@" + f.loc.file + ":" +
                                             std::to_string(f.loc.line)) != 0)
                     : rr.status == RunStatus::AssertFailed;
      std::string note = rr.status == RunStatus::UB && rr.ub
                             ? std::string("replay hit a different UB: ") + ubKindName(rr.ub->kind) +
                                   (rr.ub->loc.valid() ? " at " + rr.ub->loc.file.substr(rr.ub->loc.file.find_last_of('/') + 1) +
                                                             ":" + std::to_string(rr.ub->loc.line)
                                                       : std::string())
                             : std::string("replay ended with status ") + runStatusName(rr.status) +
                                   (rr.message.empty() ? "" : ": " + rr.message);
      addFinding(f, "symbolic", ok, true, note, sr.overApprox);
    }
    // The symbolic pass's own setup region (DESIGN.md §22.442). Reported separately from the concolic one
    // because the two engines can disagree: this pass replays every PATH from the entry, so it pays for the
    // region far more often, and its memory model (arrays, symbolic offsets) can leave values the concolic
    // domain never produces -- a refusal here with a reuse there is a real and useful thing to see.
    if (sr.setupSeen && sr.setupReused) {
      char rs[48];
      std::snprintf(rs, sizeof rs, "%.3f", sr.setupSecRestore);
      er.assumptions.push_back({"setup_region",
          "the symbolic escalation pass reused the same declared setup region: it ran ONCE (" +
          std::to_string(sr.setupOps) + " interpreter steps, " + std::to_string(sr.setupObjects) +
          " objects) and was restored on " + std::to_string(sr.setupSkips) + " of " +
          std::to_string(sr.pathsExplored) + " path(s), costing " + rs +
          "s. No path forks inside the region, so what it does is one execution, not a space", {}});
    }
    if (sr.setupSeen && !sr.setupReused)
      er.assumptions.push_back({"setup_region",
          "the symbolic escalation pass did NOT reuse the declared setup region -- it ran on every path: " +
          sr.setupRefusal + ". No path forks inside it either way", {}});
    if (sr.overApprox) er.assumptions.push_back({"precision", "symbolic memory accesses with symbolic offsets were over-approximated (object contents forgotten); findings are replay-checked", {}});
    if (!sr.complete) er.incomplete.push_back({sr.reason.empty() ? "incomplete" : "symbolic_" + sr.reason, sr.note});
    loopCut += sr.loopCut;
  }
  if (loopCut || tr.loopCut)
    er.incomplete.push_back({"loop_bound", std::to_string(loopCut + tr.loopCut) + " execution(s) were cut when a loop ran more than " + std::to_string(opt.loopBound) + " iterations (--loop-bound): bugs that need longer loops are not covered"});
  // ---- the project's own initialiser(s), when the spec named any (`init:`, DESIGN.md §22.368).
  //
  // Running them is not an approximation: it is the program's own code, executed, and it is the only way the
  // globals a handler reads hold the values it is really called with. But it is still a CHOICE that shapes every
  // verdict below it, and an initialiser with configuration-dependent branches (`if (is_t234()) ... else ...`)
  // pins the whole scan to one configuration, so a defect reachable only under another one is hidden. That is a
  // narrowing, and §22.361's rule is that a narrowing may never be invisible.
  if (!plan.prologue.empty()) {
    std::string names;
    for (auto &pc : plan.prologue) {
      names += (names.empty() ? "" : ", ") + ("@" + pc.function);
      er.initFunctions.push_back(pc.function);  // a reproduction has to run the same ones, in this order
    }
    report::Assumption ia;
    ia.category = "project_init";
    ia.text = "the project's own initialiser(s) " + names +
              " ran in full before this entry, so the globals it reads hold what they set. They were executed ONCE "
              "and the resulting state reused for every run and path, so any branch inside them -- on a "
              "configuration (SoC id, safety build, virtualisation) or on an unmodelled external's result -- was "
              "decided one way, and the state the other way produces is not analysed. The program was started with "
              "NO command-line options (argc = 1, argv = { name, NULL }, and `getopt` answers accordingly), so "
              "whatever an option would have configured keeps its default";
    er.assumptions.insert(er.assumptions.begin() + static_cast<long>(std::min(globalAssumptionAt, er.assumptions.size())), ia);
  }
  // ---- thread/work creation callbacks called directly (`--spawn-callbacks`, DESIGN.md §22.372).
  //
  // Two opposite departures in one change, which is why it has to be named rather than counted as a free win:
  // the callback's body becomes reachable (a WIDENING: code that was a blind spot is now analysed), and it is
  // executed as if the thread had run to completion at the creation point (a NARROWING in sequencing: no
  // interleaving with the code that follows is explored, so a race between them is still invisible).
  if (opt.spawnCallbacks) {
    report::Assumption sp;
    sp.category = "spawn_callback";
    sp.text = std::to_string(opt.spawnCallbacks) +
              " thread/work creation call(s) had their callback executed directly, once, at the point of creation. "
              "The body of the thread is therefore analysed, but it is analysed as if it had run to completion "
              "before the creating code continued: no interleaving between them is explored, so a race between the "
              "thread and its creator is not covered by this run";
    er.assumptions.insert(er.assumptions.begin() + static_cast<long>(std::min(globalAssumptionAt, er.assumptions.size())), sp);
  }
  // ---- G2: globals the program never wrote, promoted to unconstrained (DESIGN.md §22.374).
  //
  // This REMOVES the §22.362 narrowing rather than adding one: until now such a global kept its static
  // initialiser and the branch it gates was decided concretely with NO FORK, so the edge the real module would
  // take was never explored. It is a widening and cannot hide a defect. What it still assumes is that the value
  // is unconstrained rather than whatever the module's own initialiser would really have set.
  // The automatic seed (§22.386). Where a search STARTS is a configuration, not a property of the program, and a
  // reader comparing two scans of the same code has to be able to see that this one did not start from zeros.
  if (!tr.autoSeedBytes.empty()) {
    std::vector<uint8_t> sb = tr.autoSeedBytes;
    while (!sb.empty() && !sb.back()) sb.pop_back();  // anything a C string parser reads stops at the first NUL
    std::string asc;
    for (uint8_t c : sb) {
      if (c >= 0x20 && c < 0x7f) { asc += static_cast<char>(c); continue; }
      char hx[5];
      snprintf(hx, sizeof hx, "\\x%02x", c);
      asc += hx;
    }
    report::Assumption as;
    as.category = "auto_seed";
    as.text = "the first run did not start from zeroed attacker bytes: " + std::to_string(tr.autoSeedProbes) +
              " candidate(s) were derived by asking the solver to flip the deepest branch of the run before them, "
              "and the one covering the most branch edges was kept (" + std::to_string(tr.autoSeedBlocks) + " vs " +
              std::to_string(tr.autoSeedBaseline) + " blocks for zeros): \"" + asc +
              "\". Each candidate is a model of a real path condition, so it reaches what it reaches by construction. "
              "This changes where the search starts, never what the program is allowed to do -- but a scan that "
              "found something from here is not evidence that a scan from zeros would";
    er.assumptions.push_back(as);
  }
  if (tr.globalsPromoted) {
    report::Assumption gp;
    gp.category = "promoted_global";
    gp.text = std::to_string(tr.globalsPromoted) +
              " global(s) this entry reads were never written by the program, so instead of keeping their static "
              "initialiser they were given an unconstrained value and both edges of the branches they gate are "
              "explored. Only globals in the measured read set are promoted -- one the entry never reads keeps its "
              "initial value, which bounds the cost but means the set is as complete as the first pass's coverage. "
              "A POINTER field of such a global is materialised on demand as a fresh blank object rather than read "
              "as NULL (invented bytes carry no provenance, so without this every promoted pointer is NULL whatever "
              "the solver picks): out there nothing is bounded by its real struct and nothing is null, the same "
              "trade the synthesis_frontier assumption states";
    er.assumptions.insert(er.assumptions.begin() + static_cast<long>(std::min(globalAssumptionAt, er.assumptions.size())), gp);
  }
  // ---- the command line the initialiser was run with (§22.380). Stating one is a CHOICE of configuration and
  // NOT stating one is a stronger claim still -- "this program is started with no options" -- which for anything
  // with a mandatory option is false, and was false silently: <driver>'s `main` returned at its first check and its
  // whole initialiser was skipped with nothing in the report to show for it.
  if (!plan.prologue.empty()) {
    bool takesArgs = false;
    for (auto &pc : plan.prologue) takesArgs |= !pc.paramTys.empty();
    if (takesArgs) {
      if (!opt.initArgv.empty()) {
        std::string cl;
        for (size_t i = 0; i < opt.initArgv.size(); ++i) cl += (i ? " " : "") + opt.initArgv[i];
        er.assumptions.push_back({"project_init",
                                  "the initialiser was run with the command line the project states in " + opt.externsPath +
                                      ": `" + cl + "`. A module that branches on its options is analysed for THIS "
                                      "configuration only; another command line is another scan",
                                  {}});
      } else {
        er.assumptions.push_back({"project_init",
                                  "no command line was stated for the initialiser, so it was run with argc = 1 and "
                                  "argv = { \"prog\", NULL } -- the claim that this program is started with no "
                                  "options. If any of its options is mandatory that claim is false and the "
                                  "initialiser will have returned at its first check, leaving every global at its "
                                  "static value. State the real one as `argv:` in an --externs file",
                                  {}});
      }
    }
  }
  if (!opt.ubContinue.empty()) {
    std::string ks;
    for (UBKind k : opt.ubContinue) { if (!ks.empty()) ks += ", "; ks += ubKindName(k); }
    er.assumptions.push_back({"attacker_model",
                              "--ub-continue " + ks +
                                  ": runs did NOT stop at these undefined behaviours, they were recorded and walked "
                                  "past. Everything reported beyond such a site is reasoned about on an execution "
                                  "the C standard does not define, which is a deliberate choice made for this "
                                  "target, not a property the engine proved",
                              {}});
  }
  // ---- externals that wrote a buffer with contents their model does not state (§22.377). This is a WIDENING --
  // the alternative, saying nothing, leaves the buffer holding whatever it held, which is how a scan reports
  // `safe` about a struct the real library had long since filled in. §22.361 says a widening is named too, and
  // here the name matters doubly: it tells the reader which model to make precise to turn the resulting warnings
  // into verdicts.
  if (!tr.unknownWrites.empty()) {
    std::string fns;
    size_t shown = 0;
    for (auto &kv : tr.unknownWrites) {
      if (shown >= 8) { fns += ", ..."; break; }
      if (shown++) fns += ", ";
      fns += "@" + kv.first;
    }
    er.assumptions.push_back({"unknown_external_write",
                              "the model(s) for " + fns +
                                  " say these functions write a buffer the caller owns but not what they write into "
                                  "it, so those bytes are unknown and belong to nobody: branches they gate are "
                                  "explored both ways, and a finding that rests only on them is reported as the "
                                  "analysis's own invention (a warning) rather than as a defect anyone can trigger. "
                                  "Giving the model real contents is what turns such a warning into a verdict",
                              {}});
  }
  // ---- the container_of pointer-arithmetic waiver (frontend::LowerResult::containerOfWaived, §22.368).
  //
  // `container_of(p, T, member)` subtracts a member offset from a pointer, which on an empty list lands BEFORE the
  // object -- `list_for_each_entry`'s first step, where the result is immediately compared and never dereferenced.
  // The arithmetic check on that expression is waived. Waiving a check is a NARROWING and §22.361 says a narrowing
  // may not be invisible, so it is named here even though what it can hide is bounded: every DEREFERENCE through
  // such a pointer still goes through the ordinary out-of-bounds check.
  if (opt.containerOfWaived) {
    report::Assumption ca;
    ca.category = "container_of_waiver";
    ca.text = std::to_string(opt.containerOfWaived) +
              " container_of expression(s) in this module compute a pointer by subtracting a member offset, and the "
              "pointer-arithmetic check on them is waived (on an empty list the idiom legitimately lands before the "
              "object and never dereferences the result" +
              (opt.containerOfFirstSite.empty() ? std::string() : ", first at " + opt.containerOfFirstSite) +
              "). Dereferencing such a pointer out of bounds is still reported; computing one is not";
    er.assumptions.insert(er.assumptions.begin() + static_cast<long>(std::min(globalAssumptionAt, er.assumptions.size())), ca);
  }
  // ---- the session constructor could not succeed here. Named, so the reason is the CAUSE and not the symptom:
  // without this the entry just reports `no_run_completed`, which says an execution was cut but not that the
  // constructor is why, nor what to do about it. (sound/core: `snd_ctl_open` looks its card up by `iminor(inode)`
  // and the card is registered by a driver that is not in the scan set, so it can only return -ENODEV.)
  if (tr.setupInfeasible && plan.setup.valid)
    er.incomplete.push_back({"setup_infeasible",
                             "the session constructor @" + plan.setup.function +
                                 " cannot succeed in this scan set, so no execution got past it. Either add the code that "
                                 "creates the object it looks up (for a device handler, the driver that registers the device) "
                                 "to the link set, or state the constructor's preconditions in the spec. The analysis fell "
                                 "back to synthesising the session field by field"});
  // ---- the session constructor, when the spec named one (`setup:`, DESIGN.md §22.368 §7).
  //
  // This REPLACES a narrowing with a smaller one. Without it the report says the session "degrades to kernel-owned
  // untainted state" -- an object built field by field, whose fields are individually legal and jointly impossible
  // (§22.365). With it the object is what the module's own constructor actually produced. What is still assumed:
  // the constructor SUCCEEDED, and its other parameters were zeroed context rather than whatever a real caller
  // passes. Both are narrowings, so both are named.
  if (plan.setup.valid) {
    er.setupFunction = plan.setup.function;
    report::Assumption sa;
    sa.category = "session_ctor";
    sa.text = "the session object this entry is handed was built by running the module's own constructor @" +
              plan.setup.function + ", not synthesised field by field" +
              (plan.setup.success.empty() ? std::string() : ", and it was assumed to succeed (" + plan.setup.success + ")") +
              ". Its other parameters were zeroed objects standing for the kernel-owned context a real caller "
              "passes, and any configuration-dependent branch inside it was decided one way";
    er.assumptions.insert(er.assumptions.begin() + static_cast<long>(std::min(globalAssumptionAt, er.assumptions.size())), sa);
  }
  // ---- the global-initial-value narrowing, now that the runs are in.
  // A branch decided by a global the program never wrote rests on the whole module not having run: `module_init`
  // and the other internal initialisers are never executed, so the global still holds its static initialiser's
  // value (or zero). Worse than an ordinary narrowing, it cuts BOTH ways at once -- the branch is decided
  // concretely with no fork, so the edge the real module would take may never be explored, while the edge it would
  // not take is explored and can produce a `replay: confirmed` finding for code that is dead in reality. Until
  // §22.362's follow-up makes these symbolic, the only honest thing to do is to name it (DESIGN.md §22.362).
  if (!tr.globalGatedBy.empty()) {
    std::string names;
    size_t i = 0;
    for (auto &kv : tr.globalGatedBy) {
      if (i == 8) { names += ", ... (" + std::to_string(tr.globalGatedBy.size() - 8) + " more)"; break; }
      names += (i++ ? ", " : "") + kv.first;
    }
    report::Assumption ga;
    ga.category = "global_initial_value";
    ga.text = std::to_string(tr.globalGatedSites.size()) +
              " branch(es) read a global no function of the module had written, so they were decided by its static initialiser (or zero): " + names +
              ". module_init and the other internal initialisers are not executed, and the branch is taken concretely without a fork, so the opposite edge is not explored either";
    ga.loc = toLoc(tr.globalGatedBy.begin()->second);
    er.assumptions.insert(er.assumptions.begin() + static_cast<long>(std::min(globalAssumptionAt, er.assumptions.size())), ga);
  }
  // what was checked, and what attacker data reached (DESIGN.md §22.369)
  for (auto &kv : tr.checks) {
    report::CheckSummary cs;
    cs.kind = ubKindName(static_cast<UBKind>(kv.first));
    cs.reached = kv.second.reached; cs.decidedConcretely = kv.second.decidedConcretely;
    cs.queried = kv.second.queried; cs.sat = kv.second.sat; cs.unsat = kv.second.unsat;
    er.checks.push_back(std::move(cs));
  }
  // A memory-safety check that was REACHED many times and never once handed to the solver means its
  // condition was never symbolic -- the engine decided every one of them concretely. That is the signature
  // of DESIGN.md §22.388, where a missing source file left the conversion helpers opaque, taint died at
  // every char->value conversion, and 575875 checks were settled without a single query; the CVE was then
  // found by stumbling rather than solving, and two wrong diagnoses were written before anyone looked at
  // this number. Until now finding it took a hand-written `python3 -c` over the JSON.
  //
  // It is NOT always a defect, and the wording says so. §22.394 is the honest counter-example: a string
  // length produced by a scan is a loop induction variable, so on any single concolic path the branches have
  // already fixed it and the index is concrete for a structural reason. The two are told apart by what else
  // the report says -- an empty `opaque_calls` and a large flippable-branch count mean taint IS arriving and
  // the cause is the second kind.
  {
    const unsigned long long kMinReached = 1000;   // below this the absence of queries says nothing
    for (const auto &c : er.checks) {
      const bool memorySafety = c.kind == "oob_read" || c.kind == "oob_write" || c.kind == "ptr_arith_oob";
      if (!memorySafety || c.queried != 0 || c.reached < kMinReached) continue;
      report::Assumption a;
      a.category = "checks_never_symbolic";
      a.text = c.kind + ": " + std::to_string(c.reached) +
               " check(s) reached, none queried -- every one was decided concretely, so the solver was never "
               "asked whether this check CAN fail. Either attacker data is not reaching the condition (look at "
               "opaque_calls and docs/SCAN_SETUP_CHECKLIST.md first) or the index is a loop counter the path "
               "has already pinned, which is normal. An empty opaque_calls with a large flippable-branch count "
               "means the second";
      er.assumptions.push_back(std::move(a));
    }
  }
  {  // the target set, with runtime object ids mapped back to the parameter names the spec uses
    std::map<unsigned, std::string> byId;
    for (auto &kv : wp.objId) byId[kv.second] = kv.first;
    // Name each location the best way available, then MERGE the ones that end up with the same name. Two runtime
    // objects of the same record type, or from the same allocation site, are one piece of program state read at
    // two moments; reporting them as `obj:47` and `obj:51` split one fact into two unmatchable ones (§22.375).
    std::map<std::string, std::set<uint64_t>> merged;
    for (auto &kv : tr.reads) {
      std::string loc = kv.first;
      if (loc.rfind("obj:", 0) == 0 && loc.size() > 4 && isdigit(static_cast<unsigned char>(loc[4]))) {
        unsigned id = static_cast<unsigned>(std::stoul(loc.substr(4)));
        auto nm = byId.find(id);
        if (nm != byId.end()) loc = nm->second;  // a harness parameter: the spec's own name beats everything
        else {
          auto sk = tr.objKeys.find(id);
          loc = sk != tr.objKeys.end() ? "obj:" + sk->second : "obj:#" + std::to_string(id);
        }
      }
      merged[loc].insert(kv.second.begin(), kv.second.end());
    }
    for (auto &kv : merged) {
      report::EntryReport::ReadSet rs;
      rs.location = kv.first;
      rs.offsets.assign(kv.second.begin(), kv.second.end());
      er.reads.push_back(std::move(rs));
    }
    er.readsIncomplete = tr.readsIncomplete;
  }
  for (auto &kv : tr.opaqueCalls) er.opaqueCalls.push_back(kv);
  std::sort(er.opaqueCalls.begin(), er.opaqueCalls.end(), [](auto &a, auto &b) { return a.second > b.second; });
  // Search-budget profile (§22.392), and -- when some function is enumerating what a solver could decide in one
  // step -- an assumption saying so. It is an assumption and not an `incomplete` on purpose: a diluted budget
  // makes a `safe` weaker in a way `frontier_dropped` and `run_limit` already report when it actually bites, and
  // promoting it to a verdict-changing code here would reclassify entries that are genuinely finished.
  er.flippablePcsTotal = tr.flippablePcsTotal;
  er.setupRegion.declared = tr.setupRegionSeen;
  er.setupRegion.reused = tr.setupRegionReused;
  er.setupRegion.refusal = tr.setupRegionRefusal;
  er.setupRegion.ops = tr.setupRegionOps;
  er.setupRegion.skips = tr.setupRegionSkips;
  er.setupRegion.secRestore = tr.setupRegionSecRestore;
  er.setupRegion.allocsForced = tr.setupRegionAllocs;
  er.setupRegion.objects = tr.setupRegionObjects;
  er.setupRegion.symbolic = tr.setupRegionSymbolic;
  // A reused region is an UNDER-APPROXIMATION the harness asked for, so it is listed with the other assumptions
  // and not merely in the metrics: conditions inside the region were not offered to the search, and anything the
  // region would have done differently on a later run did not happen.
  if (er.setupRegion.declared && er.setupRegion.reused)
    er.assumptions.push_back({"setup_region",
        "the harness declared a deterministic setup region (hlir_setup_begin/hlir_setup_end); it ran ONCE (" +
        std::to_string(er.setupRegion.ops) + " interpreter steps, " + std::to_string(er.setupRegion.objects) +
        " objects) and was restored on " + std::to_string(er.setupRegion.skips) +
        " later run(s). Branch conditions inside it were not offered to the search; " +
        std::to_string(er.setupRegion.symbolic) +
        " value(s) it produced were FROZEN to what that one execution computed, so nothing downstream explores "
        "them; " + std::to_string(er.setupRegion.allocsForced) +
        " allocation(s) in it were taken as SUCCEEDING, so an allocation-failure path inside the region is not "
        "analysed; and the region is assumed to produce the same state on every run -- a property of the "
        "harness, not one the engine proved", {}});
  if (er.setupRegion.declared && !er.setupRegion.reused)
    er.assumptions.push_back({"setup_region",
        "the harness declared a deterministic setup region but the engine REFUSED to reuse it, so it was "
        "executed on every run: " + er.setupRegion.refusal +
        ". It is still a declared region: its branch conditions were not offered to the search and " +
        std::to_string(er.setupRegion.allocsForced) + " allocation(s) in it were taken as succeeding", {}});
  for (auto &s : tr.frontier)
    er.frontier.push_back({s.function, s.flippablePcs, s.queued, s.calls, s.share, s.perCall, s.library, s.foldCandidate, s.checksReached, s.checksQueried});
  for (auto &s : er.frontier) {
    if (!s.foldCandidate) continue;
    char pct[16];
    std::snprintf(pct, sizeof pct, "%.0f%%", 100.0 * s.share);
    er.assumptions.push_back({"search_budget",
                              std::string(pct) + " of the search's flippable branch conditions are inside @" + s.function +
                                  ", which costs " + std::to_string(static_cast<unsigned>(s.perCall + 0.5)) +
                                  " independent decisions per call: the budget is being spent enumerating a choice a closed "
                                  "form would hand the solver as one disjunction (DESIGN.md §22.385)",
                              {}});
  }
  er.taintReach.memoryIndex = tr.taintReach.memoryIndex;
  er.taintReach.loopBound = tr.taintReach.loopBound;
  er.taintReach.allocSize = tr.taintReach.allocSize;
  er.taintReach.sink = tr.taintReach.sink;
  er.coverage = computeCoverage(*full, hn, tr, tr.terminations, wp, sr.blocksVisited, &out.edgeKeys, &out.blockKeys, opt.listMissedBranches);
  if (!tr.runs.empty() && tr.runsReturned == 0 && found.empty()) {
    // no run finished: the verdict would rest on paths that were cut or ended at a noreturn call, never on a complete execution
    if (tr.runsTerminated > 0) {
      const auto &t = er.coverage.terminations.empty() ? report::TerminationSite{} : er.coverage.terminations.front();
      er.incomplete.push_back({"no_run_completed", "every run ended at a noreturn call or abort (most often " + t.by + " in @" + t.function +
                                                     (t.loc.valid() ? " at " + t.loc.file + ":" + std::to_string(t.loc.line) : std::string()) +
                                                     "): the code after it was not analysed"});
    } else {
      er.incomplete.push_back({"no_run_completed", "no run finished (" + std::to_string(tr.runs.size()) + " run(s) were cut by a bound or limit before the entry returned): the verdict is not based on any complete execution"});
    }
  }
  if (opt.minCoverage > 0 && er.coverage.blocksReachable > 0 && er.coverage.blockRatio() < opt.minCoverage) {
    char buf[96];
    std::snprintf(buf, sizeof buf, "%.1f%% of the reachable blocks were entered (required: %.1f%%)", 100.0 * er.coverage.blockRatio(), 100.0 * opt.minCoverage);
    er.incomplete.push_back({"low_coverage", buf});
  }

  for (auto &kv : found) er.findings.push_back(std::move(kv.second));
  std::stable_sort(er.findings.begin(), er.findings.end(), [](const report::Finding &a, const report::Finding &b) {
    return (a.replay == report::ReplayStatus::NotReproduced) < (b.replay == report::ReplayStatus::NotReproduced);
  });
  for (auto &f : er.findings)
    if (f.replay == report::ReplayStatus::NotReproduced && !f.inPrologue) {
      // `inPrologue` is excluded for the same reason it is excluded from the verdict: a finding in the project
      // initialiser is a fact about init code the entry's attacker never drives, so it may not turn this entry's
      // result into `unknown` either. Leaving it in was measured on sound/core round 49d -- 74 of 87 entries came
      // back `unknown` with every one of them citing an unreproduced prologue warning, which is the same hijack as
      // round 49b's `bug`, one verdict further along (DESIGN.md §22.368).
      er.incomplete.push_back({"unconfirmed_findings", "finding " + f.id + " was not reproduced by replay [" + f.unconfirmedReason + "]"});
      break;
    }
  (void)escalated;
  er.verdict = report::computeVerdict(er);
  er.metrics.secondsAnalysis = secondsSince(tAnalysis);
  er.metrics.secondsTotal = secondsSince(tStart);
  out.ok = true;
  return out;
}

}  // namespace hlir::driver

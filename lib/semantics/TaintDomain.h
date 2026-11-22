// Private. The taint-selective value domain (DESIGN.md §20): every value is a concrete APInt plus, only when it
// depends on attacker-controlled data, a taint label set and an SMT term. Untainted computation never builds a term;
// tainted computation records what the SMT query needs (path constraints, query sites, environment facts).
//
// This is concolic execution: the run follows the concrete seed, tainted branch conditions are recorded as path
// constraints, and the driver (Taint.cpp) solves "prefix + negated branch" to produce the next input.
#pragma once
#include <optional>
#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "ConcreteDomain.h"
#include "Machine.h"
#include "TermOps.h"

namespace hlir {

struct TVal {
  llvm::APInt conc{1, 0};
  smt::TermRef sym = nullptr;  // set iff tainted
  uint32_t labels = 0;         // bit set over TaintDomain::labels()
  // NOTE the name: this asks "does this value have a symbolic term", NOT "is this attacker data". The two are not
  // the same -- the harness promotes its OWN structural choices (is this optional pointer absent? which funcptr
  // target?) to symbolic so both configurations get explored, and those are symbolic without being anyone's input.
  // Every solver-plumbing use below wants this meaning. The three SECURITY verdicts (taint sink, loop bound, index)
  // want the other one and must ask TaintDomain::isAttackerControlled instead (DESIGN.md §22.363).
  bool tainted() const { return sym != nullptr; }
};

// A tainted branch / assumption seen on the executed path, in execution order. The term is true on this run.
struct PcEntry {
  smt::TermRef cond;
  bool flippable;              // a real branch (can be negated to reach a new path)
  unsigned depth;              // call depth (1 = harness callee)
  const Op *site;
  std::string function;
  bool dir = true;             // flippable branches: the direction this run took (the branch op + direction identify a covered edge)
  // This entry is not a decision the program made: it records that the engine PINNED a symbolic value to this
  // run's concrete one (today: the length of a bulk copy/fill, Memory.h `bulk`). It must stay in the path
  // condition for SAFETY queries -- dropping it is what DESIGN.md Sec.22.457 fixed -- but it must NOT constrain
  // a branch flip, whose whole purpose is to produce a DIFFERENT input. Left in, it says "the next input must
  // keep this length", and since the length is usually derived from the attacker bytes themselves that pins the
  // entire input: measured on CVE-2021-3575, 253 of 253 flip queries came back UNSAT and the search never
  // produced a second run (DESIGN.md Sec.22.467).
  bool concretisation = false;
};

struct QuerySiteRec {
  smt::TermRef bad;            // Bool: the check is violated
  size_t pcCount;              // path constraints that held when the check ran (prefix of the pc list)
  Finding finding;
};

// A concrete value that a tainted computation or query depends on (DESIGN.md §20.6).
struct EnvFactRec {
  llvm::APInt value;
  const Op *op;                // the consuming op
  std::string function;
};

struct SourceRec {
  std::string name;
  unsigned width;
  std::string label;
};

struct NondetRec {
  std::string name;
  llvm::APInt value;
};

struct FuncCounters {
  uint64_t ops = 0, pcs = 0, queries = 0, sources = 0, outTaint = 0, kills = 0;
};

struct TaintDomainConfig {
  std::set<std::string> promote;   // nondet names promoted to symbolic inputs even without a taint attribute
  bool promoteAll = false;
  std::string inputLabel = "input";
  std::map<std::string, std::vector<uint8_t>> labelSeeds;  // TaintConfig::labelSeeds
  unsigned dropPcsAboveDepth = 0;  // debugging/regression aid: forget path constraints from deeper callees (0 = off)
  // Name recorded in PcEntry::function for a branch evaluated at call depth 0 (directly in the harness/entry
  // function's own body, before any core.call has been pushed) -- Taint.cpp sets this to the actual entry function
  // name it is about to run() so that --reach-target's call-graph distance lookup (keyed by real function names,
  // see ReachTarget.h) can find it; left at the literal "<entry>" sentinel for any other TaintDomain construction
  // (keeps prior behaviour unchanged there, since "<entry>" deliberately never matches a real function name).
  std::string entryFunction = "<entry>";
};

class TaintDomain {
 public:
  using Val = TVal;
  static constexpr bool kExact = true;  // pointers are concrete; tainted pointer values are concretised
  static constexpr bool kArrays = false;
  static constexpr bool kTaint = true;

  TaintDomain(smt::TermManager &tm, const std::map<std::string, llvm::APInt> &seed, TaintDomainConfig cfg)
      : ops_(tm), tm_(tm), seed_(seed), cfg_(std::move(cfg)) {}

  // ---------------------------------------------------------------- recorded slice
  const std::vector<PcEntry> &pcs() const { return pcs_; }
  const std::vector<QuerySiteRec> &queries() const { return queries_; }
  const std::vector<EnvFactRec> &envFacts() const { return envFacts_; }
  const std::vector<SourceRec> &sources() const { return sources_; }
  const std::vector<NondetRec> &nondetOrder() const { return nondets_; }
  const std::map<std::string, llvm::APInt> &varValues() const { return varConc_; }
  const std::vector<Finding> &concreteFindings() const { return concreteFindings_; }
  const std::vector<std::string> &labels() const { return labels_; }
  uint64_t taintedOps() const { return cnt_.ops; }
  uint64_t concretizedPointers() const { return concretized_; }
  // A tainted address this run resolved by SELECTION instead of by concretising it (Memory.h
  // symStoreTargets). Counted separately because it is the opposite of a precision loss -- but it
  // must still reach the escalation gate, which is why it exists at all: see Sec.22.487. The gate
  // asks "was there tainted addressing the concolic engine could not settle on its own", and before
  // selection every one of these answered it through concretizedPointers.
  uint64_t selectedAddresses() const { return selectedAddrs_; }
  void noteSelectedAddress() { ++selectedAddrs_; }
  struct ClassStats { uint64_t calls = 0, inert = 0, observer = 0, transformer = 0, source = 0, sanitizer = 0; };
  const std::map<std::string, ClassStats> &functionClasses() const { return classes_; }
  std::map<std::string, FuncCounters> functionActivity() const { return activity_; }
  // One (caller, callee) call-graph edge: how many times this run executed it, and whether any of those calls touched
  // tainted data (see onReturn: the same "inert vs. not" test as FunctionTaintClass, applied per edge instead of per
  // function). Used to render the taint-highlighted call graph (tools/hlir-taint --format dot).
  struct EdgeStats { uint64_t calls = 0; bool tainted = false; };
  const std::map<std::pair<std::string, std::string>, EdgeStats> &callEdges() const { return edges_; }

  // ---------------------------------------------------------------- instrumentation hooks
  static bool isTainted(const Val &v) { return v.tainted(); }
  // Does this value carry a label that belongs to a real source (a parameter, a model's `source:`, a promoted
  // environment value) rather than only the harness's own structural choices? See kHarnessLabel.
  bool isAttackerControlled(const Val &v) const { return (v.labels & ~(harnessBit_ | frontierBit_)) != 0; }
  // Everything this value depends on was invented by the harness past the synthesis frontier -- no input, no model
  // source, not even a harness choice backed by evidence (a `nullable` field is nullable because some body in the
  // analysed set NULL-tests it, §22.353; frontier filler is backed by nothing at all, because the engine never
  // looked at that struct). A UB that only such a value can produce is a UB we wrote ourselves: it is reported,
  // with its witness, but as a warning, so it cannot turn an entry's verdict into `bug` (DESIGN.md §22.365).
  // `labels != 0` matters: a condition with NO labels is the program's own constant, i.e. a real defect.
  bool onlyFrontier(const Val &v) const { return frontierBit_ && v.labels != 0 && (v.labels & ~frontierBit_) == 0; }
  void beginOp(const Op &op) { curOp_ = &op; curTainted_ = false; }
  // Inside a harness-declared setup region (DESIGN.md §22.438) a tainted branch is still a path CONDITION but is
  // no longer an offer to the search: the region is executed once and restored afterwards, so a flip of a
  // condition inside it would move the solver's model and not the memory. Recording it as flippable would spend
  // runs on edges that cannot move. The constraint itself is kept, so nothing downstream is weakened.
  void setSetupRegion(bool on) { setupRegion_ = on; }
  // Drop the symbolic side of a value and keep the concrete one this run computed (DESIGN.md §22.438). Used only
  // on what a declared setup region leaves behind: freezing it is what makes the region replayable at all, and
  // the alternative is not "explore it" but "re-execute the region on every run and explore it there".
  // Attacker data is NEVER frozen. Freezing it would turn "the region reads the entry's input" into "every later
  // run sees the first run's input", which silently removes everything behind the region from the search and
  // reports nothing. A region that touches attacker data is a harness mistake, and refusing says so.
  std::optional<Val> freezeVal(const Val &v) {
    if (isAttackerControlled(v)) return std::nullopt;
    return Val{v.conc};
  }
  void onCall(const Function &f) {
    std::string caller = stack_.empty() ? std::string("<entry>") : stack_.back().fn->name;
    stack_.push_back({&f, cnt_, std::move(caller)});
  }
  void onReturn(const Function &f, const Val *ret) {
    if (stack_.empty() || stack_.back().fn != &f) return;
    FuncCounters s = stack_.back().snap;
    std::string caller = stack_.back().caller;
    stack_.pop_back();
    FuncCounters d;
    d.ops = cnt_.ops - s.ops;
    d.pcs = cnt_.pcs - s.pcs;
    d.queries = cnt_.queries - s.queries;
    d.sources = cnt_.sources - s.sources;
    d.outTaint = cnt_.outTaint - s.outTaint + ((ret && ret->tainted()) ? 1 : 0);
    d.kills = cnt_.kills - s.kills;
    ClassStats &c = classes_[f.name];
    ++c.calls;
    FuncCounters &a = activity_[f.name];
    a.ops += d.ops; a.pcs += d.pcs; a.queries += d.queries; a.sources += d.sources; a.outTaint += d.outTaint; a.kills += d.kills;
    bool inert = !(d.sources || d.kills || d.outTaint || d.ops || d.pcs || d.queries);
    if (d.sources) ++c.source;
    else if (d.kills && !d.outTaint) ++c.sanitizer;
    else if (d.outTaint) ++c.transformer;
    else if (d.ops || d.pcs || d.queries) ++c.observer;
    else ++c.inert;
    // Call-graph edge: this invocation of `f` from `caller` touched tainted data iff it was not classified inert above
    // (it introduced/observed/transformed/sanitized taint). A later call of the same edge that *is* inert does not
    // clear the flag: the edge is red if taint flowed through it on at least one occasion.
    EdgeStats &e = edges_[{caller, f.name}];
    ++e.calls;
    if (!inert) e.tainted = true;
  }
  void noteStore(const Val &v) { if (v.tainted()) { ++cnt_.outTaint; } }
  void noteKill() { ++cnt_.kills; }

  // ---------------------------------------------------------------- model support (see Machine::execModel)
  // Value produced by an external function: attacker controlled (symbolic, tainted) with a label, else the seed's value.
  Val modelInput(Env &, const std::string &name, unsigned w, const std::string &label, const std::optional<llvm::APInt> &dflt = std::nullopt) {
    if (dflt && !seed_.count(name)) fallback_[name] = dflt->zextOrTrunc(w);
    if (label.empty()) {
      llvm::APInt v = seedValue(name, w);
      varConc_[name] = v;
      return Val{v};
    }
    return source(name, w, label, false);
  }
  // `cur` after an opaque function call that reads `froms`: tainted (a fresh variable carrying their labels) iff any is.
  Val opaqueDerived(const Val &cur, const std::vector<Val> &froms, const std::string &name) {
    uint32_t labels = 0;
    for (auto &f : froms) labels |= f.labels;
    if (!labels) return cur;
    Val r = cur;
    r.sym = tm_.bvVar(name, cur.conc.getBitWidth());
    r.labels = labels;
    if (varConc_.emplace(name, cur.conc).second) { sources_.push_back({name, cur.conc.getBitWidth(), "derived"}); ++cnt_.sources; }
    return r;
  }
  Val clearTaint(const Val &v) { if (v.tainted()) ++cnt_.kills; return Val{v.conc}; }
  template <class MakeFinding>
  void taintSink(const Val &v, MakeFinding &&mk) {
    if (isAttackerControlled(v)) concreteFindings_.push_back(mk());  // a data-flow finding: the run goes on
  }
  // An attacker-controlled value governs a loop's iteration count. This is a DoS warning only when the count is
  // NOT held under a constant: a dominating guard (`if (n > C) return`) or a narrow type that caps every
  // attacker-controlled operand of the loop condition makes the loop run a bounded number of times, which is not
  // uncontrolled resource consumption. This mirrors indexWarn: given the condition's governing scalar operands,
  // we defer a query asking whether ANY of them can still exceed kLoopBoundWarnThreshold under the path
  // constraints. UNSAT means a constant cap is in force on this path (the `n <= 64` from a dominating guard, or a
  // uint8/uint16 load whose width alone bounds it) -- suppress. SAT means no constant bounds it -- warn. With no
  // attacker-controlled operand to threshold (an opaque/derived condition we cannot decompose), we keep the old
  // unconditional warning rather than silently drop it. Deduplicated per site by the driver; the run goes on.
  static constexpr uint64_t kLoopBoundWarnThreshold = 1ull << 16;
  static constexpr unsigned kLoopBoundWidth = 64;  // threshold is compared at this width; operands are zero-extended to it
  template <class MakeFinding>
  void taintLoopWarn(const Val &cond, const std::vector<std::pair<Val, bool>> &invBounds, bool variantTaint,
                     MakeFinding &&mk) {
    if (!isAttackerControlled(cond)) return;
    // A loop-variant attacker operand (an element re-read each iteration) means the trip count is not bounded by
    // any single value cap -- keep the warning. Likewise when we could not attribute the taint to any operand.
    if (variantTaint || invBounds.empty()) { concreteFindings_.push_back(mk()); return; }
    smt::TermRef bad = nullptr;
    for (const auto &bs : invBounds) {
      const Val &b = bs.first;
      bool sgn = bs.second;  // the loop compares this bound signed: a negative bound is 0 iterations, not huge
      if (!b.tainted() || !isAttackerControlled(b)) continue;
      unsigned w = b.conc.getBitWidth();
      // Compare at a fixed wide width so the threshold is representable regardless of the operand's width, extending
      // with the comparison's own signedness: a uint8/uint16 or dominating-guarded bound then provably cannot
      // exceed the cap. "can this exceed the cap?" is Sgt (signed loop) or Ugt (unsigned) over the extended term.
      smt::TermRef s = w < kLoopBoundWidth ? (sgn ? ops_.sext(b.sym, kLoopBoundWidth) : ops_.zext(b.sym, kLoopBoundWidth))
                       : w > kLoopBoundWidth ? ops_.trunc(b.sym, kLoopBoundWidth) : b.sym;
      smt::TermRef t = tm_.toBool(ops_.icmp(sgn ? Pred::Sgt : Pred::Ugt, s,
                                            tm_.bvConst(llvm::APInt(kLoopBoundWidth, kLoopBoundWarnThreshold))));
      if (t->isFalse()) continue;  // statically bounded (a constant, or a narrow extend the simplifier already folded)
      bad = bad ? tm_.mkOr(bad, t) : t;
    }
    // bad == null means every invariant bound is provably below the threshold on this path: suppress. Otherwise the
    // warning fires only if the solver finds `bad` satisfiable under the path constraints (no constant cap in force).
    if (bad) warnQueries_.push_back({bad, pcs_.size(), mk()});
  }
  // An attacker-controlled value is used as a memory index. A warning *unless* a constant upper bound is in force on
  // the current path (a fixed-range sanitizer check): we record "the index can exceed kIndexWarnThreshold under the
  // path constraints" as a solver query -- UNSAT means some constant below the threshold bounds it (suppress), SAT
  // means it is bounded only by a symbolic/attacker value or not at all (warn). A runtime `i < size` where size is
  // itself attacker-controlled is NOT a constant bound and still warns (per the stricter sanitizer rule).
  static constexpr uint64_t kIndexWarnThreshold = 1ull << 20;
  template <class MakeFinding>
  void indexWarn(const Val &idx, MakeFinding &&mk) {
    if (!idx.tainted() || !isAttackerControlled(idx)) return;  // `.sym` is used below, so BOTH questions apply here
    unsigned w = idx.conc.getBitWidth();
    smt::TermRef bad = tm_.toBool(ops_.icmp(Pred::Ugt, idx.sym, tm_.bvConst(llvm::APInt(w, kIndexWarnThreshold))));
    if (bad->isFalse()) return;  // already provably bounded (e.g. a constant mask): no query needed
    warnQueries_.push_back({bad, pcs_.size(), mk()});
  }
  const std::vector<QuerySiteRec> &warnQueries() const { return warnQueries_; }

  // ---------------------------------------------------------------- values
  static unsigned width(const Val &v) { return v.conc.getBitWidth(); }
  Val constant(const llvm::APInt &v) { return Val{v}; }
  Val zero(unsigned w) { return Val{llvm::APInt(w, 0)}; }
  Val allOnes(unsigned w) { return Val{llvm::APInt::getAllOnes(w)}; }
  Val smin(unsigned w) { return Val{llvm::APInt::getSignedMinValue(w)}; }

#define HLIR_TAINT_BIN(NAME, CNAME)                                                              \
  Val NAME(const Val &a, const Val &b) {                                                         \
    llvm::APInt c = ConcreteDomain::CNAME(a.conc, b.conc);                                       \
    if (!a.sym && !b.sym) return Val{c};                                                         \
    return mk(c, ops_.CNAME(sym(a, b), sym(b, a)), a.labels | b.labels);                        \
  }
  HLIR_TAINT_BIN(add, add) HLIR_TAINT_BIN(sub, sub) HLIR_TAINT_BIN(mul, mul)
  HLIR_TAINT_BIN(udiv, udiv) HLIR_TAINT_BIN(sdiv, sdiv) HLIR_TAINT_BIN(urem, urem) HLIR_TAINT_BIN(srem, srem)
  HLIR_TAINT_BIN(and_, and_) HLIR_TAINT_BIN(or_, or_) HLIR_TAINT_BIN(xor_, xor_)
  HLIR_TAINT_BIN(shl, shl) HLIR_TAINT_BIN(lshr, lshr) HLIR_TAINT_BIN(ashr, ashr)
  HLIR_TAINT_BIN(concat, concat)
#undef HLIR_TAINT_BIN

  Val not_(const Val &a) { return un(a, ConcreteDomain::not_(a.conc), [&](smt::TermRef s) { return ops_.not_(s); }); }
  Val neg(const Val &a) { return un(a, ConcreteDomain::neg(a.conc), [&](smt::TermRef s) { return ops_.neg(s); }); }
  Val zext(const Val &a, unsigned w) { return un(a, a.conc.zext(w), [&](smt::TermRef s) { return ops_.zext(s, w); }); }
  Val sext(const Val &a, unsigned w) { return un(a, a.conc.sext(w), [&](smt::TermRef s) { return ops_.sext(s, w); }); }
  Val trunc(const Val &a, unsigned w) { return un(a, a.conc.trunc(w), [&](smt::TermRef s) { return ops_.trunc(s, w); }); }
  Val extract(const Val &a, unsigned hi, unsigned lo) {
    return un(a, ConcreteDomain::extract(a.conc, hi, lo), [&](smt::TermRef s) { return ops_.extract(s, hi, lo); });
  }
  Val icmp(Pred p, const Val &a, const Val &b) {
    llvm::APInt c = ConcreteDomain::icmp(p, a.conc, b.conc);
    if (!a.sym && !b.sym) return Val{c};
    return mk(c, ops_.icmp(p, sym(a, b), sym(b, a)), a.labels | b.labels);
  }
  Val select(const Val &c, const Val &a, const Val &b) {
    llvm::APInt r = c.conc.getBoolValue() ? a.conc : b.conc;
    if (!c.sym && !a.sym && !b.sym) return Val{r};
    bool any = true;
    (void)any;
    return mk(r, ops_.select(sym(c, a, b), sym(a, c, b), sym(b, c, a)), c.labels | a.labels | b.labels);
  }

  std::string str(const Val &v, bool isBool = false) { return ConcreteDomain::str(v.conc, isBool) + (v.tainted() ? "*" : ""); }

  // ---------------------------------------------------------------- memory-model support
  // Evidence only: answer "is this symbolic" / "what concrete value does it carry" WITHOUT the
  // concretisation side effect constValue() has on the concolic domain (it counts a followed tainted
  // pointer, which would make the concretized_pointer assumption count reads that are only being
  // reported). Used by Memory::objEvidence (DESIGN.md §22.369).
  static bool isSymbolicVal(const Val &v) { return v.tainted(); }
  static std::optional<llvm::APInt> peekVal(const Val &v) { return v.conc; }
  std::optional<llvm::APInt> constValue(const Val &v) {
    if (v.tainted()) ++concretized_;  // a tainted address is followed concretely (policy: concretise)
    return v.conc;
  }
  static bool same(const Val &a, const Val &b) { return a.conc.getBitWidth() == b.conc.getBitWidth() && a.conc == b.conc && a.sym == b.sym; }
  static bool asIte(const Val &, Val &, Val &, Val &) { return false; }
  Val fresh(const std::string &, unsigned w) { return Val{llvm::APInt(w, 0)}; }
  // Bytes of an entry parameter object: concrete value from the seed, symbolic variable of the same name.
  Val input(Env &, const std::string &name, unsigned w) { return source(name, w, cfg_.inputLabel, /*unique=*/false); }
  // A byte of memory the harness invented rather than read from anywhere: the blank content past the synthesis
  // frontier (Memory::lazyFrontier, DESIGN.md §22.364). It must be SYMBOLIC -- a concrete 0 out there is the same
  // category of invention as the concrete NULL the frontier used to hand out, and it decides branches, divisors and
  // loop counts that nothing ever decided -- but it is the harness's own choice, not anyone's input, so it carries
  // only the reserved harness label and reads as not attacker-controlled (§22.363).
  Val harnessInput(Env &, const std::string &name, unsigned w) {
    frontierBit_ = labelBit(kFrontierLabel);
    return source(name, w, kFrontierLabel, /*unique=*/false);
  }

  // ---------------------------------------------------------------- control and properties
  bool decide(const Val &cond) {
    bool dir = cond.conc.getBoolValue();
    if (cond.tainted()) {
      smt::TermRef b = tm_.toBool(cond.sym);
      // A condition whose term has already constant-folded (Term.cpp's foldConst, e.g. because it traces back
      // to a single-point-pinned scalar -- see InitGen.cpp's single-point range handling) isn't a real branch
      // decision: there is nothing to flip, the outcome is provably fixed given what's already known, not just
      // "this run happened to take this direction". Recording it anyway would make a tight loop driven by such
      // a value generate one near-duplicate "flip this iteration's exit" candidate per iteration (confirmed
      // mechanism, docs/DESIGN.md Sec.22.304) for no benefit, since every single one is unsatisfiable to flip.
      if (!b->isConst()) addPc(dir ? b : tm_.mkNot(b), /*flippable=*/true, dir);
    }
    return dir;
  }
  template <class MakeFinding>
  bool violated(const Val &cond, MakeFinding &&mk) {
    if (cond.conc.getBoolValue()) {  // it really happens on this concrete execution
      concreteFindings_.push_back(mk());
      // The execution ends here, but inputs that pass the check continue: record the violation as a branch so the
      // driver can flip it and explore what follows (the symbolic engine also continues under "check passed").
      if (cond.tainted()) addPc(tm_.toBool(cond.sym), /*flippable=*/true);
      return true;
    }
    if (cond.tainted()) {  // it could happen for other inputs along this path: a query for the solver
      smt::TermRef b = tm_.toBool(cond.sym);
      if (b->isFalse()) return false;
      queries_.push_back({b, pcs_.size(), mk()});
      ++cnt_.queries;
      addPc(tm_.mkNot(b), /*flippable=*/false);  // execution continues only where the check passed
    }
    return false;
  }
  // An assumption that the concrete values violate but that depends on attacker input (a precondition on the content of a
  // parameter object): the engine solves "path so far AND this" to get a seed that satisfies it.
  struct Repair { size_t pcCount; smt::TermRef cond; };
  const std::optional<Repair> &repair() const { return repair_; }
  bool assume(const Val &cond) {
    if (!cond.conc.getBoolValue()) {
      if (cond.tainted() && !repair_) repair_ = Repair{pcs_.size(), tm_.toBool(cond.sym)};
      return false;
    }
    if (cond.tainted()) addPc(tm_.toBool(cond.sym), /*flippable=*/false);
    return true;
  }
  // `assume` for a fact the ENGINE imposed rather than one the program tested: see PcEntry::concretisation.
  bool assumeConcretisation(const Val &cond) {
    if (!cond.conc.getBoolValue()) {
      if (cond.tainted() && !repair_) repair_ = Repair{pcs_.size(), tm_.toBool(cond.sym)};
      return false;
    }
    if (cond.tainted()) addPc(tm_.toBool(cond.sym), /*flippable=*/false, /*dir=*/true, /*concretisation=*/true);
    return true;
  }
  Val nondet(Env &, const Op &op, unsigned width) {
    std::string base = "nd";
    if (const Attr *n = op.attr("name")) base = n->s;
    std::string label;
    if (const Attr *t = op.attr("taint")) label = t->s;
    bool promoted = !label.empty() || cfg_.promoteAll || cfg_.promote.count(base);
    // A promoted nondet with no taint attribute is the HARNESS's own choice, not an input of the program. It still
    // needs a symbolic term (otherwise the branch testing it is not a branch and the explorer can never take the
    // other side -- see InitVar::promote), but it must not read as attacker data to the security verdicts. It gets
    // a reserved label for that. It used to get "env", which is a REAL source label (models/libc.yaml gives it to
    // getenv's result), so the two shared one bit and could not be told apart.
    if (label.empty()) { label = kHarnessLabel; harnessBit_ = labelBit(kHarnessLabel); }
    unsigned k = nameCount_[base]++;
    std::string name = k ? base + "#" + std::to_string(k) : base;
    if (!promoted) {
      llvm::APInt v = seedValue(name, width);
      nondets_.push_back({name, v});
      varConc_[name] = v;
      return Val{v};
    }
    return source(name, width, label, true);
  }

  void finish() { curTainted_ = false; }

 private:
  struct Frame { const Function *fn; FuncCounters snap; std::string caller; };

  llvm::APInt seedValue(const std::string &name, unsigned w) {
    auto it = seed_.find(name);
    if (it != seed_.end()) return it->second.zextOrTrunc(w);
    auto fb = fallback_.find(name);
    return fb == fallback_.end() ? llvm::APInt(w, 0) : fb->second;
  }
  uint32_t labelBit(const std::string &l) {
    for (size_t i = 0; i < labels_.size(); ++i)
      if (labels_[i] == l) return 1u << i;
    labels_.push_back(l);
    return 1u << (labels_.size() - 1);
  }
  Val source(const std::string &name, unsigned w, const std::string &label, bool isNondet) {
    llvm::APInt v = seedValue(name, w);
    if (w == 8 && !seed_.count(name) && !fallback_.count(name) && !cfg_.labelSeeds.empty()) {  // see TaintConfig::labelSeeds
      auto ls = cfg_.labelSeeds.find(label);
      if (ls != cfg_.labelSeeds.end()) {
        auto ni = labelIdx_.find(name);
        if (ni == labelIdx_.end()) ni = labelIdx_.emplace(name, labelNext_[label]++).first;
        if (ni->second < ls->second.size()) v = llvm::APInt(8, ls->second[ni->second]);
      }
    }
    Val r;
    r.conc = v;
    r.sym = tm_.bvVar(name, w);
    r.labels = labelBit(label);
    if (varConc_.emplace(name, v).second) { sources_.push_back({name, w, label}); ++cnt_.sources; }
    if (isNondet) nondets_.push_back({name, v});
    return r;
  }
  Val mk(const llvm::APInt &c, smt::TermRef s, uint32_t labels) {
    if (!curTainted_) { curTainted_ = true; ++cnt_.ops; }
    Val r;
    r.conc = c;
    r.sym = s;
    r.labels = labels;
    return r;
  }
  // Symbolic term of `x`; an untainted operand mixed into a tainted computation becomes an environment fact.
  smt::TermRef sym(const Val &x, const Val &o1) { return symOf(x, o1.tainted()); }
  smt::TermRef sym(const Val &x, const Val &o1, const Val &o2) { return symOf(x, o1.tainted() || o2.tainted()); }
  smt::TermRef symOf(const Val &x, bool otherTainted) {
    if (x.sym) return x.sym;
    if (otherTainted && curOp_) {
      bool seen = false;
      for (auto it = envFacts_.rbegin(); it != envFacts_.rend() && it->op == curOp_; ++it) seen |= (it->value.getBitWidth() == x.conc.getBitWidth() && it->value == x.conc);
      if (!seen) envFacts_.push_back({x.conc, curOp_, stack_.empty() ? std::string("<entry>") : stack_.back().fn->name});
    }
    return tm_.bvConst(x.conc);
  }
  template <class F>
  Val un(const Val &a, const llvm::APInt &c, F f) {
    if (!a.sym) return Val{c};
    return mk(c, f(a.sym), a.labels);
  }
  void addPc(smt::TermRef cond, bool flippable, bool dir = true, bool concretisation = false) {
    unsigned depth = static_cast<unsigned>(stack_.size());
    if (cfg_.dropPcsAboveDepth && depth >= cfg_.dropPcsAboveDepth) return;
    if (setupRegion_) flippable = false;  // see setSetupRegion
    pcs_.push_back({cond, flippable, depth, curOp_, stack_.empty() ? cfg_.entryFunction : stack_.back().fn->name, dir,
                    concretisation});
    ++cnt_.pcs;
  }

  TermOps ops_;
  smt::TermManager &tm_;
  const std::map<std::string, llvm::APInt> &seed_;
  TaintDomainConfig cfg_;
  bool setupRegion_ = false;  // see setSetupRegion (DESIGN.md §22.438)
  std::vector<PcEntry> pcs_;
  std::optional<Repair> repair_;
  std::vector<QuerySiteRec> queries_;
  std::vector<QuerySiteRec> warnQueries_;  // index-warning candidates: solved like queries_ but with no path-constraint side effects
  std::vector<EnvFactRec> envFacts_;
  std::vector<SourceRec> sources_;
  std::vector<NondetRec> nondets_;
  std::map<std::string, llvm::APInt> varConc_;
  std::map<std::string, unsigned> nameCount_;
  std::map<std::string, unsigned> labelIdx_, labelNext_;  // label seed streams: input name -> index, next index per label
  std::map<std::string, llvm::APInt> fallback_;  // model-provided defaults for unseeded inputs
  std::vector<Finding> concreteFindings_;
  // Reserved: the label of a value the HARNESS made up, never of anything the program read. Never written in a
  // spec or a model -- `source:`/`taint:` entries naming it would collide, which is exactly the bug that made this
  // reserved name necessary.
  static constexpr const char *kHarnessLabel = "harness";
  // Frontier filler is a SECOND reserved label, not the same bit as `harness`: both are the harness's own doing and
  // neither is attacker data, but a `nullable` choice has evidence behind it and frontier filler has none, so only
  // the latter may disqualify a finding from counting as a defect. See onlyFrontier().
  static constexpr const char *kFrontierLabel = "frontier";
  uint32_t harnessBit_ = 0;   // 0 until a harness choice is first promoted, so `~harnessBit_` is then all-ones
  uint32_t frontierBit_ = 0;  // likewise for frontier filler
  std::vector<std::string> labels_;
  std::vector<Frame> stack_;
  FuncCounters cnt_;
  std::map<std::string, ClassStats> classes_;
  std::map<std::string, FuncCounters> activity_;
  std::map<std::pair<std::string, std::string>, EdgeStats> edges_;
  uint64_t concretized_ = 0;
  uint64_t selectedAddrs_ = 0;
  const Op *curOp_ = nullptr;
  bool curTainted_ = false;
};

}  // namespace hlir

// Private. The execution engine for `core`, generic over the value domain D (DESIGN.md §17.1-17.2).
// Every op's semantics is written once here; the concrete interpreter instantiates it with ConcreteDomain.
// Required of D: see ConcreteDomain (Val, width, constant, arithmetic, icmp, select, decide, str ...).
#pragma once
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstring>
#include <map>
#include <optional>
#include <set>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "hlir/semantics/Interpreter.h"
#include "hlir/ir/Loops.h"
#include <functional>

#include "FpEval.h"
#include "Memory.h"
#include "Pred.h"
#include "UBConditions.h"

namespace hlir {

// What a domain is told when a property can fail on the current path (see D::violated).
struct Finding {
  RunStatus status = RunStatus::UB;  // UB or AssertFailed
  std::optional<UBReport> ub;
  std::string message;
  Loc loc;
  const Op *site = nullptr;  // the failing op: identifies the finding across paths
  // The UB condition depends only on bytes the harness invented past the synthesis frontier (D::onlyFrontier).
  // Reported with its witness, but as a warning: it is our own invention failing, not the program (§22.365).
  bool frontierOnly = false;
  // `core.check.ptr_arith` only: the out-of-range pointer this check guards is never dereferenced -- every use of
  // it is a pointer comparison or a pointer difference. Reported as a warning (DESIGN.md §22.390).
  bool cmpOnlyPtr = false;
  // The site is inside one of the project initialisers the harness runs before the entry (RunConfig::prologueFns,
  // §22.368). A fact about init code, not about this handler's attack surface.
  bool inPrologue = false;
};

// The state a harness-declared deterministic setup region produced (DESIGN.md §22.438). Memory is the same
// snapshot the project-initialiser path already uses; what this adds is the LIVE REGISTERS of the harness frame
// and the position to resume at, because unlike the generated prologue (whose result the harness discards) a
// hand-written setup region's whole point is the value it leaves in a local -- libxml2's parsed `xmlSchemaPtr`.
template <class D>
struct SetupState : SetupCache {
  struct Reg { typename D::Val a{}, b{}; };
  std::vector<std::pair<const Value *, Reg>> regs;  // the harness frame's registers as the region left them
  const Function *fn = nullptr;                      // the frame the two markers were in; they must be the same
  size_t frameDepth = 0;
  const Block *resumeBlk = nullptr;                  // where to continue: the op right after `hlir.setup.end`
  size_t resumeIp = 0;
  typename Memory<D>::Snapshot snap;
};

template <class D>
class Machine {
 public:
  using Val = typename D::Val;

  Machine(D &d, const Module &m, Env &env, const RunConfig &cfg) : d_(d), mod_(m), env_(env), cfg_(cfg), mem_(d, m.ctx.ptrWidth()) {
    mem_.setBound(cfg.memBound);
    mem_.setMaxExpand(cfg.memExpandMax);
    mem_.setTableSelect(cfg.tableSelect);
    mem_.setStoreSelect(cfg.storeSelect);
    mem_.setInputSource([this](const std::string &name) { return d_.input(env_, name, 8); });
    mem_.setFrontierSource([this](const std::string &name) { return d_.harnessInput(env_, name, 8); });
  }

  RunResult run(const Function &entry, std::vector<Val> args) {
    std::vector<Slot> slots;
    for (auto &a : args) slots.push_back(Slot{std::move(a), Val{}});
    pushFrame(entry, std::move(slots), nullptr);
    event(TraceEvent::Call, entry.name, "entry", Loc{});
    while (!done_) {
      if (++res_.steps > cfg_.maxSteps) { stop(RunStatus::StepLimit, "step limit reached"); break; }
      if ((res_.steps & 1023) == 0 && std::chrono::steady_clock::now() >= cfg_.deadline) { stop(RunStatus::StepLimit, "time budget exhausted"); break; }
      step();
    }
    if (retslot_) retval_ = retslot_->a;
    if (cfg_.coverage) {
      res_.blocksVisited.assign(cov_.begin(), cov_.end());
      res_.branchesVisited.assign(branchCov_.begin(), branchCov_.end());
    }
    if constexpr (std::is_same_v<Val, llvm::APInt>)
      if (retval_) res_.returnValue = *retval_;
    return std::move(res_);
  }
  // The value returned by the entry function, in the domain's own representation (the obj part for pointers).
  const std::optional<Val> &returned() const { return retval_; }
  const Memory<D> &memory() const { return mem_; }

 private:
  using Ptr = PtrV<D>;
  // A register: an integer/bool uses `a`; a pointer is (obj = a, off = b).
  struct Slot {
    Val a{}, b{};
  };
  // Is the current execution inside one of the project initialisers the harness runs before the entry
  // (RunConfig::prologueFns, DESIGN.md §22.368)? Answered by looking at the live frames rather than by keeping a
  // counter, so there is no enter/leave bookkeeping to get out of step with the real stack. Called only when a
  // check has already been violated, which is rare, so walking the frames costs nothing on the hot path.
  // The executor's typed snapshot holder, if it gave us one of the right type. A mismatch is impossible with an
  // executor that built the cache for this domain, but a silent one would corrupt every object id, so it is
  // checked and simply means "re-run the initialiser".
  typename Memory<D>::Cache *prologueCache() const {
    return cfg_.prologueCache ? dynamic_cast<typename Memory<D>::Cache *>(cfg_.prologueCache) : nullptr;
  }
  // The typed holder for the harness-declared setup region (DESIGN.md §22.438), if the executor gave us one of
  // the right type. Same checked dynamic_cast as prologueCache(): a mismatch simply means "run the region".
  SetupState<D> *setupCache() const {
    return cfg_.setupCache ? dynamic_cast<SetupState<D> *>(cfg_.setupCache) : nullptr;
  }
  size_t setupBase_ = 0;
  uint64_t setupStartSteps_ = 0;
  bool capturingSetup_ = false;
  // Execution is between hlir_setup_begin() and hlir_setup_end(). Separate from capturingSetup_ on purpose: the
  // markers MEAN "this is setup", and what that means must not depend on whether this particular run happens to
  // be the one capturing, or on whether the state turned out to be reusable at all. Otherwise run 1 and run 7
  // would be analysing two different programs.
  bool inSetupRegion_ = false;
  // Objects the region wrote. Only the ones it CREATED live above setupBase_; a local of the harness frame is an
  // `alloca` made before the region and written inside it, and without this it was not saved at all.
  std::set<uint32_t> setupWrites_;
  // Registers the harness frame already held when the region began. Only registers the region ADDED are saved and
  // restored: the ones that were there are the entry's own inputs (libxml2's `in`, `in_len`), they are symbolic,
  // they differ per run by design, and writing the capturing run's values back over them would hand every later
  // run the first run's input.
  std::unordered_set<const Value *> setupRegsBefore_;
  // HLIR_SETUP_VERIFY (DESIGN.md §22.441): run the region AGAIN instead of restoring it, and report every way
  // the fresh state differs from the cached one. A checkpoint whose restore is not equal to a re-run is a bug
  // by definition, and §22.440 found two of those only by noticing a finding had gone missing.
  bool verifyingSetup_ = false;
  bool setupVerified_ = false;
  static bool setupVerifyOn() { static const bool on = getenv("HLIR_SETUP_VERIFY") != nullptr; return on; }
  // HLIR_NO_SETUP_CACHE: honour the markers but never capture or restore, so the region simply runs every
  // time. It is the control for "what did the CACHE buy", separately from what the markers buy -- the two are
  // different questions and §22.441 could only tell them apart by perturbing the harness.
  static bool setupCacheOff() { static const bool off = getenv("HLIR_NO_SETUP_CACHE") != nullptr; return off; }
  bool skipPrologue_ = false, capturePrologue_ = false;
  bool entryBegun_ = false;        // past `hlir.entry.begin`: setup is done, G2 promotion may apply
  std::set<std::string> promoted_;  // globals considered for promotion already (once each)
  size_t prologueBase_ = 0;

  // Record what a nondet means, by name, so the witness can say more than "nondet" (DESIGN.md §22.369). The name
  // is the one the domain uses, i.e. the op's `name` attribute.
  void noteNondet(const Op &op, const char *what) {
    const Attr *n = op.attr("name");
    if (!n || res_.nondetOrigins.count(n->s)) return;
    NondetOrigin o;
    o.function = top().fn ? top().fn->name : "";
    o.loc = op.loc;
    // An op lowered from inline assembly carries its own origin; otherwise say which model or construct made it.
    if (const Attr *og = op.attr("origin")) o.what = og->s;
    else o.what = what;
    res_.nondetOrigins.emplace(n->s, std::move(o));
  }

  // Pops frames back out of the outermost prologue function, as if it had returned. False when we are not inside
  // one -- then the caller treats the call normally.
  bool unwindPrologue(const Op &op) {
    if (!cfg_.prologueFns || cfg_.prologueFns->empty()) return false;
    size_t outer = frames_.size();
    for (size_t i = 0; i < frames_.size(); ++i)
      if (frames_[i].fn && cfg_.prologueFns->count(frames_[i].fn->name)) { outer = i; break; }
    if (outer >= frames_.size()) return false;
    event(TraceEvent::Return, top().fn->name, "initialiser reached " + op.sym, op.loc);
    const Op *callOp = frames_[outer].callOp;
    while (frames_.size() > outer) {
      for (uint32_t id : frames_.back().allocas) mem_.killId(id);
      if (isStaticInit(*frames_.back().fn)) mem_.setInStaticInit(--initDepth_ > 0);
      frames_.pop_back();
    }
    // the initialiser "returned" without a value the harness reads (HarnessGen discards it); define the register
    // anyway so nothing downstream sees it uninitialised.
    if (!frames_.empty() && callOp && callOp->result) {
      const Type *rt = callOp->result->ty;
      if (rt->isPtr()) setP(callOp->result.get(), Ptr{d_.zero(mem_.ptrWidth()), d_.zero(mem_.ptrWidth())});
      else set(callOp->result.get(), d_.constant(llvm::APInt(rt->isBool() ? 1 : rt->width(), 0)));
    }
    ++res_.prologueStops;
    return true;
  }

  // Measurement only (RunConfig::recordReads): which location this load touched. A symbolic pointer denotes no
  // single location, so it is skipped rather than guessed -- the target set is then an UNDER-estimate, which is
  // the direction that matters: using it as a mask must never silently drop a location the entry really reads.
  static constexpr size_t kMaxReadLocs = 4096, kMaxReadOffs = 256;
  void noteRead(const Ptr &p, unsigned bytes) {
    uint32_t id = 0;
    bool offKnown = false, offSym = false;
    int64_t off = 0;
    mem_.pointerEvidence(p, id, offKnown, off, offSym);
    if (!id || !offKnown || off < 0) { res_.readsIncomplete = true; return; }
    ObjEvidence oe = mem_.objEvidence(id, 0);
    // Name the location so that it means the same thing in every run (DESIGN.md §22.375). A runtime object id is
    // an allocation-order counter, unique only WITHIN one run; this result unions many runs, so two unrelated
    // objects that both happened to be id 47 would silently become one entry. Only a harness parameter object
    // keeps its id, because the driver maps exactly those back to the names the spec uses, and the harness builds
    // them in a fixed order before anything else runs.
    // A callee's own stack slot is not in the target set at all. The set answers two questions -- "what state must
    // the initialiser have established before this entry runs" and "what may be promoted instead of believed" --
    // and a local that is born and dies inside one call is neither: no prologue can set it and it holds no static
    // initial value. Measured on sound/core: they were 395 of the 456 locations @snd_pcm_oss_ioctl reported, i.e.
    // the set was 87% noise. (Reading one before it is written is a real defect, but that is uninit_read's job.)
    if (oe.kind == "stack") return;
    std::string key;
    if (oe.kind == "global" && !oe.name.empty()) key = "global:" + oe.name;
    else if (oe.kind == "param") {
      key = "obj:" + std::to_string(id);
      // Harness parameter objects are the one case where the id is worth keeping: the driver maps exactly those
      // back to the names the spec uses. Carry the stable key alongside for the nested ones it cannot name. Two
      // runs disagreeing on what id N was is possible for an object materialised lazily mid-run, and that is an
      // under-estimate of the set, so it is recorded as such rather than silently resolved.
      if (!oe.stableKey.empty()) {
        auto ins = res_.objKeys.emplace(id, oe.stableKey);
        if (!ins.second && ins.first->second != oe.stableKey) res_.readsIncomplete = true;
      }
    }
    else if (!oe.stableKey.empty()) key = "obj:" + oe.stableKey;
    else key = "obj:#" + std::to_string(id);  // no type and no site: say so rather than imply comparability
    auto it = res_.reads.find(key);
    if (it == res_.reads.end()) {
      if (res_.reads.size() >= kMaxReadLocs) { res_.readsIncomplete = true; return; }
      it = res_.reads.emplace(key, std::set<uint64_t>{}).first;
    }
    if (it->second.size() >= kMaxReadOffs) { res_.readsIncomplete = true; return; }
    for (unsigned i = 0; i < bytes && i < 16; ++i) it->second.insert(static_cast<uint64_t>(off) + i);
  }

  bool inPrologue() const {
    if (!cfg_.prologueFns || cfg_.prologueFns->empty()) return false;
    for (auto &f : frames_)
      if (f.fn && cfg_.prologueFns->count(f.fn->name)) return true;
    return false;
  }

  struct Frame {
    const Function *fn;
    const Block *blk;
    size_t ip = 0;
    std::unordered_map<const Value *, Slot> regs;
    std::vector<uint32_t> allocas;  // stack objects that die when this frame returns
    const Op *callOp = nullptr;  // call op in the caller that is waiting for this frame's result
    std::unordered_map<const Block *, unsigned> visits;  // loop bound: how often each block was entered in this call
  };

  // ---------------------------------------------------------------- non_termination step-1 prototype
  // (RunConfig::detectNonTermination, docs/DESIGN.md Sec.22.326). One loop header is watched at a time (nested
  // loops / recursion are out of scope for this prototype -- a watch on an outer loop is simply dropped, see
  // trackLoopWatch, rather than risk an incorrect nested answer).
  struct LoopWatch {
    const Block *header = nullptr;
    size_t frameDepth = 0;  // frames_.size() when this iteration's observation started; the loop's own frame
    std::set<std::pair<uint64_t, uint64_t>> writes;  // (obj, byte offset) touched since the watch (re)started
    std::set<std::pair<uint64_t, uint64_t>> deps;    // (obj, byte offset) any branch decision since then depended on
    bool unknownDep = false;   // the backward walk hit something it can't resolve (call result / block-arg /
                                // symbolic address) -- conservative bail, never report for this iteration
    bool sawNewNondet = false;  // a core.nondet was drawn since the watch (re)started -- conservative bail
    // Objects core.alloca'd since the watch (re)started: these die with whatever frame created them, which has
    // already returned by the time execution is back at the watched header (calls made during one iteration are
    // over by then) -- so they cannot carry anything across the iteration boundary and are excluded from both
    // `writes` and `deps`. Without this, the extremely common "spill a pointer parameter to a fresh local, then
    // load it right back" pattern (ubiquitous at -O0) looks like a write-then-read of the SAME address within one
    // iteration and is wrongly counted as a real dependency the iteration's own writes could have disturbed.
    std::set<uint64_t> transientObjs;
  };
  std::optional<LoopWatch> watch_;
  // The concrete (obj, offset) a core.load last read from, keyed by its result Value -- populated whenever a watch
  // is active so collectDeps() can resolve a load it walks back into without re-evaluating anything.
  std::unordered_map<const Value *, std::pair<uint64_t, uint64_t>> loadAddr_;

  // Called from jump() with the post-increment visit count of the block just entered.
  void trackLoopWatch(const Block *dest, unsigned nVisits) {
    if (!watch_) {
      if (nVisits >= 2) { watch_ = LoopWatch{}; watch_->header = dest; watch_->frameDepth = frames_.size(); }
      return;
    }
    if (frames_.size() < watch_->frameDepth) { watch_.reset(); return; }  // the loop's own frame returned
    if (dest != watch_->header || frames_.size() != watch_->frameDepth) return;  // still mid-iteration
    // Back at the watched header, same frame: one full iteration (watch start -> here) just completed.
    if (!watch_->unknownDep && !watch_->sawNewNondet) {
      bool disjoint = true;
      for (auto &w : watch_->writes)
        if (watch_->deps.count(w)) { disjoint = false; break; }
      if (disjoint && !watch_->deps.empty()) {  // an empty dep set here means the walk never ran (no branch taken
                                                 // this iteration) -- not evidence of anything, skip it
        res_.zeroProgressLoopObserved = true;
        res_.zeroProgressLoopFunction = top().fn->name;
        res_.zeroProgressLoopHeader = blockName(dest);
      }
    }
    watch_->writes.clear();
    watch_->deps.clear();
    watch_->transientObjs.clear();
    watch_->unknownDep = false;
    watch_->sawNewNondet = false;
  }

  void recordWrite(const Ptr &p, uint64_t bytes) {
    if (!watch_) return;
    auto id = d_.constValue(p.obj), off = d_.constValue(p.off);
    if (!id || !off) { watch_->unknownDep = true; return; }  // a symbolic address in a concrete run: be conservative
    uint64_t objId = id->getZExtValue();
    if (watch_->transientObjs.count(objId)) return;  // dies with this iteration's own call frame -- irrelevant, see LoopWatch::transientObjs
    uint64_t o0 = off->getZExtValue();
    for (uint64_t k = 0; k < bytes; ++k) watch_->writes.insert({objId, o0 + k});
  }

  // Backward walk from a branch condition (or anything it depends on) through the def-use chain: records the
  // concrete address of every core.load reached (and recurses into the load's own address computation too, since a
  // data-dependent address that later changes is just as much a reason the loop could diverge), terminates cleanly
  // on core.const, and conservatively bails (sets unknownDep) on anything it cannot follow -- a call result or a
  // block argument, neither handled by this prototype.
  void collectDeps(const Value *v, int fuel = 64) {
    if (!watch_ || watch_->unknownDep) return;
    if (fuel <= 0) { watch_->unknownDep = true; return; }
    if (v->kind == Value::BlockArg) { watch_->unknownDep = true; return; }
    const Op *def = v->defOp;
    if (!def) { watch_->unknownDep = true; return; }
    if (def->opc == Opc::Const) return;
    if (def->opc == Opc::Call) {
      // core.call is always direct in this IR (always @sym, no function-pointer call opcode) -- the callee's own
      // internal branches already contribute to watch_->deps independently, via the same CondBr/Switch hook firing
      // while that call executes (it runs inside this same watched iteration, whatever the call depth). What is
      // NOT otherwise covered is a plain dataflow return with no intervening branch (`return x;` straight off a
      // load, no `if`) -- so virtually inline just the return value's own dependency chain, bounded by `fuel`.
      // Known gap (documented, not silently papered over): a callee reached only through a function pointer isn't
      // expressible as core.call at all in this IR, so this case doesn't need a separate bail path for it.
      const Function *callee = mod_.findFunction(def->sym);
      if (!callee || callee->isDeclaration()) { watch_->unknownDep = true; return; }  // no body to look into -- bail
      for (auto &b : callee->blocks)
        for (auto &op : b->ops)
          if (op->opc == Opc::Return && !op->operands.empty()) collectDeps(op->operands[0], fuel - 1);
      return;
    }
    if (def->opc == Opc::Load) {
      auto it = loadAddr_.find(v);
      if (it == loadAddr_.end()) { watch_->unknownDep = true; return; }
      if (!watch_->transientObjs.count(it->second.first)) watch_->deps.insert(it->second);  // see LoopWatch::transientObjs
      if (!def->operands.empty()) collectDeps(def->operands[0], fuel - 1);
      return;
    }
    for (auto *operand : def->operands) collectDeps(operand, fuel - 1);
  }

  // ---------------------------------------------------------------- globals still holding their initial value
  // A branch whose condition reads a global the program has not written is decided by that global's INITIAL value
  // -- the static initialiser's, or zero. `module_init` and every other internal function that would have set it is
  // not executed (DESIGN.md §22.362), so the decision is an assumption about the module never having run, and it is
  // one-sided: `Machine` takes the concrete edge with no fork, so the other side of the branch is not explored
  // either. That makes one such global able to produce a false finding and a silent coverage loss at the same time.
  //
  // This is a MEASUREMENT: it changes no decision. The walk is syntactic over the def-use chain and bails (answering
  // "no") on block arguments, call results and anything else it cannot follow, so it UNDER-counts on purpose -- the
  // number it reports is a lower bound on how much of the report rests on this assumption.
  const std::string *pristineGlobalIn(const Value *v, int fuel = 32) {
    if (fuel <= 0 || !v || v->kind == Value::BlockArg) return nullptr;
    const Op *def = v->defOp;
    if (!def || def->opc == Opc::Const || def->opc == Opc::Call) return nullptr;
    if (def->opc == Opc::GlobalAddr) return mem_.globalIsPristine(def->sym) ? &def->sym : nullptr;
    for (auto *a : def->operands)
      if (const std::string *g = pristineGlobalIn(a, fuel - 1)) return g;
    return nullptr;
  }
  void noteGlobalGated(const Op &op, const Value *cond) {
    if (initDepth_) return;  // a branch inside the static initialiser itself decides nothing about the program
    const std::string *g = pristineGlobalIn(cond);
    if (!g) return;
    // G2 already replaced this global's value with an unconstrained one, so the branch is NOT being decided by
    // the static initialiser any more -- naming it under `global_initial_value` as well would report a narrowing
    // that was just removed (DESIGN.md §22.374).
    if (promoted_.count(*g) && cfg_.promoteGlobals && cfg_.promoteGlobals->count(*g)) return;
    res_.globalGatedSites.insert(&op);
    res_.globalGatedBy.emplace(*g, op.loc);
  }

  // ---------------------------------------------------------------- helpers
  Frame &top() { return frames_.back(); }
  const Val &get(const Value *v) { return top().regs.at(v).a; }
  void set(const Value *v, Val x) { top().regs.insert_or_assign(v, Slot{std::move(x), Val{}}); }
  Ptr getP(const Value *v) { const Slot &s = top().regs.at(v); return {s.a, s.b}; }
  std::map<const Function *, std::vector<Loop>> loopCache_;  // loopsOf(fn), computed once per function
  // The INNERMOST natural loop whose body contains `blk` -- the loop this branch belongs to -- or nullptr. (Not a
  // lookup by header: the warning fires at the loop's own condition branch, whose already-visited successor is the
  // body, not the header.) Innermost = smallest body, so a bound defined in an outer loop but inside this one is
  // still correctly variant. Computed once per function and cached; only touched on the rare warning path.
  const Loop *loopContaining(const Function *fn, const Block *blk) {
    if (!fn || !blk) return nullptr;
    auto it = loopCache_.find(fn);
    if (it == loopCache_.end()) it = loopCache_.emplace(fn, loopsOf(*fn)).first;
    const Loop *best = nullptr;
    for (const Loop &L : it->second)
      if (L.body.count(blk) && (!best || L.body.size() < best->body.size())) best = &L;
    return best;
  }
  // The root object of a pointer: follow PtrAdd/PtrDiff back to the Alloca/GlobalAddr/HeapAlloc (or whatever the
  // chain bottoms out at). Used to decide store-aliasing by base identity.
  static const Value *baseOf(const Value *addr) {
    while (addr && addr->defOp && (addr->defOp->opc == Opc::PtrAdd || addr->defOp->opc == Opc::PtrDiff) &&
           !addr->defOp->operands.empty())
      addr = addr->defOp->operands[0];
    return addr;
  }
  // The base objects any Store in the loop body writes to. A Load whose base is in here may change between
  // iterations even if its address is loop-invariant (`while (n-- > 0)` reloads n from a slot it also writes), so
  // it is NOT loop-invariant. Cached per loop header.
  std::map<const Block *, std::set<const Value *>> storedBaseCache_;
  const std::set<const Value *> &storedBasesOf(const Loop *L) {
    auto it = storedBaseCache_.find(L->header);
    if (it != storedBaseCache_.end()) return it->second;
    std::set<const Value *> s;
    for (const Block *b : L->body)
      for (const auto &op : b->ops)
        if (op->opc == Opc::Store && op->operands.size() >= 2) s.insert(baseOf(op->operands[1]));
    return storedBaseCache_.emplace(L->header, std::move(s)).first->second;
  }
  // Is value `v` loop-invariant: the same on every iteration of this loop? Constants, allocas and addresses are;
  // a pure computation is iff its operands are; a Load is iff its address is invariant AND its base is never
  // stored in the loop; a loop-header block argument (the induction/phi) and anything we do not recognise are NOT
  // (conservative -- an unproven value is treated as varying so the DoS warning is kept).
  bool loopInvariant(const Value *v, const std::set<const Block *> &body, const std::set<const Value *> &stored,
                     int depth) {
    if (!v || depth > 24) return false;
    const Op *d = v->defOp;
    if (!d) return v->defBlock && !body.count(v->defBlock);  // block arg: invariant iff defined outside the loop
    switch (d->opc) {
      case Opc::Const: case Opc::Alloca: case Opc::HeapAlloc: case Opc::GlobalAddr: case Opc::FuncAddr:
        return true;
      case Opc::Load:
        return !d->operands.empty() && loopInvariant(d->operands[0], body, stored, depth + 1) &&
               !stored.count(baseOf(d->operands[0]));
      case Opc::Add: case Opc::Sub: case Opc::Mul: case Opc::UDiv: case Opc::SDiv: case Opc::URem:
      case Opc::SRem: case Opc::And: case Opc::Or: case Opc::Xor: case Opc::Not: case Opc::Neg:
      case Opc::Shl: case Opc::LShr: case Opc::AShr: case Opc::ZExt: case Opc::SExt: case Opc::Trunc:
      case Opc::Extract: case Opc::Concat: case Opc::ICmp: case Opc::Select: case Opc::B2I: case Opc::I2B:
      case Opc::PtrAdd: case Opc::PtrDiff:
        for (const Value *opnd : d->operands)
          if (!loopInvariant(opnd, body, stored, depth + 1)) return false;
        return true;
      default:
        return false;  // Call, and anything with a side effect or we do not model: assume it may vary
    }
  }
  // kTaint: classify the scalar operands feeding a loop-governing branch condition for taintLoopWarn's
  // dominating-cap check. Descend one or two levels through boolean And/Or/Select/Not, then take the operands of
  // each comparison. An operand defined INSIDE the loop body is loop-VARIANT: it is re-read every iteration
  // (`buf[i]` in a `while (buf[i])` scan), so a cap on its value does NOT bound the trip count -- if any such
  // operand is attacker-controlled we cannot prove the loop bounded and set `variantTaint`. An operand defined
  // OUTSIDE the body is loop-invariant (the `n` of `i < n`): a dominating cap on it DOES bound the loop, so it
  // goes to `invBounds` for thresholding. Only values already materialised in this frame are taken.
  void gatherLoopBounds(const Value *v, const Loop *L, const std::set<const Value *> *stored,
                        std::vector<std::pair<Val, bool>> &invBounds, bool &variantTaint, int depth) {
    if (!v || depth > 2) return;
    const Op *d = v->defOp;
    if (!d) return;
    if (d->opc == Opc::ICmp) {
      // The comparison's signedness decides how the bound is thresholded: a signed `i < n` means a negative n
      // runs zero iterations, so it must be sign-extended and compared signed, or a negative attacker value
      // looks huge when zero-extended and the warning never gets suppressed.
      bool sgn = !d->pred.empty() && d->pred[0] == 's';
      for (const Value *opnd : d->operands) {
        if (!top().regs.count(opnd)) continue;
        const Val &ov = get(opnd);
        if (!d_.isAttackerControlled(ov)) continue;
        // Provably loop-INVARIANT (same value every iteration) => a cap on it bounds the trip count, so threshold
        // it. Otherwise (varies, or the loop was not identified) we cannot bound the loop from this operand: keep
        // the warning. Suppression needs positive proof, never a missing fact.
        bool invariant = L && stored && loopInvariant(opnd, L->body, *stored, 0);
        if (invariant) invBounds.push_back({ov, sgn});
        else variantTaint = true;
      }
    } else if (d->opc == Opc::And || d->opc == Opc::Or || d->opc == Opc::Select || d->opc == Opc::Not) {
      for (const Value *opnd : d->operands) gatherLoopBounds(opnd, L, stored, invBounds, variantTaint, depth + 1);
    }
  }
  void setP(const Value *v, Ptr p) { top().regs.insert_or_assign(v, Slot{std::move(p.obj), std::move(p.off)}); }
  const Slot &getSlot(const Value *v) { return top().regs.at(v); }
  void setSlot(const Value *v, Slot s) { top().regs.insert_or_assign(v, std::move(s)); }
  unsigned accessBytes(const Type *t) const { return t->isBool() ? 1 : t->isPtr() ? mem_.ptrWidth() / 8 : (t->width() + 7) / 8; }
  bool checkMemFailed(const Op &op) {
    if (!mem_.failed()) return false;
    unsupported(op, mem_.error());
    return true;
  }
  // Bounds-checks a declarative ModelDB effect (source:/copy:/fill: in execModel) against `p`'s backing object,
  // for a dynamic access width `n` that a hand-written core.func body would instead prove via two constant-width
  // core.check.oob instructions (see models/libc.core's @memcpy). Honours --ub (Report/Assume/Ignore) the same way
  // the Opc::CheckOob dispatch does. Returns true if execution should stop here (UB reported, or an Assume made the
  // call infeasible) -- the caller must `return` immediately in that case, exactly like the existing
  // `if (checkMemFailed(op)) return;` calls right after it in execModel.
  bool checkDeclOob(const Op &op, const Ptr &p, Val n, UBKind kind) {
    CheckMode mode = modeFor(op);
    if (mode == CheckMode::Ignore) return false;
    Val cond = mem_.oobCond(p, n);
    if (checkMemFailed(op)) return true;
    if (mode == CheckMode::Assume) {
      if (!d_.assume(d_.not_(cond))) { stop(RunStatus::Infeasible, std::string("assumed absent: ") + ubKindName(kind), &op); return true; }
      return false;
    }
    if (d_.violated(cond, [&] { return ubFinding(kind, op); })) { reportUB(kind, op); return true; }
    return false;
  }
  // ---------------------------------------------------------------- external functions: ModelDB (hlir/model/Model.h)
  Ptr modelPtr(const Op &op, unsigned k, bool &ok) {
    if (k >= op.operands.size() || !op.operands[k]->ty->isPtr()) {
      unsupported(op, "model refers to argument " + std::to_string(k) + ", which is not a pointer argument of the call");
      ok = false;
      return {};
    }
    return getP(op.operands[k]);
  }
  Val toWidth(Val v, unsigned w, bool isSigned) {
    unsigned cw = d_.width(v);
    if (cw == w) return v;
    if (cw > w) return d_.trunc(v, w);
    return isSigned ? d_.sext(v, w) : d_.zext(v, w);
  }
  // Size operand -> value of pointer width. `ret` is the call's (integer) result; negative results count as 0.
  Val modelSize(const model::Size &z, const Op &op, const Slot *ret, bool &ok) {
    unsigned pw = mem_.ptrWidth();
    switch (z.kind) {
      case model::Size::Const: return d_.constant(llvm::APInt(pw, z.value));
      case model::Size::Arg:
        if (z.index >= op.operands.size() || op.operands[z.index]->ty->isPtr()) { unsupported(op, "size refers to a non-integer argument"); ok = false; return d_.zero(pw); }
        return toWidth(get(op.operands[z.index]), pw, false);
      case model::Size::Ret: {
        if (!ret) { unsupported(op, "size: ret of a function without a result"); ok = false; return d_.zero(pw); }
        Val r = ret->a;
        return d_.select(d_.icmp(Pred::Sge, r, d_.zero(d_.width(r))), toWidth(r, pw, true), d_.zero(pw));
      }
      case model::Size::Strlen: case model::Size::StrlenPlus1: {
        Ptr p = modelPtr(op, z.index, ok);
        if (!ok) return d_.zero(pw);
        Val n = mem_.cstrlen(p);
        return z.kind == model::Size::StrlenPlus1 ? d_.add(n, d_.constant(llvm::APInt(pw, 1))) : n;
      }
      case model::Size::None: break;
    }
    unsupported(op, "model has no size");
    ok = false;
    return d_.zero(pw);
  }

  void execModel(const Op &op, const Function &callee, const model::CallModel &m) {
    if (m.noreturn) { terminate(op, callee.name); return; }
    const auto &o = op.operands;
    const unsigned inst = modelCalls_[callee.name]++;
    const std::string base = "in." + callee.name + "#" + std::to_string(inst);
    const Type *rt = callee.retTy;
    bool ok = true;
    d_.onCall(callee);
    event(TraceEvent::Call, callee.name, "model, from @" + top().fn->name, op.loc);

    // ---- result
    std::optional<Slot> ret;
    // The object `returns.alloc` made, BEFORE `may_fail` turned the result into a select of NULL and it.
    // `points_to` writes into this one: on the failure branch the caller gets NULL and never reads the field,
    // so storing through the select would be a write to object 0 on a path that does not exist.
    std::optional<Ptr> retAlloc;
    if (!rt->isVoid()) {
      unsigned w = rt->isBool() ? 1 : rt->isPtr() ? mem_.ptrWidth() : rt->width();
      Slot r;
      switch (m.ret.kind) {
        case model::ReturnSpec::Opaque:
          if (rt->isPtr()) {  // unknown pointer result: NULL or a zeroed 4096-byte object
            Ptr p = mem_.alloc(ObjKind::Heap, d_.constant(llvm::APInt(mem_.ptrWidth(), 4096)), 16, false, true);
            p.obj = d_.select(d_.modelInput(env_, base + ".fail", 1, ""), mem_.nullPtr().obj, p.obj);
            r.a = p.obj;
            r.b = p.off;
          } else r.a = d_.modelInput(env_, base + ".ret", w, "");
          break;
        case model::ReturnSpec::Unspecified:
          if (rt->isPtr()) { unsupported(op, "model of pointer-returning @" + callee.name + " needs a 'returns' entry"); return; }
          r.a = d_.modelInput(env_, base + ".ret", w, "");
          break;
        case model::ReturnSpec::Nondet: {
          if (rt->isPtr()) { unsupported(op, "returns.nondet needs an integer result"); return; }
          std::optional<llvm::APInt> dflt;
          if (m.ret.dflt) {
            if (m.ret.dflt->kind == model::Ref::Const) dflt = llvm::APInt(w, static_cast<uint64_t>(m.ret.dflt->value), true);
            else if (m.ret.dflt->index < o.size() && !o[m.ret.dflt->index]->ty->isPtr())
              if (auto cv = d_.constValue(toWidth(get(o[m.ret.dflt->index]), w, true))) dflt = *cv;
          }
          r.a = d_.modelInput(env_, base + ".ret", w, m.ret.taintLabel, dflt);
          auto bound = [&](const std::optional<model::Ref> &b, Pred p) {
            if (!b || !ok) return;
            Val bv;
            if (b->kind == model::Ref::Const) bv = d_.constant(llvm::APInt(w, static_cast<uint64_t>(b->value), true));
            else if (b->index < o.size() && !o[b->index]->ty->isPtr()) bv = toWidth(get(o[b->index]), w, true);
            else { unsupported(op, "returns.nondet bound refers to a non-integer argument"); ok = false; return; }
            if (!d_.assume(d_.icmp(p, r.a, bv))) { stop(RunStatus::Infeasible, "model result bound is infeasible", &op); ok = false; }
          };
          bound(m.ret.min, Pred::Sge);
          bound(m.ret.max, Pred::Sle);
          if (!ok) return;
          break;
        }
        case model::ReturnSpec::Const:
          if (rt->isPtr()) { unsupported(op, "returns.value needs an integer result"); return; }
          r.a = d_.constant(llvm::APInt(w, static_cast<uint64_t>(m.ret.value), true));
          break;
        case model::ReturnSpec::Arg:
          if (m.ret.arg >= o.size()) { unsupported(op, "returns.arg is out of range"); return; }
          r = getSlot(o[m.ret.arg]);
          break;
        case model::ReturnSpec::Strlen: {
          if (rt->isPtr()) { unsupported(op, "returns.strlen needs an integer result"); return; }
          Ptr sp = modelPtr(op, m.ret.arg, ok);
          if (!ok) return;
          r.a = toWidth(mem_.cstrlen(sp), w, false);
          if (checkMemFailed(op)) return;
          break;
        }
        case model::ReturnSpec::Null: {
          if (!rt->isPtr()) { unsupported(op, "returns.null needs a pointer result"); return; }
          Ptr np = mem_.nullPtr();
          r.a = np.obj;
          r.b = np.off;
          break;
        }
        case model::ReturnSpec::Alloc: {
          if (!rt->isPtr()) { unsupported(op, "returns.alloc needs a pointer result"); return; }
          Val size = modelSize(m.ret.allocSize, op, nullptr, ok);
          if (!ok) return;
          Ptr p = mem_.alloc(ObjKind::Heap, size, 16, false, m.ret.zeroed);
          retAlloc = p;
          if (m.ret.mayFail) p.obj = d_.select(d_.modelInput(env_, base + ".fail", 1, ""), mem_.nullPtr().obj, p.obj);
          r.a = p.obj;
          r.b = p.off;
          break;
        }
      }
      ret = r;
    }
    const Slot *retp = ret ? &*ret : nullptr;

    // ---- memory effects: attacker-controlled input, copies, fills
    unsigned si = 0;
    for (auto &s : m.sources) {
      Ptr p;
      if (s.ptr.kind == model::Ref::Ret) {
        if (!ret || !rt->isPtr()) { unsupported(op, "source.ptr: ret needs a pointer result"); return; }
        p = Ptr{ret->a, ret->b};
      } else {
        p = modelPtr(op, s.ptr.index, ok);
      }
      Val n = ok ? modelSize(s.size, op, retp, ok) : Val{};
      if (!ok) return;
      std::string label = s.label, prefix = base + ".s" + std::to_string(si++) + "+";
      if (checkDeclOob(op, p, n, UBKind::OobWrite)) return;
      mem_.fillWith(p, n, [&](uint64_t i) { return d_.modelInput(env_, prefix + std::to_string(i), 8, label); });
      if (checkMemFailed(op)) return;
    }
    // Bytes the real callee wrote and we cannot name (DESIGN.md §22.377). Symbolic, so nothing downstream is
    // decided concretely by a value we invented, and labelled as the HARNESS's own rather than the attacker's, so
    // a finding that rests only on them is reported as the analysis's invention and not as a defect.
    unsigned ui = 0;
    for (auto &u : m.fillsUnknown) {
      Ptr p;
      if (u.ptr.kind == model::Ref::Ret) {
        if (!ret || !rt->isPtr()) { unsupported(op, "fills_unknown.ptr: ret needs a pointer result"); return; }
        p = Ptr{ret->a, ret->b};
      } else {
        p = modelPtr(op, u.ptr.index, ok);
      }
      Val n = ok ? modelSize(u.size, op, retp, ok) : Val{};
      if (!ok) return;
      std::string prefix = base + ".u" + std::to_string(ui++) + "+";
      if (checkDeclOob(op, p, n, UBKind::OobWrite)) return;
      mem_.fillWith(p, n, [&](uint64_t i) { return d_.harnessInput(env_, prefix + std::to_string(i), 8); });
      if (checkMemFailed(op)) return;
      ++res_.unknownWrites[op.sym];
    }
    // The pointer FIELDS of what the callee handed back (DESIGN.md §22.475). `source` and `fills_unknown` say
    // what is in a buffer we already hold; this one says that a word inside it is a pointer and builds what it
    // points at. The size is stated by the model, not invented like the synthesis frontier's, which is the only
    // reason a bounds verdict about the pointee means anything (see PointsToSpec).
    unsigned pi = 0;
    for (auto &pt : m.pointsTo) {
      Ptr holder;
      if (pt.base.kind == model::Ref::Ret) {
        if (!retAlloc) { unsupported(op, "points_to.base: ret needs returns.alloc"); return; }
        holder = *retAlloc;
      } else {
        holder = modelPtr(op, pt.base.index, ok);
        if (!ok) return;
      }
      Val n = modelSize(pt.size, op, retp, ok);
      if (!ok) return;
      Ptr pointee = mem_.alloc(ObjKind::Heap, n, 16, false, pt.zeroed);
      if (!pt.zeroed) {
        std::string prefix = base + ".p" + std::to_string(pi) + "+";
        if (pt.unknown)
          mem_.fillWith(pointee, n, [&](uint64_t i) { return d_.harnessInput(env_, prefix + std::to_string(i), 8); });
        else
          mem_.fillWith(pointee, n, [&](uint64_t i) { return d_.modelInput(env_, prefix + std::to_string(i), 8, pt.label); });
        if (checkMemFailed(op)) return;
      }
      ++pi;
      const unsigned pw = mem_.ptrWidth();
      Ptr field{holder.obj, d_.add(holder.off, d_.constant(llvm::APInt(pw, pt.offset)))};
      if (checkDeclOob(op, field, d_.constant(llvm::APInt(pw, pw / 8)), UBKind::OobWrite)) return;
      mem_.storePtr(field, pointee);
      if (checkMemFailed(op)) return;
    }
    for (auto &c : m.copies) {
      Ptr dst = modelPtr(op, c.dst.index, ok), src = modelPtr(op, c.src.index, ok);
      Val n = ok ? modelSize(c.size, op, retp, ok) : Val{};
      if (!ok) return;
      if (checkDeclOob(op, dst, n, UBKind::OobWrite)) return;
      if (checkDeclOob(op, src, n, UBKind::OobRead)) return;
      mem_.copy(dst, src, n);
      if (checkMemFailed(op)) return;
    }
    for (auto &f : m.fills) {
      Ptr p = modelPtr(op, f.ptr.index, ok);
      Val n = ok ? modelSize(f.size, op, retp, ok) : Val{};
      if (!ok) return;
      Val byte;
      if (f.value.kind == model::Ref::Const) byte = d_.constant(llvm::APInt(8, static_cast<uint64_t>(f.value.value)));
      else if (f.value.kind == model::Ref::Arg && f.value.index < o.size() && !o[f.value.index]->ty->isPtr()) byte = toWidth(get(o[f.value.index]), 8, false);
      else { unsupported(op, "fill.value must be an integer or an integer argument"); return; }
      if (checkDeclOob(op, p, n, UBKind::OobWrite)) return;
      mem_.set(p, byte, n);
      if (checkMemFailed(op)) return;
    }

    // ---- taint flow and sinks (only the taint domain tracks them; other domains skip this)
    if constexpr (D::kTaint) {
      unsigned fi = 0;
      auto pointee = [&](const model::Ref &r, Ptr &p) {  // resolves argK_pointee / ret_pointee
        if (r.kind == model::Ref::ArgPointee) { p = modelPtr(op, r.index, ok); return ok; }
        if (r.kind == model::Ref::RetPointee && ret && rt->isPtr()) { p = Ptr{ret->a, ret->b}; return true; }
        return false;
      };
      for (auto &f : m.flows) {
        std::string tag = base + ".f" + std::to_string(fi++);
        if (f.to.kind == model::Ref::Ret) tag = base + ".ret";  // the derived result *is* the call's result input: models replay
        Val n = d_.zero(mem_.ptrWidth());
        bool needsSize = f.from.kind == model::Ref::ArgPointee || f.to.kind == model::Ref::ArgPointee || f.to.kind == model::Ref::RetPointee;
        if (needsSize) { n = modelSize(f.size, op, retp, ok); if (!ok) return; }
        if (f.clear) {
          if (f.to.kind == model::Ref::Ret && ret && !rt->isPtr()) ret->a = d_.clearTaint(ret->a);
          else {
            Ptr p;
            if (!pointee(f.to, p)) { if (!ok) return; continue; }
            if (!mem_.mapBytes(p, n, [&](Val b, uint64_t) { return d_.clearTaint(b); })) { checkMemFailed(op); return; }
          }
          continue;
        }
        std::vector<Val> froms;
        if (f.from.kind == model::Ref::Arg) {
          if (f.from.index >= o.size()) { unsupported(op, "flow.from refers to a missing argument"); return; }
          froms.push_back(get(o[f.from.index]));
          if (o[f.from.index]->ty->isPtr()) froms.push_back(getSlot(o[f.from.index]).b);
        } else if (f.from.kind == model::Ref::ArgPointee) {
          Ptr p = modelPtr(op, f.from.index, ok);
          if (!ok || !mem_.readBytes(p, n, froms)) { checkMemFailed(op); return; }
        } else { unsupported(op, "flow.from must be argK or argK_pointee"); return; }
        if (f.to.kind == model::Ref::Ret && ret) {
          if (rt->isPtr()) { unsupported(op, "flow to a pointer result is not supported"); return; }
          ret->a = d_.opaqueDerived(ret->a, froms, tag);
        } else {
          Ptr p;
          if (!pointee(f.to, p)) { if (!ok) return; unsupported(op, "flow.to must be ret, argK_pointee or ret_pointee"); return; }
          if (!mem_.mapBytes(p, n, [&](Val b, uint64_t k) { return d_.opaqueDerived(b, froms, tag + "+" + std::to_string(k)); })) { checkMemFailed(op); return; }
        }
      }
    }
    for (auto &s : m.sinks) {
      event(TraceEvent::Observable, top().fn->name, "sink " + s.kind + " " + callee.name, op.loc);
      if constexpr (D::kTaint) {
        std::vector<Val> vals;
        if (s.arg.kind == model::Ref::Arg && s.arg.index < o.size()) vals.push_back(get(o[s.arg.index]));
        else if (s.arg.kind == model::Ref::ArgPointee) {
          Ptr p = modelPtr(op, s.arg.index, ok);
          if (!ok || !mem_.cstringBytes(p, vals)) { checkMemFailed(op); return; }
        }
        for (auto &v : vals)
          if (d_.isAttackerControlled(v)) {
            res_.taintReach.sink = true;
            d_.taintSink(v, [&] {
              Finding fd = ubFinding(UBKind::TaintedSink, op);
              fd.ub->origin = "sink:" + s.kind;
              fd.ub->op = "core.call @" + callee.name;
              return fd;
            });
            break;
          }
      }
    }

    d_.onReturn(callee, ret ? &ret->a : nullptr);
    if (ret && op.result) setSlot(op.result.get(), *ret);
  }

  // A call into a compromised component (ModelProvider::untrusted): the result and everything it can write through its pointer arguments
  // is attacker-controlled.
  void execUntrusted(const Op &op, const Function &callee, const std::string &label, unsigned outMax) {
    const auto &o = op.operands;
    const unsigned inst = modelCalls_[callee.name]++;
    const std::string base = "in." + callee.name + "#" + std::to_string(inst);
    const Type *rt = callee.retTy;
    d_.onCall(callee);
    event(TraceEvent::Call, callee.name, "untrusted API, from @" + top().fn->name, op.loc);
    const unsigned pw = mem_.ptrWidth();
    std::optional<Slot> ret;
    if (!rt->isVoid()) {
      Slot r;
      if (rt->isPtr()) {
        Val size = d_.constant(llvm::APInt(pw, outMax));
        Ptr p = mem_.alloc(ObjKind::Heap, size, 16, false, false);
        mem_.fillWith(p, size, [&](uint64_t i) { return d_.modelInput(env_, base + ".r+" + std::to_string(i), 8, label); });
        if (checkMemFailed(op)) return;
        p.obj = d_.select(d_.modelInput(env_, base + ".fail", 1, label), mem_.nullPtr().obj, p.obj);
        r.a = p.obj;
        r.b = p.off;
      } else {
        unsigned w = rt->isBool() ? 1 : rt->width();
        r.a = d_.modelInput(env_, base + ".ret", w, label);
      }
      ret = r;
    }
    for (size_t i = 0; i < o.size(); ++i) {  // out-parameters: a hostile callee may write through any pointer it is given
      if (!o[i]->ty->isPtr()) continue;
      Ptr p = getP(o[i]);
      auto id = d_.constValue(p.obj);
      if (!id || id->isZero()) continue;
      auto sz = d_.constValue(mem_.sizeOf(p)), off = d_.constValue(p.off), cst = d_.constValue(mem_.isConstObj(p));
      if (!sz || !off || (cst && !cst->isZero())) continue;
      uint64_t S = sz->getZExtValue(), O = off->getZExtValue();
      if (O >= S || S - O > outMax) continue;
      uint64_t n = S - O;
      std::string pre = base + ".a" + std::to_string(i) + "+";
      mem_.fillWith(p, d_.constant(llvm::APInt(pw, n)), [&](uint64_t k) { return d_.modelInput(env_, pre + std::to_string(k), 8, label); });
      if (checkMemFailed(op)) return;
    }
    d_.onReturn(callee, ret ? &ret->a : nullptr);
    if (ret && op.result) setSlot(op.result.get(), *ret);
  }

  bool isBoolVal(const Value *v) const { return v->ty->isBool(); }

  void event(TraceEvent::Kind k, const std::string &fn, const std::string &text, const Loc &loc) {
    if (cfg_.trace) res_.trace.push_back({k, fn, text, loc});
  }

  // The program ends at `op` (a noreturn call or abort/exit/trap): not a bug, not a real execution to analyse further.
  void terminate(const Op &op, const std::string &by) {
    res_.terminated = true;
    res_.terminatedIn = top().fn->name;
    res_.terminatedBy = by;
    res_.terminatedAt = op.loc;
    for (size_t i = frames_.size(); i-- > 1 && res_.terminatedStack.size() < 400;) {  // callers: the call op of each frame sits in the frame below it
      const Op *co = frames_[i].callOp;
      if (!co) break;
      if (!res_.terminatedStack.empty()) res_.terminatedStack += " <- ";
      res_.terminatedStack += frames_[i - 1].fn->name + (co->loc.valid() ? " (" + co->loc.file.substr(co->loc.file.find_last_of('/') + 1) + ":" + std::to_string(co->loc.line) + ")" : "");
      if (std::count(res_.terminatedStack.begin(), res_.terminatedStack.end(), '<') >= 3) break;
    }
    stop(RunStatus::Infeasible, "the program ends here (" + by + ")", &op);
  }
  void stop(RunStatus s, std::string msg = "", const Op *at = nullptr) {
    res_.status = s;
    res_.message = std::move(msg);
    if (at) res_.messageLoc = at->loc;
    done_ = true;
  }
  void unsupported(const Op &op, const std::string &why) {
    stop(RunStatus::Unsupported, "core." + std::string(opInfo(op.opc).name) + ": " + why, &op);
  }

  std::string blockName(const Block *b) const { return b->name.empty() ? "?" : b->name; }

  std::string describe(const Value *v) {
    const Slot &s = getSlot(v);
    if (v->ty->isPtr()) return "ptr(obj=" + d_.str(s.a) + ", off=" + d_.str(s.b) + ")";
    return d_.str(s.a, v->ty->isBool());
  }

  UBReport makeUBReport(UBKind k, const Op &op) {
    UBReport r;
    r.kind = k;
    r.loc = op.loc;
    // A model body has no source location. Attribute the finding to the nearest enclosing call site that does,
    // and say so (UBReport::locFromFrame).
    if (!r.loc.valid()) {
      for (auto it = frames_.rbegin(); it != frames_.rend(); ++it) {
        if (it->callOp && it->callOp->loc.valid()) {
          r.loc = it->callOp->loc;
          r.locFromFrame = it->fn ? it->fn->name : std::string();
          break;
        }
      }
    }
    r.function = top().fn->name;
    r.block = blockName(top().blk);
    r.op = "core." + std::string(opInfo(op.opc).name);
    if (const Attr *o = op.attr("origin")) r.origin = o->s;
    r.step = res_.steps;
    for (auto &fr : frames_) r.callStack.push_back(fr.fn->name);
    std::string det;
    for (size_t i = 0; i < op.operands.size(); ++i) det += (i ? ", " : "operands: ") + describe(op.operands[i]);
    r.detail = det;
    collectEvidence(r, op);
    return r;
  }

  // What object was hit, where, and what state the run was in (DESIGN.md §22.369). Gathered here, at the check,
  // because this is the only place the memory still holds it: by the time the report is written the run is gone.
  // Every check op this fires on takes the offending pointer as its first operand.
  void collectEvidence(UBReport &r, const Op &op) {
    if (getenv("HLIR_DEBUG_EVIDENCE"))
      fprintf(stderr, "[ev] op=%s nops=%zu op0ptr=%d\n", opInfo(op.opc).name, op.operands.size(),
              op.operands.empty() ? -1 : (int)op.operands[0]->ty->isPtr());
    if (!op.operands.empty() && op.operands[0]->ty->isPtr()) {
      Ptr p = getP(op.operands[0]);
      uint32_t id = 0;
      bool offKnown = false, offSym = false;
      int64_t off = 0;
      mem_.pointerEvidence(p, id, offKnown, off, offSym);
      if (getenv("HLIR_DEBUG_EVIDENCE"))
        fprintf(stderr, "[ev]   id=%u offKnown=%d off=%lld offSym=%d globals=%zu\n", id, (int)offKnown,
                (long long)off, (int)offSym, mem_.globalEvidence().size());
      // `core.check.ptr_arith %p, %delta` reports where the arithmetic LANDS, which is the number a reader needs;
      // the other checks are about `%p` itself.
      if (op.opc == Opc::CheckPtrArith && op.operands.size() > 1 && !op.operands[1]->ty->isPtr()) {
        if (auto d = D::peekVal(get(op.operands[1]))) {
          if (D::isSymbolicVal(get(op.operands[1]))) offSym = true;
          else if (offKnown && d->getBitWidth() <= 64) off += d->getSExtValue();
        }
      }
      r.access.valid = id != 0 || offKnown;
      r.access.obj = id;
      r.access.offsetKnown = offKnown && !offSym;
      r.access.offset = off;
      r.access.offsetSymbolic = offSym;
      if (const Attr *w = op.attr("w")) r.access.width = static_cast<unsigned>(w->i);
      if (const Attr *a = op.attr("access")) r.access.access = a->s;
      if (id) {
        ObjEvidence oe = mem_.objEvidence(id);
        r.access.objName = oe.name;
        r.access.objSizeKnown = oe.sizeKnown;
        r.access.objSize = oe.size;
        r.objects.push_back(std::move(oe));
      }
    }
    // ... and every global the run touched, so a reader can tell which of them the path depended on and which of
    // those still hold their static initialiser (the `global_initial_value` narrowing, §22.362) rather than
    // something the module's own initialiser set.
    for (auto &g : mem_.globalEvidence()) {
      bool dup = false;
      for (auto &o : r.objects) dup |= o.id == g.id;
      if (!dup) r.objects.push_back(std::move(g));
    }
  }

  // See the call site in Opc::Load. Applies at most once per (field, object): the cells cache returns the same
  // value afterwards, so repeating the assumption would only add redundant path constraints.
  void applyFrontierBound(const Op &op, const Ptr &p, const Type *t) {
    unsigned w = t->isBool() ? 1 : t->width();
    if (!w || w > 64) return;
    std::string key = mem_.frontierFieldKey(p);
    if (key.empty()) return;
    ++res_.frontierFieldReads;
    auto it = cfg_.fieldBounds->find(key);
    if (it == cfg_.fieldBounds->end()) { ++res_.frontierBoundsMissing; return; }
    const FieldBound &b = it->second;
    if (b.bits != w || (!b.hasLo && !b.hasHi)) { ++res_.frontierBoundsMissing; return; }  // a different member starts at this offset: not this read
    uint32_t id = mem_.objIdOf(p);
    if (!id || !boundedFields_.insert(key + "/" + std::to_string(id)).second) return;
    ++res_.frontierBoundsApplied;
    Val v = get(op.result.get());
    auto ok = [&](Val c) {
      if (d_.assume(c)) return true;
      ++res_.frontierBoundsInfeasible;
      stop(RunStatus::Infeasible, "a bound the program asserts about " + key + " cannot hold here", &op);
      return false;
    };
    if (b.hasLo && !ok(d_.icmp(b.isSigned ? Pred::Sge : Pred::Uge, v, d_.constant(llvm::APInt(w, static_cast<uint64_t>(b.lo), true))))) return;
    if (b.hasHi) ok(d_.icmp(b.isSigned ? Pred::Sle : Pred::Ule, v, d_.constant(llvm::APInt(w, static_cast<uint64_t>(b.hi), true))));
  }

  Finding ubFinding(UBKind k, const Op &op) {
    Finding f;
    f.status = RunStatus::UB;
    f.ub = makeUBReport(k, op);
    f.loc = op.loc;
    f.site = &op;
    return f;
  }

  void reportUB(UBKind k, const Op &op) {
    res_.ub = makeUBReport(k, op);
    event(TraceEvent::UBEvent, top().fn->name, std::string(ubKindName(k)), op.loc);
    stop(RunStatus::UB);
  }

  void pushFrame(const Function &f, std::vector<Slot> args, const Op *callOp) {
    Frame fr;
    fr.fn = &f;
    fr.blk = f.entry();
    if (cfg_.coverage) cov_.insert(fr.blk);
    fr.callOp = callOp;
    for (size_t i = 0; i < args.size(); ++i) fr.regs.insert_or_assign(f.entry()->args[i].get(), std::move(args[i]));
    frames_.push_back(std::move(fr));
    if (isStaticInit(f)) mem_.setInStaticInit(++initDepth_ > 0);
    res_.maxDepth = std::max<unsigned>(res_.maxDepth, static_cast<unsigned>(frames_.size()));
  }

  // `@__hlir_init.G` / `@__hlir_init.strN` replay a static initialiser (Frontend.cpp): what they write is the value
  // the global was BORN with, not the program having run. See Memory::Obj::progWritten.
  static bool isStaticInit(const Function &f) { return f.name.rfind("__hlir_init.", 0) == 0; }

  // Parallel assignment of branch arguments, then transfer control.
  void jump(const Op &term, const Succ &s) {
    unsigned nVisits = ++top().visits[s.dest];
    if (cfg_.loopBound && nVisits > cfg_.loopBound) {
      stop(RunStatus::LoopBound, "a loop ran more than " + std::to_string(cfg_.loopBound) + " iterations", &term);
      return;
    }
    if (cfg_.detectNonTermination) trackLoopWatch(s.dest, nVisits);
    if (cfg_.coverage && term.opc == Opc::CondBr) branchCov_.insert({&term, &s == &term.succs[0]});
    std::vector<Slot> vals;
    for (auto *a : s.args) vals.push_back(getSlot(a));
    for (size_t i = 0; i < vals.size(); ++i) setSlot(s.dest->args[i].get(), std::move(vals[i]));
    top().blk = s.dest;
    if (cfg_.coverage) cov_.insert(s.dest);
    top().ip = 0;
    event(TraceEvent::Branch, top().fn->name, "^" + blockName(s.dest), term.loc);
  }

  enum class CheckMode { Report, Assume, Ignore };
  CheckMode modeFor(const Op &op) const {
    if (const Attr *m = op.attr("mode")) {
      if (m->s == "assume") return CheckMode::Assume;
      if (m->s == "ignore") return CheckMode::Ignore;
      return CheckMode::Report;
    }
    switch (cfg_.ub) {
      case UBMode::Report: return CheckMode::Report;
      case UBMode::AssumeAbsent: return CheckMode::Assume;
      case UBMode::Wrap:
        return (op.opc == Opc::CheckSAddOvf || op.opc == Opc::CheckSSubOvf || op.opc == Opc::CheckSMulOvf || op.opc == Opc::CheckSNegOvf)
                   ? CheckMode::Ignore
                   : CheckMode::Report;
    }
    return CheckMode::Report;
  }

  // ---------------------------------------------------------------- one instruction
  // strchr/strrchr over a constant needle: answer with a chain of selects instead of executing the model's loop.
  //
  // The loop is not wrong, it is EXPENSIVE IN THE ONLY CURRENCY THE SEARCH HAS. Each iteration ends in two
  // `core.cond_br` on a condition the attacker's byte decides, so a 16-character needle contributes up to 34
  // flippable branches per call -- and "is this character a hex digit" is ONE decision, which the solver should
  // be able to settle in one query by picking any of the 16 values. Measured on c-ares CVE-2023-31130: 88% of
  // all flippable path conditions, and 82% of the queued branch flips, were inside @strchr; the subject's own
  // code contributed ~8 branches per run against strchr's ~62 (DESIGN.md §22.385).
  //
  // Applies only when the needle is a constant string the program never wrote (Memory::constBytes). Anything
  // else falls through to the model body, which stays exactly as it was.
  // --discover-pass-fn: force a gate to succeed -- return the named integer success code, or a non-null 4096-byte
  // object for a pointer-returning gate so a `!= NULL` check downstream passes.
  void passReturn(const Op &op, long value) {
    if (!op.result) return;
    const Type *rt = op.result->ty;
    if (rt->isPtr()) setP(op.result.get(), mem_.global("__hlir_discover_nonnull", 4096, false));
    else set(op.result.get(), d_.constant(llvm::APInt(rt->isBool() ? 1 : rt->width(), (uint64_t)value)));
  }

  // Direction A hybrid: symbolic bytes over a pass-fn'd call's pointer out-parameters. `--discover-pass-fn` forces
  // the CONTROL gate (the call's success code) so the setup prefix is deterministic and the search does not have to
  // line up a deep conjunction of success codes; but the real function ALSO writes fields a later DATA gate selects
  // on (e.g. hal_init fills hal_ctx->num_items), and those must read symbolic so `if (num_items > 0)` forks. So
  // after forcing the return, havoc its pointer args exactly as execUntrusted does: width-stable names (callee +
  // instance + arg + byte), bounds-clamped, a `label` that makes each byte a flippable source. M3b-A.
  void discoverHavocPtrArgs(const Op &op, const std::string &callee, const char *label, unsigned outMax) {
    if (outMax == 0) return;
    const auto &o = op.operands;
    const unsigned inst = modelCalls_[callee]++;
    const std::string base = "disc." + callee + "#" + std::to_string(inst);
    const unsigned pw = mem_.ptrWidth();
    for (size_t i = 0; i < o.size(); ++i) {
      if (!o[i]->ty->isPtr()) continue;
      Ptr p = getP(o[i]);
      auto id = d_.constValue(p.obj);
      if (!id || id->isZero()) continue;
      auto sz = d_.constValue(mem_.sizeOf(p)), off = d_.constValue(p.off), cst = d_.constValue(mem_.isConstObj(p));
      if (!sz || !off || (cst && !cst->isZero())) continue;
      uint64_t S = sz->getZExtValue(), O = off->getZExtValue();
      if (O >= S || S - O > outMax) continue;
      uint64_t n = S - O;
      std::string pre = base + ".a" + std::to_string(i) + "+";
      mem_.fillWith(p, d_.constant(llvm::APInt(pw, n)), [&](uint64_t k) { return d_.modelInput(env_, pre + std::to_string(k), 8, label); });
      if (checkMemFailed(op)) return;
    }
  }

  // --entries registered discovery run: define a skipped call's result register so later reads stay defined.
  void noopCall(const Op &op, const std::vector<Value *> & = {}) {
    if (!op.result) return;
    const Type *rt = op.result->ty;
    if (rt->isPtr()) setP(op.result.get(), Ptr{d_.zero(mem_.ptrWidth()), d_.zero(mem_.ptrWidth())});
    else set(op.result.get(), d_.constant(llvm::APInt(rt->isBool() ? 1 : rt->width(), 0)));
  }

  // --entries registered: at a registration call (resmgr_attach, vendor_util_run_loop, ...), read the
  // dispatch table it was handed and record which handler sits at which byte offset. A function pointer is a
  // global named "fn:<symbol>" (Opc::FuncAddr), so a slot whose loaded object matches one of those resolves to the
  // handler's name.
  void captureRegistration(const Op &op, const Function &callee, const std::vector<Value *> &o) {
    const RunConfig::RegCapture *rc = nullptr;
    for (auto &c : *cfg_.captureRegs)
      if (c.function == callee.name) { rc = &c; break; }
    if (!rc || rc->tableArg < 0 || (size_t)rc->tableArg >= o.size()) return;
    Ptr tbl = getP(o[rc->tableArg]);
    if (!d_.constValue(tbl.obj)) return;  // table pointer not concrete -- nothing to read
    std::map<uint64_t, std::string> fnByObj;  // obj id -> function name, for resolving slot pointers
    for (auto &fp : mod_.functions) {
      Ptr g = mem_.global("fn:" + fp->name, 1, true);
      if (auto gid = d_.constValue(g.obj)) fnByObj[gid->getZExtValue()] = fp->name;
    }
    RunConfig::CapturedReg cap;
    cap.function = callee.name;
    std::set<uint64_t> seen;
    scanHandlerTable(tbl, rc->scanBytes, fnByObj, cap, 1, seen);
    cfg_.capturedRegs->push_back(std::move(cap));
  }

  // Scan `scanBytes` of the object at `base`, pointer-slot by pointer-slot. A slot holding a function pointer
  // (a "fn:<name>" global) is a registered handler. A slot holding a pointer to ANOTHER object is followed one
  // level (`depth`), because the dispatch table commonly hangs off a pointer field rather than being inline: a module
  // sets `util_attr->callbacks = calloc(...); util_attr->callbacks[0].devctl = &my_devctl` -- the handlers live
  // behind the `callbacks` pointer, not in util_attr's own bytes (which hold only the lifecycle callbacks). `seen`
  // bounds the walk to a DAG; depth bounds it to one indirection..
  void scanHandlerTable(const Ptr &base, int scanBytes, const std::map<uint64_t, std::string> &fnByObj,
                        RunConfig::CapturedReg &cap, int depth, std::set<uint64_t> &seen) {
    auto bid = d_.constValue(base.obj);
    if (!bid || !seen.insert(bid->getZExtValue()).second) return;  // need a concrete object; never revisit one
    unsigned pw = mem_.ptrWidth();
    int step = (int)(pw / 8);
    for (int off = 0; step > 0 && off + step <= scanBytes; off += step) {
      Ptr slot{base.obj, d_.add(base.off, d_.constant(llvm::APInt(pw, (uint64_t)off)))};
      Ptr val = mem_.loadPtr(slot);
      auto vid = d_.constValue(val.obj);
      if (!vid) continue;
      auto it = fnByObj.find(vid->getZExtValue());
      if (it != fnByObj.end()) { cap.handlers.push_back({off, it->second}); continue; }
      if (depth > 0 && !vid->isZero()) scanHandlerTable(val, scanBytes, fnByObj, cap, depth - 1, seen);  // follow a sub-table pointer
    }
  }

  bool charClassFast(const Op &op, const Function &callee, const std::vector<Value *> &o) {
    // A/B aid (HLIR_NO_CHARCLASS_FOLD=1): run the model's loop instead, so the cost of the fold can be measured
    // against the thing it replaced rather than argued about.
    static const bool noFold = getenv("HLIR_NO_CHARCLASS_FOLD") != nullptr;
    if (noFold) return false;
    const bool rev = callee.name == "strrchr";
    // memchr is the same closed form with a COUNT instead of a terminator: scan exactly n bytes, first match
    // wins, no match is NULL, and the "strchr(s,0) finds the terminator" rule does not apply. It needs
    // constBytesN rather than constBytes, because it does not stop at a NUL (DESIGN.md §22.412).
    const bool isMem = callee.name == "memchr";
    if (!rev && !isMem && callee.name != "strchr") return false;
    if (o.size() != (isMem ? 3u : 2u) || !op.result || !op.result->ty->isPtr()) return false;
    Ptr base = getP(o[0]);
    std::vector<uint8_t> nb;
    if (isMem) {
      Val nv = get(o[2]);
      auto nc = D::peekVal(nv);
      if (D::isSymbolicVal(nv) || !nc) return false;
      const uint64_t n = nc->getZExtValue();
      if (n > 4096) return false;
      if (!mem_.constBytesN(base, n, nb)) return false;
    } else if (!mem_.constBytes(base, nb, 4096)) {
      return false;
    }
    const unsigned pw = mem_.ptrWidth();
    Val c = d_.trunc(get(o[1]), 8);                       // strchr takes an int and compares as a char
    Val found = d_.constant(llvm::APInt(1, 0));
    Val idx = d_.constant(llvm::APInt(pw, 0));
    // strchr(s, 0) returns a pointer to the TERMINATOR, so the NUL at nb.size() is a legal match too. Taken
    // first here, and overridden below by any earlier (strchr) match. memchr has no terminator rule: it
    // matches a zero byte only if one is actually among the n bytes scanned, which the loop below covers.
    if (!isMem) {
      Val hit = d_.icmp(Pred::Eq, c, d_.constant(llvm::APInt(8, 0)));
      idx = d_.select(hit, d_.constant(llvm::APInt(pw, nb.size())), idx);
      found = d_.or_(hit, found);
    }
    // strchr wants the FIRST match, strrchr the LAST: walk so that the wanted one is written last.
    for (size_t n = 0; n < nb.size(); ++n) {
      size_t i = rev ? n : nb.size() - 1 - n;
      Val hit = d_.icmp(Pred::Eq, c, d_.constant(llvm::APInt(8, nb[i])));
      idx = d_.select(hit, d_.constant(llvm::APInt(pw, i)), idx);
      found = d_.or_(hit, found);
    }
    Ptr np = mem_.nullPtr();
    Ptr r{d_.select(found, base.obj, np.obj), d_.select(found, d_.add(base.off, idx), np.off)};
    setP(op.result.get(), r);
    ++res_.charClassFolded;
    return true;
  }

  // ---------------------------------------------------------------- fixed-length equality, branch-free (§22.393)
  //
  // `@strstr` / `@memmem` compare the needle at each candidate position with an inner loop: one `core.cond_br` per
  // byte, on a condition the attacker decides. That is the §22.385 shape again -- ONE logical question ("do these
  // L bytes match?") spelled as L sequential ones -- but the fix cannot be the §22.385 fix. charClassFast folds a
  // call whose CONSTANT side is the buffer being scanned (a 16-byte character-class table); here the constant is
  // the needle and the scanned side is the attacker's buffer, whose length and terminator position are both
  // symbolic (HarnessGen.cpp asserts `byte[size-1] == 0` rather than writing a concrete NUL, and `size` itself
  // ranges). Folding the whole call would mean summarising a scan over a symbolic-length buffer, which is a
  // different and much harder problem, and the outer scan's `h[i] == 0` branches are not redundant anyway: they
  // ARE the encoding of where the string ends.
  //
  // So only the INNER comparison is collapsed, through a model-level helper the engine answers natively. The
  // outer scan keeps its branches, its termination semantics and its per-byte bounds checks exactly as they were.
  //
  // The precondition that matters is `inBoundsFor`. The loop reads byte k only if bytes 0..k-1 matched, so it
  // STOPS at the first mismatch; reading all n eagerly would fault where the loop never would. That is the musl
  // `strchr` false positive of §22.391 in miniature. Rather than reconstruct the guarded check, the fold simply
  // declines unless all n bytes on both sides are provably readable -- and declining costs nothing, because the
  // model body behind the helper is the same lazy byte loop this replaces.
  static constexpr uint64_t kMemEqMax = 256;

  bool inBoundsFor(const Ptr &p, uint64_t n) {
    Val w = d_.constant(llvm::APInt(mem_.ptrWidth(), n));
    auto c = D::peekVal(mem_.oobCond(p, w));
    return c && c->isZero();  // not foldable to "in bounds" (a symbolic object size, say) -> decline
  }

  // ---------------------------------------------------------------- printf closed form (DESIGN.md §22.439)
  //
  // `models/libc.core`'s @snprintf does not format: the buffer gets a NUL and the RESULT is a bounded nondet
  // labelled `fmt`, which exists so that `p += snprintf(p, rem, ...)` can drive `p` out of its buffer
  // (§22.205/§22.298). That is right when the length cannot be known -- and wrong whenever it can. libxml2 pays
  // for it on every single schema parse:
  //
  //     bufsize = snprintf(NULL, 0, "%+d.0", value) + 1;   // xmlschemastypes.c:244
  //     decimal->str = xmlMalloc(bufsize);                 // ...so the object has a SYMBOLIC size
  //     snprintf((char *)decimal->str, bufsize, "%+d.0", value);  // ...and unknown contents
  //
  // Nothing there is unknown: the format is a literal and `value` is concrete on the path. This computes the
  // real bytes and the real length when every input is concrete, and declines -- falling through to the model,
  // unchanged -- the moment any of them is not. Strictly a refinement: the nondet return is still what a
  // `%s` of an attacker string, or a symbolic integer, gets.
  //
  // The rendering is done by the HOST's snprintf, one conversion at a time. Re-implementing C's conversion
  // rules (flags, width, precision, length modifiers, the exact digits of INT_MIN) is a way to be subtly wrong
  // in a value that then gets stored into the program's memory; the library that defines them is right here.
  static constexpr uint64_t kPrintfFmtMax = 1024, kPrintfStrMax = 4096, kPrintfOutMax = 8192;

  // A NUL-terminated string the program can really read: every byte concrete, in bounds, terminated inside the
  // cap. Any of those failing is a decline, never a guess.
  bool concreteCString(const Ptr &p, uint64_t cap, std::string &out) {
    out.clear();
    const unsigned pw = mem_.ptrWidth();
    for (uint64_t i = 0; i < cap; ++i) {
      if (!inBoundsFor(p, i + 1)) return false;
      Val b = mem_.load(Ptr{p.obj, d_.add(p.off, d_.constant(llvm::APInt(pw, i)))}, 1);
      if (D::isSymbolicVal(b)) return false;
      auto c = D::peekVal(b);
      if (!c) return false;
      uint8_t ch = static_cast<uint8_t>(c->getZExtValue());
      if (!ch) return true;
      out.push_back(static_cast<char>(ch));
    }
    return false;  // no terminator within the cap
  }

  // One 8-byte variadic slot, as the frontend packed it (zeroed, then the promoted value stored at offset 0).
  bool varargSlot(const Ptr &va, uint64_t index, unsigned bytes, uint64_t &out) {
    const unsigned pw = mem_.ptrWidth();
    if (!inBoundsFor(va, 8 * (index + 1))) return false;
    Val v = mem_.load(Ptr{va.obj, d_.add(va.off, d_.constant(llvm::APInt(pw, 8 * index)))}, bytes);
    if (D::isSymbolicVal(v)) return false;
    auto c = D::peekVal(v);
    if (!c) return false;
    out = c->getZExtValue();
    return true;
  }

  // The pointer stored in a variadic slot. Pointers are (obj, off) pairs, so this needs the slot's provenance
  // rather than its integer value -- Memory::loadPtr is what the interpreter itself uses for a pointer load.
  bool varargPtr(const Ptr &va, uint64_t index, Ptr &out) {
    const unsigned pw = mem_.ptrWidth();
    if (!inBoundsFor(va, 8 * (index + 1))) return false;
    out = mem_.loadPtr(Ptr{va.obj, d_.add(va.off, d_.constant(llvm::APInt(pw, 8 * index)))});
    return true;
  }

  // Render `fmt` with the arguments in the vararg block. False = this call cannot be folded.
  bool renderPrintf(const std::string &fmt, const Ptr &va, bool haveVa, std::string &out) {
    out.clear();
    uint64_t slot = 0;
    for (size_t i = 0; i < fmt.size();) {
      if (fmt[i] != '%') { out.push_back(fmt[i++]); if (out.size() > kPrintfOutMax) return false; continue; }
      size_t start = i++;
      if (i < fmt.size() && fmt[i] == '%') { out.push_back('%'); ++i; continue; }
      while (i < fmt.size() && strchr("-+ #0'", fmt[i])) ++i;            // flags
      std::vector<long long> starArgs;
      auto numField = [&]() -> bool {                                    // width or precision
        if (i < fmt.size() && fmt[i] == '*') {
          uint64_t w;
          if (!haveVa || !varargSlot(va, slot++, 4, w)) return false;
          starArgs.push_back(static_cast<long long>(static_cast<int32_t>(w)));
          ++i;
          return true;
        }
        while (i < fmt.size() && isdigit(static_cast<unsigned char>(fmt[i]))) ++i;
        return true;
      };
      if (!numField()) return false;
      if (i < fmt.size() && fmt[i] == '.') { ++i; if (!numField()) return false; }
      std::string len;                                                   // length modifier
      while (i < fmt.size() && strchr("hljztL", fmt[i])) len.push_back(fmt[i++]);
      if (i >= fmt.size()) return false;
      const char conv = fmt[i++];
      std::string spec = fmt.substr(start, i - start);
      char buf[512];
      int n = -1;
      // The host spec must name the SAME width the slot holds, whatever the program wrote. The frontend
      // promotes, so an integer slot is at least 4 bytes and `l`/`ll`/`z`/`j`/`t` mean 8.
      const bool wide = len == "l" || len == "ll" || len == "z" || len == "j" || len == "t";
      switch (conv) {
        case 'd': case 'i': {
          uint64_t raw;
          if (!haveVa || !varargSlot(va, slot++, wide ? 8 : 4, raw)) return false;
          long long v = wide ? static_cast<long long>(raw) : static_cast<long long>(static_cast<int32_t>(raw));
          std::string hs = spec.substr(0, spec.size() - 1 - len.size()) + "lld";
          n = starArgs.size() == 2 ? snprintf(buf, sizeof buf, hs.c_str(), (int)starArgs[0], (int)starArgs[1], v)
            : starArgs.size() == 1 ? snprintf(buf, sizeof buf, hs.c_str(), (int)starArgs[0], v)
                                   : snprintf(buf, sizeof buf, hs.c_str(), v);
          break;
        }
        case 'u': case 'o': case 'x': case 'X': {
          uint64_t raw;
          if (!haveVa || !varargSlot(va, slot++, wide ? 8 : 4, raw)) return false;
          unsigned long long v = wide ? raw : static_cast<unsigned long long>(static_cast<uint32_t>(raw));
          std::string hs = spec.substr(0, spec.size() - 1 - len.size()) + "ll" + conv;
          n = starArgs.size() == 2 ? snprintf(buf, sizeof buf, hs.c_str(), (int)starArgs[0], (int)starArgs[1], v)
            : starArgs.size() == 1 ? snprintf(buf, sizeof buf, hs.c_str(), (int)starArgs[0], v)
                                   : snprintf(buf, sizeof buf, hs.c_str(), v);
          break;
        }
        case 'c': {
          uint64_t raw;
          if (!len.empty() || !haveVa || !varargSlot(va, slot++, 4, raw)) return false;
          n = starArgs.empty() ? snprintf(buf, sizeof buf, spec.c_str(), static_cast<int>(raw & 0xff))
                               : snprintf(buf, sizeof buf, spec.c_str(), (int)starArgs[0], static_cast<int>(raw & 0xff));
          break;
        }
        case 's': {
          Ptr sp;
          std::string sv;
          if (!len.empty() || !haveVa || !varargPtr(va, slot++, sp)) return false;
          // A NULL argument is glibc's "(null)", not C's: declining keeps the engine from writing bytes the
          // standard does not promise into the program's own memory.
          if (!concreteCString(sp, kPrintfStrMax, sv)) return false;
          if (sv.size() + out.size() > kPrintfOutMax) return false;
          std::vector<char> big(sv.size() + 512);
          n = starArgs.size() == 2 ? snprintf(big.data(), big.size(), spec.c_str(), (int)starArgs[0], (int)starArgs[1], sv.c_str())
            : starArgs.size() == 1 ? snprintf(big.data(), big.size(), spec.c_str(), (int)starArgs[0], sv.c_str())
                                   : snprintf(big.data(), big.size(), spec.c_str(), sv.c_str());
          if (n < 0 || static_cast<size_t>(n) >= big.size()) return false;
          out.append(big.data(), static_cast<size_t>(n));
          if (out.size() > kPrintfOutMax) return false;
          continue;
        }
        // %p would print a HOST address for a value that is an (object, offset) pair here, and %n writes
        // through a pointer. Neither has an answer this engine is entitled to give.
        default: return false;
      }
      if (n < 0 || static_cast<size_t>(n) >= sizeof buf) return false;
      out.append(buf, static_cast<size_t>(n));
      if (out.size() > kPrintfOutMax) return false;
    }
    return true;
  }

  // The checks a write of `bytes` bytes into `p` owes, run through the same Report/Assume path (and the same
  // per-check accounting) as a core.check.* op. True = the run stopped here.
  bool reportWrite(const Op &op, const Ptr &p, uint64_t bytes) {
    CheckMode mode = modeFor(op);
    if (mode == CheckMode::Ignore) return false;
    std::vector<UBViolation<D>> vs;
    mem_.accessViolations(p, d_.constant(llvm::APInt(mem_.ptrWidth(), bytes)), /*write=*/true, vs);
    if (checkMemFailed(op)) return true;
    for (auto &v : vs) {
      if (mode == CheckMode::Assume) {
        if (!d_.assume(d_.not_(v.cond))) { stop(RunStatus::Infeasible, std::string("assumed absent: ") + ubKindName(v.kind), &op); return true; }
        continue;
      }
      CheckStat &cs = res_.checks[static_cast<int>(v.kind)];
      ++cs.reached;
      const bool sym = D::isSymbolicVal(v.cond);
      if (sym) ++cs.queried; else ++cs.decidedConcretely;
      if (top().fn) { CheckStat &fc = res_.checksByFn[top().fn]; ++fc.reached; if (sym) ++fc.queried; else ++fc.decidedConcretely; }
      if (d_.violated(v.cond, [&] { Finding f = ubFinding(v.kind, op); f.frontierOnly = d_.onlyFrontier(v.cond); f.inPrologue = inPrologue(); return f; })) {
        reportUB(v.kind, op);
        return true;
      }
    }
    return false;
  }

  bool printfFold(const Op &op, const Function &callee, const std::vector<Value *> &o) {
    static const bool noFold = getenv("HLIR_NO_PRINTF_FOLD") != nullptr;
    if (noFold) return false;
    const bool isSn = callee.name == "snprintf";
    const bool isSp = callee.name == "sprintf";
    if (!isSn && !isSp) return false;
    if (!op.result || !op.result->ty->isInt()) return false;
    if (isSn && o.size() != 4) return false;
    if (isSp && o.size() != 3) return false;
    static const bool diag = getenv("HLIR_DEBUG_PRINTF") != nullptr;
    auto decline = [&](const char *why) { if (diag) fprintf(stderr, "[printf] decline @%s:%u: %s\n", op.loc.file.c_str(), op.loc.line, why); return false; };

    const Ptr buf = getP(o[0]);
    const Ptr fmtP = getP(o[isSn ? 2 : 1]);
    const Ptr va = getP(o[isSn ? 3 : 2]);
    uint64_t n = 0;
    if (isSn) {
      Val nv = get(o[1]);
      auto nc = D::peekVal(nv);
      if (D::isSymbolicVal(nv) || !nc) return decline("the size argument is symbolic");
      n = nc->getZExtValue();
    }
    std::string fmt;
    if (!concreteCString(fmtP, kPrintfFmtMax, fmt)) return decline("the format string is not a concrete, bounded C string");
    std::string out;
    auto vaNull = D::peekVal(va.obj);
    const bool haveVa = !(vaNull && vaNull->isZero());
    if (!renderPrintf(fmt, va, haveVa, out)) return decline("a conversion or an argument is not concrete");

    // snprintf writes at most n-1 bytes plus the terminator and writes nothing at all when n is 0; sprintf
    // writes the whole thing. The RETURN is the would-be length either way, which is the contract the
    // `p += snprintf(...)` idiom rests on and the reason the model's nondet exists.
    const uint64_t len = out.size();
    const uint64_t copy = isSp ? len : (n == 0 ? 0 : std::min<uint64_t>(len, n - 1));
    if (isSp || n > 0) {
      if (reportWrite(op, buf, copy + 1)) return true;
      const unsigned pw = mem_.ptrWidth();
      for (uint64_t k = 0; k < copy; ++k)
        mem_.store(Ptr{buf.obj, d_.add(buf.off, d_.constant(llvm::APInt(pw, k)))},
                   d_.constant(llvm::APInt(8, static_cast<uint8_t>(out[k]))), 1);
      mem_.store(Ptr{buf.obj, d_.add(buf.off, d_.constant(llvm::APInt(pw, copy)))}, d_.constant(llvm::APInt(8, 0)), 1);
      if (checkMemFailed(op)) return true;
    }
    set(op.result.get(), d_.constant(llvm::APInt(op.result->ty->width(), len)));
    ++res_.printfFolded;
    if (diag) fprintf(stderr, "[printf] folded @%s:%u \"%s\" -> \"%s\" (%llu)\n", op.loc.file.c_str(), op.loc.line,
                      fmt.c_str(), out.c_str(), static_cast<unsigned long long>(len));
    return true;
  }

  bool memEqFast(const Op &op, const Function &callee, const std::vector<Value *> &o) {
    // A/B aid, same contract as HLIR_NO_CHARCLASS_FOLD: run the model's loop so the cost can be measured.
    static const bool noFold = getenv("HLIR_NO_MEMEQ_FOLD") != nullptr;
    if (noFold) return false;
    if (callee.name != "__hlir_memeq") return false;
    if (o.size() != 3 || !op.result || !op.result->ty->isInt()) return false;
    static const bool diag = getenv("HLIR_DEBUG_MEMEQ") != nullptr;
    Val nv = get(o[2]);
    auto nc = D::peekVal(nv);
    if (D::isSymbolicVal(nv) || !nc) {
      if (diag) fprintf(stderr, "[memeq] decline: length is not a concrete constant (symbolic=%d)\n", (int)D::isSymbolicVal(nv));
      return false;
    }
    const uint64_t n = nc->getZExtValue();
    if (n > kMemEqMax) {  // the term count is linear in n; a huge n is not worth one branch
      if (diag) fprintf(stderr, "[memeq] decline: n=%llu over cap\n", static_cast<unsigned long long>(n));
      return false;
    }
    Ptr a = getP(o[0]), b = getP(o[1]);
    const bool ia = inBoundsFor(a, n), ib = inBoundsFor(b, n);
    if (!ia || !ib) {
      // Worth printing rather than guessing: the usual cause is an object whose SIZE is symbolic (an attacker
      // cstring parameter is allocated with a size range, HarnessGen.cpp), and then nothing here can fold.
      if (diag) fprintf(stderr, "[memeq] decline: n=%llu haystack_in_bounds=%d needle_in_bounds=%d\n",
                        static_cast<unsigned long long>(n), ia, ib);
      return false;
    }
    const unsigned pw = mem_.ptrWidth(), rw = op.result->ty->width();
    Val eq = d_.constant(llvm::APInt(1, 1));
    for (uint64_t k = 0; k < n; ++k) {
      Val off = d_.constant(llvm::APInt(pw, k));
      Val x = mem_.load(Ptr{a.obj, d_.add(a.off, off)}, 1);
      Val y = mem_.load(Ptr{b.obj, d_.add(b.off, off)}, 1);
      eq = d_.and_(eq, d_.icmp(Pred::Eq, x, y));
    }
    set(op.result.get(), d_.select(eq, d_.constant(llvm::APInt(rw, 1)), d_.constant(llvm::APInt(rw, 0))));
    ++res_.memEqFolded;
    return true;
  }

  // ---------------------------------------------------------------- strcmp against a LITERAL (§22.491)
  //
  // Every configuration and protocol parser is a keyword table: `strcasecmp(token, "Host")` sixty times
  // over. Modelled faithfully, each call is a per-byte loop whose branches the attacker decides, and the
  // flip queue fills with them -- measured on libssh's ssh_config_parse_string the moment strcasecmp got
  // a model: 1,116,733 calls, 43% of the search budget in strcasecmp and another 41% in the
  // ssh_config_get_opcode loop around it, 868,227 flips queued, and ONE symbolic path out of 7077 runs.
  // The run was re-walking the keyword table instead of getting past it.
  //
  // Same shape as §22.385 and §22.393: one logical question ("is this token that word?") spelled as L
  // sequential ones. Here the constant side is a NUL-terminated literal whose bytes and length the engine
  // can read (Memory::constBytes), so the whole call folds to a value with no branches at all.
  //
  // The value is EXACT, not just "zero or not". glibc returns the difference of the first differing byte
  // pair, and callers sort with it (bsearch over a keyword table does exactly that), so a fold that only
  // preserved equality would quietly break ordering. The chain below is that difference, innermost-last:
  //     ite(b0 != l0, b0 - l0, ite(b1 != l1, b1 - l1, ... ite(bL != 0, bL - 0, 0)))
  // including position L, where the literal's NUL decides whether the subject is longer.
  //
  // Declines the way memEqFast does when the subject's L+1 bytes are not provably readable: a symbolic
  // object size means the model's lazy loop is the only honest answer, and declining costs nothing.
  static constexpr uint64_t kStrCmpLiteralMax = 64;

  bool strCmpLiteralFast(const Op &op, const Function &callee, const std::vector<Value *> &o) {
    static const bool noFold = getenv("HLIR_NO_STRCMP_FOLD") != nullptr;
    if (noFold) return false;
    const bool fold_case = callee.name == "strcasecmp" || callee.name == "stricmp";
    if (!fold_case && callee.name != "strcmp") return false;
    if (o.size() != 2 || !op.result || !op.result->ty->isInt()) return false;

    // Which side is the literal? Either, and if both are the comparison is constant anyway.
    Ptr a = getP(o[0]), b = getP(o[1]);
    std::vector<uint8_t> lit;
    Ptr subj;
    static const bool diag = getenv("HLIR_DEBUG_STRCMP") != nullptr;
    bool litIsSecond;
    if (mem_.constBytes(b, lit, kStrCmpLiteralMax)) { subj = a; litIsSecond = true; }
    else if (mem_.constBytes(a, lit, kStrCmpLiteralMax)) { subj = b; litIsSecond = false; }
    else {
      if (diag) fprintf(stderr, "[strcmp] decline: neither side is a readable constant string\n");
      return false;
    }
    const uint64_t L = lit.size();                       // constBytes stops at the NUL, which it excludes
    if (L + 1 > kStrCmpLiteralMax || !inBoundsFor(subj, L + 1)) {
      if (diag) fprintf(stderr, "[strcmp] decline: literal=%.*s L=%llu subject_in_bounds=%d\n",
                        (int)std::min<size_t>(lit.size(), 24), (const char *)lit.data(),
                        (unsigned long long)L, (int)inBoundsFor(subj, L + 1));
      return false;
    }

    const unsigned pw = mem_.ptrWidth(), rw = op.result->ty->width();
    auto lower = [&](Val v) {
      if (!fold_case) return v;
      Val ge = d_.icmp(Pred::Uge, v, d_.constant(llvm::APInt(8, 'A')));
      Val le = d_.icmp(Pred::Ule, v, d_.constant(llvm::APInt(8, 'Z')));
      Val up = d_.and_(ge, le);
      return d_.select(up, d_.add(v, d_.constant(llvm::APInt(8, 32))), v);
    };
    auto litByte = [&](uint64_t k) {
      uint8_t c = k < L ? lit[k] : 0;
      if (fold_case && c >= 'A' && c <= 'Z') c = static_cast<uint8_t>(c + 32);
      return d_.constant(llvm::APInt(8, c));
    };

    Val r = d_.constant(llvm::APInt(rw, 0));             // all L+1 positions equal -> 0
    for (uint64_t k = L + 1; k-- > 0;) {
      Val off = d_.constant(llvm::APInt(pw, k));
      Val sb = lower(mem_.load(Ptr{subj.obj, d_.add(subj.off, off)}, 1));
      Val lb = litByte(k);
      Val diff = d_.sub(d_.zext(sb, rw), d_.zext(lb, rw));
      if (!litIsSecond) diff = d_.sub(d_.zext(lb, rw), d_.zext(sb, rw));
      r = d_.select(d_.icmp(Pred::Eq, sb, lb), r, diff);
    }
    set(op.result.get(), r);
    ++res_.strCmpFolded;
    return true;
  }

  // ---------------------------------------------------------------- compare-only pointer arithmetic (§22.390)
  //
  // `if (p + n > end)` is the standard C bound-check idiom and it is undefined behaviour: C11 6.5.6p8 lets a
  // pointer land inside its object or one past the end and nowhere else, so FORMING `p + n` is already UB even
  // though nothing is ever read or written through it. That is a true positive, not an over-approximation --
  // AddressSanitizer reports the same sites as `invalid-pointer-pair` (verified on c-ares
  // `inet_net_pton.c:334`, a 2-byte stack overshoot, and `ares_parse_naptr_reply.c:108`, where the overshoot is
  // the attacker's 16-bit RDLENGTH) -- so it is still reported.
  //
  // What it is NOT is a memory-safety violation, and reporting it at full severity broke the one thing verdicts
  // exist for. On the c-ares tree where CVE-2017-1000381 is FIXED, the only non-warning findings were four of
  // these, so a tree with the defect removed still read `bug`: the negative control, which is one of the four
  // criteria the CVE corpus detects by, was being satisfied only because the lines were checked by hand.
  //
  // The test is static, intra-function and conservative. Take the `core.ptr_add` this check guards and require
  // every use of its result to be a pointer comparison, a pointer difference, another bounds check, or a
  // FURTHER ptr_add that is itself only compared. The last case is not optional: `encoded + offset + 1` (c-ares
  // ares_expand_name.c:175) is two chained adds, and without the transitive step the first one stays a finding
  // and keeps a clean tree at `bug` on its own. A store, a load, a call argument, a successor argument --
  // anything that could let the pointer reach memory -- leaves it a finding, as does a value with no uses at
  // all, which is not this idiom. A cycle resolves to "not compare-only"; the conservative direction.
  // A LOCAL SLOT (an `alloca` holding a local variable) is compare-only when its ADDRESS never escapes --
  // every use is a load from it or a store into it -- and every value loaded back out is itself
  // compare-only. If some other value is also stored into the same slot and THAT one is dereferenced, the
  // loads are not compare-only and no downgrade happens: the conservative direction.
  static bool slotOnlyCompared(const Value *slot, const std::unordered_map<const Value *, std::vector<const Op *>> &uses,
                               const std::unordered_map<const Value *, const Op *> &defs,
                               std::unordered_map<const Value *, int> &memo) {
    auto m = memo.find(slot);
    if (m != memo.end()) return m->second == 1;
    memo[slot] = 2;
    auto it = uses.find(slot);
    if (it == uses.end() || it->second.empty()) return false;
    for (const Op *u : it->second) {
      switch (u->opc) {
        case Opc::Load:
          if (!u->result || !valOnlyCompared(u->result.get(), uses, defs, memo)) return false;
          break;
        case Opc::Store:
          // the slot may only be written THROUGH; storing the slot's own address somewhere lets it escape
          if (u->operands.size() < 2 || u->operands[1] != slot) return false;
          break;
        // The checks the engine itself emits around a slot access (`core.check.uninit %slot` precedes every
        // load of a local) validate the access to the SLOT, not a dereference of the pointer stored in it,
        // so they do not make the stored pointer anything other than compare-only. Leaving them out is what
        // made the first version of this rule do nothing: `ep`'s alloca is used by a check.uninit before it
        // is ever loaded, and that single unlisted opcode rejected the whole slot.
        case Opc::CheckUninit: case Opc::CheckNull: case Opc::CheckUaf: case Opc::CheckOob:
        case Opc::CheckAlign: case Opc::CheckConstWrite:
          break;
        default:
          return false;
      }
    }
    memo[slot] = 1;
    return true;
  }

  static bool valOnlyCompared(const Value *v, const std::unordered_map<const Value *, std::vector<const Op *>> &uses,
                              const std::unordered_map<const Value *, const Op *> &defs,
                              std::unordered_map<const Value *, int> &memo) {
    auto m = memo.find(v);
    if (m != memo.end()) return m->second == 1;
    memo[v] = 2;  // cycles and re-entry resolve to "not compare-only" until proven otherwise
    auto it = uses.find(v);
    if (it == uses.end() || it->second.empty()) return false;
    for (const Op *u : it->second) {
      switch (u->opc) {
        case Opc::PtrCmp: case Opc::CheckPtrCmp: case Opc::PtrDiff: case Opc::CheckPtrArith:
          break;  // reads the pointer's VALUE, never the memory it names
        case Opc::PtrAdd:
          if (!u->result || !valOnlyCompared(u->result.get(), uses, defs, memo)) return false;
          break;
        case Opc::Store: {
          // `const u_char *ep = cp + len;` puts the pointer in a local, so the ptr_add's first use is a
          // store into an alloca and the value only reappears at the matching load. Without following that,
          // the rule stops at the first statement of nearly every tcpdump printer (DESIGN.md §22.406).
          // Only as the STORED VALUE: if `v` were the address operand, the pointer would be the target of a
          // write, which is a dereference and must stay a finding.
          if (u->operands.size() < 2 || u->operands[0] != v || u->operands[1] == v) return false;
          const Value *slot = u->operands[1];
          auto d = defs.find(slot);
          if (d == defs.end() || d->second->opc != Opc::Alloca) return false;
          if (!slotOnlyCompared(slot, uses, defs, memo)) return false;
          break;
        }
        default:
          return false;
      }
    }
    memo[v] = 1;
    return true;
  }
  bool ptrArithCompareOnly(const Op &chk) {
    const Block *b = chk.parent;
    const Function *fn = b ? b->parent : nullptr;
    if (!fn) return false;
    if (cmpOnlyDone_.insert(fn).second) {
      std::unordered_map<const Value *, std::vector<const Op *>> uses;
      std::unordered_map<const Value *, const Op *> defs;   // result value -> the op that defines it
      for (auto &blk : fn->blocks)
        for (auto &o : blk->ops) {
          const Op *op = o.get();
          op->forEachUse([&](const Value *v) { if (v) uses[v].push_back(op); });
          if (op->result) defs[op->result.get()] = op;
        }
      std::unordered_map<const Value *, int> valMemo;  // 0 unknown, 1 compare-only, 2 not (also the cycle guard)
      for (auto &blk : fn->blocks)
        for (size_t i = 0; i < blk->ops.size(); ++i) {
          const Op *c = blk->ops[i].get();
          if (c->opc != Opc::CheckPtrArith) continue;
          const Op *add = nullptr;
          for (size_t j = i + 1; j < blk->ops.size() && j <= i + 3; ++j)
            if (blk->ops[j]->opc == Opc::PtrAdd && blk->ops[j]->operands == c->operands) { add = blk->ops[j].get(); break; }
          cmpOnlyMemo_[c] = add && add->result && valOnlyCompared(add->result.get(), uses, defs, valMemo);
        }
      // Same pass, second question: a `core.check.uninit` whose LOADED VALUE has no uses at all. Reading an
      // indeterminate value is undefined (C11 6.3.2.1p2) and is reported, but when the value goes NOWHERE,
      // stopping the run is detection in the wrong place -- the same argument as §22.428 for pointer
      // arithmetic. The concrete case is libxml2's
      //
      //     xmlSAXHandlerPtr sax;
      //     (void) sax;            /* silences an unused-variable warning */
      //     ...
      //     sax = ctxt->sax;
      //
      // which sits in xmlCtxtInitializeLate, i.e. in front of EVERY parse. The run died there, runs=0, and
      // nothing of the library was analysed. A value with no uses cannot make any later state wrong, so the
      // finding is recorded and execution goes on.
      for (auto &blk : fn->blocks)
        for (size_t i = 0; i < blk->ops.size(); ++i) {
          const Op *c = blk->ops[i].get();
          if (c->opc != Opc::CheckUninit) continue;
          const Op *ld = nullptr;
          for (size_t j = i + 1; j < blk->ops.size() && j <= i + 3; ++j)
            if (blk->ops[j]->opc == Opc::Load && !blk->ops[j]->operands.empty() && !c->operands.empty() &&
                blk->ops[j]->operands[0] == c->operands[0]) { ld = blk->ops[j].get(); break; }
          auto u = ld && ld->result ? uses.find(ld->result.get()) : uses.end();
          uninitDeadMemo_[c] = ld && ld->result && (u == uses.end() || u->second.empty());
        }
    }
    auto it = cmpOnlyMemo_.find(&chk);
    return it != cmpOnlyMemo_.end() && it->second;
  }
  // `core.check.uninit` whose loaded value has no uses: the read is undefined but goes nowhere (see the pass).
  bool uninitValueDead(const Op &chk) {
    const Block *b = chk.parent;
    const Function *fn = b ? b->parent : nullptr;
    if (!fn) return false;
    if (!cmpOnlyDone_.count(fn)) (void)ptrArithCompareOnly(chk);  // the pass computes both
    auto it = uninitDeadMemo_.find(&chk);
    return it != uninitDeadMemo_.end() && it->second;
  }
  std::unordered_set<const Function *> cmpOnlyDone_;
  std::unordered_map<const Op *, bool> cmpOnlyMemo_;
  std::unordered_map<const Op *, bool> uninitDeadMemo_;

  void step() {
    Frame &fr = top();
    const Op &op = *fr.blk->ops[fr.ip];
    // Stamp every object allocated from here on with the site that created it (DESIGN.md §22.375). Done once per
    // op rather than at each `mem_.alloc` call so that an allocation inside a model handler is stamped too.
    mem_.setAllocSite(fr.fn, &op.loc);
    d_.beginOp(op);
    ++fr.ip;  // call/branch handlers override
    const auto &o = op.operands;
    auto bin = [&](auto f) { set(op.result.get(), f(get(o[0]), get(o[1]))); };

    switch (op.opc) {
      case Opc::Const: set(op.result.get(), d_.constant(op.constVal)); break;
      case Opc::Add: bin([&](auto &a, auto &b) { return d_.add(a, b); }); break;
      case Opc::Sub: bin([&](auto &a, auto &b) { return d_.sub(a, b); }); break;
      case Opc::Mul: bin([&](auto &a, auto &b) { return d_.mul(a, b); }); break;
      case Opc::UDiv: bin([&](auto &a, auto &b) { return d_.udiv(a, b); }); break;
      case Opc::SDiv: bin([&](auto &a, auto &b) { return d_.sdiv(a, b); }); break;
      case Opc::URem: bin([&](auto &a, auto &b) { return d_.urem(a, b); }); break;
      case Opc::SRem: bin([&](auto &a, auto &b) { return d_.srem(a, b); }); break;
      case Opc::And: bin([&](auto &a, auto &b) { return d_.and_(a, b); }); break;
      case Opc::Or: bin([&](auto &a, auto &b) { return d_.or_(a, b); }); break;
      case Opc::Xor: bin([&](auto &a, auto &b) { return d_.xor_(a, b); }); break;
      case Opc::Shl: bin([&](auto &a, auto &b) { return d_.shl(a, b); }); break;
      case Opc::LShr: bin([&](auto &a, auto &b) { return d_.lshr(a, b); }); break;
      case Opc::AShr: bin([&](auto &a, auto &b) { return d_.ashr(a, b); }); break;
      case Opc::Not: set(op.result.get(), d_.not_(get(o[0]))); break;
      case Opc::Neg: set(op.result.get(), d_.neg(get(o[0]))); break;
      case Opc::ZExt: set(op.result.get(), d_.zext(get(o[0]), op.resultType()->width())); break;
      case Opc::SExt: set(op.result.get(), d_.sext(get(o[0]), op.resultType()->width())); break;
      case Opc::Trunc: set(op.result.get(), d_.trunc(get(o[0]), op.resultType()->width())); break;
      case Opc::Extract: set(op.result.get(), d_.extract(get(o[0]), static_cast<unsigned>(op.intAttr("hi")), static_cast<unsigned>(op.intAttr("lo")))); break;
      case Opc::Concat: bin([&](auto &a, auto &b) { return d_.concat(a, b); }); break;
      case Opc::ICmp: {
        Pred p;
        predFromString(op.pred, p);
        set(op.result.get(), d_.icmp(p, get(o[0]), get(o[1])));
        break;
      }
      case Opc::Select:
        if (op.resultType()->isPtr()) {
          Ptr a = getP(o[1]), b = getP(o[2]);
          setP(op.result.get(), Ptr{d_.select(get(o[0]), a.obj, b.obj), d_.select(get(o[0]), a.off, b.off)});
        } else {
          set(op.result.get(), d_.select(get(o[0]), get(o[1]), get(o[2])));
        }
        break;
      case Opc::B2I: set(op.result.get(), d_.zext(get(o[0]), op.resultType()->width())); break;
      case Opc::FOp: {
        // IEEE arithmetic on bit patterns. Exact when every operand is concrete (concrete runs, and the concrete side of the taint
        // engine); a symbolic operand gives an unconstrained result (floating point is not modelled in SMT), tainted if an operand is.
        std::vector<Val> args;
        std::vector<llvm::APInt> cs;
        bool allConst = true;
        for (auto *x : o) {
          args.push_back(get(x));
          auto c = d_.constValue(args.back());
          if (!c) { allConst = false; break; }
          cs.push_back(*c);
        }
        unsigned rw = op.resultType()->isBool() ? 1 : op.resultType()->width();
        Val r;
        if (allConst) {
          auto v = fpEval(op.attr("k") ? op.attr("k")->s : "", static_cast<unsigned>(op.intAttr("fw", 64)), static_cast<unsigned>(op.intAttr("rw", 64)), cs, rw);
          if (!v) { unsupported(op, "floating point operation " + (op.attr("k") ? op.attr("k")->s : std::string("?"))); return; }
          r = d_.constant(*v);
        } else {
          r = d_.fresh("fop", rw);
        }
        // The name is deliberately stable (not `fresh`): seeds and replay are keyed by variable name. It must still
        // encode the RESULT WIDTH -- the TermManager outlives a single run, and the same (function, step) index can
        // land on a differently-typed fp op on another path, which used to abort the worker in TermManager::bvVar
        // and turn the whole entry into a silent `unknown` (DESIGN.md §22.414).
        if constexpr (D::kTaint)
          r = d_.opaqueDerived(r, args, "fop." + top().fn->name + "." + std::to_string(res_.steps) + "w" + std::to_string(rw));
        set(op.result.get(), std::move(r));
        break;
      }
      case Opc::I2B: {
        const Val &v = get(o[0]);
        set(op.result.get(), d_.icmp(Pred::Ne, v, d_.zero(d_.width(v))));
        break;
      }

      case Opc::Br: jump(op, op.succs[0]); break;
      case Opc::CondBr: {
        if (cfg_.detectNonTermination && watch_) collectDeps(o[0]);
        if constexpr (D::kTaint) {
          const Val &c = get(o[0]);
          // A tainted branch that controls a loop: taking one of its edges re-enters a block already visited in this
          // frame (a back-edge / loop-header re-check). In a structured CFG a successor can be already-visited only
          // across a back-edge, so this is a loop whose iteration count the attacker influences -> DoS warning.
          if (d_.isAttackerControlled(c)) {
            res_.taintReach.loopBound = true;
            bool loop = false;
            for (auto &sc : op.succs) if (top().visits.count(sc.dest)) { loop = true; break; }
            if (loop && warnedLoop_.insert(&op).second) {
              // Classify the condition's attacker-controlled operands into loop-invariant bounds (the `n` of
              // `i < n`, thresholded against a dominating cap) and loop-variant ones (an element re-read every
              // iteration, which no value cap can bound). taintLoopWarn suppresses only when every invariant
              // bound is capped AND no attacker-controlled variant operand is present. The loop is the one
              // CONTAINING this branch (op.parent), not the already-visited successor.
              const Loop *L = loopContaining(top().fn, op.parent);
              const std::set<const Value *> *stored = L ? &storedBasesOf(L) : nullptr;
              std::vector<std::pair<Val, bool>> invBounds;  // (bound value, signed comparison?)
              bool variantTaint = false;
              gatherLoopBounds(o[0], L, stored, invBounds, variantTaint, 0);
              d_.taintLoopWarn(c, invBounds, variantTaint, [&] { return ubFinding(UBKind::TaintedLoopBound, op); });
            }
          }
        }
        noteGlobalGated(op, o[0]);
        jump(op, d_.decide(get(o[0])) ? op.succs[0] : op.succs[1]);
        break;
      }
      case Opc::Switch: {
        if (cfg_.detectNonTermination && watch_) collectDeps(o[0]);
        const Val &v = get(o[0]);
        unsigned w = d_.width(v);
        for (size_t i = 0; i < op.caseVals.size(); ++i)
          if (d_.decide(d_.icmp(Pred::Eq, v, d_.constant(op.caseVals[i].sextOrTrunc(w))))) { jump(op, op.succs[i]); return; }
        jump(op, op.succs.back());
        break;
      }
      case Opc::Return: {
        std::optional<Slot> rv;
        if (!o.empty()) rv = getSlot(o[0]);
        event(TraceEvent::Return, top().fn->name, rv ? describe(o[0]) : "void", op.loc);
        const Op *callOp = top().callOp;
        d_.onReturn(*top().fn, rv ? &rv->a : nullptr);
        for (uint32_t id : top().allocas) mem_.killId(id);  // locals die with the frame
        if (isStaticInit(*top().fn)) mem_.setInStaticInit(--initDepth_ > 0);
        frames_.pop_back();
        if (frames_.empty()) {
          res_.status = RunStatus::Returned;
          retslot_ = rv;
          done_ = true;
        } else if (callOp && callOp->result && rv) {
          setSlot(callOp->result.get(), std::move(*rv));
        }
        break;
      }
      case Opc::Unreachable:
        d_.violated(d_.constant(llvm::APInt(1, 1)), [&] { return ubFinding(UBKind::UnreachableReached, op); });
        reportUB(UBKind::UnreachableReached, op);
        break;
      case Opc::Call: {
        const Function *callee = mod_.findFunction(op.sym);
        if (!callee) {
          // Discovery run (--entries registered): the run only has to REACH the registration calls, so an
          // unknown callee is skipped, not fatal. Its result register is defined to a default so later reads do
          // not fault. Outside bestEffortInit this stays the hard error it has always been.
          if (cfg_.bestEffortInit) { noopCall(op, o); break; }
          unsupported(op, "call to unknown function @" + op.sym); return;
        }
        // --entries registered: capture the dispatch table handed to a registration call (resmgr_attach, the util
        // wrapper, register_filesystem, ...). The handlers written into it ARE the taint entries, read out of the
        // live table by running main -- so a handler passed through a parameter or stored in a heap field (both of
        // which defeat the static iface binding) is found all the same.
        if (cfg_.captureRegs && cfg_.capturedRegs) captureRegistration(op, *callee, o);
        // --discover-pass-fn: a semantic gate forced to succeed (return its named success code, or a non-null
        // object for a pointer) without running its body, so the discovery run reaches the registration past a
        // check it otherwise fails (e.g. a HAL version compare, a hal_ctx==NULL guard).
        if (cfg_.passFns) {
          auto pf = cfg_.passFns->find(callee->name);
          if (pf != cfg_.passFns->end()) {
            passReturn(op, pf->second);
            if (cfg_.discoverHavoc) discoverHavocPtrArgs(op, callee->name, "disc", (unsigned)cfg_.discoverHavocBytes);
            break;
          }
        }
        // A dispatch-loop entry reached from inside the initialiser: the initialiser has done its job. Unwind to
        // just before the prologue call and let the harness continue with the entry -- blocking in that loop is
        // what the real program does, and it is the state the handler is then called from. Never applies outside
        // the prologue: there the same function is an ordinary (unmodelled) call. DESIGN.md §22.368 §2.
        if (cfg_.stopFns && cfg_.stopFns->count(callee->name) && unwindPrologue(op)) break;
        // A char-class lookup over a CONSTANT set has a closed form and must not be run as a loop (§22.385).
        if (charClassFast(op, *callee, o)) break;
        if (memEqFast(op, *callee, o)) break;
        if (strCmpLiteralFast(op, *callee, o)) break;
        if (printfFold(op, *callee, o)) break;
        // Already-done initialiser: memory holds what it produced, so the call is a no-op. Its result is never read
        // (the harness discards it), and zero is written only so the register is defined.
        if (skipPrologue_ && cfg_.prologueFns && cfg_.prologueFns->count(callee->name)) {
          if (op.result) {
            const Type *rt = op.result->ty;
            if (rt->isPtr()) setP(op.result.get(), Ptr{d_.zero(mem_.ptrWidth()), d_.zero(mem_.ptrWidth())});
            else set(op.result.get(), d_.constant(llvm::APInt(rt->isBool() ? 1 : rt->width(), 0)));
          }
          break;
        }
        const model::CallModel *ovm = !callee->isDeclaration() && cfg_.models ? cfg_.models->lookup(callee->name) : nullptr;
        if (ovm && !ovm->overrideBody) ovm = nullptr;  // a body wins over a model unless the model says `override: true`
        if (callee->isDeclaration() || ovm) {
          const model::CallModel *cm = ovm ? ovm : cfg_.models ? cfg_.models->lookup(callee->name) : nullptr;
          if (cm && !ovm && cm->function == "<opaque>") {  // an unmodelled external: hostile when it belongs to an untrusted API
            ++res_.opaqueCalls[callee->name];
            // Direction A (discoverHavoc): run the opaque setup call AS IF untrusted -- a symbolic return and
            // symbolic bytes over every pointer arg it is handed -- so a field it "fills" (e.g. a driver: hal_ctx->num_items)
            // reads symbolic and the registration-selecting gate forks. This is where the environment turns symbolic
            // (opaque calls are most of a module's setup)..
            if (cfg_.discoverHavoc) { execUntrusted(op, *callee, "disc", (unsigned)cfg_.discoverHavocBytes); return; }
            std::string lb;
            unsigned om = 0;
            if (cfg_.models->untrusted(callee->name, lb, om)) { execUntrusted(op, *callee, lb, om); return; }
          }
          if (!cm) {
            if (cfg_.discoverHavoc) { execUntrusted(op, *callee, "disc", (unsigned)cfg_.discoverHavocBytes); return; }  // model-less setup call: same symbolic treatment
            if (cfg_.bestEffortInit) { noopCall(op, o); return; }  // discovery run: skip, only reaching registration calls matters
            unsupported(op, "call to external function @" + op.sym + " (no model for it: add one to the ModelDB)"); return;
          }
          execModel(op, *callee, *cm);
          return;
        }
        if (frames_.size() >= cfg_.maxCallDepth) { stop(RunStatus::DepthLimit, "call depth limit reached", &op); return; }
        std::vector<Slot> args;
        for (auto *a : o) args.push_back(getSlot(a));
        event(TraceEvent::Call, callee->name, "from @" + top().fn->name, op.loc);
        pushFrame(*callee, std::move(args), &op);
        d_.onCall(*callee);
        break;
      }

      case Opc::Assume:
        if (!d_.assume(get(o[0]))) {
          if (const Attr *t = op.attr("terminates")) terminate(op, t->s.empty() ? "assume" : t->s);
          else {
            // The session constructor could not succeed in this scan set. Flagged rather than just "infeasible",
            // because the right response is to DROP the constructor and analyse the entry anyway -- a half-run
            // constructor leaves a state the program never has, and §22.368 §3's rule is all-or-nothing.
            const Attr *nm = op.attr("name");
            if (nm && nm->s == "setup.success") res_.setupInfeasible = true;
            stop(RunStatus::Infeasible, nm ? "assumption is false: " + nm->s : std::string("assumption is false"), &op);
          }
        }
        break;
      case Opc::Assert: {
        const Attr *m = op.attr("msg");
        std::string msg = m ? m->s : "assertion failed";
        auto mk = [&] {
          Finding f;
          f.status = RunStatus::AssertFailed;
          f.message = msg;
          f.loc = op.loc;
          f.site = &op;
          return f;
        };
        if (d_.violated(d_.not_(get(o[0])), mk)) stop(RunStatus::AssertFailed, msg, &op);
        break;
      }
      case Opc::Nondet: {
        if (cfg_.detectNonTermination && watch_) watch_->sawNewNondet = true;
        const Type *t = op.resultType();
        if (t->isPtr()) { unsupported(op, "pointer-valued nondet is introduced by entry initialisation (P5)"); return; }
        Val v = d_.nondet(env_, op, t->isBool() ? 1 : t->width());
        noteNondet(op, "an unconstrained value the engine chose");
        event(TraceEvent::Nondet, top().fn->name, d_.str(v, t->isBool()), op.loc);
        set(op.result.get(), std::move(v));
        break;
      }
      case Opc::Trace: {
        // The harness brackets the project initialiser's calls with these (HarnessGen, DESIGN.md §22.368). The
        // initialiser does not depend on the entry's inputs, so its result is the same on every run: capture it
        // once and skip the calls afterwards. Measured need: without this the median sound/core run grew from 381
        // to 34587 steps and the concolic fuzzer lost an order of magnitude of runs (round 49c).
        if (const Attr *ev = op.attr("event")) {
          if (ev->s == "hlir.prologue.begin") {
            auto *c = prologueCache();
            if (c && c->valid && mem_.restoreSnapshot(c->snap)) {
              skipPrologue_ = true;   // the calls below are no-ops; memory already holds what they produced
            } else {
              skipPrologue_ = false;
              prologueBase_ = mem_.objectCount();
              capturePrologue_ = c != nullptr;
            }
            break;
          }
          if (ev->s == "hlir.entry.begin") { entryBegun_ = true; break; }
          // ---------------------------------------------------------- setup region (DESIGN.md §22.438)
          if (ev->s == "hlir.setup.begin") {
            // The markers mean "this is setup" to EVERY engine and on EVERY run: allocations in here succeed and
            // the branches in here are not offered to the search. That must not depend on whether a cache is
            // attached, on whether this run is the capturing one, or on whether the state turned out reusable --
            // measured: the symbolic escalation pass gets no cache, ran the region as ordinary code, and
            // reported a null_deref from an allocation failure inside a region the harness had declared.
            inSetupRegion_ = true;
            d_.setSetupRegion(true);
            auto *c = setupCacheOff() ? nullptr : setupCache();
            if (!c) break;             // nobody is collecting one: the region simply runs, with the above in force
            if (c->state == SetupCache::State::Refused) break;
            if (c->state == SetupCache::State::Valid && setupVerifyOn() && !setupVerified_) {
              // Re-run the region exactly as the capturing run did, but into nothing: the comparison at the end
              // marker is the whole output, and execution then continues through the region's own result, so a
              // verified run is a NORMAL run and the verdict it produces is still the engine's.
              setupVerified_ = true;
              verifyingSetup_ = true;
              setupBase_ = mem_.objectCount();
              setupStartSteps_ = res_.steps;
              capturingSetup_ = true;
              setupWrites_.clear();
              mem_.setWriteLog(&setupWrites_);
              setupRegsBefore_.clear();
              for (auto &kv : top().regs) setupRegsBefore_.insert(kv.first);
              break;
            }
            if (c->state == SetupCache::State::Valid) {
              Frame &f = top();
              if (f.fn != c->fn || frames_.size() != c->frameDepth) {
                c->state = SetupCache::State::Refused;
                c->refusal = "the region was entered from a different frame than the one that produced it";
                break;
              }
              const auto tRestore = std::chrono::steady_clock::now();
              if (!mem_.restoreSnapshot(c->snap)) {
                c->state = SetupCache::State::Refused;
                c->refusal = "the memory snapshot no longer matches this run's object numbering";
                break;
              }
              for (auto &kv : c->regs) f.regs.insert_or_assign(kv.first, Slot{kv.second.a, kv.second.b});
              inSetupRegion_ = false;  // execution resumes PAST the end marker, which it will never reach
              d_.setSetupRegion(false);
              res_.secSetupRestore +=
                  std::chrono::duration<double>(std::chrono::steady_clock::now() - tRestore).count();
              f.blk = c->resumeBlk;
              f.ip = c->resumeIp;
              ++c->skips;
              if (getenv("HLIR_DEBUG_SETUP"))
                fprintf(stderr, "[setup] restored: base=%zu tail=%zu objs_now=%zu regs=%zu\n", c->snap.base,
                        c->snap.tail.size(), mem_.objectCount(), c->regs.size());
              break;
            }
            setupBase_ = mem_.objectCount();
            setupStartSteps_ = res_.steps;
            capturingSetup_ = true;
            setupWrites_.clear();
            mem_.setWriteLog(&setupWrites_);
            c->fn = top().fn;
            c->frameDepth = frames_.size();
            setupRegsBefore_.clear();
            for (auto &kv : top().regs) setupRegsBefore_.insert(kv.first);
            break;
          }
          if (ev->s == "hlir.setup.end") {
            inSetupRegion_ = false;
            d_.setSetupRegion(false);
            mem_.setWriteLog(nullptr);
            auto *c = setupCache();
            const bool wasCapturing = capturingSetup_;
            capturingSetup_ = false;
            if (c && verifyingSetup_) {
              verifyingSetup_ = false;
              Memory<D> &mm = mem_;
              auto fresh = mm.snapshotSince(setupBase_, &setupWrites_);
              auto diffs = mm.diffSnapshots(c->snap, fresh);
              Frame &f = top();
              std::vector<std::pair<const Value *, typename SetupState<D>::Reg>> freshRegs;
              for (auto &kv : f.regs) {
                if (setupRegsBefore_.count(kv.first)) continue;
                freshRegs.push_back({kv.first, typename SetupState<D>::Reg{kv.second.a, kv.second.b}});
              }
              // Matched by KEY, not by position: the frame's register map is unordered, so comparing two
              // iterations index by index would report differences that are only an iteration order.
              std::unordered_map<const Value *, typename SetupState<D>::Reg> freshBy;
              for (auto &kv : freshRegs) freshBy.emplace(kv.first, kv.second);
              if (freshRegs.size() != c->regs.size())
                diffs.push_back("the region left " + std::to_string(c->regs.size()) + " new register(s) when it " +
                                "was captured and " + std::to_string(freshRegs.size()) + " when it ran again");
              for (auto &kv : c->regs) {
                auto it = freshBy.find(kv.first);
                if (it == freshBy.end())
                  diffs.push_back("register %" + kv.first->name + " exists only in the cached run");
                else if (!D::same(kv.second.a, it->second.a) || !D::same(kv.second.b, it->second.b))
                  diffs.push_back("register %" + kv.first->name + " differs");
              }
              fprintf(stderr, "[setup-verify] %zu difference(s) between the restored state and a re-run\n",
                      diffs.size());
              for (auto &dmsg : diffs) fprintf(stderr, "[setup-verify]   %s\n", dmsg.c_str());
              break;
            }
            if (!c || !wasCapturing) break;
            Frame &f = top();
            auto refuse = [&](std::string why) {
              c->state = SetupCache::State::Refused;
              c->refusal = std::move(why);
              c->regs.clear();
              c->snap = {};
            };
            if (f.fn != c->fn || frames_.size() != c->frameDepth)
              { refuse("the two markers are not in the same call of the same function"); break; }
            c->snap = mem_.snapshotSince(setupBase_, &setupWrites_);
            if (!c->snap.valid) { refuse("the memory snapshot could not be taken"); break; }
            c->objects = static_cast<unsigned>(c->snap.tail.size());
            c->symbolicCells = Memory<D>::symbolicBytesIn(c->snap);
            c->capturedOps = res_.steps - setupStartSteps_;
            if ((c->symbolicCells || c->symbolicRegs) && getenv("HLIR_DEBUG_SETUP")) {
              for (auto &w : mem_.symbolicWhereIn(c->snap)) fprintf(stderr, "[setup] symbolic cell: %s\n", w.c_str());
              for (auto &kv : f.regs) {
                if (setupRegsBefore_.count(kv.first)) continue;
                if (D::isSymbolicVal(kv.second.a) || D::isSymbolicVal(kv.second.b))
                  fprintf(stderr, "[setup] symbolic register: %s\n", kv.first->name.c_str());
              }
            }
            // A region that produced symbolic data would otherwise NOT be replayable: the restored cell keeps the
            // concrete side this run chose while the solver still believes it can choose that variable, so a later
            // flip of it would move the model and not the memory -- the run would explore nothing and say it had.
            // Freezing those values to what this run computed removes the disagreement, at the price of not
            // exploring them, which is exactly what declaring the region asked for. What cannot be frozen refuses.
            c->regs.clear();
            c->symbolicRegs = 0;
            bool frozenOk = true;
            for (auto &kv : f.regs) {
              if (setupRegsBefore_.count(kv.first)) continue;  // the entry's own inputs: per-run, never restored
              Val ra = kv.second.a, rb = kv.second.b;
              for (Val *v : {&ra, &rb}) {
                if (!D::isSymbolicVal(*v)) continue;
                ++c->symbolicRegs;
                auto fv = d_.freezeVal(*v);
                if (!fv) { frozenOk = false; break; }
                *v = *fv;
              }
              if (!frozenOk) break;
              c->regs.push_back({kv.first, typename SetupState<D>::Reg{ra, rb}});
            }
            unsigned frozenCells = 0;
            if (frozenOk) frozenOk = mem_.freezeSnapshot(c->snap, frozenCells);
            if (!frozenOk) {
              refuse("the region left values that cannot be frozen -- attacker-controlled data, or an object "
                     "whose bytes are not enumerable (" + std::to_string(c->symbolicCells) +
                     " symbolic byte(s), " + std::to_string(c->symbolicRegs) + " symbolic register(s))");
              break;
            }
            c->resumeBlk = f.blk;
            c->resumeIp = f.ip;
            c->state = SetupCache::State::Valid;
            if (getenv("HLIR_DEBUG_SETUP")) {
              fprintf(stderr, "[setup] captured: base=%zu tail=%zu pre_written=%zu regs=%zu\n", c->snap.base,
                      c->snap.tail.size(), c->snap.preGlobals.size(), c->regs.size());
              unsigned shown = 0;
              for (auto &oo : c->snap.tail) {
                if (shown++ >= 8) break;
                fprintf(stderr, "[setup]   obj id=%u kind=%d cells=%zu arr=%d\n", oo.id, (int)oo.kind,
                        oo.cells.size(), (int)oo.arr);
              }
            }
            break;
          }
          if (ev->s == "hlir.prologue.end") {
            if (capturePrologue_) {
              if (auto *c = prologueCache()) {
                c->snap = mem_.snapshotSince(prologueBase_);
                c->valid = c->snap.valid;
              }
            }
            skipPrologue_ = false;
            capturePrologue_ = false;
            break;
          }
        }
        std::string text;
        if (const Attr *e = op.attr("event")) text = e->s;
        for (auto *v : o) text += " " + d_.str(get(v), isBoolVal(v));
        event(TraceEvent::Observable, top().fn->name, text, op.loc);
        break;
      }

      case Opc::CheckDiv: case Opc::CheckShift: case Opc::CheckSAddOvf: case Opc::CheckSSubOvf: case Opc::CheckSMulOvf:
      case Opc::CheckSNegOvf: case Opc::CheckNull: case Opc::CheckUaf: case Opc::CheckOob: case Opc::CheckPtrArith:
      case Opc::CheckFree: case Opc::CheckUninit: case Opc::CheckAlign: case Opc::CheckConstWrite: case Opc::CheckPtrCmp:
      case Opc::CheckFieldOob: {
        CheckMode mode = modeFor(op);
        if (mode == CheckMode::Ignore) break;
        std::vector<UBViolation<D>> vs;
        std::vector<Val> ints;
        std::vector<Ptr> ptrs;
        for (auto *a : o) {
          if (a->ty->isPtr()) ptrs.push_back(getP(a));
          else ints.push_back(get(a));
        }
        if (!ubViolations(d_, op, ints, vs) && !mem_.violations(op, ptrs, ints, vs)) { unsupported(op, "check not implemented"); return; }
        if (checkMemFailed(op)) return;
        if constexpr (D::kTaint) {
          // An attacker-controlled value used as a memory index: core.check.ptr_arith carries the (scaled) index as
          // its only integer operand and runs at every bounds-checked indexed access, before any fault. Warn unless a
          // constant upper bound is in force on this path (indexWarn records that as a solver query). Emitted here
          // rather than at core.ptr_add because the arithmetic check precedes the add and may itself stop the run.
          if (op.opc == Opc::CheckPtrArith && mode == CheckMode::Report && ints.size() == 1 && d_.isAttackerControlled(ints[0]))
            res_.taintReach.memoryIndex = true;
          if (op.opc == Opc::CheckPtrArith && mode == CheckMode::Report && ints.size() == 1 && d_.isAttackerControlled(ints[0]) && warnedIndex_.insert(&op).second)
            d_.indexWarn(ints[0], [&] { return ubFinding(UBKind::TaintedIndex, op); });
        }
        if constexpr (D::kTaint) {
          // Diagnostic (HLIR_DEBUG_CHECKTAINT=<line>): for every memory check at that source line, which of the
          // condition's inputs still carries taint. A check is only ever handed to the solver when its CONDITION
          // is tainted (TaintDomain::violated), so when a defect site is reported as decided-concretely this says
          // which operand lost it.
          static const int wantLine = [] { const char *e = getenv("HLIR_DEBUG_CHECKTAINT"); return e ? atoi(e) : -1; }();
          if (wantLine >= 0 && op.loc.line == static_cast<unsigned>(wantLine)) {
            std::string pd, idd;
            for (auto &pp : ptrs) { pd += std::to_string((int)D::isSymbolicVal(pp.off)); pd += "/"; pd += std::to_string((int)D::isSymbolicVal(pp.obj)); pd += " "; }
            for (auto &ii : ints) { idd += std::to_string((int)D::isSymbolicVal(ii)); idd += " "; }
            for (auto &v : vs)
              fprintf(stderr, "[chk] %s:%u %-18s cond=%d ptrs[off/obj]= %s ints= %s\n",
                      op.loc.file.c_str(), op.loc.line, ubKindName(v.kind), (int)D::isSymbolicVal(v.cond),
                      pd.c_str(), idd.c_str());
          }
        }
        for (auto &v : vs) {
          if (mode == CheckMode::Assume) {
            if (!d_.assume(d_.not_(v.cond))) { stop(RunStatus::Infeasible, std::string("assumed absent: ") + ubKindName(v.kind), &op); return; }
          } else {
            // How this check was settled (DESIGN.md §22.369). Counted here, where both the kind and whether the
            // condition is symbolic are in hand.
            CheckStat &cs = res_.checks[static_cast<int>(v.kind)];
            ++cs.reached;
            const bool sym = D::isSymbolicVal(v.cond);
            if (sym) ++cs.queried; else ++cs.decidedConcretely;
            if (fr.fn) {  // same settlement, attributed to the function (RunResult::checksByFn)
              CheckStat &fc = res_.checksByFn[fr.fn];
              ++fc.reached;
              if (sym) ++fc.queried; else ++fc.decidedConcretely;
            }
            // Only computed when something actually violated: walking the frames on every check would cost on the
            // hot path, and a violation is rare.
            bool prol = false, cmpOnly = false;
            if (d_.violated(v.cond, [&] {
                  Finding f = ubFinding(v.kind, op);
                  f.frontierOnly = d_.onlyFrontier(v.cond);
                  f.cmpOnlyPtr = cmpOnly = (v.kind == UBKind::PtrArithOob && ptrArithCompareOnly(op));
                  f.inPrologue = prol = inPrologue();
                  return f;
                })) {
              // A UB inside the project initialiser is recorded and the run CONTINUES. Stopping here is what made
              // the feature unusable on real kernel code: one deterministic `ptr_arith_oob` in `snd_info_register`
              // (the empty-list `container_of` in `list_for_each_entry`, a benign idiom) halted the first run of
              // every one of sound/core's 87 entries, so no entry was analysed at all (DESIGN.md §22.368, round
              // 49b). Continuing past real UB is a deliberate choice, named in the report: the alternative is
              // analysing nothing. It only applies to init code the entry's attacker does not drive.
              // A COMPARE-ONLY out-of-range pointer is recorded and the run CONTINUES, for the same reason
              // the prologue case does and with a stronger argument. §22.390 proved the pointer is never
              // dereferenced -- every use is a comparison, a difference or another bounds check -- so letting
              // execution go on cannot corrupt the memory state; only the pointer's VALUE travels, and it
              // travels into comparisons that are modelled exactly.
              //
              // Stopping made the whole tcpdump CVE family unreachable (DESIGN.md §22.407). Every protocol
              // printer opens with `const u_char *ep = cp + len;` where `len` comes from the packet header and
              // may exceed the capture; the run died on that line, so no printer could be explored past its
              // first statement and the defects the corpus is aiming at sat behind it. The downgrade added in
              // §22.390 only changed how the finding was REPORTED -- the halt was still taken.
              // `cmpOnly` and `prol` above are side effects of BUILDING the Finding, and a domain is free not to
              // build one: ConcreteDomain::violated ignores the callback entirely (it only needs the bool). So on
              // a concrete run -- which is what REPLAY is -- `cmpOnly` stayed false and the run halted on exactly
              // the compare-only pointer that §22.407 established must be walked past. The halt was invisible,
              // because it only affected confirmation: tcpdump CVE-2017-13020's `oob_read` at `print-vtp.c:246`
              // was found, queried SAT and witnessed, and then its replay died two lines earlier on
              // `while (tptr < (pptr+length))` and came back `replay_different_ub`. Recompute the property here,
              // where the decision is actually made, and only on the rare path where something violated.
              if (!cmpOnly && v.kind == UBKind::PtrArithOob) cmpOnly = ptrArithCompareOnly(op);
              // ANY out-of-range pointer ARITHMETIC is recorded and the run continues -- not only the
              // compare-only ones §22.390 could prove (ENGINE_LIMITATIONS.md §7.12).
              //
              // Halting here is detection in the wrong place. `p = q + n` by itself corrupts nothing: the
              // offset is modelled exactly, so the state after it is exact. If that pointer is then
              // DEREFERENCED, `core.check.oob` fires at the dereference with the right site and the right kind,
              // and that halt still happens. If it is never dereferenced, halting bought nothing and cost
              // everything after it.
              //
              // What it cost, measured three times independently before this was changed:
              //   - tcpdump (§22.407): every printer opens with `ep = cp + len` from the packet header; the run
              //     died on that line and the whole CVE family sat behind it. §22.390's compare-only downgrade
              //     fixed the REPORTING and left the halt.
              //   - Redis ziplist (§22.207) / libxml2 (§22.209) / the CVE-class table at §23591: the fix's OWN
              //     new bounds check is `p + len > end`, so BOTH trees reported ptr_arith_oob and the
              //     differential went flat; under --lenient-ptr-arith the same site reported the real
              //     `oob_write`. The strict check pre-empted the better finding and named the wrong kind.
              //   - LZ4 (§7.12): `match = op - offset` is dereferenced on one branch and only compared on
              //     another, so compare-only is false for the VALUE and the halt was taken. That cut the entire
              //     external-dictionary branch: LZ4_copyExtDictMatch was never entered at any budget, and
              //     branch coverage sat at 47% instead of 62%.
              //
              // The finding is NOT lost: TaintDomain::violated pushes it before this decision is reached, and
              // the site is added to `ubContinued` so the report says execution went on. --lenient-ptr-arith
              // keeps its own meaning: it does not emit the check at all, so it also saves the solver queries.
              if (v.kind == UBKind::PtrArithOob) cmpOnly = true;
              // An indeterminate value that nothing reads (see uninitValueDead): reported, not fatal.
              if (v.kind == UBKind::UninitRead && uninitValueDead(op)) cmpOnly = true;
              // The caller named this kind as non-fatal for this target (RunConfig::ubContinue).
              if (cfg_.ubContinue.count(v.kind)) cmpOnly = true;
              if (prol || cmpOnly || inPrologue()) {
                res_.ubContinued.insert(std::string(ubKindName(v.kind)) + "@" + op.loc.file + ":" +
                                        std::to_string(op.loc.line));
                continue;
              }
              reportUB(v.kind, op);
              return;
            }
          }
        }
        break;
      }

      // ---- memory and pointers
      case Opc::Alloca: {
        Val size = d_.constant(llvm::APInt(mem_.ptrWidth(), static_cast<uint64_t>(op.intAttr("size"))));
        Ptr p = mem_.alloc(ObjKind::Stack, size, static_cast<uint64_t>(op.intAttr("align", 1)), op.hasAttr("const"), false);
        top().allocas.push_back(mem_.lastId());
        if (cfg_.detectNonTermination && watch_) watch_->transientObjs.insert(mem_.lastId());
        setP(op.result.get(), p);
        break;
      }
      case Opc::HeapAlloc: {
        if (!o.empty() && d_.isAttackerControlled(get(o[0]))) res_.taintReach.allocSize = true;
        const Attr *kindAttr = op.attr("kind"), *content = op.attr("content");
        bool param = kindAttr && kindAttr->s == "param";  // an entry-parameter object (harness): not freeable, never fails
        bool owned = param && op.hasAttr("owned");  // a parameter object the callee owns: an ordinary (freeable) heap object that cannot fail
        Ptr p = mem_.alloc(param && !owned ? ObjKind::Param : ObjKind::Heap, get(o[0]), static_cast<uint64_t>(op.intAttr("align", 16)), false,
                           content && content->s == "zero");
        if (const Attr *nm = op.attr("name")) mem_.nameLastObject(nm->s);  // the spec's own path, for the target set
        if (content && content->s == "input") mem_.markInputContent();
        if (content && content->s == "unknown") mem_.markUnknownContent();
        if (op.hasAttr("externally_mutable")) mem_.markExternallyMutable();
        const Attr *f = op.attr("fail");
        if (!param && !(f && f->s == "never")) {
          // Inside a declared setup region the allocation SUCCEEDS (DESIGN.md §22.440). "Can this malloc fail?"
          // is a real question about the program, and it is the wrong question to ask of code the harness has
          // just said is setup: every allocation there forks a path into an initialiser's cleanup handler, which
          // is where libxml2's schema parse spends a large part of the search and where the `null_deref` in
          // xmlSchemaCleanupTypesInternal came from. The choice is DECLARED (it is counted and reported), which
          // is the difference between an assumption and an omission.
          if (inSetupRegion_ || cfg_.forceAllocSuccess) ++res_.setupAllocsForced;
          else {
            Val fail = d_.nondet(env_, op, 1);
            noteNondet(op, "whether this allocation failed");
            p.obj = d_.select(fail, mem_.nullPtr().obj, p.obj);
          }
        }
        setP(op.result.get(), p);
        break;
      }
      case Opc::GlobalAddr:
        setP(op.result.get(), mem_.global(op.sym, static_cast<uint64_t>(op.intAttr("size", 8)), op.hasAttr("const")));
        // G2 (DESIGN.md §22.374). Done HERE and not in a sweep at the entry marker, because globals are created
        // lazily at their first use: at the marker the object does not exist yet. By this point the frontend has
        // already emitted the `@__hlir_init.G` call that replays the static initialiser, so `progWritten` still
        // distinguishes "the module set this" from "this is what it was born with" -- which is the whole question.
        // NOT inside `@__hlir_init.G` itself: the first global_addr after the entry marker is the one the static
        // initialiser uses to WRITE the initial value, and promoting there is undone a moment later by that write.
        if (entryBegun_ && cfg_.promoteGlobals && !isStaticInit(*top().fn) && promoted_.insert(op.sym).second) {
          auto pit = cfg_.promoteGlobals->find(op.sym);
          if (pit != cfg_.promoteGlobals->end() &&
              mem_.promoteUnwrittenGlobal(op.sym, pit->second,
                                          [&](const std::string &n) { return d_.harnessInput(env_, "g2." + n, 8); }))
            ++res_.globalsPromoted;
        }
        break;
      case Opc::FuncAddr:  // a function's address is a distinct 1-byte const object: comparable, never dereferenced
        setP(op.result.get(), mem_.global("fn:" + op.sym, 1, true));
        break;
      case Opc::Free: case Opc::LifetimeEnd: mem_.kill(getP(o[0])); break;
      case Opc::Load: {
        const Type *t = op.resultType();
        Ptr p = getP(o[0]);
        if (cfg_.detectNonTermination && watch_) {
          auto id = d_.constValue(p.obj), off = d_.constValue(p.off);
          if (id && off) loadAddr_[op.result.get()] = {id->getZExtValue(), off->getZExtValue()};
          else watch_->unknownDep = true;  // a symbolic address in a concrete run: be conservative
        }
        if (cfg_.recordReads) noteRead(p, accessBytes(t));
        if (op.hasAttr("volatile")) event(TraceEvent::Observable, top().fn->name, "volatile load", op.loc);
        // An integer read out of an object materialised past the synthesis frontier: nothing ever wrote this
        // field, so its value is the harness's invention -- but the program may have STATED what it can be, in its
        // own assertion macros (`snd_BUG_ON(plugin->src_width <= 0)`, harvested as fieldAsserts, §22.358). Those
        // become `where:` preconditions on the objects the InitPlan names, and a frontier object is not one of
        // them, so until now the invariant was collected and then thrown away (DESIGN.md §22.365). Assume it here
        // instead, once per field. It is a NARROWING like every other `where:`, and it is named by the same
        // `synthesis_frontier` assumption that names the frontier itself.
        if (t->isPtr()) {
          const Attr *pe = op.attr("pointee");
          setP(op.result.get(), mem_.loadPtr(p, pe ? pe->s : std::string()));
        }
        else if (mem_.mayBeExternallyMutable(p)) {
          // Externally-mutable memory (declared via spec, e.g. shared memory / mmap'd registers): a real second
          // actor can change the bytes between two reads with no intervening store, so this load must not hit the
          // ordinary cells cache (that would make two reads of the same offset collapse onto one symbolic value and
          // hide a real TOCTOU window). Each load gets its own fresh, independently-tainted input instead of a
          // cached byte -- D::input(), not D::fresh() (TaintDomain::fresh() returns an untainted constant 0, which
          // would make this branch invisible to taint/relation checks). Pointer-typed loads are excluded above
          // (constructing a legal obj id for an externally-mutable pointer read is out of scope for this MVP).
          // the "in." prefix matters, not just as a naming convention: Taint.cpp's replay path only captures
          // variables whose name starts with "in." into the replay environment (see SymFinding::inputs /
          // SeqEnv::input) -- without it, a finding built on this value would solve correctly but never replay
          // (the concrete replay run would see the name as unseeded and default to 0, "not reproduced").
          Val raw = d_.input(env_, "in.extmut." + std::to_string(++extMutSeq_), 8 * accessBytes(t));
          if (t->isBool()) set(op.result.get(), d_.icmp(Pred::Ne, raw, d_.zero(8 * accessBytes(t))));
          else set(op.result.get(), d_.trunc(raw, t->width()));
        } else {
          Val raw = mem_.load(p, accessBytes(t));
          if (t->isBool()) set(op.result.get(), d_.icmp(Pred::Ne, raw, d_.zero(8)));
          else set(op.result.get(), d_.trunc(raw, t->width()));
        }
        // After the value exists, never before: this reads op.result.
        if (!t->isPtr() && cfg_.fieldBounds && !cfg_.fieldBounds->empty()) applyFrontierBound(op, p, t);
        checkMemFailed(op);
        break;
      }
      case Opc::Store: {
        const Type *t = o[0]->ty;
        Ptr p = getP(o[1]);
        if (op.hasAttr("volatile")) event(TraceEvent::Observable, top().fn->name, "volatile store", op.loc);
        d_.noteStore(get(o[0]));
        if (t->isPtr()) {
          if (cfg_.detectNonTermination && watch_) recordWrite(p, mem_.ptrWidth() / 8);
          mem_.storePtr(p, getP(o[0]));
        } else {
          unsigned bytes = accessBytes(t);
          if (cfg_.detectNonTermination && watch_) recordWrite(p, bytes);
          mem_.store(p, d_.zext(get(o[0]), 8 * bytes), bytes);
        }
        checkMemFailed(op);
        break;
      }
      case Opc::PtrAdd: {
        Ptr p = getP(o[0]);
        p.off = d_.add(p.off, get(o[1]));
        setP(op.result.get(), p);
        break;
      }
      case Opc::PtrDiff: set(op.result.get(), d_.sub(getP(o[0]).off, getP(o[1]).off)); break;
      case Opc::PtrCmp: {
        Pred pr;
        predFromString(op.pred, pr);
        Ptr a = getP(o[0]), b = getP(o[1]);
        if (pr == Pred::Eq) set(op.result.get(), d_.and_(d_.icmp(Pred::Eq, a.obj, b.obj), d_.icmp(Pred::Eq, a.off, b.off)));
        else if (pr == Pred::Ne) set(op.result.get(), d_.not_(d_.and_(d_.icmp(Pred::Eq, a.obj, b.obj), d_.icmp(Pred::Eq, a.off, b.off))));
        else set(op.result.get(), d_.icmp(pr, a.off, b.off));  // cross-object ordering is UB, reported by core.check.ptr_cmp
        break;
      }
      case Opc::IsNull: set(op.result.get(), mem_.isNull(getP(o[0]))); break;
      case Opc::ObjSize: set(op.result.get(), mem_.sizeOf(getP(o[0]))); break;
      case Opc::ObjAlive: set(op.result.get(), mem_.aliveOf(getP(o[0]))); break;
      case Opc::MemCpy: case Opc::MemMove:
        if (cfg_.detectNonTermination && watch_) watch_->unknownDep = true;
        mem_.copy(getP(o[0]), getP(o[1]), get(o[2])); checkMemFailed(op); break;
      case Opc::MemSet:
        if (cfg_.detectNonTermination && watch_) watch_->unknownDep = true;
        mem_.set(getP(o[0]), get(o[1]), get(o[2])); checkMemFailed(op); break;
      case Opc::IntToPtr: {
        // An integer has no provenance: the pointer denotes no object (obj 0), whatever its value, except that a value
        // produced by core.ptr_to_int (address = id << 32 | offset, see below) goes back to its object when that exists.
        unsigned pw = mem_.ptrWidth(), w = d_.width(get(o[0]));
        Val v = get(o[0]);
        if (pw == 64) {
          auto c = d_.constValue(v);
          if (c && c->getActiveBits() > 32 && mem_.hasObject(static_cast<uint32_t>(c->getZExtValue() >> 32))) {
            uint64_t a = c->getZExtValue();
            setP(op.result.get(), Ptr{d_.constant(llvm::APInt(32, a >> 32)), d_.constant(llvm::APInt(pw, a & 0xffffffffu))});
            break;
          }
        }
        setP(op.result.get(), Ptr{mem_.nullPtr().obj, w >= pw ? d_.trunc(v, pw) : d_.zext(v, pw)});
        break;
      }
      case Opc::PtrToInt: {
        // Objects have no real address here. The integer of an object pointer is `id << 32 | offset`: unique per object,
        // every object 4 GiB aligned (so alignment masks and same-object differences/orderings behave), objects up to 4 GiB.
        // `p.obj` may itself be symbolic (an ite over a few candidate objects, e.g. a pointer merged across branches);
        // Memory::ptrToIntVal builds the same formula as an ite-chain over those candidates in that case.
        Ptr p = getP(o[0]);
        auto r = mem_.ptrToIntVal(p, op.resultType()->width());
        if (!r) { unsupported(op, "pointer-to-integer cast of an object pointer needs a 64-bit pointer width"); return; }
        set(op.result.get(), *r);
        break;
      }

      default:
        unsupported(op, "not implemented by the integer-only engine (memory and pointer ops arrive in P4)");
        break;
    }
  }

  D &d_;
  const Module &mod_;
  Env &env_;
  const RunConfig &cfg_;
  std::vector<Frame> frames_;
  std::map<std::string, unsigned> modelCalls_;  // call instances per modelled function (names the inputs a call introduces)
  RunResult res_;
  std::optional<Val> retval_;
  std::optional<Slot> retslot_;
  Memory<D> mem_;
  uint64_t extMutSeq_ = 0;  // Opc::Load: names successive externally-mutable reads so each gets its own fresh input
  bool done_ = false;
  std::unordered_set<const Block *> cov_;  // RunConfig::coverage
  std::set<std::pair<const Op *, bool>> branchCov_;  // RunConfig::coverage: (cond_br op, direction taken)
  unsigned initDepth_ = 0;                           // frames of `@__hlir_init.*` currently on the stack
  std::set<const Op *> warnedLoop_, warnedIndex_;    // kTaint: DoS warnings already raised this run (one per site)
  std::set<std::string> boundedFields_;             // see applyFrontierBound
};

}  // namespace hlir

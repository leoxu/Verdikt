// z3 linked directly via its C API (libz3.so), as an alternative backend to the z3 subprocess (Z3Process.cpp).
// Third-party specifics (Z3_* calls, its C API's reference-counting rules) stay in this file; nothing here leaks
// through smt::Solver.
//
// Stage 1 scope (docs/DESIGN.md has the full writeup): a simple, direct mapper plus one Z3_solver per session.
// Z3Process's adaptive assume/push query-strategy switch and its (reset)+replay session machinery are
// process-boundary/text-protocol workarounds and are deliberately NOT ported here; if real workloads show this
// backend needs something similar, that is a later-stage decision made from data, not assumed up front.
//
// VERSION NOTE -- read before trusting any cross-backend comparison. This file links against whatever libz3.so
// CMake finds (find_library/find_path for libz3-dev). On the machine this was written on that is libz3-dev/libz3-4
// 4.8.12 (/usr/lib/x86_64-linux-gnu/libz3.so, /usr/include/z3.h). Z3Process (lib/smt/Z3Process.cpp) defaults to
// running whatever `z3` resolves to on $PATH, which on that same machine is a *different* version (a pip-installed
// z3-solver, Z3 5.1.0). There is no 4.8.12 `z3` CLI executable installed there: the apt `libz3-dev`/`libz3-4`
// packages ship only the library + headers, not a matching `z3` binary, and apt's `z3` package (which would supply
// one) is not installed (installing it is a system-level change outside this task's scope). So on that machine the
// two backends cannot be run at byte-identical Z3 versions, and any conformance test between them is comparing
// 4.8.12 (library, this file) against whatever `z3` is on $PATH for Z3Process -- this is a real, known environment
// limitation, not a hidden assumption. name() below always reports Z3Native's actual linked version via
// Z3_get_full_version() so this stays visible to anyone using the two backends together; Z3Process::name() stays
// "z3-process" (it does not know its own subprocess's version without parsing `z3 --version`, which is out of scope
// here). A disagreement between the two backends must first be checked against "is this just a version difference"
// before being treated as a bug in either mapper.
#ifdef HLIR_HAVE_Z3_NATIVE
#include <z3.h>

#include <stdexcept>
#include <unordered_map>

#include "hlir/smt/Solver.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringRef.h"

namespace hlir::smt {

namespace {

// Thrown by checkError()/noteMgr() when something goes wrong; caught at the Solver method boundary so one bad
// term/query turns into lastError()+Unknown instead of a crash or (worse) a wrong sat/unsat answer.
struct Z3ApiError {
  std::string msg;
};

std::string numeralString(const llvm::APInt &v) {
  llvm::SmallString<80> s;
  v.toStringUnsigned(s, 10);
  return std::string(s.str());
}

class Z3Native final : public Solver {
 public:
  explicit Z3Native(unsigned timeoutMs) : initTimeoutMs_(timeoutMs) {
    Z3_config cfg = Z3_mk_config();
    ctx_ = Z3_mk_context_rc(cfg);
    Z3_del_config(cfg);
    // No handler: Z3 records the error on the context (Z3_get_error_code) instead of invoking a default handler
    // that would abort the process. checkError() is called after every mk_*/solver_* call that can fail.
    Z3_set_error_handler(ctx_, nullptr);
    solver_ = mkQfAbvSolver();
    Z3_solver_inc_ref(ctx_, solver_);
    applyTimeout(initTimeoutMs_);
  }

  ~Z3Native() override {
    clearNamed();
    for (auto &kv : astById_) if (kv) Z3_dec_ref(ctx_, kv);
    Z3_solver_dec_ref(ctx_, solver_);
    Z3_del_context(ctx_);
  }

  void push() override {
    try { Z3_solver_push(ctx_, solver_); checkError(); } catch (Z3ApiError &e) { err_ = e.msg; }
  }
  void pop() override {
    try { Z3_solver_pop(ctx_, solver_, 1); checkError(); } catch (Z3ApiError &e) { err_ = e.msg; }
  }

  // Stage 1: a session owns its own Z3_solver (freshly made/torn down), not a (reset)+replay of one shared solver.
  // Term->Z3_ast caching stays (it is keyed off TermManager ids, is solver-independent, and ctx_ owns those asts).
  void beginSession() override {
    try {
      clearNamed();
      Z3_solver_dec_ref(ctx_, solver_);
      solver_ = mkQfAbvSolver();
      Z3_solver_inc_ref(ctx_, solver_);
      applyTimeout(initTimeoutMs_);
      checkError();
    } catch (Z3ApiError &e) { err_ = e.msg; }
  }
  void endSession() override { beginSession(); }  // leaves a clean, empty solver_ behind for the next user

  void assertTerm(TermRef t, const std::string &name) override {
    try {
      noteMgr(t);
      Z3_ast a = build(t);
      if (name.empty()) {
        Z3_solver_assert(ctx_, solver_, a);
      } else {
        Z3_ast p = Z3_mk_const(ctx_, Z3_mk_string_symbol(ctx_, name.c_str()), Z3_mk_bool_sort(ctx_));
        checkError();
        Z3_inc_ref(ctx_, p);
        named_[name] = p;
        Z3_solver_assert_and_track(ctx_, solver_, a, p);
      }
      checkError();
    } catch (Z3ApiError &e) { err_ = e.msg; }
  }

  SatResult check() override {
    try {
      ++checks_;
      Z3_lbool r = Z3_solver_check(ctx_, solver_);
      checkError();
      return fromLbool(r);
    } catch (Z3ApiError &e) { err_ = e.msg; return SatResult::Unknown; }
  }

  // Z3 natively supports assumption literals via check_assumptions: no push/pop scope needs to be opened, unlike
  // the base class default (and unlike Z3Process's two strategies -- see the file header).
  SatResult checkAssuming(const std::vector<TermRef> &terms) override {
    lastAssumPos_.clear();
    try {
      std::vector<Z3_ast> a;
      a.reserve(terms.size());
      for (size_t i = 0; i < terms.size(); ++i) {
        TermRef t = terms[i];
        if (t->isTrue()) continue;  // dropped here, so the core must map back through lastAssumPos_, not through `a`
        noteMgr(t);
        a.push_back(build(t));
        lastAssumPos_.push_back(i);
      }
      lastAssum_ = a;
      ++checks_;
      Z3_lbool r = Z3_solver_check_assumptions(ctx_, solver_, static_cast<unsigned>(a.size()), a.data());
      checkError();
      return fromLbool(r);
    } catch (Z3ApiError &e) { err_ = e.msg; return SatResult::Unknown; }
  }

  // Z3 returns the core as a subset of the assumption ASTs it was given. Terms are hash-consed within a context, so
  // the returned pointers ARE the ones that were passed and identity is the right way to find them again; a name
  // would have to be invented for an anonymous term and then parsed back out.
  std::vector<size_t> unsatCoreAssumptions() override {
    std::vector<size_t> res;
    if (lastAssum_.empty()) return res;
    try {
      std::unordered_map<Z3_ast, size_t> at;
      for (size_t i = 0; i < lastAssum_.size(); ++i) at.emplace(lastAssum_[i], lastAssumPos_[i]);
      Z3_ast_vector core = Z3_solver_get_unsat_core(ctx_, solver_);
      checkError();
      Z3_ast_vector_inc_ref(ctx_, core);
      unsigned n = Z3_ast_vector_size(ctx_, core);
      for (unsigned i = 0; i < n; ++i) {
        auto it = at.find(Z3_ast_vector_get(ctx_, core, i));
        if (it != at.end()) res.push_back(it->second);
      }
      Z3_ast_vector_dec_ref(ctx_, core);
      checkError();
    } catch (Z3ApiError &e) { err_ = e.msg; res.clear(); }
    std::sort(res.begin(), res.end());
    return res;
  }
  void endCheckAssuming() override {}  // no scope was opened above

  std::vector<llvm::APInt> values(const std::vector<TermRef> &vars) override {
    std::vector<llvm::APInt> res;
    for (auto *v : vars) res.emplace_back(v->sort.width, 0);
    if (vars.empty()) return res;
    try {
      if (!vars.empty()) noteMgr(vars.front());
      Z3_model m = Z3_solver_get_model(ctx_, solver_);
      checkError();
      if (!m) { err_ = "Z3Native::values(): no model (check() was not Sat)"; return res; }
      Z3_model_inc_ref(ctx_, m);
      for (size_t i = 0; i < vars.size(); ++i) {
        Z3_ast term = build(vars[i]);
        Z3_ast val = nullptr;
        bool ok = Z3_model_eval(ctx_, m, term, /*model_completion=*/true, &val);
        checkError();
        if (!ok || !val) { err_ = "Z3Native::values(): model_eval failed"; continue; }
        res[i] = llvm::APInt(vars[i]->sort.width, llvm::StringRef(Z3_get_numeral_string(ctx_, val)), 10);
        checkError();
      }
      Z3_model_dec_ref(ctx_, m);
    } catch (Z3ApiError &e) { err_ = e.msg; }
    return res;
  }

  std::vector<std::string> unsatCore() override {
    std::vector<std::string> res;
    try {
      Z3_ast_vector core = Z3_solver_get_unsat_core(ctx_, solver_);
      checkError();
      Z3_ast_vector_inc_ref(ctx_, core);
      unsigned n = Z3_ast_vector_size(ctx_, core);
      for (unsigned i = 0; i < n; ++i) {
        Z3_ast p = Z3_ast_vector_get(ctx_, core, i);
        Z3_symbol sym = Z3_get_decl_name(ctx_, Z3_get_app_decl(ctx_, Z3_to_app(ctx_, p)));
        res.push_back(Z3_get_symbol_string(ctx_, sym));
      }
      Z3_ast_vector_dec_ref(ctx_, core);
      checkError();
    } catch (Z3ApiError &e) { err_ = e.msg; }
    return res;
  }

  void setTimeoutMs(unsigned ms) override {
    try { applyTimeout(ms); checkError(); } catch (Z3ApiError &e) { err_ = e.msg; }
  }

  std::string name() const override { return std::string("z3-native (libz3 ") + Z3_get_full_version() + ")"; }
  std::string lastError() const override { return err_; }
  uint64_t checkCount() const override { return checks_; }

 private:
  static SatResult fromLbool(Z3_lbool r) {
    switch (r) {
      case Z3_L_TRUE: return SatResult::Sat;
      case Z3_L_FALSE: return SatResult::Unsat;
      default: return SatResult::Unknown;
    }
  }

  void checkError() {
    Z3_error_code ec = Z3_get_error_code(ctx_);
    if (ec != Z3_OK) throw Z3ApiError{std::string("z3: ") + Z3_get_error_msg(ctx_, ec)};
  }

  // Bug found in stage 3 (docs/DESIGN.md has the writeup): Z3_mk_solver(ctx_) builds a solver with the generic
  // "smt" tactic, which is valid for any logic but is not the specialized, complete-for-QF_ABV strategy Z3 picks
  // when the logic is named. Z3Process always sends `(set-logic QF_ABV)` before anything else (see its init());
  // Z3Native did not have an equivalent, so on real array+bitvector workloads (arrays, loops, deep terms -- not
  // triggered by the simpler formulas in conformance()) it would spuriously return Z3_L_UNDEF after burning the
  // full timeout on checks the generic tactic struggled with, where the QF_ABV-tuned tactic (and Z3Process, same
  // libz3 version, via the text protocol) answered conclusively and fast. Z3_mk_solver_for_logic() falls back to
  // Z3_mk_solver()'s behaviour if the logic name is unknown/unsupported, so this is strictly no worse even if a
  // future libz3 drops/renames the QF_ABV strategy.
  Z3_solver mkQfAbvSolver() { return Z3_mk_solver_for_logic(ctx_, Z3_mk_string_symbol(ctx_, "QF_ABV")); }

  void applyTimeout(unsigned ms) {
    Z3_params p = Z3_mk_params(ctx_);
    Z3_params_inc_ref(ctx_, p);
    Z3_params_set_uint(ctx_, p, Z3_mk_string_symbol(ctx_, "timeout"), ms ? ms : 4294967295u);
    Z3_solver_set_params(ctx_, solver_, p);
    Z3_params_dec_ref(ctx_, p);
  }

  void clearNamed() {
    for (auto &kv : named_) Z3_dec_ref(ctx_, kv.second);
    named_.clear();
  }

  // Stage 1 assumed one TermManager for the solver's whole lifetime and failed loudly (lastError()+Unknown) the
  // moment a different one showed up, reasoning that silently mixing term ids from two managers would be a
  // correctness bug. Stage 3's real-pipeline benchmark (docs/DESIGN.md has the writeup) showed that assumption was
  // wrong: Pipeline.cpp's scanEntry() reuses one Solver across several runs/paths of the same entry, and each run
  // builds its own TermManager (Term::id is "unique inside the owning TermManager", Term.h) -- so a single
  // Z3Native instance legitimately sees a sequence of different managers in normal operation, not just in a
  // misuse case. The old code threw on the SECOND manager and never recovered (curMgr_ was never reset), which
  // turned every subsequent query of that entry's scan into Unknown: wrong/missing verdicts, not merely a missed
  // optimisation, and the fewer solver_queries in the benchmark's "before" run (exploration gives up early once a
  // feasibility check comes back Unknown) is the same bug, not a separate one.
  //
  // Fix: (mgr, id) -- not id alone -- names a term (Term.h's own comment on Term::mgr says so). astById_ is keyed
  // by id alone, so it is only valid while curMgr_ is the term's manager; the moment a term from a different
  // manager is seen, every cached Z3_ast in it belongs to ids from the OLD manager and must be dropped before any
  // term from the new manager is looked up or built, or an unrelated term could alias a leftover id and silently
  // produce a wrong (not just slower) answer. Z3_solver state itself does not need special handling here: the
  // normal per-session Z3_mk_solver_for_logic() in beginSession()/endSession() already gives every session a
  // clean solver_, so the only state that crosses a manager switch is this cache.
  void noteMgr(TermRef t) {
    if (curMgr_ == t->mgr) return;
    clearAstCache();
    curMgr_ = t->mgr;
  }

  void clearAstCache() {
    for (auto &a : astById_) if (a) Z3_dec_ref(ctx_, a);
    astById_.clear();
  }

  Z3_sort sortOf(const Sort &s) {
    if (s.isBool) return Z3_mk_bool_sort(ctx_);
    if (s.isArray) return Z3_mk_array_sort(ctx_, Z3_mk_bv_sort(ctx_, s.idxWidth), Z3_mk_bv_sort(ctx_, s.width));
    return Z3_mk_bv_sort(ctx_, s.width);
  }

  bool haveAst(TermRef t) const { return t->id < astById_.size() && astById_[t->id] != nullptr; }
  Z3_ast getAst(TermRef t) const { return astById_[t->id]; }
  void setAst(TermRef t, Z3_ast a) {
    if (t->id >= astById_.size()) astById_.resize(t->id + 1, nullptr);
    Z3_inc_ref(ctx_, a);
    astById_[t->id] = a;
  }

  Z3_ast buildOne(TermRef t) {
    auto a = [&](size_t i) { return getAst(t->args[i]); };
    switch (t->kind) {
      case Kind::BoolConst: return t->value.getBoolValue() ? Z3_mk_true(ctx_) : Z3_mk_false(ctx_);
      case Kind::BvConst: return Z3_mk_numeral(ctx_, numeralString(t->value).c_str(), Z3_mk_bv_sort(ctx_, t->sort.width));
      case Kind::Var: return Z3_mk_const(ctx_, Z3_mk_string_symbol(ctx_, t->name.c_str()), sortOf(t->sort));
      case Kind::Not: return Z3_mk_not(ctx_, a(0));
      case Kind::And: { Z3_ast args[2] = {a(0), a(1)}; return Z3_mk_and(ctx_, 2, args); }
      case Kind::Or: { Z3_ast args[2] = {a(0), a(1)}; return Z3_mk_or(ctx_, 2, args); }
      case Kind::Ite: return Z3_mk_ite(ctx_, a(0), a(1), a(2));
      case Kind::Eq: return Z3_mk_eq(ctx_, a(0), a(1));
      case Kind::Ult: return Z3_mk_bvult(ctx_, a(0), a(1));
      case Kind::Ule: return Z3_mk_bvule(ctx_, a(0), a(1));
      case Kind::Slt: return Z3_mk_bvslt(ctx_, a(0), a(1));
      case Kind::Sle: return Z3_mk_bvsle(ctx_, a(0), a(1));
      case Kind::BvAdd: return Z3_mk_bvadd(ctx_, a(0), a(1));
      case Kind::BvSub: return Z3_mk_bvsub(ctx_, a(0), a(1));
      case Kind::BvMul: return Z3_mk_bvmul(ctx_, a(0), a(1));
      case Kind::BvUdiv: return Z3_mk_bvudiv(ctx_, a(0), a(1));
      case Kind::BvUrem: return Z3_mk_bvurem(ctx_, a(0), a(1));
      case Kind::BvSdiv: return Z3_mk_bvsdiv(ctx_, a(0), a(1));
      case Kind::BvSrem: return Z3_mk_bvsrem(ctx_, a(0), a(1));
      case Kind::BvAnd: return Z3_mk_bvand(ctx_, a(0), a(1));
      case Kind::BvOr: return Z3_mk_bvor(ctx_, a(0), a(1));
      case Kind::BvXor: return Z3_mk_bvxor(ctx_, a(0), a(1));
      case Kind::BvShl: return Z3_mk_bvshl(ctx_, a(0), a(1));
      case Kind::BvLshr: return Z3_mk_bvlshr(ctx_, a(0), a(1));
      case Kind::BvAshr: return Z3_mk_bvashr(ctx_, a(0), a(1));
      case Kind::BvNot: return Z3_mk_bvnot(ctx_, a(0));
      case Kind::BvNeg: return Z3_mk_bvneg(ctx_, a(0));
      // Term.h: "ZExt/SExt use `hi` as the target width" -- Z3_mk_{zero,sign}_ext wants the number of bits to add.
      case Kind::ZExt: return Z3_mk_zero_ext(ctx_, t->hi - t->args[0]->sort.width, a(0));
      case Kind::SExt: return Z3_mk_sign_ext(ctx_, t->hi - t->args[0]->sort.width, a(0));
      case Kind::Extract: return Z3_mk_extract(ctx_, t->hi, t->lo, a(0));
      case Kind::Concat: return Z3_mk_concat(ctx_, a(0), a(1));
      case Kind::Select: return Z3_mk_select(ctx_, a(0), a(1));
      case Kind::Store: return Z3_mk_store(ctx_, a(0), a(1), a(2));
      case Kind::ConstArray: return Z3_mk_const_array(ctx_, Z3_mk_bv_sort(ctx_, t->sort.idxWidth), a(0));
    }
    throw Z3ApiError{std::string("Z3Native: unhandled Kind ") + kindName(t->kind)};
  }

  // Iterative post-order DAG walk with memoization by Term::id, mirroring SmtLibEmitter::emit() (lib/smt/SmtLib.cpp)
  // and evalTerm() (lib/smt/Eval.cpp) -- the same structure, building Z3_ast instead of text or an llvm::APInt.
  Z3_ast build(TermRef root) {
    std::vector<TermRef> stack{root};
    while (!stack.empty()) {
      TermRef t = stack.back();
      if (haveAst(t)) { stack.pop_back(); continue; }
      bool ready = true;
      for (auto *c : t->args)
        if (!haveAst(c)) { stack.push_back(c); ready = false; }
      if (!ready) continue;
      stack.pop_back();
      Z3_ast r = buildOne(t);
      checkError();
      setAst(t, r);
    }
    return getAst(root);
  }

  Z3_context ctx_;
  Z3_solver solver_;
  std::vector<Z3_ast> astById_;              // Term::id -> Z3_ast, memoized across the object's lifetime
  std::unordered_map<std::string, Z3_ast> named_;  // assertion name -> tracking literal, reset per session
  uint32_t curMgr_ = 0;
  unsigned initTimeoutMs_ = 0;
  std::string err_;
  uint64_t checks_ = 0;
  std::vector<Z3_ast> lastAssum_;      // assumptions of the last checkAssuming, for unsatCoreAssumptions()
  std::vector<size_t> lastAssumPos_;   // ...and their positions in the vector the caller passed
};

}  // namespace

std::unique_ptr<Solver> makeZ3NativeSolver(unsigned timeoutMs) {
  return std::make_unique<Z3Native>(timeoutMs);
}

}  // namespace hlir::smt

#else  // !HLIR_HAVE_Z3_NATIVE

#include "hlir/smt/Solver.h"

namespace hlir::smt {
std::unique_ptr<Solver> makeZ3NativeSolver(unsigned /*timeoutMs*/) { return nullptr; }
}  // namespace hlir::smt

#endif

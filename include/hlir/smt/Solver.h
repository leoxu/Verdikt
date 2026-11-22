// STABLE. The solver abstraction used by the rest of the system. Implementations (a z3 subprocess, exhaustive
// enumeration for tiny problems, a future cvc5/bitwuzla backend) live in lib/smt and are chosen by factory functions;
// consumers depend only on this interface (docs/ARCHITECTURE.md §3, replaceability matrix).
#pragma once
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "hlir/smt/Term.h"

namespace hlir::smt {

enum class SatResult { Sat, Unsat, Unknown };
const char *satResultName(SatResult r);

class Solver {
 public:
  virtual ~Solver() = default;

  // Assertion stack. Everything asserted after push() is dropped by the matching pop().
  virtual void push() = 0;
  virtual void pop() = 0;
  // `t` must be Bool-sorted. A non-empty `name` makes the assertion trackable in unsatCore() (e.g. "init.len",
  // "pc.17", "ub.core.check.div@f:3"). Names must be unique among live assertions.
  virtual void assertTerm(TermRef t, const std::string &name = "") = 0;

  virtual SatResult check() = 0;

  // A session is a stretch of work with ONE TermManager during which the backend may keep state at the top level (see
  // checkAssuming). endSession() drops it again, so other users of the solver see a clean top level. Not nested.
  virtual void beginSession() {}
  virtual void endSession() {}

  // Satisfiability of the conjunction of `terms` (Bool-sorted) under the current stack. A backend that can keep terms asserted
  // across calls does (assumption literals: each distinct term is parsed and internalised once, learned clauses are reused);
  // the default pushes, asserts, checks and pops. A model is available for values() afterwards.
  virtual SatResult checkAssuming(const std::vector<TermRef> &terms) {
    push();
    for (auto *t : terms) assertTerm(t);
    SatResult r = check();
    // the model is read by the caller before the next call: leave the scope open until pop is requested
    pendingPop_ = true;
    return r;
  }
  // Ends a checkAssuming() (and the use of its model). Always call it after the model has been read.
  virtual void endCheckAssuming() { if (pendingPop_) { pop(); pendingPop_ = false; } }

  // After check() == Sat: values of the given bit-vector terms in the model (unconstrained parts get an arbitrary value).
  virtual std::vector<llvm::APInt> values(const std::vector<TermRef> &vars) = 0;
  // After check() == Unsat: names of a (not necessarily minimal) subset of the named assertions that is unsatisfiable.
  virtual std::vector<std::string> unsatCore() = 0;
  // After checkAssuming() == Unsat: the POSITIONS, in the vector that call was given, of a subset of those terms that is
  // already unsatisfiable. Names cannot carry this -- the terms are passed anonymously -- and positions are what the
  // caller can act on: constraint i of a cone is path condition i of a run, so a core names the branches to flip.
  // An empty result means "this backend does not report cores", never "the core is empty"; callers must treat it as
  // no information and fall back, since an unsat check with no core is still a correct unsat check.
  virtual std::vector<size_t> unsatCoreAssumptions() { return {}; }

  // Changes the per-check time limit (0 = unlimited) for subsequent check() calls. No-op for backends without one.
  virtual void setTimeoutMs(unsigned /*ms*/) {}

  virtual std::string name() const = 0;
  // Non-empty if the backend hit an error (bad output, process died); check() then returns Unknown.
  virtual std::string lastError() const { return {}; }
  virtual uint64_t checkCount() const = 0;

 protected:
  bool pendingPop_ = false;
};

// z3 as a child process (`<exe> -in`), speaking SMT-LIB2. Returns nullptr if the executable cannot be started.
// `timeoutMs` bounds each check-sat (0 = unlimited).
std::unique_ptr<Solver> makeZ3ProcessSolver(const std::string &exe = "z3", unsigned timeoutMs = 10000);

// z3 linked directly via its C API (libz3.so), bypassing the subprocess/SMT-LIB2 text protocol that
// makeZ3ProcessSolver() uses. NOT the default anywhere in the system (docs/DESIGN.md has the writeup): this exists
// alongside makeZ3ProcessSolver(), which stays the backend every existing caller uses. Returns nullptr if the build
// was not linked against libz3 (CMake did not find libz3-dev; guarded by HLIR_HAVE_Z3_NATIVE) -- callers must check
// for nullptr the same way they would for a missing z3 executable. `timeoutMs` bounds each check (0 = unlimited).
// Stage 1 implementation (lib/smt/Z3Native.cpp): a simple direct term->Z3_ast mapper, one Z3_solver per session, no
// adaptive query-strategy switching and no (reset)+replay -- those are specific to the subprocess text protocol.
// VERSION WARNING: this backend's Z3 version is whatever libz3.so CMake linked against, which can differ from
// whatever `z3` executable makeZ3ProcessSolver()'s caller passes (often just "z3" resolved from $PATH). name() on
// the returned Solver reports the exact linked version (Z3_get_full_version()); do not assume the two backends are
// running the same Z3 build without checking it.
std::unique_ptr<Solver> makeZ3NativeSolver(unsigned timeoutMs = 10000);

// Exhaustive enumeration over all variable assignments; answers Unknown when the variables in the live assertions
// total more than `maxBits` bits. A self-contained oracle for tests and a no-dependency fallback for tiny problems.
std::unique_ptr<Solver> makeEnumSolver(unsigned maxBits = 20);

// ---- SMT-LIB2 text (also usable on its own, e.g. `hlir-smt --emit`) ----
// Prints `(declare-fun ...)`/`(define-fun ...)` for everything `t` needs that is not yet in `declared`, then returns
// the SMT-LIB expression for `t`. `declared` holds term ids already emitted (so shared subterms are defined once).
struct SmtLibEmitter {
  std::vector<bool> emitted;  // indexed by Term::id
  std::vector<std::vector<uint32_t>> scopeLog;  // ids emitted per push level, for pop()
  SmtLibEmitter() { scopeLog.emplace_back(); }
  void push() { scopeLog.emplace_back(); }
  void pop();
  // Appends the needed declarations to `out` and returns the name/expression to use for `t`.
  std::string emit(TermRef t, std::string &out);
};
std::string bvLiteral(const llvm::APInt &v);  // #b... / #x...

}  // namespace hlir::smt

// `throw`/`try`/`catch`, including cross-function propagation (see IMPLEMENTATION_PLAN "跨函数异常传播"). A `throw`
// is resolved against every `try` enclosing it in the SAME function at lowering time (not at runtime — the thrown
// object's type is always the throw-expression's exact static type, never some more-derived runtime type, so no
// vptr needs to be read), innermost first, first matching `catch` in source order wins. No match in the throwing
// function itself: the exception is handed to its caller via two global slots (an object pointer and an RTTI
// marker) that every ordinary/virtual/`operator new`/`operator delete` call site checks right after the call —
// found a match there (now *at runtime*, since the callee's thrown type isn't known where it's caught), same
// `catch` dispatch; no match there either, hand it to THAT function's own caller, recursively. Only once it
// escapes every function on the call stack with nothing left to propagate to does it become this project's
// pre-existing "uncaught exception" modelling (`terminateProgram`, status `infeasible`, same as `abort()`) — at
// the harness/entry wrapper for a `hlir-scan`-style analysis (see IMPLEMENTATION_PLAN's real-project validation),
// which is not reachable from these tests' direct `Interpreter(mod).run(fn, ...)` calls (no entry/harness
// involved), so "fully uncaught, reaches `terminateProgram`" is not exercised by the tests in this file — see the
// real-code validation instead. What IS exercised here, with a bare function call as the "caller": that function
// handing the still-unhandled exception back out to the TEST HARNESS itself is an ordinary `return` with the
// exception state left set in the globals (unobserved by this file's direct calls) — not `infeasible` — exactly
// matching the new, more useful default: a function makes no judgement about whether ITS OWN caller will catch
// what it couldn't.
//
// Constructor/destructor base/member-initialiser chaining calls, lazily-initialised globals' init calls, a
// virtual dispatcher's call to the real overrider, and indirect calls do NOT get full local-catch matching (no
// `try` context to match against in most of those shapes anyway) — only the branchless safety net: an exception
// escaping one of those becomes the pre-existing `terminateProgram` outcome immediately, not propagated further.
struct MyError {
  int code;
  explicit MyError(int c) : code(c) {}
  virtual ~MyError() {}
};
struct FatalError : MyError {
  explicit FatalError(int c) : MyError(c) {}
};

// RUN: @t_catch_exact(-5) => -5
// RUN: @t_catch_exact(3) => 1
extern "C" int t_catch_exact(int x) {
  try {
    if (x < 0) throw MyError(x);
    return 1;
  } catch (MyError &e) {
    return e.code;
  }
}
// RUN: @t_catch_base(-5) => -50
extern "C" int t_catch_base(int x) {  // catching the base class catches a thrown derived object too
  try {
    if (x < 0) throw FatalError(x);
    return 1;
  } catch (MyError &e) {
    return e.code * 10;
  }
}
// RUN: @t_catch_by_value(-5) => -5
extern "C" int t_catch_by_value(int x) {  // `catch (T e)`, not by reference: still binds correctly
  try {
    if (x < 0) throw MyError(x);
    return 1;
  } catch (MyError e) {
    return e.code;
  }
}
// RUN: @t_catch_all(-5) => 999
extern "C" int t_catch_all(int x) {
  try {
    if (x < 0) throw MyError(x);
    return 1;
  } catch (...) {
    return 999;
  }
}
// RUN: @t_derived_does_not_catch_base() => 0
static int derived_does_not_catch_base() {  // `catch (Derived&)` does NOT match a thrown Base: propagates out
  try {
    throw MyError(1);
  } catch (FatalError &e) {
    return e.code;
  }
  return -1;  // unreachable from a normal path (only reached if, contrary to the test's point, the catch matched)
}
extern "C" int t_derived_does_not_catch_base() {
  // this function's own `catch` ALSO does not match `MyError` (same mismatch, one level up): cross-function
  // propagation correctly carries it THROUGH `derived_does_not_catch_base`'s frame without a local-looking match
  // along the way, and hands it to the test harness exactly like any other still-unhandled exception — i.e. to
  // code outside this file's model, which (not knowing the convention) just sees an ordinary `return 0` (the
  // callee's dummy early-return value; ordinary call-site-after-call code must never *use* a possibly-garbage
  // result without checking the in-flight-exception slot first — see IMPLEMENTATION_PLAN) rather than -1.
  try {
    return derived_does_not_catch_base();
  } catch (FatalError &e) {
    return e.code;
  }
}
// RUN: @t_single_level_propagation() => 5
static int callee_throws_uncaught(int x) {  // no local `try` at all: an unmatched `throw` always propagates
  if (x < 0) throw MyError(x);
  return 1;
}
extern "C" int t_single_level_propagation() {  // the user's "single-level" scenario: callee throws, caller catches
  try {
    return callee_throws_uncaught(-5);
  } catch (MyError &e) {
    return -e.code;
  }
}
// RUN: @t_multilevel_chain_a_b_c() => 42
static int c_throws() { throw MyError(42); }
static int b_no_try() { return c_throws(); }  // no `try` here: cleanly forwards whatever `c_throws` propagates
extern "C" int t_multilevel_chain_a_b_c() {  // the user's "a() calls b() calls c()" scenario: c throws, b has no
  try {                                       // try, a catches — the exception crosses b's frame untouched
    return b_no_try();
  } catch (MyError &e) {
    return e.code;
  }
}
static int g_b_dtor_log;
struct BLogger {
  ~BLogger() { g_b_dtor_log = 1; }
};
static int b_with_local_then_throws() {
  BLogger l;
  (void)l;
  return c_throws();  // b itself declares no `try`; its OWN local `l` must still be destroyed while propagating
}
// RUN: @t_multilevel_intermediate_dtor() => 1042
extern "C" int t_multilevel_intermediate_dtor() {  // the user's "intermediate frame destructors really run" scenario
  g_b_dtor_log = 0;
  try {
    return b_with_local_then_throws();
  } catch (MyError &e) {
    return g_b_dtor_log * 1000 + e.code;
  }
}
// RUN: @t_scalar_match() => 7
extern "C" int t_scalar_match() {  // non-class exception types work too, matched exactly
  try {
    throw 7;
  } catch (int n) {
    return n;
  }
}
// RUN: @t_nested_mismatch_propagates_out() => 107
extern "C" int t_nested_mismatch_propagates_out() {
  try {
    try {
      throw MyError(7);
    } catch (FatalError &) {  // does not match: propagates to the OUTER try, not swallowed here
      return -2;
    }
  } catch (MyError &e) {
    return e.code + 100;
  }
  return -1;
}
// RUN: @t_throw_from_handler_skips_siblings() => 55
extern "C" int t_throw_from_handler_skips_siblings() {
  // a throw from inside a catch handler is not caught by a sibling handler of the same try, only an outer one
  try {
    try {
      throw MyError(1);
    } catch (MyError &) {
      throw FatalError(55);
    } catch (FatalError &) {  // never reached for the re-throw above: sibling handlers don't catch each other
      return -3;
    }
  } catch (MyError &e) {
    return e.code;
  }
  return -1;
}
static int g_dtor_log;
struct Logger {
  ~Logger() { g_dtor_log = 1; }
};
// RUN: @t_unwind_runs_local_dtors() => 1005
extern "C" int t_unwind_runs_local_dtors() {  // a local declared between the throw point and the `try` is destroyed
  g_dtor_log = 0;
  try {
    Logger l;
    (void)l;
    throw MyError(5);
  } catch (MyError &e) {
    return g_dtor_log * 1000 + e.code;
  }
}

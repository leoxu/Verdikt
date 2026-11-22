# Invariant-checker fixtures

`sum_to.core` is the lowered form of `sum_to.c`, committed so the checker's test does not depend on the
frontend, clang headers, or anything else that can change underneath it.

The three candidates the test pins are chosen so that **each one fails differently if the checker breaks**:

| candidate | expected | what a wrong answer would mean |
|---|---|---|
| `i <= n` | `inductive` | the checker cannot prove anything (e.g. the back edge is never reached and everything is `vacuous`) |
| `i < n` | `not_inductive` | the checker accepts a candidate that fails on the LAST iteration — the classic off-by-one, and the most dangerous direction |
| `acc >= i` | `not_inductive` | the checker ignores the body's effect on state |

A fourth property is pinned implicitly: `i <= n` must come back `inductive` and **not** `vacuous`. The
vacuity guard exists because a loop whose body always traps would otherwise "pass" every candidate ever
written — the first pointer-carrying loop this checker ran on did exactly that.

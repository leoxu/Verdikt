// `--link` fixture, paired with xglobal_defs.c (see that file for the full scenario). This file only declares
// `driver`/`driver_v2` as `extern` and reads a field through an indirect pointer parameter (like freetype's
// `FT_Add_Module(library, clazz)` reads `clazz->module_size`) - not a direct named access, which Clang can
// (and does) constant-fold away, hiding the bug. Their real initializers live entirely in xglobal_defs.c,
// reached only via `#include`-ing xglobal_tmpl.c. Before the fix, `--link`'s "export this unit's initialised
// globals for other units" pass (Frontend.cpp) required `isInMainFile`, which is false for `#include`d content
// even when it's a `.c` file meant to be pasted in once - so `driver`'s initialiser was silently dropped and
// the global stayed all-zero at runtime: `read_n(&driver)` returned 0, and `100 / read_n(&driver)` divided by
// zero, an incorrectly reported `bug`. With the fix, `driver`'s real content (`n = 4`) is modeled exactly: no
// division by zero.
typedef struct { int n; int (*f)(void); } Rec;
extern const Rec driver;
extern const Rec driver_v2;

int read_n(const Rec *r) { return r->n; }

int entry(int x) {
  return x / read_n(&driver) + read_n(&driver_v2);
}

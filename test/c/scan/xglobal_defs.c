// `--link` fixture, paired with xglobal_entry.c: `driver`/`driver_v2` are *global variables* (not functions)
// defined only by #include-ing xglobal_tmpl.c twice (the X-macro idiom - see that file), and NEITHER is read
// from this file. This mirrors the real shape that exposed the bug: freetype's ttdriver.c defines
// `tt_driver_class` the same way (#include'd into truetype.c), and only ftinit.c, a different `--link` unit,
// ever reads it (through an `extern` declaration of a *smaller, compatible-prefix* struct type, the common
// "forward-declare the first member's type" C idiom) - see DESIGN.md for the full writeup.
typedef struct { int n; int (*f)(void); } Rec;

#define NS(x) x
#define LIMIT 4
#define TMPL_GUARD
#include "xglobal_tmpl.c"
#undef TMPL_GUARD
#undef LIMIT
#undef NS

#define NS(x) x##_v2
#define LIMIT 100
#define TMPL_GUARD
#include "xglobal_tmpl.c"
#undef TMPL_GUARD
#undef LIMIT
#undef NS

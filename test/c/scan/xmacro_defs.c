// `--link` fixture, paired with xmacro_entry.c: `get_count`/`get_count_v2` are defined only by #include-ing
// xmacro_tmpl.c twice (the X-macro idiom - see that file), and NEITHER is called from this file. This mirrors
// the real shape that exposed the bug: expat's xmltok.c defines `XmlInitEncoding`/NS the same way, and only a
// different file (xmlparse.c) ever calls them. A function reached only through a same-file call (the common
// case, and the only shape earlier ad hoc checks of this fix happened to cover) is not a regression test for
// this bug - the definition must be invisible to its own file and only resolved by `--link` from the caller's
// file, which is exactly what used to silently drop it.
#define NS(x) x
#define LIMIT 4
#define TMPL_GUARD
#include "xmacro_tmpl.c"
#undef TMPL_GUARD
#undef LIMIT
#undef NS

#define NS(x) x##_v2
#define LIMIT 100
#define TMPL_GUARD
#include "xmacro_tmpl.c"
#undef TMPL_GUARD
#undef LIMIT
#undef NS

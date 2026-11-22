// `--link` fixture, paired with xmacro_defs.c (see that file for the full scenario). This file only declares
// `get_count`/`get_count_v2` and calls them from `entry`; their bodies live entirely in xmacro_defs.c, reached
// only via `#include`-ing xmacro_tmpl.c. Before the fix, `--link`'s view of `get_count` had no body anywhere in
// the linked program (xmacro_defs.c's own FnCollector pass dropped it, since the X-macro template's content
// lives in a file `#include`d by, but not equal to, xmacro_defs.c, and nothing in xmacro_defs.c calls it to
// pull it in through the separate "reached via calls" path) - so it was treated as opaque: an untainted nondet
// return value, defaulting to its seed of 0. `100 / get_count()` divides by zero on that default seed, an
// incorrectly reported `bug` (division UB fires deterministically on the untainted nondet's seed value,
// unlike a tainted-branch-shaped check whose unsoundness would depend on the taint-exploration policy). With
// the fix, `get_count`'s real body (`return 4`, via xmacro_defs.c) is modeled exactly: no division by zero.
int get_count(void);
int get_count_v2(void);

int entry(int x) {
  return x / get_count() + get_count_v2();
}

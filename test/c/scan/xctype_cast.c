// `--link` fixture, added to xctype_entry.c + xctype_defs.c: a function stored into a check() slot through a cast. Real
// code calls such functions through the type it cast to, so it must stay a candidate of the check() call: its 256-byte
// write into the 16-byte struct addr6 is then reachable from entry().
#include "xctype_types.h"

static int getname_cast(struct trans *t, struct saddr *sa, int peer) {
  for (int i = 0; i < 256; i++) sa->data[i] = (char)peer;
  return t != 0;
}

struct trans cast_trans = { (int (*)(struct net_x *, const struct addr6 *, unsigned))getname_cast };

// Single-file (no --link) counterpart of xctype_entry.c + xctype_defs.c: the frontend's own per-file candidate list
// follows the same rule. A finding in entry() means getname_wide() was listed for the check() call.
#include "xctype_types.h"

static int check_real(struct net_x *n, const struct addr6 *a, unsigned s) { return a->b[0] != 0 && s == 0 && n != 0; }

static int getname_wide(struct trans *t, struct saddr *sa, int peer) {
  for (int i = 0; i < 256; i++) sa->data[i] = (char)peer;
  return t != 0;
}

struct trans the_trans = { check_real };
const struct sops the_sops = { getname_wide };

int entry(struct trans *t, struct net_x *n, struct addr6 *a) {
  if (!t->check) return 0;
  return t->check(n, a, 0);
}

// `--link` fixture: a call through a pointer of type check() in an object the scanner synthesizes, so the pointer can be
// any candidate the dispatcher lists. Only functions of that C type -- or whose address was cast to it -- may be called.
#include "xctype_types.h"

int entry(struct trans *t, struct net_x *n, struct addr6 *a) {
  if (!t->check) return 0;
  return t->check(n, a, 0);
}

// A field type no address-taken function has, although functions with its core signature exist: in the real program it
// holds a function of a module we do not have. The call must go on as an opaque external call; the store after it is the
// marker that the path got past the call (a NULL field would end it there, see Scan.cpp fieldsYaml).
struct other_ops { int (*cb)(struct net_x *, struct saddr *, int); };

int entry_other(struct other_ops *o, struct net_x *n, struct saddr *sa) {
  int r = o->cb(n, sa, 1);
  *(volatile int *)0 = 1;
  return r;
}

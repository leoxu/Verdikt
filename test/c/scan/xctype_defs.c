// `--link` fixture, paired with xctype_entry.c: one function of each type, both address-taken through tables of their
// own type. getname_wide() writes 256 bytes: called with a 16-byte struct addr6 it would overflow, so a finding in
// entry() means the dispatcher of the check() call listed a function of another C type.
#include "xctype_types.h"

static int check_real(struct net_x *n, const struct addr6 *a, unsigned s) { return a->b[0] != 0 && s == 0 && n != 0; }

static int getname_wide(struct trans *t, struct saddr *sa, int peer) {
  for (int i = 0; i < 256; i++) sa->data[i] = (char)peer;
  return t != 0;
}

struct trans the_trans = { check_real };
const struct sops the_sops = { getname_wide };

// The kernel's EXPORT_SYMBOL keeps every exported function alive through __ADDRESSABLE, which casts its address to
// `void *` into a discarded variable. That is no escape: getname_exported must stay out of the check() dispatcher.
static int getname_exported(struct trans *t, struct saddr *sa, int peer) {
  for (int i = 0; i < 256; i++) sa->data[i] = (char)peer;
  return t != 0;
}
const struct sops the_sops2 = { getname_exported };
static void *__UNIQUE_ID___addressable_getname_exported1 __attribute__((used)) = (void *)(unsigned long)&getname_exported;

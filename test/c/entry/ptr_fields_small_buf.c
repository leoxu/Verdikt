// ENTRY: use
// EXPECT: bug oob_read
// SPEC: ptr_fields_small.yaml
// the input struct carries a data pointer and an ops table: with pointer fields initialised to legal objects the
// function is safe; with them NULL (the old behaviour) every access would be a null_deref
#include <string.h>
struct ops { int (*op)(int); };
struct msg { int len; char *buf; const struct ops *ops; };
static int h_dbl(int x) { return x * 2 + 0; }
static int h_neg(int x) { return -x; }
static const struct ops my_ops = { h_dbl };
static const struct ops other_ops = { h_neg };   /* makes h_neg an address-taken (possible indirect call target) function */
int use(struct msg *m) {
  char local[8] = {0};
  if (m->len < 0 || m->len > 8) return -1;
  memcpy(local, m->buf, (unsigned long)m->len);
  return m->ops->op(m->len) + (int)(unsigned char)local[0];
}

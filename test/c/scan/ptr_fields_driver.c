// hlir-scan fixture: an input struct that is full of pointers (the shape of real driver contexts).
//   in    : pointer to a nested struct
//   ops   : pointer to a table of function pointers (targets are the address-taken functions with the right signature)
//   priv  : `void *` whose real type is revealed by the cast in ctx_use
//   head  : singly linked list (the `next` link is self-referential and stays NULL)
struct inner { int count; char name[8]; };
struct ops { int (*run)(int); };
struct priv { int mode; };
struct node { struct node *next; int v; };
struct dev_ctx { struct inner *in; const struct ops *ops; void *priv; struct node *head; };

static int run_a(int x) { return x & 0x7f; }
static int run_b(int x) { return (x >> 1) & 0x7f; }
static const struct ops ops_a = { run_a };
static const struct ops ops_b = { run_b };

int ctx_use(struct dev_ctx *c, int n) {
  struct priv *p = (struct priv *)c->priv;
  int s = (c->in->count & 0xff) + (p->mode & 0xff) + c->ops->run(n & 0xff);
  if (c->head) s += c->head->v & 0xff;
  if (c->head && c->head->next) s += 1;       /* uses the link, so it is a used (and self-referential) pointer field */
  return s;
}

int ctx_bug(struct dev_ctx *c) {
  return c->in->name[c->in->count];          /* count is attacker controlled and never checked against 8 */
}

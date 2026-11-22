// hlir-scan fixture: intrusive doubly linked lists (the Linux list_head / <driver> shape).
// An empty list head points at itself; with NULL links every list operation below would dereference NULL.
struct list_node { struct list_node *next, *prev; };
struct item { int v; struct list_node link; };
struct dev { int count; struct list_node items; };      /* list head embedded in the context */

static int list_empty(const struct list_node *h) { return h->next == h; }

int dev_first(struct dev *d) {
  if (list_empty(&d->items)) return -1;
  struct item *it = (struct item *)((char *)d->items.next - __builtin_offsetof(struct item, link));
  return it->v;
}

int dev_count(struct dev *d) {
  struct list_node *n = d->items.next;
  int cnt = 0;
  while (n != &d->items && cnt < 100) { n = n->next; cnt++; }
  return cnt;
}

int node_unlink(struct list_node *h) {                  /* the parameter itself is a list head */
  h->next->prev = h->prev;
  h->prev->next = h->next;
  return 0;
}

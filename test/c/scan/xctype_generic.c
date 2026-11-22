// Generic dispatch, the libwayland + libffi shape (DESIGN §22.342): a handler typed with struct pointers sits in a typed
// vtable, the vtable is read back as `void (* const *)(void)` and the entry calls it through a `void *` signature. The
// handler's own address is never cast, so only the C-type matching rule decides: `void *` positions must match any
// struct pointer. Reaching the store means the call reached on_req (with --link and without).
struct client;
struct resource;
struct iface { void (*req)(struct client *, struct resource *, int); };

static void on_req(struct client *c, struct resource *r, int v) {
  (void)c; (void)r;
  if (v == 7) *(volatile int *)0 = 1;
}

static const struct iface impl = { on_req };

void entry(int v) {
  const void *p = &impl;
  void (*fn)(void) = ((void (* const *)(void))p)[0];
  ((void (*)(void *, void *, int))fn)(0, 0, v);
}

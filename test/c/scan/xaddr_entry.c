// `--link` fixture, paired with xaddr_defs.c: calls through the pointer xaddr_tmpl.c stored. Reaching the store
// below means the call did not return init_scan's value.
struct enc { int (*scan)(int); };
void enc_init(struct enc *e);

void entry(void) {
  struct enc e;
  enc_init(&e);
  if (e.scan(0) != 7) *(volatile int *)0 = 1;
}

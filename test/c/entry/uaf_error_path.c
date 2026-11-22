// ENTRY: handle
// EXPECT: bug use_after_free
// SPEC: handle.yaml
void *malloc(unsigned long);
void free(void *);
int handle(int op) {
  int *state = malloc(sizeof(int));
  if (!state) return -1;
  *state = 7;
  if (op == 42) free(state);      /* error path frees early ... */
  int r = *state;                 /* ... but the common path keeps using it */
  free(state);
  return r;
}

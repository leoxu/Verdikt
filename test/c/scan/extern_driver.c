// --extern: `clamp_idx` has a body here, but the analysis is told to use a model instead (as for header inlines of an API).
static inline int clamp_idx(int x) { return x; }          /* the body does NOT clamp */
int pick(int v) {
  int table[4] = {1, 2, 3, 4};
  return table[clamp_idx(v)];
}

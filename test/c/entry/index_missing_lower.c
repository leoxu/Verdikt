// ENTRY: lookup
// EXPECT: bug ptr_arith_oob
// SPEC: lookup.yaml
static const int weights[8] = {1, 2, 3, 4, 5, 6, 7, 8};
int table[8];
int lookup(int idx) {
  int local[8];
  for (int i = 0; i < 8; i++) local[i] = i * 3;
  if (idx >= 8) return -1;       /* idx < 0 is not rejected */
  return local[idx];
}

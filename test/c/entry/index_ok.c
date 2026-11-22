// ENTRY: lookup
// EXPECT: safe
// SPEC: lookup.yaml
int lookup(int idx) {
  int local[8];
  for (int i = 0; i < 8; i++) local[i] = i * 3;
  if (idx < 0 || idx >= 8) return -1;
  return local[idx];
}

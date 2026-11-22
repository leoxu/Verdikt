// ENTRY: fill
// EXPECT: safe
// SPEC: fill.yaml
int fill(char *dst, const char *src, unsigned n) {
  char tmp[16];
  if (n > 16) return -1;
  for (unsigned i = 0; i < n; i++)
    tmp[i] = src[i];
  if (n > 0) dst[0] = tmp[0];
  return (int)n;
}

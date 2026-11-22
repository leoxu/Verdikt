// ENTRY: fill
// EXPECT: bug oob_write
// SPEC: fill.yaml
int fill(char *dst, const char *src, unsigned n) {
  char tmp[16];
  if (n > 16) return -1;
  for (unsigned i = 0; i <= n; i++)     /* <= writes tmp[16] when n == 16 */
    tmp[i] = src[i];
  dst[0] = tmp[0];
  return (int)n;
}

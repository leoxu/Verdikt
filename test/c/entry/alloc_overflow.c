// ENTRY: make
// EXPECT: bug signed_overflow
// SPEC: make.yaml
void *malloc(unsigned long);
void free(void *);
int make(int count) {
  if (count <= 0) return -1;
  int bytes = count * 64;           /* overflows for count > 33554431 */
  char *p = malloc(bytes);
  if (!p) return -2;
  p[0] = 1;
  free(p);
  return 0;
}

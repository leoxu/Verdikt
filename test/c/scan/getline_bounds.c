// Regression for the new `getline` ModelDB model (models/libc.core): the model allocates a fixed 4096-byte
// buffer and fills 4095 bytes + a NUL terminator. `line[r-1]` (r is the real returned length, <= 4095) must stay
// in-bounds; reading unconditionally past the model's known capacity (line[5000], ignoring r entirely) must not.
#include <stdio.h>
int consume_safe(FILE *fp) {
  char *line = NULL;
  size_t n = 0;
  ssize_t r = getline(&line, &n, fp);
  if (r > 0) return line[r - 1];
  return 0;
}
int consume_bug(FILE *fp) {
  char *line = NULL;
  size_t n = 0;
  getline(&line, &n, fp);
  return line[5000];
}

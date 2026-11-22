// An internal function in the style of bzip2's BZ2_hbMakeCodeLengths: it trusts its callers for the preconditions.
//   0 <= alphaSize <= 4, every freq[i] in [0, 2^23), len has room for alphaSize entries
#include <string.h>
#define MAX_ALPHA 4
struct coder { int err; int pad; };

int make_lengths(unsigned char *len, const int *freq, int alphaSize) {
  int weight[MAX_ALPHA + 1];
  int total = 0;
  for (int i = 0; i < alphaSize; i++) {
    weight[i + 1] = (freq[i] == 0 ? 1 : freq[i]) << 8;      /* negative freq: UB; freq >= 2^23: overflow */
    total += weight[i + 1] >> 8;
  }
  for (int i = 0; i < alphaSize; i++) len[i] = (unsigned char)(total & 0x7f);
  return total;
}

const char *err_name(struct coder *c) {
  static const char *names[] = {"ok", "bad-data", "overflow", "eof"};
  return names[-c->err];                                     /* err is in [-3, 0] by the coder's own invariant */
}

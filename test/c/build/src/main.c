// compiled with: -Iinc -DLIMIT=8 -DEXTRA_FEATURE -fno-strict-overflow  (see ../Makefile)
#include "cfg.h"
#include <string.h>

int copy_in(char *dst, const char *src, int n) {
  char buf[CAP] = {0};                 /* 16 bytes */
  if (n < 0 || n > CAP) return -1;     /* exactly the buffer size: safe */
  memcpy(buf, src, (unsigned long)n);
  dst[0] = buf[0];
  return n;
}

int copy_off_by_one(char *dst, const char *src, int n) {
  char buf[CAP] = {0};
  if (n < 0 || n > CAP + 1) return -1; /* one too many: a real bug, but only visible if CAP is known to be 16 */
  memcpy(buf, src, (unsigned long)n);
  dst[0] = buf[0];
  return n;
}

int add(int a, int b) { return a + b; }  /* -fno-strict-overflow: wraps, not undefined */

#ifdef EXTRA_FEATURE
int feature(int x) { return x & 0xff; }
#endif
int checked(void) { return CHECKED; }

// Sibling of strcat_overflow.c: `h.buf` is 512 bytes, large enough to hold any synthesized `src` cstring (the
// auto-synthesizer's cstring range is 1..256 bytes) plus the NUL terminator -- confirms the new `strcat` model
// doesn't over-report (no false positive once there's genuinely enough room).
#include <string.h>
struct holder { char buf[512]; };
int consume(const char *src) {
  struct holder h;
  h.buf[0] = 0;
  strcat(h.buf, src);
  return 0;
}

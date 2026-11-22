// Regression for the new `strcat` ModelDB model (models/libc.core): `h.buf` is an 8-byte local, starts empty
// (strlen 0), `src` is a `const char *` with no length parameter -- the auto-synthesizer treats that as a
// NUL-terminated cstring of 1..256 bytes (see Scan.cpp's `cstr` handling). Any src longer than 7 chars overflows
// `h.buf`; the model must catch this (it didn't exist before -- strcat was a completely opaque, unmodelled call).
#include <string.h>
struct holder { char buf[8]; };
int consume(const char *src) {
  struct holder h;
  h.buf[0] = 0;
  strcat(h.buf, src);
  return 0;
}

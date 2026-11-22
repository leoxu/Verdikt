// Minimal stand-in for the stb-style "single-header library" idiom (stb_image.h, dr_libs, qoi, miniz,
// nuklear, ...): declarations are always visible, but the real function body only exists when the
// *including* file itself `#define`s SINGLEHEADER_IMPLEMENTATION before `#include`-ing this header.
#ifndef SINGLEHEADER_LIB_H
#define SINGLEHEADER_LIB_H

void singleheader_copy(int *out, const int *in, int n);

#ifdef SINGLEHEADER_IMPLEMENTATION

void singleheader_copy(int *out, const int *in, int n) {
  int local[4];
  // deliberate bug: writes local[0..n] inclusive, so n == 4 (an attacker-controlled, in-range-looking
  // value) already overflows local[4]'s 4 slots by one.
  for (int i = 0; i <= n; i++) {
    local[i] = in[i];
  }
  for (int i = 0; i < n && i < 4; i++) out[i] = local[i];
}

#endif  // SINGLEHEADER_IMPLEMENTATION

#endif  // SINGLEHEADER_LIB_H

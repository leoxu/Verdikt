// Multi-dimensional variable length arrays (VLAs): locally-declared `int buf[n][m]`/`int buf[n][m][k]`, and the
// row-major stride arithmetic used to address them. Single-dimension VLA is covered incidentally by `oob` in ub.c;
// this file is specifically about the multi-dimensional case (`docs/FEATURE_STATUS.md` previously listed this as
// an unsupported gap: `declare()` used to reject any VLA whose element type was itself a VLA).

// RUN: @vla1d(5, 4) => 0
// RUN: @vla1d(5, 5) => ub:oob_write
// RUN: @vla1d(5, -1) => ub:ptr_arith_oob
int vla1d(int n, int i) { int buf[n]; buf[i] = 1; return 0; }

// RUN: @vla2d(3, 4, 2, 3) => 0
// RUN: @vla2d(3, 4, 2, 4) => ub:oob_write
// RUN: @vla2d(3, 4, 3, 0) => ub:oob_write
// RUN: @vla2d(3, 4, -1, 0) => ub:ptr_arith_oob
int vla2d(int n, int m, int i, int j) { int buf[n][m]; buf[i][j] = 1; return 0; }

// RUN: @vla3d(2, 3, 4, 1, 2, 3) => 0
// RUN: @vla3d(2, 3, 4, 1, 2, 4) => ub:oob_write
// RUN: @vla3d(2, 3, 4, 2, 0, 0) => ub:oob_write
int vla3d(int n, int m, int k, int i, int j, int l) { int buf[n][m][k]; buf[i][j][l] = 1; return 0; }

// buf[1][0] must land at flat offset m (not n, and not some other stride): proves the row stride used to
// address the outer dimension is the *inner* dimension's runtime size, not a fixed/wrong one.
// RUN: @vla2d_rowstride(3, 4) => 1
int vla2d_rowstride(int n, int m) {
  int buf[n][m];
  buf[1][0] = 9;
  int *flat = (int *)buf;
  return flat[m] == 9;
}

// the same stride check one level deeper: buf[0][1][0] must land at flat offset k (the innermost dimension).
// RUN: @vla3d_rowstride(2, 3, 4) => 1
int vla3d_rowstride(int n, int m, int k) {
  int buf[n][m][k];
  buf[0][1][0] = 7;
  int *flat = (int *)buf;
  return flat[k] == 7;
}

// writing through the last row of the outer dimension must not corrupt an earlier row (would fail if the
// allocation size used the wrong stride/dimension order and undersized the buffer).
// RUN: @vla2d_no_alias(3, 4) => 1
int vla2d_no_alias(int n, int m) {
  int buf[n][m];
  buf[0][0] = 11;
  buf[n - 1][m - 1] = 22;
  return buf[0][0] == 11;
}

// a non-positive VLA dimension is diagnosed (as `core.assert`) before any allocation/addressing happens, for
// every nesting level, not just the outermost one.
// RUN: @vla_neg_outer(-1, 4) => assert_failed
// RUN: @vla_neg_inner(4, 0) => assert_failed
int vla_neg_outer(int n, int m) { int buf[n][m]; buf[0][0] = 1; return 0; }
int vla_neg_inner(int n, int m) { int buf[n][m]; buf[0][0] = 1; return 0; }

// mixed VLA + trailing constant dimension (`int[n][4]`): the constant inner dimension must still use its
// compile-time size, not be mistaken for a second runtime dimension.
// RUN: @vla_mixed(3, 2, 3) => 0
// RUN: @vla_mixed(3, 2, 4) => ub:oob_write
// RUN: @vla_mixed(3, 3, 0) => ub:oob_write
int vla_mixed(int n, int i, int j) { int buf[n][4]; buf[i][j] = 1; return 0; }

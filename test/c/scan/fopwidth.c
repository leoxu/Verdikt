/* Regression for DESIGN.md §22.414: the fp-result symbolic name must encode the result width.
   The TermManager outlives a single run, so two runs that reach the same (function, step) index with
   differently-typed fp operations used to request the same variable name at two widths, which aborted
   the worker in TermManager::bvVar and turned the whole entry into a silent `unknown`.
   Alternating float (32-bit result) and double (64-bit) work under an attacker-controlled branch puts
   different fp widths at the same step index on different paths. */
static volatile double g_sink;

static double fop_mix(const unsigned char *b, unsigned n) {
  double acc = 0.0;
  for (unsigned i = 0; i < n && i < 12; i++) {
    if (b[i] & 1) {
      float f = (float) b[i] * 1.5f;      /* 32-bit fp result */
      f = f / 3.0f;
      acc += (double) f;
    } else {
      double d = (double) b[i] * 1.25;    /* 64-bit fp result */
      d = d / 7.0;
      acc += d;
    }
  }
  return acc;
}

int demo_fopwidth(const unsigned char *in, unsigned len) {
  if (len < 12) return -1;
  g_sink = fop_mix(in, len);
  return (int) g_sink;
}

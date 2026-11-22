// Coverage is a fraction, and `init:` was changing its DENOMINATOR (DESIGN.md §22.376). The harness calls the
// project's own initialiser before it calls the entry, so a reachability walk seeded at the harness counts every
// block `main` can reach as "reachable by this entry". Measured on a QNX resource manager: the same devctl
// handler reported 594 reachable blocks without `init:` and 2194 with it -- a quarter of the percentage for the
// identical analysis. The number a reader uses to decide whether a `safe` verdict means anything must not depend
// on how much unrelated code the initialiser happens to touch.
int gCovLimit;

// --- the initialiser's own world: large, and the entry never calls any of it ---------------------------------
static int cov_init_helper1(int x) { if (x > 1) return x + 1; if (x < -1) return x - 1; return 0; }
static int cov_init_helper2(int x) { if (x & 1) return cov_init_helper1(x); if (x & 2) return x * 2; return 1; }
static int cov_init_helper3(int x) { if (x > 10) return cov_init_helper2(x); if (x > 5) return x; return 2; }

void demo_cov_init(void) {
  int a = cov_init_helper3(7) + cov_init_helper2(3) + cov_init_helper1(9);
  gCovLimit = a > 0 ? 8 : 4;
}

// --- the entry's world: small, and the initialiser never calls it --------------------------------------------
static char covBuf[8];
static int cov_entry_helper(unsigned i) { return (int)(i & 7); }

int demo_cov_entry(unsigned idx) {
  if (idx > 100) return -1;
  return covBuf[cov_entry_helper(idx)];
}

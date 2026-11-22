// A branch decided by a global's INITIAL value is an unrecorded narrowing (DESIGN.md §22.362): `module_init` and
// the other internal initialisers are never executed, so the global still holds what its static initialiser gave
// it, and `Machine` takes the branch concretely with no fork. One global therefore produces a false finding (the
// edge the real module would never take) and a silent coverage loss (the edge it would) at the same time.
int gFoo = 10;             // the module's own init sets this to 100; the scanner never runs that
static char buf[8];

void demo_g_init(void) { gFoo = 100; }

// positive: `gFoo < 100` is true only because demo_g_init did not run
int demo_g_gated(unsigned idx) {
  if (gFoo < 100) return buf[idx + 100];   // dead in reality, reached here
  return buf[idx & 7];
}

// negative 1: the program itself writes it before the branch, so the decision is the program's, not the initial
// value's.  negative 2: a const global cannot be changed by an initialiser either, so reading it asserts nothing.
const int kLimit = 8;
int gSet;

int demo_g_plain(unsigned idx) {
  gSet = (int)(idx & 1);
  if (gSet) return buf[idx & 7];
  if ((int)idx < kLimit) return buf[idx & 7];
  return 0;
}

// A project's own statement about the externals it calls (`--externs`, DESIGN.md §22.379).
//
// `ext_log` contributes nothing to any state an entry reads -- it is logging. `ext_unexamined` nobody has looked
// at. Both are opaque and both BEHAVE identically; the point is that the report must not say the same thing
// about them, because they are different claims. Lumped together, the second hides inside the first.
extern void ext_log(const char *msg, int v);
extern int ext_unexamined(int v);
extern int ext_unused(int v);   // declared, never called: a skip list entry may legitimately name it

static char ebuf[8];

int demo_ext_entry(unsigned idx) {
  ext_log("hello", (int)idx);
  int k = ext_unexamined((int)idx);
  if (k > 8) return -1;
  return ebuf[k & 7];
}

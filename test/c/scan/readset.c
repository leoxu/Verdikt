// The TARGET SET (DESIGN.md §22.374/§22.375): which locations the entry's call chain actually reads. It is both
// the completion criterion for an initialiser ("has everything this entry reads been established?") and the mask
// that keeps G2's promotion from exploding. For either use it has to be (a) free of locations no initialiser
// could ever establish, and (b) named so that two passes -- and a reader -- can match the same location.
#include <stddef.h>

struct cfg { int n; int pad[3]; };
struct sess { struct cfg *cfg; int flag; };

int gReadsetLimit = 4;

// a callee with locals of its own: these are born and die inside one call, so they belong to no target set
static int demo_rs_helper(unsigned x) {
  int scratch[4];
  scratch[0] = (int)(x & 3);
  scratch[1] = scratch[0] + 1;
  return scratch[1];
}

int demo_readset(struct sess *s, unsigned idx) {
  int local[2];
  local[0] = demo_rs_helper(idx);
  local[1] = gReadsetLimit;
  if (s->flag) return s->cfg->n + local[0];
  return local[1];
}

/* DESIGN.md §22.415 -- the coverage frontier as an automatic target set.
   What this fixture pins down is the MECHANISM, not a win over the baseline:
     - `not_entered` lists the program's own functions and none of the engine's `__hlir_init.str*`
       (the string literal below is there to make those exist);
     - a never-entered function that can hold a defect sorts before one that cannot;
     - `--auto-target N` re-runs the search aimed at them and says so in the report;
     - the reported coverage is the UNION over every round, so it never shrinks.
   `cold_checked` is unreachable for a reason the solver settles at once: two bytes multiply to at most
   65025, so == 0xFFFF has no solution. That is deliberate. A coverage gap may be infeasible rather than
   unexplored, the two are not distinguishable from the summary numbers, and a targeted round is exactly
   how you tell them apart. */
#include <stddef.h>

static const char *kTag = "autotarget-fixture";

static int cold_checked(const unsigned char *b, unsigned n) {  /* loads => core.check.* inside */
  int s = 0;
  for (unsigned i = 0; i < n && i < 4; i++) s += b[i];
  return s;
}

static int cold_barren(void) { return 1; }  /* no load, no check: nothing can be found in here */

static int warm(const unsigned char *b, unsigned n) {
  int acc = 0;
  for (unsigned i = 0; i < n && i < 8; i++) {
    if (b[i] < 0x20) acc += 1;
    else if (b[i] < 0x40) acc += 2;
    else if (b[i] < 0x60) acc += 3;
    else acc += 4;
  }
  return acc;
}

int demo_autotarget(const unsigned char *in, unsigned len) {
  if (len < 8) return -1;
  if ((unsigned) (in[0] * in[1]) == 0xFFFFu) return cold_checked(in, len) + cold_barren();
  return warm(in, len) + (int) kTag[0];
}

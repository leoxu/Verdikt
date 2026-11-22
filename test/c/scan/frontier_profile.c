// The search-budget profile (DESIGN.md §22.392): the engine reports WHERE its frontier went and singles out a
// library model whose loop spells one logical decision as N sequential branches. That is the shape §22.385
// removed from `strchr` by hand -- and until now it was found only because someone set HLIR_DEBUG_FRONTIER and
// thought to look at the output. The selection is what this pins; the folding itself is still a human decision.
//
// Two halves, and the second is the one that is easy to get wrong:
//
//   1. @strstr must be named a FOLD CANDIDATE. Its model is a nested loop that branches on an attacker byte per
//      iteration, it has no closed form behind it, and `pick` calls it with a constant needle -- so a single call
//      costs many independent flips (measured ~11, against ~1 for ordinary control flow).
//
//   2. @pick must NOT be, however much of the frontier it owns. An entry owning its own frontier is the HEALTHY
//      state -- it is exactly what folding @strchr achieved on c-ares, where inet_net_pton_ipv6 went on to hold
//      77% of the frontier at 14.7 flips per call. Flagging that would report the cure as the disease. The test
//      that separates them is not a threshold: program code may never be summarised away, because its control
//      flow is the thing under analysis, so only a function whose branches carry NO source location qualifies.
//
// The `bias` chain exists only to give @pick a frontier of its own, so both rows are populated and half 2 is
// actually exercised rather than vacuously true.
#include <string.h>

int pick(const char *w, unsigned bias)
{
  int n = 0;
  if (strstr(w, "alpha")) n += 1;
  if (strstr(w, "bravo")) n += 2;
  if (bias & 1u) n += 8;
  if (bias & 2u) n += 16;
  if (bias & 4u) n += 32;
  if (bias & 8u) n += 64;
  if (bias > 100u) n += 128;
  if (bias < 7u) n += 256;
  return n;
}

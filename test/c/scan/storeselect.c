// The write side of selection (DESIGN.md §22.487), the dual of consttable.c.
//
// `targets()` concretised a STORE's symbolic offset to the slot this run took, so the write landed
// there alone and every other slot kept an untainted byte. A condition built from one of those
// slots was then not symbolic at all: the branch landed in `const` -- "executed, but the condition
// was never symbolic" -- and its other edge was never explored. Same mechanism as §22.465, one
// direction later.
//
// Both halves are here, because a fix that only makes the sick case pass is not evidence:
//
//   st_symindex    symbolic store index, constant read index -> the gap. Must reach BOTH edges.
//   st_constindex  constant store index, symbolic value      -> never had the gap. Must stay complete.
//
// A store has no unguarded fallback target the way a read does: an offset outside the object writes
// nothing (the out-of-bounds check reports that separately), so every target carries its guard and
// `wr()` turns each into ite(off == k, new, old). An unguarded last target would scatter one write
// across the whole object.
#include <stdint.h>

int ss_a, ss_b, ss_c, ss_d;

void st_symindex(unsigned char *src, unsigned len)
{
  if (len < 1) return;
  unsigned char tab[16];
  for (unsigned i = 0; i < 16; i++) tab[i] = 0;
  tab[src[0] & 15] = 1;          // symbolic offset: the write must be visible from EVERY slot
  if (tab[3]) ss_a = 1; else ss_b = 1;
}

void st_constindex(unsigned char *src, unsigned len)
{
  if (len < 1) return;
  unsigned char tab[16];
  for (unsigned i = 0; i < 16; i++) tab[i] = 0;
  tab[3] = src[0] & 1;           // constant offset, symbolic value: always worked
  if (tab[3]) ss_c = 1; else ss_d = 1;
}

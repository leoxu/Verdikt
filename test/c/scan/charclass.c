// strchr/strrchr over a CONSTANT needle are answered in closed form -- a chain of core.select with no branches at
// all -- instead of by running the model's loop (DESIGN.md §22.385). The loop is not wrong, it is expensive in the
// only currency the search has: each iteration ends in two `core.cond_br` on a condition the attacker's byte
// decides, so a 16-character needle costs up to 34 FLIPPABLE branches per call, and a text parser calls it once or
// twice per input character. Measured on c-ares CVE-2023-31130: 1856902 of 2111991 flippable path conditions (88%)
// were inside @strchr, and with them gone the same scan finds the defect from a fully symbolic input.
//
// Folding a call is only sound if it answers exactly what the loop would. Every expectation below is hand-computed
// and a disagreement is turned into an out-of-bounds write, so the SCANNER ITSELF is the oracle: `safe` here means
// every case agreed, for every one of the 256 values of `c`.
#include <string.h>

static const char tbl[] = "0123456789abcdef";
static const char rev[] = "aXbXc";

int demo_charclass(unsigned char c)
{
  char guard[1];
  const char *p, *q;
  int a, b, bad = 0;

  guard[0] = 0;
  p = strchr(tbl, (int)c);
  q = strrchr(rev, (int)c);
  a = p ? (int)(p - tbl) : -1;
  b = q ? (int)(q - rev) : -1;

  if (c == '0' && a != 0)  bad = 1;   /* first character */
  if (c == 'f' && a != 15) bad = 1;   /* last character */
  if (c == 'z' && a != -1) bad = 1;   /* absent -> NULL */
  if (c == 0   && a != 16) bad = 1;   /* strchr(s, 0) returns the TERMINATOR, not NULL */
  if (c == 'X' && b != 3)  bad = 1;   /* strrchr takes the LAST match, not the first */
  if (c == 'a' && b != 0)  bad = 1;
  if (c == 'c' && b != 4)  bad = 1;
  if (c == 'q' && b != -1) bad = 1;
  if (bad) guard[64] = 1;             /* oob_write iff the folded answer disagreed */
  return guard[0];
}

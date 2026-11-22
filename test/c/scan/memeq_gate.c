// A bug gated ONLY by `strstr` finding a 6-byte needle in attacker data, so the run threshold measures exactly
// the cost of the needle search and nothing else (DESIGN.md §22.393). Measured, 3/3 reproducible at every level:
//
//     inner loop (HLIR_NO_MEMEQ_FOLD=1)   100 runs      5/10/20/30/50 miss
//     branch-free equality                  5 runs      the smallest budget tried, still found
//
// The collapse does not make the search cleverer: it stops spending one flippable branch per needle BYTE on a
// question -- "do these six bytes match?" -- that is one disjunction for the solver. Six branches per candidate
// position, per run, is the entire difference.
#include <string.h>

int strstr_gate(const char *req)
{
    char small[4];
    if (!strstr(req, "/admin")) return 0;
    small[7] = 1;                 /* out of bounds, reachable only on a real match (line 16) */
    return small[7];
}

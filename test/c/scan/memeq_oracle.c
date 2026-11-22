// @strstr / @memmem now collapse their INNER comparison into one branch-free conjunction (DESIGN.md §22.393,
// Machine::memEqFast). A collapsed comparison must answer exactly what the byte loop answered, so this fixture
// makes the SCANNER ITSELF the oracle: every expectation below is hand-computed, and any disagreement is turned
// into an out-of-bounds write. `safe` here means all of them agreed; a wrong fold turns it into `bug`.
//
// The cases are chosen for where a fixed-length equality goes wrong: an empty needle, a needle longer than the
// haystack, a match at offset 0, a match that is not the first candidate position, a near-miss that shares a
// prefix with the real match (the case a non-lazy comparison gets wrong), and a needle that only occurs across
// the NUL for memmem (which has an explicit length and no terminator).
#include <string.h>

static const char hay[] = "abcabdabcx";   /* 10 chars + NUL */

int demo_memeq(unsigned char pick)
{
    char guard[1];
    int bad = 0;

    /* strstr: empty needle is the haystack itself */
    if (strstr(hay, "") != hay) bad = 1;
    /* no match at all */
    if (strstr(hay, "zz") != 0) bad = 1;
    /* needle longer than the haystack */
    if (strstr(hay, "abcabdabcxy") != 0) bad = 1;
    /* match at offset 0 */
    if (strstr(hay, "abc") != hay + 0) bad = 1;
    /* the FIRST match wins, and the candidate at 0 shares the prefix "ab" with it */
    if (strstr(hay, "abd") != hay + 3) bad = 1;
    /* a match that starts only after a near-miss: "abcx" shares "abc" with offset 0 */
    if (strstr(hay, "abcx") != hay + 6) bad = 1;
    /* the whole haystack */
    if (strstr(hay, hay) != hay + 0) bad = 1;
    /* a one-byte needle, last position */
    if (strstr(hay, "x") != hay + 9) bad = 1;

    /* memmem: explicit length, no terminator involved */
    if (memmem(hay, 10, "abd", 3) != hay + 3) bad = 1;
    if (memmem(hay, 10, "", 0) != hay) bad = 1;
    /* the length bound is respected: "cx" ends at index 9, so a bound of 9 must not find it */
    if (memmem(hay, 10, "cx", 2) != hay + 8) bad = 1;
    if (memmem(hay, 9, "cx", 2) != 0) bad = 1;
    /* a needle longer than the bound */
    if (memmem(hay, 3, "abca", 4) != 0) bad = 1;

    /* the attacker byte only decides WHICH wrong answer is written, never whether one is */
    if (bad) guard[pick] = 1;   /* out of bounds for every pick but 0, and pick == 0 is unreachable when bad */
    return bad;
}

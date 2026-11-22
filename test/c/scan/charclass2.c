// The character-class family -- memchr/strpbrk/strspn/strcspn -- answered in closed form, with the scanner
// as its own oracle (DESIGN.md §22.412, same discipline as charclass.c for strchr/strrchr).
//
// memchr folds through Machine::charClassFast with a COUNT instead of a terminator; the other three fold
// because their models ask @strchr about the constant set, so they inherit §22.385's fold rather than
// adding a second one. Every expectation below is hand-computed, and a disagreement becomes an
// out-of-bounds write -- so `safe` here means all of them agreed, for every one of the 256 byte values.
#include <string.h>

static const char tbl[] = "0123456789abcdef";
static const char zed[] = "a\0b";          /* embedded NUL: memchr must look past it, strchr must not */

int demo_charclass2(unsigned char c)
{
    char guard[1];
    int bad = 0;
    const void *m;

    /* ---- memchr: a count, not a terminator */
    m = memchr(tbl, '0', 16);   if (m != tbl + 0)  bad = 1;
    m = memchr(tbl, 'f', 16);   if (m != tbl + 15) bad = 1;
    m = memchr(tbl, 'f', 15);   if (m != 0)        bad = 1;   /* just short of it */
    m = memchr(tbl, 'z', 16);   if (m != 0)        bad = 1;
    m = memchr(tbl, '0', 0);    if (m != 0)        bad = 1;   /* zero count never matches */
    m = memchr(zed, 'b', 3);    if (m != zed + 2)  bad = 1;   /* PAST the embedded NUL */
    m = memchr(zed, 0, 3);      if (m != zed + 1)  bad = 1;   /* a zero byte is an ordinary match */

    /* ---- strpbrk / strspn / strcspn over a constant set */
    if (strpbrk("xyz9w", tbl) != 0 && *strpbrk("xyz9w", tbl) != '9') bad = 1;
    if (strpbrk("xyzw", tbl) != 0)   bad = 1;                  /* nothing from the set */
    if (strpbrk("", tbl) != 0)       bad = 1;                  /* empty subject */
    if (strspn("123xyz", tbl) != 3)  bad = 1;
    if (strspn("xyz", tbl) != 0)     bad = 1;
    if (strspn("", tbl) != 0)        bad = 1;
    if (strcspn("xyz123", tbl) != 3) bad = 1;
    if (strcspn("123", tbl) != 0)    bad = 1;
    if (strcspn("xyz", tbl) != 3)    bad = 1;                  /* no reject byte at all */

    /* the attacker byte only decides WHICH wrong answer is written, never whether one is */
    if (bad) guard[c] = 1;
    return bad;
}

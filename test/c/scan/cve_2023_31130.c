// c-ares CVE-2023-31130 (GHSA-x6mf-cxr9-8q6v), minimised from `inet_net_pton_ipv6` at f22cc010^.
//
// TIER A per DESIGN.md §22.370: a REGRESSION GUARD, never a recall number. A hand-extracted snippet is a
// different program -- the character classifier here is two range tests, where c-ares calls strchr() over a
// 16-character constant, and that difference is exactly what decides whether the search finds the input
// (§22.385). What this fixture pins is the part that does NOT change: a stack object, a bound recomputed from
// attacker data, a guard that tests `==` where it needed `>`, and a write that lands BEFORE the object.
//
// The defect: `endp` starts at tmp+16 and every bound check in the parse loop is made against it. Afterwards it
// is re-based on `bits`, which the attacker supplies as "/N" -- for N <= 16 it becomes tmp+4, while `tp` has
// advanced by the real number of groups. The shift loop then writes `endp - i` for i = 1..n with n = tp - colonp,
// and nothing stops n from exceeding endp - tmp. "::1:2:3/0" gives n = 6 against a 4-byte window: tmp[-1], tmp[-2].
//
// Upstream did not patch the guard; it moved "/bits" out of the function entirely.

int demo_cve_2023_31130(const char *src)
{
  unsigned char tmp[16];
  unsigned char *tp = tmp, *endp = tmp + 16, *colonp = 0;
  int bits = -1, words, n, i, val = 0, saw = 0, ch;
  const char *p = src;

  for (i = 0; i < 16; i++) tmp[i] = 0;

  /* Leading "::" needs the same special case the original has: without it the loop sees both colons and the
     second one is rejected, so the published trigger would not even parse. Dropping it was the first thing this
     minimisation got wrong -- a snippet is a different program (DESIGN.md §22.370). */
  if (*p == ':') { if (*++p != ':') return -8; }

  while ((ch = *p++) != 0) {
    if (ch >= '0' && ch <= '9') { val = ch - '0'; saw = 1; continue; }   /* one digit per group: see the note above */
    if (ch == ':') {
      if (!saw) { if (colonp) return -1; colonp = tp; continue; }
      if (tp + 2 > endp) return -2;                 /* checked against the ORIGINAL endp */
      *tp++ = (unsigned char)(val >> 8);
      *tp++ = (unsigned char)val;
      saw = 0; val = 0; continue;
    }
    if (ch == '/') {
      if (*p < '0' || *p > '9') return -3;
      bits = (*p++ - '0') * 16;   /* one digit, scaled: 0 and 1 give the small `words` the defect needs */
      break;
    }
    return -4;
  }
  if (saw) {
    if (tp + 2 > endp) return -5;
    *tp++ = (unsigned char)(val >> 8);
    *tp++ = (unsigned char)val;
  }
  if (bits == -1) bits = 128;
  words = (bits + 15) / 16;
  if (words < 2) words = 2;
  endp = tmp + 2 * words;                           /* the defect: the bound is re-based on attacker data */
  if (colonp) {
    n = (int)(tp - colonp);
    if (tp == endp) return -6;                      /* `==` where it needed `>` */
    for (i = 1; i <= n; i++) {
      *(endp - i) = *(colonp + n - i);              /* writes before `tmp` once n > endp - tmp */
      *(colonp + n - i) = 0;
    }
    tp = endp;
  }
  if (tp != endp) return -7;
  return tmp[0];
}

// The published trigger, concrete: this half of the guard is about DETECTION (a negative offset into a real
// stack object, and a replay that reproduces it), and it must never depend on the search finding anything.
int demo_cve_2023_31130_trigger(void)
{
  return demo_cve_2023_31130("::1:2:3/0");
}

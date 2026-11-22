// Interprocedural validate-then-use (BACKWARD_WP_P0_PLAN §3.x). The return summary is a DISJUNCTION over return sites:
// a constant return becomes an exact `r == c` disjunct (a sentinel like -1 is kept precisely), a structurally-bounded
// return a `r <= M` disjunct. The caller's own branch on the result (`if (c >= 0) ...`, a step-3b path condition) then
// excludes the sentinel and leaves the bounded disjunct -- so the classic `c = classify(x); if (c>=0) buf[c]` idiom
// proves SAFE. The old single `r <= max` could not: the -1 return made max vacuous.

static int classify(unsigned x)      { if (x & 1) return -1; return x & 7; }   // -1 (sentinel) OR 0..7
static int classify_wide(unsigned x) { if (x & 1) return -1; return x & 31; }  // -1 OR 0..31

char vu_safe(unsigned k) {              // on c>=0, classify returned 0..7 -> buf[8][c] SAFE
    char buf[8]; int c = classify(k);
    if (c >= 0) return buf[c];
    return 0;
}

char vu_noguard(unsigned k) {           // no sentinel check: c may be -1 -> buf[c] MUST stay sat
    char buf[8]; int c = classify(k);
    return buf[c];
}

char vu_toowide(unsigned k) {           // valid range 0..31 into buf[8]: c can be 31 -> MUST stay sat
    char buf[8]; int c = classify_wide(k);
    if (c >= 0) return buf[c];
    return 0;
}

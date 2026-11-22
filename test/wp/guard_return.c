// Interprocedural guard-derived return bound (BACKWARD_WP_P0_PLAN §3.x). The return value's bound comes not from the
// return EXPRESSION's structure (`x & 7`) but from a GUARD inside the callee that dominates the return site:
// `if (n <= 16) return n;` -- the `return n` is reached only when n <= 16, so the summary's disjunct is r <= 16. Built
// by matching the returned value (through promotable single-store loads) against a step-3b dominating guard.

static int get_len(const unsigned char *p)    { int n = p[0]; if (n <= 16) return n; return -1; }  // valid 0..16
static int get_strict(const unsigned char *p) { int n = p[0]; if (n < 16)  return n; return -1; }  // valid 0..15

char gr_safe(const unsigned char *p) {          // on len>=0, get_len returned 0..16 -> buf[17][len] SAFE
    char buf[17]; int len = get_len(p);
    if (len >= 0) return buf[len];
    return 0;
}

char gr_toosmall(const unsigned char *p) {      // same bound but buf[16]: len can be 16 -> OOB -> MUST stay sat
    char buf[16]; int len = get_len(p);
    if (len >= 0) return buf[len];
    return 0;
}

char gr_strict(const unsigned char *p) {        // get_strict uses `< 16` -> len <= 15 -> buf[16][len] SAFE
    char buf[16]; int len = get_strict(p);
    if (len >= 0) return buf[len];
    return 0;
}

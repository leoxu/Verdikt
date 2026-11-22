// P2 symbolic-step accumulator (BACKWARD_WP_P0_PLAN §3.x): cnt += s with s a LOOP-INVARIANT (but symbolic) value, in a
// single unconditional in-loop store, gives the EXACT relation  cnt == init0 + s*(iv - iv0)  over shared symbols (s
// shares termOf with any guard that bounds it). A surrounding bound on s then bounds cnt by the trip count. An unbounded
// step, or a step that varies per iteration, provably cannot be bounded this way and stays sat.

char ss_safe(unsigned x) {              // bounded invariant step: x <= 9, so cnt == x*i, i < 10 -> cnt <= 81 < 100 -> SAFE
    char buf[100]; unsigned cnt = 0, i;
    if (x > 9) return 0;
    for (i = 0; i < 10; i++) { buf[cnt] = 0; cnt += x; }
    return 0;
}

char ss_unbounded(unsigned x) {         // invariant but UNBOUNDED step: cnt == x*i with x free -> MUST stay sat
    char buf[100]; unsigned cnt = 0, i;
    for (i = 0; i < 10; i++) { buf[cnt] = 0; cnt += x; }
    return 0;
}

char ss_vary(unsigned *a) {             // step a[i] changes each iteration (NOT loop-invariant) -> MUST stay sat
    char buf[100]; unsigned cnt = 0, i;
    for (i = 0; i < 10; i++) { buf[cnt] = 0; cnt += a[i]; }
    return 0;
}

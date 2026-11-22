// P2 interval-delta accumulator (BACKWARD_WP_P0_PLAN §3.x): a per-iteration-VARYING step `cnt += s` where each s has a
// STRUCTURAL constant upper bound M -- a byte read (zext from i8, M=255), a masked value (`x & 0xF`, M=15), or a URem by
// a constant. Each iteration then adds at most M, so cnt <= init0 + M*(iv - iv0): the trip-count bound even though the
// step is not fixed. (The probe has no interval domain, so only structurally-bounded steps are admitted -- a full-width
// unbounded step stays sat.) Source bytes come from fixed-size local arrays so src[i] is itself in-bounds, isolating the
// out[cnt] accumulator access as the check under test.

char ib_byte(void) {                    // byte step (M=255): out[2048], cnt <= 255*7 < 2048 -> SAFE
    unsigned char src[8]; char out[2048]; unsigned cnt = 0, i;
    for (i = 0; i < 8; i++) { out[cnt] = 0; cnt += src[i]; }
    return 0;
}

char ib_mask(void) {                    // masked step cnt += (x & 0xF) (M=15): out[200], cnt <= 15*7 < 200 -> SAFE
    unsigned src[8]; char out[200]; unsigned cnt = 0, i;
    for (i = 0; i < 8; i++) { out[cnt] = 0; cnt += src[i] & 0xF; }
    return 0;
}

char ib_small(void) {                   // byte step but out[100]: cnt can reach 255 > 100 -> out[cnt] MUST stay sat
    unsigned char src[8]; char out[100]; unsigned cnt = 0, i;
    for (i = 0; i < 8; i++) { out[cnt] = 0; cnt += src[i]; }
    return 0;
}

char ib_unbounded(void) {               // full 32-bit step, no structural bound -> out[cnt] MUST stay sat
    unsigned src[8]; char out[2048]; unsigned cnt = 0, i;
    for (i = 0; i < 8; i++) { out[cnt] = 0; cnt += src[i]; }
    return 0;
}

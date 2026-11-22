// P2 post-loop exit value (BACKWARD_WP_P0_PLAN §3.x): a loop counter / accumulator used AFTER the loop reads the loop's
// EXIT value, which the trip count bounds. For a unit-step induction counter i with const init and guard `i < N`, the
// exit value obeys  i0 <= i <= umax(N, i0)  (sound even with `break` exits, and for zero iterations). For a constant-
// step accumulator cnt of that loop,  cnt <= cnt0 + C*(i_exit - i0)  -- the `process(buf, cnt)` length idiom. Each case
// pins exactly what the exit-value bound must, and must NOT, prove.

char pl_iv_safe(void) {              // induction counter after the loop: i == 50 <= 63 -> SAFE
    char buf[64]; unsigned i;
    for (i = 0; i < 50; i++) buf[0] = 0;
    return buf[i];                    // post-loop: 0 <= i <= 50 < 64
}

char pl_acc_safe(void) {             // accumulator LENGTH after the loop: cnt <= 5*16 = 80 < 100 -> SAFE
    char buf[100]; unsigned i, cnt = 0;
    for (i = 0; i < 16; i++) cnt += 5;
    return buf[cnt];                  // post-loop: cnt <= 80 < 100
}

char pl_iv_oob(unsigned dummy) {     // buffer too small for the trip count: i <= 50 but buf[40] -> MUST stay sat
    char buf[40]; unsigned i;
    for (i = 0; i < 50; i++) buf[0] = (char)dummy;
    return buf[i];
}

char pl_nonstrict(void) {            // `<=` guard exits at 51, not 50: a non-strict bound is not emitted -> MUST stay sat
    char buf[51]; unsigned i;
    for (i = 0; i <= 50; i++) buf[0] = 0;
    return buf[i];
}

char pl_restore(unsigned n) {        // counter overwritten after the loop: the exit-value bound must NOT apply -> MUST stay sat
    char buf[64]; unsigned i;
    for (i = 0; i < 50; i++) buf[0] = 0;
    i = n;                            // post-loop re-store -> storesConfinedToLoop fails
    return buf[i];
}

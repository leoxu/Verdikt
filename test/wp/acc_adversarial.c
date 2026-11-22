/* 1. accumulator DOES overflow: buf too small -> MUST stay sat */
int acc_ovf(void) {
    char buf[40];
    unsigned cnt = 0;
    for (unsigned i = 0; i < 10; i++) { buf[cnt] = 0; cnt += 5; }  /* cnt up to 45 > 40 -> OOB -> sat */
    return 0;
}
/* 2. symbolic step: cnt += x, x unknown -> MUST stay sat */
int acc_sym(unsigned x) {
    char buf[100];
    unsigned cnt = 0;
    for (unsigned i = 0; i < 10; i++) { buf[cnt] = 0; cnt += x; }  /* x unbounded -> sat */
    return 0;
}
/* 3. iv incremented conditionally (not every iteration) -> invariant unsound if applied -> MUST stay sat */
int acc_condiv(unsigned flag) {
    char buf[20];
    unsigned cnt = 0, i = 0;
    while (i < 10) { buf[cnt] = 0; cnt += 5; if (flag) i += 1; }   /* i may not advance -> loop longer -> cnt huge */
    return 0;
}

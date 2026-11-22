int trip(void) {
    char buf[100];
    unsigned cnt = 0;
    for (unsigned i = 0; i < 10; i++) {   /* trip = 10 */
        cnt += 5;                          /* constant step 5, lockstep with i -> cnt == 5*i */
    }
    return buf[cnt];                       /* cnt == 50 after loop; needs cnt <= 5*10 -> buf[50] in buf[100] SAFE */
}
int trip_in(void) {
    char buf[100];
    unsigned cnt = 0;
    for (unsigned i = 0; i < 10; i++) {
        buf[cnt] = 0;                      /* cnt == 5*i, i<10 -> cnt<50 < 100 -> SAFE if cnt=5*i known */
        cnt += 5;
    }
    return 0;
}

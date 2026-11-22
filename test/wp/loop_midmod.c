int midmod(void) {
    int a[10];
    for (unsigned i = 0; i < 10; i++) {
        unsigned j = i + 1;   // j = i+1, up to 10
        a[j] = 0;             // a[10] when i=9 -> OOB. backward must NOT prove safe.
    }
    return a[0];
}
int midmod2(void) {
    int a[10];
    unsigned i = 0;
    while (i < 10) {
        i = i + 1;            // modify the induction slot IN the body, before the access
        a[i] = 0;             // a[10] when i was 9 -> i becomes 10 -> OOB
    }
    return a[0];
}

int fill_known(void) {
    int a[10];
    for (unsigned i = 0; i < 10; i++) a[i] = 0;   // i<10 guard + a[10] -> should be SAFE now
    return a[0];
}
int fill_bad(unsigned n) {
    int a[10];
    for (unsigned i = 0; i < n; i++) a[i] = 0;    // n unknown -> still sat
    return a[0];
}

int bounded1(unsigned i) {
    int a[10];
    if (i < 10) return a[i];   // single dominating guard (no &&, no phi) -> should be SAFE
    return -1;
}
int bad1(unsigned i) {
    int a[10];
    if (i < 20) return a[i];   // guard too loose -> still sat (i in [10,20) overflows)
    return -1;
}

int bounded(int i) {
    int a[10];
    if (i >= 0 && i < 10) {
        a[i] = 7;          // guarded: i in [0,10), a has 10 ints -> should be SAFE with path conditions
        return a[i];
    }
    return -1;
}
int unbounded(int i) {
    int a[10];
    a[i] = 7;              // no guard -> still sat (candidate)
    return a[i];
}

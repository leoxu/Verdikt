// P2 in-loop lower bound: a SIGNED induction counter is sign-extended into the pointer offset, so without a lower bound
// the oob V's `slt(offset, 0)` (negative-index) disjunct keeps even a bounded access `sat`. A unit-step induction var
// (or non-negative accumulator) never drops below its const init, so `init0 <=s i` discharges that disjunct; the step-3b
// guard `i < N` supplies the upper half.

int sidx_safe(void) {              // signed i in [0,50): i>=0 (lower bound) AND i<50 (guard) -> SAFE
    int a[50]; int i;
    for (i = 0; i < 50; i++) a[i] = 0;
    return a[0];
}

int sidx_down(void) {              // a DOWN counter is not a +1 induction var: no lower bound fires, and a[10] is a real
    int a[10]; int i;             // out-of-bounds write -> MUST stay sat (the lower bound must not over-apply)
    for (i = 10; i >= 0; i--) a[i] = 0;
    return a[0];
}

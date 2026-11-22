// seam③ differential-oracle fixture (test/wp/diff_oracle.py). Several UB kinds, each flagged by the forward scanner;
// the backward --solve verdict at each site must not CONTRADICT forward (backward SAFE where forward found a bug).
// Buffers are unknown-size pointer params on purpose, so the real UB stays a backward `sat` candidate -- the oracle
// then checks the two engines agree on danger, with zero contradictions.

int oob_guarded(int *a, int i) {
    if (i >= 0 && i < 4) return a[i];   // the guard does not bound a's size (a is a param) -> still a candidate
    return a[i];                         // unguarded index -> oob candidate
}

int div_zero(int x, int y) {
    return x / y;                        // div_by_zero candidate (y unconstrained)
}

int add_ovf(int x, int y) {
    return x + y;                        // signed_overflow candidate
}

int shift_amt(unsigned x, int s) {
    return (int)(x << s);                // shift_range candidate (s unconstrained)
}

int safe_stack(void) {
    int b[8];
    b[3] = 7;                            // in-bounds write into a known-size stack array:
    return b[3];                         // backward proves SAFE(unsat), forward finds nothing -> agree on safety
}

// Never an entry below, and never called by one -> the forward scan never enters it. Backward still enumerates
// its check and proves the bounded write SAFE. This is the seam③ UNCOVERED-BUCKET (BACKWARD_WP_DESIGN §3.3): a
// safety result on code forward cannot reach -- backward's unique payoff. The oracle asserts >=1 such site.
int unreached_safe(int i) {
    int c[16];
    if (i >= 0 && i < 16) c[i] = 1;      // compound guard + known-size array -> backward SAFE(unsat), in a never-entered fn
    return c[0];
}

// P2 coupled-counter invariant (BACKWARD_WP_P0_PLAN §3.x). The length-bounded byte copy `while (dn) { buf[up]=..; up++;
// dn--; }` couples an up-counter and a down-counter: the body runs at most dn0 (the down-counter's initial value) times,
// so up <= up0 + C*dn0 even though the loop GUARD is on dn, not up. When dn0 is bounded (here via the interprocedural
// return summary on the callee that produces it), the indexed write proves SAFE. This is the shape of the brotli CVE's
// tail-copy -- which stays sat here precisely because in brotli dn0 (GetAvailIn) is genuinely unbounded.

unsigned ret7(const unsigned char *p)  { return p[0] & 7; }     // <= 7
unsigned ret15(const unsigned char *p) { return p[0] & 15; }    // <= 15

char dc_safe(const unsigned char *in) {        // dn0 = ret7() <= 7, so up <= 7 < 8 -> SAFE
    unsigned char buf[8]; unsigned i = 0, avail = ret7(in);
    while (avail) { buf[i] = *in; i++; in++; avail--; }
    return buf[0];
}

char dc_unbounded(const unsigned char *in, unsigned n) {   // dn0 = n is unbounded -> MUST stay sat (the brotli shape)
    unsigned char buf[8]; unsigned i = 0, avail = n;
    while (avail) { buf[i] = *in; i++; in++; avail--; }
    return buf[0];
}

char dc_toobig(const unsigned char *in) {      // dn0 = ret15() <= 15 but buf[8]: up can reach 15 -> MUST stay sat
    unsigned char buf[8]; unsigned i = 0, avail = ret15(in);
    while (avail) { buf[i] = *in; i++; in++; avail--; }
    return buf[0];
}

char dc_reset(const unsigned char *in, unsigned m) {   // avail re-stored inside the loop -> not a clean down-counter -> sat
    unsigned char buf[8]; unsigned i = 0, avail = ret7(in);
    while (avail) { buf[i] = *in; i++; in++; avail--; if (m) avail = m; }
    return buf[0];
}

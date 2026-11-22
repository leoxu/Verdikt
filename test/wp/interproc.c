// Interprocedural WP -- bounded-return summary (BACKWARD_WP_P0_PLAN §3.x). A `core.call` result was modelled as a
// fresh unconstrained value (call_ret root), so any check indexing with a callee's return stayed sat. The summary
// constrains the result by a SOUND upper bound computed from the callee's return sites: if EVERY return is a constant
// or a structurally-bounded value (zext from a narrow type, x & mask, x % c), the result is <= max(those bounds). One
// unbounded return site defeats the whole summary (sound: the result could then be anything).

unsigned clamp3(unsigned x)  { return x & 7; }      // returns 0..7
unsigned ident(unsigned x)   { return x; }          // unbounded
unsigned clamp15(unsigned x) { return x & 15; }     // returns 0..15
unsigned maybe(unsigned x, int f) { if (f) return x & 7; return x; }  // one return unbounded -> NO summary

char ip_safe(unsigned k)      { char buf[8]; return buf[clamp3(k)]; }    // idx <= 7 < 8 -> SAFE
char ip_unbounded(unsigned k) { char buf[8]; return buf[ident(k)]; }     // unbounded return -> MUST stay sat
char ip_toobig(unsigned k)    { char buf[8]; return buf[clamp15(k)]; }   // idx <= 15 into buf[8] -> MUST stay sat
char ip_mixed(unsigned k, int f) { char buf[8]; return buf[maybe(k, f)]; }  // one unbounded return -> MUST stay sat

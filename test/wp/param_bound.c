// Interprocedural parameter-bound summary (BACKWARD_WP_P0_PLAN §3.x). A parameter is a fresh unconstrained value, so a
// check that indexes/shifts with a parameter stays sat. For an INTERNAL (C `static`) function -- all callers are in the
// module, marked `internal` in the core by the frontend -- that is not address-taken and whose EVERY direct call site
// passes a structurally-bounded argument, the parameter is bounded by the meet over those call sites (sound: those are
// ALL the callers). An external function could be called from outside with any argument, so its parameters stay free.

static char pick(unsigned i)   { char t[16]; t[0] = 1; return t[i]; }  // internal; every caller passes <= 7 -> t[i] SAFE
static char pick_u(unsigned i) { char t[16]; t[0] = 1; return t[i]; }  // internal; one caller passes an unbounded arg -> sat
static char pick_w(unsigned i) { char t[16]; t[0] = 1; return t[i]; }  // internal; a caller passes 31 (> 16) -> sat
char        ext_pick(unsigned i){ char t[16]; t[0] = 1; return t[i]; }  // EXTERNAL; params arbitrary -> sat

char pb_driver(unsigned k) {
    return pick(3) + pick(7)          // pick: all call args <= 7 < 16 -> SAFE
         + pick_u(3) + pick_u(k)      // pick_u: k is unbounded -> no bound -> sat
         + pick_w(3) + pick_w(31)     // pick_w: 31 >= 16 -> t[i] can be OOB -> sat
         + ext_pick(3);               // ext_pick is external -> not summarised -> sat
}

// `queried == 0` with a large `reached` is reported as a warning (DESIGN.md §22.413). It is the signature
// of §22.388 -- a missing source file left two helpers opaque, taint died at every conversion, 575875
// memory-safety checks were settled without a single solver query, and the defect was found by stumbling
// rather than solving. Two wrong diagnoses were written before anyone looked at that number, and finding it
// used to need a hand-written `python3 -c` over the JSON.
//
// Both halves are here because the warning has to be silent on healthy code, not just loud on sick code.
//
//   demo_neversym  the index is a concrete loop counter, so every bounds check is decided concretely
//                  -> the warning must FIRE
//   demo_symindex  the index comes from the attacker's buffer, so the checks are handed to the solver
//                  -> the warning must stay SILENT

int demo_neversym(const char *buf, unsigned n)
{
    char     sink = 0;
    unsigned i;

    if (n < 4) {
        return -1;
    }
    for (i = 0; i < 2000; i++) {
        sink = (char) (sink ^ buf[i & 3]);   /* index concrete; only the CONTENTS are tainted */
    }
    return sink;
}

int demo_symindex(const char *buf, unsigned n)
{
    char     sink = 0;
    unsigned i;

    if (n < 8) {
        return -1;
    }
    for (i = 0; i < 2000; i++) {
        sink = (char) (sink ^ buf[(unsigned char) buf[0] & 7]);   /* index comes FROM the attacker */
    }
    return sink;
}

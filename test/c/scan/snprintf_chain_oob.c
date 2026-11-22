// Mirrors the real triggering mechanism of CVE-2017-7376 (libxml2 nanohttp.c's xmlNanoHTTPMethodRedir(), see
// docs/DESIGN.md Sec.22.205/22.298): chained `p += snprintf(p, remaining, ...)` calls to build up a message,
// relying on snprintf's return value being "the length that WOULD have been written" (independent of and not
// capped by the `remaining` argument) to advance the write pointer. If the model's return value is a hardcoded 0
// (the pre-fix behaviour), `p` never advances and this real bug class is structurally unreachable.
//
// The pieces that advance `p` are `%s` of an ATTACKER-CONTROLLED string, which is what the CVE actually is: the
// redirect URL's length is what drives the pointer out of the buffer. It is also the case the printf closed form
// (Sec.22.439) must DECLINE -- the bytes are symbolic, so there is no length to compute and the bounded nondet
// return is still what this call gets. Before Sec.22.439 this fixture used a constant format with no arguments,
// `snprintf(p, remaining, "a")`, whose return is simply 1: the model's inability to say so was the only reason
// that version ever reported a bug, and a scanner that folds correctly now says what the real program does.
#include <stdio.h>

void consume(const char *name) {
  char buf[8];
  char *p = buf;
  int remaining = sizeof(buf);
  // Two chained calls, each advancing p by the would-be length of an attacker string. A real-world caller trusts
  // the "would-be length" contract and never re-validates p against buf's real bounds in between.
  p += snprintf(p, remaining, "%s", name);
  p += snprintf(p, remaining, "%s", name);
  // By now p may already be past buf's end. This call's %buf argument is that advanced p -- and the write it
  // performs is what catches the out-of-bounds write.
  snprintf(p, remaining, "c");
}

// The other half of the same question: with everything concrete the engine must report the REAL length, not a
// nondet that can be anything up to 64KiB. `use_folded` has no defect at all, and before Sec.22.439 it had one --
// the model let the first call's return be large enough to push `p` out of `buf`.
int use_folded(void) {
  char buf[16];
  char *p = buf;
  p += snprintf(p, sizeof buf, "%s", "ab");   /* exactly 2 */
  p += snprintf(p, 4, "%d", 7);               /* exactly 1 */
  *p = 0;
  return (int)(p - buf);                      /* 3 */
}

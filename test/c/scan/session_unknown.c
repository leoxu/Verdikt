// A `session` object's bytes are the DRIVER's, not zero (DESIGN.md §22.381). Measured on a QNX resource manager:
// every handler returned its error path before reaching any of its real work, because the module's own validity
// gate (`gpio_attr->magic == <DRIVER>_MACRO`) is a field of the session and a synthesised session is all zeroes --
// a state the module's constructor can never produce and which therefore makes the gate unsatisfiable. Coverage
// was 7-12% and no entry got past its first `if`. `content: unknown` gives those bytes symbolic,
// harness-labelled values instead: the gate becomes satisfiable, and a finding that rests ONLY on such a byte is
// reported harness_only rather than as a defect anyone should chase.
#include <stdint.h>

#define SU_MAGIC 0x5A5A1234u

struct su_session {
  uint32_t magic;
  uint32_t limit;
};

// The defect behind the gate is driven by the ATTACKER's buffer, not by the session: once the gate can open, this
// is an ordinary out-of-bounds write and must be reported as reproducible from a real input.
int demo_su_gated(struct su_session *s, const uint8_t *msg, int n) {
  char out[8];
  if (!s || s->magic != SU_MAGIC) return -1;   // unsatisfiable against a zero-filled session
  if (n < 1) return -2;
  out[msg[0]] = 1;                             // OOB: msg[0] is attacker data, 0..255 against an 8-byte object
  return 0;
}

// ...whereas a defect decided ONLY by a session byte is the harness's own invention: `limit` is a field nobody in
// this scan ever wrote, so a report that calls this a defect would send a reader after a state no caller can set.
int demo_su_sessiononly(struct su_session *s) {
  char out[8];
  if (!s || s->magic != SU_MAGIC) return -1;
  out[s->limit & 0x3f] = 2;                    // OOB decided entirely by an invented byte
  return 0;
}

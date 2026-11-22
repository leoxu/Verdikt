/* LLM-assisted witness distillation -- the target (experiments/llm-witness-distill/README.md).
 *
 * A medium-difficulty bug: 6 attacker bytes run through a non-obvious mixing loop; a specific 32-bit
 * result gates an out-of-bounds write. Hitting the gate by luck is 2^-32, so fuzzing cannot reach it;
 * but once the loop is DISTILLED into an SMT problem the cone is tiny and a solver inverts it instantly.
 *
 * NOTE: this target is hand-written (a controlled stand-in for "a real symbolic loop"). What is genuine
 * is the distill->solve->verify loop: the model is cross-checked against these C semantics, the solver
 * finds a real preimage, and the witness is confirmed on the compiled binary under UBSan.
 *
 * Scan with: hlir-scan --link --dump-linked t.core --entry harness target.c
 * Backward WP (hlir-wp-probe --list --solve t.core) reports the buf[200] write as sat(candidate):
 * it cannot prove it safe, and the obligation is to reach the gate `(a^b) == MAGIC`.
 */
#include <stdint.h>
#include <stddef.h>

#define MAGIC 0x370dd88fu   /* a REACHABLE target (= the loop's output for some input; see solve.py) */

void parse(const uint8_t *in) {
    uint32_t a = 0x1234u, b = 0u;
    for (int i = 0; i < 6; i++) {
        a = (a << 5) + a + in[i];     /* a = a*33 + byte  (uint32 wrap) */
        b ^= a + (b >> 3);            /* b >> 3 is logical; uint32 wrap  */
    }
    if ((a ^ b) == MAGIC) {           /* the magic gate -- fuzzing-infeasible */
        char buf[16];
        buf[200] = 7;                 /* out-of-bounds write, only on the gated path */
    }
}

int harness(const uint8_t *data, size_t n) { if (n >= 6) parse(data); return 0; }

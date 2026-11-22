/* LLM-assisted witness distillation -- the verify step (ground-truth adjudication).
 *
 * Runs target.c's parse() on the witness the solver found and lets the sanitizer adjudicate: the model is
 * never trusted, the real binary is. The witness below is solve.py's output for MAGIC == 0x370dd88f.
 *
 * Build & run:
 *   gcc -fsanitize=address,undefined -fno-sanitize-recover=all -g verify.c -o verify && ./verify
 * Expected:
 *   verify.c:...: runtime error: index 200 out of bounds for type 'char [16]'
 */
#include <stdint.h>

#define MAGIC 0x370dd88fu

void parse(const uint8_t *in) {
    uint32_t a = 0x1234u, b = 0u;
    for (int i = 0; i < 6; i++) {
        a = (a << 5) + a + in[i];
        b ^= a + (b >> 3);
    }
    if ((a ^ b) == MAGIC) {
        char buf[16];
        buf[200] = 7;                 /* out-of-bounds write, reached only via the solved witness */
    }
}

int main(void) {
    uint8_t witness[6] = {0x0c, 0xc4, 0x97, 0x24, 0xe8, 0xd5};  /* solve.py's preimage of MAGIC */
    parse(witness);
    return 0;
}

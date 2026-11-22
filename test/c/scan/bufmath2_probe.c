/* §22.450 probe 2. Probe 1 showed the engine models the pointer arithmetic correctly, so the question
 * moved to `n`. In the engine the branch is classified `const` -- NOT symbolic -- which means both
 * operands were concrete on every path. In the real program `n` is `st->length`, written into a HEAP
 * STATE STRUCT by parse_prefix_int from attacker bytes and read back by parse_literal on a later call.
 * If taint is lost on that round trip, `n` is concrete and the branch folds, which is exactly what is
 * observed. This probe is probe 1 with that round trip added and nothing else. */
#include <stdlib.h>
#include <string.h>

typedef struct { unsigned char *pos, *last, *end, *start; } probe_buf_t;
typedef struct { probe_buf_t *buf; unsigned length; unsigned state; } probe_st_t;

unsigned long hx_probe2_sink;

/* mirrors ngx_http_v3_parse_literal's sw_start: n comes from the state struct, not from a parameter */
static int step2(probe_st_t *st)
{
    unsigned n = st->length;
    if ((size_t) (st->buf->end - st->buf->last) < (size_t) n + 1) {
        return 1;
    }
    st->buf->last += n + 1;
    return 0;
}

int hx_bufmath2(const unsigned char *in, unsigned int in_len)
{
    probe_buf_t *b;
    probe_st_t  *st;
    int r1, r2;

    if (in_len < 2) return -1;

    b = calloc(1, sizeof(probe_buf_t));
    st = calloc(1, sizeof(probe_st_t));
    if (b == NULL || st == NULL) return -1;
    b->start = malloc(32);
    if (b->start == NULL) return -1;
    b->pos = b->last = b->start;
    b->end = b->start + 32;
    st->buf = b;

    st->length = in[0];        /* attacker byte -> heap struct field */
    r1 = step2(st);            /* the name literal */

    st->length = in[1];        /* and again, as parse_field_iln does for the value */
    r2 = step2(st);

    hx_probe2_sink += (unsigned long) (b->last - b->start);
    free(b->start); free(b); free(st);
    return (r1 << 1) | r2;
}

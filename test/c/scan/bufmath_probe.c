/* §22.450 probe. The open question is whether the engine models the two operations
 * ngx_http_v3_parse_literal performs on the dynamic table's insert buffer:
 *
 *     avail = (size_t) (st->buf->end - st->buf->last);   // same-object pointer subtraction
 *     st->buf->last += n + 1;                            // the advance, across two calls
 *
 * This entry does exactly those and nothing else. If the engine covers BOTH directions of the
 * comparison, the model is fine and the discrepancy is elsewhere. If it only ever takes one, the model
 * is the cause. Two calls to `step` so the advance has to persist between them, like the name and the
 * value literal of one Insert With Literal Name instruction. */
#include <stdlib.h>
#include <string.h>

typedef struct { unsigned char *pos, *last, *end, *start; } probe_buf_t;

unsigned long hx_probe_sink;

static probe_buf_t *mk(size_t size)
{
    probe_buf_t *b = calloc(1, sizeof(probe_buf_t));
    if (b == NULL) return NULL;
    b->start = malloc(size ? size : 1);
    if (b->start == NULL) { free(b); return NULL; }
    b->pos = b->last = b->start;
    b->end = b->start + size;
    return b;
}

/* returns 1 when the carve is refused, 0 when it is taken -- the shape of parse_literal:638 */
static int step(probe_buf_t *b, unsigned n)
{
    if ((size_t) (b->end - b->last) < (size_t) n + 1) {
        return 1;
    }
    b->last += n + 1;
    return 0;
}

int hx_bufmath(const unsigned char *in, unsigned int in_len)
{
    probe_buf_t *b;
    int r1, r2;

    if (in_len < 2) return -1;

    b = mk(32);                      /* HX_V3CAP's 32, as a concrete size */
    if (b == NULL) return -1;

    r1 = step(b, in[0]);             /* the name literal */
    r2 = step(b, in[1]);             /* the value literal, which must see the advance */

    hx_probe_sink += (unsigned long) (b->last - b->start);
    free(b->start);
    free(b);
    return (r1 << 1) | r2;
}

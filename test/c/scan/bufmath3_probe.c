/* §22.450 probe 3. Probes 1 and 2 cleared the pointer arithmetic and the heap-state round trip. What is
 * left between the attacker's bytes and `n` is ngx_http_v3_parse_prefix_int's accumulation:
 *     st->pint.value += (uint64_t) (ch & 0x7f) << st->pint.shift;   with st->pint.shift += 7 per continuation byte
 * carried in a heap struct across calls. This probe is probe 2 with that accumulation in front of it. */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { unsigned char *pos, *last, *end, *start; } probe_buf_t;
typedef struct { uint64_t value; unsigned shift; unsigned state; } probe_pint_t;
typedef struct { probe_buf_t *buf; unsigned length; probe_pint_t pint; } probe_st_t;

unsigned long hx_probe3_sink;

/* mirrors parse_prefix_int: a 5-bit prefix, then 0x80-continued bytes, accumulating into the struct */
static int pint(probe_st_t *st, const unsigned char *p, unsigned len, unsigned *used)
{
    unsigned i = 0;
    unsigned char ch;

    if (len == 0) return 0;
    ch = p[i++];
    st->pint.value = ch & 0x1f;
    st->pint.shift = 0;
    if ((ch & 0x1f) != 0x1f) { *used = i; return 1; }

    while (i < len) {
        ch = p[i++];
        st->pint.value += (uint64_t) (ch & 0x7f) << st->pint.shift;
        if ((ch & 0x80) == 0) { *used = i; return 1; }
        st->pint.shift += 7;
        if (st->pint.shift > 56) return -1;
    }
    *used = i;
    return 0;
}

static int step3(probe_st_t *st)
{
    unsigned n = st->length;
    if ((size_t) (st->buf->end - st->buf->last) < (size_t) n + 1) return 1;
    st->buf->last += n + 1;
    return 0;
}

int hx_bufmath3(const unsigned char *in, unsigned int in_len)
{
    probe_buf_t *b;
    probe_st_t  *st;
    unsigned used = 0, off = 0;
    int r1, r2, rc;

    if (in_len < 2) return -1;

    b = calloc(1, sizeof(probe_buf_t));
    st = calloc(1, sizeof(probe_st_t));
    if (b == NULL || st == NULL) return -1;
    b->start = malloc(32);
    if (b->start == NULL) return -1;
    b->pos = b->last = b->start;
    b->end = b->start + 32;
    st->buf = b;

    rc = pint(st, in + off, in_len - off, &used);
    if (rc != 1) { free(b->start); free(b); free(st); return -2; }
    off += used;
    st->length = (unsigned) st->pint.value;      /* exactly what parse_field_iln does */
    r1 = step3(st);

    if (off >= in_len) { free(b->start); free(b); free(st); return -3; }
    rc = pint(st, in + off, in_len - off, &used);
    if (rc != 1) { free(b->start); free(b); free(st); return -4; }
    st->length = (unsigned) st->pint.value;
    r2 = step3(st);

    hx_probe3_sink += (unsigned long) (b->last - b->start);
    free(b->start); free(b); free(st);
    return (r1 << 1) | r2;
}

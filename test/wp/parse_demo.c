#include <string.h>
#include <stdint.h>

struct hdr { uint16_t len; uint8_t kind; };

/* §2.1 canonical: a loop accumulates cnt, then a memcpy uses it. S should be {cnt}-ish. */
int copy_records(const struct hdr *recs, unsigned n, char *dst, const char *src) {
    unsigned cnt = 0;
    for (unsigned i = 0; i < n; i++) {
        cnt += recs[i].len;          /* cnt: loop-carried accumulator; recs[i].len: struct-field load in loop */
    }
    memcpy(dst, src, cnt);           /* V: cnt > sizeof(dst). dependency = {cnt} */
    return 0;
}

/* array index = a parsed struct field (struct-chained offset) */
int index_by_field(const struct hdr *h, int *table) {
    return table[h->kind];           /* oob offset = h->kind, one load */
}

/* nested: offset depends on two inputs through arithmetic */
int two_inputs(int *a, int i, int j) {
    return a[i * 8 + j];             /* oob offset depends on {i, j} */
}

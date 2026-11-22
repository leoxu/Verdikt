/* An array of structs sized by a sibling COUNT field (DESIGN.md §22.352, found on FreeType's
 * `TT_FaceRec { FT_UShort num_tables; TT_Table dir_tables; }` walked as `limit = entry + face->num_tables`).
 * Without `size: {from_field: {..., elem: N}}` the array is synthesized as exactly one element while the count
 * stays free, so every walk of it runs off the end -- 20 confirmed ptr_arith_oob at ttload.c:75 in one scan. */
#include <stddef.h>

struct table { unsigned int tag; unsigned int sum; unsigned int off; unsigned int len; };  /* 16 bytes, no pointers */

/* the count names only the TAIL of the pointer's name: dir_tables <- num_tables */
struct face {
	unsigned short num_tables;
	struct table *dir_tables;
};

/* the ordinary name-composed shape: items <- num_items */
struct holder {
	unsigned int num_items;
	struct table *items;
};

/* a bare `count` beside a struct pointer that is NOT an array: pairing it would size `ctx` as
 * `count * 16`, which can come out smaller than the single object it really points to */
struct plain {
	unsigned int count;
	struct table *ctx;
};

unsigned int walk_tables(struct face *f)
{
	struct table *e = f->dir_tables, *limit = e + f->num_tables;
	unsigned int sum = 0;

	for ( ; e < limit; e++ )
		sum += e->tag;
	return sum;
}

unsigned int walk_items(struct holder *h)
{
	unsigned int sum = 0, i;

	for (i = 0; i < h->num_items; i++)
		sum += h->items[i].tag;
	return sum;
}

unsigned int read_ctx(struct plain *p)
{
	return p->ctx->tag + p->ctx->len;
}

/* Witness object-id attribution (DESIGN.md §22.351, found on fs/jfs dbJoin).
 *
 * `outer` has a pointer field that the body dereferences, so entry synthesis allocates a sub-object for it
 * BETWEEN the two parameter objects. The printer used to guess the object id from the parameter's position
 * among the buffer parameters, so `h`'s bytes were looked up under the sub-object's name and rendered as
 * "all bytes 0" -- a witness that cannot reach the very finding it is attached to. */
#include <stddef.h>

struct outer {
	unsigned char *inner;
	unsigned int misc;
};

struct hdr {
	unsigned int nleafs;
	unsigned int leafidx;
	unsigned char pad[8];
	signed char tree[16];
};

/* the out-of-bounds read depends only on `h`'s bytes: `nleafs` has to exceed 4 and `leafidx` has to run off `tree` */
int probe_objid(struct outer *o, struct hdr *h)
{
	signed char *leaf = h->tree + h->leafidx;
	int sum = o->inner[0];
	if (h->nleafs > 4)
		sum += leaf[1];
	return sum;
}

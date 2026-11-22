/* The count of an INLINE fixed array (DESIGN.md §22.356, found on FreeType's
 * `CFF_PrivateRec { FT_Fixed blue_values[14]; FT_Byte num_blue_values; }`, walked as
 * `for (i = 0; i < num_blue_values; i += 2) ... zone[count++] = blue_values[i]`). The array is a member, not a
 * pointer field, so no size mechanism reaches it; what is missing is the bound the real producer enforces --
 * FreeType's CFF parser caps the count at 14 via CFF_FIELD_DELTA_FIXED(6, blue_values, 14, ...), while a
 * synthesized private_dict leaves the FT_Byte free to 255. */
#include <stddef.h>

struct priv {
	long          blue_values[14];
	unsigned char num_blue_values;
};

/* the sub-object shape: the counted struct hangs off a pointer field, one level down */
struct font {
	struct priv *dict;
	unsigned int tag;
};

/* a NEGATIVE: `limit` is not composed from `slots`, so nothing says it bounds that array */
struct loose {
	long         slots[8];
	unsigned int limit;
};

/* a NEGATIVE: the bound would be the type's own maximum, so stating it adds nothing */
struct wide {
	unsigned char bytes[256];
	unsigned char num_bytes;
};

long sum_blues(struct priv *p)
{
	long s = 0;
	unsigned int i;

	for (i = 0; i < p->num_blue_values; i++)
		s += p->blue_values[i];
	return s;
}

long sum_dict(struct font *f)
{
	long s = 0;
	unsigned int i;

	for (i = 0; i < f->dict->num_blue_values; i++)
		s += f->dict->blue_values[i];
	return s + f->tag;
}

long sum_loose(struct loose *l)
{
	long s = 0;
	unsigned int i;

	for (i = 0; i < l->limit; i++)
		s += l->slots[i];
	return s;
}

/* only the generated spec matters for this one (no bound is worth stating), so it does not walk the array --
 * a 255-iteration symbolic loop costs the test suite more than the case is worth */
long sum_wide(struct wide *w)
{
	return w->bytes[w->num_bytes];
}

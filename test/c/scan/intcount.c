/* An array of WIDER INTEGERS sized by a sibling count (DESIGN.md §22.355, found on FreeType's
 * `FT_Outline { unsigned short n_contours; ...; unsigned short *contours; }`, which its own documentation
 * calls "an array of n_contours shorts"). Unpaired it gets a free size range while the count runs to 65535,
 * so `outline->contours[n_contours - 1] = ...` is an out-of-bounds write that no real program can perform.
 * Only an unambiguous COUNT spelling may size it: reading a BYTE length as a count would make the object
 * `sizeof(element)` times too big and hide a real overrun instead of inventing one. */
#include <stddef.h>

/* the FT_Outline shape: `n_<field>` is a count of elements */
struct outline {
	unsigned short  n_contours;
	unsigned short *contours;
};

/* a NEGATIVE: `_len` is a byte length, not an element count -- pairing it as a count would quadruple the object */
struct packet {
	unsigned int  words_len;
	unsigned int *words;
};

/* a NEGATIVE: a bare `length` is a byte length too (the Heartbleed shape, which stays bytes-only) */
struct record {
	unsigned int   length;
	unsigned long *slots;
};

/* a byte buffer must keep exactly the plain byte-count form it had before */
struct blob {
	unsigned int   data_len;
	unsigned char *data;
};

unsigned int last_contour(struct outline *o)
{
	if (!o->n_contours)
		return 0;
	return o->contours[o->n_contours - 1];
}

unsigned int last_word(struct packet *p)
{
	return p->words[0];
}

unsigned long last_slot(struct record *r)
{
	return r->slots[0];
}

unsigned int first_byte(struct blob *b)
{
	return b->data_len ? b->data[0] : 0u;
}

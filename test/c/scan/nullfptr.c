/* An OPTIONAL callback field (DESIGN.md §22.353, found on FreeType's `FT_StreamRec.read`, which is NULL for a
 * memory stream and tested in 13 places). Synthesized as always-non-NULL, every call through `read` dispatches
 * into the one real implementation with state nobody set up, and the branch a real caller actually takes --
 * the one that reads the buffer directly -- is never explored. The gate is the code itself: `read` is tested
 * for NULL here, `fill` never is, so only `read` may be synthesized as NULL. */
#include <stddef.h>

struct io {
	unsigned int (*read)(struct io *s, unsigned int n);   /* optional: tested for NULL below */
	unsigned int (*fill)(struct io *s);                   /* never tested: a real io always has it */
	unsigned char *base;
	unsigned int size;
	unsigned int pos;
};

static unsigned int zip_read(struct io *s, unsigned int n)
{
	return s->pos + n;
}

static unsigned int zip_fill(struct io *s)
{
	return s->size;
}

/* takes both addresses, so both fields have a candidate target and neither is dropped for lack of one */
unsigned int (*nullfptr_pick_read(void))(struct io *, unsigned int) { return zip_read; }
unsigned int (*nullfptr_pick_fill(void))(struct io *) { return zip_fill; }

unsigned int nullfptr_fetch(struct io *s, unsigned int n)
{
	if (s->read)
		return s->read(s, n);
	/* the memory-stream path: unreachable while `read` can never be NULL. `n` is free and so is the
	 * object behind `base`, so this is a genuine out-of-bounds read of the synthesized input. */
	return s->base[n] + s->fill(s);
}

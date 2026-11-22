/* The (base, cursor, limit) idiom: several pointer fields of one struct that all walk ONE buffer
 * (DESIGN.md §22.354, found on FreeType's `PS_ParserRec { FT_Byte *cursor, *base, *limit; }` and
 * `FT_ValidatorRec { const FT_Byte *base, *limit; }`). Synthesized as independent allocations,
 * `while (cur < limit)` compares pointers into unrelated objects -- 11 confirmed ptr_cmp_diff_obj
 * at psobjs.c:286 in one scan, and the bound test means nothing. */
#include <stddef.h>

/* the parser shape: the cursor is declared BEFORE the base it walks */
struct parser {
	unsigned char *cursor;
	unsigned char *base;
	unsigned char *limit;
	int error;
};

/* the validator shape: just the two boundaries */
struct validator {
	const unsigned char *base;
	const unsigned char *limit;
};

/* the stream shape: base, cursor and limit ALL have a plausible sibling length (`size`), so each of them used to
 * get its own object of that size -- three separate allocations, and `cursor < limit` still cross-object. Being a
 * view has to win over a derived size. This is FreeType's `FT_StreamRec` verbatim. */
struct stream {
	unsigned char *base;
	unsigned long  size;
	unsigned char *cursor;
	unsigned char *limit;
};

/* a NEGATIVE: `limit` here points at a different element type, so it is a second buffer, not a view */
struct mixed {
	unsigned char *base;
	unsigned long *limit;
};

unsigned int scan_spaces(struct parser *p)
{
	unsigned char *cur = p->cursor;
	unsigned int n = 0;

	while (cur < p->limit) {
		if (*cur != ' ')
			break;
		cur++;
		n++;
	}
	p->cursor = cur;
	/* a real parser also reports how far it has come, which is what keeps `base` alive: a field no visible
	 * code reads is pruned, and with the owner gone its cursor and limit stay independent objects */
	return n + (unsigned int)(cur - p->base);
}

unsigned int span_len(struct validator *v)
{
	return (unsigned int)(v->limit - v->base);
}

unsigned long read_mixed(struct mixed *m)
{
	return m->base[0] + m->limit[0];
}

unsigned int stream_span(struct stream *s)
{
	unsigned int n = 0;

	while (s->cursor < s->limit) {
		n += *s->cursor;
		s->cursor++;
	}
	return n + (unsigned int)(s->limit - s->base) + (unsigned int)s->size;
}

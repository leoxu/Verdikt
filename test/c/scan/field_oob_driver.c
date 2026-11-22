#include <stdlib.h>

/* ---- true positive: unchecked index into a fixed-size struct field overflows into the adjacent field ---- */
#define N_SLOTS 4
struct Ctx { void *slots[N_SLOTS]; void *node; long version; };

void bug_field_write(struct Ctx *ctx, unsigned idx)
{
	ctx->slots[idx] = (void *)0; /* idx is attacker-controlled, no bound check */
}

void safe_field_write(struct Ctx *ctx, unsigned idx)
{
	if (idx >= N_SLOTS) return;
	ctx->slots[idx] = (void *)0;
}

/* ---- regression: flexible array member ("struct hack") must not be flagged ---- */
struct FamHolder { int n; char data[1]; };

void fam_write(unsigned idx)
{
	struct FamHolder *h = malloc(sizeof(struct FamHolder) + 64);
	if (!h) return;
	h->data[idx] = 'x'; /* legitimately indexes past data[1] into the over-allocated storage */
}

/* ---- regression: union members must not be flagged (overlapping access is valid C) ---- */
union U { int arr[2]; long wide; };

void union_write(union U *u, unsigned idx)
{
	u->arr[idx] = 0; /* idx up to 3 stays within the union's own 8-byte size even though arr[] is declared [2] */
}

/* ---- historical-bug closure: Redis modules/vector-sets/hnsw.c's random_level()/InsertContext, §22.235-adjacent
 * P1 gap write-up in docs/KNOWN_GAPS_PRIORITIZED.md. level_queues[HNSW_MAX_LEVEL] is the struct's first field,
 * immediately followed by `node`; pre-fix, level can reach HNSW_MAX_LEVEL itself (one past the valid
 * 0..HNSW_MAX_LEVEL-1 range), so `level_queues[level] = candidates` overwrites `node` -- a real type-confusion
 * memory corruption that core.check.oob alone cannot see (the write stays inside the whole InsertContext
 * allocation). */
#define HNSW_MAX_LEVEL 16
struct InsertContext { void *level_queues[HNSW_MAX_LEVEL]; void *node; long version; };

static int random_level_raw(unsigned threshold_hits)
{
	int level = 0;
	while (threshold_hits-- > 0 && level < HNSW_MAX_LEVEL) level += 1;
	return level; /* pre-fix: can return HNSW_MAX_LEVEL itself */
}

static int random_level_fixed(unsigned threshold_hits)
{
	int level = random_level_raw(threshold_hits);
	if (level >= HNSW_MAX_LEVEL) level = HNSW_MAX_LEVEL - 1;
	return level;
}

void hnsw_insert_bug(struct InsertContext *ctx, void *candidates, unsigned threshold_hits)
{
	int level = random_level_raw(threshold_hits);
	ctx->level_queues[level] = candidates;
}

void hnsw_insert_fixed(struct InsertContext *ctx, void *candidates, unsigned threshold_hits)
{
	int level = random_level_fixed(threshold_hits);
	ctx->level_queues[level] = candidates;
}

/* ---- regression: the index is checked at its value, not its width. An `unsigned char` index into a 256-entry
 * field can never be out of bounds (expat's tokenizer: `((struct normal_encoding *)enc)->type[(unsigned char)*p]`);
 * comparing it at 8 bits against 256 truncated the bound to 0 and flagged every access. A `signed char` index is
 * still out of bounds when negative. */
struct ByteTable { unsigned char type[256]; int after; };

int byte_class(struct ByteTable *t, unsigned char c)
{
	return t->type[c];
}

int byte_class_signed(struct ByteTable *t, signed char c)
{
	return t->type[c];
}

/* ---- regression: `&field[n]` only forms the one-past-the-end pointer, which is valid (C11 6.5.3.2p3, 6.5.6p8):
 * expat's siphash.h `sip_endof(H->buf)` is `&(H->buf)[sizeof H->buf]`. One further is still out of bounds. */
struct Sip { unsigned long long v; unsigned char buf[8], *p; };

int sip_room(struct Sip *h)
{
	h->p = h->buf + 3;
	return h->p < &h->buf[8];
}

int sip_past(struct Sip *h, unsigned i)
{
	h->p = h->buf + 3;
	return h->p < &h->buf[i];
}

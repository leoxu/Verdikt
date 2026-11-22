#include <stdlib.h>

/* ---- true positive: a pointer born from an arbitrary integer cast (core.int_to_ptr of a value that isn't a
 * recoverable object id -- see IntToPtr in lib/semantics/Machine.h) keeps object 0 with its real, possibly
 * nonzero, offset. `raw != 0` must therefore be reachable for any nonzero `raw`, and the dereference on that
 * path is a genuine null_deref (object 0 is never a real allocation, whatever the offset). Pre-fix, HLIR's
 * `ptr == 0`/`ptr != 0` lowering used core.is_null (object-id-only), which is wrongly true whenever object is 0
 * regardless of offset, so this whole branch looked unreachable and the bug was invisible. */
void bug_int2ptr_deref(unsigned long raw)
{
	int *p = (int *)raw;
	if (p != 0) {
		*p = 1; /* raw can be any nonzero value: an unsafe dereference that must be found */
	}
}

/* ---- regression: same int-to-pointer+compare shape, but never dereferenced -- must stay safe ---- */
void safe_int2ptr_noderef(unsigned long raw)
{
	int *p = (int *)raw;
	if (p != 0) {
		(void)p;
	}
}

/* ---- regression: the bare-truthiness and logical-not spellings of the same idiom (`if (p)`, `if (!p)`) go
 * through FnGen::toBool, a second, independent call site of the same core.is_null shortcut -- must be fixed too */
void bug_int2ptr_bare_truthy(unsigned long raw)
{
	int *p = (int *)raw;
	if (p) *p = 1;
}

void bug_int2ptr_lnot(unsigned long raw)
{
	int *p = (int *)raw;
	if (!p) return;
	*p = 1;
}

/* ---- regression: the ordinary malloc-fail idiom (a real NULL check on a real allocation result, offset
 * always 0) must keep working exactly as before -- this is the common case the old is_null shortcut was
 * actually right for, and the fix must not disturb it ---- */
void safe_malloc_null_check(void)
{
	int *p = malloc(sizeof(int));
	if (p == 0) return;
	*p = 1;
}

/* ---- regression: a real null pointer must still compare equal to 0 (no over-correction) ---- */
void safe_real_null_is_null(void)
{
	int *p = 0;
	if (p != 0) {
		*p = 1; /* must never be reached: p is a true null, not an int-cast pointer */
	}
}

/* ---- historical-bug closure: libxslt CVE-2025-7424 shape (docs/KNOWN_GAPS_PRIORITIZED.md), collapsed into one
 * function. `extra` plays the role of xmlNode.psvi: a small integer ID (`sentinel_id`) gets written into it
 * upstream (models generate-id()'s `*psviPtr != NULL`-guarded write), and this function's own
 * `cur->extra != 0` check (transform.c's `(cur->ns!=NULL)&&(cur->psvi!=NULL)`) is the only thing standing
 * between that sentinel and a real struct-member dereference through it. Pre-fix, `cur->extra != 0` was wrongly
 * judged always false, so the dereference looked unreachable; post-fix it is a reachable null_deref. */
struct PreComp { void (*func)(void); int tag; };
struct Node { struct PreComp *extra; int ns; };

void bug_sentinel_as_ptr_deref(struct Node *cur, unsigned long sentinel_id)
{
	cur->extra = (struct PreComp *)sentinel_id;
	if (cur->ns != 0 && cur->extra != 0) {
		cur->extra->func = 0; /* dereferences what is actually a tiny integer, not a pointer */
	}
}

/* ---- fixed sibling: the sentinel is never treated as a real pointer, so it stays safe regardless ---- */
void fixed_sentinel_never_dereferenced(struct Node *cur, unsigned long sentinel_id)
{
	cur->extra = (struct PreComp *)sentinel_id;
	if (cur->ns != 0 && cur->extra != 0) {
		(void)cur->extra; /* no dereference: the sentinel is never used as a real pointer */
	}
}

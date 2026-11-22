/* A harness-declared deterministic setup region (DESIGN.md §22.438).
 *
 * `hlir_setup_begin()` / `hlir_setup_end()` bracket work that does not depend on the entry's input, so the
 * engine runs it once and restores the state it produced on every later run. Unlike the generated harness's
 * project-initialiser bracket, the RESULT matters here: `table` below is what the region exists to build.
 *
 * Two entries, and the second is the one that makes this test mean anything.
 *
 *   pure_region   -- the region touches no attacker data. It must be REUSED, and the defect that sits AFTER
 *                    it (an index out of `table`) must still be found: a checkpoint that lost the defect
 *                    would be a faster way to report nothing.
 *
 *   tainted_region -- the same shape, except the region reads `in[0]`. Freezing that would hand every later
 *                    run the first run's input and quietly remove everything behind the region from the
 *                    search. The engine must REFUSE to reuse it, and the defect must still be found. Without
 *                    this entry the feature could silently trade recall for speed and the test would pass. */
#include <stdlib.h>

void hlir_setup_begin(void);
void hlir_setup_end(void);

static unsigned char table[16];

static void build(unsigned seed)
{
	unsigned i, j, acc = seed;
	for (i = 0; i < 16; i++) {
		for (j = 0; j < 64; j++) acc = acc * 1103515245u + 12345u;
		table[i] = (unsigned char)(acc >> 24);
	}
}

int pure_region(const unsigned char *in, unsigned int n)
{
	unsigned k;

	if (n < 4) return -1;
	hlir_setup_begin();
	build(7);                       /* no input is read here: the same table on every run */
	hlir_setup_end();
	/* three guards, so the defect takes several flips to reach: a region restored on later runs has to be
	   restored CORRECTLY, not merely once, or the runs after the first explore a different program. */
	if (in[0] != 0x5a) return 0;
	if (in[2] != 0xa5) return 0;
	k = in[1];
	return table[k];                /* OUT OF BOUNDS once in[1] >= 16 */
}

int tainted_region(const unsigned char *in, unsigned int n)
{
	unsigned k;

	if (n < 4) return -1;
	hlir_setup_begin();
	build(in[0]);                   /* reads attacker data: NOT a deterministic region */
	hlir_setup_end();
	if (in[2] != 0xa5) return 0;
	k = in[1];
	return table[k];                /* OUT OF BOUNDS once in[1] >= 16 */
}

/* "Can this malloc fail?" is a real question about the program, and the wrong question to ask of code the
   harness has just said is setup: every allocation there forks a path into an initialiser's cleanup handler.
   Inside a declared region the allocation SUCCEEDS (DESIGN.md §22.440), so the unchecked store below is not a
   null_deref -- while `unguarded_alloc`, the same code without the markers, must still report one. The defect
   AFTER the region has to survive both. */
int region_alloc(const unsigned char *in, unsigned int n)
{
	unsigned char *q;
	unsigned k;

	if (n < 2) return -1;
	hlir_setup_begin();
	q = malloc(16);
	q[0] = 1;                       /* unchecked, but inside a declared setup region */
	hlir_setup_end();
	k = in[1];
	return q[0] + table[k];         /* OUT OF BOUNDS once in[1] >= 16 */
}

int unguarded_alloc(const unsigned char *in, unsigned int n)
{
	unsigned char *q;
	unsigned k;

	if (n < 2) return -1;
	q = malloc(16);                 /* the SAME code with the markers removed */
	q[0] = 1;                       /* no region: the allocation may fail and this IS a null_deref */
	k = in[1];
	return q[0] + table[k];
}

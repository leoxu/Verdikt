/* Bounds the program states about its own members, harvested from assertion macros (DESIGN.md §22.358, found on
 * sound/core's `snd_BUG_ON(dp->max_synthdev > SNDRV_SEQ_OSS_MAX_SYNTH_DEVS)` in round 42). The invariant is written
 * down in the assertion and nowhere a name heuristic can reach.
 *
 * The line that must not be crossed: an ASSERTION states an internal invariant, an `if (x) return -EINVAL` VALIDATES
 * ATTACKER INPUT. Harvesting the second would assume away exactly the values we are looking for. */
#include <stddef.h>

#define MAX_DEVS 12
#define WARN_ON(c)  ({ int __r = !!(c); if (__r) warn_hook(); __r; })   /* like the kernel's: the condition moves
                                                                         * into a local, so the `if` no longer
                                                                         * mentions the member at all */
#define snd_BUG_ON(c) WARN_ON((c))

extern void warn_hook(void);

static int devs[MAX_DEVS];

struct info {
	int  ndev;        /* asserted: <= MAX_DEVS */
	int  checked;     /* only ever validated, never asserted */
	char pad[8];
};

/* the assertion lives here, in a function the entry never calls -- a per-type fact, not a per-path one */
void info_cleanup(struct info *p)
{
	if (snd_BUG_ON(p->ndev > MAX_DEVS))
		return;
	for (int i = 0; i < p->ndev; i++)
		devs[i] = 0;
}

int sum_devs(struct info *p)
{
	int s = 0;

	for (int i = 0; i < p->ndev; i++)
		s += devs[i];
	return s;
}

/* NEGATIVE: `checked` is validated, not asserted. Assuming it away would hide the overrun. */
int sum_checked(struct info *p)
{
	int s = 0;

	if (p->checked > MAX_DEVS)
		return -1;
	for (int i = 0; i < p->checked; i++)
		s += devs[i];
	return s;
}

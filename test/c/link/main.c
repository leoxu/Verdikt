/* first translation unit: uses lib.c's data and functions; has its own static `counter` and `bump` */
#include "impl.inc"
extern int shared_cnt;
extern int table[];          /* incomplete: the size lives in lib.c */
int helper(int x);
int get_limit(void);

static int counter = 5;
static int bump(int x) { counter += 1; return x + counter; }

/* every cross-file initialiser and the per-file statics must come out right */
int check_init(int dummy) {
	if (shared_cnt != 7) return *(int *)0;
	if (table[3] != 4) return *(int *)0;
	if (counter != 5) return *(int *)0;
	if (bump(0) != 6) return *(int *)0;
	if (helper(0) != 200) return *(int *)0;
	return 0;
}

/* the bound comes from another file */
int checked_lookup(int i) {
	if (i < 0 || i >= get_limit()) return -1;
	return table[i];
}

int unchecked_lookup(int i) { return table[i]; }

/* string literals of different units must not collide (both have __str.0) */
const char *greeting(void) { return "hi"; }

/* a by-value struct argument inside the condition of an else-if, and inside the right operand of && */
struct pt { long a, b; };
static int lt(struct pt x, struct pt y) { return x.a < y.a; }
struct pt gp = {1, 2};
int cmp_chain(int sel, long v) {
	struct pt p = {v, 0};
	if (sel == 0)
		return 0;
	else if (sel == 1 && lt(p, gp))
		return 1;
	else if (lt(gp, p))
		return 2;
	return 3;
}
int use_tbl(int i) { return tbl.f(i & 7) + tbl.g(i & 7); }

/* dispatch through a table defined in handlers.c: the targets live in another file */
struct handler { int (*run)(int); void (*note)(int *); };
extern const struct handler handlers[3];
int dispatch(int which, int arg) {
	if (which < 0 || which >= 3) return -1;
	return handlers[which].run(arg);
}

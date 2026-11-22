/* third translation unit: registers handlers in a table; main.c dispatches through the table without knowing the functions */
struct handler { int (*run)(int); void (*note)(int *); };

static int on_small(int x) { return x * 2; }
static int on_big(int x) { return x - 100; }
static void note_zero(int *p) { *p = 0; }
int handler_bug(int x) { int a[4]; a[x] = 1; return a[0]; }   /* reachable through the table only: unbounded index */

const struct handler handlers[3] = {
	{ on_small, note_zero },
	{ on_big, 0 },
	{ handler_bug, 0 },
};

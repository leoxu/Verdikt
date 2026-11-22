/* included into main.c: these static functions are only reachable through the initialiser of `tbl` */
static int h1(int x) { return x + 1; }
static int h2(int x) { return x + 2; }
struct ops { int (*f)(int); int (*g)(int); };
static const struct ops tbl = { h1, h2 };

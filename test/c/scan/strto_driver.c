#include <stdlib.h>
#include <errno.h>
/* the number parsed out of the attacker's string is used as an index without a bound */
int idx(const char *s) {
	static const int tab[8] = {1, 2, 3, 4, 5, 6, 7, 8};
	char *end;
	long v = strtol(s, &end, 10);
	if (v < 0) return -1;
	return tab[v];
}
/* the same with the bound */
int idx_ok(const char *s) {
	static const int tab[8] = {1, 2, 3, 4, 5, 6, 7, 8};
	char *end;
	long v = strtol(s, &end, 10);
	if (v < 0 || v >= 8) return -1;
	return tab[v];
}

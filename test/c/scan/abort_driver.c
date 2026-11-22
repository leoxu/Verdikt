#include <stdlib.h>
int alloc_or_die(unsigned n) {
	if (n == 0 || n > 16) return 0;
	char *p = malloc(n);
	if (!p) abort();
	p[0] = 1;                /* never reached with p == NULL */
	int r = p[0];
	free(p);
	return r;
}

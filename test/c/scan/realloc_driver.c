#include <stdlib.h>
#include <string.h>
int grow(const char *d, unsigned n) {
	if (n == 0 || n > 32) return 0;
	char *b = malloc(n);
	if (!b) return 0;
	memcpy(b, d, n);
	char *c = realloc(b, n * 2);
	if (!c) { free(b); return 0; }
	int r = c[n - 1];
	free(c);
	return r;
}
int grow_bug(const char *d, unsigned n) {
	if (n == 0 || n > 32) return 0;
	char *b = malloc(n);
	if (!b) return 0;
	char *c = realloc(b, n * 2);
	if (!c) { free(b); return 0; }
	free(b);           /* b was freed by a successful realloc */
	free(c);
	return 0;
}

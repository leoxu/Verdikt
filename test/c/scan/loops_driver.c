#include <stddef.h>
int count_a(const unsigned char *s, size_t n) {
	int c = 0;
	for (size_t i = 0; i < n; i++)
		if (s[i] == 'a') c++;
	if (c == 5) return 100 / (c - 5);
	return c;
}
int records(const unsigned char *p, size_t n) {
	size_t i = 0;
	int sum = 0;
	while (i + 1 < n) {
		unsigned len = p[i];
		if (i + 1 + len > n) return -1;
		sum += p[i + 1 + (len ? len - 1 : 0)];
		i += 1 + len;
		if (len == 0) break;
	}
	return sum;
}
int parse_dec(const char *s, size_t n) {
	int v = 0;
	for (size_t i = 0; i < n; i++) {
		if (s[i] < '0' || s[i] > '9') return -1;
		v = v * 10 + (s[i] - '0');
	}
	return v;
}

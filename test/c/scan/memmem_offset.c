/* c-ares' ares_buf_consume_until_seq idiom: memmem's result points into the haystack, so `p - big` is a same-object
   pointer difference. Before models/libc.core had a @memmem model the call fell to the opaque-external default, whose
   result is an unrelated object, and the subtraction was a spurious ptr_cmp_diff_obj (DESIGN.md). */
#define _GNU_SOURCE
#include <string.h>

long offset_of_crlf(const unsigned char *big, unsigned len) {
	const unsigned char *p;
	if (len > 64)
		return -1;
	p = memmem(big, len, "\r\n", 2);
	return p ? (long)(p - big) : -1;
}

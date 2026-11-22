/* Length <-> buffer pairing shapes from c-ares (DESIGN.md §22.346). */
#include <stddef.h>

/* ares_parse_*_reply: a length word with a type tag must still pair with its buffer */
int parse_reply(const unsigned char *abuf, int alen_int) {
	return alen_int > 0 ? abuf[alen_int - 1] : 0;
}

/* ares_inet_net_pton: size describes dst; src is the C string being parsed */
int net_pton(int af, const char *src, void *dst, size_t size) {
	unsigned char *d = dst;
	size_t i = 0;
	(void)af;
	while (src[i] && i < size) { d[i] = (unsigned char)src[i]; i++; }
	return (int)i;
}

/* only a `const char *` in the group: the length still describes it */
int parse_str(const char *s, size_t len) {
	return len ? s[len - 1] : 0;
}

/* libwebp ParseHeadersInternal: the length word carries a role tag, not a type tag (DESIGN.md §22.349) */
int parse_headers(const unsigned char *data_param, size_t data_size_param) {
	return data_size_param ? data_param[data_size_param - 1] : 0;
}

/* the tag is stripped, not trusted: `flags` is not a length, so `flags_param` must not pair with anything */
int take_flags(const unsigned char *buf, int flags_param) {
	return flags_param ? buf[0] : 0;
}

/* ares_parse_ptr_reply: addrlen belongs to addr, not to abuf before alen_int */
int ptr_reply(const unsigned char *abuf, int alen_int, const void *addr, int addrlen) {
	return (alen_int > 0 ? abuf[0] : 0) + (addrlen > 0 ? ((const unsigned char *)addr)[0] : 0);
}

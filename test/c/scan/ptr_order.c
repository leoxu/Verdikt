/* a pointer before the start of the object is "less than" the start: the usual validator idiom */
int back_ref(const unsigned char *buf, unsigned n, unsigned back) {
	if (n < 8 || n > 32) return -1;
	const unsigned char *ref = buf + 4 - back;         /* may point before buf */
	if (ref < buf) return -1;                          /* checked before the access */
	return ref[0];
}

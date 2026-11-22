/* `dstlen` (no underscore, lower case) is the length of dst: the generated spec must relate them */
int fill_last(char *dst, unsigned long dstlen, int v) {
	if (dstlen < 1) return 0;
	dst[dstlen - 1] = (char)v;
	return 1;
}

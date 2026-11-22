// CVE:    CVE-2024-25629
// SOURCE: c-ares src/lib/ares__read_line.c:62, fix 76cefd5a (GHSA-mg26-v6qh-x48q)
// KIND:   ptr_arith_oob
// VULN:   readline_vuln
// FIXED:  readline_fixed
//
// `fgets()` succeeds whenever it reads anything at all, INCLUDING a line whose first byte is an embedded NUL.
// Then `strlen(buf + offset)` is 0 and `offset` is 0, so `len == 0` and `len - 1` wraps to SIZE_MAX: the read
// lands one byte BEFORE the allocation. A heap buffer underflow read, reached from any configuration file the
// library parses.
//
// Here the "file" is the attacker buffer and `fgets` is the copy loop; what matters is that `len` can be 0
// with `offset` 0 and that nothing stands between that and `buf[len - 1]`.
//
// KIND is `ptr_arith_oob`, not `oob_read`: `len - 1` wraps first, so FORMING the address is the UB the engine
// stops at and the load never executes. Upstream the same input is an ASan heap-buffer-underflow READ one
// byte before a 128-byte allocation; the difference is where each tool draws the line, not what happens.

int readline_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[16];
	unsigned i, offset, len;

	if (caplen < 16)
		return -1;
	for (i = 0; i < 16; i++)
		buf[i] = in[i];
	buf[15] = 0;

	offset = 0;
	len = offset;
	while (len < 16 && buf[len] != 0)      /* strlen(buf + offset) */
		len++;

	if (buf[len - 1] == '\n')              /* CVE: len == 0 wraps */
		return 1;
	return 0;
}

int readline_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[16];
	unsigned i, offset, len;

	if (caplen < 16)
		return -1;
	for (i = 0; i < 16; i++)
		buf[i] = in[i];
	buf[15] = 0;

	offset = 0;
	len = offset;
	while (len < 16 && buf[len] != 0)
		len++;

	if (len == 0)                          /* the fix: throw the line away */
		return 2;
	if (buf[len - 1] == '\n')
		return 1;
	return 0;
}

// CVE:    CVE-2022-37434
// SOURCE: zlib inflate.c:769 (gzip EXTRA field), fix eff308af
// KIND:   ptr_arith_oob
// VULN:   gzhead_vuln
// FIXED:  gzhead_fixed
// ARGS:   --buf-max 16
//
// `len` is how much of the EXTRA field has already been delivered. Nothing checks it against `extra_max`, the
// size of the buffer the CALLER handed to inflateGetHeader(). Once `len >= extra_max`:
//   * `extra + len` is already past that buffer, and
//   * the clamp `len + copy > extra_max ? extra_max - len : copy` UNDERFLOWS -- the ternary meant to limit the
//     copy picks the larger value instead.
// The underflowing clamp is the point of the fixture: a version that only walked the pointer past the end
// would miss what made this exploitable.
//
// KIND is `ptr_arith_oob` for the same reason as CVE-2023-31130: on the real tree HLIR reports
// `ptr_arith_oob @ inflate.c:769`, because forming `extra + len` past the caller's buffer is the UB the
// engine stops at, before the copy runs.

int gzhead_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char extra[8];
	unsigned char src[16];
	unsigned i, extra_max, extra_len, have, len, copy, amount;

	if (caplen < 16)
		return -1;
	for (i = 0; i < 16; i++)
		src[i] = in[i];
	for (i = 0; i < 8; i++)
		extra[i] = 0;

	extra_max = 8;                      /* what the caller's buffer actually holds */
	extra_len = (unsigned)src[0];       /* what the stream claims the EXTRA field is */
	have = (unsigned)(src[1] & 0x0f);
	len = (unsigned)src[2];             /* already delivered */
	if (len > extra_len)
		return -2;

	copy = extra_len - len;
	if (copy > have)
		copy = have;
	if (copy) {
		/* CVE: `len` is never checked against extra_max */
		amount = (len + copy > extra_max) ? (extra_max - len) : copy;
		for (i = 0; i < amount && i < 16; i++)
			extra[len + i] = src[i];
	}
	return (int)extra[0];
}

int gzhead_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char extra[8];
	unsigned char src[16];
	unsigned i, extra_max, extra_len, have, len, copy, amount;

	if (caplen < 16)
		return -1;
	for (i = 0; i < 16; i++)
		src[i] = in[i];
	for (i = 0; i < 8; i++)
		extra[i] = 0;

	extra_max = 8;
	extra_len = (unsigned)src[0];
	have = (unsigned)(src[1] & 0x0f);
	len = (unsigned)src[2];
	if (len > extra_len)
		return -2;

	copy = extra_len - len;
	if (copy > have)
		copy = have;
	if (copy && len < extra_max) {      /* the fix: nothing is copied once len has reached extra_max */
		amount = (len + copy > extra_max) ? (extra_max - len) : copy;
		for (i = 0; i < amount && i < 16; i++)
			extra[len + i] = src[i];
	}
	return (int)extra[0];
}

// CVE:    CVE-2023-31130
// SOURCE: c-ares src/lib/inet_net_pton.c:360 (inet_net_pton_ipv6), fix f22cc010
// KIND:   ptr_arith_oob
// VULN:   netpton_vuln
// FIXED:  netpton_fixed
// ARGS:   --buf-max 16
//
// All the bounds checks in the parse loop are against `endp = tmp + 16`, and they are correct. The defect is
// that `endp` is then RECOMPUTED from the attacker's `/bits` while `tp` keeps the value the real group count
// gave it -- the two come apart. The shift loop guards only equality (`tp == endp`) where it needed `tp >
// endp`, so writing backwards from `endp` runs off the FRONT of the array. "::1:2:3/0" is nine characters:
// colonp = tmp+0, tp = tmp+6, bits = 0 -> words = 2 -> endp = tmp+4, n = 6, and `*(endp - 6)` is tmp-2.
//
// A buffer UNDERFLOW write, which is why this fixture is worth keeping separate from the over-read family.
//
// KIND is `ptr_arith_oob`, which is what HLIR reports at inet_net_pton.c:360 on the real tree too:
// `core.check.ptr_arith` fires on `endp - i` before the store ever runs. With `--lenient-ptr-arith` the same
// site comes back as `oob_write`, offset -1 of a 16-byte stack object. The advisory calls it an underflow
// WRITE; both descriptions are of the same event, and the fixture asserts the one the engine actually emits.

int netpton_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char tmp[16];
	unsigned char *tp, *endp, *colonp;
	unsigned i, groups, bits, words;
	long n;

	for (i = 0; i < 16; i++)
		tmp[i] = 0;
	if (caplen < 2)
		return -1;

	groups = in[0] & 0x07;          /* how many groups the address really had */
	bits = in[1];                   /* ... and the /bits the attacker asked for */
	tp = tmp + 2 * groups;          /* `tp` advanced by the REAL group count */
	colonp = tmp;
	if (tp > tmp + 16)
		return -2;

	words = (bits + 15) / 16;
	if (words < 2)
		words = 2;
	if (words > 8)
		words = 8;
	endp = tmp + 2 * words;         /* ... `endp` recomputed from the CLAIMED bits */

	n = (long)(tp - colonp);
	if (tp == endp)                 /* CVE: needed `tp > endp` */
		return -3;
	for (i = 1; (long)i <= n; i++) {
		*(endp - i) = *(colonp + n - i);   /* n > endp - tmp writes before tmp */
		*(colonp + n - i) = 0;
	}
	return (int)tmp[0];
}

int netpton_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char tmp[16];
	unsigned char *tp, *endp, *colonp;
	unsigned i, groups, bits, words;
	long n;

	for (i = 0; i < 16; i++)
		tmp[i] = 0;
	if (caplen < 2)
		return -1;

	groups = in[0] & 0x07;
	bits = in[1];
	tp = tmp + 2 * groups;
	colonp = tmp;
	if (tp > tmp + 16)
		return -2;

	words = (bits + 15) / 16;
	if (words < 2)
		words = 2;
	if (words > 8)
		words = 8;
	endp = tmp + 2 * words;

	n = (long)(tp - colonp);
	if (tp >= endp)                 /* the fix */
		return -3;
	for (i = 1; (long)i <= n; i++) {
		*(endp - i) = *(colonp + n - i);
		*(colonp + n - i) = 0;
	}
	return (int)tmp[0];
}

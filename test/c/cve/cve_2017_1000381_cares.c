// CVE:    CVE-2017-1000381
// SOURCE: c-ares ares_parse_naptr_reply.c, fix 9478908a
// KIND:   oob_read
// VULN:   naptr_vuln
// FIXED:  naptr_fixed
//
// The only bound on a record body is `aptr + rr_len > abuf + alen`, which constrains the RECORD not to run off
// the buffer. When `rr_len == 0` and the record ends exactly at the end of the buffer, `aptr == abuf + alen`,
// the comparison is false, and the four bytes of NAPTR order/preference are then read UNCONDITIONALLY.
//
// The "ends exactly at the end" part is the whole defect, so the fixture must allow the record length to come
// out zero -- a version that forced `rr_len >= 1` would prove nothing.

int naptr_vuln(const unsigned char *in, unsigned alen)
{
	unsigned char abuf[24];
	const unsigned char *aptr, *endp;
	unsigned i, rr_len, rr_type;
	int n = 0;

	if (alen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		abuf[i] = in[i];
	endp = abuf + 24;

	aptr = abuf + 4;
	for (i = 0; i < 2; i++) {
		if (aptr + 4 > endp)
			break;
		rr_type = abuf[0] & 0x01;
		rr_len = aptr[3];
		aptr += 4;                       /* RRFIXEDSZ */
		if (aptr + rr_len > endp)        /* the only check: the RECORD must fit */
			break;
		if (rr_type)                     /* a NAPTR record */
			n += (aptr[0] << 8) | aptr[1];   /* CVE: unconditional, and rr_len may be 0 */
		aptr += rr_len;
	}
	return n;
}

int naptr_fixed(const unsigned char *in, unsigned alen)
{
	unsigned char abuf[24];
	const unsigned char *aptr, *endp;
	unsigned i, rr_len, rr_type;
	int n = 0;

	if (alen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		abuf[i] = in[i];
	endp = abuf + 24;

	aptr = abuf + 4;
	for (i = 0; i < 2; i++) {
		if (aptr + 4 > endp)
			break;
		rr_type = abuf[0] & 0x01;
		rr_len = aptr[3];
		aptr += 4;
		if (aptr + rr_len > endp)
			break;
		if (rr_type) {
			if (rr_len < 4 || aptr + 4 > endp)   /* the fix: the BODY has to be there too */
				break;
			n += (aptr[0] << 8) | aptr[1];
		}
		aptr += rr_len;
	}
	return n;
}

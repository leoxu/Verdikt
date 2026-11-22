// CVE:    CVE-2016-7931
// SOURCE: tcpdump print-mpls.c:127, fix 69ead2a0 "Add bounds and length checks"
// KIND:   oob_read
// VULN:   mpls_vuln
// FIXED:  mpls_fixed
//
// After walking the label stack the payload protocol is inferred from the first payload byte. Nothing checked
// that the walk left the pointer inside the capture: a stack whose bottom-of-stack bit never arrives walks the
// pointer straight off the end.

int mpls_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	p = buf;
	for (i = 0; i < 6; i++) {       /* walk 4-byte label entries until bottom-of-stack */
		if (p + 4 > end)
			break;
		if (p[2] & 1) {
			p += 4;
			break;
		}
		p += 4;
	}
	switch (*p) {                   /* CVE: p may be at or past end */
	case 0x45: return 4;
	case 0x60: return 6;
	default:   return 0;
	}
}

int mpls_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	p = buf;
	for (i = 0; i < 6; i++) {
		if (p + 4 > end)
			break;
		if (p[2] & 1) {
			p += 4;
			break;
		}
		p += 4;
	}
	if (p >= end)                   /* the fix: ND_TCHECK(*p) */
		return -2;
	switch (*p) {
	case 0x45: return 4;
	case 0x60: return 6;
	default:   return 0;
	}
}

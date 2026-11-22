// CVE:    CVE-2016-7939
// SOURCE: tcpdump print-gre.c:172, fix 237efcf5 "Add some bounds checks"
// KIND:   oob_read
// VULN:   gre_vuln
// FIXED:  gre_fixed
//
// The source-route-entry loop checks the CLAIMED remaining length and then reads four bytes. `len` comes from
// the GRE header, not from the capture, so when the capture is shorter than the header claims all four reads
// run past the end.

int gre_vuln(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *bp, *end;
	unsigned i, len, srelen;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	bp = buf + 4;
	len = claimed;
	for (i = 0; i < 4; i++) {
		if (len < 4)            /* CVE: the CLAIMED length is checked, the capture is not */
			break;
		n += bp[0];
		srelen = bp[3];
		bp += 4;
		len -= 4;
		if (len < srelen)
			break;
		bp += srelen;
		len -= srelen;
	}
	(void)end;
	return n;
}

int gre_fixed(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *bp, *end;
	unsigned i, len, srelen;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	bp = buf + 4;
	len = claimed;
	for (i = 0; i < 4; i++) {
		if (len < 4)
			break;
		if (bp + 4 > end)       /* the fix: ND_TCHECK before each read */
			break;
		n += bp[0];
		srelen = bp[3];
		bp += 4;
		len -= 4;
		if (len < srelen)
			break;
		bp += srelen;
		len -= srelen;
	}
	return n;
}

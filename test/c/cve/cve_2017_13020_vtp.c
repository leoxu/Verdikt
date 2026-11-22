// CVE:    CVE-2017-13020
// SOURCE: tcpdump print-vtp.c:246, fix c5dd7bef "VTP: Add a missing bounds check"
// KIND:   oob_read
// VULN:   vtp_vuln
// FIXED:  vtp_fixed
//
// The loop bound is the CLAIMED length out of the packet header; the capture may be shorter. `ND_TCHECK2` two
// lines down guards the record body, but reading the record's own length byte is already past the capture.
//
// This fixture doubles as the §22.418 regression: `buf + claimed` is an out-of-range pointer that is only ever
// COMPARED, and a replay that halts on it (as the concrete domain used to) never reaches the defect two lines
// later -- which is exactly how this CVE was lost the first time.

int vtp_vuln(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, len;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;                 /* where the CAPTURE ends */

	tptr = buf + 4;
	while (tptr < buf + claimed) {  /* ... but the loop walks the CLAIMED length */
		len = *tptr;            /* CVE: nothing checked tptr against end */
		if (len == 0)
			break;
		if (tptr + len > end)
			break;
		n += (int)len;
		tptr += len + 1;
	}
	return n;
}

int vtp_fixed(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, len;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tptr = buf + 4;
	while (tptr < buf + claimed) {
		if (tptr >= end)        /* the fix: ND_TCHECK_8BITS(tptr) */
			break;
		len = *tptr;
		if (len == 0)
			break;
		if (tptr + len > end)
			break;
		n += (int)len;
		tptr += len + 1;
	}
	return n;
}

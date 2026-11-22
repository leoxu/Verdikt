// CVE:    CVE-2017-13050
// SOURCE: tcpdump print-rpki-rtr.c:288, fix 83c64fce "RPKI-Router: fix a few bugs"
// KIND:   ptr_arith_oob
// VULN:   rpki_vuln
// FIXED:  rpki_fixed
//
// "The decoder didn't properly check that the PDU length stored in the PDU header is correct. The only check
// in place tested whether the length is zero but that is not sufficient." The encapsulated-PDU length walks
// the pointer, and the field after it is then read unconditionally.
//
// KIND is `ptr_arith_oob`, not `oob_read`: forming the out-of-range pointer is itself the UB and the engine
// stops there, so the read two lines later never executes. That matches what HLIR reports on the real tree,
// where `ptr_arith_oob print-rpki-rtr.c:280` is one of the two findings and the one whose witness native ASan
// reproduces.

int rpki_vuln(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, encap;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tptr = buf + 8;
	encap = (unsigned)buf[4] * 4u;
	if (claimed == 0)               /* the only check that was there */
		return -2;
	tptr += encap;                  /* CVE: unchecked against end */
	if (tptr + 4 > buf + claimed)
		return -3;
	(void)end;
	return (int)(tptr[0] ^ tptr[3]);
}

int rpki_fixed(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, encap;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tptr = buf + 8;
	encap = (unsigned)buf[4] * 4u;
	if (claimed == 0)
		return -2;
	if (encap > (unsigned)(end - tptr))   /* the fix: bound the walk by the capture */
		return -4;
	tptr += encap;
	if (tptr + 4 > end)
		return -3;
	return (int)(tptr[0] ^ tptr[3]);
}

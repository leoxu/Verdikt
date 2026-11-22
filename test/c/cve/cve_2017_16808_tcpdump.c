// CVE:    CVE-2017-16808
// SOURCE: tcpdump print-aoe.c:328, fix 28f61002 (the whole fix is one ND_TCHECK2 in the loop)
// KIND:   oob_read
// VULN:   aoe_vuln
// FIXED:  aoe_fixed
//
// The correlation check uses `len` -- the length CLAIMED by the packet header -- while the data actually
// available ends at the capture. A truncated capture whose header claims more MAC addresses than were
// captured walks the pointer past the end, six bytes at a time.
//
// Reading ALL SIX address bytes is load-bearing: on the real tree the over-read happens inside
// etheraddr_string, and a stub that ignored the bytes would hide this CVE and CVE-2017-13052 both.

static int ether_string(const unsigned char *ep)
{
	int n = 0;
	unsigned i;

	for (i = 0; i < 6; i++)         /* the real one reads all six; so does this */
		n += ep[i];
	return n;
}

int aoe_vuln(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *cp, *end;
	unsigned i, nmacs;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	cp = buf + 4;
	nmacs = buf[1];
	if (4u + nmacs * 6u != claimed)  /* correlated against the CLAIMED length only */
		return -2;
	for (i = 0; i < nmacs && i < 8; i++) {
		n += ether_string(cp);   /* CVE: nothing checked cp against end */
		cp += 6;
	}
	(void)end;
	return n;
}

int aoe_fixed(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *cp, *end;
	unsigned i, nmacs;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	cp = buf + 4;
	nmacs = buf[1];
	if (4u + nmacs * 6u != claimed)
		return -2;
	for (i = 0; i < nmacs && i < 8; i++) {
		if (cp + 6 > end)        /* the fix: ND_TCHECK2(*cp, ETHER_ADDR_LEN) */
			break;
		n += ether_string(cp);
		cp += 6;
	}
	return n;
}

// CVE:    CVE-2017-12988
// SOURCE: tcpdump print-telnet.c:445, fix 8934a7d6 "TELNET: Add a missing bounds check"
// KIND:   oob_read
// VULN:   telnet_vuln
// FIXED:  telnet_fixed
// ARGS:   --buf-max 16
//
// One hunk, one inserted check, in the option-subnegotiation walk. On the real tree this finding came from the
// SYMBOLIC engine, not the concolic one -- which is why it was the target that exposed §22.419 (the symbolic
// replay ran with a default RunConfig and died `unsupported` on its first bodyless call).

int telnet_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[12];
	const unsigned char *p, *end;
	unsigned i;
	int n = 0;

	if (caplen < 12)
		return -1;
	for (i = 0; i < 12; i++)
		buf[i] = in[i];
	end = buf + 12;

	p = buf;
	while (p < end) {
		if (*p != 0xFF) {       /* IAC */
			p++;
			continue;
		}
		p++;                    /* step over IAC ... */
		n += *p;                /* CVE: ... and read the command without checking */
		p++;
		if (n > 0x400)
			break;
	}
	return n;
}

int telnet_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[12];
	const unsigned char *p, *end;
	unsigned i;
	int n = 0;

	if (caplen < 12)
		return -1;
	for (i = 0; i < 12; i++)
		buf[i] = in[i];
	end = buf + 12;

	p = buf;
	while (p < end) {
		if (*p != 0xFF) {
			p++;
			continue;
		}
		p++;
		if (p >= end)           /* the fix */
			break;
		n += *p;
		p++;
		if (n > 0x400)
			break;
	}
	return n;
}

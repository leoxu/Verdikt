// CVE:    CVE-2017-13017
// SOURCE: tcpdump print-dhcp6.c:522 (dhcp6opt_print), fix 11b426ee
//         "DHCPv6: Add a missing option length check"
// KIND:   oob_read
// VULN:   dhcp6_vuln
// FIXED:  dhcp6_fixed
//
// An option's payload is read without first checking that the option length covers it. The option header is
// bounded, the body is not.

int dhcp6_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i, optlen, opttype;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	p = buf + 4;
	for (i = 0; i < 3; i++) {
		if (p + 4 > end)
			break;
		opttype = (p[0] << 8) | p[1];
		optlen = (p[2] << 8) | p[3];
		p += 4;
		if (opttype == 0x0d)
			n += (p[0] << 8) | p[1];   /* CVE: optlen never checked to cover 2 bytes */
		else
			n += p[0];                 /* CVE: nor one */
		p += optlen;
	}
	return n;
}

int dhcp6_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i, optlen, opttype;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	p = buf + 4;
	for (i = 0; i < 3; i++) {
		if (p + 4 > end)
			break;
		opttype = (p[0] << 8) | p[1];
		optlen = (p[2] << 8) | p[3];
		p += 4;
		if (opttype == 0x0d) {
			if (optlen < 2 || p + 2 > end)   /* the fix */
				break;
			n += (p[0] << 8) | p[1];
		} else {
			if (optlen < 1 || p + 1 > end)   /* the fix */
				break;
			n += p[0];
		}
		p += optlen;
	}
	return n;
}

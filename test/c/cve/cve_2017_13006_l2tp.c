// CVE:    CVE-2017-13006
// SOURCE: tcpdump print-l2tp.c:440 (l2tp_call_errors_print), fix cc4a7391
//         "L2TP: Check whether an AVP's content exceeds the AVP length"
// KIND:   oob_read
// VULN:   l2tp_vuln
// FIXED:  l2tp_fixed
//
// "It's not good enough to check whether all the data specified by the AVP length was captured - you also have
// to check whether that length is large enough for all the required data in the AVP." The sub-printer takes a
// pointer and NO length, and walks six counters out of a buffer that may hold none of them. The nesting is
// part of the shape: on the real tree the chain is l2tp_print -> l2tp_avp_print -> l2tp_avp_print ->
// l2tp_call_errors_print, so the defect is reached through a SECOND AVP, not the first.

static int call_errors_vuln(const unsigned char *dat)
{
	int n = 0;
	unsigned i;

	dat += 2;                       /* skip "Reserved" */
	for (i = 0; i < 6; i++) {       /* CVE: no length, so nothing bounds this walk */
		n += (dat[0] << 8) | dat[1];
		dat += 2;
	}
	return n;
}

static int call_errors_fixed(const unsigned char *dat, unsigned len)
{
	int n = 0;
	unsigned i;

	if (len < 2 + 6 * 2)            /* the fix: the sub-printer gets a length and uses it */
		return 0;
	dat += 2;
	for (i = 0; i < 6; i++) {
		n += (dat[0] << 8) | dat[1];
		dat += 2;
	}
	return n;
}

int l2tp_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i, alen;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	p = buf;
	for (i = 0; i < 2; i++) {       /* the AVP loop: the defect is behind the second one */
		if (p + 4 > end)
			break;
		alen = p[1];
		if (alen < 4 || p + alen > end)
			break;
		if (p[3] == 0x22)
			n += call_errors_vuln(p + 4);
		p += alen;
	}
	return n;
}

int l2tp_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i, alen;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	p = buf;
	for (i = 0; i < 2; i++) {
		if (p + 4 > end)
			break;
		alen = p[1];
		if (alen < 4 || p + alen > end)
			break;
		if (p[3] == 0x22)
			n += call_errors_fixed(p + 4, alen - 4);
		p += alen;
	}
	return n;
}

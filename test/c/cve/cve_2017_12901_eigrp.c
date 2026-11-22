// CVE:    CVE-2017-12901
// SOURCE: tcpdump print-eigrp.c:388, fix de981e60 "EIGRP: Do more length checks"
// KIND:   oob_read
// VULN:   eigrp_vuln
// FIXED:  eigrp_fixed
//
// The TLV header's length was checked; the per-type PAYLOAD never was. Each arm casts the TLV pointer to its
// struct and reads fields at fixed offsets inside it. The fix adds ND_TCHECK2(*tlv, sizeof(...)) to nine arms.

int eigrp_vuln(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tlv, *end;
	unsigned i, tlen, type;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tlv = buf + 4;
	for (i = 0; i < 3; i++) {
		if (tlv + 4 > end)
			break;
		type = tlv[0];
		tlen = tlv[1];
		if (tlen < 4)
			break;
		/* CVE: the HEADER is in the capture, so the arm below assumes the PAYLOAD is too */
		if (type == 1)
			n += (tlv[4] << 8) | tlv[5];    /* general parms: 2 bytes at offset 4 */
		else if (type == 4)
			n += tlv[8];                    /* sw version: 1 byte at offset 8 */
		tlv += tlen;
	}
	(void)claimed;
	return n;
}

int eigrp_fixed(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tlv, *end;
	unsigned i, tlen, type;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tlv = buf + 4;
	for (i = 0; i < 3; i++) {
		if (tlv + 4 > end)
			break;
		type = tlv[0];
		tlen = tlv[1];
		if (tlen < 4)
			break;
		if (type == 1) {
			if (tlv + 6 > end)      /* the fix */
				break;
			n += (tlv[4] << 8) | tlv[5];
		} else if (type == 4) {
			if (tlv + 9 > end)      /* the fix */
				break;
			n += tlv[8];
		}
		tlv += tlen;
	}
	(void)claimed;
	return n;
}

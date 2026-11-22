// CVE:    CVE-2017-13045
// SOURCE: tcpdump print-vqp.c:155, fix 3b36ec4e
// KIND:   oob_read
// VULN:   vqp_vuln
// FIXED:  vqp_fixed
//
// The loop is guarded by `tlen > 0`, a counter derived from the length the HEADER claims, while the data
// actually present ends at the capture. ONE byte of claimed length is enough to enter an iteration that reads
// a six-byte TLV header. The fix adds ND_TCHECK(*tlv) and bounds the TLV length against `tlen`.

int vqp_vuln(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, tlen, nitems, obj_len;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tptr = buf + 8;
	nitems = buf[1] & 0x07;
	tlen = claimed;
	while (nitems > 0 && tlen > 0) {     /* CVE: tlen is the CLAIMED remainder */
		n += (tptr[0] << 8) | tptr[1];      /* obj_type: 4 bytes on the real tree */
		obj_len = (tptr[4] << 8) | tptr[5]; /* obj_length */
		tptr += 6 + obj_len;
		if (tlen < 6 + obj_len)
			break;
		tlen -= 6 + obj_len;
		nitems--;
	}
	(void)end;
	return n;
}

int vqp_fixed(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, tlen, nitems, obj_len;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tptr = buf + 8;
	nitems = buf[1] & 0x07;
	tlen = claimed;
	while (nitems > 0 && tlen > 0) {
		if (tptr + 6 > end)          /* the fix: ND_TCHECK(*vqp_obj_tlv) */
			break;
		n += (tptr[0] << 8) | tptr[1];
		obj_len = (tptr[4] << 8) | tptr[5];
		if (tlen < 6 + obj_len)      /* ... and bound obj_len against tlen */
			break;
		tptr += 6 + obj_len;
		tlen -= 6 + obj_len;
		nitems--;
	}
	return n;
}

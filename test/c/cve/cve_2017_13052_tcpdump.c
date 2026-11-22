// CVE:    CVE-2017-13052
// SOURCE: tcpdump print-cfm.c:619 (Sender ID TLV), fix 5d340a5c
// KIND:   oob_read
// VULN:   cfm_vuln
// FIXED:  cfm_fixed
//
// The Sender ID TLV decoder took a `tptr` and NO length, so the caller's bounds were never available to it:
//
//   -                       register const u_char *tptr)
//   +                       register const u_char *tptr, const u_int length)
//   +    if (length < 1) { ... }
//   +        if (length != 1 + 4)  { /* invalid IPv4 address length */ break; }
//
// Same family as CVE-2017-13006 (a sub-printer without a length), kept separately because the fix is a
// different one and a regression could plausibly lose one and not the other.

static int mac_string(const unsigned char *ep)
{
	int n = 0;
	unsigned i;

	for (i = 0; i < 6; i++)
		n += ep[i];
	return n;
}

static int sender_id_vuln(const unsigned char *tptr)
{
	unsigned chassis_id_length = tptr[0];

	if (chassis_id_length == 0)
		return 0;
	return mac_string(tptr + 1);     /* CVE: no length, so nothing bounds this */
}

static int sender_id_fixed(const unsigned char *tptr, unsigned length)
{
	unsigned chassis_id_length;

	if (length < 1)                  /* the fix: the TLV's own length reaches the sub-printer */
		return 0;
	chassis_id_length = tptr[0];
	if (chassis_id_length == 0)
		return 0;
	if (length < 1 + 6)
		return 0;
	return mac_string(tptr + 1);
}

int cfm_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, tlv_type, tlv_len;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tptr = buf + 4;
	for (i = 0; i < 2; i++) {
		if (tptr + 3 > end)
			break;
		tlv_type = tptr[0];
		tlv_len = (tptr[1] << 8) | tptr[2];
		tptr += 3;
		if (tptr + tlv_len > end)
			break;
		if (tlv_type == 1)
			n += sender_id_vuln(tptr);
		tptr += tlv_len;
	}
	return n;
}

int cfm_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *tptr, *end;
	unsigned i, tlv_type, tlv_len;
	int n = 0;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];
	end = buf + 24;

	tptr = buf + 4;
	for (i = 0; i < 2; i++) {
		if (tptr + 3 > end)
			break;
		tlv_type = tptr[0];
		tlv_len = (tptr[1] << 8) | tptr[2];
		tptr += 3;
		if (tptr + tlv_len > end)
			break;
		if (tlv_type == 1)
			n += sender_id_fixed(tptr, tlv_len);
		tptr += tlv_len;
	}
	return n;
}

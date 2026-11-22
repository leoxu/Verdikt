// CVE:    CVE-2017-13688
// SOURCE: tcpdump print-olsr.c:619 (OLSR_NAMESERVICE_MSG), fix 6fca58f
// KIND:   ptr_arith_oob
// VULN:   olsr_vuln
// FIXED:  olsr_fixed
//
//     case OLSR_NAMESERVICE_MSG: {
//         u_int name_entries = EXTRACT_16BITS(msg_data + 2);   /* line 619, nothing checked first */
//
// The fix does exactly what its subject says: bounds-check before fetching. The message type comes from the
// packet, so reaching the arm at all is part of what the search has to solve -- which is why this fixture
// keeps the dispatch rather than calling the handler directly.

int olsr_vuln(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[16];
	const unsigned char *msg_data, *end;
	unsigned i, msg_type, msg_len, name_entries;
	int n = 0;

	if (caplen < 16)
		return -1;
	for (i = 0; i < 16; i++)
		buf[i] = in[i];
	end = buf + 16;

	msg_data = buf + 4;
	msg_type = buf[4];
	msg_len = (buf[6] << 8) | buf[7];
	if (msg_len > claimed)
		return -2;
	msg_data += 12;                      /* past the OLSR message header */

	if (msg_type == 0x82) {              /* OLSR_NAMESERVICE_MSG */
		name_entries = (msg_data[2] << 8) | msg_data[3];   /* CVE */
		n += (int)name_entries;
	}
	(void)end;
	return n;
}

int olsr_fixed(const unsigned char *in, unsigned caplen, unsigned claimed)
{
	unsigned char buf[16];
	const unsigned char *msg_data, *end;
	unsigned i, msg_type, msg_len, name_entries;
	int n = 0;

	if (caplen < 16)
		return -1;
	for (i = 0; i < 16; i++)
		buf[i] = in[i];
	end = buf + 16;

	msg_data = buf + 4;
	msg_type = buf[4];
	msg_len = (buf[6] << 8) | buf[7];
	if (msg_len > claimed)
		return -2;
	msg_data += 12;

	if (msg_type == 0x82) {
		if (msg_data + 4 > end)      /* the fix: ND_TCHECK before the fetch */
			return -3;
		name_entries = (msg_data[2] << 8) | msg_data[3];
		n += (int)name_entries;
	}
	return n;
}

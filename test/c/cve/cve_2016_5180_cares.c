// CVE:    CVE-2016-5180
// SOURCE: c-ares ares_create_query(), fix c1b5aa7 (write one past the allocation)
// KIND:   oob_write
// VULN:   createq_vuln
// FIXED:  createq_fixed
// ARGS:   --buf-max 16
//
// The size of the query buffer is worked out by ONE pass over the name and the bytes are written by ANOTHER.
// An escape sequence makes the two passes disagree about how many bytes the name costs, so the writing pass
// runs one past the end of what the sizing pass asked for.
//
// This fixture keeps the DISAGREEMENT, which is the defect, rather than c-ares' exact escape grammar: the
// sizing pass charges an escaped byte 1, the writing pass emits 2. A version where both passes shared one
// helper could not express the bug at all.

int createq_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char out[16];
	unsigned i, len, w;

	if (caplen < 8)
		return -1;

	/* pass 1: size it */
	len = 0;
	for (i = 0; i < 8; i++) {
		if (in[i] == 0)
			break;
		len++;                  /* CVE: an escaped byte is charged ONE here ... */
	}
	if (len + 2 > 16)
		return -2;

	/* pass 2: write it */
	w = 0;
	for (i = 0; i < 8; i++) {
		if (in[i] == 0)
			break;
		if (in[i] == '\\') {
			out[w++] = '\\';
			out[w++] = in[i];   /* ... and costs TWO here */
		} else {
			out[w++] = in[i];
		}
	}
	out[w] = 0;
	return (int)out[0];
}

int createq_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char out[16];
	unsigned i, len, w;

	if (caplen < 8)
		return -1;

	len = 0;
	for (i = 0; i < 8; i++) {
		if (in[i] == 0)
			break;
		len += (in[i] == '\\') ? 2u : 1u;   /* the fix: the two passes agree */
	}
	if (len + 2 > 16)
		return -2;

	w = 0;
	for (i = 0; i < 8; i++) {
		if (in[i] == 0)
			break;
		if (in[i] == '\\') {
			out[w++] = '\\';
			out[w++] = in[i];
		} else {
			out[w++] = in[i];
		}
	}
	out[w] = 0;
	return (int)out[0];
}

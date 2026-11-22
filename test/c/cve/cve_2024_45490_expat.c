// CVE:    CVE-2024-45490
// SOURCE: libexpat xmlparse.c:2066 (XML_ParseBuffer), fix ef485e96 adds `if (len < 0)`
// KIND:   ptr_arith_oob
// VULN:   parsebuffer_vuln
// FIXED:  parsebuffer_fixed
//
// `XML_ParseBuffer(parser, len, isFinal)` never checked `len` for negativity, so a negative length walked
// `m_bufferEnd` BACKWARDS, below the start of the buffer, and every later bound derived from it was wrong.
// The fix is one check at the top of the function.

int parsebuffer_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[16];
	const unsigned char *start, *bufferEnd, *parseEnd;
	unsigned i;
	int len;

	if (caplen < 8)
		return -1;
	for (i = 0; i < 16 && i < caplen; i++)
		buf[i] = in[i % 8];

	start = buf;
	bufferEnd = buf + 8;
	len = (int)(signed char)in[0];      /* attacker-controlled, and may be negative */
	if (len > 8)                        /* XML_GetBuffer's contract, held by BOTH versions */
		return -4;

	bufferEnd += len;                   /* CVE: walks below `buf` when len < 0 */
	parseEnd = bufferEnd;
	if (parseEnd < start)
		return -2;
	return (int)(parseEnd - start);
}

int parsebuffer_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[16];
	const unsigned char *start, *bufferEnd, *parseEnd;
	unsigned i;
	int len;

	if (caplen < 8)
		return -1;
	for (i = 0; i < 16 && i < caplen; i++)
		buf[i] = in[i % 8];

	start = buf;
	bufferEnd = buf + 8;
	len = (int)(signed char)in[0];
	if (len > 8)                        /* the same contract */
		return -4;
	if (len < 0)                        /* the fix: XML_ERROR_INVALID_ARGUMENT */
		return -3;

	bufferEnd += len;
	parseEnd = bufferEnd;
	if (parseEnd < start)
		return -2;
	return (int)(parseEnd - start);
}

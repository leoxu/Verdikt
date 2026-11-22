// CVE:    CVE-2022-23852
// SOURCE: libexpat xmlparse.c:2070 (XML_GetBuffer), fix 30f4455 adds the second overflow check
// KIND:   signed_overflow
// VULN:   getbuffer_vuln
// FIXED:  getbuffer_fixed
//
// The FIRST addition is guarded -- the comment in the source even says "Do not invoke signed arithmetic
// overflow" -- and then `neededSize += keep;` a few lines later is not:
//
//     int neededSize = (int)((unsigned)len + (unsigned)(bufferEnd - bufferPtr));
//     if (neededSize < 0) { ... return NULL; }        /* guarded */
//     keep = ...; if (keep > XML_CONTEXT_BYTES) keep = XML_CONTEXT_BYTES;
//     neededSize += keep;                             /* line 2070 -- NOT guarded */
//
// A fixture that only kept the first addition would test the check that was already there.

#define XML_CONTEXT_BYTES 1024

int getbuffer_vuln(const unsigned char *in, unsigned caplen)
{
	int len, have, neededSize, keep;

	if (caplen < 8)
		return -1;
	len = (int)((unsigned)in[0] << 24 | (unsigned)in[1] << 16 | (unsigned)in[2] << 8 | in[3]);
	have = (int)(in[4] & 0x7f);
	keep = (int)(in[5] & 0x7f);
	if (len < 0 || have < 0 || keep < 0)
		return -2;

	neededSize = (int)((unsigned)len + (unsigned)have);
	if (neededSize < 0)             /* the check that WAS there */
		return -3;
	if (keep > XML_CONTEXT_BYTES)
		keep = XML_CONTEXT_BYTES;
	neededSize += keep;             /* CVE: signed overflow */
	return neededSize;
}

int getbuffer_fixed(const unsigned char *in, unsigned caplen)
{
	int len, have, neededSize, keep;

	if (caplen < 8)
		return -1;
	len = (int)((unsigned)in[0] << 24 | (unsigned)in[1] << 16 | (unsigned)in[2] << 8 | in[3]);
	have = (int)(in[4] & 0x7f);
	keep = (int)(in[5] & 0x7f);
	if (len < 0 || have < 0 || keep < 0)
		return -2;

	neededSize = (int)((unsigned)len + (unsigned)have);
	if (neededSize < 0)
		return -3;
	if (keep > XML_CONTEXT_BYTES)
		keep = XML_CONTEXT_BYTES;
	if (neededSize > 0x7fffffff - keep)   /* the fix: guard the second addition too */
		return -4;
	neededSize += keep;
	return neededSize;
}

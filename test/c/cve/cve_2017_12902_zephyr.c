// CVE:    CVE-2017-12902
// SOURCE: tcpdump print-zephyr.c:96, fix d17507ff "Zephyr: Fix bounds checking"
// KIND:   oob_read
// VULN:   zephyr_vuln
// FIXED:  zephyr_fixed
//
// The guard is `<=`, so on the last iteration the pointer equals the end of the capture and `**pptr` reads one
// past it. The fix replaces the hand-rolled comparison with ND_TTEST, which uses `<`.
//
// Reaching the defect needs EVERY copied byte non-zero, which makes the witness long: before §22.417 the
// report printed sixteen of them and "(+N more)", and no external reproducer could be built from it.

int zephyr_vuln(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];

	p = buf;
	end = buf + 24;
	while (p <= end && *p)          /* CVE: `<=`, so *p at p == end is one past */
		p++;
	return (int)(p - buf);
}

int zephyr_fixed(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i;

	if (caplen < 24)
		return -1;
	for (i = 0; i < 24; i++)
		buf[i] = in[i];

	p = buf;
	end = buf + 24;
	while (p < end && *p)           /* the fix */
		p++;
	return (int)(p - buf);
}

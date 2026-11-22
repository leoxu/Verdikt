/* The "shared object" of dlsym_host.c: reachable only through a dlsym'd symbol name. */
int plugin_parse(const unsigned char *in, unsigned caplen)
{
	unsigned char buf[16];
	unsigned i, n;

	if (caplen < 2)
		return -1;
	n = in[0];                  /* attacker-controlled, never checked against sizeof(buf) */
	for (i = 0; i < n; i++)
		buf[i] = in[i + 1];     /* overflows buf when n > 16 */
	return buf[0];
}

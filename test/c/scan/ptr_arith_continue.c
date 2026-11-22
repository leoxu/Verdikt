/* A real defect sitting BEHIND an out-of-range pointer computation.
 *
 * `in - n` is a pointer before the object: undefined behaviour (C11 6.5.6p8), and the program only ever
 * compares it -- the `p + n > end` / `match = op - offset` idiom that decompressors, ring buffers and every
 * tcpdump printer open with.
 *
 * Until ENGINE_LIMITATIONS.md §7.12 the engine REPORTED that and STOPPED there, so everything after it was
 * never executed: `out[k]` below was unreachable at any budget and the scan came back with the weaker
 * finding at the wrong line. Now the arithmetic is recorded and the run goes on, so the write is found at
 * the write, with the right kind.
 *
 * `guarded` is the control: the same shape with the out-of-range pointer never formed. Without it this test
 * could not tell "walks past the arithmetic" from "stopped reporting bounds errors". */
int behind_ptr_arith(const unsigned char *in, unsigned int n)
{
	unsigned char out[16];
	const unsigned char *back;

	if (n == 0 || n > 64) return -1;
	back = in - n;                  /* out of the object: formal UB, compared below, never dereferenced */
	if (back < in) {
		unsigned int k = in[0];
		out[k] = 1;             /* REAL out-of-bounds write once k >= 16 */
		return 0;
	}
	return 0;
}

int guarded(const unsigned char *in, unsigned int n)
{
	unsigned char out[16];

	if (n == 0 || n > 64) return -1;
	{
		unsigned int k = in[0];
		if (k >= sizeof out) return -1;
		out[k] = 1;             /* in bounds: nothing to report */
		return 0;
	}
}

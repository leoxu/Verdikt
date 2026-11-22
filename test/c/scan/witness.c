// A finding whose witness is only usable if the report prints ALL of it (DESIGN.md §22.417).
//
// Two defects met here on the same day:
//   * the counterexample renderer capped the byte list at 16 and then printed "... (+N more)", so a finding
//     marked `replay: confirmed` could not be rebuilt by anyone but the engine -- which is exactly what an
//     external ground-truth step (native ASan) needs;
//   * the SYMBOLIC engine names entry parameters `nd.<base>.<counter>` while the concolic one uses `<base>`, so
//     every lookup in the witness printer missed and the object's size came out blank with the scalars as
//     anonymous `nondet` rows -- no `in_len`, no `len`.
// tcpdump CVE-2017-12902's ASan step was blocked by both until they were fixed.
//
// The shape below is that CVE's, minimised: the scan loop's guard is `<=`, so the last iteration dereferences
// one past the end. Reaching it needs EVERY byte of the buffer to be non-zero, which is what makes the witness
// long -- a 16-byte summary of a 24-byte all-non-zero input is not a reproducer.
int witness_scan(const unsigned char *in, unsigned len)
{
	unsigned char buf[24];
	const unsigned char *p, *end;
	unsigned i;

	if (len < 24)
		return -1;
	/* The bytes are copied into a FIXED-SIZE local, exactly as the tcpdump harness does, so that a read past
	   the end is out of bounds of a real object. Scanning a synthesised parameter object instead would hit the
	   §22.403 trap: the object may legally be larger than `len`, and then the read past `len` is defined and
	   the fixture proves nothing. */
	for (i = 0; i < 24; i++)
		buf[i] = in[i];

	p = buf;
	end = buf + 24;
	while (p <= end && *p)      /* `<=`: at p == end this reads buf[24] */
		p++;
	return (int)(p - buf);
}

/* DESIGN.md Sec.22.461. A tainted buffer carries one SOFT preference from InitGen -- `size(buf) <= 64`
 * -- and the generated spec carries the hard relation `len <= size(buf)`. Ask for a seed length above
 * 64 and the preference is correctly rejected; what went wrong was what happened next. SeedSolver only
 * re-checked when at least one preference survived, so with the single preference rejected the model was
 * read off the solver's last, UNSAT, check: all zeros, while the result still said Sat. The entry then
 * ran with len = 0, returned at the guard, and the report said `blocks_visited 0` with nothing naming
 * the cause.
 *
 * 64 bytes is exactly where real format headers stop fitting -- ar's member header is 68, cpio's newc
 * header 110 -- so this silently blocked every entry of the libarchive profile. */
unsigned long seed_value_large_sink;

int
seed_value_large(const unsigned char *in, unsigned int in_len)
{
	unsigned int i;

	if (in_len == 0 || in_len > 96)
		return -1;
	for (i = 0; i < in_len; i++)
		seed_value_large_sink += in[i];
	return (int) in_len;
}

/* Fixture for --dump-branches: the three reasons an edge can be missing must come back DIFFERENT.
 *
 * A branch-coverage percentage on its own is not actionable, because it adds together things that need
 * opposite responses: one of these is worth spending budget on and two of them are not (DESIGN.md §22.429). */
int dump_branches(const unsigned char *in, unsigned int n)
{
	/* `const`: the condition is a compile-time fact, so the engine never sees a symbolic value here and the
	   false edge can never be taken. No budget changes that -- it is not a search failure. */
	if (sizeof(int) < 2) return -1;

	if (n == 0 || n > 64) return -1;

	/* `unsat`: inside this branch n <= 8, so the inner test cannot hold. The solver is asked and says so. */
	if (n <= 8) {
		if (n > 32) return 2;
		return 1;
	}
	return (int)in[0];
}

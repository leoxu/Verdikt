/* a goto jumps past a declaration in the same scope: the end-of-scope lifetime marker is not dominated by the declaration */
int skip_decl(int n) {
	int r = 0;
	{
		if (n == 0)
			goto done;
		int tmp = n & 7;
		r = tmp;
	done:
		r += 1;
	}
	return r;
}

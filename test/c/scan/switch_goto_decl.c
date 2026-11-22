/* A declaration shared across fallthrough `case` labels inside one unclosed brace, with a `goto` that skips part of
   it from an earlier case (the SQLite VDBE-interpreter idiom, see DESIGN.md): the entry edge via `case 1`/`case 2`
   reaches `tmp`'s uses directly through the switch's own dispatch, never passing through `case 0`'s block where
   the declaration is lexically written, so its `core.alloca` must be hoisted to the entry block to dominate them.
   Every path reassigns `tmp` before the final `return`, so there is no genuine UB here: this fixture is only about
   whether the function lowers and verifies at all, not about any particular finding. */
int shared_locals(int op, int x) {
	switch (op) {
	case 0: {
		int tmp = x;
		if (x == 0)
			goto merged;
		tmp = op;
	case 1:
	case 2:
		tmp = op;
	merged:
		return tmp;
	}
	}
	return -1;
}

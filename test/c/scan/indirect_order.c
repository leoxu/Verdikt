/* The indirect-call dispatcher's candidate order must not depend on the address space (DESIGN.md §22.443).
 *
 * With `--link`, hlir::link turns every call through a function pointer into `@__hlir_indirect.<sig>`, a chain of
 * `core.ptr_cmp` tests against the program's address-taken functions. It builds that chain by walking the list the
 * frontend hands it -- and that list used to be filled by iterating a `std::set<const FunctionDecl *>`, i.e. in the
 * order clang happened to ALLOCATE those AST nodes. That order moves with ASLR, so two runs of the same hlir-scan
 * command produced linked modules that differed in the order of the tests, and the analysis differed with them:
 * the same single deterministic first run took 15185 steps or 15188 depending on the process.
 *
 * The names below are deliberately not in source order, so a dispatcher that simply followed the source would fail
 * this too -- the requirement is a FIXED order, and sorted-by-name is the one that can be checked. */
typedef int (*op_t)(int);

static int zulu(int x) { return x + 1; }
static int alpha(int x) { return x + 2; }
static int mike(int x) { return x + 3; }
static int bravo(int x) { return x + 4; }
static int yankee(int x) { return x + 5; }

op_t ops_table[5] = {zulu, alpha, mike, bravo, yankee};

int pick(unsigned i, int v) { return ops_table[i % 5](v); }

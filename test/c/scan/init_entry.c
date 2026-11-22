// The project's own initialiser, run before the entry (`init:` / `--init-fn`, DESIGN.md §22.368).
//
// A handler is never called in the state the scanner starts it in: until `module_init` (a Linux driver), `main` (a
// server or QNX resource manager) or a `constructor`/`_init` (a shared library) has run, every global still holds
// its static initialiser. G1 (§22.362) measured the cost: a branch decided by such a global produces a false
// finding on the edge the real module would never take AND a silent coverage loss on the edge it would, at once.
//
// Four things are checked here, and the last two are the ones a small fixture is the only honest way to pin down,
// because the real-corpus round that found them (sound/core 49b) had them tangled together:
//
//   1. the initialiser actually RUNS           -- `g_limit` is zero until `demo_init_b` sets it
//   2. the initialisers run IN ORDER           -- `demo_init_b` only sets it if `demo_init_a` ran first
//   3. UB INSIDE an initialiser does not decide the entry's verdict ...
//   4. ... and does not stop the entry from being analysed
//
// 3 and 4 are the whole content of the round-49b fix. Before it, one deterministic `ptr_arith_oob` in
// `snd_info_register` -- the empty-list `container_of` that `list_for_each_entry` performs, a benign kernel idiom
// -- halted the FIRST run of every one of sound/core's 87 entries: block coverage fell 70%, all 87 verdicts became
// `bug` citing that one init-path site, and the 58 findings the entries really had vanished. A finding whose cause
// is init code the attacker never drives may not decide the entry, exactly as a finding decided only by the
// harness's own frontier filler may not (§22.365).

static char buf[8];

// ---- 1 and 2: the initialisers, and the order between them -------------------------------------------------
static int g_phase;   // 0 until demo_init_a runs
static int g_limit;   // 0 until demo_init_b runs, AND ONLY IF demo_init_a ran first

void demo_init_a(void) { g_phase = 1; }

void demo_init_b(void) {
  if (g_phase == 1) g_limit = 8;   // the dependency: without demo_init_a this does nothing
}

// ---- 3 and 4: an initialiser that performs real UB, harmlessly ----------------------------------------------
// `&g_tbl[0] - 1` is exactly the shape of `container_of(head, T, list)` on an empty list: a pointer computed
// before the start of the object, which the code then never dereferences. Strictly UB, universally harmless, and
// extremely common in real initialisation code -- which is why it must not be allowed to speak for the entry.
static int g_tbl[4];
static int *g_cursor;

void demo_init_ub(void) {
  g_cursor = &g_tbl[0] - 1;   // ptr_arith_oob here, inside the prologue
  g_cursor = &g_tbl[0];       // ... and the initialiser carries on and finishes its job
}

// ---- the entries --------------------------------------------------------------------------------------------

// Reachable only while `g_limit` is still zero, i.e. only if the initialisers did not run. The out-of-bounds read
// behind it is dead in the real module, so running the initialisers must make it disappear -- and NOT running
// them (or running `demo_init_b` alone) must leave it there, which is what proves the order matters.
int demo_init_gated(unsigned idx) {
  if (g_limit == 0) return buf[idx + 100];
  return buf[idx & 7u];
}

// A defect of the ENTRY's own, which no initialiser touches. It has to survive: the point of 3 and 4 is that the
// prologue's own UB stops deciding things, not that findings stop being reported.
int demo_init_real_oob(unsigned idx) { return buf[idx]; }

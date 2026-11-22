// A more complex `--reach-target` demo: the actual brotli CVE-2026-111497 shape (docs/DESIGN.md Sec.22.322),
// scaled down to a few dozen lines -- a "block switch" function that sets a state field on its success path but
// NOT on its early-return failure path, and a reader several call frames away that trusts the field without
// checking it. Unlike reach_demo.c (a single branch gated on one exact value), reaching the bug here needs TWO
// independent conditions to both hold (block_switch's failure path AND read_symbol's specific selector), and the
// write/read sites are in different functions three frames apart -- the actual shape findWriteSites/reachWriteSite
// (docs/DESIGN.md Sec.22.329/22.330) are built to locate and target, not just a single easy-to-spot branch.

typedef struct {
  int ready;  // 0 = not ready. block_switch's success path sets it to 1; nothing ever resets it to 0 again.
} Ctx;

// Mirrors DecodeXxxBlockSwitchInternal (Sec.22.322): num_types<=1 returns early WITHOUT touching `ready` at all.
void block_switch(Ctx *c, int num_types) {
  if (num_types <= 1) {
    return;  // the candidate write site this path skips: c->ready is left at whatever it already was
  }
  c->ready = 1;
}

// Mirrors ReadXxxInternal: trusts `ready` without re-deriving it; the read site findWriteSites would anchor at.
void read_symbol(Ctx *c, int selector) {
  if (c->ready) {
    // normal, safe path -- nothing interesting here
  } else {
    // only reachable when block_switch's failure path was taken AND the caller is asking for this one selector
    int *bad = 0;
    if (selector == 777) *bad = 1;
  }
}

void process_block(Ctx *c, int num_types, int selector) {
  block_switch(c, num_types);
  read_symbol(c, selector);
}

void noise(int seed) {
  int acc = seed % 100;  // clamped: pure noise, no signed_overflow of its own (see reach_demo.c)
  if (acc > 1) acc += 1; else acc -= 1;
  if (acc > 2) acc += 1; else acc -= 1;
  if (acc > 3) acc += 1; else acc -= 1;
  if (acc > 4) acc += 1; else acc -= 1;
  if (acc > 5) acc += 1; else acc -= 1;
  if (acc > 6) acc += 1; else acc -= 1;
  if (acc > 7) acc += 1; else acc -= 1;
  if (acc > 8) acc += 1; else acc -= 1;
  if (acc > 9) acc += 1; else acc -= 1;
  if (acc > 10) acc += 1; else acc -= 1;
  if (acc > 11) acc += 1; else acc -= 1;
  if (acc > 12) acc += 1; else acc -= 1;
  if (acc > 13) acc += 1; else acc -= 1;
  if (acc > 14) acc += 1; else acc -= 1;
  if (acc > 15) acc += 1; else acc -= 1;
  if (acc > 16) acc += 1; else acc -= 1;
  if (acc > 17) acc += 1; else acc -= 1;
  if (acc > 18) acc += 1; else acc -= 1;
  if (acc > 19) acc += 1; else acc -= 1;
  if (acc > 20) acc += 1; else acc -= 1;
}

void reach_demo2_entry(int seed, int num_types, int selector) {
  Ctx c;
  c.ready = 0;  // mirrors a freshly-created decoder state, before any block_switch call ever ran
  noise(seed);
  process_block(&c, num_types, selector);
}

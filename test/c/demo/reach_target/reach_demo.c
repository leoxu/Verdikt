// Small demo program for `hlir-scan --reach-target`, not a project test (scratch file). Shape: `entry` first
// walks through 20 "noise" branches (tainted, but irrelevant to the bug -- just there to swamp a coverage-guided
// search), then calls into `near(z)` -> `target(z)`, which has the real bug (a null-pointer write) gated behind a
// single hard-to-guess-by-chance condition (`z == 123456789`). With a tiny per-entry run budget, the default
// coverage-guided search spends it all on the noise branches and never gets to `target`'s own branch; with
// `--reach-target target`, the search frontier is reordered by call-graph distance to `target` so `near`'s single
// branch (distance 1) is tried before any of `noise`'s (unreachable from `target`, so lowest priority), reaching
// the bug inside the same tiny budget.

void noise(int seed) {
  int acc = seed % 100;  // clamp away from INT_MIN/MAX so these branches are pure "noise" (no signed_overflow of their own)
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

void target(int z) {
  if (z == 123456789) {
    int *bad = 0;
    *bad = 1;  // the real bug: null-pointer write, only on this one exact value of z
  }
}

void near(int z) {
  target(z);
}

void reach_demo_entry(int seed, int z) {
  noise(seed);
  near(z);
}

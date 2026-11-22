// FIXED (2026-10-25, see docs/DESIGN.md Sec.22.306/22.307 for the full story): a minimal structural mirror of
// the brotli CVE-2026-111497 investigation's final bottleneck (Sec.22.301/302; docs/KNOWN_GAPS_PRIORITIZED.md
// "污染驱动的深层循环/长约束合取链展开代价过高"). Was `unknown`/time-budget-exhausted for a long time (see the
// git-free history in DESIGN.md Sec.22.303/304/305 for the diagnosis and a failed fix attempt); now reaches
// `bug`/replay-confirmed within budget. test/c/scan_tests.cpp asserts this.
//
// Mechanism: counter/trigger are direct scalar params pinned via taint:value,range:[N,N] (see the companion
// spec in deep_loop_taint_scalar_spec/consume.yaml) -- a SINGLE-POINT range (lo==hi). The fix (InitGen.cpp +
// TaintDomain.h's decide(), Sec.22.307) makes such a parameter a real constant term instead of a free
// variable plus an equality constraint, so the SMT term library's existing constant folding (Term.cpp's
// foldConst) propagates it through the loop's arithmetic automatically: `counter`'s value folds to a new
// literal every `counter--`, and the loop condition folds to a literal boolConst every iteration instead of
// staying a genuine free-variable comparison. decide() skips recording an already-constant condition as a
// "flippable" branch decision (there's nothing to flip: provably fixed, not just "happened to go this way on
// this run"), which is what used to make a 2,000,000-iteration loop record ~2,000,000 near-duplicate flip
// candidates (the root cause identified in Sec.22.304).
//
// Before the fix: `hlir-scan --entry consume --spec-dir deep_loop_taint_scalar_spec --timeout 60 --max-steps
// 3000000` -> verdict: unknown, incomplete: [time_budget, no_run_completed], solver_queries=468, sec_solve
// ~25s dominant. After the fix, same command: solver_queries=0, pure step-budget behaviour identical to the
// fully-untainted sibling (test/c/scan/deep_loop_concrete.c) -- raising --max-steps to actually clear the
// 2,000,000-iteration loop (needs roughly 33 interpreter steps/iteration, ~66,000,000 total) gives verdict:
// bug, oob_write@consume replay-confirmed, incomplete: [] (a fully complete verdict). See
// test/c/scan/deep_loop_taint_where.c for the sibling case this fix does NOT help (buffer bytes pinned via
// --spec-dir's `where:` byte preconditions go through the assume()+repair mechanism at runtime, never become
// literal constant terms the way a single-point scalar range does at plan time -- still open).
void consume(unsigned int counter, int trigger) {
  unsigned char buf[8];
  unsigned int pos = 0;
  while (counter != 0) {
    buf[pos & 7] = (unsigned char)(trigger ^ 0x5A);
    pos++;
    counter--;
  }
  if (trigger == 0x99) {
    buf[8] = 0xFF;
  }
}

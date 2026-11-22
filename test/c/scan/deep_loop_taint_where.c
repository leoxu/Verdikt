// INVESTIGATION FIXTURE, STATUS: open, not yet fixed -- sibling of deep_loop_taint_scalar.c (see that file's
// header for full context: docs/DESIGN.md brotli CVE-2026-111497 series Sec.22.301/302 and the 2026-10-25
// minimal-repro follow-up; docs/KNOWN_GAPS_PRIORITIZED.md "污染驱动的深层循环/长约束合取链展开代价过高").
//
// Same loop shape, but the trip count is derived from individual buffer BYTES pinned via --spec-dir's
// `where:` byte preconditions (see the companion spec in deep_loop_taint_where_spec/consume.yaml) instead of
// deep_loop_taint_scalar.c's direct scalar taint:value pinning. This mechanism DOES need repair rounds: each
// `where:` byte precondition violates the all-zero M0 benign seed, and TaintDomain's repair_ (TaintDomain.h
// ~256-263) only captures one violated tainted assumption per run, so N independent `where:` bytes cost
// roughly N sequential repair-and-retry rounds before a run can even reach the loop for real.
//
// Baseline behaviour as of 2026-10-25 (6 `where:` byte preconditions -- offsets 9-14 pinning counter=2000000
// and the post-loop trigger byte):
//   `hlir-scan --entry consume --spec-dir deep_loop_taint_where_spec --timeout 60 --max-steps 3000000`
//   -> verdict: unknown, incomplete: [time_budget, no_run_completed]; runs=6 (repair rounds, consistent with
//   needing ~6 to satisfy 6 independent where: bytes), solver_queries=624, sec_solve=~25.5s.
// Comparing this to deep_loop_taint_scalar.c's runs=1/solver_queries=468/sec_solve=~25s: removing the repair
// mechanism (scalar taint:value pinning, zero repair rounds) did NOT meaningfully reduce the dominant solver
// cost -- so the repair mechanism's extra ~5 rounds are a real but secondary cost on top of the primary one,
// which is intrinsic to walking a long loop whose trip count is tainted at all (see that file's header for
// the isolated mechanism: TaintDomain.h:231 marking every iteration's core.cond_br flippable).
//
// Once the underlying issue is fixed, this fixture should additionally verify the repair-mechanism overhead
// specifically doesn't regress back to needing O(preconditions) sequential full-loop walks.
//
// STATUS UPDATE (2026-10-25, DESIGN.md Sec.22.306/22.307): the scalar sibling (deep_loop_taint_scalar.c) got
// fixed -- a single-point taint:value,range:[N,N] scalar param is now a real constant term instead of a free
// variable, so the loop condition constant-folds away. Confirmed (re-ran this exact fixture after that fix)
// that it does NOT help here: the loop's trip count here comes from individual buffer BYTES pinned via
// --spec-dir's `where:` mechanism, which goes through the runtime assume()+repair path, not InitGen's
// plan-time single-point scalar handling -- those bytes never become literal constant terms, so the loop
// condition stays a genuine (if ultimately always-true-until-the-last-iteration) free-variable comparison and
// every iteration is still recorded as a flippable branch. This case remains open.
void consume(const unsigned char *in, int in_len) {
  if (in_len < 15) return;
  unsigned int counter = ((unsigned)in[9] << 24) | ((unsigned)in[10] << 16) | ((unsigned)in[11] << 8) | in[12];
  unsigned char buf[8];
  unsigned int pos = 0;
  while (counter != 0) {
    buf[pos & 7] = (unsigned char)(in[13] ^ 0x5A);
    pos++;
    counter--;
  }
  if (in[14] == 0x99) {
    buf[8] = 0xFF;
  }
}

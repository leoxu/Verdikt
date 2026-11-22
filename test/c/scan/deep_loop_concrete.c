// Synthetic regression for the maxSteps CLI gap (docs/KNOWN_GAPS_PRIORITIZED.md, "maxSteps预算硬编码"):
// a no-arg, fully concrete entry whose loop alone costs far more interpreter steps than hlir-scan's
// default 1,000,000-step-per-run budget (lib/semantics/Taint.h TaintConfig::maxSteps), before it reaches
// a real one-byte out-of-bounds write. Mirrors the shape of CVE-2025-32023 (hllSparseToDense(): a real
// OOB write gated behind ~130,000 real loop iterations) without depending on an external source tree.
//
// At the default budget: the run is cut by step_limit before the write, reported incomplete/unknown.
// With --max-steps raised past the loop's real step cost: the run completes and the OOB write is found.
#include <stdint.h>

static unsigned char buf[8];

void deep_loop_concrete(void) {
  volatile int32_t sink = 0;
  for (int32_t i = 0; i < 140000; i++) {
    sink += i & 7;
  }
  buf[8] = (unsigned char)sink;  // one byte past the end of buf[8]: a real out-of-bounds write
}

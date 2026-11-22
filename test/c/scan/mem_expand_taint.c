// Synthetic regression for the kMaxExpand CLI gap on the *primary* concolic/taint engine (TaintExecutor), not just
// the symbolic escalation pass (docs/KNOWN_GAPS_PRIORITIZED.md, "kMaxExpand硬编码"). A no-arg, fully concrete entry
// whose memcpy length is a compile-time constant one byte over Memory::kMaxExpandDefault (1<<20): lib/semantics/
// Memory.h's bulk() refuses to physically expand it and the run ends RunStatus::Unsupported before reaching the
// real one-byte out-of-bounds write that follows. Mirrors the shape of the Redis CVE-2022-24834 / libxml2
// CVE-2026-86138 scenarios (a real bug gated behind a near-1MB memcpy) without depending on an external source tree.
//
// At the default --mem-expand-max (1048576 = 1<<20): the memcpy is rejected, the run is cut incomplete:unsupported
// before the write. With --mem-expand-max raised past N: the memcpy completes and the OOB write is found (bug).
#include <string.h>

#define N ((1u << 20) + 1)  // Memory::kMaxExpandDefault + 1: one byte over the default cap

static unsigned char src[N];
static unsigned char dst[N];

void mem_expand_taint(void) {
  memcpy(dst, src, N);  // constant length, one byte over the default kMaxExpand cap
  dst[N] = 1;           // one byte past the end of dst: a real out-of-bounds write
}

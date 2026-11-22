// same_alloc regression fixture: the base/end cursor-pair idiom (NFS xdr_stream's p/end, QuickJS BCReaderState,
// Duktape valstack_top/bottom) -- `end` must be a one-past-the-end view into the SAME allocation `p` was
// synthesized into (see docs/KNOWN_GAPS_PRIORITIZED.md's "two pointer fields must point to same allocation" P1
// entry and InitGen.cpp's PlannedField::sameAllocIndex / HarnessGen.cpp's same_alloc emission).
typedef struct {
  char *p;
  char *end;
} stream_t;

// correctly stops at end: safe
int stream_consume_safe(stream_t *s) {
  while (s->p < s->end) {
    *s->p = 0;
    s->p++;
  }
  return 0;
}

// off-by-one (<= instead of <): writes one byte past the real end of the SAME allocation
int stream_consume_bug(stream_t *s) {
  char *p = s->p;
  while (p <= s->end) {
    *p = 0;
    p++;
  }
  return 0;
}

// Externally-mutable memory / double-fetch (TOCTOU) regression fixture (docs/KNOWN_GAPS_PRIORITIZED.md's "no
// external/volatile memory" P1 entry). `h` models shared memory / an mmap'd device register / a DMA buffer: a real
// second actor (attacker process, hardware) can change its bytes between two reads with no store in between.
//
// n_elems is read twice: once to validate it against MAX_ELEMS, once (independently) to size a memcpy into a
// fixed-size buffer. Under HLIR's ordinary deterministic memory model the two reads are the SAME cached symbolic
// value, so the validating check also bounds the second read and the memcpy can never overflow -- the TOCTOU window
// is invisible. When the spec declares `h` `externally_mutable: true`, each core.load against it gets its own fresh,
// independently-tainted value (Machine.h Opc::Load / Memory.h markExternallyMutable()), so the two reads can
// disagree and the real race is detectable.
#include <string.h>

struct hdr {
  unsigned n_elems;
  char data[64];
};

#define MAX_ELEMS 16

int consume_toctou(struct hdr *h) {
  char buf[MAX_ELEMS];
  if (h->n_elems > MAX_ELEMS) return -1;  // validating read
  unsigned n = h->n_elems;                // using read: may disagree with the validated value when h is externally mutable
  memcpy(buf, h->data, n);
  return 0;
}

// Pointer-typed loads against an externally-mutable object are explicitly out of scope for this MVP (constructing a
// legal obj id for such a read needs more design) and must keep the ordinary cached-load behaviour: two loads of the
// same pointer field at the same offset, no store in between, must still observe the same pointer.
struct phdr {
  struct hdr *inner;
};

int consume_ptr_load(struct phdr *h) {
  struct hdr *a = h->inner;
  struct hdr *b = h->inner;
  return a == b;
}

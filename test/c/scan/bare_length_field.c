// Regression for the bare-generic-sibling-length-name fallback in findSiblingLenField()
// (lib/frontend/Frontend.cpp): a struct whose only buffer-ish field's real size is described by a sibling
// field with a BARE generic name (not derived from the buffer field's own name at all) -- the real-world
// instance that motivated this fix is OpenSSL's `SSL3_RECORD { unsigned int length; ...; unsigned char *data; }`
// (CVE-2014-0160/Heartbleed: `tls1_process_heartbeat` reads an attacker-declared payload length and memcpy's
// that many bytes out of `rrec.data`, whose real allocation is `rrec.length` bytes -- a sibling pair the
// original name-composite candidate list (data -> datalen/data_size/...) could never match, because "length"
// has no textual relation to "data" at all). This fixture reproduces the same shape in miniature.
#include <stddef.h>

struct record { int type; unsigned int length; unsigned char *data; };

int consume(struct record *r) {
  if (r->length == 0) return -1;
  return r->data[r->length - 1];
}

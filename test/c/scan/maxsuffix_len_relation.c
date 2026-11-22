// Regression for isLenName() recognizing the "_max"/"Max" suffix (ground-truth verified against zlib's real
// CVE-2022-37434: gz_header::extra_max, a buffer's declared capacity, was never recognized as a length-ish
// name, so the top-level length<->buffer relation never tied the synthesized `extra_buf`'s size to it -- a
// repro without this fix could not cleanly distinguish the vulnerable code from the fixed code; see
// docs/DESIGN.md's ground-truth write-up). Mirrors the real inflate.c EXTRA-case computation: `length`/`copy`
// obey the real invariant (0 <= length <= extra_len, copy <= length) that the real state machine maintains
// across calls; the bug is that `len = extra_len - length` is used for pointer arithmetic/memcpy without ever
// checking `len < extra_max` first.
#include <string.h>
typedef unsigned char Bytef;
typedef unsigned int uInt;
struct gz_header_s { Bytef *extra; uInt extra_len; uInt extra_max; };

int consume(unsigned char *extra_buf, unsigned extra_max, unsigned extra_len,
            unsigned length, const unsigned char *next, unsigned copy) {
  if (length > extra_len) return -1;
  if (copy > length) return -1;
  unsigned len;
  struct gz_header_s hdr;
  hdr.extra = extra_buf;
  hdr.extra_len = extra_len;
  hdr.extra_max = extra_max;
  struct gz_header_s *head = &hdr;
  if (head->extra != (void*)0) {
    len = head->extra_len - length;
    memcpy(head->extra + len, next,
           len + copy > head->extra_max ? head->extra_max - len : copy);
  }
  return 0;
}

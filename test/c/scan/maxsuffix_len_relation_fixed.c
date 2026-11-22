// Sibling of maxsuffix_len_relation.c with the real zlib CVE-2022-37434 fix applied (commit eff308af): the
// `len < head->extra_max` guard before touching extra/len at all. Confirms the from-"_max"-suffix relation
// fix doesn't suppress the safe case -- the real fix should scan safe_under_assumptions, 100% coverage.
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
  len = head->extra_len - length;
  if (head->extra != (void*)0 && len < head->extra_max) {
    memcpy(head->extra + len, next,
           len + copy > head->extra_max ? head->extra_max - len : copy);
  }
  return 0;
}

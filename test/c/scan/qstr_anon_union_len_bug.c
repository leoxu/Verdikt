// Sibling of qstr_anon_union_len.c: same struct/field shape (len packed inside an anonymous union/struct,
// struct-qstr style), but without the `len == 0` guard, so `q->len - 1` underflows to UINT_MAX when len is 0
// -- a genuine out-of-bounds read. Confirms the anonymous-union recursion fix does not suppress a real bug
// just because it also eliminates the spurious independent-size finding (mirrors
// sibling_size_field_auto_bug.c / bare_length_field_bug.c's counterparts).
#include <stddef.h>

struct qstr_like {
  const unsigned char *name;
  union {
    unsigned long long hash_len;
    struct { unsigned int hash, len; };
  };
};

int consume(struct qstr_like *q) {
  return q->name[q->len - 1];
}

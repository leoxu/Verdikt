// Regression for findSiblingLenField()'s anonymous-union/struct recursion (lib/frontend/Frontend.cpp,
// collectFieldsForLenSearch): the real-world shape that motivated this is VFS's `struct qstr`:
//   struct qstr { union { u64 hash_len; struct { u32 hash, len; }; }; };
// `len` is not a direct field of the outer struct -- Clang's RecordDecl::fields() only ever yields the
// anonymous union as a single unnamed FieldDecl, so without recursing into it, findSiblingLenField() could
// never see `len` as a candidate at all (not a bitfield issue -- an anonymous union/struct member is a
// different, much narrower Clang construct). `len` has no textual relation to `name`, so once visible it is
// only found via the bare-generic-name fallback (see bare_length_field.c), same as upstream `struct qstr`.
#include <stddef.h>

struct qstr_like {
  const unsigned char *name;
  union {
    unsigned long long hash_len;
    struct { unsigned int hash, len; };
  };
};

int consume(struct qstr_like *q) {
  if (q->len == 0) return -1;
  return q->name[q->len - 1];
}

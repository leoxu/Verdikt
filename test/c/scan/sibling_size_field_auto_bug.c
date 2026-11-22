// Sibling of sibling_size_field_auto.c: same struct/field shape, but without the `datalen == 0` guard, so
// `el->datalen - 1` underflows to SIZE_MAX when datalen is 0 -- a genuine pointer-arithmetic UB. Confirms the
// auto-discovery `from_field` fix does not suppress a real bug just because it also eliminates the spurious
// independent-size finding (mirrors test/c/entry/sibling_size_field_bug.c's hand-written-spec counterpart).
#include <stddef.h>

struct element {
  unsigned char *data;
  size_t datalen;
};

int consume(struct element *el) {
  unsigned char last = el->data[el->datalen - 1];
  return last;
}

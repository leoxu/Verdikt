// ENTRY: consume
// SPEC: sibling_size_field.yaml
// EXPECT: bug ptr_arith_oob
//
// Sibling of sibling_size_field.c: same `size: {from_field: ...}` spec (reused via the same SPEC file, the kind
// name must match this file's ENTRY), but without the `datalen == 0` guard -- confirms the fix doesn't suppress a
// REAL bug (datalen==0 underflows `datalen - 1` to SIZE_MAX, a genuine pointer-arithmetic UB) just because it also
// eliminates the spurious independent-size finding.
#include <stddef.h>

struct element {
  unsigned char *data;
  size_t datalen;
};

int consume(struct element *el) {
  unsigned char last = el->data[el->datalen - 1];
  return last;
}

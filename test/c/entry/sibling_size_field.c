// ENTRY: consume
// SPEC: sibling_size_field.yaml
// EXPECT: safe
//
// Regression for the relations-DSL sibling-field-pair gap (field `size: {from_field: ...}` in Spec.cpp/InitGen.cpp/
// HarnessGen.cpp): `el->data`'s real allocation size must equal `el->datalen`'s own value, not an independent
// synthesized size -- without the fix, `el->data[el->datalen - 1]` reports a spurious oob_read because `data` is
// synthesized with an unrelated, usually-too-small size (see DESIGN.md's relations-DSL-gap root-cause family,
// recurred a dozen+ times across the open-source/kernel testing series: zlib/mbedtls/mpack/lz4/libtiff/...).
#include <stddef.h>

struct element {
  unsigned char *data;
  size_t datalen;
};

int consume(struct element *el) {
  if (el->datalen == 0) return -1;
  unsigned char last = el->data[el->datalen - 1];
  return last;
}

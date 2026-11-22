// Regression for the auto-discovery side of the relations-DSL sibling-field-pair fix (DESIGN.md §22.105 added
// Spec.cpp/InitGen.cpp/HarnessGen.cpp's `size: { from_field: ... }`, but cmark/Duktape §22.127/130 found that
// `--entries all`'s automatic spec synthesizer never actually emitted it -- it only ever fired on hand-written
// specs. This fixture (distinct from test/c/entry/sibling_size_field.c, which pins the hand-written-spec path via
// a SPEC: directive) exercises the auto-discovery path directly: Frontend.cpp's findSiblingLenField() must notice
// that `data`'s struct has a sibling `datalen` field and record it on the PtrFieldInfo, and Scan.cpp's fieldsYaml()
// must turn that into a `size: { from_field: ... } }` clause in the *generated* spec, not an independent range.
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

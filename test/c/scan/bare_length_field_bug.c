// Sibling of bare_length_field.c: same struct/field shape, but reads one byte past the declared length
// (`r->data[r->length]` instead of `r->data[r->length - 1]`) -- confirms the fallback fix doesn't suppress a
// real bug just because it also ties `data`'s size to `length`.
#include <stddef.h>

struct record { int type; unsigned int length; unsigned char *data; };

int consume(struct record *r) {
  if (r->length == 0) return -1;
  return r->data[r->length];
}

// Regression for the fix to the declarative `strlen` ModelDB model (models/libc.core): it used to be purely
// declarative (models/libc.yaml's `returns: { strlen: 0 }`), implemented by the engine as an opaque,
// concrete-bytes-only native primitive (cstrlen() in lib/semantics/Memory.h) with no real branch-structured IR --
// invisible to the concolic engine's branch-flipping exploration and unsupported by the symbolic engine on
// genuinely symbolic bytes ("string length needs concrete bytes"). Mirrors the real-world shape this was found
// against: OpenSSL's CVE-2021-3712 (ASN1_STRING's {length;data} pair is not guaranteed NUL-terminated within
// `length` bytes, but code across the codebase called strlen()/OPENSSL_strdup() on `->data` directly). `len` is
// sibling-field-linked to `data`'s real size (§22.105/133's `from_field` mechanism), so `data` is exactly
// `len` bytes with no NUL guaranteed -- if none of those bytes happen to be 0, strlen() walks past the object end.
#include <stddef.h>
struct holder { unsigned char *data; int len; };
int consume(struct holder *h) {
  if (h->len <= 0) return -1;
  return (int)strlen((const char *)h->data);
}

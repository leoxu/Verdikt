// ENTRY: parse
// EXPECT: bug oob_read
// SPEC: parse.yaml
#include <string.h>
struct pkt { int len; char data[8]; };
int parse(const struct pkt *p, char *out) {
  if (p->len > 64) return -1;        /* data[] only holds 8 bytes */
  memcpy(out, p->data, p->len);
  return p->len;
}

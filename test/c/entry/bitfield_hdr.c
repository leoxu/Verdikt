// ENTRY: parse_hdr
// EXPECT: bug oob_write
// SPEC: hdr.yaml
// a 4-bit length field from the wire used to index a 8-byte buffer
struct hdr { unsigned type : 4; unsigned len : 4; };
int parse_hdr(const struct hdr *h) {
  char buf[8];
  for (unsigned i = 0; i <= h->len; i++) buf[i] = (char)i;   /* len up to 15 */
  return buf[0] + h->type;
}

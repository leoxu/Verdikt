// Sibling of sockaddr_len.c: same signature shape, but with a real off-by-one past the declared addr_len (reads
// `p[addr_len]` instead of `p[addr_len - 1]`) -- confirms the sockaddr/addr_len relation fix does not suppress a
// real bug just because it also eliminates the spurious independent-size finding.
struct sockaddr {
  unsigned short sa_family;
  char sa_data[14];
};

int consume(const struct sockaddr *uaddr, int addr_len) {
  if (addr_len < (int)sizeof(unsigned short)) return -1;
  const char *p = (const char *)uaddr;
  char last = p[addr_len];
  return last;
}

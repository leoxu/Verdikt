// Regression for P0 item 2 of docs/KNOWN_GAPS_PRIORITIZED.md: `struct sockaddr *addr, socklen_t addr_len`-shaped
// top-level parameters (the single highest-frequency signature in the Linux BSD-socket layer -- unix_bind/connect,
// and every protocol family's own bind/connect, all take this shape) were never linked to each other because
// `isByteBuffer()` only recognised `void*`/`int*` pointees, never `struct`. `addr` got synthesized as a fixed
// `sizeof(struct sockaddr)`-byte object regardless of what `addr_len` claimed, producing a spurious oob_read/
// ptr_arith_oob whenever a run picked an `addr_len` bigger than the generic struct (DESIGN.md §22.118/123). Fixed by
// `isSockaddrLike()` (name-prefix match on "sockaddr") feeding into the existing length<->buffer relation mechanism.
struct sockaddr {
  unsigned short sa_family;
  char sa_data[14];
};

int consume(const struct sockaddr *uaddr, int addr_len) {
  if (addr_len < (int)sizeof(unsigned short)) return -1;
  const char *p = (const char *)uaddr;
  char last = p[addr_len - 1];
  return last;
}

// Regression for the §22.144 follow-up fix: under `--linux`, a sockaddr-family struct parameter's synthesized
// size floor is raised to sizeof(struct sockaddr_storage) (128 bytes), not just sizeof(the declared struct) --
// real Linux syscall arguments of this shape are always backed by at least that much real allocation (kernel-wide
// convention; net/unix/af_unix.c's unix_mkname_bsd comment documents it explicitly). Without `--linux`, the floor
// must stay at the declared struct's own size (110 for sockaddr_un here) -- that guarantee does not generally
// hold for arbitrary userspace code. scan_tests.cpp checks the generated `size: { min: ... }` differs between
// the two modes for this exact fixture.
struct sockaddr_un {
  unsigned short sun_family;
  char sun_path[108];
};

int consume(const struct sockaddr_un *uaddr, int addr_len) {
  if (addr_len < 0) return -1;
  const char *p = (const char *)uaddr;
  return addr_len > 0 ? p[addr_len - 1] : 0;
}

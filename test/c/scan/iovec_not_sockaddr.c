// Negative control for the `isSockaddrLike()` fix (P0 item 2): `struct iovec *iov, int iovcnt` has the exact same
// `(struct X *, int)` signature shape as `struct sockaddr *addr, int addr_len`, and `iovcnt` matches `isLenName()`
// just as well as `addr_len` does -- but `iovcnt` is an element count, not a byte length, so it must NOT get a
// `size(iov)` relation (that would be wrong: `size(iov)` is `sizeof(struct iovec)`, unrelated to the element count).
// `isSockaddrLike()` is gated on the struct's name starting with "sockaddr", so `iovec` must stay untouched: `iov`
// keeps its fixed `sizeof(struct iovec)` size and no relation is generated for `iovcnt`.
struct iovec {
  void *iov_base;
  unsigned long iov_len;
};

int consume(struct iovec *iov, int iovcnt) {
  if (iovcnt < 1) return -1;
  return (int)iov->iov_len;
}

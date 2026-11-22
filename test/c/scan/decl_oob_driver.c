// Regression fixture for the declarative ModelDB bounds-check fix (docs/KNOWN_GAPS_PRIORITIZED.md's "curl
// CVE-2019-5436" P1 gap): source:/copy:/fill: effects (recv/read/getenv/strcpy/memset for modules that only
// declare them) previously wrote through Memory::bulk()/wr() with no check against the destination object's
// declared size at all -- unlike a hand-written core.func body (memcpy, fgets, ...), which always brackets its
// writes with explicit core.check.oob instructions. `recv` here is declared-only (no body), so the real ModelDB
// `source:` entry in models/libc.yaml is exercised, not a hand-written core.func. `strcpy` itself later gained a
// real core.func body (models/libc.core, cJSON CVE-2024-31755 ground-truth write-up in docs/DESIGN.md) -- it is
// declared-only here only because the fixture doesn't #include <string.h>, but the real model from models/libc.c
// takes over at link time regardless, same as any other real source file calling strcpy().
typedef unsigned long size_t;
typedef long ssize_t;

ssize_t recv(int fd, void *buf, size_t len, int flags);
char *strcpy(char *dst, const char *src);

// bug: `source:` effect -- recv()'s declared length (500) exceeds the real 10-byte destination. Returns a
// constant (not a byte of `buf`) so the only finding at stake is the oob_write, not an unrelated uninit_read
// from reading back a buffer recv() may only have partially filled.
int bug_recv_oob(void) {
  char buf[10];
  recv(0, buf, 500, 0);
  return 0;
}

// safe: the destination is large enough for the requested length.
int safe_recv_fits(void) {
  char buf[16];
  recv(0, buf, 8, 0);
  return 0;
}

// bug: `copy:` effect -- strcpy()'s size is derived from the source string's own length (strlen(arg1)+1), which
// exceeds the real 4-byte destination here. A concrete literal (not an attacker-tainted parameter) keeps the
// source length itself concrete, so this is a clean oob_write case without colliding with the separate,
// pre-existing "cstrlen needs concrete bytes" limitation on a fully symbolic source string.
int bug_strcpy_oob(void) {
  char buf[4];
  strcpy(buf, "this string is far longer than four bytes");
  return 0;
}

// safe: copying a short literal into a destination that is large enough.
int safe_strcpy_fits(void) {
  char buf[16];
  strcpy(buf, "hi");
  return 0;
}

// `__test_decl_copy` is test-only, declared-only (no body); its ModelDB entry is supplied at test time via
// `--models` with a `copy:` size independent of the real source object's length, so it directly exercises the
// `copy:` effect's *source*-side bound (the destination-side cases above already exercise strcpy's `copy:`, but
// there its size is always strlen(src)+1 -- i.e. never larger than the real source -- so it cannot reach a
// source-side out-of-bounds read).
void __test_decl_copy(void *dst, const void *src, unsigned long n);

// bug: the requested copy length (50) exceeds the real 4-byte source object.
int bug_decl_copy_src_oob(void) {
  char dst[64];
  char src[4] = {1, 2, 3, 4};
  __test_decl_copy(dst, src, 50);
  return 0;
}

// safe: the requested copy length fits inside both the real source and destination objects.
int safe_decl_copy_src_fits(void) {
  char dst[64];
  char src[4] = {1, 2, 3, 4};
  __test_decl_copy(dst, src, 4);
  return 0;
}

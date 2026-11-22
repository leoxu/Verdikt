/* Regression for docs/DESIGN.md §22.128/§22.129/§22.1XX: models/linux.core's `_copy_from_user` model used to run a
   "synthesized object size" oob/ptr_arith check against `from` too, even though `from` is a __user pointer and the
   real kernel access is fault-safe (an illegal user-space access is intercepted by the page-fault handler;
   copy_from_user() just returns a nonzero byte count, it never corrupts or overreads kernel memory). That produced a
   spurious bug report whenever the copy length had no relation to any parameter the auto spec synthesizer could tie
   to `from`'s size (a hardcoded copy length is the simplest such shape). The `to` (kernel destination) check is a
   real attack surface and must keep working exactly as before. */
static inline unsigned long copy_from_user(void *to, const void *from, unsigned long n) {
  return n; /* never lowered: hlir-extern keeps this a declaration so models/linux.core's body is used instead */
}

/* `from`'s length (300) is a literal, not tied to any parameter: the auto spec synthesizer cannot relate it to
   `from`'s synthesized size, so pre-fix this reports a bogus ptr_arith_oob on the user-space source pointer even
   though `to` (512 bytes) is plenty large. Must be safe_under_assumptions after the fix. */
int cfu_src_hardcoded_len(const char *from) {
  char buf[512];
  if (copy_from_user(buf, from, 300))
    return -1;
  return 0;
}

/* `to` really is too small for a caller-controlled `n`: a genuine kernel-side overflow that must still be reported
   after the fix (only the `from`-side check is removed, not the `to`-side one). */
int cfu_dst_too_small(const char *from, unsigned long n) {
  char buf[16];
  if (copy_from_user(buf, from, n))
    return -1;
  return 0;
}

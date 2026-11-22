/* mirrors <linux/uaccess.h>'s `static __always_inline copy_from_user()` wrapper: every translation unit that
   includes it redeclares it identically, with internal (static) linkage; hlir-scan --linux's hlir-extern directive
   tells the frontend to leave its body unlowered so models/linux.core's plain-named `copy_from_user` model (which
   really writes through `to` on the non-fault path) binds instead. */
static inline unsigned long copy_from_user(void *to, const void *from, unsigned long n) {
  return n; /* never lowered: hlir-extern keeps this a declaration */
}

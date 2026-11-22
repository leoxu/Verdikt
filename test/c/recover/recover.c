// hlir-scan --recover fixture: the build environment of this file is incomplete on purpose.
//   * <vendor/platform.h> and "missing_local.h" do not exist (skipped, treated as empty)
//   * u32 / dev_handle_t come from the missing headers (stub typedefs: u32 is 32 bits, dev_handle_t opaque)
//   * vendor_barrier() and vendor_log() are never declared (implicit declarations)
//   * MAX_ITEMS is a macro from a missing header (functions using it cannot be lowered)
//   * struct vendor_ctx is only forward-declared (functions touching its fields cannot be lowered)
#include <string.h>
#include <vendor/platform.h>
#include "missing_local.h"
#include "safe_math.h"

struct vendor_ctx;

int copy_clamped(char *dst, const char *src, int len) {
  char local[16];
  vendor_barrier();
  len = clamp_len(len, 16);
  if (len < 0) return -1;
  memcpy(local, src, len);
  return (int)sat_add_u32((u32)len, 1u);
}

int copy_unclamped(char *dst, const char *src, int len) {
  char local[16];
  if (len < 0) return -1;
  memcpy(local, src, len);                 /* bug: no upper bound */
  return vendor_log(len);
}

int items_ok(int n) { return n < MAX_ITEMS; }                       /* not lowered: MAX_ITEMS is undeclared */
int ctx_flags(struct vendor_ctx *c) { return c->flags; }            /* not lowered: incomplete type */
int handle_open(dev_handle_t h, u32 flags) { return h ? (int)flags : -1; }   /* not lowered: an opaque stub type cannot be used as a scalar */
unsigned int sum32(u32 a, u32 b) { return sat_add_u32(a, b); }
void v_ret(int x) { return vendor_log(x); }                        /* `return f();` in a void function */

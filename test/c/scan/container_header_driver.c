// hlir-scan fixture: container_of behind a header-defined accessor (container_header.h's `to_outer`), mirroring the
// real-world `drm_to_adev()` pattern (amdgpu.h, called by ~all amdgpu ioctl handlers): the entry function only ever
// sees `struct inner *`, the container_of happens inside a helper the entry function's own file does not define.
#include <string.h>
#include "container_header.h"

int outer_read(struct inner *i, char *out, int n) {
  struct outer *o = to_outer(i);
  if (n < 0 || n > 8) return -1;
  memcpy(out, o->buf, (unsigned long)n);
  return o->pad & 0xff;
}

int outer_bug(struct inner *i, char *out, int n) {
  struct outer *o = to_outer(i);
  if (n < 0 || n > 32) return -1;
  memcpy(out, o->buf, (unsigned long)n);  /* buf holds 8 bytes, the whole object 20: n up to 32 reads past the object */
  return 0;
}

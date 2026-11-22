// Shared helper for container_header_driver.c. The container_of accessor (`to_outer`) lives in a header, the way
// Linux kernel subsystems do it (e.g. amdgpu's `drm_to_adev()` in amdgpu.h): it is never the "main file" for any of
// the many .c files that call it. The hint must still be discovered and carried across the call into the caller's
// own parameter, or the harness allocates `in` as a lone top-level object and the container_of subtraction lands
// before it.
#define offsetof(T, m) __builtin_offsetof(T, m)
#define container_of(ptr, type, member) ({ void *__mptr = (void *)(ptr); ((type *)(__mptr - offsetof(type, member))); })

struct inner { int x; };
struct outer { int pad; char buf[8]; struct inner in; int tail; };

static inline struct outer *to_outer(struct inner *i) { return container_of(i, struct outer, in); }

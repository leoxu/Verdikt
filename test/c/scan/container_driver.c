// hlir-scan fixture: container_of. The kernel idiom `file->private_data` is a pointer to a member embedded in a larger
// driver object; the code recovers the object with container_of(). Without knowing that, the pointer is a lone 64-byte
// object and subtracting offsetof() lands before it.
#include <string.h>
#define offsetof(T, m) __builtin_offsetof(T, m)
#define container_of(ptr, type, member) ({ void *__mptr = (void *)(ptr); ((type *)(__mptr - offsetof(type, member))); })

struct misc { int minor; int flags; };
struct drv { int state; char buf[8]; struct misc miscdev; int tail; };
struct file { void *private_data; int mode; };

static inline struct drv *to_drv(struct file *f) { return container_of(f->private_data, struct drv, miscdev); }

int drv_read(struct file *f, char *out, int n) {
  struct drv *d = to_drv(f);
  if (n < 0 || n > 8) return -1;
  memcpy(out, d->buf, (unsigned long)n);
  return d->state & 0xff;
}

int drv_bug(struct file *f, char *out, int n) {
  struct drv *d = to_drv(f);
  if (n < 0 || n > 32) return -1;
  memcpy(out, d->buf, (unsigned long)n);          /* buf holds 8 bytes and the whole object 24: n up to 32 reads past the object */
  return 0;
}

/* the parameter itself is the embedded member */
int misc_open(struct misc *m) {
  struct drv *d = container_of(m, struct drv, miscdev);
  return (d->state & 0xff) + (d->tail & 0xff) + (m->minor & 0xff);
}

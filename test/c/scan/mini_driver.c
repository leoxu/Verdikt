// hlir-scan fixture: a miniature ioctl-style driver.
//   roots:      mini_ioctl (dispatcher), mini_api (exported buffer API)
//   callbacks:  do_read (bug: unchecked length), do_write (safe)  -- reached through the handler table
//   not entries: helper_checksum (static, called internally), mini_noarg (nothing attacker-controlled)
#include <string.h>
typedef unsigned int u32;
struct dev { int open_count; };
struct req { u32 cmd; u32 len; char data[16]; };

static int helper_checksum(const char *p, int n) {
  int s = 0;
  for (int i = 0; i < n; i++) s += p[i];
  return s;
}
static int do_read(struct dev *g, struct req *r) {
  char local[8];
  memcpy(local, r->data, r->len);          /* r->len is attacker-controlled and never checked against 8 */
  return helper_checksum(local, 8);
}
static int do_write(struct dev *g, struct req *r) {
  char local[16];
  if (r->len > 16) return -1;
  memcpy(local, r->data, r->len);
  g->open_count++;
  return (int)r->len;
}
typedef int (*handler_t)(struct dev *, struct req *);
static handler_t table[2] = { do_read, do_write };

int mini_ioctl(struct dev *g, u32 cmd, struct req *r) {
  if (cmd >= 2) return -1;
  return table[cmd](g, r);
}
int mini_api(char *buf, int len) {
  char tmp[32];
  if (len < 0 || len > 32) return -1;
  memcpy(tmp, buf, len);
  return helper_checksum(tmp, len);
}
int mini_noarg(void) { return 7; }

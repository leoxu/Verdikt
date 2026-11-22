// ENTRY: copy_len
// EXPECT: safe
// SPEC: len_buf.yaml
#include <string.h>
int copy_len(char *dst, const char *src, int len) {
  char local[16];
  if (len < 0) return -1;
  if (len > 16) return -2;
  memcpy(local, src, len);
  memcpy(dst, local, len);
  return len;
}

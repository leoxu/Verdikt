#include "static_inline_extern_shared.h"
int get_len_b(int *optlen) {
  int len;
  if (copy_from_user(&len, optlen, sizeof(int)))
    return -1;
  return len;
}

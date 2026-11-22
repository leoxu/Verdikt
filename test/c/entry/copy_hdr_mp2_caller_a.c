// ENTRY: caller_path_a
// EXPECT: bug oob_write
// SPEC: copy_hdr_mp2_caller_a.yaml
//
// mode 固定常量 1（调用方决定，不是攻击者可控），选中路径 A：
// `small[m->hdr_len] = m->hdr[0]`，check 在 @copy_hdr 自己体内，和
// copy_hdr_mp2_caller_b_*.c 的路径 B 落在完全不同的 Op* 上。
#include <string.h>

struct msg {
    char *hdr;
    unsigned int hdr_len;
};

static void copy_hdr(struct msg *m, char *out, unsigned int mode) {
    char small[4];
    if (mode) {
        small[m->hdr_len] = m->hdr[0];
    } else {
        memcpy(out, m->hdr, m->hdr_len);
    }
}

void caller_path_a(struct msg *m) {
    copy_hdr(m, 0, 1);
}

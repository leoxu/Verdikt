// ENTRY: caller_path_b_bug
// EXPECT: bug oob_write
// SPEC: copy_hdr_mp2_caller_b_bug.yaml
//
// 同 copy_hdr_mp2_caller_b_safe.c，mode 固定常量 0（路径 B），但没有
// 检查、buf 只有 16 字节——真实缺陷。
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

void caller_path_b_bug(struct msg *m) {
    char buf[16];
    copy_hdr(m, buf, 0);
}

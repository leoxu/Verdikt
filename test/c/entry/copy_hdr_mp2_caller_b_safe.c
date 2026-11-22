// ENTRY: caller_path_b_safe
// EXPECT: safe
// SPEC: copy_hdr_mp2_caller_b_safe.yaml
//
// mode 固定常量 0，选中路径 B（memcpy 进调用方传入的 out）。调用方检查过
// hdr_len <= 64 并传了 64 字节的 buf——应该安全。
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

void caller_path_b_safe(struct msg *m) {
    char buf[64];
    if (m->hdr_len > 64) return;
    copy_hdr(m, buf, 0);
}

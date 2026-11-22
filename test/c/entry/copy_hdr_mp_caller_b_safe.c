// ENTRY: caller_path_b_safe
// EXPECT: safe
// SPEC: copy_hdr_mp_caller_b_safe.yaml
//
// mode 固定成常量 0，选中路径 B（写调用方传入的 out）。这次调用方检查过
// hdr_len <= 64 并且传了 64 字节的 buf——应该安全。配上
// copy_hdr_mp_caller_b_bug.c（同样选路径 B，但没检查、buf 只有 16 字节）
// 两相对照：同一条路径 B 的 obligation，在不同调用方那里一个能还清、
// 一个还不清。
#include <string.h>

struct msg {
    char *hdr;
    unsigned int hdr_len;
};

static void copy_hdr(struct msg *m, char *out, unsigned int mode) {
    if (mode) {
        char small[4];
        memcpy(small, m->hdr, m->hdr_len);
    } else {
        memcpy(out, m->hdr, m->hdr_len);
    }
}

void caller_path_b_safe(struct msg *m) {
    char buf[64];
    if (m->hdr_len > 64) return;
    copy_hdr(m, buf, 0);
}

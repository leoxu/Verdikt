// ENTRY: caller_path_a
// EXPECT: bug oob_write
// SPEC: copy_hdr_mp_caller_a.yaml
//
// 调用方把 mode 固定成常量 1（不是攻击者可控，是调用方自己写死的），
// 选中 copy_hdr 的路径 A（写本函数自己的局部 small[4]，和这里传的 out
// 完全无关——这里干脆传 0/NULL）。真实违反发生在 copy_hdr 内部，不是
// 这个调用方自己的逻辑错误，但分析必须沿调用链一路跟下去才能发现它。
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

void caller_path_a(struct msg *m) {
    copy_hdr(m, 0, 1);
}

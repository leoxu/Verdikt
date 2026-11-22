// ENTRY: caller_b
// EXPECT: bug oob_write
// SPEC: copy_hdr_caller_b.yaml
//
// DESIGN.md §22.6 最小合成样本，第二个三件套：caller_b 没有任何检查就把
// m 转给 copy_hdr，只是本地缓冲区从 64 字节缩到了 16 字节——真实缺陷，
// 应该在这里报，而且（和设计备忘 §2.2 的"报在正确位置"不同，HLIR 不需要
// 刻意追求这个）report 的 chain 天然就是 caller_b -> copy_hdr，因为整个
// 分析本来就是沿着这条真实调用链走的。
#include <string.h>

struct msg {
    char *hdr;
    unsigned int hdr_len;
};

static void copy_hdr(struct msg *m, char *out) {
    memcpy(out, m->hdr, m->hdr_len);
}

void caller_b(struct msg *m) {
    char buf[16];
    copy_hdr(m, buf);
}

// ENTRY: caller_a
// EXPECT: safe
// SPEC: copy_hdr_caller_a.yaml
//
// DESIGN.md §22.6 的最小合成样本（第一个三件套之一）：照抄
// doc/design-precondition-inference.md 第 2.1/2.2 节的 copy_hdr/caller_a/
// caller_b 原型，但用 HLIR 真实的"完整递归解释"去跑真实调用链，建立
// 一个可信的基线——§22.1 的校正说过，HLIR 不需要摘要机制也不会在这个
// 场景下误报，因为调用方的检查天然就在 path condition 里。
// 这个文件（caller_a）验证的正是这件事：没有任何摘要/代入替换代码，
// 单靠真实递归解释，调用方做了检查（hdr_len <= 64）就应该判 safe。
#include <string.h>

struct msg {
    char *hdr;
    unsigned int hdr_len;
};

static void copy_hdr(struct msg *m, char *out) {
    memcpy(out, m->hdr, m->hdr_len);
}

void caller_a(struct msg *m) {
    char buf[64];
    if (m->hdr_len > 64) return;
    copy_hdr(m, buf);
}

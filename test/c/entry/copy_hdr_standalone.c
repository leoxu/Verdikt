// ENTRY: copy_hdr
// EXPECT: bug oob_write
// SPEC: copy_hdr_standalone.yaml
//
// DESIGN.md §22.6 最小合成样本，第三个三件套——这个代表 Phase A 设想的
// "把函数当自入口单独分析"：copy_hdr 自己的两个形参都换成攻击者可控/
// 已知容量的值（out 容量固定 16 字节，和 caller_b 的 buf[16] 刻意对齐），
// hdr_len 完全不受约束。
//
// 这不是在跑 Phase A 的真实生成代码（那套代码还不存在，§22 仍是提案），
// 是手工搭一个等价场景，验证"单独分析 copy_hdr 得到的违反条件"和
// "copy_hdr_caller_b.c 里真实调用链跑出来的违反条件"是不是同一个形状——
// 如果标准答案一致，说明 Phase A 设想的"自入口分析 + 形参/字段符号配对"
// 这个核心思路在 HLIR 的执行模型上是成立的，值得往下投入；如果对不上，
// 说明这个思路本身就有问题，不用再往下铺更大的范围。
#include <string.h>

struct msg {
    char *hdr;
    unsigned int hdr_len;
};

void copy_hdr(struct msg *m, char *out) {
    memcpy(out, m->hdr, m->hdr_len);
}

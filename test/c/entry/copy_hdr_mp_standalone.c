// ENTRY: copy_hdr
// EXPECT: bug oob_write
// SPEC: copy_hdr_mp_standalone.yaml
//
// DESIGN.md §22.6 第 6 步的"选支"验证样本：copy_hdr 这次有**两条真正不同
// 的路径**，各自产出形状不同的 obligation，分支是由一个**调用方决定、
// 不是攻击者可控**的形参 `mode` 选的（和真实调用链里的常见形状一致：
// dispatcher 按固定常量选行为，不是按用户输入选）：
//   mode != 0  ->  路径 A：写进本函数自己的局部 small[4]，和 out 完全无关
//   mode == 0  ->  路径 B：写进调用方传入的 out，容量取决于调用方给的是
//                  什么（copy_hdr_mp_caller_b_{safe,bug}.c 分别给 64/16 字节）
// 单独分析 copy_hdr（mode 不固定，当攻击者可控/自由值处理）应该探出
// **两条**不同的违反路径——这是要验证的核心：自入口分析能不能产出一组
// 真正析取的 obligation，而不是只有一条。
#include <string.h>

struct msg {
    char *hdr;
    unsigned int hdr_len;
};

void copy_hdr(struct msg *m, char *out, unsigned int mode) {
    if (mode) {
        char small[4];
        memcpy(small, m->hdr, m->hdr_len);
    } else {
        memcpy(out, m->hdr, m->hdr_len);
    }
}

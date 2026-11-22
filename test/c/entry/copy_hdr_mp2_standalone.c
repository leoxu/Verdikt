// ENTRY: copy_hdr
// EXPECT: bug oob_write
// SPEC: copy_hdr_mp2_standalone.yaml
//
// DESIGN.md §22.9 结论里说的"绕开共享 sink"版本：§22.8 那版两条路径都
// 调 memcpy（同一个共享被调函数、同一个 Op*，被 TaintExecutor::run() 的
// (op,kind) 去重拦掉了第二条）。这次改成两条路径落在**两个不同的
// check-op**上：
//   mode != 0  ->  路径 A：`small[m->hdr_len] = m->hdr[0]` 直接下标写，
//                  check 落在 @copy_hdr 自己的函数体里（不经过任何共享
//                  被调函数）
//   mode == 0  ->  路径 B：`memcpy(out, m->hdr, m->hdr_len)`，check 落在
//                  共享的 @memcpy 内部——但这次只有**一条**路径会走到它，
//                  不会和另一条路径的 check 撞成同一个 Op*
// 单独分析 copy_hdr（mode 不固定）这次应该能拿到**两条**不同的 finding。
#include <string.h>

struct msg {
    char *hdr;
    unsigned int hdr_len;
};

void copy_hdr(struct msg *m, char *out, unsigned int mode) {
    char small[4];
    if (mode) {
        small[m->hdr_len] = m->hdr[0];
    } else {
        memcpy(out, m->hdr, m->hdr_len);
    }
}

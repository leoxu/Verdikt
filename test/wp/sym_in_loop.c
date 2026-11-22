#include <stdint.h>

/* 符号在循环里:每个字节 buf[i] 是符号 load，累加出写偏移 w（loop-carried）。
   out[w] 的越界依赖 w —— 后向 WP 推到此必须停在 loop 边界，成为"义务：该循环能否产生 w > sizeof(out)"。
   这是 DESIGN §4.4 / §2.1 的核心触发：无闭式，但有界问题（0≤w≤2n）就够回答越界。*/
int expand(const uint8_t *buf, unsigned n, char *out) {
    unsigned w = 0;
    for (unsigned i = 0; i < n; i++) {
        uint8_t c = buf[i];              /* 符号 load，在循环内 */
        if (c & 0x80u) { w += 2u; } else { w += 1u; }
        out[w] = (char)c;                /* oob: 偏移 w = loop-carried 累加器，源自 buf[] 内容 */
    }
    return (int)w;
}

/* 对照:循环界本身是符号 n，下标 = i（纯归纳变量），越界只依赖 {i}（其界即 n） */
int fill(int *a, unsigned n) {
    for (unsigned i = 0; i < n; i++) a[i] = 0;   /* oob: i loop-carried */
    return 0;
}

#include <string.h>
#include <stdint.h>

/* 反例1: 下标 = 10 个参数之和。|S| 应 ~10，但全是 param（标量，过滤"尺寸"失效但根好建模） */
int many_params(int *a, int p0,int p1,int p2,int p3,int p4,int p5,int p6,int p7,int p8,int p9) {
    return a[p0+p1+p2+p3+p4+p5+p6+p7+p8+p9];
}

/* 反例2: 下标 = 8 个独立内存读之和。|S| 应 ~8，全是 load（真正的硬案例：每个 load 重新引入别名） */
int many_loads(int *a, const int *arr) {
    return a[arr[0]+arr[1]+arr[2]+arr[3]+arr[4]+arr[5]+arr[6]+arr[7]];
}

/* 反例3: 深指针链 a[s->p->q->idx]，嵌套 load */
struct c3 { int idx; };
struct c2 { struct c3 *q; };
struct c1 { struct c2 *p; };
int deep_chain(int *a, struct c1 *s) {
    return a[s->p->q->idx];
}

/* 反例4: 分支里给长度不同赋值，memcpy 用之。分支汇合应 union 两臂的根 */
int branchy_len(char *dst, const char *src, const int *lut, int sel, int extra) {
    int cnt;
    if (sel > 0) cnt = lut[0] + lut[1];      /* 两个 load */
    else         cnt = extra + lut[2];       /* param + load */
    memcpy(dst, src, (unsigned)cnt);         /* S = union 两臂 */
    return 0;
}

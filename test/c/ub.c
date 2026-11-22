// RUN: @oob(8) => ub:oob_write
// RUN: @oob(7) => 0
// RUN: @null_deref(0) => ub:null_deref
// RUN: @div(0) => ub:div_by_zero
// RUN: @ovf(2147483647) => ub:signed_overflow
// RUN: @shift(40) => ub:shift_range
// RUN: @uninit(0) => ub:uninit_read
// RUN: @uaf(0) => ub:use_after_free
// RUN: @dfree(0) => ub:double_free
// RUN: @ret_local(0) => ub:use_after_scope
void *malloc(unsigned long); void free(void *);
int oob(int i) { char b[8]; b[i] = 1; return 0; }
int null_deref(int x) { int *p = 0; return *p; }
int div(int x) { return 10 / x; }
int ovf(int x) { return x + 1; }
int shift(int s) { return 1 << s; }
int uninit(int x) { int y; return y; }
int uaf(int x) { int *p = malloc(4); *p = 1; free(p); return *p; }
int dfree(int x) { void *p = malloc(4); free(p); free(p); return 0; }
int *leak(void) { int v = 5; return &v; }
int ret_local(int x) { int *p = leak(); return *p; }

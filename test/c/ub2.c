// RUN: @write_literal(0) => ub:const_write
// RUN: @vla_zero(0) => assert_failed
// RUN: @vla_ok(3) => 3
// RUN: @bf_null(0) => ub:null_deref
// RUN: @struct_copy_oob(0) => ub:oob_read
// RUN: @bad_fp(0) => ub:unreachable_reached
// RUN: @good_fp(0) => 8
// RUN: @abort_path(1) => infeasible
// RUN: @static_const_write(0) => ub:const_write
char *dup_lit(void) { return "abc"; }
int write_literal(int x) { char *s = dup_lit(); s[0] = 'x'; return 0; }
int vla_zero(int n) { int a[n]; a[0] = 1; return a[0]; }
int vla_ok(int n) { int a[n]; a[n - 1] = n; return a[n - 1]; }
struct B { unsigned a : 4; unsigned b : 4; };
int bf_null(int x) { struct B *p = 0; return p->b; }
struct Big { char d[16]; };
int struct_copy_oob(int x) { char small[4] = {0}; struct Big *b = (struct Big *)small; struct Big c = *b; return c.d[0]; }
int one(int x) { return x + 1; }
int bad_fp(int x) { int (*f)(int) = (int (*)(int))0x1234; return f(1) + one(0); }
int good_fp(int x) { int (*f)(int) = one; return f(7); }
void exit(int);
int abort_path(int x) { if (x) { exit(1); } return 0; }
static const int k[2] = {1, 2};
int static_const_write(int x) { int *p = (int *)k; p[0] = 5; return p[0]; }

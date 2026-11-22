// RUN: @fp_table(1) => 40
// RUN: @fp_table(0) => 20
// RUN: @fp_direct(0) => 7
// RUN: @fp_param(5) => 25
// RUN: @glob_table(2) => 30
// RUN: @glob_string(1) => 98
// RUN: @glob_struct(0) => 23
// RUN: @static_init(0) => 12
// RUN: @byval(0) => 17
// RUN: @sret(3) => 17
// RUN: @bitfield_rw(0) => 5
// RUN: @bitfield_neighbors(0) => 37
// RUN: @bitfield_signed(0) => -3
// RUN: @goto_loop(5) => 15
// RUN: @goto_cleanup(1) => -1
// RUN: @goto_cleanup(0) => 0
// RUN: @vla(6) => 15
// RUN: @stmt_expr(4) => 20
// RUN: @elvis(0) => 9
// RUN: @elvis(5) => 5
// RUN: @case_range(7) => 2
// RUN: @case_range(50) => 3
// RUN: @case_range_wide(0) => 1
// RUN: @case_range_wide(0x70000000) => 2
// RUN: @case_range_wide(0x7fffffff) => 2
// RUN: @case_range_wide(0x6fffffff) => 0
// RUN: @case_range_wide(0x80000000) => 0
// RUN: @case_range_wide(10) => 3
// RUN: @overflow(0) => 1
// RUN: @no_overflow(0) => 0
// RUN: @compound_lit(0) => 9
// RUN: @anon_union(0) => 513
// RUN: @designated(0) => 9
// RUN: @volatile_rw(0) => 4
// RUN: @call_chain(3) => 14
// RUN: @struct_array(0) => 14
// RUN: @ptr_to_ptr(0) => 6
// RUN: @offsets(0) => 12

int twice(int x) { return 2 * x; }
int thrice(int x) { return 3 * x; }
int plus1(int x) { return x + 1; }
typedef int (*op_t)(int);
int fp_table(int i) { op_t t[3] = {plus1, twice, thrice}; return t[i + 1](10) + (i == 1 ? 10 : 0); }
int fp_direct(int x) { op_t f = &plus1; return (*f)(6); }
int apply(op_t f, int v) { return f(f(v)) ; }
int fp_param(int x) { return apply(plus1, x) == x + 2 ? apply(twice, 0) + x * x : -1; }

struct entry { const char *name; op_t fn; int arg; };
static const struct entry table[] = { {"a", plus1, 1}, {"b", twice, 5}, {"c", thrice, 10} };
int glob_table(int i) { return table[i].fn(table[i].arg); }
const char *names[] = {"zero", "bee", "two"};
int glob_string(int i) { return names[i][0] ; }
struct cfg { int a; int b; int arr[3]; } cfg0 = {1, 2, {3, 4, 5}};
int glob_struct(int x) { return cfg0.a + cfg0.b * 10 + cfg0.arr[2] - 3 + cfg0.arr[1] - 4 + (x ? 100 : 0); }
int counter(void) { static int c = 10; c++; return c; }
int static_init(int x) { counter(); return counter(); }

struct P { int x; int y; };
int sum_p(struct P p) { p.x += 1; return p.x + p.y; }
int byval(int x) { struct P a = {6, 10}; int r = sum_p(a); return r + a.x - 6 + 0 * a.y; }
struct P mk(int a) { struct P p; p.x = a; p.y = a * 3; return p; }
int sret(int x) { struct P p = mk(x); return p.x + p.y + mk(x - 1).y - 1 + 0; }

struct bf { unsigned a : 3; unsigned b : 5; int c : 4; unsigned d : 12; };
int bitfield_rw(int x) { struct bf s = {0}; s.a = 5; return s.a; }
int bitfield_neighbors(int x) { struct bf s = {0}; s.a = 5; s.b = 17; s.d = 100; s.a = 5; return s.b + s.a * 4 - 0 + (s.d == 100 ? 0 : 1000); }
int bitfield_signed(int x) { struct bf s = {0}; s.c = -3; s.a = 7; return s.c; }

int goto_loop(int n) { int i = 0, s = 0; top: if (i >= n) goto done; i++; s += i; goto top; done: return s; }
int goto_cleanup(int fail) { int r = 0; if (fail) goto err; return r; err: r = -1; return r; }
int vla(int n) { int a[n]; for (int i = 0; i < n; i++) a[i] = i; int s = 0; for (int i = 0; i < n; i++) s += a[i]; return s; }
int stmt_expr(int x) { return ({ int t = x * 2; t + x * 3; }); }
int elvis(int x) { return x ?: 9; }
int case_range(int v) { switch (v) { case 0 ... 9: return 2; case 10 ... 99: return 3; default: return 0; } }
// a GNU case range too wide to expand into individual core.switch labels (regression for Frontend.cpp's genSwitch)
int case_range_wide(unsigned int v) { switch (v) { case 0: return 1; case 0x70000000 ... 0x7fffffff: return 2; case 10: return 3; default: return 0; } }
int overflow(int x) { int r; return __builtin_add_overflow(2147483647, 1, &r); }
int no_overflow(int x) { int r; return __builtin_mul_overflow(1000, 1000, &r) + (r == 1000000 ? 0 : 5); }
int compound_lit(int x) { struct P *p = &(struct P){4, 5}; return p->x + p->y; }
union u { unsigned char b[4]; struct { unsigned short lo; unsigned short hi; }; };
int anon_union(int x) { union u v; v.b[0] = 1; v.b[1] = 2; v.b[2] = 0; v.b[3] = 0; return v.lo; }
int designated(int x) { int a[5] = { [1] = 4, [3] = 5 }; return a[0] + a[1] + a[2] + a[3]; }
int volatile_rw(int x) { volatile int v = 4; return v; }
int c1(int x) { return x + 1; }
int c2(int x) { return c1(x) * 2 + c1(c1(x)) + 7 - 6; }
int call_chain(int x) { return c2(x) + 0; }
struct P arr_p[2] = {{1, 2}, {3, 4}};
int struct_array(int x) { struct P *q = arr_p; int s = 0; for (int i = 0; i < 2; i++) s += q[i].x * q[i].y; return s; }
int ptr_to_ptr(int x) { int v = 6; int *p = &v; int **pp = &p; return **pp; }
struct S3 { char c; int i; short s; };
int offsets(int x) { return (int)__builtin_offsetof(struct S3, s) + (int)sizeof(struct S3) - 8; }

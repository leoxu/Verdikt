// RUN: @bits(0x12345678) => 275963063
// RUN: @unsigned_wrap(0) => 4294967295
// RUN: @char_math(100) => 100
// RUN: @compound(7) => 23
// RUN: @matrix(0) => 45
// RUN: @enum_sw(2) => 30
// RUN: @static_counter(0) => 3
// RUN: @glob(5) => 15
// RUN: @ptrdiff(0) => 3
// RUN: @strlen_loop(0) => 5
// RUN: @strnlen_bounded(10) => 5
// RUN: @strnlen_bounded(3) => 3
// RUN: @strnlen_bounded(0) => 0
// RUN: @lldiv_sum(17) => 5
// RUN: @lldiv_sum(-17) => -5
// RUN: @dowhile(5) => 15
// RUN: @nested_break(0) => 6
// RUN: @callee_ptr(0) => 99
// RUN: @short_sum(0) => 300
// RUN: @neg_div(-7) => -3
// RUN: @neg_mod(-7) => -1
// RUN: @shift_ops(8) => 33
// RUN: @cond_chain(15) => 3
// RUN: @longs(0) => 8589934592
// RUN: @bool_val(5) => 1
// RUN: @struct_ptr(0) => 11
// RUN: @arr_param(0) => 10
// RUN: @str_cmp(0) => 1
enum color { RED, GREEN = 10, BLUE = 20 };
int bits(unsigned x) { return (int)((x ^ (x >> 3)) & 0x7fffffffu) | 4; }
unsigned unsigned_wrap(int x) { unsigned u = 0; u = u - 1; return u; }
int char_math(int x) { char c = (char)x; c += 28; c -= 28; return c; }
int compound(int x) { x *= 3; x += 4; x -= 3; x <<= 0; x |= 0; return x + 1; }
int matrix(int x) { int m[3][3]; int k = 1; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) m[i][j] = k++; int s = 0; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) s += m[i][j]; return s; }
int enum_sw(int x) { enum color c = x == 2 ? BLUE : GREEN; switch (c) { case RED: return 1; case GREEN: return 20; case BLUE: return 30; } return 0; }
int bump(void) { static int n; return ++n; }
int static_counter(int x) { bump(); bump(); return bump(); }
int total;
int arr[4];
int glob(int x) { total = x; arr[1] = 10; return total + arr[1]; }
int ptrdiff(int x) { int a[8]; int *p = &a[5], *q = &a[2]; return (int)(p - q); }
int len(const char *s) { int n = 0; while (s[n]) n++; return n; }
int strlen_loop(int x) { return len("hello"); }
int dowhile(int n) { int s = 0, i = 1; do { s += i; i++; } while (i <= n); return s; }
int nested_break(int x) { int s = 0; for (int i = 0; i < 10; i++) { for (int j = 0; j < 10; j++) { if (j == 3) break; s++; } if (i == 1) break; } return s; }
int get99(void) { return 99; }
int callee_ptr(int x) { int v = 5; int *p = &v; *p = get99(); return v; }
int short_sum(int x) { short a = 100, b = 200; return a + b; }
int neg_div(int x) { return x / 2; }
int neg_mod(int x) { return x % 2; }
int shift_ops(int x) { return (x << 2) | (x >> 3) | 0; }
int cond_chain(int x) { return x % 3 == 0 && x % 5 == 0 ? 3 : x % 3 == 0 ? 1 : x % 5 == 0 ? 2 : 0; }
long longs(int x) { long a = 1L << 32; return a * 2; }
int bool_val(int x) { _Bool b = x; return b; }
struct node { int v; struct node *next; };
int struct_ptr(int x) { struct node a, b; a.v = 5; a.next = &b; b.v = 6; b.next = 0; int s = 0; for (struct node *p = &a; p; p = p->next) s += p->v; return s; }
int sum4(const int *a) { int s = 0; for (int i = 0; i < 4; i++) s += a[i]; return s; }
int arr_param(int x) { int a[4] = {1, 2, 3, 4}; return sum4(a); }
int str_cmp(int x) { const char *a = "abc"; const char *b = "abd"; int i = 0; while (a[i] && a[i] == b[i]) i++; return b[i] > a[i]; }

/* strnlen had no public model -- only the @__hlir_strnlen helper that other hand-written bodies used --
 * so real code calling it got an opaque external: the scan of `s` was invisible and the returned length
 * unconstrained. DESIGN.md Sec.22.463. The three expectations pin both halves of its contract: it stops
 * at the NUL when maxlen allows, and it stops at maxlen when the NUL is further away. */
#include <string.h>
int strnlen_bounded(int n) { return (int) strnlen("hello", (size_t) n); }

/* lldiv returns a STRUCT, which the frontend lowers to an sret pointer -- so an opaque @lldiv writes
 * neither field and the caller reads indeterminate memory. That produced a confirmed uninit_read from
 * two different libarchive readers (DESIGN.md Sec.22.464). 17/4 = 4 rem 1 -> 5; C truncates toward
 * zero, so -17/4 = -4 rem -1 -> -5, which is what pins the sign convention. */
#include <stdlib.h>
int lldiv_sum(int n) { lldiv_t d = lldiv((long long) n, 4LL); return (int)(d.quot + d.rem); }

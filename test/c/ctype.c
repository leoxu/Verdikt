// RUN: @kinds(48) => 0
// RUN: @kinds(65) => 5
// RUN: @kinds(97) => 1
// RUN: @kinds(32) => 2
// RUN: @kinds(10) => 2
// RUN: @kinds(33) => 8
// RUN: @kinds(200) => 0
// RUN: @digit_count(0) => 3
// RUN: @hex(70) => 1
// RUN: @hex(71) => 0
// RUN: @lower(65) => 97
// RUN: @lower(97) => 97
// RUN: @lower(33) => 33
// RUN: @upper(97) => 65
// RUN: @upper(65) => 65
// RUN: @upper(33) => 33
// glibc's isdigit()/isalpha()/... macros index the table behind __ctype_b_loc(); libc.core builds it for the C locale
// tolower()/toupper() are not only macros: glibc also ships `__extern_inline` BODIES for them, gated on
// __USE_EXTERN_INLINES, which features.h sets from -O1 upward. If the frontend lowers those bodies they
// collide with models/libc.core's @tolower/@toupper and the module stops linking --
// "redefinition of function @tolower" -- which kills a scan at the very last step of its setup, as far
// from the cause as it gets (DESIGN.md Sec.22.453). This test defines the gate directly so it does not
// depend on the optimization level the test harness happens to lower at. The model must win: the lowered
// body indexes a table through __ctype_tolower_loc(), which has no body here.
#define __USE_EXTERN_INLINES 1
#include <ctype.h>
int kinds(int c) { return (isalpha(c) ? 1 : 0) + (isspace(c) ? 2 : 0) + (isupper(c) ? 4 : 0) + (ispunct(c) ? 8 : 0); }
int digit_count(int x) { const char *s = "a1b22"; int n = 0; for (; *s; s++) if (isdigit((unsigned char)*s)) n++; return n; }
int hex(int c) { return isxdigit(c) ? 1 : 0; }
int lower(int c) { return tolower(c); }
int upper(int c) { return toupper(c); }

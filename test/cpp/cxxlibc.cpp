// RUN: @find_char(97) => 1
// RUN: @find_char(122) => 0
// RUN: @copy_len(3) => 3

// glibc's <string.h> does not only DECLARE memchr/strchr/strpbrk/strrchr/strstr for C++. Under
// __CORRECT_ISO_CPP_STRING_H_PROTO it wraps each of them in an `extern "C++"` OVERLOAD PAIR -- one
// taking `char *`, one `const char *` -- both carrying __asm__("strchr"), and from -O1 upward both with
// a body:
//
//     __extern_always_inline char *strchr (char *__s, int __c) __THROW
//     { return __builtin_strchr (__s, __c); }
//
// Those have C++ linkage, so the Sec.22.453 test ("system header AND extern C") let them through, and
// because the asm label collapses both overloads onto the single symbol `strchr` the module ended up
// with @strchr defined TWICE -- a "redefinition of function @strchr" that killed the first C++ target
// to reach it (MariaDB's sql/net_serv.cc; DESIGN.md Sec.22.459). The rule now is "system header AND an
// unmangled name", which covers both spellings.
//
// __OPTIMIZE__ is defined here on purpose: it is the gate glibc puts those bodies behind, and the test
// harness lowers without an -O flag. Same device as test/c/ctype.c.
//
// The std::vector use is the control. It is a header-defined template with no ModelDB entry, so if the
// rule ever widens to "system header" alone it stops being lowered and these RUN lines fail -- which is
// what keeps this test honest about which half of the condition is doing the work.
#define __OPTIMIZE__ 1
#include <string.h>

#include <vector>

static char g_buf[8] = "abcdef";

extern "C" int find_char(int c) {
  std::vector<int> v;
  v.push_back(1);
  return strchr(g_buf, c) != 0 ? v[0] : 0;
}

extern "C" int copy_len(int n) {
  char dst[8];
  std::vector<int> v;
  if (n < 0 || n > 6) return -1;
  memcpy(dst, g_buf, (size_t) n);
  dst[n] = '\0';
  v.push_back((int) strlen(dst));
  return v[0];
}

// Trivial defaulted assignment of unions/structs (std::swap on a union) copies the bytes.
#include <utility>
union VH { long i; void *p; };
extern "C" int s2(int n) { VH a, b; b.i = n; VH t = std::move(a); a = std::move(b); b = std::move(t); return (int)a.i; }
extern "C" int s3(int n) { VH a, b; b.i = n; std::swap(a, b); return (int)a.i; }
// RUN: @s2(3) => 3
// RUN: @s3(3) => 3

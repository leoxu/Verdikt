// Lambdas: closure objects with by-value / by-reference / this captures, mutable, generic (template argument).
template <class F> int apply(F f, int x) { return f(x) + 1; }
struct Acc { int base; int run(int n) { auto g = [this](int k) { return base + k; }; return g(n) * 2; } };
extern "C" int l1(int a) { int k = 10; auto f = [k](int x) { return x + k; }; return f(a); }
extern "C" int l2(int a) { int s = 0; auto f = [&s](int x) { s += x; }; f(a); f(a + 1); return s; }
extern "C" int l3(int a) { int k = 3; return apply([=](int x) { return x * k; }, a); }
extern "C" int l4(int a) { Acc c{a}; return c.run(5); }
extern "C" int l5(int a) { auto f = [](int x, int y) { return x * y; }; return f(a, a + 1); }
extern "C" int l6(int a) { int n = 0; auto inc = [&] { n++; return n; }; inc(); inc(); return n + a + inc(); }
extern "C" int l7(int a) { auto f = [a](int x) mutable { a += x; return a; }; int r = f(1); r += f(1); return r + a; }
// RUN: @l1(5) => 15
// RUN: @l2(5) => 11
// RUN: @l3(5) => 16
// RUN: @l4(5) => 20
// RUN: @l5(5) => 30
// RUN: @l6(5) => 10
// RUN: @l7(5) => 18

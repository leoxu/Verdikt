// Virtual base classes: complete-object vs base-object constructors/destructors, offset tables in the vtable markers, diamonds.
static long g_log;
static void log(int d) { g_log = g_log * 10 + d; }
struct V { int v; V() : v(5) { log(1); } V(int x) : v(x) { log(2); } virtual ~V() { log(3); } virtual int f() const { return v; } };
struct A : virtual V { int a; A() : V(7), a(1) { log(4); } ~A() { log(5); } int f() const override { return v + a; } };
struct B : virtual V { int b; B() : b(2) { log(6); } ~B() { log(7); } };
struct D : A, B { int d; D() : d(3) { log(8); } ~D() { log(9); } int f() const override { return v * 100 + a * 10 + b + d; } };
struct P { int p; P() : p(1) {} int getp() const { return p; } };
struct Q : virtual P { Q() { p += 10; } };
struct R : virtual P { R() { p *= 2; } };
struct S : Q, R { int s; S() : s(p) {} };
extern "C" int vb1(int x) { g_log = 0; { D d; log(0); } return (int)(g_log % 1000000007L) + x; }
extern "C" int vb2(int x) { D d; V *p = &d; A *a = &d; B *b = &d; return p->f() * 1 + a->v + b->v + x; }
extern "C" int vb3(int x) { g_log = 0; V *p = new D(); int r = p->f(); delete p; return r + (int)(g_log % 100000) + x; }
extern "C" int vb4(int x) { S s; Q *q = &s; R *r = &s; return s.p * 100 + q->p * 10 + r->getp() + x + s.s; }
extern "C" int vb5(int x) { A a; B b; return a.f() + b.v + x; }
// RUN: @vb1(1) => 146809754
// RUN: @vb2(1) => 526
// RUN: @vb3(1) => 90269
// RUN: @vb4(1) => 2465
// RUN: @vb5(1) => 14

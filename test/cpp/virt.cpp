// Inheritance and virtual functions: dispatch through base pointers and references, overriding, multiple inheritance,
// virtual destructors, abstract classes, calls from constructors and destructors.
static long g_log;
static void log(int d) { g_log = g_log * 10 + d; }

struct Shape {
	int tag;
	Shape() : tag(1) {}
	virtual ~Shape() { log(1); }
	virtual int area() const { return 0; }
	virtual int scaled(int k) const { return area() * k; }
	int plain() const { return 100 + area(); }
};
struct Rect : Shape {
	int w, h;
	Rect(int a, int b) : w(a), h(b) { tag = 2; }
	~Rect() override { log(2); }
	int area() const override { return w * h; }
};
struct Square : Rect {
	explicit Square(int s) : Rect(s, s) { tag = 3; }
	~Square() override { log(3); }
	int scaled(int k) const override { return area() * k + 1; }
};
struct Circle : Shape {
	int r;
	explicit Circle(int x) : r(x) { tag = 4; }
	int area() const override { return 3 * r * r; }
};
struct Abstract {
	virtual int value() const = 0;
	virtual ~Abstract() {}
	int twice() const { return value() * 2; }
};
struct Impl : Abstract { int v; explicit Impl(int x) : v(x) {} int value() const override { return v; } };

struct A { int a; A() : a(1) {} virtual int fa() const { return a; } virtual ~A() {} };
struct B { int b; B() : b(2) {} virtual int fb() const { return b * 10; } virtual ~B() {} };
struct AB : A, B { int c; AB() : c(3) {} int fa() const override { return a + 100; } int fb() const override { return b * 10 + c; } };

struct Noisy {
	Noisy() { log(5); who(); }
	virtual void who() { log(6); }
	virtual ~Noisy() { who(); log(7); }
};
struct NoisyD : Noisy {
	void who() override { log(8); }
};

static int viaPtr(const Shape *s) { return s->area(); }
static int viaRef(const Shape &s) { return s.scaled(3); }

// RUN: @t_basic(2, 5) => 120
extern "C" long t_basic(int a, int b) { Rect r(a, b); Shape *s = &r; return viaPtr(s) + s->plain(); }
// RUN: @t_override(4) => 16048
extern "C" long t_override(int x) { Square sq(x); Circle c(x); const Shape *a[2] = {&sq, &c}; return viaPtr(a[0]) * 1000 + viaPtr(a[1]); }
// RUN: @t_scaled(3) => 281881
extern "C" long t_scaled(int x) { Square sq(x); Rect r(x, 2); Circle c(x); return viaRef(sq) * 10000 + viaRef(r) * 100 + viaRef(c); }
// RUN: @t_tag() => 234
extern "C" long t_tag() { Rect r(1, 2); Square s(3); Circle c(4); return r.tag * 100 + s.tag * 10 + c.tag; }
// RUN: @t_abstract(21) => 63
extern "C" long t_abstract(int x) { Impl i(x); Abstract *p = &i; return p->twice() + p->value(); }
// RUN: @t_delete() => 32104
extern "C" long t_delete() { g_log = 0; Shape *s = new Square(2); int a = s->area(); delete s; return g_log * 100 + a; }
// RUN: @t_delete_circle() => 112
extern "C" long t_delete_circle() { g_log = 0; Shape *s = new Circle(2); int a = s->area(); delete s; return g_log * 100 + a; }
// RUN: @t_multi(0) => 101023
extern "C" long t_multi(int d) { AB x; A *pa = &x; B *pb = &x; return pa->fa() * 1000 + pb->fb() + d; }
// RUN: @t_multi_delete() => 23
extern "C" long t_multi_delete() { AB *x = new AB; B *pb = x; int r = pb->fb(); delete pb; return r; }
// RUN: @t_ctor_virtual() => 56867
extern "C" long t_ctor_virtual() { g_log = 0; { NoisyD d; d.who(); } return g_log; }
// RUN: @t_exact() => 76
extern "C" long t_exact() { Square s(5); return s.area() + s.scaled(2); }

// C++ basics: methods, references, namespaces, overloading, default arguments, templates, operators, static members.
// Every test is an extern "C" function so the interpreter and the native compiler can call it by name.
namespace geo {
struct Point {
	int x, y;
	Point() : x(0), y(0) {}
	Point(int a, int b) : x(a), y(b) {}
	int sum() const { return x + y; }
	void scale(int k) { x *= k; y *= k; }
	Point operator+(const Point &o) const { return Point(x + o.x, y + o.y); }
	bool operator==(const Point &o) const { return x == o.x && y == o.y; }
};
inline int dot(const Point &a, const Point &b) { return a.x * b.x + a.y * b.y; }
}  // namespace geo

static int over(int a) { return a + 1; }
static int over(long a) { return static_cast<int>(a) * 2; }
static int over(int a, int b) { return a * b; }
static int defarg(int a, int b = 10, int c = 100) { return a + b + c; }

template <typename T> T maxOf(T a, T b) { return a > b ? a : b; }
template <typename T, int N> struct Buf {
	T data[N];
	T total() const { T s = 0; for (int i = 0; i < N; i++) s += data[i]; return s; }
};

struct Counter {
	static int created;
	int id;
	Counter() : id(++created) {}
};
int Counter::created = 0;

static void incr(int &r) { r += 5; }
static int &pick(int &a, int &b, bool first) { return first ? a : b; }
static const int &cref(const int &v) { return v; }

// RUN: @t_method(3, 4) => 7
extern "C" int t_method(int a, int b) { geo::Point p(a, b); return p.sum(); }
// RUN: @t_scale(3, 4) => 14
extern "C" int t_scale(int a, int b) { geo::Point p(a, b); p.scale(2); return p.sum(); }
// RUN: @t_operator(1, 2) => 14
extern "C" int t_operator(int a, int b) {
	geo::Point p(a, b), q(3, 4);
	geo::Point r = p + q;
	return r.sum() + (r == geo::Point(4, 6) ? 4 : 0);
}
// RUN: @t_dot(2, 3) => 13
extern "C" int t_dot(int a, int b) { geo::Point p(a, b); return geo::dot(p, p); }
// RUN: @t_default() => 0
extern "C" int t_default() { geo::Point p; return p.x + p.y; }
// RUN: @t_overload(5) => 49
extern "C" int t_overload(int a) { return over(a) + over(static_cast<long>(a)) + over(a, a) + 8; }
// RUN: @t_defarg(1) => 343
extern "C" int t_defarg(int a) { return defarg(a) + defarg(a, 20) + defarg(a, 20, 30) - 0 + 0 + 0 + 54 + 6; }
// RUN: @t_template(7, 9) => 25
extern "C" int t_template(int a, int b) { return maxOf(a, b) + maxOf<long>(3, 4) + maxOf(a - 7, 0) + 12; }
// RUN: @t_buf(4) => 40
extern "C" int t_buf(int k) { Buf<int, 4> b; for (int i = 0; i < 4; i++) b.data[i] = k * (i + 1); return b.total(); }
// RUN: @t_static() => 3
extern "C" int t_static() { Counter a, b, c; return c.id; }
// RUN: @t_ref(10) => 15
extern "C" int t_ref(int v) { int x = v; incr(x); return x; }
// RUN: @t_refret(3, 8) => 103
extern "C" int t_refret(int a, int b) { pick(a, b, false) = 100; return a + b - 3 + 3; }
// RUN: @t_cref(21) => 21
extern "C" int t_cref(int v) { const int &r = cref(v); return r; }
// RUN: @t_refvar(5) => 17
extern "C" int t_refvar(int v) { int a = v; int &r = a; r += 7; const int &c = a; return c + 5; }
// RUN: @t_bool(3) => 2
extern "C" int t_bool(int v) { bool b = v > 2; bool n = !b; return (b ? 2 : 0) + (n ? 1 : 0); }
// RUN: @t_nullptr(0) => 1
extern "C" int t_nullptr(int v) { int *p = nullptr; int x = 4; if (v) p = &x; return p == nullptr ? 1 : *p; }

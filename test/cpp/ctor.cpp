// Constructors, destructors, temporaries, copies, new/delete: the order in which they run is observable through g_log.
static long g_log;
static void log(int d) { g_log = g_log * 10 + d; }

struct Guard {
	int id;
	explicit Guard(int i) : id(i) { log(i); }
	Guard(const Guard &o) : id(o.id + 1) { log(8); }
	~Guard() { log(id + 4); }
};
static int use(const Guard &g) { return g.id; }
static int byValue(Guard g) { return g.id * 2; }
static Guard make(int i) { return Guard(i); }

struct Pair {
	Guard a;
	Guard b;
	Pair() : a(1), b(2) { log(9); }
	~Pair() { log(7); }
};
struct Base { Base() { log(1); } ~Base() { log(3); } };
struct Derived : Base {
	Guard m;
	Derived() : Base(), m(2) { log(6); }
	~Derived() { log(5); }
};
struct Defaults {
	int a = 5;
	int b;
	Defaults() : b(a + 1) {}
	Defaults(int x) : Defaults() { b += x; }
};
struct Holder {
	int &ref;
	explicit Holder(int &r) : ref(r) {}
	void bump() { ref += 3; }
};
struct Agg { int x; int y; int z; };

static int early(int e) { Guard a(1); if (e) return 10; Guard b(2); return 20; }
static int loopy(int n) {
	int s = 0;
	for (int i = 0; i < n; i++) {
		Guard g(1);
		if (i == 1) continue;
		if (i == 3) break;
		s += i;
	}
	return s;
}

// RUN: @t_scope() => 126375
extern "C" long t_scope() { g_log = 0; { Guard a(1); { Guard b(2); } Guard c(3); } return g_log; }
// RUN: @t_early_yes() => 1510
extern "C" long t_early_yes() { g_log = 0; int r = early(1); return g_log * 100 + r; }
// RUN: @t_early_no() => 126520
extern "C" long t_early_no() { g_log = 0; int r = early(0); return g_log * 100 + r; }
// RUN: @t_loop() => 1515151502
extern "C" long t_loop() { g_log = 0; int r = loopy(5); return g_log * 100 + r; }
// RUN: @t_temp() => 3703
extern "C" long t_temp() { g_log = 0; int r = use(Guard(3)); return g_log * 100 + r; }
// RUN: @t_byvalue() => 18604
extern "C" long t_byvalue() { g_log = 0; Guard g(1); int r = byValue(g); return g_log * 100 + r; }
// RUN: @t_return_obj() => 226
extern "C" long t_return_obj() { g_log = 0; { Guard g = make(2); log(g.id); } return g_log; }
// RUN: @t_members() => 129765
extern "C" long t_members() { g_log = 0; { Pair p; } return g_log; }
// RUN: @t_base() => 126563
extern "C" long t_base() { g_log = 0; { Derived d; } return g_log; }
// RUN: @t_defaults() => 5616
extern "C" long t_defaults() { Defaults d; Defaults e(10); return d.a * 1000 + d.b * 100 + e.b; }
// RUN: @t_refmember(4) => 10
extern "C" long t_refmember(int v) { int x = v; Holder h(x); h.bump(); h.bump(); return x; }
// RUN: @t_new() => 226
extern "C" long t_new() { g_log = 0; Guard *p = new Guard(2); log(p->id); delete p; return g_log; }
// RUN: @t_newint(5) => 11
extern "C" long t_newint(int v) { int *p = new int(v); int *a = new int[3]{1, 2, 3}; int r = *p + a[0] + a[1] + a[2]; delete p; delete[] a; return r; }
// RUN: @t_newzero() => 0
extern "C" long t_newzero() { int *a = new int[4](); int s = a[0] + a[1] + a[2] + a[3]; delete[] a; return s; }
// RUN: @t_agg(2) => 109
extern "C" long t_agg(int v) { Agg a{v, v + 1, v + 2}; Agg b = a; b.z = 100; return a.z + b.x + b.y + b.z; }
// RUN: @t_deletenull() => 7
extern "C" long t_deletenull() { Guard *p = nullptr; delete p; return 7; }
// RUN: @t_cond_obj(1) => 1501
extern "C" long t_cond_obj(int c) { g_log = 0; int r = use(c ? Guard(1) : Guard(2)); return g_log * 100 + r; }

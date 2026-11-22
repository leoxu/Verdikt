// Arrays of class objects: construction, copy (implicit copy constructor), destruction in reverse order, aggregate fillers.
static long lg;
struct T { int v; T() : v(1) { lg = lg * 10 + 1; } T(const T &o) : v(o.v + 1) { lg = lg * 10 + 2; } ~T() { lg = lg * 10 + 3; } };
struct H { T a[3]; int k = 0; };
extern "C" int a1(int x) { lg = 0; { T t[2]; } return (int)lg + x; }
extern "C" int a2(int x) { lg = 0; { H h; H g(h); return g.a[2].v * 1000 + (int)(lg % 1000) + x; } }
extern "C" int a3(int x) { lg = 0; { T t[3] = {T(), T()}; } return (int)(lg % 100000000) + x; }
// RUN: @a1(1) => 1134
// RUN: @a2(1) => 2223
// RUN: @a3(1) => 111334

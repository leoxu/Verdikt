// Floating point: values are IEEE bit patterns, core.fop computes on them (exact when concrete); conversions, comparisons, float/double/long double.
extern "C" int f_add(int a) { double x = a * 1.5; x += 0.25; return (int)(x * 4); }
extern "C" int f_cmp(int a) { float f = a; if (f < 2.5f) return 1; if (f == 7.0f) return 2; return 3; }
extern "C" int f_loop(int n) { double s = 0; for (int i = 1; i <= n; i++) s += 1.0 / i; return (int)(s * 1000); }
extern "C" int f_neg(int a) { double d = -a; float g = (float)d; long double l = g; l = l * 2; return (int)l + (d ? 100 : 0); }
extern "C" int f_unsigned(unsigned a) { double d = a; return (int)(d / 3); }
extern "C" double f_ret(int a) { return a / 2.0; }
extern "C" int f_call(int a) { return (int)f_ret(a) * 10 + (int)(f_ret(a) * 2); }
// RUN: @f_add(3) => 19
// RUN: @f_cmp(2) => 1
// RUN: @f_cmp(7) => 2
// RUN: @f_cmp(9) => 3
// RUN: @f_loop(10) => 2928
// RUN: @f_neg(5) => 90
// RUN: @f_neg(0) => 0
// RUN: @f_unsigned(4000000000) => 1333333333
// RUN: @f_call(7) => 37

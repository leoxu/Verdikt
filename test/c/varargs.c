#include <stdarg.h>
/* variadic functions of the project: the caller packs the variable arguments, va_start/va_arg walk them */
static int sum(int n, ...) { va_list ap; va_start(ap, n); int s = 0; for (int i = 0; i < n; i++) s += va_arg(ap, int); va_end(ap); return s; }
static long mixed(const char *tag, ...) {
	va_list ap, copy;
	va_start(ap, tag);
	va_copy(copy, ap);
	long a = va_arg(ap, long);
	const char *s = va_arg(ap, const char *);
	int b = va_arg(copy, long) > 0;   /* the copy starts at the same place */
	va_end(ap);
	va_end(copy);
	return a + s[0] + b + tag[0];
}
static int over(int n, ...) { va_list ap; va_start(ap, n); int s = 0; for (int i = 0; i <= n; i++) s += va_arg(ap, int); va_end(ap); return s; }
// RUN: @t_sum(5) => 18
int t_sum(int a) { return sum(3, a, a + 1, a + 2) + sum(0); }
// RUN: @t_mixed(2) => 244
long t_mixed(long a) { return mixed("x", a, "y"); }
// RUN: @t_over(5) => ub:oob_read
int t_over(int a) { return over(2, a, a); }

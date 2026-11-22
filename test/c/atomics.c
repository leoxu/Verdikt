// RUN: @atomic_exchange_test(10) => 15

#include <stdatomic.h>

// __c11_atomic_exchange (3-arg: ptr, value, order) has no Val2 sub-expression, unlike the GNU 4-arg
// __atomic_exchange(ptr, val_ptr, ret_ptr, order); a frontend that calls getVal2() unconditionally for
// anything whose name ends in "_exchange" crashes clang's own AtomicExpr::getVal2() assertion on this.
int atomic_exchange_test(int x) {
  int v = 5;
  int old = __c11_atomic_exchange((_Atomic(int) *)&v, x, __ATOMIC_SEQ_CST);
  return old + v;
}

// RUN: @atomic_qualified_rw(7) => 70
// An _Atomic-qualified object read and written as an ordinary one. Both directions used to stop the
// WHOLE function from lowering -- `unsupported: cast kind AtomicToNonAtomic` on the read and
// `unsupported: assignment of type '_Atomic(uint32_t)'` on the write -- and a function that does not
// lower becomes an opaque extern, so the code under test vanishes from the analysis while the scan
// still reports coverage and a verdict. Redis's processInlineBuffer did exactly that: 42138 calls,
// every one opaque, a 300s scan with runs=1 (DESIGN.md Sec.22.452).
//
// The engine explores one thread, so an _Atomic(T) object is a T object; carrying it as T is exact.
static _Atomic(unsigned) g_counter;
static _Atomic(long) g_stamp;

int atomic_qualified_rw(int x) {
  g_counter = 0;                  /* assignment to an _Atomic scalar */
  g_counter = (unsigned) x;       /* ... with a value conversion */
  g_stamp = 3;
  unsigned c = g_counter;         /* AtomicToNonAtomic on the read */
  long s = g_stamp;
  unsigned long t = c * (unsigned long) s;   /* both values must be usable afterwards */
  if (t > 1000) return -1;
  return (int) (t * 10 / 3);
}

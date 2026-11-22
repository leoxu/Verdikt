/* Replaces <aarch64/atomic.h> from the QNX SDP 800 target headers. Pass it with `-include`.
 *
 * WHY: that header's LSE helpers tie an `"=r" (unsigned)` output to an `"0" (volatile unsigned *)` input --
 *
 *     __asm__ __volatile__ ( ".arch armv8.1-a\n" "ldaddal %w2, %w0, [%1]\n"
 *                            : "=r" (__res) : "0" (__loc), "r" (__incr) : "memory" );
 *
 * clang rejects that as `unsupported inline asm: input with type 'volatile unsigned int *' matching output with
 * type 'unsigned int'`, and it is not a -march/-mcpu/+lse question: all three were tried and none helps. It is a
 * GCC-ism the QNX toolchain accepts and clang does not. 26 of the 244 non-<driver> resmgr sources fail on it alone,
 * across <driver>, <driver>, <driver>, <driver>, <driver>, <driver>, <driver> and pps -- i.e. it is the single
 * biggest mechanical blocker to scanning that tree, and it has nothing to do with the code being analysed.
 *
 * WHAT THIS CHANGES SEMANTICALLY, stated plainly: these become ordinary non-atomic read-modify-writes. HLIR is
 * single-threaded, so for the analysis that is not an approximation at all EXCEPT in the one place it matters --
 * a concurrency bug whose window is inside one of these operations becomes invisible. That is already true of
 * every scan this engine does (see the <driver> round: a real UAF race needed a deliberate injection harness to be
 * seen at all), so this file does not make it worse; it just must not be read as "the atomics were modelled".
 *
 * `atomic.h` itself only DECLARES atomic_add/atomic_sub/... as externs; the llsc_ and lse_ inlines below are the
 * only thing the CPU header contributes, so defining the include guard and supplying plain-C equivalents is
 * enough -- nothing else in the SDP headers depends on their shape.
 */
#ifndef HLIR_QNX_ATOMIC_OVERRIDE_H
#define HLIR_QNX_ATOMIC_OVERRIDE_H

/* claim the SDP header's guard so <atomic.h>'s `#include _NTO_CPU_HDR_(atomic.h)` becomes a no-op */
#define _AARCH64_ATOMIC_H_INCLUDED

#define HLIR_QNX_ATOMIC_RMW(name, expr)                                                             \
  static __inline__ unsigned __attribute__((__unused__))                                            \
  name##_value(volatile unsigned *const __loc, unsigned const __arg) {                              \
    unsigned const __old = *__loc;                                                                  \
    *__loc = (expr);                                                                                \
    (void)__arg;                                                                                    \
    return __old;                                                                                   \
  }                                                                                                 \
  static __inline__ void __attribute__((__unused__))                                                \
  name(volatile unsigned *const __loc, unsigned const __arg) { (void)name##_value(__loc, __arg); }

/* the ldaddal/ldclral/ldsetal/ldeoral family returns the PREVIOUS value, which the macro above preserves */
HLIR_QNX_ATOMIC_RMW(llsc_atomic_add,    __old + __arg)
HLIR_QNX_ATOMIC_RMW(llsc_atomic_sub,    __old - __arg)
HLIR_QNX_ATOMIC_RMW(llsc_atomic_clr,    __old & ~__arg)
HLIR_QNX_ATOMIC_RMW(llsc_atomic_set,    __old | __arg)
HLIR_QNX_ATOMIC_RMW(llsc_atomic_toggle, __old ^ __arg)
HLIR_QNX_ATOMIC_RMW(lse_atomic_add,     __old + __arg)
HLIR_QNX_ATOMIC_RMW(lse_atomic_sub,     __old - __arg)
HLIR_QNX_ATOMIC_RMW(lse_atomic_clr,     __old & ~__arg)
HLIR_QNX_ATOMIC_RMW(lse_atomic_set,     __old | __arg)
HLIR_QNX_ATOMIC_RMW(lse_atomic_toggle,  __old ^ __arg)

#undef HLIR_QNX_ATOMIC_RMW

#endif /* HLIR_QNX_ATOMIC_OVERRIDE_H */

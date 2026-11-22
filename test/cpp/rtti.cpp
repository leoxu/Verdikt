#include <typeinfo>
// dynamic_cast and typeid: the runtime check compares an object's vptr against the marker of every class of this
// translation unit derived from the operand's static type (the same mechanism virtual calls already use), adjusts
// the pointer to the target subobject on a match, and returns null (pointer form) / traps (reference form, a
// simplified stand-in for `std::bad_cast` — see IMPLEMENTATION_PLAN) on no match. `typeid` reuses the very same
// per-class marker as its identity, so `typeid(a) == typeid(b)` is a plain pointer comparison underneath.
struct Animal { virtual ~Animal() {} virtual int sound() const { return 0; } };
struct Dog : Animal { int sound() const override { return 1; } int fetch() const { return 42; } };
struct Cat : Animal { int sound() const override { return 2; } };

struct Flies { virtual ~Flies() {} int lift = 7; };
struct Bird : Animal, Flies { int sound() const override { return 3; } };

// RUN: @t_downcast_ok() => 42
extern "C" long t_downcast_ok() {
  Dog d;
  Animal *a = &d;
  Dog *p = dynamic_cast<Dog *>(a);
  return p ? p->fetch() : -1;
}
// RUN: @t_downcast_fail() => -1
extern "C" long t_downcast_fail() {
  Cat c;
  Animal *a = &c;
  Dog *p = dynamic_cast<Dog *>(a);
  return p ? p->fetch() : -1;
}
// RUN: @t_downcast_null() => -1
extern "C" long t_downcast_null() {
  Animal *a = nullptr;
  Dog *p = dynamic_cast<Dog *>(a);  // well-defined: null in, null out, no UB
  return p ? p->fetch() : -1;
}
// RUN: @t_upcast() => 1
extern "C" long t_upcast() {
  Dog d;
  Dog *p = &d;
  Animal *a = dynamic_cast<Animal *>(p);  // always succeeds (a static upcast)
  return a->sound();
}
// RUN: @t_crosscast_multi() => 7
extern "C" long t_crosscast_multi() {  // Bird's Flies subobject is at a non-zero offset: exercises the pointer adjustment
  Bird b;
  Animal *a = &b;
  Flies *f = dynamic_cast<Flies *>(a);
  return f ? f->lift : -1;
}
// RUN: @t_void_complete() => 1
extern "C" long t_void_complete() {
  Bird b;
  Flies *f = &b;
  void *v = dynamic_cast<void *>(f);
  return v == static_cast<void *>(&b) ? 1 : 0;
}
// RUN: @t_ref_ok() => 42
extern "C" long t_ref_ok() {
  Dog d;
  Animal &a = d;
  Dog &r = dynamic_cast<Dog &>(a);
  return r.fetch();
}
// RUN: @t_ref_fail() => infeasible
extern "C" long t_ref_fail() {
  Cat c;
  Animal &a = c;
  Dog &r = dynamic_cast<Dog &>(a);  // no Dog in sight: traps (simplified `std::bad_cast`)
  return r.fetch();
}
// typeid's OWN identity mechanism (a per-class marker, the same one `dynamic_cast` compares vptrs against) is
// tested directly, by address, below: that part is this project's own code and is sound. `std::type_info`'s real
// `operator==`/`operator!=` (member functions inline in <typeinfo>, so this frontend reaches and analyses their
// REAL libstdc++ body like any other reachable code) are a separate, known, documented limitation — see the
// `t_typeid_compare_known_limitation` test and FEATURE_STATUS.md: that body expects a full ABI-layout `type_info`
// object (a vtable pointer plus a `_name` field), which this project's lightweight 8-byte identity-only markers
// are not, so its non-constexpr branch reads past the marker. `typeid(x) == typeid(y)` in real user code hits
// this every time, not just on a mismatch — there is no pointer-identity fast path taken at actual runtime in
// this libstdc++ version (only under `std::is_constant_evaluated()`, which is never true here).
// RUN: @t_typeid_same() => 1
extern "C" long t_typeid_same() {
  Dog d1, d2;
  Animal *a = &d1, *b = &d2;
  return &typeid(*a) == &typeid(*b) ? 1 : 0;
}
// RUN: @t_typeid_diff() => 1
extern "C" long t_typeid_diff() {
  Dog d;
  Cat c;
  Animal *a = &d, *b = &c;
  return &typeid(*a) != &typeid(*b) ? 1 : 0;
}
// RUN: @t_typeid_static_name() => 1
extern "C" long t_typeid_static_name() {
  Dog d;
  Animal *a = &d;
  return &typeid(*a) == &typeid(Dog) ? 1 : 0;
}
// RUN: @t_typeid_static_name_false() => 1
extern "C" long t_typeid_static_name_false() {
  Dog d;
  Animal *a = &d;
  return &typeid(*a) != &typeid(Cat) ? 1 : 0;
}
// RUN: @t_typeid_compare_known_limitation() => ub:oob_read
extern "C" long t_typeid_compare_known_limitation() {
  Dog d1, d2;
  Animal *a = &d1, *b = &d2;
  return typeid(*a) == typeid(*b) ? 1 : 0;  // same type, but still: see the comment above
}

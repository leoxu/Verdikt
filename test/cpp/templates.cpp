// Template-metaprogramming-adjacent constructs found while trialling nlohmann/json (single-header, ~25k lines,
// heavy template instantiation) as a representative "template-heavy" C++ project: aggregate initialization of a
// class with base classes (clang's own `priority_tag<N>`-style tag-dispatch idiom, and nlohmann/json's own use of
// it), structured bindings (tuple-like, array, and plain-struct decomposition), std::initializer_list, a scalar
// value built with brace-init syntax (`T{x}`, as opposed to `T x = {init};`), and std::nullptr_t passed by value
// through a template parameter (the shape nlohmann/json uses for its no-context exception-creation overloads).

// ---- aggregate initialization of a class with (public, non-virtual, direct) base classes --------------------
struct AggBase { int x; };
struct AggDerived : AggBase { int y; };
extern "C" int agg_base1() {
  AggDerived d{{1}, 2};  // base subobject first, then the derived class's own field
  return d.x * 10 + d.y;
}
// RUN: @agg_base1() => 12

template <unsigned N>
struct Tag : Tag<N - 1> {};
template <>
struct Tag<0> {};
extern "C" int agg_base2() {
  Tag<3> t{};  // every level is an empty struct: nothing to initialize, but the base chain must be walked
  (void)t;
  return 7;
}
// RUN: @agg_base2() => 7

struct AggBase2 { int a; int b; };
struct AggMid : AggBase2 { int c; };
struct AggTop : AggMid { int d; };
extern "C" int agg_base3() {
  AggTop t{{{1, 2}, 3}, 4};  // two levels of base, nested braces
  return t.a * 1000 + t.b * 100 + t.c * 10 + t.d;
}
// RUN: @agg_base3() => 1234

// ---- structured bindings (C++17) ------------------------------------------------------------------------------
#include <utility>
extern "C" int sb_pair(int a, int b) {
  std::pair<int, int> p{a, b};
  auto [x, y] = p;  // tuple-like: each binding gets a hidden reference "holding var" initialized by get<N>(p)
  return x * 100 + y;
}
// RUN: @sb_pair(3, 4) => 304

extern "C" int sb_array() {
  int arr[3] = {1, 2, 3};
  auto [a, b, c] = arr;  // array decomposition: no holding var, each binding re-evaluates a subscript expression
  return a * 100 + b * 10 + c;
}
// RUN: @sb_array() => 123

struct SbPoint { int x; int y; };
extern "C" int sb_struct() {
  SbPoint p{5, 6};
  auto [x, y] = p;  // plain-struct decomposition: no holding var, each binding re-evaluates a member expression
  return x * 10 + y;
}
// RUN: @sb_struct() => 56

// ---- std::initializer_list -------------------------------------------------------------------------------------
#include <initializer_list>
extern "C" int il_range_for() {
  int sum = 0;
  for (int v : {1, 2, 3, 4}) sum += v;  // a bare braced-init-list used directly as a range: materializes the backing array + the initializer_list object
  return sum;
}
// RUN: @il_range_for() => 10

static int sumList(std::initializer_list<int> l) {
  int s = 0;
  for (int v : l) s += v;
  return s;
}
extern "C" int il_call_arg() { return sumList({10, 20, 30}); }  // a braced-init-list bound to a by-value std::initializer_list<T> parameter
// RUN: @il_call_arg() => 60

// ---- scalar value built with brace-init syntax (T{x}, not T x = {init}) ----------------------------------------
extern "C" int scalar_brace(int a) {
  using u64 = unsigned long long;
  u64 x = u64{static_cast<unsigned>(a)};  // a CXXFunctionalCastExpr around a single-element InitListExpr of scalar type
  return static_cast<int>(x);
}
// RUN: @scalar_brace(7) => 7

// ---- std::nullptr_t forwarded by value through a template parameter --------------------------------------------
// This is the exact shape nlohmann/json's exception::create()/diagnostics() overloads use for their "no context"
// case: a BasicJsonContext template parameter deduced to std::nullptr_t, read and forwarded by value. clang elides
// the usual CK_LValueToRValue node for a std::nullptr_t glvalue (nothing to "load": the type has one value), and
// folds it directly into the CK_NullToPointer cast at the call site instead - so a bare DeclRefExpr to it can reach
// genR()/genL() without the wrapping cast node every other variable read normally goes through.
#include <cstddef>
static int useNull(std::nullptr_t n) {
  (void)n;
  return 42;
}
template <typename T>
static int forwardNull(T context) {
  return useNull(context);
}
extern "C" int null_context() { return forwardNull(nullptr); }
// RUN: @null_context() => 42

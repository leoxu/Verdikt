// libstdc++ containers lowered from the real headers: vector, string, map; std::move / forward / addressof builtins.
#include <map>
#include <string>
#include <utility>
#include <vector>

extern "C" int t_vec(int n) { std::vector<int> v; for (int i = 0; i < n; i++) v.push_back(i * 2); int s = 0; for (size_t i = 0; i < v.size(); i++) s += v[i]; return s; }
// RUN: @t_vec(5) => 20
// RUN: @t_vec(0) => 0
extern "C" int t_str(int n) { std::string s; for (int i = 0; i < n; i++) s += 'a' + (i % 3); return (int)s.size() + s[0]; }
// RUN: @t_str(5) => 102
extern "C" int t_map(int n) { std::map<int, int> m; for (int i = 0; i < n; i++) m[i % 3] += i; return m[0] + m[1] + m[2]; }
// RUN: @t_map(5) => 10
extern "C" int t_mapiter(int n) {
	std::map<int, int> m;
	for (int i = 0; i < n; i++) m[(i * 7) % 5] = i;
	int s = 0, k = 1;
	for (auto it = m.begin(); it != m.end(); ++it) { s += it->first * k + it->second; k++; }
	m.erase(2);
	return s * 100 + (int)m.size();
}
// RUN: @t_mapiter(5) => 5004
extern "C" int t_move(int n) {
	std::vector<int> a;
	for (int i = 0; i < n; i++) a.push_back(i);
	std::vector<int> b = std::move(a);
	return (int)a.size() * 100 + (int)b.size() * 10 + b[n - 1];
}
// RUN: @t_move(4) => 43
extern "C" int t_maprev(int n) {
	std::map<int, int> m;
	for (int i = 0; i < n; i++) m.insert(m.end(), std::make_pair((i * 3) % 7, i));
	int s = 0;
	for (auto it = m.rbegin(); it != m.rend(); ++it) s = s * 3 + it->first;
	auto j = m.end();
	--j;
	return s + j->first + (int)m.size();
}
// RUN: @t_maprev(5) => 665

// std::shared_ptr: its refcount bumps/drops go through libstdc++'s __atomic_fetch_add/__atomic_fetch_sub
// (ext/atomicity.h), which the interpreter lowers as plain (non-atomic) RMW since it is single-threaded.
#include <memory>
extern "C" int t_shared(int n) {
	std::shared_ptr<int> a(new int(n));
	{
		std::shared_ptr<int> b = a;   // use_count: 1 -> 2 (fetch_add)
		*b += 1;
	}                                // b destroyed: use_count: 2 -> 1 (fetch_sub)
	return *a * 10 + (int)a.use_count();
}
// RUN: @t_shared(4) => 51

// Aggregate-init of a struct with a reference member (the member holds the referenced object's address,
// same convention as a reference local/field assigned the ordinary way).
struct RefAgg { const int &x; int y; };
extern "C" int t_refagg(int n) {
	int v = n * 2;
	RefAgg r{v, n};
	return r.x + r.y;
}
// RUN: @t_refagg(5) => 15

// A type trait (TypeTraitExpr) and a class template's non-type template parameter (SubstNonTypeTemplateParmExpr),
// both resolved by Sema at parse time for non-dependent instantiations.
#include <type_traits>
extern "C" int t_trait(int n) {
	bool trivial = std::is_trivially_copyable<int>::value;
	bool cls = std::is_class<RefAgg>::value;
	return n + (trivial ? 100 : 0) + (cls ? 10 : 0);
}
// RUN: @t_trait(1) => 111

// Fifth real-project round (CLI11, cpp-httplib-style STL-heavy code): four front-end gaps found and fixed.

// (1) Binding a named function to a forwarding-reference parameter (`T&&`, deduced as a reference-to-function
// type for a function lvalue argument - no pointer decay happens, unlike an ordinary by-value parameter) is
// exactly the shape libstdc++'s `std::function` converting constructor uses internally (`template<typename
// Functor> function(Functor&& f)`) when constructed from a plain function pointer/name, which is how this gap
// was found (CLI11's `std::function<std::string(const App*, const Error&)> = FailureMessage::simple`). `genL`
// on a `DeclRefExpr` to a `FunctionDecl` previously only had a case for the already-decayed
// (`CK_FunctionToPointerDecay`) form and failed on this undecayed one ("reference to 'f' as an lvalue"); a
// second, related gap was in `funcValue` (used for the decayed form) not handling a *further* reference to that
// reference parameter (e.g. passing it on to another function taking `const _Tp&`, as libstdc++'s own
// `_M_not_empty_function` overload resolution does one call frame further in). This minimal, direct
// reproduction isolates the language-level binding itself from `std::function`'s own type-erasure/indirect-call
// machinery (a separate, broader gap: the real `std::function<int(int)> f = double_it; f(n);` call chain goes
// through a template-instantiated static invoker thunk whose address this project's indirect-call candidate
// matching does not currently resolve - out of scope here, not one of the bugs this round fixes).
static int triple_it(int x) { return x * 3; }
template <typename T>
bool same_addr(T &&f) { return (void *)&f == (void *)&triple_it; }
extern "C" int t_func_ref_binding(int n) { return same_addr(triple_it) ? n + 1 : -1; }
// RUN: @t_func_ref_binding(9) => 10

// (2) A handful of builtin names (`exit`, `abort`, `trap`, `_exit`, `unreachable`, `__assert_fail`, ...) were
// matched by bare (unqualified) name on *any* callee, free function or method; a C++ class with its own method
// literally named `exit` (e.g. CLI11's `CLI::App::exit(const Error&, ...)`) collided with the libc-`exit()`
// special case and got silently replaced by `terminateProgram()` - the method's real (scalar) return type was
// never produced, surfacing confusingly as "return of an aggregate" at the call site's enclosing `return`.
struct Exiter {
	int code = 0;
	int exit(int c) { code = c; return code + 1; }  // not libc's exit(): must run as an ordinary method
};
extern "C" int t_method_named_exit(int n) {
	Exiter e;
	return e.exit(n);
}
// RUN: @t_method_named_exit(4) => 5

// (3)+(4): libstdc++'s `basic_string::operator=(basic_string&&)` self-move guard calls `std::__addressof`
// (the internal, `operator&`-bypassing equivalent of `std::addressof`, used pervasively inside the standard
// library's own implementation) - only the public `addressof` name was special-cased, so this fell through to
// an unmodeled external call. Separately, the allocator-propagation step `std::__alloc_on_move` assigns through
// `_Alloc&` references into libstdc++'s `_Alloc_hider : allocator_type` (an empty base, elided by the empty-base
// optimization so it shares its address with the non-empty sibling field `_M_p` that follows it); the trivial
// assignment special case copied `sizeOf()` bytes unconditionally, and `sizeOf()` of a standalone empty class is
// padded to a minimum of 1 (so two distinct empty objects never compare address-equal) - copying that one
// meaningless padding byte through the aliased EBO address corrupted the real pointer field's first byte,
// observed turning a correct `this+16` local-buffer pointer into `(null)+16` right before the `memcpy` that
// implements the move (a false `null_deref`). Isolated reproduction of the EBO corruption, independent of any
// standard-library internals:
struct Empty {};  // eligible for the empty base optimization: occupies 0 bytes as a base-class subobject
struct Holder : Empty { int *p; };  // Holder::p sits at the same offset (0) as the Empty subobject
extern "C" int t_ebo_trivial_assign(int n) {
	int v1 = n, v2 = n * 100;
	Holder a; a.p = &v1;
	Holder b; b.p = &v2;
	Empty &ea = a, &eb = b;  // references to just the empty base subobject, the same shape `std::__alloc_on_move`
	                         // uses to assign allocators: `eb = ea;` must copy zero bytes and leave `b.p` intact
	eb = ea;
	return *b.p;
}
// RUN: @t_ebo_trivial_assign(3) => 300

// The real end-to-end scenario the two bugs above were found in: a move-assignment that is not a self-move
// (the common case: moving a substring result into a destination string) must actually copy the characters.
// Built character-by-character (not from a `const char*` literal) so this test does not also depend on a
// `strlen` ModelDB entry for the concrete-interpreter harness this file runs under - unrelated to this round.
extern "C" int t_str_move_self_guard(int n) {
	std::string a;
	const char *src = "hello world";
	for (int i = 0; i < 11; i++) a += src[i];
	std::string b = a.substr(n);
	std::string c;
	c = std::move(b);  // exercises operator=(string&&)'s std::__addressof self-move guard (taking the "not a
	                    // self-move" branch) and std::__alloc_on_move (a no-op for the stateless allocator)
	return (int)c.size();
}
// RUN: @t_str_move_self_guard(6) => 5

// A genuine self-move (`std::__addressof(__str) == this`): the guard must detect it and skip the copy/length
// update entirely, matching libstdc++'s own (not this project's) behaviour for self-move-assigning a string.
extern "C" int t_str_self_move(int n) {
	std::string s;
	for (int i = 0; i < n; i++) s += 'x';
	s = std::move(s);
	return (int)s.size();
}
// RUN: @t_str_self_move(5) => 0

// std::string 不变式建模 (IMPLEMENTATION_PLAN.md): `find`/`rfind`/`compare` are *declared* in the class body
// (bits/basic_string.h) but *defined* out-of-line in bits/basic_string.tcc; under C++17 libstdc++ wraps that class
// in `extern template class basic_string<char>`, so Sema records these members as "explicit instantiation
// declaration" and leaves no body in a TU that never links libstdc++.so (every TU this project's engines actually
// run) - this project's frontend then has nothing to lower and treats the call as an ordinary unmodelled external,
// falling back to hlir-scan's generic opaque-external result: an arbitrary, untainted value with none of `find`'s
// own invariant (result < size() or == npos). A caller that trusts that invariant - e.g. `current.substr(0, val)`
// right after `val = current.find(',')`, the exact shape CLI11's `split_names` uses - can then be handed a `val`
// that is neither a real match position nor `npos`, raising a real `std::out_of_range` out of `substr` on
// perfectly ordinary input (CLI11 round, IMPLEMENTATION_PLAN "第五轮"). The fix (lib/frontend/Frontend.cpp,
// `lowerC`) makes `basic_string<char>`/`<wchar_t>` ordinary implicitly-instantiated templates again (the same
// `_GLIBCXX_EXTERN_TEMPLATE` escape hatch libstdc++ itself uses for `-D_GLIBCXX_ASSERTIONS` builds, applied
// without that flag's unrelated bounds-check side effects), so these members get real, analyzable bodies like
// every other STL member already does - not a hand-written model of `find`'s semantics. Built without a `const
// char*`-constructed std::string (`strlen` is not linked into the concrete-interpreter harness this file's `RUN:`
// directives run under; this project's --libc/hlir-scan environments do link it and are not affected).
extern "C" int t_str_find(int n) {
	std::string s;
	const char *lit = "ab,cd,ef";
	for (int i = 0; lit[i]; i++) s += lit[i];
	std::string::size_type p1 = s.find(',');
	std::string::size_type p2 = s.find(',', p1 + 1);
	std::string::size_type p3 = s.find('z');  // absent: must be npos, not an arbitrary index
	int r = (int)p1 * 100 + (int)p2;
	if (p3 == std::string::npos) r += 1000;
	return r + n * 0;
}
// RUN: @t_str_find(0) => 1205

extern "C" int t_str_rfind(int n) {
	std::string s;
	const char *lit = "aXbXcX";
	for (int i = 0; lit[i]; i++) s += lit[i];
	return (int)s.rfind('X') + n * 0;
}
// RUN: @t_str_rfind(0) => 5

extern "C" int t_str_compare(int n) {
	std::string a, b;
	const char *la = "hello";
	const char *lb = n ? "hello" : "world";
	for (int i = 0; la[i]; i++) a += la[i];
	for (int i = 0; lb[i]; i++) b += lb[i];
	int c = a.compare(b);
	return c == 0 ? 0 : (c < 0 ? -1 : 1);
}
// RUN: @t_str_compare(1) => 0
// RUN: @t_str_compare(0) => -1

// End-to-end regression for the CLI11 `App::get_default_flag_values`/`split_names` finding (IMPLEMENTATION_PLAN
// "第五轮"): splitting a short, fixed, comma-separated option-name string (the shape of CLI11's own default
// `"-h,--help"`) must not throw `std::out_of_range` out of `substr` - that only happened because `find` (see
// `t_str_find` above) could return an index past the end of the string instead of a real match or `npos`.
extern "C" int t_str_split_names(int n) {
	std::string current;
	const char *lit = "-h,--help";
	for (int i = 0; lit[i]; i++) current += lit[i];
	std::vector<std::string> output;
	std::string::size_type val;
	while ((val = current.find(',')) != std::string::npos) {
		output.push_back(current.substr(0, val));
		current.erase(0, val + 1);
	}
	output.push_back(current);
	int total = 0;
	for (auto &s : output) total += (int)s.size();
	return total * 100 + (int)output.size() + n * 0;
}
// RUN: @t_str_split_names(0) => 802

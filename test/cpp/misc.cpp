// Global references, anonymous-union and bit-field members initialised by constructors.
static int g_val = 7;
static int &g_ref = g_val;
static const int &g_cref = 42;
struct S { union { int a; char c; }; int flag : 3; int m; S(int x) : a(x), flag(2), m(x + 1) {} };
extern "C" int gr1(int x) { g_ref += x; return g_val * 100 + g_cref; }
extern "C" int gr2(int x) { S s(x); return s.a * 100 + s.flag * 10 + s.m; }
// RUN: @gr1(5) => 1242
// RUN: @gr2(5) => 526

// [[fallthrough]] (an AttributedStmt wrapping a null statement) between case labels: common real-world C++17 idiom.
extern "C" int fallthrough1(int n) {
  int acc = 0;
  switch (n) {
    case 4:
      acc += 1;
      [[fallthrough]];
    case 3:
      acc += 10;
      [[fallthrough]];
    case 2:
      acc += 100;
      [[fallthrough]];
    case 1:
      acc += 1000;
      break;
    default:
      acc = -1;
  }
  return acc;
}
// RUN: @fallthrough1(4) => 1111
// RUN: @fallthrough1(3) => 1110
// RUN: @fallthrough1(1) => 1000
// RUN: @fallthrough1(9) => -1

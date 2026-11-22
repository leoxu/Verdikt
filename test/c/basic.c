// RUN: @sum_to(10) => 45
// RUN: @fact(5) => 120
// RUN: @classify(2) => 20
// RUN: @classify(9) => 99
// RUN: @arr_sum(0) => 10
// RUN: @ptr_walk(0) => 6
// RUN: @short_circuit(0) => 0
// RUN: @tern(3) => 6
// RUN: @st(0) => 7
int sum_to(int n) { int s = 0; for (int i = 0; i < n; i++) s += i; return s; }
int fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
int classify(int v) {
  switch (v) { case 1: return 10; case 2: return 20; default: return 99; }
}
int arr_sum(int x) {
  int a[4] = {1, 2, 3, 4}; int s = 0;
  for (int i = 0; i < 4; i++) s += a[i];
  return s;
}
int ptr_walk(int x) {
  char buf[4] = {1, 2, 3, 0}; char *p = buf; int s = 0;
  while (*p) { s += *p; p++; }
  return s;
}
int short_circuit(int x) { int *p = 0; return p && *p; }
int tern(int x) { return x > 2 ? x * 2 : x; }
struct S { int a; char b; long c; };
int st(int x) { struct S s = {3, 4, 0}; struct S t = s; return t.a + t.b; }

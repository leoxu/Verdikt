// an entry whose exploration does not finish within a few seconds: the loop bound is attacker controlled
int slow(int n, int k) {
  int s = 0;
  for (int i = 0; i < n; i++) {
    if ((i ^ k) & 1) s += i & 7;
    else s -= i & 3;
  }
  return s;
}

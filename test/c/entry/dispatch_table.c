// ENTRY: dispatch
// EXPECT: bug ptr_arith_oob
// SPEC: dispatch.yaml
// a devctl-style handler table indexed by an attacker-chosen command: the upper bound is checked, the lower one is not
typedef int (*handler_t)(int arg);
static int h_get(int arg) { return arg; }
static int h_set(int arg) { return arg + 1; }
static int h_clr(int arg) { return 0; }
static handler_t handlers[3] = { h_get, h_set, h_clr };
int dispatch(int cmd, int arg) {
  if (cmd >= 3) return -1;
  return handlers[cmd](arg);
}

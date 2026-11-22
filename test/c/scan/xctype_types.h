// Shared by the xctype_*.c `--link` fixtures: two function pointer types with the same core signature
// `(ptr, ptr, i32) -> i32` but different C types -- the shape of net/rds's `trans->laddr_check(net, addr, scope)` next to
// `rds_getname(sock, uaddr, peer)` (DESIGN §22.342).
struct net_x { int id; };
struct addr6 { unsigned char b[16]; };
struct saddr { char data[256]; };
struct trans { int (*check)(struct net_x *, const struct addr6 *, unsigned); };
struct sops { int (*getname)(struct trans *, struct saddr *, int); };

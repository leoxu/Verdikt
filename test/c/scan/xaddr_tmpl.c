// Shared "template" for xaddr_defs.c (see that file). Like expat's xmltok_ns.c, it both defines a static scanner
// and stores that scanner's address into the object it initialises -- the reference to `init_scan` is written
// here, in the #include'd file, not in the file passed to hlir-scan.
static int init_scan(int x) { return x + 7; }

void enc_init(struct enc *e) { e->scan = init_scan; }

// `--link` fixture, paired with xaddr_entry.c. The only place `init_scan`'s address is taken is xaddr_tmpl.c,
// #include'd here. The indirect-call dispatcher's candidates are the address-taken functions of each unit, and
// that collection used to count only references inside the main file, so `init_scan` was no candidate and the
// call through `e->scan` fell to the opaque fallback (an arbitrary result, default 0) -- expat's XmlInitEncoding /
// initScanProlog, where every document was then rejected.
struct enc { int (*scan)(int); };
#include "xaddr_tmpl.c"

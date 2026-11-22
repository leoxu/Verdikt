// The SDP's own resource-manager API (hlir-scan --qnx; models/qnx.yaml + the iofunc_ocb_attach model in
// models/qnx.core). These functions have no body in any tree being scanned, and leaving them opaque is not a
// neutral approximation in either direction:
//
//   iofunc_attr_init   fills the module's attribute structure. Unmodelled, the structure keeps the zeros the
//                      harness gave it: the branch below is decided for us and the out-of-bounds read behind it
//                      is never reached -- a VACUOUS safe (the failure DESIGN.md §22.373 measured on <driver>).
//   iofunc_ocb_attach  sets ocb->attr = attr. Unmodelled, ocb->attr stays NULL and every ocb->attr->... in the
//                      tree is a PHANTOM null dereference, reported as a real defect.
//
// Two opposite failures from the same omission, which is why both are asserted here.
typedef struct _iofunc_attr { char o[128]; } iofunc_attr_t;
typedef struct _iofunc_ocb { iofunc_attr_t *attr; int ioflag; char rest[20]; } iofunc_ocb_t;
typedef struct _resmgr_context { char o[152]; } resmgr_context_t;

extern void iofunc_attr_init(iofunc_attr_t *a, unsigned mode, iofunc_attr_t *d, void *info);
extern int iofunc_ocb_attach(resmgr_context_t *c, void *m, iofunc_ocb_t *o, iofunc_attr_t *a, const void *f);

static iofunc_attr_t gQAttr;
static iofunc_ocb_t gQOcb;
static char gQBuf[8];

void demo_qnx_init(void) { iofunc_attr_init(&gQAttr, 0666, 0, 0); }

// reads attr->flags (offset 40) as an index: unknown after the model runs, zero without it
int demo_qnx_attr(unsigned idx) {
  unsigned n = *(unsigned *)((char *)&gQAttr + 40);
  if (n > 8) return -1;
  return gQBuf[n] + (int)idx;   // n == 8 is one past the end
}

// dereferences ocb->attr right after attaching it
int demo_qnx_ocb(resmgr_context_t *c, void *m) {
  iofunc_ocb_attach(c, m, &gQOcb, &gQAttr, 0);
  return (int)*(unsigned *)((char *)gQOcb.attr + 40);
}

// --- the rest of the API: the four whose effect is on the INITIALISER's own progress ------------------------
// dispatch_create_channel / resmgr_attach / dispatch_context_alloc / procmgr_daemon decide whether `main` gets
// as far as registering the resource manager at all. Each keeps its failure edge (a module that does not check
// is making a real mistake), and the dispatch context gets its real 152 bytes with UNKNOWN contents -- zeroing
// it would assert `rcvid == 0`, "nobody is waiting", a state the loop never runs in.
typedef struct _dispatch dispatch_t;
typedef struct _dispatch_context { char o[152]; } dispatch_context_t;
typedef struct _resmgr_connect_funcs { char o[80]; } resmgr_connect_funcs_t;
typedef struct _resmgr_io_funcs { char o[272]; } resmgr_io_funcs_t;
extern dispatch_t *dispatch_create_channel(int chid, unsigned flags);
extern dispatch_context_t *dispatch_context_alloc(dispatch_t *d);
extern int resmgr_attach(dispatch_t *d, void *a, const char *p, int t, unsigned f, const void *c, const void *i, void *h);
extern void iofunc_func_init(unsigned nc, resmgr_connect_funcs_t *c, unsigned ni, resmgr_io_funcs_t *i);
extern int procmgr_daemon(int s, unsigned f);
static resmgr_connect_funcs_t cf; static resmgr_io_funcs_t iof;
static char gQBuf2[8];
int demo_qnx_rest(unsigned idx) {
  dispatch_t *dpp = dispatch_create_channel(0, 0);
  if (dpp == 0) return -1;                      // may_fail is kept: this edge must exist
  iofunc_func_init(1, &cf, 1, &iof);
  int id = resmgr_attach(dpp, 0, "/dev/x", 0, 0, &cf, &iof, 0);
  if (id == -1) return -2;                      // the failure edge must exist too
  dispatch_context_t *ctp = dispatch_context_alloc(dpp);
  if (ctp == 0) return -3;
  if (procmgr_daemon(0, 0) != 0) return -4;
  unsigned n = *(unsigned *)((char *)ctp + 16); // a field of the context: unknown, not zero
  if (n > 8) return -5;
  return gQBuf2[n] + (int)idx;
}

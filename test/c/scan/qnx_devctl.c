// A QNX resource manager's devctl entry: the request payload lives PAST the end of the declared pointee type
// (models/interfaces/qnx_resmgr.yaml, DESIGN.md §22.357).
//
// `io_devctl_t` is a 16-byte union. The bytes a client actually sent start at byte 16 of the SAME allocation --
// the resmgr library's receive buffer, `resmgr_attr.msg_max_size` bytes long -- and `_DEVCTL_DATA(msg->i)` is
// literally `(char *)&msg->i + sizeof(msg->i)`. Sized by its declared type the object is 16 bytes, so every
// handler in the tree is out of bounds on its first payload access, before it has run a statement of its own.
// That is a fact about the C declaration and about nothing else, and it is the reason the QNX resmgr rounds had
// never been scanned with the tool at all -- the result would have been one structural artefact per handler.
//
// Three handlers below, registered the way the real tree registers them (field-by-field assignment into a
// `resmgr_io_funcs_t`, not a designated initialiser -- both forms are recorded, and this is the one that is
// actually used):
//
//   demo_devctl_ok     reads a fixed-size payload struct. In bounds under the contract; no finding.
//   demo_devctl_oob    indexes the payload with an attacker-chosen index it never bounds. A real out-of-bounds
//                      read, and it must survive the contract -- widening the object must not hide defects.
//   demo_devctl_verify calls devctl_verify_len() first, which (models/qnx.core) makes `nbytes` the length
//                      encoded in `dcmd`: at most 16383, and equal to the sizeof() that command declares. The
//                      loop that walks `nbytes` entries is then bounded by the module's own check against it.
//
// The sizes here mirror the tree: 2048 is what <driver>, <driver>, <driver> and <driver> all pass to
// `resmgr_attr.msg_max_size`.

typedef struct _resmgr_context resmgr_context_t;
typedef struct _iofunc_ocb iofunc_ocb_t;

struct _io_devctl {
  unsigned short type;
  unsigned short combine_len;
  int dcmd;
  unsigned int nbytes;
  int zero;
};
struct _io_devctl_reply {
  unsigned int zero;
  int ret_val;
  unsigned int nbytes;
  int zero2;
};
typedef union {
  struct _io_devctl i;
  struct _io_devctl_reply o;
} io_devctl_t;

typedef int (*devctl_fn)(resmgr_context_t *, io_devctl_t *, iofunc_ocb_t *);
typedef struct _resmgr_io_funcs {
  unsigned nfuncs;
  int (*read)(resmgr_context_t *, io_devctl_t *, iofunc_ocb_t *);
  int (*write)(resmgr_context_t *, io_devctl_t *, iofunc_ocb_t *);
  devctl_fn devctl;
  int (*msg)(resmgr_context_t *, io_devctl_t *, iofunc_ocb_t *);
} resmgr_io_funcs_t;

int iofunc_devctl_default(resmgr_context_t *ctp, io_devctl_t *msg, iofunc_ocb_t *ocb);
int devctl_verify_len(resmgr_context_t *ctp, io_devctl_t *msg, iofunc_ocb_t *ocb, unsigned checks);

#define _RESMGR_DEFAULT ((int)((~0U ^ (~0U >> 1U)) | 1U))
#define _DEVCTL_DATA(m) ((void *)(sizeof(m) + (char *)(&m)))

#define DEMO_SLOTS 8

struct demo_req {
  unsigned int index;
  unsigned int count;
  unsigned int table[DEMO_SLOTS];
};

// Reads a fixed-size payload struct that sits entirely inside the receive buffer. Under the contract this is in
// bounds; under the declared 16-byte pointee every line of it is an out-of-bounds read.
int demo_devctl_ok(resmgr_context_t *ctp, io_devctl_t *msg, iofunc_ocb_t *ocb) {
  struct demo_req *rx;
  if (iofunc_devctl_default(ctp, msg, ocb) != _RESMGR_DEFAULT) return 0;
  rx = (struct demo_req *)_DEVCTL_DATA((msg->i));
  return (int)(rx->index + rx->count + rx->table[0]);
}

// The payload's own `index` is never bounded against DEMO_SLOTS. Widening the object must not make this go away.
int demo_devctl_oob(resmgr_context_t *ctp, io_devctl_t *msg, iofunc_ocb_t *ocb) {
  struct demo_req *rx;
  if (iofunc_devctl_default(ctp, msg, ocb) != _RESMGR_DEFAULT) return 0;
  rx = (struct demo_req *)_DEVCTL_DATA((msg->i));
  return (int)rx->table[rx->index];
}

// `nbytes` is the client's, but devctl_verify_len() ties it to the length encoded in `dcmd`, and the module
// then checks it against what it is about to write. With the verify modelled there is nothing left to report; with
// it opaque, `nbytes` is an unconstrained 32-bit attacker value and the loop walks off `out[]`.
int demo_devctl_verify(resmgr_context_t *ctp, io_devctl_t *msg, iofunc_ocb_t *ocb) {
  struct demo_req *rx;
  unsigned int out[DEMO_SLOTS];
  unsigned int n, k;
  if (iofunc_devctl_default(ctp, msg, ocb) != _RESMGR_DEFAULT) return 0;
  if (devctl_verify_len(ctp, msg, ocb, 0x400U | 0x1U) != 0) return 22;
  rx = (struct demo_req *)_DEVCTL_DATA((msg->i));
  n = msg->i.nbytes / sizeof(unsigned int);
  if (n == 0u || n > DEMO_SLOTS) return 22;
  for (k = 0; k < n; k++) out[k] = rx->table[0] + k;
  return (int)out[0];
}

resmgr_io_funcs_t demo_io_funcs;

void demo_register(void) {
  demo_io_funcs.devctl = demo_devctl_ok;
  demo_io_funcs.read = demo_devctl_oob;
  demo_io_funcs.msg = demo_devctl_verify;
}

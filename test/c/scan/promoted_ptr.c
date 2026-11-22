// G2 promotes a global the entry reads and the program never wrote (DESIGN.md §22.374). For an INTEGER field
// that works; for a POINTER field it did nothing, and the reason is mechanical: a pointer is only a pointer if
// its bytes carry provenance (Memory.h loadPtr's rdProv/rdPidx test), and the unconstrained bytes promotion
// writes carry none -- so the field reads as obj 0, i.e. NULL, whatever the solver picks. Measured on <driver>'s
// `hal_ctx = gpio_attr_dir->hal_ctx` out of a promoted `s_AttrInfo`: the handler's own command dispatcher
// was unreachable for this reason alone. §22.382 materialises the object the way the synthesis frontier does.
struct pp_ctx {
  unsigned magic;
  char *buf;
};

static struct pp_ctx gPpCtx;   // never written by any function the entry reaches

int demo_pp(unsigned idx) {
  if (gPpCtx.magic != 0xABCDu) return -1;   // the integer field: promotion alone already opens this
  if (gPpCtx.buf == 0) return -2;           // the pointer field: NULL without §22.382, whatever the solver picks
  if (idx > 3) return -3;
  return gPpCtx.buf[idx];                   // reached only when both gates open
}

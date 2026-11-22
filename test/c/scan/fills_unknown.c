// `fills_unknown` (DESIGN.md §22.377): the third answer to "what did this external do to my buffer".
//
// `ext_attr_init` is the shape of `iofunc_attr_init_sized` -- a library function with no body here that fills a
// struct the caller owns. The three ways of modelling it are not interchangeable:
//   * no model (the opaque fallback): the struct still holds what it held, i.e. the zeros the harness gave it.
//     `gAttr.nbytes` is 0, `buf[0]` is in bounds, and the entry is pronounced safe for a reason that is an
//     artefact of the analysis. This is the failure that made a whole QNX resource-manager scan vacuously safe.
//   * `source`: the bytes are the ATTACKER's. The out-of-bounds read below then gets reported as a defect
//     somebody can trigger, which is a lie in the other direction -- nothing attacker-controlled reaches here.
//   * `fills_unknown`: the bytes are unknown and nobody's. The branch is explored, the out-of-bounds read is
//     FOUND, and it is attributed to the analysis's own invention rather than to an attacker.
struct attr { unsigned nbytes; char pad[60]; };

extern void ext_attr_init(struct attr *a);

static struct attr gAttr;
static char buf[8];

int demo_fu_entry(unsigned idx) {
  ext_attr_init(&gAttr);
  if (gAttr.nbytes > 8) return -1;
  return buf[gAttr.nbytes] + (int)idx;   // nbytes == 8 is one past the end
}

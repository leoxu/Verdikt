// A struct whose outermost member is an anonymous union (DESIGN.md §22.484). The collector used to skip unions
// whole, so a parameter of this shape contributed NO pointer fields: `h->inner->len` was then read out of a
// blank stand-in the synthesis frontier made up, and the overrun below could not be found at all.
// `struct folio` is exactly this shape, which is why every address_space_operations handler was affected.
struct inner { unsigned long len; };

struct holder {
  union {
    struct {
      unsigned long flags;
      struct inner *inner;     /* the first arm: the real layout */
    };
    struct {
      unsigned long raw[2];
    };
  };
  unsigned long tail;
};

int ua_entry(struct holder *h, unsigned long idx)
{
  char buf[8];
  if (!h->inner)
    return -1;
  if (idx >= h->inner->len)      /* reachable only if `inner` is a real object */
    return -2;
  buf[0] = 1;
  return buf[idx];               /* oob_read once len > 8 */
}

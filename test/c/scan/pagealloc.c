// The kernel page allocator returns an `unsigned long`, not a pointer (DESIGN.md §22.476). Two things have to
// work for that to be scannable at all: the model must allocate `PAGE_SIZE << order` rather than a constant,
// and the integer it returns must survive the caller's cast back to a pointer with its provenance intact --
// `int_to_ptr` recovers an object only from a CONSTANT `id << 32 | offset`, so the model may not hand back the
// `select(fail, NULL, obj)` that a failable heap_alloc produces.
typedef unsigned int gfp_t;
unsigned long get_free_pages_noprof(gfp_t, unsigned int);

// positive: one page, read past its end
int pg_oob(unsigned idx)
{
  char *p = (char *)get_free_pages_noprof(0, 0);
  if (!p)
    return -1;
  p[idx] = 1;                    /* oob_write once idx >= 4096 */
  return 0;
}

// negative control 1: the same page, read inside it. The NULL check is real and must still be explorable.
int pg_safe(unsigned idx)
{
  char *p = (char *)get_free_pages_noprof(0, 0);
  if (!p)
    return -1;
  p[idx & 4095] = 2;      /* in bounds: nothing to report */
  return 0;
}

// negative control 2: order 2 is FOUR pages. A model that allocated a constant 4096 would report an overrun
// here on correct code -- the one thing a model may never do.
int pg_order2(unsigned idx)
{
  char *p = (char *)get_free_pages_noprof(0, 2);
  if (!p)
    return -1;
  p[idx & 16383] = 2;     /* in bounds for FOUR pages */
  return 0;
}

// `page_address()` / `folio_address()` (DESIGN.md §22.479). The real kernel inline turns a `struct page *` into
// a virtual address by arithmetic on fabricated bases, so lowered faithfully it produces an integer with no
// provenance and every call returns NULL. models/linux.core returns the page pointer itself instead. Two
// properties are asserted here, because a model that got either wrong would be worse than no model.
typedef unsigned int gfp_t;
struct page;
struct page *alloc_pages_noprof(gfp_t, unsigned int);
void *lowmem_page_address(const struct page *);

// 1. STABLE: two calls give the same object. isofs_lookup passes `page_address(p)` and `1024 + page_address(p)`
//    to one function and depends on the second being the first plus 1024; a fresh object per call breaks that.
//    Written through the first pointer, read through the second: an unstable model reports uninit_read here.
int pa_stable(void)
{
  struct page *p = alloc_pages_noprof(0, 0);
  char *a, *b;
  if (!p)
    return -1;
  a = (char *)lowmem_page_address(p);
  b = (char *)lowmem_page_address(p);
  a[7] = 42;
  return b[7];
}

// 2. BOUNDED: the page is 4096 real bytes, so a write past it is a finding ...
int pa_oob(unsigned idx)
{
  struct page *p = alloc_pages_noprof(0, 0);
  char *a;
  if (!p)
    return -1;
  a = (char *)lowmem_page_address(p);
  a[idx] = 1;                     /* oob_write once idx >= 4096 */
  return 0;
}

// ... and a write inside it is not.
int pa_inbounds(unsigned idx)
{
  struct page *p = alloc_pages_noprof(0, 0);
  char *a;
  if (!p)
    return -1;
  a = (char *)lowmem_page_address(p);
  a[idx & 4095] = 1;
  return 0;
}

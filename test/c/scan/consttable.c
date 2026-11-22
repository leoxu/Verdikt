// G2's remaining half (DESIGN.md §22.465): a SYMBOLIC index into a CONSTANT table.
//
// `targets()` used to concretise a symbolic offset to the slot THIS run took, so the byte read back
// carried no taint and the condition built from it was not symbolic at all. The branch landed in
// `const` -- "executed, but the condition was never symbolic" -- and its other edge was never
// explored. Measured on nginx's `usual[]` bitmap; this is the same shape, minimal.
//
// Both halves are here, because a fix that only makes the sick case pass is not evidence:
//
//   tbl_symindex    symbolic index, constant shift  -> the gap. Must reach BOTH edges.
//   tbl_constindex  constant index, symbolic shift  -> never had the gap. Must stay at both edges.
//
// Selection over the static initialiser is EXACT. The other thing G2 could do -- promoting the table
// to an unconstrained value (§22.374) -- is not done here on purpose: §22.465 measured a falsifiable
// condition becoming unfalsifiable once the table stopped being its own initial value.
#include <stdint.h>

// NOT `const`, on purpose: nginx's is `static uint32_t usual[]` (ngx_http_parse.c:17). The first
// version of this fixture was written with `const` and the first version of the gate required it,
// so both agreed with each other and neither agreed with the program G2 exists for. A lookup table
// is defined by nothing ever writing it -- G1's `progWritten` (Sec.22.362) -- not by the qualifier.
static uint32_t usual[8] = {
    0xffffdbfeU, 0x7fff37d6U, 0xffffffffU, 0xffffffffU,
    0xffffffffU, 0xffffffffU, 0xffffffffU, 0xffffffffU,
};

int ct_a, ct_b, ct_c, ct_d;

void tbl_symindex(unsigned char *src, unsigned len)
{
  if (len < 1) return;
  unsigned ch = src[0];
  if (usual[ch >> 5] & 1U) ct_a = 1; else ct_b = 1;
}

void tbl_constindex(unsigned char *src, unsigned len)
{
  if (len < 1) return;
  unsigned ch = src[0];
  if (usual[0] & (1U << (ch & 0x1f))) ct_c = 1; else ct_d = 1;
}

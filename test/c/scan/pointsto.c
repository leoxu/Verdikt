// `points_to` (DESIGN.md §22.475): an external hands back a HANDLE, and the payload is behind a pointer field
// inside it. Without the spec the handle is a zeroed blob, the field reads NULL, and the parser below either
// dies on a null_deref the harness invented or never runs -- which is what made the fs/isofs round vacuous.
#include <stddef.h>

struct blk {
  unsigned long state;   // offset 0
  unsigned size;         // offset 8
  char *data;            // offset 16 (x86_64)
};

struct blk *get_block(int which, unsigned size);   // modelled: ret->data points at `size` attacker bytes

// The defect: `len` is the first byte of the block and nothing bounds it against the block's own size.
// It is reachable ONLY if get_block's payload is attacker-controlled, which is the whole point of the model.
int pt_parse(int which)
{
  struct blk *b = get_block(which, 64);
  char out[16] = {0};          /* initialised: the defect under test is the OVERRUN, not an uninit read */
  unsigned char len;
  unsigned i;

  if (!b)
    return -1;
  len = (unsigned char)b->data[0];
  for (i = 0; i < len; i++)
    out[i] = b->data[1 + i];      // out[16] overruns once len > 16; b->data[1+i] overruns once len > 63
  return out[0];
}

// Negative control: the same block, read within both bounds. Must stay clean.
int pt_safe(int which)
{
  struct blk *b = get_block(which, 64);
  char out[16] = {0};
  unsigned i;

  if (!b)
    return -1;
  for (i = 0; i < 16; i++)
    out[i] = b->data[i];
  return out[0];
}

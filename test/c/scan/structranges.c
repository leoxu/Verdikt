// Declared per-struct field ranges (DESIGN.md §22.480). `blk` is a field of the object the entry is handed, and
// the code shifts by it and masks with it -- both are correct in the real system only because the mount path
// restricted it to 9/10/11, which the synthesised object knows nothing about.
struct sb {
  unsigned long blocksize;   /* offset 0  */
  unsigned long blk;         /* offset 8  */
  char pad[16];
};

int sr_shift(struct sb *s, unsigned long off)
{
  char buf[8];
  unsigned long n = off >> s->blk;     /* shift_range unless blk is bounded */
  if (n >= 8)
    return -1;
  return buf[n];
}

// the mask idiom the isofs directory walk uses: correct only for a power-of-two blocksize, which is what an
// `enum` can state and a range cannot.
int sr_mask(struct sb *s, unsigned long off)
{
  if (s->blocksize > 2048)
    return -1;
  return (int)(off & (s->blocksize - 1));
}

// A `void *` whose real pointee type only the code knows (DESIGN.md §22.482). Without the declared retype the
// synthesis gives it the generic stand-in with no struct name, so no declared range for its real type can apply
// and the shift below is by an unconstrained field.
struct priv { unsigned long zone; };
struct sb2 {
  unsigned long pad;
  void *fs_info;             /* offset 8: really a struct priv * */
};

// No `struct priv *` cast anywhere: the field is read as a raw word, exactly as the frontend sees
// `super_block::s_fs_info` when the cast macro lives in a header it did not fold into this access. A cast in the
// same function IS inferred, and then the field is typed without any declaration -- that case is covered by
// sr_shift above and is not what this fixture is for.
int sr_void(struct sb2 *s, unsigned long off)
{
  char buf[8];
  unsigned long zone = *(unsigned long *)s->fs_info;   /* priv.zone, with nothing naming the type */
  unsigned long n = off >> zone;         /* shift_range unless the retype reaches priv.zone */
  if (n >= 8)
    return -1;
  buf[0] = 1;
  return buf[n];
}

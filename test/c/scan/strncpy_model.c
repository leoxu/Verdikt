// strncpy had NO model at all, so it fell under "assumed opaque: no effect on memory" and left its destination
// UNINITIALISED -- every later read of a buffer the program had just filled came back as a uninit_read. Found as a
// false positive on the c-ares FIX tree while running the CVE-2023-31130 negative control (DESIGN.md §22.385):
// `strncpy(buf, src, sizeof buf)` followed by `if (*buf == ':')`, on a 51-byte stack buffer. The entry stopped at
// its first run (0 runs returned, 7 of 186 branch edges) because that invented UB ended every path.
//
// strncpy is NOT "strcpy with a cap", and both halves of the difference have to be modelled or the model trades
// one wrong answer for another:
//   - the source is SHORTER than n: the rest of the destination is PADDED WITH ZEROS (so it is initialised), and
//   - the source is NOT shorter: NO terminator is written (so reading the destination as a C string is a real bug).
// It also may not scan the source past n bytes: a source with no NUL in the first n is legal, and is exactly the
// case above -- scanning it with plain strlen() invents an out-of-bounds read of a valid object.
#include <string.h>

// (1) padded, therefore initialised: the false positive this model exists to remove
int demo_strncpy_init(const char *src)
{
  char buf[8];
  if (strlen(src) >= sizeof buf) return -1;
  strncpy(buf, src, sizeof buf);
  return buf[0] + buf[7];          /* both ends must read as initialised */
}

// (2) ...but a model that merely zero-fills would hide this: no terminator was written, so strlen runs off the end
int demo_strncpy_unterminated(const char *src)
{
  char buf[4];
  strncpy(buf, src, sizeof buf);
  return (int)strlen(buf);         /* reads past buf */
}

// (3) ...and the source may legally have no NUL inside n: reading src[n] would be the model's own invention
int demo_strncpy_nonul(void)
{
  char src[4], dst[4];
  int i;
  for (i = 0; i < 4; i++) src[i] = (char)('a' + i);   /* deliberately unterminated */
  strncpy(dst, src, 4);
  return dst[0] + dst[3];
}

// A `size_from` whose length parameter is UNTAINTED used to generate a harness that did not compile
// (DESIGN.md §22.478). The entry then came back `unknown` with 0/0 blocks and an `input_error` buried in its
// `incomplete` list -- a contract that silently deleted its own entries. Three of fs/isofs's d_compare slots
// were lost that way, and nothing in the summary said a contract was at fault.
struct ctx { int x; };
struct tops { int (*cmp)(const struct ctx *, unsigned int, const char *); };

static int my_cmp(const struct ctx *ctxp, unsigned int len, const char *str)
{
  unsigned i;
  int s = 0;
  for (i = 0; i < len; i++)
    s += str[i];
  return s + ctxp->x;
}

const struct tops my_tops = { .cmp = my_cmp };

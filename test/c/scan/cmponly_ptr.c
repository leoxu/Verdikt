// `if (p + n > end)` is the standard C bound-check idiom and it is undefined behaviour (C11 6.5.6p8: a pointer
// may land inside its object or one past the end, nowhere else) -- forming the pointer is already UB even though
// nothing is read or written through it. AddressSanitizer agrees: it reports these sites as invalid-pointer-pair
// (verified on c-ares inet_net_pton.c:334 and ares_parse_naptr_reply.c:108). So it is a true positive and stays
// reported -- but it is NOT a memory-safety violation, and when it decided the verdict a c-ares tree with
// CVE-2017-1000381 ALREADY FIXED still read `bug`, with four of these as its only non-warning findings.
//
// It is a warning now. The line between "warning" and "finding" is drawn statically and conservatively: every
// use of the out-of-range pointer must be a comparison or a pointer difference (DESIGN.md §22.390).
int demo_cmponly(const unsigned char *buf, int len)
{
  const unsigned char *p = buf;
  unsigned a, b;

  if (len < 4) return -1;
  a = buf[0];                     /* attacker-controlled, 0..255 */
  b = buf[1];                     /* likewise, and never bounded below */

  /* (1) COMPARE-ONLY: `p + a` can leave the object, but its only use is this comparison. Warning. */
  if (p + a > buf + len) return -2;

  /* (2) COMPARE-ONLY THROUGH A CHAIN: two ptr_adds, the first feeding the second, and only the second is
     compared. Without the transitive step the first add stays a finding -- that is exactly the shape of
     c-ares ares_expand_name.c:175, which on its own kept a clean tree at `bug`. Warning. */
  if (p + a + 1 > buf + len) return -3;

  /* (3) NOT COMPARE-ONLY: `b` was never bounded, and the pointer is DEREFERENCED. A real out-of-bounds read,
     and the arithmetic that produced it must stay a finding. */
  return *(p + b);
}

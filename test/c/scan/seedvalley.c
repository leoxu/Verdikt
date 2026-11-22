// The automatic seed has to cross a VALLEY, not climb a slope (DESIGN.md §22.386).
//
// Measured on c-ares CVE-2023-31130: `inet_net_pton_ipv6` rejects a lone leading ':' outright, so the input the
// defect needs ("::...") is reached only through a point that scores WORSE than the inputs around it -- 39 -> 2
// -> 41 branch edges across a two-byte edit. Every ordering that ranks candidates by how much they cover starves
// that point: random mutation never produced "::" in 500 probes, greedy ascent derived it and threw it away, and
// best-first by total coverage sorted it last and never reached it. Only ranking by NOVELTY -- edges no earlier
// candidate had -- floats it above the crowd of high-scoring candidates whose children re-cover known ground.
//
// This fixture is that shape, in miniature. '#' opens a deep region but a lone '#' is rejected immediately, while
// the digit branch is a broad, rewarding dead end that any coverage-ranked search prefers.
int demo_seedvalley(const char *s)
{
  char out[4];
  if (s[0] == '#') {
    if (s[1] != '#') return -1;        /* the valley: one byte in, and the path ends at once */
    if (s[2] != 'z') return 1;
    out[(unsigned char)s[3] & 0x3f] = 1;   /* out of bounds for any s[3] >= 4 */
    return 0;
  }
  /* The slope: wider and deeper than a lone '#', and it leads nowhere. */
  int n = 0;
  if (s[0] >= '0' && s[0] <= '9') { n++;
    if (s[1] >= '0' && s[1] <= '9') { n++;
      if (s[2] >= '0' && s[2] <= '9') { n++;
        if (s[3] >= '0' && s[3] <= '9') n++; } } }
  return n;
}

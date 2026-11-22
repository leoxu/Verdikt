// `--seed-bytes LABEL=HEX` starts the attacker's bytes from a valid message instead of zeros. It looks the label
// up BY NAME -- and the bytes of a parameter OBJECT used to carry TaintConfig's default "input" while a scalar
// parameter carried the label the spec declares, so one attacker wore two labels and the flag silently did
// nothing for every buffer (DESIGN.md §22.384). Measured on c-ares CVE-2023-31130: with the declared label the
// flag changed nothing; with the literal string "input" the very first run found the defect.
int demo_seedlabel(const char *s)
{
  char out[4];
  // A gate no zero-filled seed can pass. The search can of course solve it given runs; the point of the fixture
  // is the FIRST run, where the seed is the only thing that decides what the bytes are.
  if (s[0] != 'A' || s[1] != 'B' || s[2] != 'C' || s[3] != 'D') return -1;
  out[(unsigned char)s[4] & 0x3f] = 1;   // out of bounds for any s[4] >= 4
  return 0;
}

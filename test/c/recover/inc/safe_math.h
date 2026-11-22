/* a header-defined helper (the <driver> "static_analysis.h" pattern): must be lowered together with its callers */
static inline unsigned int sat_add_u32(unsigned int a, unsigned int b) {
  unsigned int r = a + b;
  return r < a ? 0xffffffffu : r;
}
static inline int clamp_len(int len, int max) { return len > max ? max : len; }

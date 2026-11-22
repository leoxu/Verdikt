// Pointer-field synthesis is FINITE, and the report has to say so (DESIGN.md §22.364).
//
// `fields:` names a pointer and the harness builds it an object; hlir-scan expands two levels of pointees, which
// here names `b`, `c` and `d` and stops. `d`'s object exists but is blank, so `d->e` used to be read out of blank
// content -- and a word with no provenance is obj 0, i.e. NULL -- and `demo_chain_ioctl` was a confirmed null_deref.
//
// Unlike every narrowing a spec carries, that was a WIDENING: it could not hide a defect, it manufactured one. The
// real driver's `.open` builds the whole chain, so no caller can ever see that NULL. Synthesis is otherwise
// deliberate about never inventing NULL -- only a field some visible body actually NULL-tests may be null (§22.353)
// -- and the frontier bypassed that discipline for every pointer at once. Memory::lazyFrontier() now materialises
// the object on demand instead, so BOTH handlers below come out clean.
//
// Found by triaging the sound/core `--entries iface` round: 14 of its 19 confirmed null_deref were exactly this,
// e.g. `rmidi->card->number` at rawmidi.c:627, where `file -> private_data -> substream -> rmidi` used up the
// budget and `rmidi->card` came back NULL.
//
// `file` is the session (kernel-owned, untainted) under the interface contract, so the pointers the harness stores
// into it are the real synthesised objects rather than attacker-chosen words -- which is what makes the frontier,
// and not the taint, the only thing that can produce a NULL here.
struct l5 {
  int v;
  int w;
};
struct l4 { struct l5 *e; };
struct l3 { struct l4 *d; };
struct l2 { struct l3 *c; };
struct file { struct l2 *b; };

// walks one pointer past the frontier
long demo_chain_ioctl(struct file *file, unsigned int cmd, unsigned long arg) {
  (void)cmd;
  (void)arg;
  return file->b->c->d->e->v;
}

// the same chain stopped at the frontier: every pointer it walks is named by the spec, so it stays inside the
// synthesised objects and must come out clean.
long demo_inside_ioctl(struct file *file, unsigned int cmd, unsigned long arg) {
  (void)cmd;
  (void)arg;
  return file->b->c->d != 0;
}

// An object materialised past the frontier is a stand-in for a struct the engine never looked at, so its SIZE is a
// stand-in too -- it is whatever kFrontierObjBytes happens to be. Walking an array inside it therefore says nothing
// about the real struct, in either direction. This is `snd_mixer_oss_devmask` (sound/core/oss/mixer_oss.c:133):
// `for (chn = 0; chn < 31; chn++) pslot = &mixer->slots[chn];` where `mixer` is past the frontier. Once the pointer
// stopped being NULL that loop walked 31 * sizeof(slot) bytes of an invented allocation and came out a confirmed
// ptr_arith_oob -- 16 of round 44's 20, a fact about our own constant and nothing else. Memory::sizeIsReal() keeps
// the bounds checks from being asked out here at all, and the report's `synthesis_frontier` assumption says so.
struct slot { long a, b, c, d, e, f, g, h, i; };  // 72 bytes, as snd_mixer_oss_slot is
struct l3arr { struct slot slots[31]; };
struct l2arr { struct l3arr *c; };
struct filearr { struct l2arr *b; };

long demo_array_read(struct filearr *file, char *buf, unsigned long count, long long *ppos) {
  (void)buf;
  (void)count;
  (void)ppos;
  long r = 0;
  for (int chn = 0; chn < 31; chn++) {
    struct slot *pslot = &file->b->c->slots[chn];
    r |= pslot->a;
  }
  return r;
}

// Past the frontier the CONTENT is invented too, not just the size: `v` was never read from anywhere, the harness
// filled it in. A divisor that only the harness's own filler can make zero is our invention failing, not the
// program -- so it is still reported, with its witness, but as a `warning`, and the entry does not become `bug`
// (DESIGN.md §22.365). This is `oss_frame_bytes = plugin_first->src_width * ... / 8` at
// sound/core/oss/pcm_oss.c:1371: in the real kernel `snd_pcm_oss_change_params` sets src_width, and the engine
// walked past that constructor because another invented field (`runtime->oss.params`) read "already configured".
long demo_div_write(struct file *file, const char *buf, unsigned long count, long long *ppos) {
  (void)buf;
  (void)ppos;
  return count / file->b->c->d->e->v;
}

// ... unless the program SAYS what the field can be. `w` is just as invented as `v`, but the module states its
// invariant in its own assertion macro, and that harvest (fieldAsserts, DESIGN.md §22.358) already exists -- it
// was simply never applied out here, because it becomes a `where:` precondition on the objects the InitPlan names
// and a frontier object is materialised at run time, long after the plan is built (§22.365). Now it is applied,
// so this divisor is known nonzero and there is no finding at all. The real instance is
// `snd_BUG_ON(plugin->src_width <= 0)` at sound/core/oss/pcm_plugin.c:173, guarding the divisor of
// `oss_frame_bytes` at pcm_oss.c:1365.
#define assert(c) \
  do {            \
    if (!(c)) __builtin_trap(); \
  } while (0)

void demo_l5_invariant(struct l5 *e) { assert(e->w > 0); }

long demo_div_llseek(struct file *file, long long offset, int whence) {
  (void)whence;
  return offset / file->b->c->d->e->w;
}

struct file_operations {
  long (*unlocked_ioctl)(struct file *, unsigned int, unsigned long);
  long (*compat_ioctl)(struct file *, unsigned int, unsigned long);
  long (*read)(struct filearr *, char *, unsigned long, long long *);
  long (*write)(struct file *, const char *, unsigned long, long long *);
  long (*llseek)(struct file *, long long, int);
};
const struct file_operations demo_fops = {.unlocked_ioctl = demo_chain_ioctl,
                                          .compat_ioctl = demo_inside_ioctl,
                                          .read = demo_array_read,
                                          .write = demo_div_write,
                                          .llseek = demo_div_llseek};

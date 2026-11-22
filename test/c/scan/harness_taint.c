// The harness's own structural choices are NOT attacker data (DESIGN.md §22.363).
//
// `demo_ioctl` is registered in `file_operations.unlocked_ioctl`, so under the interface contract `file` is the
// session: kernel-owned, untainted. `cmd` and `arg` ARE attacker data -- and are deliberately unused here, so the
// only thing left that could make anything "tainted" is the harness's own synthesis of `file`: each pointer field
// it creates is `nullable`, and that NULL-or-not choice is a free input of the harness.
//
// `devmask` then loops a literal 31 times reading those fields. No attacker input can change that iteration count,
// so `tainted_loop_bound` must not fire. It did: `TVal::tainted()` means "has a symbolic term", and promoting a
// structural choice to symbolic was implemented by giving it a taint label, which made every such choice look like
// attacker control to the three security verdicts that ask `isTainted` (sink / loop bound / index).
//
// Found by triaging the sound/core `--entries iface` round: 24 of its 55 confirmed findings were this, all on
// loops whose bound is a literal constant.
struct slot { int (*put_volume)(int); int (*put_recsrc)(int); int stereo; };
struct mixer { struct slot slots[31]; int mask; };
struct file { void *private_data; };

static int noop(int x) { return x; }

static int devmask(struct mixer *m) {
  int result = 0, chn;
  for (chn = 0; chn < 31; chn++) {          // a literal bound: the attacker cannot change the iteration count
    struct slot *p = &m->slots[chn];
    if (p->put_volume || p->put_recsrc)     // ... but this condition reads harness-chosen NULL-or-not fields
      result |= 1 << chn;
  }
  return result;
}

long demo_ioctl(struct file *file, unsigned int cmd, unsigned long arg) {
  struct mixer *m = file->private_data;
  (void)arg;
  (void)cmd;
  (void)noop;
  if (!m) return -1;
  return devmask(m);
}

struct file_operations { long (*unlocked_ioctl)(struct file *, unsigned int, unsigned long); };
const struct file_operations demo_fops = {.unlocked_ioctl = demo_ioctl};

// The session constructor (`setup:`, DESIGN.md §22.368 §7).
//
// A handler is handed a per-fd object the module's own `.open` built -- `file->private_data`, a QNX OCB, a device
// context. Synthesising that object field by field produces one whose fields are individually legal and jointly
// impossible, which is the §22.365 root cause; and the interface contract says so in the report today:
// "running that constructor is not implemented, so it degrades to kernel-owned untainted state".
//
// That sentence is what this fixture is about. `demo_sc_ioctl` divides by `s->scale`, which the constructor sets
// to a nonzero value and which NOTHING else ever writes. Without the constructor the field is whatever the
// harness invented -- it can be zero -- and the scan reports a division by zero that the real driver cannot
// perform. With the constructor run, the field holds what `demo_sc_open` put there and the finding is gone,
// because it was never a defect of the program.
//
// The control is `demo_sc_ioctl_oob`: a real defect of the handler's own, which the constructor neither causes
// nor prevents. It must survive, or "run the constructor" would just be a way of making findings disappear.

struct sess {
  int scale;        // set by the constructor; never zero in a real session
  int limit;        // set by the constructor to the real capacity of buf
  unsigned char buf[8];
};

struct inode;       // the constructor's other parameter: kernel-owned context, not attacker input

int demo_sc_open(struct inode *ino, struct sess *s) {
  (void)ino;
  if (!s) return -1;
  s->scale = 4;
  s->limit = 8;
  return 0;
}

// Divides by a field only the constructor ever writes.
long demo_sc_ioctl(struct sess *s, unsigned long arg) {
  return (long)(arg / (unsigned long)s->scale);
}

// A constructor that performs real UB on the way -- here `&tbl[0] - 1`, the shape of an empty-list container_of,
// but written so the waiver does not apply (the subtraction is on an int*, not a byte pointer). It still finishes
// its job. The entry must not become a `bug` because of it, must still be analysed, and the UB must be reported
// as a warning saying where it really is. Round 49b measured the cost of getting this wrong: one deterministic UB
// in setup code made all 87 sound/core entries `bug` and stopped any of them from being analysed at all.
static int tbl[4];
static int *cursor;

int demo_sc_open_ub(struct inode *ino, struct sess *s) {
  (void)ino;
  if (!s) return -1;
  cursor = &tbl[0] - 1;   // UB here, inside the constructor
  cursor = &tbl[0];
  s->scale = 4;
  s->limit = 8;
  return 0;
}

// ... and a defect of the handler's own: `arg` indexes `buf` with only the session's own limit as a guard, and
// that guard is off by one. Running the constructor does not create or remove it.
long demo_sc_ioctl_oob(struct sess *s, unsigned long arg) {
  if (arg > (unsigned long)s->limit) return -1;   // `>` should be `>=`: arg == limit == 8 reads buf[8]
  return s->buf[arg];
}

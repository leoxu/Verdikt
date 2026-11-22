// Lowering an interface contract into the entry-spec DSL (DESIGN.md §22.361): the handlers below have the real
// kernel signatures, so `file_operations`' slots apply to them parameter for parameter. What the contract must
// change relative to generic synthesis: `struct file *` stops being attacker data, the __user buffer stops being
// a kernel object, and the scalars the attacker really controls stay controlled.
typedef unsigned long size_t;
typedef long ssize_t;
typedef long long loff_t;
struct inode;
struct poll_table_struct;

// a real pointee, so generic synthesis would have something to taint field by field -- the contrast the test checks
struct file {
  void *private_data;
  unsigned int f_flags;
};

struct file_operations {
  int (*open)(struct inode *, struct file *);
  ssize_t (*read)(struct file *, char *, size_t, loff_t *);
  ssize_t (*write)(struct file *, const char *, size_t, loff_t *);
  long (*unlocked_ioctl)(struct file *, unsigned int, unsigned long);
  unsigned int (*poll)(struct file *, struct poll_table_struct *);
};

static int demo_open(struct inode *ino, struct file *filp) { (void)ino; filp->f_flags = 0; return 0; }

// file: session, buf: user_addr(out, size_from count), count: value, ppos: kernel_owned(inout)
static ssize_t demo_read(struct file *filp, char *ubuf, size_t count, loff_t *ppos) {
  (void)ubuf;
  (void)ppos;
  return (ssize_t)(count + filp->f_flags);
}

// file: session, cmd: value, arg: user_addr -- but `arg` is a SCALAR, so it is an attacker-controlled value, not
// an object: the user_addr role must not turn it into an empty buffer.
static long demo_ioctl(struct file *filp, unsigned int cmd, unsigned long arg) {
  (void)filp;
  return (long)(cmd + arg);
}

// every parameter is kernel-owned or session state: under the contract there is nothing for the attacker to supply
static unsigned int demo_poll(struct file *filp, struct poll_table_struct *wait) {
  (void)wait;
  return filp->f_flags;
}

// registered in `.write`, whose contract describes four parameters -- this takes three. The contract must be
// dropped WHOLE (a shifted parameter list would silently mislabel every role) and the function synthesised
// generically, with a note saying so.
static ssize_t demo_write3(struct file *filp, const char *buf, size_t n) {
  (void)filp;
  (void)buf;
  return (ssize_t)n;
}

const struct file_operations demo_fops = {
    .open = demo_open,
    .read = demo_read,
    .write = (ssize_t(*)(struct file *, const char *, size_t, loff_t *))demo_write3,
    .unlocked_ioctl = demo_ioctl,
    .poll = demo_poll,
};

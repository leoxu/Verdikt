// Dispatch-table registrations: which handler was written into which slot of which vtable struct
// (frontend::LowerResult::vtableBindings, DESIGN.md §22.359). Both shapes real code uses, plus the cases that must
// NOT produce a binding.
typedef unsigned long size_t;
typedef long ssize_t;
struct inode;
struct file;

// ---- shape 1: a static initialiser with designated initialisers (how the kernel registers almost everything)
struct file_operations {
  void *owner;                                            // not a function pointer: must NOT bind
  ssize_t (*read)(struct file *, char *, size_t);
  ssize_t (*write)(struct file *, const char *, size_t);
  long (*unlocked_ioctl)(struct file *, unsigned, unsigned long);
  int (*release)(struct inode *, struct file *);
};

static ssize_t demo_read(struct file *f, char *b, size_t n) { (void)f; (void)b; return (ssize_t)n; }
static ssize_t demo_write(struct file *f, const char *b, size_t n) { (void)f; (void)b; return (ssize_t)n; }
static long demo_ioctl(struct file *f, unsigned c, unsigned long a) { (void)f; (void)c; return (long)a; }
static int demo_release(struct inode *i, struct file *f) { (void)i; (void)f; return 0; }

static void *const demo_owner = 0;

// expect: file_operations#read -> demo_read, file_operations#write -> demo_write,
//         file_operations#unlocked_ioctl -> demo_ioctl.   `.owner` must not appear.
const struct file_operations demo_fops = {
    .owner = (void *)&demo_owner,
    .read = demo_read,
    .write = demo_write,
    .unlocked_ioctl = demo_ioctl,
};

// ---- shape 2: a run-time assignment (some drivers patch the table during probe)
// expect: file_operations#release -> demo_release
void demo_patch(struct file_operations *ops) { ops->release = demo_release; }

// ---- negative 1: a struct nobody modelled still yields a binding (the MODEL decides, not the frontend)
struct demo_private_ops {
  int (*step)(int);
};
static int demo_step(int x) { return x + 1; }
// expect: demo_private_ops#step -> demo_step   (recorded; `--entries iface` will ignore it)
const struct demo_private_ops demo_privops = {.step = demo_step};

// ---- negative 2: a nested record initialiser keys the slot by the INNER tag, never the outer one
struct demo_inner { int (*cb)(int); };
struct demo_outer { int tag; struct demo_inner in; };
static int demo_cb(int x) { return x - 1; }
// expect: demo_inner#cb -> demo_cb.   demo_outer#in must NOT appear (it is not a function pointer anyway).
const struct demo_outer demo_nested = {.tag = 7, .in = {.cb = demo_cb}};

// ---- negative 3: an array of vtables binds every element to the ELEMENT type
static int demo_s0(int x) { return x; }
static int demo_s1(int x) { return -x; }
// expect: demo_private_ops#step also -> demo_s0 and demo_s1
const struct demo_private_ops demo_table[2] = {{.step = demo_s0}, {.step = demo_s1}};

// ---- negative 4: taking an address without storing it in a record field binds nothing
static int demo_loose(int x) { return x * 2; }
int (*demo_loose_ptr)(int) = demo_loose;  // a plain global pointer, not a record field: no binding

int demo_entry(unsigned cmd) { return (int)cmd; }

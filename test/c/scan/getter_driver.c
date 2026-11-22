// hlir-scan fixture: private data reached through getters (i2c_get_clientdata -> dev_get_drvdata -> dev->driver_data)
// and an intrusive list in the recovered object.
struct list_head { struct list_head *next, *prev; };
struct device { void *driver_data; int id; };
struct client { int addr; struct device dev; };

static inline void *dev_get_drvdata(const struct device *d) { return d->driver_data; }
static inline void *client_get_data(const struct client *c) { return dev_get_drvdata(&c->dev); }

struct my_dev { int n; struct list_head queue; int count; };

static inline void list_add_head(struct list_head *new, struct list_head *head) {
  struct list_head *next = head->next;
  next->prev = new;
  new->next = next;
  new->prev = head;
  head->next = new;
}

int on_event(struct client *c, int ev) {
  struct my_dev *d = client_get_data(c);
  struct list_head item;
  list_add_head(&item, &d->queue);
  d->count = (ev & 0xf);
  return d->n & 0xff;
}

/* `unused` is never read or written by the code above: it gets no object (only pointer fields that are used are initialised) */
struct big { int a; int *used; int *unused; };
int use_big(struct big *b) { return *b->used & 0xff; }

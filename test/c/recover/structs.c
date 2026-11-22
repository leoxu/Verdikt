// hlir-scan --recover fixture: struct definitions and constants live in a header that does not exist.
//   struct ctx / struct req are only forward-declared; their members are inferred from how this file uses them.
#include <string.h>
#include "missing_structs.h"
struct ctx; struct req; struct dev;
int getpid(void);

int get_pid(struct ctx *c, struct req *a) {
  struct dev *d = c->dev;                 /* c->dev: pointer to struct dev (typed variable) */
  a->pid = getpid();                      /* a->pid: int (assigned from a prototyped call) */
  return d != 0;
}
int copy_req(struct req *r, char *out) {
  char local[8];
  if (r->size > 16u) return -1;           /* r->size: unsigned (compared) ... */
  memcpy(local, r->data, r->size);        /* ... and size_t (argument), so unsigned long; r->data: void * */
  out[0] = local[0];
  return r->flags;
}
int nested(struct ctx *c) { return c->cfg.level + c->opts->mode; }   /* c->cfg is a struct, c->opts a pointer to one */
int classify(int x) {
  switch (x) {                            /* two different constants from the missing header: distinct values */
    case CMD_START: return 1;
    case CMD_STOP: return 2;
    default: return 0;
  }
}

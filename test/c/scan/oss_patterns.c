// hlir-scan fixture: patterns that real projects (bzip2, ...) exposed in the generated entry specs.
#include <stdlib.h>
#include <string.h>

/* 1. a C string parameter: `const char *` without a length is NUL-terminated */
int count_w(const char *mode) {
  int n = 0;
  while (*mode) { n += (*mode == 'w'); mode++; }
  return n;
}
/* ... but `const char *buf, int len` is a buffer with a length */
int sum_buf(const char *buf, int len) {
  int s = 0;
  for (int i = 0; i < len; i++) s += buf[i];
  return s;
}

/* 2. a struct bigger than the default max_obj (4096) */
struct big { char data[10000]; int n; };
int big_get(struct big *b) { return b->data[b->n & 0xff]; }

/* 3. a callee that frees its parameter: the caller must pass a heap object */
void my_free(void *p) { free(p); }
void free_twice(void *p) { free(p); free(p); }

/* 4. an opaque handle typed one call deeper */
typedef void HANDLE;
struct state { int a; int b; };
static int inner(HANDLE *h) { struct state *s = (struct state *)h; return ((s->a & 0xff) + (s->b & 0xff)) & 0xff; }
int outer(HANDLE *h) { return inner(h); }

/* 5. a handle released through a local and a callee; an array with a camelCase count */
static void release(struct state *s) { free(s); }
void close_h(HANDLE *h) { struct state *st = (struct state *)h; release(st); }
int sum_ints(int *vals, int nVals) {
  int s = 0;
  for (int i = 0; i < nVals; i++) s += vals[i] & 0xff;
  return s;
}

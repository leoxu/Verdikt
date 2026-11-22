/* Third translation unit for the cross-unit used-fields test: the only file that reads `outer.target`. Not included
   or seen by field_use_entry.c's own AST at all -- only --link's whole-program view connects the two. */
#include "field_use.h"
#include <string.h>

int touch_ok(struct outer *o, char *out, int n) {
  if (n < 0 || n > 4) return -1;
  memcpy(out, o->target->tag, (unsigned long)n);  /* tag is 4 bytes: bounded */
  return o->target->val;
}

int touch_bug(struct outer *o, char *out, int n) {
  if (n < 0 || n > 16) return -1;                 /* struct inner is 8 bytes (int val + char tag[4], padded); */
  memcpy(out, o->target->tag, (unsigned long)n);  /* n up to 16 reads past the object -- a real OOB, reachable only
                                                       once `target` is allocated as a real inner, not left null. */
  return 0;
}

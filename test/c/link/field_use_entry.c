/* Entry-holding unit for the cross-unit used-fields test (see field_use.h, field_use_body.c): this file's own AST
   never touches `outer.target` -- it only forwards `o` into touch_ok/touch_bug, whose bodies live in the other file.
   A per-unit used-fields check (no --link awareness) would leave `target` at zero, turning both entries into an
   immediate null_deref false positive before any real code is reached. */
#include "field_use.h"

int touch_ok(struct outer *o, char *out, int n);
int touch_bug(struct outer *o, char *out, int n);

int entry_ok(struct outer *o, char *out, int n) { return touch_ok(o, out, n); }
int entry_bug(struct outer *o, char *out, int n) { return touch_bug(o, out, n); }

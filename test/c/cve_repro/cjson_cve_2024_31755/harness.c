// Harness for CVE-2024-31755 (cJSON v1.7.17, fixed in 7e4d5dabe7a9b754c601f214e65b544e67ba9f59): calls the real,
// unmodified cJSON_SetValuestring with a pointer whose null-ness is derived from a tainted selector, mirroring the
// project's established pattern for exercising a null-deref that depends on which value a caller happened to pass
// (scanner_friendly_demo.c, test/c/cve_repro/brotli_cve_2026_111497_prefix/harness.c) -- consume() shape so
// hlir-scan's own entry/taint machinery drives the exploration instead of a single hand-picked literal input.
#include "cJSON.h"

void cjson_setvaluestring_entry(int use_null, const char *s) {
  cJSON *item = cJSON_CreateString("x");
  const char *v = use_null ? (const char *)0 : s;
  cJSON_SetValuestring(item, v);
}

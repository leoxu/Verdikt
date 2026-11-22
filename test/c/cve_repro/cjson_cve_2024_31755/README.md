# CVE-2024-31755 — cJSON v1.7.17 `cJSON_SetValuestring` NULL deref

## Source

- Repo: https://github.com/DaveGamble/cJSON
- Vulnerable commit: `87d8f0961a01bf09bef98ff89bae9fdec42181ee` (== tag `v1.7.17`)
- Fix commit: `7e4d5dabe7a9b754c601f214e65b544e67ba9f59` ("Add NULL check to cJSON_SetValuestring()"), 11 commits before `v1.7.18`
- NVD: CVE-2024-31755, CVSS 3.1 7.6 HIGH, CWE-476 (NULL Pointer Dereference)

`cJSON.c`/`cJSON.h` here are the unmodified vulnerable (`v1.7.17`) sources. The fix is a single line in
`cJSON_SetValuestring`:
```diff
-    if (object->valuestring == NULL)
+    if (object->valuestring == NULL || valuestring == NULL)
```
The vulnerable version only checks `object->valuestring`, not the `valuestring` parameter itself, so
`cJSON_SetValuestring(item, NULL)` reaches `strlen(valuestring)` with a NULL pointer.

## Harness

`harness.c`'s `cjson_setvaluestring_entry(int use_null, const char *s)` derives the pointer passed to
`cJSON_SetValuestring` from a tainted selector (`use_null ? NULL : s`), the same pattern used throughout this
project's other CVE repros (e.g. `test/c/cve_repro/brotli_cve_2026_111497_prefix/harness.c`) to let
`hlir-scan`'s own taint-concolic search discover the triggering input instead of hand-picking a single literal.

## Reproducing

```sh
hlir-scan --link --entry cjson_setvaluestring_entry --timeout 60 cJSON.c harness.c
```
Found cleanly on the vulnerable source (`cJSON.c` here): `verdict: bug`, `null_deref`, replay-confirmed, call
chain `cjson_setvaluestring_entry -> cJSON_SetValuestring -> strlen -> __hlir_strlen`, counterexample
`use_null = 64` (truthy), in 30.8s.

## Negative control (fixed version) — honest caveat

Re-running the same harness against the real fixed `cJSON.c` (`7e4d5dabe7a9b754c601f214e65b544e67ba9f59`, not
checked in here) does **not** confirm the finding (good), but also does not reach `verdict: safe` within a
120–600s budget — it stays `unknown`/`incomplete:symbolic_time_budget`. The concolic pass's own coverage-guided
search reaches a fixed point quickly (~65 runs, no finding) at 82%/43% block/branch coverage; the remaining gap
is handed to the symbolic escalation pass (triggered because a tainted pointer was followed concretely), and
that pass does not finish proving the rest clean within the budgets tried. See `docs/DESIGN.md` for the section
documenting this in full, including how far a much larger budget got.

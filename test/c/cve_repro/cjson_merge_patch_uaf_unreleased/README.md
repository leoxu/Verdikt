# cJSON `merge_patch` heap-use-after-free — unreleased at scan time (found via `hlir-scan`, not a known CVE)

## Source

- Repo: https://github.com/DaveGamble/cJSON
- `cJSON.c`/`cJSON.h`/`cJSON_Utils.c`/`cJSON_Utils.h` here are the real, unmodified sources at tag `v1.7.19`
  (commit `c859b25`, the latest tagged release as of this scan) — **vulnerable**.
- Fix commit: `6d9f2443ab071f86e5d9b43025a40929ec41c46c`, "Fix: heap-use-after-free in merge_patch when patch is
  subtree of target (#1065)", merged to `master` 2026-09-16 — **not in any tagged release yet** at scan time.
  Fixes upstream issue #1060.

## The bug

`merge_patch()`'s non-object branch (`cJSON_Utils.c`):
```c
if (!cJSON_IsObject(patch))
{
    /* scalar value, array or NULL, just duplicate */
    cJSON_Delete(target);
    return cJSON_Duplicate(patch, 1);
}
```
If `patch` is a subtree of `target` (an aliased pointer obtained via e.g. `cJSON_GetObjectItem(target, ...)`,
not an independently allocated object), `cJSON_Delete(target)` frees the memory `patch` points into, and the
following `cJSON_Duplicate(patch, 1)` reads it. Fix: duplicate `patch` first, then delete `target`.

## Harness

`harness.c`'s `merge_patch_uaf_entry()` takes **no attacker-controlled input** — this is a pure API-misuse/
aliasing bug, reproduced the same way the fix commit's own regression test does it: build `target = {"a":
[1,2,3]}`, take `patch = cJSON_GetObjectItem(target, "a")` (a subtree of `target`, not independent), call
`cJSONUtils_MergePatch(target, patch)`.

## Reproducing

```sh
hlir-scan --link --include-noarg --entry merge_patch_uaf_entry --timeout 60 cJSON.c cJSON_Utils.c harness.c
```
Found immediately (0.08s): `verdict: bug`, `use_after_free`, replay-confirmed, call chain
`merge_patch_uaf_entry -> cJSONUtils_MergePatch -> merge_patch -> cJSON_Duplicate -> cJSON_Duplicate_rec` at
`cJSON.c:2793:21` — matches the fix commit's own description ("detected by AddressSanitizer at
cJSON_Duplicate_rec, cJSON.c:2808" at the exact `master` revision the fix was authored against; the small line
offset is just the file's own churn between that revision and `v1.7.19`).

Negative control (swap in the real fixed `cJSON_Utils.c` from commit `6d9f2443...`, not checked in here): same
harness, same command, `verdict: safe_under_assumptions` in 0.06s.

## Why this is here, not under `docs/KNOWN_GAPS_PRIORITIZED.md` or as a formal CVE repro

No CVE has been filed for this (checked at scan time); it's a real, fixed-on-`master`-but-unreleased bug found
by scanning the **latest tagged release** of a project this session had already built tooling and ground-truth
familiarity with (`docs/DESIGN.md`'s cJSON CVE-2024-31755 write-up), not a known-CVE ground-truth repro like the
other `test/c/cve_repro/*` directories. Kept here under the same directory family since the shape (real
project, real unmodified source, a harness, a README with the exact repro command) matches.

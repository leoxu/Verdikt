# `--reach-target` demos

Two teaching examples, not CVE repros and not registered `ctest` fixtures -- see `docs/DESIGN.md` Sec.22.332
for the full step-by-step walkthrough and output transcripts.

## `reach_demo.c` — minimal example

A single branch (`z == 123456789` in `target()`) competing against 20 irrelevant "noise" branches for a tiny
flip budget.

```sh
hlir-scan --list reach_demo.c
hlir-scan --runs 2 --timeout 10 reach_demo.c                            # UNKNOWN: budget spent on noise
hlir-scan --runs 2 --timeout 10 --reach-target target reach_demo.c      # BUG: found within the same budget
```

## `reach_demo2.c` — slightly more complex example

Scaled-down version of the real brotli CVE-2026-111497 shape (`docs/DESIGN.md` Sec.22.322): a "block switch"
function sets a state field on its success path but not on its early-return failure path; a reader several
call frames away trusts the field without re-checking it. Reaching the bug needs two independent conditions to
hold at once, and the write/read sites are in different functions -- the actual shape
`findWriteSites`/`reachWriteSite` (`docs/DESIGN.md` Sec.22.329/22.330) are built to locate and target.

```sh
hlir-scan --runs 4 --timeout 10 reach_demo2.c                                 # UNKNOWN
hlir-scan --runs 4 --timeout 10 --reach-target read_symbol reach_demo2.c      # BUG: found one budget step earlier
```

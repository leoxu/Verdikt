# Verdikt

A concolic / symbolic vulnerability scanner for C and C++ built on a small, security-oriented core IR.

Verdikt is designed around one rule: **never force a finding**. Every result is one of

- `bug` — reproduced (replayed) on the concrete interpreter,
- `safe_under_assumptions` — no defect found, with every assumption listed in the report,
- `unknown` — the search was incomplete (budget, coverage, unsupported construct); the reason is named.

There is no "probably" verdict.

## Features

### Analysis engine
- **`core` IR** — a text-based dialect that is the only interface between frontends and the engine. Pointers carry explicit allocation provenance, and safety conditions are explicit check instructions (`core.check.oob`, `.ptr_arith`, `.null`, `.uaf`, `.field_oob`, ...) rather than relying on undefined behaviour to trigger at run time.
- **Concrete interpreter** — detects out-of-bounds reads/writes, null and dangling pointer dereference, double/invalid free, signed overflow, bad shifts, divide-by-zero, writes to const data, uninitialized reads, and array overflow inside a struct field (`field_oob`, distinct from whole-object `oob`).
- **Taint-guided concolic + symbolic engine** — SMT-backed exploration (`lib/smt`) driven by which bytes an attacker controls: branches are flipped where taint reaches a check, not everywhere.
- **Replay confirmation** — each `bug` finding is replayed on the concrete interpreter before it is reported.
- **Bounded verdicts** — loop-bounded unrolling with iterative deepening (`safe_up_to_loop_bound`), frontier/step/memory budgets, minimum-coverage gates, and branch-direction coverage in every report.

### Scanning real code
- **C and C++ frontend** — lowers real source through libclang straight to `core`, including struct layouts, bitfields, VLAs and inline/static-inline handling. Missing headers and unknown types are recovered from by default (`--strict` to disable).
- **Automatic entry discovery** — scan every attack-surface function at once with `--entries roots|exported|all|iface`, or name entries explicitly.
- **Entry/harness generation** — from a function signature and an optional declarative YAML spec (taint labels, buffer sizes, struct field offsets and ranges, value relations), Verdikt generates seeds and the initial memory layout.
- **Dispatch-interface models** — handlers registered in driver/ops tables (`file_operations`, Wayland request vtables, QNX resource-manager tables, ...) are scanned with the contract of the slot they are bound to, via `--entries iface`.
- **Whole-program linking** — `--link` merges translation units so cross-file call chains are scanned as they really execute.
- **Threat-model switches** — `--untrusted-api` treats a lower component as compromised; `--spawn-callbacks` follows thread bodies; `--hostile` drops length/buffer relations.
- **Parallel scans and reports** — worker processes with per-entry timeouts; `text`, `json` or `sarif` output.

### Models
Hand-written, explorable models (not opaque stubs) in `models/`:
- **libc / libstdc++** — `memcpy`, `strcpy`/`strcat`/`strlen`/`strtod`, the `malloc` family, `fread`/`getline`, and more.
- **Linux kernel** — `copy_from_user`, the `kmalloc`/`kvmalloc`/`vmalloc` families, list and filesystem helpers.
- **Wayland** and **QNX resource managers** — optional model sets (`--wayland`, `--qnx`).
- **Struct ranges and interface contracts** — per-struct field constraints and dispatch-slot contracts (`models/structs`, `models/interfaces`).

### Tools
| Tool | Purpose |
|------|---------|
| `hlir-scan` | Discover entries and scan a whole codebase |
| `hlir-taint` | Taint-selective concolic analysis of one entry |
| `hlir-sym` | Symbolic execution with SAT witness and replay |
| `hlir-entry` | Entry spec / seed generation and analysis |
| `hlir-run` | Concrete interpreter |
| `hlir-opt` | IR verifier and coverage reports |
| `hlirgen` | C/C++ source to `core` |
| `hlir-invariant`, `hlir-wp-probe` | Loop-invariant checking and backward weakest-precondition experiments |

## Build and test

Requires a C++20 compiler, CMake >= 3.20, `llvm-18-dev` and `libclang-cpp-dev` (the C/C++ frontend is skipped if libclang is absent), and Python 3.

```sh
cmake -G Ninja -B build && ninja -C build
ctest --test-dir build --output-on-failure
```

Module dependency rules are enforced by `scripts/check_deps.py`, which ctest runs. A sanitizer build is available with `-DHLIR_SANITIZE=ON`.

## Usage

Scan a codebase:

```sh
build/hlir-scan --entries all --include-noarg --format json --output out.json src1.c src2.c ...
build/hlir-scan --link --entries roots --format sarif --output out.sarif src/*.c -- -Iinclude
```

Analyse one entry with a spec:

```sh
build/hlir-taint --spec test/c/entry/len_buf.yaml test/c/entry/memcpy_off_by_one.c --entry copy_len --libc
```

Work at the IR level:

```sh
build/hlir-run test/semantics/control_flow.core --entry fib --arg 15
build/hlir-sym test/symbolic/copy_if_small.core --entry copy_unchecked
build/hlir-sym test/symbolic/libc_user.core --libc --entry overflow
build/hlir-taint --spec test/entry/copy_if_small.yaml test/entry/copy_if_small.core \
    --entry copy_if_small --libc --libc-models --format sarif --output out.sarif
```

Run `build/hlir-scan --help` for the full option list.

## Layout

```
include/hlir/   public headers
lib/            ir, frontend, semantics, smt, entry, scan, link, model, iface, report, driver
tools/          command-line tools
models/         libc / Linux / Wayland / QNX models, struct ranges, interface contracts
scripts/        scan helpers and repository checks
test/           unit, integration and CVE-reproduction tests
```

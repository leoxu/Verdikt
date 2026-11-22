# brotli CVE-2026-111497 — real-source repro asset

Not a routine test fixture. Nothing in `test/c/c_tests.cpp` or `test/c/scan_tests.cpp` discovers or runs
anything in this directory automatically (verified — see "test-suite isolation" below). This is a permanent,
faithfully-copied reproduction of a real brotli CVE that a long investigation (this session, 2026-10-25,
docs/DESIGN.md Sec.22.146 onward, especially Sec.22.288/291/294/296/299-308) used repeatedly. It's saved here
so future work on this CVE — or on the general "HLIR/taint-concolic can't get through a tainted-driven long
loop" class of problem it's the running example for — doesn't need to re-clone brotli and re-derive the
trigger input from scratch.

## What's in this directory

- `vendor/c/dec/brotli_amalgamated.c` — 12 real brotli source files, concatenated **verbatim** (byte-for-byte,
  no edits to brotli's own code) into one translation unit. Source: brotli at commit
  `2e2bcf17ae7115d84ef6588d9a3651cc987d73e7` (https://github.com/google/brotli). The 12 files:
  `c/dec/{bit_reader,decode,huffman,prefix,state,static_init}.c` +
  `c/common/{constants,context,dictionary,platform,shared_dictionary,transform}.c` — this is the exact file
  set this whole investigation used for `--link`/KLEE builds throughout (confirmed sufficient to reach the
  bug; see DESIGN.md Sec.22.288/291/299/301/308 for where this set was established and reused).
- `vendor/c/{dec,common}/*.h`, `vendor/c/include/brotli/*.h` — the real, unmodified brotli headers these 12
  files need, vendored verbatim, preserving brotli's own directory layout (so the 12 files' own `#include`
  lines — a mix of same-directory, `../common/foo.h`-relative, and `<brotli/foo.h>`-angle-bracket forms —
  resolve exactly as they do in a normal brotli build; nothing was rewritten).
- `build_amalgamation.sh` — regenerates everything above from a fresh brotli checkout (or an existing one you
  point it at). Not run automatically by anything; run it by hand if you ever need to re-derive this from a
  newer/different brotli commit. Usage: `./build_amalgamation.sh [path-to-existing-checkout]` (clones fresh if
  no path given).
- `harness.c` — **this project's own code**, not brotli's. Defines `consume(const unsigned char *in, int
  in_len)`, the entry point every HLIR/KLEE experiment in this investigation has driven at: creates a real
  `BrotliDecoderState`, sets the two non-default decoder parameters the bug needs (see below), and calls the
  real `BrotliDecoderDecompressStream`. Also carries the 15-byte trigger constant and an optional native
  verification `main()` (see "fidelity check" below).

## The bug and the trigger input

`DecodeBlockTypeAndLength()` (in the amalgamated file, originally `c/dec/decode.c` ~line 1180-1224) returns
an ambiguous sentinel error value (`BROTLI_DECODER_ERROR_FORMAT_BLOCK_SWITCH`, code **-17**) when
`max_block_type<=1`. Reaching it requires driving a Huffman-decoded block-length counter down to exactly zero
inside `ProcessCommandsInternal`'s literal-copy loop.

**The 15-byte trigger** (hex): `11 59 fe ff ff 03 80 00 08 fc 02 e0 f7 f4 1f` — hand-derived bit-by-bit from
reading brotli's own source (not found by fuzzing or solver search; see docs/DESIGN.md Sec.22.301 for the
full derivation: window_bits, NBLTYPES, degenerate 0-bit-encoded "simple Huffman" trees, and the exact
`cmd_code=504` command whose insert-length extra bits are set so the literal-copy loop's trip count lands
just over 2^24).

**Requires two non-default decoder parameters** — `BROTLI_DECODER_PARAM_LARGE_WINDOW` and
`BROTLI_DECODER_PARAM_DISABLE_RING_BUFFER_REALLOCATION`, both set in `harness.c`'s `consume()`. This is not an
artifact of this harness — docs/DESIGN.md Sec.22.301 proves (reading brotli's source, not guessing) that
**under default parameters this bug is structurally unreachable**: a metablock's declared-length cap and the
insert-length needed to trigger the bug are both exactly 2^24, and that exact-equality gap is always
intercepted by an earlier, independent format check (`FORMAT_BLOCK_LENGTH_1`) unless both these parameters
are set. This is itself a real finding about the CVE's practical severity, not just a test-setup detail.

## Fidelity check

```sh
clang -O0 -g -DBROTLI_CVE_NATIVE_MAIN \
  -I vendor/c/include -I vendor/c/common \
  vendor/c/dec/brotli_amalgamated.c harness.c \
  -o /tmp/brotli_fidelity_check
/tmp/brotli_fidelity_check
```

Expected output (confirmed when this directory was created, 2026-10-25):
```
BrotliDecoderResult = 0
BrotliDecoderErrorCode = -17 (_ERROR_FORMAT_BLOCK_SWITCH)
```
exit code 0. If this ever prints anything else, the amalgamation has drifted from a faithful copy of real
brotli behaviour — do not trust it for anything until that's fixed (regenerate via `build_amalgamation.sh`
and re-check; if it still doesn't reproduce, the brotli commit may have changed the bug's reachability).

## Current status: real native repro confirmed; neither HLIR nor KLEE can find it (as of 2026-10-25)

- **Real brotli decoder**: triggers cleanly (see fidelity check above). This is a real, confirmed bug, not a
  false lead — just one requiring non-default parameters most callers don't set (see above).
- **HLIR**: cannot reach the target branch. Not a search-strategy problem — even with the exact trigger input
  given with zero search needed, the literal-copy loop needs ~16.77 million interpreter steps in one
  continuous trace, and HLIR's taint-concolic engine's work-queue scheduler abandons a path that long before
  completing it, regardless of `--max-steps` (raising the budget 9x gave zero improvement — confirmed, not
  assumed). Full diagnosis chain: docs/DESIGN.md Sec.22.301 (native repro + structural-unreachability proof),
  Sec.22.302 (`--max-steps` doesn't help), Sec.22.303/304 (a much smaller, faster-to-iterate synthetic
  reproduction of the same underlying mechanism — see `test/c/scan/deep_loop_taint_scalar.c` and
  `deep_loop_taint_where.c`), Sec.22.305 (a candidate fix attempt that caused real regressions, reverted),
  Sec.22.306 (an independent-tool comparison: KLEE gets a real advantage on the *synthetic* case when a value
  is pinned by an equality constraint, because KLEE's expression layer folds it to a literal), Sec.22.307 (the
  resulting HLIR fix — real, verified, no regressions, but scoped to top-level scalar params pinned via
  `taint:value,range:[N,N]`; confirmed NOT to help this brotli case, where the loop-driving value is computed
  during execution via Huffman decode, not a directly-pinned parameter).
- **KLEE** (an independent, mature, long-established symbolic execution tool — not an HLIR-specific limit):
  also cannot reach the target branch, confirmed directly on this exact amalgamated source + exact 15-byte
  trigger (docs/DESIGN.md Sec.22.308). The reason is NOT the same as HLIR's (ruling out "well of course no
  tool can do this" as too easy an explanation) — KLEE's own diagnostics point to the cost of symbolic access
  into brotli's internal ~32MB ring buffer (needed for the two non-default parameters above), independent of
  solver-query count or search strategy. This is a newly-identified fourth potential bottleneck dimension,
  on top of the three already identified from HLIR-only investigation (solver query cost, taint-concolic
  bookkeeping complexity, work-queue scheduling) — see `docs/KNOWN_GAPS_PRIORITIZED.md`'s "污染驱动的深层循环"
  entry for the consolidated picture across all of these.

If you're picking this up later: read docs/DESIGN.md Sec.22.301 through the latest section referencing
"brotli" before assuming any of the above is stale or re-deriving any of it from scratch — this file is a
pointer into that history, not a replacement for it.

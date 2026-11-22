# brotli CVE-2026-111497 — the TRUE pre-fix vulnerable version

**This directory corrects a major mistake documented in `docs/DESIGN.md` Sec.22.311-22.314.** The sibling
directory `test/c/cve_repro/brotli_cve_2026_111497/` (note: no `_prefix` suffix) was built from commit
`2e2bcf17ae7115d84ef6588d9a3651cc987d73e7`, which — confirmed via `git merge-base --is-ancestor` against the
real brotli history — is a **descendant of the fix commit**, not the vulnerable version. That directory is
kept (not deleted) because it still correctly documents the *fixed* code's behavior, but it is NOT a CVE
repro. **This directory is the real one.**

## Source

- Repo: https://github.com/google/brotli
- Vulnerable commit: `34f020fa9daba975747b29885314c2545b7aa040` (2026-02-26) — the immediate parent of the
  fix commit `0ed4268a4401abcb4472096340477cf4af7d1a2b` ("Detect and report invalid stream earlier.",
  2026-02-27).
- `vendor/c/dec/brotli_amalgamated.c`: literal concatenation (via a Python script run once, not committed —
  see `build_amalgamation.sh` for the file list) of the real, unmodified `c/dec/{bit_reader,decode,huffman,
  prefix,state,static_init}.c` + `c/common/{constants,context,dictionary,platform,shared_dictionary,
  transform}.c` at that commit. No brotli logic was edited, only mechanically concatenated.

## The real bug (confirmed by source reading + a live gdb backtrace, not guessed)

In this version, `DecodeLiteralBlockSwitchInternal` is:
```c
static BROTLI_INLINE BROTLI_BOOL DecodeLiteralBlockSwitchInternal(
    int safe, BrotliDecoderState* s) {
  if (!DecodeBlockTypeAndLength(safe, s, 0)) {
    return BROTLI_FALSE;
  }
  PrepareLiteralDecoding(s);
  return BROTLI_TRUE;
}
static void BROTLI_NOINLINE DecodeLiteralBlockSwitch(BrotliDecoderState* s) {
  DecodeLiteralBlockSwitchInternal(0, s);   /* <-- return value discarded */
}
```
`PrepareLiteralDecoding` (which sets `s->literal_htree`/`s->context_map_slice`/`s->context_lookup`/
`s->trivial_literal_context`) is only called on the success path. `DecodeLiteralBlockSwitch` is `void` and
throws away `DecodeLiteralBlockSwitchInternal`'s `BROTLI_BOOL` result entirely. At the call site
(`ProcessCommandsInternal`'s `NextLiteralBlock:` label):
```c
NextLiteralBlock:
  BROTLI_SAFE(DecodeLiteralBlockSwitch(s));   /* unsafe-mode: bare call, no check at all */
  goto CommandInner;
```
So when `s->num_block_types[0] <= 1` (the same condition the already-fixed sibling CVE directory chases —
`DecodeBlockTypeAndLength` returns `BROTLI_FALSE` for this case before this commit's fix gave it a proper
multi-valued `BrotliDecoderErrorCode`), execution unconditionally falls through to `CommandInner` and starts
decoding literal bytes through `PreloadSymbol(safe, s->literal_htree, ...)` using whatever `s->literal_htree`
was left over — **never actually set for this block**, since `PrepareLiteralDecoding` was skipped.

This was confirmed live: with the decoder spinning (see "Reproducing" below), attaching gdb and interrupting
it lands reliably at:
```
#0  PreloadSymbol (safe=0, table=0x..., br=0x..., bits=..., value=...) at decode.c:447
#1  ProcessCommandsInternal (safe=0, s=0x...) at decode.c:2014
#2  ProcessCommands (s=0x...) at decode.c:2346
#3  BrotliDecoderDecompressStream (...) at decode.c:2788
```
`table` is a non-null-looking pointer — i.e. a **stale/never-initialized Huffman table pointer** being used
to decode literal symbols, exactly the scenario the source reading predicted. In this specific construction
it manifests as a **hang** (the fast literal-decode hot loop never terminates when fed a bogus table) rather
than a crash — still a real, serious bug (CWE-835, unbounded CPU consumption / denial of service), consistent
with the fix commit's own title, "Detect and report invalid stream earlier": the old behavior detected the
problem too late (or not cleanly), the fix makes every caller check the result and abort immediately instead.

**Differential confirmation**: the exact same 55-byte input (see below) run against the already-fixed sibling
directory's amalgamation completes in ~0.1s with `error_code=-17` (clean, expected error). Run against this
(true vulnerable) source, it hangs indefinitely (not killed by a timeout even after 2+ minutes in earlier
testing during this investigation).

## The trigger: 55 bytes (15-byte payload + 40 bytes of padding)

```
11 59 fe ff ff 03 80 00 08 fc 02 e0 f7 f4 1f
00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00 00 00
```
The first 15 bytes are unchanged from `docs/DESIGN.md` Sec.22.301's construction for the (already-fixed)
sibling directory (same technique: a single command whose insert length deliberately exceeds the metablock's
declared length, driving `block_length[0]` to exactly 0 inside that one command's insert loop, with
`num_block_types[0]` declared as 1 so the block-switch lookup hits the `max_block_type<=1` sentinel).

**Why the extra 40 bytes of padding are needed** (this is the piece that took three background-task rounds of
blind trial to not find, and was instead found in a few minutes by reading `c/dec/bit_reader.h` directly):
`BrotliCheckInputAmount` gates brotli's fast/"unsafe" decode path:
```c
#define BROTLI_FAST_INPUT_SLACK 28
/* in BrotliBitReaderSetInput: */
if (avail_in + 1 > BROTLI_FAST_INPUT_SLACK) {
  br->guard_in = next_in + (avail_in + 1 - BROTLI_FAST_INPUT_SLACK);
} else {
  br->guard_in = next_in;              /* i.e. the fast path is immediately disallowed */
}
/* BrotliCheckInputAmount: */
return br->next_in < br->guard_in;
```
With only the 15-byte payload (or even 15+16=31 bytes, which earlier investigation rounds tried), `avail_in`
is too small for `guard_in` to end up meaningfully past the header-parsing region, so `BrotliCheckInputAmount`
goes false well before reaching the one command we need processed in "unsafe" (fast, unchecked) mode — the
decoder instead falls back to its "safe" (byte-at-a-time, fully-checked) path, which returns
`BROTLI_DECODER_NEEDS_MORE_INPUT`, triggering an unrelated proactive `WriteRingBuffer` call at the top of the
main state-machine loop that itself fails on `meta_block_remaining_len < 0` (a value our construction
deliberately produces as part of the insert-length-overflow technique) with error `-9`
(`BROTLI_DECODER_ERROR_FORMAT_BLOCK_LENGTH_1`) — masking the real bug entirely. Padding to 55 bytes total
(`avail_in=55`, `guard_in = next_in + (56-28) = next_in+28`) keeps `BrotliCheckInputAmount` true long enough
for the fast/unsafe path to carry the one command all the way through its insert loop, reaching
`NextLiteralBlock` without the `-9` detour. (40 was found to work empirically once the right mechanism was
identified; the exact minimum padding was not separately minimized — 40 is known-good, not necessarily
tight.)

## Reproducing

```sh
clang -O0 -g -DBROTLI_CVE_NATIVE_MAIN \
  -Ivendor/c/include -Ivendor/c/common -Ivendor/c/dec \
  vendor/c/dec/brotli_amalgamated.c harness.c -o /tmp/probe
timeout 20 /tmp/probe   # expected: hangs, "starting..." printed, no further output, killed by timeout
```
For comparison, run the identical 55-byte input against the fixed sibling directory's amalgamation (adjust
the harness there to use this same 55-byte array) to see it return `error_code=-17` in well under a second.

## Status / what's NOT done yet

- **No crash confirmed, only a hang** (CWE-835-class DoS, not a memory-corruption CWE). Whether a different
  construction (e.g. one that gets further into actually decoding a corrupted-but-non-null-looking Huffman
  table rather than one that spins) could also produce an ASan-reported memory-safety crash was not
  investigated further — this hang is itself already a confirmed, real, serious bug.
- **HLIR detection not yet (fully) attempted** against this corrected vulnerable source — see
  `docs/DESIGN.md` Sec.22.314 for whatever was or wasn't tried in the round that produced this directory.
- The exact minimum padding (somewhere between 32 and 40 bytes) was not pinned down precisely; 40 is
  known-good, used as-is.

## Relationship to the other `brotli_cve_*` directories

- `test/c/cve_repro/brotli_cve_2026_111497/` (no suffix): the already-FIXED version, kept as reference
  material for "what the patched code looks like", NOT a vulnerability repro (see its own README and
  `docs/DESIGN.md` Sec.22.311 for the full correction story). Do not confuse the two.

# LLM-assisted witness distillation — measured, 2026-11-20

When backward WP proves a site is **reachable-but-unprovable-safe** (a `sat` candidate) but the triggering
input is hard to construct by fuzzing, this loop finds the witness: instead of asking an LLM to guess the
input, the **LLM distills the relevant code (including a symbolic loop) into a small self-contained function
`f(unknowns)` with a target `f == value`**, a solver inverts the small problem instantly, and the candidate
is adjudicated on the real binary under a sanitizer.

## The loop (four steps, all run here)

| step | tool | result on this target |
|---|---|---|
| 1. backward WP points at the site | `hlir-wp-probe --list --solve` | `check.oob @parse buf[200] sat(candidate)`; obligation = reach the gate `(a^b)==MAGIC` |
| 2. LLM distills the loop into SMT | `solve.py` (`hz`) | translated the mixing loop to Z3; **cross-check vs real C semantics (`hpy`) = True** |
| 3. solver inverts | Z3 | found a **genuine preimage** `0c c4 97 24 e8 d5` (≠ the input that defined the target); and proved an arbitrary target `0x0BADF00D` **unsat** (the gate is dead) |
| 4. verify on the real binary | `verify.c` + UBSan | `runtime error: index 200 out of bounds for type 'char [16]'` |

## Reproduce

```sh
# 1. backward WP obligation
hlir-scan --link --dump-linked /tmp/t.core --entry harness target.c
hlir-wp-probe --list --solve /tmp/t.core | grep buf   # -> buf[200] sat(candidate)

# 2+3. distill + solve  (needs z3-solver)
python3 solve.py
#   model-vs-C cross-check: True ...
#   WITNESS bytes: 0c c4 97 24 e8 d5
#   arbitrary target 0x0BADF00D reachable? False  (unsat => the gate is proven dead)

# 4. verify
gcc -fsanitize=address,undefined -fno-sanitize-recover=all -g verify.c -o /tmp/verify && /tmp/verify
#   verify.c:...: runtime error: index 200 out of bounds for type 'char [16]'
```

## What this measured (honest)

- **Solving is not the bottleneck.** After distillation the cone is tiny (6 bytes, an unrolled loop) and Z3
  inverts it instantly — the same principle as backward WP's `|S|=1` slice: *LLM distillation shrinks the cone
  the solver cannot handle.* A 2^-32 magic gate, infeasible for fuzzing, is trivial once distilled.
- **The bottleneck is distillation faithfulness**, and its difficulty scales with how stateful / encoded /
  malformed the code is:

  | dimension | this target (medium) | brotli CVE-2026-111497 (hard) |
  |---|---|---|
  | scope | one self-contained function | multi-function state machine |
  | input → loop variables | direct byte reads | through bitstream **decoding** |
  | trip count | fixed 6, unrollable | 2^24 regime |
  | target state | ordinary value, has a preimage | a **malformed** state no encoder emits |

- **The cross-check is the safety net.** A mistranslated model returns a false `unsat` / a false witness
  silently; running the real C concretely and asserting the model agrees is what keeps it honest. This mirrors
  the discipline that the model is never trusted — the real execution adjudicates (cf.
  `docs/HYBRID_FUZZING_DESIGN.md` §3.1).
- **Direction matters.** This is sound *as a method* only for the **witness / confirmation (under-approx)**
  direction, because a witness self-validates. It must **never** be used for safety proofs (over-approx):
  an unfaithful abstraction there would assert a false "safe" that nothing self-validates.
- **Bonus:** the `unsat` answer is useful too — the solver *proved the gate unreachable* for the arbitrary
  magic (conditional on this trip count), which neither fuzzing nor backward WP alone can conclude.

## The hard boundary — why the same loop fails on brotli CVE-2026-111497 (investigated 2026-11-20)

We then ran the same flow on the real brotli vuln decoder (`0ed4268a^`). Step 1 (backward WP) works: the
tail-copy write `s->buffer.u8[s->buffer_length++]` is flagged `sat` with `|S|=1`. Step 2 (distill) STALLS,
and the reason is now precise — not merely "it's big."

The sink distills to ~12 lines (`while (available_in) buffer.u8[len++]=...` → OOB when `available_in > 8`).
What does **not** distill is the *obligation to reach it*: `DecodeBlockTypeAndLength` must run with
`num_block_types[t] <= 1` at a point where a block switch is requested (`block_length[t] == 0`). Enumerating
**every** write to the two fields in `c/dec/` and tracing the switch-trigger order gives an invariant:

- `num_block_types[t]` is only set in the header (`DecodeVarLenUint8()+1 ∈ [1,256]`) or reset to 1 in
  `MetablockBegin`; it never drops from ≥2 to ≤1 inside a metablock.
- `block_length[t]` is read *small* only at three sites, all guarded by `num_block_types[t] >= 2`; otherwise
  it is `BROTLI_BLOCK_SIZE_CAP = 2^24` and decremented per symbol.
- the switch fires only when `block_length[t] == 0` **with another symbol pending** (checked at the top of the
  decode loop, before the decrement).

So `num_block_types[t] == 1  ⟹  block_length[t] == 2^24`, and a metablock has `≤ MLEN ≤ 2^24 == CAP` symbols.
The counter decrements to 0 only on the last symbol, when the metablock ends and no symbol is pending — the
disagreement is off by exactly one at the `CAP == MLEN_max` boundary. **Through the directly traceable
input→state flow, the triggering state is unreachable; every enumerable write maintains the invariant that
forbids it.**

That is the structural reason the method cannot reach it: **distillation (and backward slicing) can only
reduce "reach state S" when S is a traceable function of the input bytes. Here the triggering state is kept
*invariant* by all traceable writes, so the path that violates it is non-local / emergent** — a different
state field corrupting the count, a ringbuffer/pos boundary, a specific multi-metablock sequence. It does not
live in any flow a mechanical slice/distill can follow. This is corroborated: our own report calls it an open
question, a directed fuzzer with a trap on the exact condition missed it in 473,300 runs (random mutation
walks the direct flow, where the state does not exist), and the tool that found it (OpenAI Codex Security)
reasoned about the whole state machine rather than slicing from the sink.

Net: **backward WP points at the sink (`sat`), but no automatic dimensionality reduction reaches it — not
because solving is hard, but because the relevant state is not a traceable function of the input.** That is
the far edge of the gradient (scope + encoding + trip-count + malformed target, all adversarial at once).

## Caveat

`target.c` / `verify.c` are hand-written — a controlled stand-in for "a real symbolic loop", so the
*analyze-unfamiliar-code* part is simulated. What is genuine: the faithful translation + cross-check, the
real inversion, and the sanitizer confirmation. The brotli boundary analysis above is on the real decoder.
Related: `docs/BACKWARD_WP_DESIGN.md`, `docs/HYBRID_FUZZING_DESIGN.md`,
(report not included in this repo).

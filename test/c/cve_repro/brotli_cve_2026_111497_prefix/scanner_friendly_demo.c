// Scanner-friendly variant of minimal_bug_demo.c: same real-world mechanism (DecodeBlockTypeAndLength-style
// failure + a void wrapper that discards it), but reshaped so hlir-scan's taint-concolic engine has an actual
// attacker-controlled parameter to drive, and the two consequences are real HLIR-detectable outcomes instead
// of safely-capped/in-bounds demo prints:
//   (a) a genuine null_deref (the stale-pointer family, made concrete: htree starts NULL, like a freshly
//       created BrotliDecoderState really does, instead of "stale-but-still-valid" -- NULL is the simplest
//       faithful case HLIR's UB checks can actually flag).
//   (b) a genuine unbounded loop (the CWE-835 family, left uncapped like the real bug -- do not run this
//       natively without an external timeout).
// See minimal_bug_demo.c and docs/DESIGN.md Sec.22.311/314/322/323 for the full derivation/background.

#include <stdbool.h>

typedef struct {
    int num_block_types;
    int block_length;
    int *htree;
} decode_state;

static bool decode_block_type_and_length(decode_state *s) {
    if (s->num_block_types <= 1) {
        return false;
    }
    s->block_length = 16;
    static int real_table[4] = {1, 2, 3, 4};
    s->htree = real_table;
    return true;
}

static bool decode_block_switch_internal(decode_state *s) {
    if (!decode_block_type_and_length(s)) return false;
    return true;
}

// PRE-FIX: the real bug -- void wrapper, discards the result.
static void decode_block_switch_PRE_FIX(decode_state *s) {
    decode_block_switch_internal(s);
}

// POST-FIX: propagates the real result.
static bool decode_block_switch_POST_FIX(decode_state *s) {
    return decode_block_switch_internal(s);
}

// (a) null_deref entry: num_block_types is the attacker-controlled parameter (mirrors the real stream's
// declared NBLTYPES field). htree is constructed NULL (mirrors a freshly created BrotliDecoderState, not a
// "stale, happens to be valid" pointer -- NULL is the faithful case for a single, first, isolated call,
// which is exactly what a standalone taint-concolic entry synthesizes). When num_block_types <= 1, the
// failing switch leaves htree NULL and the discarded-return-value bug lets execution fall straight through
// to the dereference below.
int demo_null_deref_entry(int num_block_types) {
    decode_state s = { .num_block_types = num_block_types, .block_length = 0, .htree = 0 };
    if (s.block_length == 0) {
        decode_block_switch_PRE_FIX(&s);
    }
    return s.htree[0];
}

// Same shape, but using the POST-FIX wrapper: expected to be safe (failure is detected and reported, the
// dereference never happens on that path) -- a negative control to confirm the fix actually closes this.
int demo_null_deref_entry_POST_FIX(int num_block_types) {
    decode_state s = { .num_block_types = num_block_types, .block_length = 0, .htree = 0 };
    if (s.block_length == 0) {
        if (!decode_block_switch_POST_FIX(&s)) {
            return -1;
        }
    }
    return s.htree[0];
}

// (b) unbounded-loop entry: mirrors the real `CommandBegin:` label's
// `if (block_length[1]==0) { BROTLI_SAFE(DecodeCommandBlockSwitch(s)); goto CommandBegin; }` exactly, with
// no safety cap. DO NOT run this natively without an external timeout -- when num_block_types<=1 this is a
// genuine infinite loop (block_length is never advanced off 0 by the failing path), same as the real bug.
int demo_infinite_loop_entry(int num_block_types) {
    decode_state s = { .num_block_types = num_block_types, .block_length = 0, .htree = 0 };
    int iterations = 0;
    while (s.block_length == 0) {
        decode_block_switch_PRE_FIX(&s);
        iterations++;
    }
    return iterations;
}

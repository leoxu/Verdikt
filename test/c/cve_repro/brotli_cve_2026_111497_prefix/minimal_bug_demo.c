// Minimal, self-contained demonstration of the real root-cause pattern behind CVE-2026-111497, distilled
// from reading the real brotli source (vendor/c/dec/brotli_amalgamated.c in this directory) and cross-checked
// against the real upstream fix commit 0ed4268a4401abcb4472096340477cf4af7d1a2b ("Detect and report invalid
// stream earlier.", see docs/DESIGN.md Sec.22.311/314/322/323 in the parent HLIR project for the full
// derivation). This file is NOT part of brotli and does not link against it -- it is a standalone, much
// smaller program that reproduces the exact *shape* of the bug with the real field/function names simplified.
//
// The real shape (three instances in brotli, all fixed by the same commit):
//   DecodeBlockTypeAndLength()        -- returns success/failure. Pre-fix: BROTLI_BOOL. Fails (does nothing
//                                         to block_length/htree) when num_block_types <= 1 for this stream.
//   DecodeXxxBlockSwitchInternal()    -- calls the above; on failure, returns without doing its own setup
//                                         either (skips preparing the huffman table / context pointers).
//   DecodeXxxBlockSwitch()            -- PRE-FIX: declared `void`, calls Internal() and discards the result.
//                                         POST-FIX: returns the real error code so the caller can react.
//   caller (ProcessCommandsInternal)  -- PRE-FIX: `BROTLI_SAFE(DecodeXxxBlockSwitch(s))` is a bare call in
//                                         the fast/unsafe decode path -- no check at all, proceeds as if
//                                         setup had succeeded.
//
// Two distinct real-world consequences from the exact same pattern (both present in the real decoder, see
// docs/DESIGN.md Sec.22.322 for the full analysis of which brotli function hits which):
//   (a) CWE-835 infinite loop: the caller's "is a switch due?" check (`block_length == 0`) re-fires forever,
//       because the failure path never advanced block_length away from 0.
//   (b) stale-pointer use: the caller doesn't loop back, it falls straight through and uses a table/context
//       pointer that this call was supposed to (but didn't) set up -- in the real decoder this pointer is
//       *stale* (left over from a previous, unrelated, successful block), not NULL, so it doesn't fail
//       loudly; it silently decodes using the wrong table.
//
// Build & run: `cc -O0 -g minimal_bug_demo.c -o demo && ./demo`

#include <stdio.h>
#include <stdbool.h>

typedef struct {
    int num_block_types;  // from the stream header; <=1 means "this dimension never switches block type"
    int block_length;     // items left before the next switch is due; 0 means "due now"
    int *htree;           // stand-in for a real huffman table / context pointer
} decode_state;

// ---- shared "real" logic (unchanged by the fix) ----

// Mirrors DecodeBlockTypeAndLength(): fails without touching block_length/htree when num_block_types<=1.
// (Real source: brotli_amalgamated.c:1265, `if (max_block_type <= 1) { return BROTLI_FALSE; }` is the
// first line of the function body -- nothing below it ever runs on this path.)
static bool decode_block_type_and_length(decode_state *s) {
    if (s->num_block_types <= 1) {
        return false;
    }
    s->block_length = 16;          // a real decoder would read a fresh length from the stream here
    static int real_table[4] = {1, 2, 3, 4};
    s->htree = real_table;         // a real decoder would build/select the real huffman table here
    return true;
}

// Mirrors DecodeXxxBlockSwitchInternal(): propagates failure, does no further setup on that path.
static bool decode_block_switch_internal(decode_state *s) {
    if (!decode_block_type_and_length(s)) return false;
    return true;
}

// ---- PRE-FIX: void wrapper, discards the result (the real bug, all three brotli instances) ----
static void decode_block_switch_PRE_FIX(decode_state *s) {
    decode_block_switch_internal(s);   // <-- return value silently discarded, exactly like the real
                                        //     `static void DecodeLiteralBlockSwitch/DecodeCommandBlockSwitch/
                                        //     DecodeDistanceBlockSwitch` before the fix
}

// ---- POST-FIX: propagates the real result (matches the real patch's BROTLI_SAFE_WITH_STATUS behaviour) ----
static bool decode_block_switch_POST_FIX(decode_state *s) {
    return decode_block_switch_internal(s);
}

// (a) CWE-835 demo: mirrors ProcessCommandsInternal's `CommandBegin:` label --
//     `if (block_length[1] == 0) { BROTLI_SAFE(DecodeCommandBlockSwitch(s)); goto CommandBegin; }`
static void demo_infinite_loop_case(void) {
    printf("== (a) infinite-loop case (mirrors the real Command block-switch site) ==\n");
    decode_state s = { .num_block_types = 1, .block_length = 0, .htree = NULL };
    int iterations = 0;
    const int safety_cap = 5;  // the real bug has no such cap -- this would spin forever
    while (s.block_length == 0) {
        decode_block_switch_PRE_FIX(&s);   // fails every time; block_length is NEVER advanced off 0
        iterations++;
        if (iterations >= safety_cap) {
            printf("  ... stopped after %d iterations for this demo's sake.\n"
                   "  block_length is STILL %d -- nothing in the failure path ever changes it,\n"
                   "  so the real code's `goto CommandBegin;` here would never terminate.\n",
                   iterations, s.block_length);
            break;
        }
    }
    printf("\n");
}

// (b) stale-pointer demo: mirrors `CommandPostDecodeLiterals:` -- no loop-back, straight fall-through
//     into code that uses the table/context pointer this call was supposed to set up.
static void demo_stale_pointer_case(void) {
    printf("== (b) stale-pointer case (mirrors the real Distance/Literal block-switch sites) ==\n");
    // Set up a decoder that has ALREADY successfully decoded one real block (so htree points to real,
    // now-stale data), then hits a block type that triggers the bug.
    decode_state s = { .num_block_types = 2, .block_length = 0, .htree = NULL };
    decode_block_type_and_length(&s);                 // succeeds: htree now points at real_table (stale-to-be)
    printf("  after a real, successful block: htree=%p -> htree[0]=%d\n", (void *)s.htree, s.htree[0]);

    s.num_block_types = 1;  // next meta-block declares "only 1 block type" -- the vulnerable condition
    s.block_length = 0;     // due for a switch again
    decode_block_switch_PRE_FIX(&s);                  // fails silently; htree is left exactly as it was

    printf("  after the FAILED switch (result discarded): htree=%p (unchanged -- STALE, not NULL)\n",
           (void *)s.htree);
    printf("  the real decoder now proceeds to decode symbols through this stale table as if it were\n"
           "  valid for the new block -- htree[0]=%d is read and used, even though nothing set this table\n"
           "  up for the block we are actually in now.\n", s.htree[0]);
    printf("\n");
}

static void demo_post_fix(void) {
    printf("== post-fix behaviour (matches the real BROTLI_SAFE_WITH_STATUS) ==\n");
    decode_state s = { .num_block_types = 1, .block_length = 0, .htree = NULL };
    if (s.block_length == 0) {
        if (!decode_block_switch_POST_FIX(&s)) {
            printf("  failure detected and reported immediately -- no loop, no stale-pointer use.\n"
                   "  this is exactly what the real fix commit's title promises: \"Detect and report\n"
                   "  invalid stream earlier.\"\n");
            return;
        }
    }
    printf("  (would have proceeded normally)\n");
}

int main(void) {
    demo_infinite_loop_case();
    demo_stale_pointer_case();
    demo_post_fix();
    return 0;
}

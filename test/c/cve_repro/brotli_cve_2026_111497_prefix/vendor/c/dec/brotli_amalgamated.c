/* Amalgamated (literal concatenation, no edits) brotli decoder source for the TRUE pre-fix
 * vulnerable commit 34f020fa9daba975747b29885314c2545b7aa040 (parent of the fix commit
 * 0ed4268a4401abcb4472096340477cf4af7d1a2b, "Detect and report invalid stream earlier.").
 * See README.md in this directory. Files concatenated (in order): 
 * c/dec/{bit_reader,decode,huffman,prefix,state,static_init}.c, c/common/{constants,context,dictionary,platform,shared_dictionary,transform}.c */

/* ---- vendor/c/dec/bit_reader.c ---- */
/* Copyright 2013 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

/* Bit reading helpers */

#include "bit_reader.h"

#include "../common/platform.h"

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

const BROTLI_MODEL("small")
brotli_reg_t kBrotliBitMask[33] = {     0x00000000,
    0x00000001, 0x00000003, 0x00000007, 0x0000000F,
    0x0000001F, 0x0000003F, 0x0000007F, 0x000000FF,
    0x000001FF, 0x000003FF, 0x000007FF, 0x00000FFF,
    0x00001FFF, 0x00003FFF, 0x00007FFF, 0x0000FFFF,
    0x0001FFFF, 0x0003FFFF, 0x0007FFFF, 0x000FFFFF,
    0x001FFFFF, 0x003FFFFF, 0x007FFFFF, 0x00FFFFFF,
    0x01FFFFFF, 0x03FFFFFF, 0x07FFFFFF, 0x0FFFFFFF,
    0x1FFFFFFF, 0x3FFFFFFF, 0x7FFFFFFF, 0xFFFFFFFF
};

void BrotliInitBitReader(BrotliBitReader* br) {
  br->val_ = 0;
  br->bit_pos_ = 0;
}

BROTLI_BOOL BrotliWarmupBitReader(BrotliBitReader* br) {
  size_t aligned_read_mask = (sizeof(br->val_) >> 1) - 1;
  /* Fixing alignment after unaligned BrotliFillWindow would result accumulator
     overflow. If unalignment is caused by BrotliSafeReadBits, then there is
     enough space in accumulator to fix alignment. */
  if (BROTLI_UNALIGNED_READ_FAST) {
    aligned_read_mask = 0;
  }
  if (BrotliGetAvailableBits(br) == 0) {
    br->val_ = 0;
    if (!BrotliPullByte(br)) {
      return BROTLI_FALSE;
    }
  }

  while ((((size_t)br->next_in) & aligned_read_mask) != 0) {
    if (!BrotliPullByte(br)) {
      /* If we consumed all the input, we don't care about the alignment. */
      return BROTLI_TRUE;
    }
  }
  return BROTLI_TRUE;
}

BROTLI_BOOL BrotliSafeReadBits32Slow(BrotliBitReader* br,
    brotli_reg_t n_bits, brotli_reg_t* val) {
  brotli_reg_t low_val;
  brotli_reg_t high_val;
  BrotliBitReaderState memento;
  BROTLI_DCHECK(n_bits <= 32);
  BROTLI_DCHECK(n_bits > 24);
  BrotliBitReaderSaveState(br, &memento);
  if (!BrotliSafeReadBits(br, 16, &low_val) ||
      !BrotliSafeReadBits(br, n_bits - 16, &high_val)) {
    BrotliBitReaderRestoreState(br, &memento);
    return BROTLI_FALSE;
  }
  *val = low_val | (high_val << 16);
  return BROTLI_TRUE;
}

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/dec/decode.c ---- */
/* Copyright 2013 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include <brotli/decode.h>

#include "../common/constants.h"
#include "../common/context.h"
#include "../common/dictionary.h"
#include "../common/platform.h"
#include "../common/shared_dictionary_internal.h"
#include "../common/transform.h"
#include "../common/version.h"
#include "bit_reader.h"
#include "huffman.h"
#include "prefix.h"
#include "state.h"
#include "static_init.h"

#if defined(BROTLI_TARGET_NEON)
#include <arm_neon.h>
#endif

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

#define BROTLI_FAILURE(CODE) (BROTLI_DUMP(), CODE)

#define BROTLI_LOG_UINT(name)                                       \
  BROTLI_LOG(("[%s] %s = %lu\n", __func__, #name, (unsigned long)(name)))
#define BROTLI_LOG_ARRAY_INDEX(array_name, idx)                     \
  BROTLI_LOG(("[%s] %s[%lu] = %lu\n", __func__, #array_name,        \
         (unsigned long)(idx), (unsigned long)array_name[idx]))

#define HUFFMAN_TABLE_BITS 8U
#define HUFFMAN_TABLE_MASK 0xFF

/* We need the slack region for the following reasons:
    - doing up to two 16-byte copies for fast backward copying
    - inserting transformed dictionary word:
        255 prefix + 32 base + 255 suffix */
static const brotli_reg_t kRingBufferWriteAheadSlack = 542;

static const BROTLI_MODEL("small")
uint8_t kCodeLengthCodeOrder[BROTLI_CODE_LENGTH_CODES] = {
  1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15,
};

/* Static prefix code for the complex code length code lengths. */
static const BROTLI_MODEL("small")
uint8_t kCodeLengthPrefixLength[16] = {
  2, 2, 2, 3, 2, 2, 2, 4, 2, 2, 2, 3, 2, 2, 2, 4,
};

static const BROTLI_MODEL("small")
uint8_t kCodeLengthPrefixValue[16] = {
  0, 4, 3, 2, 0, 4, 3, 1, 0, 4, 3, 2, 0, 4, 3, 5,
};

BROTLI_BOOL BrotliDecoderSetParameter(
    BrotliDecoderState* state, BrotliDecoderParameter p, uint32_t value) {
  if (state->state != BROTLI_STATE_UNINITED) return BROTLI_FALSE;
  switch (p) {
    case BROTLI_DECODER_PARAM_DISABLE_RING_BUFFER_REALLOCATION:
      state->canny_ringbuffer_allocation = !!value ? 0 : 1;
      return BROTLI_TRUE;

    case BROTLI_DECODER_PARAM_LARGE_WINDOW:
      state->large_window = TO_BROTLI_BOOL(!!value);
      return BROTLI_TRUE;

    default: return BROTLI_FALSE;
  }
}

BrotliDecoderState* BrotliDecoderCreateInstance(
    brotli_alloc_func alloc_func, brotli_free_func free_func, void* opaque) {
  BrotliDecoderState* state = 0;
  if (!BrotliDecoderEnsureStaticInit()) {
    BROTLI_DUMP();
    return 0;
  }
  if (!alloc_func && !free_func) {
    state = (BrotliDecoderState*)malloc(sizeof(BrotliDecoderState));
  } else if (alloc_func && free_func) {
    state = (BrotliDecoderState*)alloc_func(opaque, sizeof(BrotliDecoderState));
  }
  if (state == 0) {
    BROTLI_DUMP();
    return 0;
  }
  if (!BrotliDecoderStateInit(state, alloc_func, free_func, opaque)) {
    BROTLI_DUMP();
    if (!alloc_func && !free_func) {
      free(state);
    } else if (alloc_func && free_func) {
      free_func(opaque, state);
    }
    return 0;
  }
  return state;
}

/* Deinitializes and frees BrotliDecoderState instance. */
void BrotliDecoderDestroyInstance(BrotliDecoderState* state) {
  if (!state) {
    return;
  } else {
    brotli_free_func free_func = state->free_func;
    void* opaque = state->memory_manager_opaque;
    BrotliDecoderStateCleanup(state);
    free_func(opaque, state);
  }
}

/* Saves error code and converts it to BrotliDecoderResult. */
static BROTLI_NOINLINE BrotliDecoderResult SaveErrorCode(
    BrotliDecoderState* s, BrotliDecoderErrorCode e, size_t consumed_input) {
  s->error_code = (int)e;
  s->used_input += consumed_input;
  if ((s->buffer_length != 0) && (s->br.next_in == s->br.last_in)) {
    /* If internal buffer is depleted at last, reset it. */
    s->buffer_length = 0;
  }
  switch (e) {
    case BROTLI_DECODER_SUCCESS:
      return BROTLI_DECODER_RESULT_SUCCESS;

    case BROTLI_DECODER_NEEDS_MORE_INPUT:
      return BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT;

    case BROTLI_DECODER_NEEDS_MORE_OUTPUT:
      return BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT;

    default:
      return BROTLI_DECODER_RESULT_ERROR;
  }
}

/* Decodes WBITS by reading 1 - 7 bits, or 0x11 for "Large Window Brotli".
   Precondition: bit-reader accumulator has at least 8 bits. */
static BrotliDecoderErrorCode DecodeWindowBits(BrotliDecoderState* s,
                                               BrotliBitReader* br) {
  brotli_reg_t n;
  BROTLI_BOOL large_window = s->large_window;
  s->large_window = BROTLI_FALSE;
  BrotliTakeBits(br, 1, &n);
  if (n == 0) {
    s->window_bits = 16;
    return BROTLI_DECODER_SUCCESS;
  }
  BrotliTakeBits(br, 3, &n);
  if (n != 0) {
    s->window_bits = (17u + n) & 63u;
    return BROTLI_DECODER_SUCCESS;
  }
  BrotliTakeBits(br, 3, &n);
  if (n == 1) {
    if (large_window) {
      BrotliTakeBits(br, 1, &n);
      if (n == 1) {
        return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_WINDOW_BITS);
      }
      s->large_window = BROTLI_TRUE;
      return BROTLI_DECODER_SUCCESS;
    } else {
      return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_WINDOW_BITS);
    }
  }
  if (n != 0) {
    s->window_bits = (8u + n) & 63u;
    return BROTLI_DECODER_SUCCESS;
  }
  s->window_bits = 17;
  return BROTLI_DECODER_SUCCESS;
}

static BROTLI_INLINE void memmove16(uint8_t* dst, uint8_t* src) {
#if defined(BROTLI_TARGET_NEON)
  vst1q_u8(dst, vld1q_u8(src));
#else
  uint32_t buffer[4];
  memcpy(buffer, src, 16);
  memcpy(dst, buffer, 16);
#endif
}

/* Decodes a number in the range [0..255], by reading 1 - 11 bits. */
static BROTLI_NOINLINE BrotliDecoderErrorCode DecodeVarLenUint8(
    BrotliDecoderState* s, BrotliBitReader* br, brotli_reg_t* value) {
  brotli_reg_t bits;
  switch (s->substate_decode_uint8) {
    case BROTLI_STATE_DECODE_UINT8_NONE:
      if (BROTLI_PREDICT_FALSE(!BrotliSafeReadBits(br, 1, &bits))) {
        return BROTLI_DECODER_NEEDS_MORE_INPUT;
      }
      if (bits == 0) {
        *value = 0;
        return BROTLI_DECODER_SUCCESS;
      }
    /* Fall through. */

    case BROTLI_STATE_DECODE_UINT8_SHORT:
      if (BROTLI_PREDICT_FALSE(!BrotliSafeReadBits(br, 3, &bits))) {
        s->substate_decode_uint8 = BROTLI_STATE_DECODE_UINT8_SHORT;
        return BROTLI_DECODER_NEEDS_MORE_INPUT;
      }
      if (bits == 0) {
        *value = 1;
        s->substate_decode_uint8 = BROTLI_STATE_DECODE_UINT8_NONE;
        return BROTLI_DECODER_SUCCESS;
      }
      /* Use output value as a temporary storage. It MUST be persisted. */
      *value = bits;
    /* Fall through. */

    case BROTLI_STATE_DECODE_UINT8_LONG:
      if (BROTLI_PREDICT_FALSE(!BrotliSafeReadBits(br, *value, &bits))) {
        s->substate_decode_uint8 = BROTLI_STATE_DECODE_UINT8_LONG;
        return BROTLI_DECODER_NEEDS_MORE_INPUT;
      }
      *value = ((brotli_reg_t)1U << *value) + bits;
      s->substate_decode_uint8 = BROTLI_STATE_DECODE_UINT8_NONE;
      return BROTLI_DECODER_SUCCESS;

    default:
      return
          BROTLI_FAILURE(BROTLI_DECODER_ERROR_UNREACHABLE);  /* COV_NF_LINE */
  }
}

/* Decodes a metablock length and flags by reading 2 - 31 bits. */
static BrotliDecoderErrorCode BROTLI_NOINLINE DecodeMetaBlockLength(
    BrotliDecoderState* s, BrotliBitReader* br) {
  brotli_reg_t bits;
  int i;
  for (;;) {
    switch (s->substate_metablock_header) {
      case BROTLI_STATE_METABLOCK_HEADER_NONE:
        if (!BrotliSafeReadBits(br, 1, &bits)) {
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        s->is_last_metablock = bits ? 1 : 0;
        s->meta_block_remaining_len = 0;
        s->is_uncompressed = 0;
        s->is_metadata = 0;
        if (!s->is_last_metablock) {
          s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_NIBBLES;
          break;
        }
        s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_EMPTY;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_HEADER_EMPTY:
        if (!BrotliSafeReadBits(br, 1, &bits)) {
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        if (bits) {
          s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_NONE;
          return BROTLI_DECODER_SUCCESS;
        }
        s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_NIBBLES;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_HEADER_NIBBLES:
        if (!BrotliSafeReadBits(br, 2, &bits)) {
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        s->size_nibbles = (uint8_t)(bits + 4);
        s->loop_counter = 0;
        if (bits == 3) {
          s->is_metadata = 1;
          s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_RESERVED;
          break;
        }
        s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_SIZE;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_HEADER_SIZE:
        i = s->loop_counter;
        for (; i < (int)s->size_nibbles; ++i) {
          if (!BrotliSafeReadBits(br, 4, &bits)) {
            s->loop_counter = i;
            return BROTLI_DECODER_NEEDS_MORE_INPUT;
          }
          if (i + 1 == (int)s->size_nibbles && s->size_nibbles > 4 &&
              bits == 0) {
            return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_EXUBERANT_NIBBLE);
          }
          s->meta_block_remaining_len |= (int)(bits << (i * 4));
        }
        s->substate_metablock_header =
            BROTLI_STATE_METABLOCK_HEADER_UNCOMPRESSED;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_HEADER_UNCOMPRESSED:
        if (!s->is_last_metablock) {
          if (!BrotliSafeReadBits(br, 1, &bits)) {
            return BROTLI_DECODER_NEEDS_MORE_INPUT;
          }
          s->is_uncompressed = bits ? 1 : 0;
        }
        ++s->meta_block_remaining_len;
        s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_NONE;
        return BROTLI_DECODER_SUCCESS;

      case BROTLI_STATE_METABLOCK_HEADER_RESERVED:
        if (!BrotliSafeReadBits(br, 1, &bits)) {
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        if (bits != 0) {
          return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_RESERVED);
        }
        s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_BYTES;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_HEADER_BYTES:
        if (!BrotliSafeReadBits(br, 2, &bits)) {
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        if (bits == 0) {
          s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_NONE;
          return BROTLI_DECODER_SUCCESS;
        }
        s->size_nibbles = (uint8_t)bits;
        s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_METADATA;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_HEADER_METADATA:
        i = s->loop_counter;
        for (; i < (int)s->size_nibbles; ++i) {
          if (!BrotliSafeReadBits(br, 8, &bits)) {
            s->loop_counter = i;
            return BROTLI_DECODER_NEEDS_MORE_INPUT;
          }
          if (i + 1 == (int)s->size_nibbles && s->size_nibbles > 1 &&
              bits == 0) {
            return BROTLI_FAILURE(
                BROTLI_DECODER_ERROR_FORMAT_EXUBERANT_META_NIBBLE);
          }
          s->meta_block_remaining_len |= (int)(bits << (i * 8));
        }
        ++s->meta_block_remaining_len;
        s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_NONE;
        return BROTLI_DECODER_SUCCESS;

      default:
        return
            BROTLI_FAILURE(BROTLI_DECODER_ERROR_UNREACHABLE);  /* COV_NF_LINE */
    }
  }
}

/* Decodes the Huffman code.
   This method doesn't read data from the bit reader, BUT drops the amount of
   bits that correspond to the decoded symbol.
   bits MUST contain at least 15 (BROTLI_HUFFMAN_MAX_CODE_LENGTH) valid bits. */
static BROTLI_INLINE brotli_reg_t DecodeSymbol(brotli_reg_t bits,
                                               const HuffmanCode* table,
                                               BrotliBitReader* br) {
  BROTLI_HC_MARK_TABLE_FOR_FAST_LOAD(table);
  BROTLI_HC_ADJUST_TABLE_INDEX(table, bits & HUFFMAN_TABLE_MASK);
  if (BROTLI_HC_FAST_LOAD_BITS(table) > HUFFMAN_TABLE_BITS) {
    brotli_reg_t nbits = BROTLI_HC_FAST_LOAD_BITS(table) - HUFFMAN_TABLE_BITS;
    BrotliDropBits(br, HUFFMAN_TABLE_BITS);
    BROTLI_HC_ADJUST_TABLE_INDEX(table,
        BROTLI_HC_FAST_LOAD_VALUE(table) +
        ((bits >> HUFFMAN_TABLE_BITS) & BitMask(nbits)));
  }
  BrotliDropBits(br, BROTLI_HC_FAST_LOAD_BITS(table));
  return BROTLI_HC_FAST_LOAD_VALUE(table);
}

/* Reads and decodes the next Huffman code from bit-stream.
   This method peeks 16 bits of input and drops 0 - 15 of them. */
static BROTLI_INLINE brotli_reg_t ReadSymbol(const HuffmanCode* table,
                                             BrotliBitReader* br) {
  return DecodeSymbol(BrotliGet16BitsUnmasked(br), table, br);
}

/* Same as DecodeSymbol, but it is known that there is less than 15 bits of
   input are currently available. */
static BROTLI_NOINLINE BROTLI_BOOL SafeDecodeSymbol(
    const HuffmanCode* table, BrotliBitReader* br, brotli_reg_t* result) {
  brotli_reg_t val;
  brotli_reg_t available_bits = BrotliGetAvailableBits(br);
  BROTLI_HC_MARK_TABLE_FOR_FAST_LOAD(table);
  if (available_bits == 0) {
    if (BROTLI_HC_FAST_LOAD_BITS(table) == 0) {
      *result = BROTLI_HC_FAST_LOAD_VALUE(table);
      return BROTLI_TRUE;
    }
    return BROTLI_FALSE;  /* No valid bits at all. */
  }
  val = BrotliGetBitsUnmasked(br);
  BROTLI_HC_ADJUST_TABLE_INDEX(table, val & HUFFMAN_TABLE_MASK);
  if (BROTLI_HC_FAST_LOAD_BITS(table) <= HUFFMAN_TABLE_BITS) {
    if (BROTLI_HC_FAST_LOAD_BITS(table) <= available_bits) {
      BrotliDropBits(br, BROTLI_HC_FAST_LOAD_BITS(table));
      *result = BROTLI_HC_FAST_LOAD_VALUE(table);
      return BROTLI_TRUE;
    } else {
      return BROTLI_FALSE;  /* Not enough bits for the first level. */
    }
  }
  if (available_bits <= HUFFMAN_TABLE_BITS) {
    return BROTLI_FALSE;  /* Not enough bits to move to the second level. */
  }

  /* Speculatively drop HUFFMAN_TABLE_BITS. */
  val = (val & BitMask(BROTLI_HC_FAST_LOAD_BITS(table))) >> HUFFMAN_TABLE_BITS;
  available_bits -= HUFFMAN_TABLE_BITS;
  BROTLI_HC_ADJUST_TABLE_INDEX(table, BROTLI_HC_FAST_LOAD_VALUE(table) + val);
  if (available_bits < BROTLI_HC_FAST_LOAD_BITS(table)) {
    return BROTLI_FALSE;  /* Not enough bits for the second level. */
  }

  BrotliDropBits(br, HUFFMAN_TABLE_BITS + BROTLI_HC_FAST_LOAD_BITS(table));
  *result = BROTLI_HC_FAST_LOAD_VALUE(table);
  return BROTLI_TRUE;
}

static BROTLI_INLINE BROTLI_BOOL SafeReadSymbol(
    const HuffmanCode* table, BrotliBitReader* br, brotli_reg_t* result) {
  brotli_reg_t val;
  if (BROTLI_PREDICT_TRUE(BrotliSafeGetBits(br, 15, &val))) {
    *result = DecodeSymbol(val, table, br);
    return BROTLI_TRUE;
  }
  return SafeDecodeSymbol(table, br, result);
}

/* Makes a look-up in first level Huffman table. Peeks 8 bits. */
static BROTLI_INLINE void PreloadSymbol(int safe,
                                        const HuffmanCode* table,
                                        BrotliBitReader* br,
                                        brotli_reg_t* bits,
                                        brotli_reg_t* value) {
  if (safe) {
    return;
  }
  BROTLI_HC_MARK_TABLE_FOR_FAST_LOAD(table);
  BROTLI_HC_ADJUST_TABLE_INDEX(table, BrotliGetBits(br, HUFFMAN_TABLE_BITS));
  *bits = BROTLI_HC_FAST_LOAD_BITS(table);
  *value = BROTLI_HC_FAST_LOAD_VALUE(table);
}

/* Decodes the next Huffman code using data prepared by PreloadSymbol.
   Reads 0 - 15 bits. Also peeks 8 following bits. */
static BROTLI_INLINE brotli_reg_t ReadPreloadedSymbol(const HuffmanCode* table,
                                                  BrotliBitReader* br,
                                                  brotli_reg_t* bits,
                                                  brotli_reg_t* value) {
  brotli_reg_t result = *value;
  if (BROTLI_PREDICT_FALSE(*bits > HUFFMAN_TABLE_BITS)) {
    brotli_reg_t val = BrotliGet16BitsUnmasked(br);
    const HuffmanCode* ext = table + (val & HUFFMAN_TABLE_MASK) + *value;
    brotli_reg_t mask = BitMask((*bits - HUFFMAN_TABLE_BITS));
    BROTLI_HC_MARK_TABLE_FOR_FAST_LOAD(ext);
    BrotliDropBits(br, HUFFMAN_TABLE_BITS);
    BROTLI_HC_ADJUST_TABLE_INDEX(ext, (val >> HUFFMAN_TABLE_BITS) & mask);
    BrotliDropBits(br, BROTLI_HC_FAST_LOAD_BITS(ext));
    result = BROTLI_HC_FAST_LOAD_VALUE(ext);
  } else {
    BrotliDropBits(br, *bits);
  }
  PreloadSymbol(0, table, br, bits, value);
  return result;
}

/* Reads up to limit symbols from br and copies them into ringbuffer,
   starting from pos. Caller must ensure that there is enough space
   for the write. Returns the amount of symbols actually copied. */
static BROTLI_INLINE int BrotliCopyPreloadedSymbolsToU8(const HuffmanCode* table,
                                                        BrotliBitReader* br,
                                                        brotli_reg_t* bits,
                                                        brotli_reg_t* value,
                                                        uint8_t* ringbuffer,
                                                        int pos,
                                                        const int limit) {
  /* Calculate range where CheckInputAmount is always true.
     Start with the number of bytes we can read. */
  int64_t new_lim = br->guard_in - br->next_in;
  /* Convert to bits, since symbols use variable number of bits. */
  new_lim *= 8;
  /* At most 15 bits per symbol, so this is safe. */
  new_lim /= 15;
  const int kMaximalOverread = 4;
  int pos_limit = limit;
  int copies = 0;
  if ((new_lim - kMaximalOverread) <= limit) {
    // Safe cast, since new_lim is already < num_steps
    pos_limit = (int)(new_lim - kMaximalOverread);
  }
  if (pos_limit < 0) {
    pos_limit = 0;
  }
  copies = pos_limit;
  pos_limit += pos;
  /* Fast path, caller made sure it is safe to write,
     we verified that is is safe to read. */
  for (; pos < pos_limit; pos++) {
    BROTLI_DCHECK(BrotliCheckInputAmount(br));
    ringbuffer[pos] = (uint8_t)ReadPreloadedSymbol(table, br, bits, value);
    BROTLI_LOG_ARRAY_INDEX(ringbuffer, pos);
  }
  /* Do the remainder, caller made sure it is safe to write,
     we need to bverify that it is safe to read. */
  while (BrotliCheckInputAmount(br) && copies < limit) {
    ringbuffer[pos] = (uint8_t)ReadPreloadedSymbol(table, br, bits, value);
    BROTLI_LOG_ARRAY_INDEX(ringbuffer, pos);
    pos++;
    copies++;
  }
  return copies;
}

static BROTLI_INLINE brotli_reg_t Log2Floor(brotli_reg_t x) {
  brotli_reg_t result = 0;
  while (x) {
    x >>= 1;
    ++result;
  }
  return result;
}

/* Reads (s->symbol + 1) symbols.
   Totally 1..4 symbols are read, 1..11 bits each.
   The list of symbols MUST NOT contain duplicates. */
static BrotliDecoderErrorCode ReadSimpleHuffmanSymbols(
    brotli_reg_t alphabet_size_max, brotli_reg_t alphabet_size_limit,
    BrotliDecoderState* s) {
  /* max_bits == 1..11; symbol == 0..3; 1..44 bits will be read. */
  BrotliBitReader* br = &s->br;
  BrotliMetablockHeaderArena* h = &s->arena.header;
  brotli_reg_t max_bits = Log2Floor(alphabet_size_max - 1);
  brotli_reg_t i = h->sub_loop_counter;
  brotli_reg_t num_symbols = h->symbol;
  while (i <= num_symbols) {
    brotli_reg_t v;
    if (BROTLI_PREDICT_FALSE(!BrotliSafeReadBits(br, max_bits, &v))) {
      h->sub_loop_counter = i;
      h->substate_huffman = BROTLI_STATE_HUFFMAN_SIMPLE_READ;
      return BROTLI_DECODER_NEEDS_MORE_INPUT;
    }
    if (v >= alphabet_size_limit) {
      return
          BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_SIMPLE_HUFFMAN_ALPHABET);
    }
    h->symbols_lists_array[i] = (uint16_t)v;
    BROTLI_LOG_UINT(h->symbols_lists_array[i]);
    ++i;
  }

  for (i = 0; i < num_symbols; ++i) {
    brotli_reg_t k = i + 1;
    for (; k <= num_symbols; ++k) {
      if (h->symbols_lists_array[i] == h->symbols_lists_array[k]) {
        return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_SIMPLE_HUFFMAN_SAME);
      }
    }
  }

  return BROTLI_DECODER_SUCCESS;
}

/* Process single decoded symbol code length:
    A) reset the repeat variable
    B) remember code length (if it is not 0)
    C) extend corresponding index-chain
    D) reduce the Huffman space
    E) update the histogram */
static BROTLI_INLINE void ProcessSingleCodeLength(brotli_reg_t code_len,
    brotli_reg_t* symbol, brotli_reg_t* repeat, brotli_reg_t* space,
    brotli_reg_t* prev_code_len, uint16_t* symbol_lists,
    uint16_t* code_length_histo, int* next_symbol) {
  *repeat = 0;
  if (code_len != 0) {  /* code_len == 1..15 */
    symbol_lists[next_symbol[code_len]] = (uint16_t)(*symbol);
    next_symbol[code_len] = (int)(*symbol);
    *prev_code_len = code_len;
    *space -= 32768U >> code_len;
    code_length_histo[code_len]++;
    BROTLI_LOG(("[ReadHuffmanCode] code_length[%d] = %d\n",
        (int)*symbol, (int)code_len));
  }
  (*symbol)++;
}

/* Process repeated symbol code length.
    A) Check if it is the extension of previous repeat sequence; if the decoded
       value is not BROTLI_REPEAT_PREVIOUS_CODE_LENGTH, then it is a new
       symbol-skip
    B) Update repeat variable
    C) Check if operation is feasible (fits alphabet)
    D) For each symbol do the same operations as in ProcessSingleCodeLength

   PRECONDITION: code_len == BROTLI_REPEAT_PREVIOUS_CODE_LENGTH or
                 code_len == BROTLI_REPEAT_ZERO_CODE_LENGTH */
static BROTLI_INLINE void ProcessRepeatedCodeLength(brotli_reg_t code_len,
    brotli_reg_t repeat_delta, brotli_reg_t alphabet_size, brotli_reg_t* symbol,
    brotli_reg_t* repeat, brotli_reg_t* space, brotli_reg_t* prev_code_len,
    brotli_reg_t* repeat_code_len, uint16_t* symbol_lists,
    uint16_t* code_length_histo, int* next_symbol) {
  brotli_reg_t old_repeat;
  brotli_reg_t extra_bits = 3;  /* for BROTLI_REPEAT_ZERO_CODE_LENGTH */
  brotli_reg_t new_len = 0;  /* for BROTLI_REPEAT_ZERO_CODE_LENGTH */
  if (code_len == BROTLI_REPEAT_PREVIOUS_CODE_LENGTH) {
    new_len = *prev_code_len;
    extra_bits = 2;
  }
  if (*repeat_code_len != new_len) {
    *repeat = 0;
    *repeat_code_len = new_len;
  }
  old_repeat = *repeat;
  if (*repeat > 0) {
    *repeat -= 2;
    *repeat <<= extra_bits;
  }
  *repeat += repeat_delta + 3U;
  repeat_delta = *repeat - old_repeat;
  if (*symbol + repeat_delta > alphabet_size) {
    BROTLI_DUMP();
    *symbol = alphabet_size;
    *space = 0xFFFFF;
    return;
  }
  BROTLI_LOG(("[ReadHuffmanCode] code_length[%d..%d] = %d\n",
      (int)*symbol, (int)(*symbol + repeat_delta - 1), (int)*repeat_code_len));
  if (*repeat_code_len != 0) {
    brotli_reg_t last = *symbol + repeat_delta;
    int next = next_symbol[*repeat_code_len];
    do {
      symbol_lists[next] = (uint16_t)*symbol;
      next = (int)*symbol;
    } while (++(*symbol) != last);
    next_symbol[*repeat_code_len] = next;
    *space -= repeat_delta << (15 - *repeat_code_len);
    code_length_histo[*repeat_code_len] =
        (uint16_t)(code_length_histo[*repeat_code_len] + repeat_delta);
  } else {
    *symbol += repeat_delta;
  }
}

/* Reads and decodes symbol codelengths. */
static BrotliDecoderErrorCode ReadSymbolCodeLengths(
    brotli_reg_t alphabet_size, BrotliDecoderState* s) {
  BrotliBitReader* br = &s->br;
  BrotliMetablockHeaderArena* h = &s->arena.header;
  brotli_reg_t symbol = h->symbol;
  brotli_reg_t repeat = h->repeat;
  brotli_reg_t space = h->space;
  brotli_reg_t prev_code_len = h->prev_code_len;
  brotli_reg_t repeat_code_len = h->repeat_code_len;
  uint16_t* symbol_lists = h->symbol_lists;
  uint16_t* code_length_histo = h->code_length_histo;
  int* next_symbol = h->next_symbol;
  if (!BrotliWarmupBitReader(br)) {
    return BROTLI_DECODER_NEEDS_MORE_INPUT;
  }
  while (symbol < alphabet_size && space > 0) {
    const HuffmanCode* p = h->table;
    brotli_reg_t code_len;
    BROTLI_HC_MARK_TABLE_FOR_FAST_LOAD(p);
    if (!BrotliCheckInputAmount(br)) {
      h->symbol = symbol;
      h->repeat = repeat;
      h->prev_code_len = prev_code_len;
      h->repeat_code_len = repeat_code_len;
      h->space = space;
      return BROTLI_DECODER_NEEDS_MORE_INPUT;
    }
    BrotliFillBitWindow16(br);
    BROTLI_HC_ADJUST_TABLE_INDEX(p, BrotliGetBitsUnmasked(br) &
        BitMask(BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH));
    BrotliDropBits(br, BROTLI_HC_FAST_LOAD_BITS(p));  /* Use 1..5 bits. */
    code_len = BROTLI_HC_FAST_LOAD_VALUE(p);  /* code_len == 0..17 */
    if (code_len < BROTLI_REPEAT_PREVIOUS_CODE_LENGTH) {
      ProcessSingleCodeLength(code_len, &symbol, &repeat, &space,
          &prev_code_len, symbol_lists, code_length_histo, next_symbol);
    } else {  /* code_len == 16..17, extra_bits == 2..3 */
      brotli_reg_t extra_bits =
          (code_len == BROTLI_REPEAT_PREVIOUS_CODE_LENGTH) ? 2 : 3;
      brotli_reg_t repeat_delta =
          BrotliGetBitsUnmasked(br) & BitMask(extra_bits);
      BrotliDropBits(br, extra_bits);
      ProcessRepeatedCodeLength(code_len, repeat_delta, alphabet_size,
          &symbol, &repeat, &space, &prev_code_len, &repeat_code_len,
          symbol_lists, code_length_histo, next_symbol);
    }
  }
  h->space = space;
  return BROTLI_DECODER_SUCCESS;
}

static BrotliDecoderErrorCode SafeReadSymbolCodeLengths(
    brotli_reg_t alphabet_size, BrotliDecoderState* s) {
  BrotliBitReader* br = &s->br;
  BrotliMetablockHeaderArena* h = &s->arena.header;
  BROTLI_BOOL get_byte = BROTLI_FALSE;
  while (h->symbol < alphabet_size && h->space > 0) {
    const HuffmanCode* p = h->table;
    brotli_reg_t code_len;
    brotli_reg_t available_bits;
    brotli_reg_t bits = 0;
    BROTLI_HC_MARK_TABLE_FOR_FAST_LOAD(p);
    if (get_byte && !BrotliPullByte(br)) return BROTLI_DECODER_NEEDS_MORE_INPUT;
    get_byte = BROTLI_FALSE;
    available_bits = BrotliGetAvailableBits(br);
    if (available_bits != 0) {
      bits = (uint32_t)BrotliGetBitsUnmasked(br);
    }
    BROTLI_HC_ADJUST_TABLE_INDEX(p,
        bits & BitMask(BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH));
    if (BROTLI_HC_FAST_LOAD_BITS(p) > available_bits) {
      get_byte = BROTLI_TRUE;
      continue;
    }
    code_len = BROTLI_HC_FAST_LOAD_VALUE(p);  /* code_len == 0..17 */
    if (code_len < BROTLI_REPEAT_PREVIOUS_CODE_LENGTH) {
      BrotliDropBits(br, BROTLI_HC_FAST_LOAD_BITS(p));
      ProcessSingleCodeLength(code_len, &h->symbol, &h->repeat, &h->space,
          &h->prev_code_len, h->symbol_lists, h->code_length_histo,
          h->next_symbol);
    } else {  /* code_len == 16..17, extra_bits == 2..3 */
      brotli_reg_t extra_bits = code_len - 14U;
      brotli_reg_t repeat_delta = (bits >> BROTLI_HC_FAST_LOAD_BITS(p)) &
          BitMask(extra_bits);
      if (available_bits < BROTLI_HC_FAST_LOAD_BITS(p) + extra_bits) {
        get_byte = BROTLI_TRUE;
        continue;
      }
      BrotliDropBits(br, BROTLI_HC_FAST_LOAD_BITS(p) + extra_bits);
      ProcessRepeatedCodeLength(code_len, repeat_delta, alphabet_size,
          &h->symbol, &h->repeat, &h->space, &h->prev_code_len,
          &h->repeat_code_len, h->symbol_lists, h->code_length_histo,
          h->next_symbol);
    }
  }
  return BROTLI_DECODER_SUCCESS;
}

/* Reads and decodes 15..18 codes using static prefix code.
   Each code is 2..4 bits long. In total 30..72 bits are used. */
static BrotliDecoderErrorCode ReadCodeLengthCodeLengths(BrotliDecoderState* s) {
  BrotliBitReader* br = &s->br;
  BrotliMetablockHeaderArena* h = &s->arena.header;
  brotli_reg_t num_codes = h->repeat;
  brotli_reg_t space = h->space;
  brotli_reg_t i = h->sub_loop_counter;
  for (; i < BROTLI_CODE_LENGTH_CODES; ++i) {
    const uint8_t code_len_idx = kCodeLengthCodeOrder[i];
    brotli_reg_t ix;
    brotli_reg_t v;
    if (BROTLI_PREDICT_FALSE(!BrotliSafeGetBits(br, 4, &ix))) {
      brotli_reg_t available_bits = BrotliGetAvailableBits(br);
      if (available_bits != 0) {
        ix = BrotliGetBitsUnmasked(br) & 0xF;
      } else {
        ix = 0;
      }
      if (kCodeLengthPrefixLength[ix] > available_bits) {
        h->sub_loop_counter = i;
        h->repeat = num_codes;
        h->space = space;
        h->substate_huffman = BROTLI_STATE_HUFFMAN_COMPLEX;
        return BROTLI_DECODER_NEEDS_MORE_INPUT;
      }
    }
    v = kCodeLengthPrefixValue[ix];
    BrotliDropBits(br, kCodeLengthPrefixLength[ix]);
    h->code_length_code_lengths[code_len_idx] = (uint8_t)v;
    BROTLI_LOG_ARRAY_INDEX(h->code_length_code_lengths, code_len_idx);
    if (v != 0) {
      space = space - (32U >> v);
      ++num_codes;
      ++h->code_length_histo[v];
      if (space - 1U >= 32U) {
        /* space is 0 or wrapped around. */
        break;
      }
    }
  }
  if (!(num_codes == 1 || space == 0)) {
    return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_CL_SPACE);
  }
  return BROTLI_DECODER_SUCCESS;
}

/* Decodes the Huffman tables.
   There are 2 scenarios:
    A) Huffman code contains only few symbols (1..4). Those symbols are read
       directly; their code lengths are defined by the number of symbols.
       For this scenario 4 - 49 bits will be read.

    B) 2-phase decoding:
    B.1) Small Huffman table is decoded; it is specified with code lengths
         encoded with predefined entropy code. 32 - 74 bits are used.
    B.2) Decoded table is used to decode code lengths of symbols in resulting
         Huffman table. In worst case 3520 bits are read. */
static BrotliDecoderErrorCode ReadHuffmanCode(brotli_reg_t alphabet_size_max,
                                              brotli_reg_t alphabet_size_limit,
                                              HuffmanCode* table,
                                              brotli_reg_t* opt_table_size,
                                              BrotliDecoderState* s) {
  BrotliBitReader* br = &s->br;
  BrotliMetablockHeaderArena* h = &s->arena.header;
  /* State machine. */
  for (;;) {
    switch (h->substate_huffman) {
      case BROTLI_STATE_HUFFMAN_NONE:
        if (!BrotliSafeReadBits(br, 2, &h->sub_loop_counter)) {
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        BROTLI_LOG_UINT(h->sub_loop_counter);
        /* The value is used as follows:
           1 for simple code;
           0 for no skipping, 2 skips 2 code lengths, 3 skips 3 code lengths */
        if (h->sub_loop_counter != 1) {
          h->space = 32;
          h->repeat = 0;  /* num_codes */
          memset(&h->code_length_histo[0], 0, sizeof(h->code_length_histo[0]) *
              (BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH + 1));
          memset(&h->code_length_code_lengths[0], 0,
              sizeof(h->code_length_code_lengths));
          h->substate_huffman = BROTLI_STATE_HUFFMAN_COMPLEX;
          continue;
        }
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_SIMPLE_SIZE:
        /* Read symbols, codes & code lengths directly. */
        if (!BrotliSafeReadBits(br, 2, &h->symbol)) {  /* num_symbols */
          h->substate_huffman = BROTLI_STATE_HUFFMAN_SIMPLE_SIZE;
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        h->sub_loop_counter = 0;
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_SIMPLE_READ: {
        BrotliDecoderErrorCode result =
            ReadSimpleHuffmanSymbols(alphabet_size_max, alphabet_size_limit, s);
        if (result != BROTLI_DECODER_SUCCESS) {
          return result;
        }
      }
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_SIMPLE_BUILD: {
        brotli_reg_t table_size;
        if (h->symbol == 3) {
          brotli_reg_t bits;
          if (!BrotliSafeReadBits(br, 1, &bits)) {
            h->substate_huffman = BROTLI_STATE_HUFFMAN_SIMPLE_BUILD;
            return BROTLI_DECODER_NEEDS_MORE_INPUT;
          }
          h->symbol += bits;
        }
        BROTLI_LOG_UINT(h->symbol);
        table_size = BrotliBuildSimpleHuffmanTable(table, HUFFMAN_TABLE_BITS,
                                                   h->symbols_lists_array,
                                                   (uint32_t)h->symbol);
        if (opt_table_size) {
          *opt_table_size = table_size;
        }
        h->substate_huffman = BROTLI_STATE_HUFFMAN_NONE;
        return BROTLI_DECODER_SUCCESS;
      }

      /* Decode Huffman-coded code lengths. */
      case BROTLI_STATE_HUFFMAN_COMPLEX: {
        brotli_reg_t i;
        BrotliDecoderErrorCode result = ReadCodeLengthCodeLengths(s);
        if (result != BROTLI_DECODER_SUCCESS) {
          return result;
        }
        BrotliBuildCodeLengthsHuffmanTable(h->table,
                                           h->code_length_code_lengths,
                                           h->code_length_histo);
        memset(&h->code_length_histo[0], 0, sizeof(h->code_length_histo));
        for (i = 0; i <= BROTLI_HUFFMAN_MAX_CODE_LENGTH; ++i) {
          h->next_symbol[i] = (int)i - (BROTLI_HUFFMAN_MAX_CODE_LENGTH + 1);
          h->symbol_lists[h->next_symbol[i]] = 0xFFFF;
        }

        h->symbol = 0;
        h->prev_code_len = BROTLI_INITIAL_REPEATED_CODE_LENGTH;
        h->repeat = 0;
        h->repeat_code_len = 0;
        h->space = 32768;
        h->substate_huffman = BROTLI_STATE_HUFFMAN_LENGTH_SYMBOLS;
      }
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_LENGTH_SYMBOLS: {
        brotli_reg_t table_size;
        BrotliDecoderErrorCode result = ReadSymbolCodeLengths(
            alphabet_size_limit, s);
        if (result == BROTLI_DECODER_NEEDS_MORE_INPUT) {
          result = SafeReadSymbolCodeLengths(alphabet_size_limit, s);
        }
        if (result != BROTLI_DECODER_SUCCESS) {
          return result;
        }

        if (h->space != 0) {
          BROTLI_LOG(("[ReadHuffmanCode] space = %d\n", (int)h->space));
          return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_HUFFMAN_SPACE);
        }
        table_size = BrotliBuildHuffmanTable(
            table, HUFFMAN_TABLE_BITS, h->symbol_lists, h->code_length_histo);
        if (opt_table_size) {
          *opt_table_size = table_size;
        }
        h->substate_huffman = BROTLI_STATE_HUFFMAN_NONE;
        return BROTLI_DECODER_SUCCESS;
      }

      default:
        return
            BROTLI_FAILURE(BROTLI_DECODER_ERROR_UNREACHABLE);  /* COV_NF_LINE */
    }
  }
}

/* Decodes a block length by reading 3..39 bits. */
static BROTLI_INLINE brotli_reg_t ReadBlockLength(const HuffmanCode* table,
                                                  BrotliBitReader* br) {
  brotli_reg_t code;
  brotli_reg_t nbits;
  code = ReadSymbol(table, br);
  nbits = _kBrotliPrefixCodeRanges[code].nbits;  /* nbits == 2..24 */
  return _kBrotliPrefixCodeRanges[code].offset + BrotliReadBits24(br, nbits);
}

/* WARNING: if state is not BROTLI_STATE_READ_BLOCK_LENGTH_NONE, then
   reading can't be continued with ReadBlockLength. */
static BROTLI_INLINE BROTLI_BOOL SafeReadBlockLength(
    BrotliDecoderState* s, brotli_reg_t* result, const HuffmanCode* table,
    BrotliBitReader* br) {
  brotli_reg_t index;
  if (s->substate_read_block_length == BROTLI_STATE_READ_BLOCK_LENGTH_NONE) {
    if (!SafeReadSymbol(table, br, &index)) {
      return BROTLI_FALSE;
    }
  } else {
    index = s->block_length_index;
  }
  {
    brotli_reg_t bits;
    brotli_reg_t nbits = _kBrotliPrefixCodeRanges[index].nbits;
    brotli_reg_t offset = _kBrotliPrefixCodeRanges[index].offset;
    if (!BrotliSafeReadBits(br, nbits, &bits)) {
      s->block_length_index = index;
      s->substate_read_block_length = BROTLI_STATE_READ_BLOCK_LENGTH_SUFFIX;
      return BROTLI_FALSE;
    }
    *result = offset + bits;
    s->substate_read_block_length = BROTLI_STATE_READ_BLOCK_LENGTH_NONE;
    return BROTLI_TRUE;
  }
}

/* Transform:
    1) initialize list L with values 0, 1,... 255
    2) For each input element X:
    2.1) let Y = L[X]
    2.2) remove X-th element from L
    2.3) prepend Y to L
    2.4) append Y to output

   In most cases max(Y) <= 7, so most of L remains intact.
   To reduce the cost of initialization, we reuse L, remember the upper bound
   of Y values, and reinitialize only first elements in L.

   Most of input values are 0 and 1. To reduce number of branches, we replace
   inner for loop with do-while. */
static BROTLI_NOINLINE void InverseMoveToFrontTransform(
    uint8_t* v, brotli_reg_t v_len, BrotliDecoderState* state) {
  /* Reinitialize elements that could have been changed. */
  brotli_reg_t i = 1;
  brotli_reg_t upper_bound = state->mtf_upper_bound;
  uint32_t* mtf = &state->mtf[1];  /* Make mtf[-1] addressable. */
  uint8_t* mtf_u8 = (uint8_t*)mtf;
  /* Load endian-aware constant. */
  const uint8_t b0123[4] = {0, 1, 2, 3};
  uint32_t pattern;
  memcpy(&pattern, &b0123, 4);

  /* Initialize list using 4 consequent values pattern. */
  mtf[0] = pattern;
  do {
    pattern += 0x04040404;  /* Advance all 4 values by 4. */
    mtf[i] = pattern;
    i++;
  } while (i <= upper_bound);

  /* Transform the input. */
  upper_bound = 0;
  for (i = 0; i < v_len; ++i) {
    int index = v[i];
    uint8_t value = mtf_u8[index];
    upper_bound |= v[i];
    v[i] = value;
    mtf_u8[-1] = value;
    do {
      index--;
      mtf_u8[index + 1] = mtf_u8[index];
    } while (index >= 0);
  }
  /* Remember amount of elements to be reinitialized. */
  state->mtf_upper_bound = upper_bound >> 2;
}

/* Decodes a series of Huffman table using ReadHuffmanCode function. */
static BrotliDecoderErrorCode HuffmanTreeGroupDecode(
    HuffmanTreeGroup* group, BrotliDecoderState* s) {
  BrotliMetablockHeaderArena* h = &s->arena.header;
  if (h->substate_tree_group != BROTLI_STATE_TREE_GROUP_LOOP) {
    h->next = group->codes;
    h->htree_index = 0;
    h->substate_tree_group = BROTLI_STATE_TREE_GROUP_LOOP;
  }
  while (h->htree_index < group->num_htrees) {
    brotli_reg_t table_size;
    BrotliDecoderErrorCode result = ReadHuffmanCode(group->alphabet_size_max,
        group->alphabet_size_limit, h->next, &table_size, s);
    if (result != BROTLI_DECODER_SUCCESS) return result;
    group->htrees[h->htree_index] = h->next;
    h->next += table_size;
    ++h->htree_index;
  }
  h->substate_tree_group = BROTLI_STATE_TREE_GROUP_NONE;
  return BROTLI_DECODER_SUCCESS;
}

/* Decodes a context map.
   Decoding is done in 4 phases:
    1) Read auxiliary information (6..16 bits) and allocate memory.
       In case of trivial context map, decoding is finished at this phase.
    2) Decode Huffman table using ReadHuffmanCode function.
       This table will be used for reading context map items.
    3) Read context map items; "0" values could be run-length encoded.
    4) Optionally, apply InverseMoveToFront transform to the resulting map. */
static BrotliDecoderErrorCode DecodeContextMap(brotli_reg_t context_map_size,
                                               brotli_reg_t* num_htrees,
                                               uint8_t** context_map_arg,
                                               BrotliDecoderState* s) {
  BrotliBitReader* br = &s->br;
  BrotliDecoderErrorCode result = BROTLI_DECODER_SUCCESS;
  BrotliMetablockHeaderArena* h = &s->arena.header;

  switch ((int)h->substate_context_map) {
    case BROTLI_STATE_CONTEXT_MAP_NONE:
      result = DecodeVarLenUint8(s, br, num_htrees);
      if (result != BROTLI_DECODER_SUCCESS) {
        return result;
      }
      (*num_htrees)++;
      h->context_index = 0;
      BROTLI_LOG_UINT(context_map_size);
      BROTLI_LOG_UINT(*num_htrees);
      *context_map_arg =
          (uint8_t*)BROTLI_DECODER_ALLOC(s, (size_t)context_map_size);
      if (*context_map_arg == 0) {
        return BROTLI_FAILURE(BROTLI_DECODER_ERROR_ALLOC_CONTEXT_MAP);
      }
      if (*num_htrees <= 1) {
        memset(*context_map_arg, 0, (size_t)context_map_size);
        return BROTLI_DECODER_SUCCESS;
      }
      h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_READ_PREFIX;
    /* Fall through. */

    case BROTLI_STATE_CONTEXT_MAP_READ_PREFIX: {
      brotli_reg_t bits;
      /* In next stage ReadHuffmanCode uses at least 4 bits, so it is safe
         to peek 4 bits ahead. */
      if (!BrotliSafeGetBits(br, 5, &bits)) {
        return BROTLI_DECODER_NEEDS_MORE_INPUT;
      }
      if ((bits & 1) != 0) { /* Use RLE for zeros. */
        h->max_run_length_prefix = (bits >> 1) + 1;
        BrotliDropBits(br, 5);
      } else {
        h->max_run_length_prefix = 0;
        BrotliDropBits(br, 1);
      }
      BROTLI_LOG_UINT(h->max_run_length_prefix);
      h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_HUFFMAN;
    }
    /* Fall through. */

    case BROTLI_STATE_CONTEXT_MAP_HUFFMAN: {
      brotli_reg_t alphabet_size = *num_htrees + h->max_run_length_prefix;
      result = ReadHuffmanCode(alphabet_size, alphabet_size,
                               h->context_map_table, NULL, s);
      if (result != BROTLI_DECODER_SUCCESS) return result;
      h->code = 0xFFFF;
      h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_DECODE;
    }
    /* Fall through. */

    case BROTLI_STATE_CONTEXT_MAP_DECODE: {
      brotli_reg_t context_index = h->context_index;
      brotli_reg_t max_run_length_prefix = h->max_run_length_prefix;
      uint8_t* context_map = *context_map_arg;
      brotli_reg_t code = h->code;
      BROTLI_BOOL skip_preamble = (code != 0xFFFF);
      while (context_index < context_map_size || skip_preamble) {
        if (!skip_preamble) {
          if (!SafeReadSymbol(h->context_map_table, br, &code)) {
            h->code = 0xFFFF;
            h->context_index = context_index;
            return BROTLI_DECODER_NEEDS_MORE_INPUT;
          }
          BROTLI_LOG_UINT(code);

          if (code == 0) {
            context_map[context_index++] = 0;
            continue;
          }
          if (code > max_run_length_prefix) {
            context_map[context_index++] =
                (uint8_t)(code - max_run_length_prefix);
            continue;
          }
        } else {
          skip_preamble = BROTLI_FALSE;
        }
        /* RLE sub-stage. */
        {
          brotli_reg_t reps;
          if (!BrotliSafeReadBits(br, code, &reps)) {
            h->code = code;
            h->context_index = context_index;
            return BROTLI_DECODER_NEEDS_MORE_INPUT;
          }
          reps += (brotli_reg_t)1U << code;
          BROTLI_LOG_UINT(reps);
          if (context_index + reps > context_map_size) {
            return
                BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_CONTEXT_MAP_REPEAT);
          }
          do {
            context_map[context_index++] = 0;
          } while (--reps);
        }
      }
    }
    /* Fall through. */

    case BROTLI_STATE_CONTEXT_MAP_TRANSFORM: {
      brotli_reg_t bits;
      if (!BrotliSafeReadBits(br, 1, &bits)) {
        h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_TRANSFORM;
        return BROTLI_DECODER_NEEDS_MORE_INPUT;
      }
      if (bits != 0) {
        InverseMoveToFrontTransform(*context_map_arg, context_map_size, s);
      }
      h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_NONE;
      return BROTLI_DECODER_SUCCESS;
    }

    default:
      return
          BROTLI_FAILURE(BROTLI_DECODER_ERROR_UNREACHABLE);  /* COV_NF_LINE */
  }
}

/* Decodes a command or literal and updates block type ring-buffer.
   Reads 3..54 bits. */
static BROTLI_INLINE BROTLI_BOOL DecodeBlockTypeAndLength(
    int safe, BrotliDecoderState* s, int tree_type) {
  brotli_reg_t max_block_type = s->num_block_types[tree_type];
  const HuffmanCode* type_tree = &s->block_type_trees[
      tree_type * BROTLI_HUFFMAN_MAX_SIZE_258];
  const HuffmanCode* len_tree = &s->block_len_trees[
      tree_type * BROTLI_HUFFMAN_MAX_SIZE_26];
  BrotliBitReader* br = &s->br;
  brotli_reg_t* ringbuffer = &s->block_type_rb[tree_type * 2];
  brotli_reg_t block_type;
  if (max_block_type <= 1) {
    return BROTLI_FALSE;
  }

  /* Read 0..15 + 3..39 bits. */
  if (!safe) {
    block_type = ReadSymbol(type_tree, br);
    s->block_length[tree_type] = ReadBlockLength(len_tree, br);
  } else {
    BrotliBitReaderState memento;
    BrotliBitReaderSaveState(br, &memento);
    if (!SafeReadSymbol(type_tree, br, &block_type)) return BROTLI_FALSE;
    if (!SafeReadBlockLength(s, &s->block_length[tree_type], len_tree, br)) {
      s->substate_read_block_length = BROTLI_STATE_READ_BLOCK_LENGTH_NONE;
      BrotliBitReaderRestoreState(br, &memento);
      return BROTLI_FALSE;
    }
  }

  if (block_type == 1) {
    block_type = ringbuffer[1] + 1;
  } else if (block_type == 0) {
    block_type = ringbuffer[0];
  } else {
    block_type -= 2;
  }
  if (block_type >= max_block_type) {
    block_type -= max_block_type;
  }
  ringbuffer[0] = ringbuffer[1];
  ringbuffer[1] = block_type;
  return BROTLI_TRUE;
}

static BROTLI_INLINE void DetectTrivialLiteralBlockTypes(
    BrotliDecoderState* s) {
  size_t i;
  for (i = 0; i < 8; ++i) s->trivial_literal_contexts[i] = 0;
  for (i = 0; i < s->num_block_types[0]; i++) {
    size_t offset = i << BROTLI_LITERAL_CONTEXT_BITS;
    size_t error = 0;
    size_t sample = s->context_map[offset];
    size_t j;
    for (j = 0; j < (1u << BROTLI_LITERAL_CONTEXT_BITS);) {
      /* NOLINTNEXTLINE(bugprone-macro-repeated-side-effects) */
      BROTLI_REPEAT_4({ error |= s->context_map[offset + j++] ^ sample; })
    }
    if (error == 0) {
      s->trivial_literal_contexts[i >> 5] |= 1u << (i & 31);
    }
  }
}

static BROTLI_INLINE void PrepareLiteralDecoding(BrotliDecoderState* s) {
  uint8_t context_mode;
  size_t trivial;
  brotli_reg_t block_type = s->block_type_rb[1];
  brotli_reg_t context_offset = block_type << BROTLI_LITERAL_CONTEXT_BITS;
  s->context_map_slice = s->context_map + context_offset;
  trivial = s->trivial_literal_contexts[block_type >> 5];
  s->trivial_literal_context = (trivial >> (block_type & 31)) & 1;
  s->literal_htree = s->literal_hgroup.htrees[s->context_map_slice[0]];
  context_mode = s->context_modes[block_type] & 3;
  s->context_lookup = BROTLI_CONTEXT_LUT(context_mode);
}

/* Decodes the block type and updates the state for literal context.
   Reads 3..54 bits. */
static BROTLI_INLINE BROTLI_BOOL DecodeLiteralBlockSwitchInternal(
    int safe, BrotliDecoderState* s) {
  if (!DecodeBlockTypeAndLength(safe, s, 0)) {
    return BROTLI_FALSE;
  }
  PrepareLiteralDecoding(s);
  return BROTLI_TRUE;
}

static void BROTLI_NOINLINE DecodeLiteralBlockSwitch(BrotliDecoderState* s) {
  DecodeLiteralBlockSwitchInternal(0, s);
}

static BROTLI_BOOL BROTLI_NOINLINE SafeDecodeLiteralBlockSwitch(
    BrotliDecoderState* s) {
  return DecodeLiteralBlockSwitchInternal(1, s);
}

/* Block switch for insert/copy length.
   Reads 3..54 bits. */
static BROTLI_INLINE BROTLI_BOOL DecodeCommandBlockSwitchInternal(
    int safe, BrotliDecoderState* s) {
  if (!DecodeBlockTypeAndLength(safe, s, 1)) {
    return BROTLI_FALSE;
  }
  s->htree_command = s->insert_copy_hgroup.htrees[s->block_type_rb[3]];
  return BROTLI_TRUE;
}

static void BROTLI_NOINLINE DecodeCommandBlockSwitch(BrotliDecoderState* s) {
  DecodeCommandBlockSwitchInternal(0, s);
}

static BROTLI_BOOL BROTLI_NOINLINE SafeDecodeCommandBlockSwitch(
    BrotliDecoderState* s) {
  return DecodeCommandBlockSwitchInternal(1, s);
}

/* Block switch for distance codes.
   Reads 3..54 bits. */
static BROTLI_INLINE BROTLI_BOOL DecodeDistanceBlockSwitchInternal(
    int safe, BrotliDecoderState* s) {
  if (!DecodeBlockTypeAndLength(safe, s, 2)) {
    return BROTLI_FALSE;
  }
  s->dist_context_map_slice = s->dist_context_map +
      (s->block_type_rb[5] << BROTLI_DISTANCE_CONTEXT_BITS);
  s->dist_htree_index = s->dist_context_map_slice[s->distance_context];
  return BROTLI_TRUE;
}

static void BROTLI_NOINLINE DecodeDistanceBlockSwitch(BrotliDecoderState* s) {
  DecodeDistanceBlockSwitchInternal(0, s);
}

static BROTLI_BOOL BROTLI_NOINLINE SafeDecodeDistanceBlockSwitch(
    BrotliDecoderState* s) {
  return DecodeDistanceBlockSwitchInternal(1, s);
}

static size_t UnwrittenBytes(const BrotliDecoderState* s, BROTLI_BOOL wrap) {
  size_t pos = wrap && s->pos > s->ringbuffer_size ?
      (size_t)s->ringbuffer_size : (size_t)(s->pos);
  size_t partial_pos_rb = (s->rb_roundtrips * (size_t)s->ringbuffer_size) + pos;
  return partial_pos_rb - s->partial_pos_out;
}

/* Dumps output.
   Returns BROTLI_DECODER_NEEDS_MORE_OUTPUT only if there is more output to push
   and either ring-buffer is as big as window size, or |force| is true. */
static BrotliDecoderErrorCode BROTLI_NOINLINE WriteRingBuffer(
    BrotliDecoderState* s, size_t* available_out, uint8_t** next_out,
    size_t* total_out, BROTLI_BOOL force) {
  uint8_t* start =
      s->ringbuffer + (s->partial_pos_out & (size_t)s->ringbuffer_mask);
  size_t to_write = UnwrittenBytes(s, BROTLI_TRUE);
  size_t num_written = *available_out;
  if (num_written > to_write) {
    num_written = to_write;
  }
  if (s->meta_block_remaining_len < 0) {
    return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_BLOCK_LENGTH_1);
  }
  if (next_out && !*next_out) {
    *next_out = start;
  } else {
    if (next_out) {
      memcpy(*next_out, start, num_written);
      *next_out += num_written;
    }
  }
  *available_out -= num_written;
  BROTLI_LOG_UINT(to_write);
  BROTLI_LOG_UINT(num_written);
  s->partial_pos_out += num_written;
  if (total_out) {
    *total_out = s->partial_pos_out;
  }
  if (num_written < to_write) {
    if (s->ringbuffer_size == (1 << s->window_bits) || force) {
      return BROTLI_DECODER_NEEDS_MORE_OUTPUT;
    } else {
      return BROTLI_DECODER_SUCCESS;
    }
  }
  /* Wrap ring buffer only if it has reached its maximal size. */
  if (s->ringbuffer_size == (1 << s->window_bits) &&
      s->pos >= s->ringbuffer_size) {
    s->pos -= s->ringbuffer_size;
    s->rb_roundtrips++;
    s->should_wrap_ringbuffer = (size_t)s->pos != 0 ? 1 : 0;
  }
  return BROTLI_DECODER_SUCCESS;
}

static void BROTLI_NOINLINE WrapRingBuffer(BrotliDecoderState* s) {
  if (s->should_wrap_ringbuffer) {
    memcpy(s->ringbuffer, s->ringbuffer_end, (size_t)s->pos);
    s->should_wrap_ringbuffer = 0;
  }
}

/* Allocates ring-buffer.

   s->ringbuffer_size MUST be updated by BrotliCalculateRingBufferSize before
   this function is called.

   Last two bytes of ring-buffer are initialized to 0, so context calculation
   could be done uniformly for the first two and all other positions. */
static BROTLI_BOOL BROTLI_NOINLINE BrotliEnsureRingBuffer(
    BrotliDecoderState* s) {
  uint8_t* old_ringbuffer = s->ringbuffer;
  if (s->ringbuffer_size == s->new_ringbuffer_size) {
    return BROTLI_TRUE;
  }

  s->ringbuffer = (uint8_t*)BROTLI_DECODER_ALLOC(s,
      (size_t)(s->new_ringbuffer_size) + kRingBufferWriteAheadSlack);
  if (s->ringbuffer == 0) {
    /* Restore previous value. */
    s->ringbuffer = old_ringbuffer;
    return BROTLI_FALSE;
  }
  s->ringbuffer[s->new_ringbuffer_size - 2] = 0;
  s->ringbuffer[s->new_ringbuffer_size - 1] = 0;

  if (!!old_ringbuffer) {
    memcpy(s->ringbuffer, old_ringbuffer, (size_t)s->pos);
    BROTLI_DECODER_FREE(s, old_ringbuffer);
  }

  s->ringbuffer_size = s->new_ringbuffer_size;
  s->ringbuffer_mask = s->new_ringbuffer_size - 1;
  s->ringbuffer_end = s->ringbuffer + s->ringbuffer_size;

  return BROTLI_TRUE;
}

static BrotliDecoderErrorCode BROTLI_NOINLINE
SkipMetadataBlock(BrotliDecoderState* s) {
  BrotliBitReader* br = &s->br;
  int nbytes;

  if (s->meta_block_remaining_len == 0) {
    return BROTLI_DECODER_SUCCESS;
  }

  BROTLI_DCHECK((BrotliGetAvailableBits(br) & 7) == 0);

  /* Drain accumulator. */
  if (BrotliGetAvailableBits(br) >= 8) {
    uint8_t buffer[8];
    nbytes = (int)(BrotliGetAvailableBits(br)) >> 3;
    BROTLI_DCHECK(nbytes <= 8);
    if (nbytes > s->meta_block_remaining_len) {
      nbytes = s->meta_block_remaining_len;
    }
    BrotliCopyBytes(buffer, br, (size_t)nbytes);
    if (s->metadata_chunk_func) {
      s->metadata_chunk_func(s->metadata_callback_opaque, buffer,
                             (size_t)nbytes);
    }
    s->meta_block_remaining_len -= nbytes;
    if (s->meta_block_remaining_len == 0) {
      return BROTLI_DECODER_SUCCESS;
    }
  }

  /* Direct access to metadata is possible. */
  nbytes = (int)BrotliGetRemainingBytes(br);
  if (nbytes > s->meta_block_remaining_len) {
    nbytes = s->meta_block_remaining_len;
  }
  if (nbytes > 0) {
    if (s->metadata_chunk_func) {
      s->metadata_chunk_func(s->metadata_callback_opaque, br->next_in,
                             (size_t)nbytes);
    }
    BrotliDropBytes(br, (size_t)nbytes);
    s->meta_block_remaining_len -= nbytes;
    if (s->meta_block_remaining_len == 0) {
      return BROTLI_DECODER_SUCCESS;
    }
  }

  BROTLI_DCHECK(BrotliGetRemainingBytes(br) == 0);

  return BROTLI_DECODER_NEEDS_MORE_INPUT;
}

static BrotliDecoderErrorCode BROTLI_NOINLINE CopyUncompressedBlockToOutput(
    size_t* available_out, uint8_t** next_out, size_t* total_out,
    BrotliDecoderState* s) {
  /* TODO(eustas): avoid allocation for single uncompressed block. */
  if (!BrotliEnsureRingBuffer(s)) {
    return BROTLI_FAILURE(BROTLI_DECODER_ERROR_ALLOC_RING_BUFFER_1);
  }

  /* State machine */
  for (;;) {
    switch (s->substate_uncompressed) {
      case BROTLI_STATE_UNCOMPRESSED_NONE: {
        int nbytes = (int)BrotliGetRemainingBytes(&s->br);
        if (nbytes > s->meta_block_remaining_len) {
          nbytes = s->meta_block_remaining_len;
        }
        if (s->pos + nbytes > s->ringbuffer_size) {
          nbytes = s->ringbuffer_size - s->pos;
        }
        /* Copy remaining bytes from s->br.buf_ to ring-buffer. */
        BrotliCopyBytes(&s->ringbuffer[s->pos], &s->br, (size_t)nbytes);
        s->pos += nbytes;
        s->meta_block_remaining_len -= nbytes;
        if (s->pos < 1 << s->window_bits) {
          if (s->meta_block_remaining_len == 0) {
            return BROTLI_DECODER_SUCCESS;
          }
          return BROTLI_DECODER_NEEDS_MORE_INPUT;
        }
        s->substate_uncompressed = BROTLI_STATE_UNCOMPRESSED_WRITE;
      }
      /* Fall through. */

      case BROTLI_STATE_UNCOMPRESSED_WRITE: {
        BrotliDecoderErrorCode result;
        result = WriteRingBuffer(
            s, available_out, next_out, total_out, BROTLI_FALSE);
        if (result != BROTLI_DECODER_SUCCESS) {
          return result;
        }
        if (s->ringbuffer_size == 1 << s->window_bits) {
          s->max_distance = s->max_backward_distance;
        }
        s->substate_uncompressed = BROTLI_STATE_UNCOMPRESSED_NONE;
        break;
      }
    }
  }
  BROTLI_DCHECK(0);  /* Unreachable */
}

static BROTLI_BOOL AttachCompoundDictionary(
    BrotliDecoderState* state, const uint8_t* data, size_t size) {
  BrotliDecoderCompoundDictionary* addon = state->compound_dictionary;
  if (state->state != BROTLI_STATE_UNINITED) return BROTLI_FALSE;
  if (!addon) {
    addon = (BrotliDecoderCompoundDictionary*)BROTLI_DECODER_ALLOC(
        state, sizeof(BrotliDecoderCompoundDictionary));
    if (!addon) return BROTLI_FALSE;
    addon->num_chunks = 0;
    addon->total_size = 0;
    addon->br_length = 0;
    addon->br_copied = 0;
    addon->block_bits = -1;
    addon->chunk_offsets[0] = 0;
    state->compound_dictionary = addon;
  }
  if (addon->num_chunks == 15) return BROTLI_FALSE;
  addon->chunks[addon->num_chunks] = data;
  addon->num_chunks++;
  addon->total_size += (int)size;
  addon->chunk_offsets[addon->num_chunks] = addon->total_size;
  return BROTLI_TRUE;
}

static void EnsureCompoundDictionaryInitialized(BrotliDecoderState* state) {
  BrotliDecoderCompoundDictionary* addon = state->compound_dictionary;
  /* 256 = (1 << 8) slots in block map. */
  int block_bits = 8;
  int cursor = 0;
  int index = 0;
  if (addon->block_bits != -1) return;
  while (((addon->total_size - 1) >> block_bits) != 0) block_bits++;
  block_bits -= 8;
  addon->block_bits = block_bits;
  while (cursor < addon->total_size) {
    while (addon->chunk_offsets[index + 1] < cursor) index++;
    addon->block_map[cursor >> block_bits] = (uint8_t)index;
    cursor += 1 << block_bits;
  }
}

static BROTLI_BOOL InitializeCompoundDictionaryCopy(BrotliDecoderState* s,
    int address, int length) {
  BrotliDecoderCompoundDictionary* addon = s->compound_dictionary;
  int index;
  EnsureCompoundDictionaryInitialized(s);
  index = addon->block_map[address >> addon->block_bits];
  while (address >= addon->chunk_offsets[index + 1]) index++;
  if (addon->total_size < address + length) return BROTLI_FALSE;
  /* Update the recent distances cache. */
  s->dist_rb[s->dist_rb_idx & 3] = s->distance_code;
  ++s->dist_rb_idx;
  s->meta_block_remaining_len -= length;
  addon->br_index = index;
  addon->br_offset = address - addon->chunk_offsets[index];
  addon->br_length = length;
  addon->br_copied = 0;
  return BROTLI_TRUE;
}

static int GetCompoundDictionarySize(BrotliDecoderState* s) {
  return s->compound_dictionary ? s->compound_dictionary->total_size : 0;
}

static int CopyFromCompoundDictionary(BrotliDecoderState* s, int pos) {
  BrotliDecoderCompoundDictionary* addon = s->compound_dictionary;
  int orig_pos = pos;
  while (addon->br_length != addon->br_copied) {
    uint8_t* copy_dst = &s->ringbuffer[pos];
    const uint8_t* copy_src =
        addon->chunks[addon->br_index] + addon->br_offset;
    int space = s->ringbuffer_size - pos;
    int rem_chunk_length = (addon->chunk_offsets[addon->br_index + 1] -
        addon->chunk_offsets[addon->br_index]) - addon->br_offset;
    int length = addon->br_length - addon->br_copied;
    if (length > rem_chunk_length) length = rem_chunk_length;
    if (length > space) length = space;
    memcpy(copy_dst, copy_src, (size_t)length);
    pos += length;
    addon->br_offset += length;
    addon->br_copied += length;
    if (length == rem_chunk_length) {
      addon->br_index++;
      addon->br_offset = 0;
    }
    if (pos == s->ringbuffer_size) break;
  }
  return pos - orig_pos;
}

BROTLI_BOOL BrotliDecoderAttachDictionary(
    BrotliDecoderState* state, BrotliSharedDictionaryType type,
    size_t data_size, const uint8_t data[BROTLI_ARRAY_PARAM(data_size)]) {
  brotli_reg_t i;
  brotli_reg_t num_prefix_before = state->dictionary->num_prefix;
  if (state->state != BROTLI_STATE_UNINITED) return BROTLI_FALSE;
  if (!BrotliSharedDictionaryAttach(state->dictionary, type, data_size, data)) {
    return BROTLI_FALSE;
  }
  for (i = num_prefix_before; i < state->dictionary->num_prefix; i++) {
    if (!AttachCompoundDictionary(
        state, state->dictionary->prefix[i],
        state->dictionary->prefix_size[i])) {
      return BROTLI_FALSE;
    }
  }
  return BROTLI_TRUE;
}

/* Calculates the smallest feasible ring buffer.

   If we know the data size is small, do not allocate more ring buffer
   size than needed to reduce memory usage.

   When this method is called, metablock size and flags MUST be decoded. */
static void BROTLI_NOINLINE BrotliCalculateRingBufferSize(
    BrotliDecoderState* s) {
  int window_size = 1 << s->window_bits;
  int new_ringbuffer_size = window_size;
  /* We need at least 2 bytes of ring buffer size to get the last two
     bytes for context from there */
  int min_size = s->ringbuffer_size ? s->ringbuffer_size : 1024;
  int output_size;

  /* If maximum is already reached, no further extension is retired. */
  if (s->ringbuffer_size == window_size) {
    return;
  }

  /* Metadata blocks does not touch ring buffer. */
  if (s->is_metadata) {
    return;
  }

  if (!s->ringbuffer) {
    output_size = 0;
  } else {
    output_size = s->pos;
  }
  output_size += s->meta_block_remaining_len;
  min_size = min_size < output_size ? output_size : min_size;

  if (!!s->canny_ringbuffer_allocation) {
    /* Reduce ring buffer size to save memory when server is unscrupulous.
       In worst case memory usage might be 1.5x bigger for a short period of
       ring buffer reallocation. */
    while ((new_ringbuffer_size >> 1) >= min_size) {
      new_ringbuffer_size >>= 1;
    }
  }

  s->new_ringbuffer_size = new_ringbuffer_size;
}

/* Reads 1..256 2-bit context modes. */
static BrotliDecoderErrorCode ReadContextModes(BrotliDecoderState* s) {
  BrotliBitReader* br = &s->br;
  int i = s->loop_counter;

  while (i < (int)s->num_block_types[0]) {
    brotli_reg_t bits;
    if (!BrotliSafeReadBits(br, 2, &bits)) {
      s->loop_counter = i;
      return BROTLI_DECODER_NEEDS_MORE_INPUT;
    }
    s->context_modes[i] = (uint8_t)bits;
    BROTLI_LOG_ARRAY_INDEX(s->context_modes, i);
    i++;
  }
  return BROTLI_DECODER_SUCCESS;
}

static BROTLI_INLINE void TakeDistanceFromRingBuffer(BrotliDecoderState* s) {
  int offset = s->distance_code - 3;
  if (s->distance_code <= 3) {
    /* Compensate double distance-ring-buffer roll for dictionary items. */
    s->distance_context = 1 >> s->distance_code;
    s->distance_code = s->dist_rb[(s->dist_rb_idx - offset) & 3];
    s->dist_rb_idx -= s->distance_context;
  } else {
    int index_delta = 3;
    int delta;
    int base = s->distance_code - 10;
    if (s->distance_code < 10) {
      base = s->distance_code - 4;
    } else {
      index_delta = 2;
    }
    /* Unpack one of six 4-bit values. */
    delta = ((0x605142 >> (4 * base)) & 0xF) - 3;
    s->distance_code = s->dist_rb[(s->dist_rb_idx + index_delta) & 0x3] + delta;
    if (s->distance_code <= 0) {
      /* A huge distance will cause a BROTLI_FAILURE() soon.
         This is a little faster than failing here. */
      s->distance_code = 0x7FFFFFFF;
    }
  }
}

static BROTLI_INLINE BROTLI_BOOL SafeReadBits(
    BrotliBitReader* const br, brotli_reg_t n_bits, brotli_reg_t* val) {
  if (n_bits != 0) {
    return BrotliSafeReadBits(br, n_bits, val);
  } else {
    *val = 0;
    return BROTLI_TRUE;
  }
}

static BROTLI_INLINE BROTLI_BOOL SafeReadBits32(
    BrotliBitReader* const br, brotli_reg_t n_bits, brotli_reg_t* val) {
  if (n_bits != 0) {
    return BrotliSafeReadBits32(br, n_bits, val);
  } else {
    *val = 0;
    return BROTLI_TRUE;
  }
}

/*
   RFC 7932 Section 4 with "..." shortenings and "[]" emendations.

   Each distance ... is represented with a pair <distance code, extra bits>...
   The distance code is encoded using a prefix code... The number of extra bits
   can be 0..24... Two additional parameters: NPOSTFIX (0..3), and ...
   NDIRECT (0..120) ... are encoded in the meta-block header...

   The first 16 distance symbols ... reference past distances... ring buffer ...
   Next NDIRECT distance symbols ... represent distances from 1 to NDIRECT...
   [For] distance symbols 16 + NDIRECT and greater ... the number of extra bits
   ... is given by the following formula:

   [ xcode = dcode - NDIRECT - 16 ]
   ndistbits = 1 + [ xcode ] >> (NPOSTFIX + 1)

   ...
*/

/*
   RFC 7932 Section 9.2 with "..." shortenings and "[]" emendations.

   ... to get the actual value of the parameter NDIRECT, left-shift this
   four-bit number by NPOSTFIX bits ...
*/

/* Remaining formulas from RFC 7932 Section 4 could be rewritten as following:

     alphabet_size = 16 + NDIRECT + (max_distbits << (NPOSTFIX + 1))

     half = ((xcode >> NPOSTFIX) & 1) << ndistbits
     postfix = xcode & ((1 << NPOSTFIX) - 1)
     range_start = 2 * (1 << ndistbits - 1 - 1)

     distance = (range_start + half + extra) << NPOSTFIX + postfix + NDIRECT + 1

   NB: ndistbits >= 1 -> range_start >= 0
   NB: range_start has factor 2, as the range is covered by 2 "halves"
   NB: extra -1 offset in range_start formula covers the absence of
       ndistbits = 0 case
   NB: when NPOSTFIX = 0, NDIRECT is not greater than 15

   In other words, xcode has the following binary structure - XXXHPPP:
    - XXX represent the number of extra distance bits
    - H selects upper / lower range of distances
    - PPP represent "postfix"

  "Regular" distance encoding has NPOSTFIX = 0; omitting the postfix part
  simplifies distance calculation.

  Using NPOSTFIX > 0 allows cheaper encoding of regular structures, e.g. where
  most of distances have the same reminder of division by 2/4/8. For example,
  the table of int32_t values that come from different sources; if it is likely
  that 3 highest bytes of values from the same source are the same, then
  copy distance often looks like 4x + y.

  Distance calculation could be rewritten to:

    ndistbits = NDISTBITS(NDIRECT, NPOSTFIX)[dcode]
    distance = OFFSET(NDIRECT, NPOSTFIX)[dcode] + extra << NPOSTFIX

  NDISTBITS and OFFSET could be pre-calculated, as NDIRECT and NPOSTFIX could
  change only once per meta-block.
*/

/* Calculates distance lookup table.
   NB: it is possible to have all 64 tables precalculated. */
static void CalculateDistanceLut(BrotliDecoderState* s) {
  BrotliMetablockBodyArena* b = &s->arena.body;
  brotli_reg_t npostfix = s->distance_postfix_bits;
  brotli_reg_t ndirect = s->num_direct_distance_codes;
  brotli_reg_t alphabet_size_limit = s->distance_hgroup.alphabet_size_limit;
  brotli_reg_t postfix = (brotli_reg_t)1u << npostfix;
  brotli_reg_t j;
  brotli_reg_t bits = 1;
  brotli_reg_t half = 0;

  /* Skip short codes. */
  brotli_reg_t i = BROTLI_NUM_DISTANCE_SHORT_CODES;

  /* Fill direct codes. */
  for (j = 0; j < ndirect; ++j) {
    b->dist_extra_bits[i] = 0;
    b->dist_offset[i] = j + 1;
    ++i;
  }

  /* Fill regular distance codes. */
  while (i < alphabet_size_limit) {
    brotli_reg_t base = ndirect + ((((2 + half) << bits) - 4) << npostfix) + 1;
    /* Always fill the complete group. */
    for (j = 0; j < postfix; ++j) {
      b->dist_extra_bits[i] = (uint8_t)bits;
      b->dist_offset[i] = base + j;
      ++i;
    }
    bits = bits + half;
    half = half ^ 1;
  }
}

/* Precondition: s->distance_code < 0. */
static BROTLI_INLINE BROTLI_BOOL ReadDistanceInternal(
    int safe, BrotliDecoderState* s, BrotliBitReader* br) {
  BrotliMetablockBodyArena* b = &s->arena.body;
  brotli_reg_t code;
  brotli_reg_t bits;
  BrotliBitReaderState memento;
  HuffmanCode* distance_tree = s->distance_hgroup.htrees[s->dist_htree_index];
  if (!safe) {
    code = ReadSymbol(distance_tree, br);
  } else {
    BrotliBitReaderSaveState(br, &memento);
    if (!SafeReadSymbol(distance_tree, br, &code)) {
      return BROTLI_FALSE;
    }
  }
  --s->block_length[2];
  /* Convert the distance code to the actual distance by possibly
     looking up past distances from the s->dist_rb. */
  s->distance_context = 0;
  if ((code & ~0xFu) == 0) {
    s->distance_code = (int)code;
    TakeDistanceFromRingBuffer(s);
    return BROTLI_TRUE;
  }
  if (!safe) {
    bits = BrotliReadBits32(br, b->dist_extra_bits[code]);
  } else {
    if (!SafeReadBits32(br, b->dist_extra_bits[code], &bits)) {
      ++s->block_length[2];
      BrotliBitReaderRestoreState(br, &memento);
      return BROTLI_FALSE;
    }
  }
  s->distance_code =
      (int)(b->dist_offset[code] + (bits << s->distance_postfix_bits));
  return BROTLI_TRUE;
}

static BROTLI_INLINE void ReadDistance(
    BrotliDecoderState* s, BrotliBitReader* br) {
  ReadDistanceInternal(0, s, br);
}

static BROTLI_INLINE BROTLI_BOOL SafeReadDistance(
    BrotliDecoderState* s, BrotliBitReader* br) {
  return ReadDistanceInternal(1, s, br);
}

static BROTLI_INLINE BROTLI_BOOL ReadCommandInternal(
    int safe, BrotliDecoderState* s, BrotliBitReader* br, int* insert_length) {
  brotli_reg_t cmd_code;
  brotli_reg_t insert_len_extra = 0;
  brotli_reg_t copy_length;
  CmdLutElement v;
  BrotliBitReaderState memento;
  if (!safe) {
    cmd_code = ReadSymbol(s->htree_command, br);
  } else {
    BrotliBitReaderSaveState(br, &memento);
    if (!SafeReadSymbol(s->htree_command, br, &cmd_code)) {
      return BROTLI_FALSE;
    }
  }
  v = kCmdLut[cmd_code];
  s->distance_code = v.distance_code;
  s->distance_context = v.context;
  s->dist_htree_index = s->dist_context_map_slice[s->distance_context];
  *insert_length = v.insert_len_offset;
  if (!safe) {
    if (BROTLI_PREDICT_FALSE(v.insert_len_extra_bits != 0)) {
      insert_len_extra = BrotliReadBits24(br, v.insert_len_extra_bits);
    }
    copy_length = BrotliReadBits24(br, v.copy_len_extra_bits);
  } else {
    if (!SafeReadBits(br, v.insert_len_extra_bits, &insert_len_extra) ||
        !SafeReadBits(br, v.copy_len_extra_bits, &copy_length)) {
      BrotliBitReaderRestoreState(br, &memento);
      return BROTLI_FALSE;
    }
  }
  s->copy_length = (int)copy_length + v.copy_len_offset;
  --s->block_length[1];
  *insert_length += (int)insert_len_extra;
  return BROTLI_TRUE;
}

static BROTLI_INLINE void ReadCommand(
    BrotliDecoderState* s, BrotliBitReader* br, int* insert_length) {
  ReadCommandInternal(0, s, br, insert_length);
}

static BROTLI_INLINE BROTLI_BOOL SafeReadCommand(
    BrotliDecoderState* s, BrotliBitReader* br, int* insert_length) {
  return ReadCommandInternal(1, s, br, insert_length);
}

static BROTLI_INLINE BROTLI_BOOL CheckInputAmount(
    int safe, BrotliBitReader* const br) {
  if (safe) {
    return BROTLI_TRUE;
  }
  return BrotliCheckInputAmount(br);
}

#define BROTLI_SAFE(METHOD)                       \
  {                                               \
    if (safe) {                                   \
      if (!Safe##METHOD) {                        \
        result = BROTLI_DECODER_NEEDS_MORE_INPUT; \
        goto saveStateAndReturn;                  \
      }                                           \
    } else {                                      \
      METHOD;                                     \
    }                                             \
  }

static BROTLI_INLINE BrotliDecoderErrorCode ProcessCommandsInternal(
    int safe, BrotliDecoderState* s) {
  int pos = s->pos;
  int i = s->loop_counter;
  BrotliDecoderErrorCode result = BROTLI_DECODER_SUCCESS;
  BrotliBitReader* br = &s->br;
  int compound_dictionary_size = GetCompoundDictionarySize(s);

  if (!CheckInputAmount(safe, br)) {
    result = BROTLI_DECODER_NEEDS_MORE_INPUT;
    goto saveStateAndReturn;
  }
  if (!safe) {
    BROTLI_UNUSED(BrotliWarmupBitReader(br));
  }

  /* Jump into state machine. */
  if (s->state == BROTLI_STATE_COMMAND_BEGIN) {
    goto CommandBegin;
  } else if (s->state == BROTLI_STATE_COMMAND_INNER) {
    goto CommandInner;
  } else if (s->state == BROTLI_STATE_COMMAND_POST_DECODE_LITERALS) {
    goto CommandPostDecodeLiterals;
  } else if (s->state == BROTLI_STATE_COMMAND_POST_WRAP_COPY) {
    goto CommandPostWrapCopy;
  } else {
    return BROTLI_FAILURE(BROTLI_DECODER_ERROR_UNREACHABLE);  /* COV_NF_LINE */
  }

CommandBegin:
  if (safe) {
    s->state = BROTLI_STATE_COMMAND_BEGIN;
  }
  if (!CheckInputAmount(safe, br)) {
    s->state = BROTLI_STATE_COMMAND_BEGIN;
    result = BROTLI_DECODER_NEEDS_MORE_INPUT;
    goto saveStateAndReturn;
  }
  if (BROTLI_PREDICT_FALSE(s->block_length[1] == 0)) {
    BROTLI_SAFE(DecodeCommandBlockSwitch(s));
    goto CommandBegin;
  }
  /* Read the insert/copy length in the command. */
  BROTLI_SAFE(ReadCommand(s, br, &i));
  BROTLI_LOG(("[ProcessCommandsInternal] pos = %d insert = %d copy = %d\n",
              pos, i, s->copy_length));
  if (i == 0) {
    goto CommandPostDecodeLiterals;
  }
  s->meta_block_remaining_len -= i;

CommandInner:
  if (safe) {
    s->state = BROTLI_STATE_COMMAND_INNER;
  }
  /* Read the literals in the command. */
  if (s->trivial_literal_context) {
    brotli_reg_t bits;
    brotli_reg_t value;
    PreloadSymbol(safe, s->literal_htree, br, &bits, &value);
    if (!safe) {
      // This is a hottest part of the decode, so we copy the loop below
      // and optimize it by calculating the number of steps where all checks
      // evaluate to false (ringbuffer size/block size/input size).
      // Since all checks are loop invariant, we just need to find
      // minimal number of iterations for a simple loop, and run
      // the full version for the remainder.
      int num_steps = i - 1;
      if (num_steps > 0 && ((brotli_reg_t)(num_steps) > s->block_length[0])) {
        // Safe cast, since block_length < steps
        num_steps = (int)s->block_length[0];
      }
      if (s->ringbuffer_size >= pos &&
          (s->ringbuffer_size - pos) <= num_steps) {
        num_steps = s->ringbuffer_size - pos - 1;
      }
      if (num_steps < 0) {
        num_steps = 0;
      }
      num_steps = BrotliCopyPreloadedSymbolsToU8(s->literal_htree, br, &bits,
                                                 &value, s->ringbuffer, pos,
                                                 num_steps);
      pos += num_steps;
      s->block_length[0] -= (brotli_reg_t)num_steps;
      i -= num_steps;
      do {
        if (!CheckInputAmount(safe, br)) {
          s->state = BROTLI_STATE_COMMAND_INNER;
          result = BROTLI_DECODER_NEEDS_MORE_INPUT;
          goto saveStateAndReturn;
        }
        if (BROTLI_PREDICT_FALSE(s->block_length[0] == 0)) {
          goto NextLiteralBlock;
        }
        BrotliCopyPreloadedSymbolsToU8(s->literal_htree, br, &bits, &value,
                                       s->ringbuffer, pos, 1);
        --s->block_length[0];
        BROTLI_LOG_ARRAY_INDEX(s->ringbuffer, pos);
        ++pos;
        if (BROTLI_PREDICT_FALSE(pos == s->ringbuffer_size)) {
          s->state = BROTLI_STATE_COMMAND_INNER_WRITE;
          --i;
          goto saveStateAndReturn;
        }
      } while (--i != 0);
    } else { /* safe */
      do {
        if (BROTLI_PREDICT_FALSE(s->block_length[0] == 0)) {
          goto NextLiteralBlock;
        }
        brotli_reg_t literal;
        if (!SafeReadSymbol(s->literal_htree, br, &literal)) {
          result = BROTLI_DECODER_NEEDS_MORE_INPUT;
          goto saveStateAndReturn;
        }
        s->ringbuffer[pos] = (uint8_t)literal;
        --s->block_length[0];
        BROTLI_LOG_ARRAY_INDEX(s->ringbuffer, pos);
        ++pos;
        if (BROTLI_PREDICT_FALSE(pos == s->ringbuffer_size)) {
          s->state = BROTLI_STATE_COMMAND_INNER_WRITE;
          --i;
          goto saveStateAndReturn;
        }
      } while (--i != 0);
    }
  } else {
    uint8_t p1 = s->ringbuffer[(pos - 1) & s->ringbuffer_mask];
    uint8_t p2 = s->ringbuffer[(pos - 2) & s->ringbuffer_mask];
    do {
      const HuffmanCode* hc;
      uint8_t context;
      if (!CheckInputAmount(safe, br)) {
        s->state = BROTLI_STATE_COMMAND_INNER;
        result = BROTLI_DECODER_NEEDS_MORE_INPUT;
        goto saveStateAndReturn;
      }
      if (BROTLI_PREDICT_FALSE(s->block_length[0] == 0)) {
        goto NextLiteralBlock;
      }
      context = BROTLI_CONTEXT(p1, p2, s->context_lookup);
      BROTLI_LOG_UINT(context);
      hc = s->literal_hgroup.htrees[s->context_map_slice[context]];
      p2 = p1;
      if (!safe) {
        p1 = (uint8_t)ReadSymbol(hc, br);
      } else {
        brotli_reg_t literal;
        if (!SafeReadSymbol(hc, br, &literal)) {
          result = BROTLI_DECODER_NEEDS_MORE_INPUT;
          goto saveStateAndReturn;
        }
        p1 = (uint8_t)literal;
      }
      s->ringbuffer[pos] = p1;
      --s->block_length[0];
      BROTLI_LOG_UINT(s->context_map_slice[context]);
      BROTLI_LOG_ARRAY_INDEX(s->ringbuffer, pos & s->ringbuffer_mask);
      ++pos;
      if (BROTLI_PREDICT_FALSE(pos == s->ringbuffer_size)) {
        s->state = BROTLI_STATE_COMMAND_INNER_WRITE;
        --i;
        goto saveStateAndReturn;
      }
    } while (--i != 0);
  }
  BROTLI_LOG_UINT(s->meta_block_remaining_len);
  if (BROTLI_PREDICT_FALSE(s->meta_block_remaining_len <= 0)) {
    s->state = BROTLI_STATE_METABLOCK_DONE;
    goto saveStateAndReturn;
  }

CommandPostDecodeLiterals:
  if (safe) {
    s->state = BROTLI_STATE_COMMAND_POST_DECODE_LITERALS;
  }
  if (s->distance_code >= 0) {
    /* Implicit distance case. */
    s->distance_context = s->distance_code ? 0 : 1;
    --s->dist_rb_idx;
    s->distance_code = s->dist_rb[s->dist_rb_idx & 3];
  } else {
    /* Read distance code in the command, unless it was implicitly zero. */
    if (BROTLI_PREDICT_FALSE(s->block_length[2] == 0)) {
      BROTLI_SAFE(DecodeDistanceBlockSwitch(s));
    }
    BROTLI_SAFE(ReadDistance(s, br));
  }
  BROTLI_LOG(("[ProcessCommandsInternal] pos = %d distance = %d\n",
              pos, s->distance_code));
  if (s->max_distance != s->max_backward_distance) {
    s->max_distance =
        (pos < s->max_backward_distance) ? pos : s->max_backward_distance;
  }
  i = s->copy_length;
  /* Apply copy of LZ77 back-reference, or static dictionary reference if
     the distance is larger than the max LZ77 distance */
  if (s->distance_code > s->max_distance) {
    /* The maximum allowed distance is BROTLI_MAX_ALLOWED_DISTANCE = 0x7FFFFFFC.
       With this choice, no signed overflow can occur after decoding
       a special distance code (e.g., after adding 3 to the last distance). */
    if (s->distance_code > BROTLI_MAX_ALLOWED_DISTANCE) {
      BROTLI_LOG(("Invalid backward reference. pos: %d distance: %d "
          "len: %d bytes left: %d\n",
          pos, s->distance_code, i, s->meta_block_remaining_len));
      return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_DISTANCE);
    }
    if (s->distance_code - s->max_distance - 1 < compound_dictionary_size) {
      int address = compound_dictionary_size -
          (s->distance_code - s->max_distance);
      if (!InitializeCompoundDictionaryCopy(s, address, i)) {
        return BROTLI_FAILURE(BROTLI_DECODER_ERROR_COMPOUND_DICTIONARY);
      }
      pos += CopyFromCompoundDictionary(s, pos);
      if (pos >= s->ringbuffer_size) {
        s->state = BROTLI_STATE_COMMAND_POST_WRITE_1;
        goto saveStateAndReturn;
      }
    } else if (i >= SHARED_BROTLI_MIN_DICTIONARY_WORD_LENGTH &&
               i <= SHARED_BROTLI_MAX_DICTIONARY_WORD_LENGTH) {
      uint8_t p1 = s->ringbuffer[(pos - 1) & s->ringbuffer_mask];
      uint8_t p2 = s->ringbuffer[(pos - 2) & s->ringbuffer_mask];
      uint8_t dict_id = s->dictionary->context_based ?
          s->dictionary->context_map[BROTLI_CONTEXT(p1, p2, s->context_lookup)]
          : 0;
      const BrotliDictionary* words = s->dictionary->words[dict_id];
      const BrotliTransforms* transforms = s->dictionary->transforms[dict_id];
      int offset = (int)words->offsets_by_length[i];
      brotli_reg_t shift = words->size_bits_by_length[i];
      int address =
          s->distance_code - s->max_distance - 1 - compound_dictionary_size;
      int mask = (int)BitMask(shift);
      int word_idx = address & mask;
      int transform_idx = address >> shift;
      /* Compensate double distance-ring-buffer roll. */
      s->dist_rb_idx += s->distance_context;
      offset += word_idx * i;
      /* If the distance is out of bound, select a next static dictionary if
         there exist multiple. */
      if ((transform_idx >= (int)transforms->num_transforms ||
          words->size_bits_by_length[i] == 0) &&
          s->dictionary->num_dictionaries > 1) {
        uint8_t dict_id2;
        int dist_remaining = address -
            (int)(((1u << shift) & ~1u)) * (int)transforms->num_transforms;
        for (dict_id2 = 0; dict_id2 < s->dictionary->num_dictionaries;
            dict_id2++) {
          const BrotliDictionary* words2 = s->dictionary->words[dict_id2];
          if (dict_id2 != dict_id && words2->size_bits_by_length[i] != 0) {
            const BrotliTransforms* transforms2 =
                s->dictionary->transforms[dict_id2];
            brotli_reg_t shift2 = words2->size_bits_by_length[i];
            int num = (int)((1u << shift2) & ~1u) *
                (int)transforms2->num_transforms;
            if (dist_remaining < num) {
              dict_id = dict_id2;
              words = words2;
              transforms = transforms2;
              address = dist_remaining;
              shift = shift2;
              mask = (int)BitMask(shift);
              word_idx = address & mask;
              transform_idx = address >> shift;
              offset = (int)words->offsets_by_length[i] + word_idx * i;
              break;
            }
            dist_remaining -= num;
          }
        }
      }
      if (BROTLI_PREDICT_FALSE(words->size_bits_by_length[i] == 0)) {
        BROTLI_LOG(("Invalid backward reference. pos: %d distance: %d "
            "len: %d bytes left: %d\n",
            pos, s->distance_code, i, s->meta_block_remaining_len));
        return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_DICTIONARY);
      }
      if (BROTLI_PREDICT_FALSE(!words->data)) {
        return BROTLI_FAILURE(BROTLI_DECODER_ERROR_DICTIONARY_NOT_SET);
      }
      if (transform_idx < (int)transforms->num_transforms) {
        const uint8_t* word = &words->data[offset];
        int len = i;
        if (transform_idx == transforms->cutOffTransforms[0]) {
          memcpy(&s->ringbuffer[pos], word, (size_t)len);
          BROTLI_LOG(("[ProcessCommandsInternal] dictionary word: [%.*s]\n",
                      len, word));
        } else {
          len = BrotliTransformDictionaryWord(&s->ringbuffer[pos], word, len,
              transforms, transform_idx);
          BROTLI_LOG(("[ProcessCommandsInternal] dictionary word: [%.*s],"
                      " transform_idx = %d, transformed: [%.*s]\n",
                      i, word, transform_idx, len, &s->ringbuffer[pos]));
          if (len == 0 && s->distance_code <= 120) {
            BROTLI_LOG(("Invalid length-0 dictionary word after transform\n"));
            return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_TRANSFORM);
          }
        }
        pos += len;
        s->meta_block_remaining_len -= len;
        if (pos >= s->ringbuffer_size) {
          s->state = BROTLI_STATE_COMMAND_POST_WRITE_1;
          goto saveStateAndReturn;
        }
      } else {
        BROTLI_LOG(("Invalid backward reference. pos: %d distance: %d "
            "len: %d bytes left: %d\n",
            pos, s->distance_code, i, s->meta_block_remaining_len));
        return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_TRANSFORM);
      }
    } else {
      BROTLI_LOG(("Invalid backward reference. pos: %d distance: %d "
          "len: %d bytes left: %d\n",
          pos, s->distance_code, i, s->meta_block_remaining_len));
      return BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_DICTIONARY);
    }
  } else {
    int src_start = (pos - s->distance_code) & s->ringbuffer_mask;
    uint8_t* copy_dst = &s->ringbuffer[pos];
    uint8_t* copy_src = &s->ringbuffer[src_start];
    int dst_end = pos + i;
    int src_end = src_start + i;
    /* Update the recent distances cache. */
    s->dist_rb[s->dist_rb_idx & 3] = s->distance_code;
    ++s->dist_rb_idx;
    s->meta_block_remaining_len -= i;
    /* There are 32+ bytes of slack in the ring-buffer allocation.
       Also, we have 16 short codes, that make these 16 bytes irrelevant
       in the ring-buffer. Let's copy over them as a first guess. */
    memmove16(copy_dst, copy_src);
    if (src_end > pos && dst_end > src_start) {
      /* Regions intersect. */
      goto CommandPostWrapCopy;
    }
    if (dst_end >= s->ringbuffer_size || src_end >= s->ringbuffer_size) {
      /* At least one region wraps. */
      goto CommandPostWrapCopy;
    }
    pos += i;
    if (i > 16) {
      if (i > 32) {
        memcpy(copy_dst + 16, copy_src + 16, (size_t)(i - 16));
      } else {
        /* This branch covers about 45% cases.
           Fixed size short copy allows more compiler optimizations. */
        memmove16(copy_dst + 16, copy_src + 16);
      }
    }
  }
  BROTLI_LOG_UINT(s->meta_block_remaining_len);
  if (s->meta_block_remaining_len <= 0) {
    /* Next metablock, if any. */
    s->state = BROTLI_STATE_METABLOCK_DONE;
    goto saveStateAndReturn;
  } else {
    goto CommandBegin;
  }
CommandPostWrapCopy:
  {
    int wrap_guard = s->ringbuffer_size - pos;
    while (--i >= 0) {
      s->ringbuffer[pos] =
          s->ringbuffer[(pos - s->distance_code) & s->ringbuffer_mask];
      ++pos;
      if (BROTLI_PREDICT_FALSE(--wrap_guard == 0)) {
        s->state = BROTLI_STATE_COMMAND_POST_WRITE_2;
        goto saveStateAndReturn;
      }
    }
  }
  if (s->meta_block_remaining_len <= 0) {
    /* Next metablock, if any. */
    s->state = BROTLI_STATE_METABLOCK_DONE;
    goto saveStateAndReturn;
  } else {
    goto CommandBegin;
  }

NextLiteralBlock:
  BROTLI_SAFE(DecodeLiteralBlockSwitch(s));
  goto CommandInner;

saveStateAndReturn:
  s->pos = pos;
  s->loop_counter = i;
  return result;
}

#undef BROTLI_SAFE

static BROTLI_NOINLINE BrotliDecoderErrorCode ProcessCommands(
    BrotliDecoderState* s) {
  return ProcessCommandsInternal(0, s);
}

static BROTLI_NOINLINE BrotliDecoderErrorCode SafeProcessCommands(
    BrotliDecoderState* s) {
  return ProcessCommandsInternal(1, s);
}

BrotliDecoderResult BrotliDecoderDecompress(
    size_t encoded_size,
    const uint8_t encoded_buffer[BROTLI_ARRAY_PARAM(encoded_size)],
    size_t* decoded_size,
    uint8_t decoded_buffer[BROTLI_ARRAY_PARAM(*decoded_size)]) {
  BrotliDecoderState s;
  BrotliDecoderResult result;
  size_t total_out = 0;
  size_t available_in = encoded_size;
  const uint8_t* next_in = encoded_buffer;
  size_t available_out = *decoded_size;
  uint8_t* next_out = decoded_buffer;
  if (!BrotliDecoderStateInit(&s, 0, 0, 0)) {
    return BROTLI_DECODER_RESULT_ERROR;
  }
  result = BrotliDecoderDecompressStream(
      &s, &available_in, &next_in, &available_out, &next_out, &total_out);
  *decoded_size = total_out;
  BrotliDecoderStateCleanup(&s);
  if (result != BROTLI_DECODER_RESULT_SUCCESS) {
    result = BROTLI_DECODER_RESULT_ERROR;
  }
  return result;
}

/* Invariant: input stream is never overconsumed:
    - invalid input implies that the whole stream is invalid -> any amount of
      input could be read and discarded
    - when result is "needs more input", then at least one more byte is REQUIRED
      to complete decoding; all input data MUST be consumed by decoder, so
      client could swap the input buffer
    - when result is "needs more output" decoder MUST ensure that it doesn't
      hold more than 7 bits in bit reader; this saves client from swapping input
      buffer ahead of time
    - when result is "success" decoder MUST return all unused data back to input
      buffer; this is possible because the invariant is held on enter */
BrotliDecoderResult BrotliDecoderDecompressStream(
    BrotliDecoderState* s, size_t* available_in, const uint8_t** next_in,
    size_t* available_out, uint8_t** next_out, size_t* total_out) {
  BrotliDecoderErrorCode result = BROTLI_DECODER_SUCCESS;
  BrotliBitReader* br = &s->br;
  size_t input_size = *available_in;
#define BROTLI_SAVE_ERROR_CODE(code) \
    SaveErrorCode(s, (code), input_size - *available_in)
  /* Ensure that |total_out| is set, even if no data will ever be pushed out. */
  if (total_out) {
    *total_out = s->partial_pos_out;
  }
  /* Do not try to process further in a case of unrecoverable error. */
  if ((int)s->error_code < 0) {
    return BROTLI_DECODER_RESULT_ERROR;
  }
  if (*available_out && (!next_out || !*next_out)) {
    return BROTLI_SAVE_ERROR_CODE(
        BROTLI_FAILURE(BROTLI_DECODER_ERROR_INVALID_ARGUMENTS));
  }
  if (!*available_out) next_out = 0;
  if (s->buffer_length == 0) {  /* Just connect bit reader to input stream. */
    BrotliBitReaderSetInput(br, *next_in, *available_in);
  } else {
    /* At least one byte of input is required. More than one byte of input may
       be required to complete the transaction -> reading more data must be
       done in a loop -> do it in a main loop. */
    result = BROTLI_DECODER_NEEDS_MORE_INPUT;
    BrotliBitReaderSetInput(br, &s->buffer.u8[0], s->buffer_length);
  }
  /* State machine */
  for (;;) {
    if (result != BROTLI_DECODER_SUCCESS) {
      /* Error, needs more input/output. */
      if (result == BROTLI_DECODER_NEEDS_MORE_INPUT) {
        if (s->ringbuffer != 0) {  /* Pro-actively push output. */
          BrotliDecoderErrorCode intermediate_result = WriteRingBuffer(s,
              available_out, next_out, total_out, BROTLI_TRUE);
          /* WriteRingBuffer checks s->meta_block_remaining_len validity. */
          if ((int)intermediate_result < 0) {
            result = intermediate_result;
            break;
          }
        }
        if (s->buffer_length != 0) {  /* Used with internal buffer. */
          if (br->next_in == br->last_in) {
            /* Successfully finished read transaction.
               Accumulator contains less than 8 bits, because internal buffer
               is expanded byte-by-byte until it is enough to complete read. */
            s->buffer_length = 0;
            /* Switch to input stream and restart. */
            result = BROTLI_DECODER_SUCCESS;
            BrotliBitReaderSetInput(br, *next_in, *available_in);
            continue;
          } else if (*available_in != 0) {
            /* Not enough data in buffer, but can take one more byte from
               input stream. */
            result = BROTLI_DECODER_SUCCESS;
            BROTLI_DCHECK(s->buffer_length < 8);
            s->buffer.u8[s->buffer_length] = **next_in;
            s->buffer_length++;
            BrotliBitReaderSetInput(br, &s->buffer.u8[0], s->buffer_length);
            (*next_in)++;
            (*available_in)--;
            /* Retry with more data in buffer. */
            continue;
          }
          /* Can't finish reading and no more input. */
          break;
        } else {  /* Input stream doesn't contain enough input. */
          /* Copy tail to internal buffer and return. */
          *next_in = br->next_in;
          *available_in = BrotliBitReaderGetAvailIn(br);
          while (*available_in) {
            s->buffer.u8[s->buffer_length] = **next_in;
            s->buffer_length++;
            (*next_in)++;
            (*available_in)--;
          }
          break;
        }
        /* Unreachable. */
      }

      /* Fail or needs more output. */

      if (s->buffer_length != 0) {
        /* Just consumed the buffered input and produced some output. Otherwise
           it would result in "needs more input". Reset internal buffer. */
        s->buffer_length = 0;
      } else {
        /* Using input stream in last iteration. When decoder switches to input
           stream it has less than 8 bits in accumulator, so it is safe to
           return unused accumulator bits there. */
        BrotliBitReaderUnload(br);
        *available_in = BrotliBitReaderGetAvailIn(br);
        *next_in = br->next_in;
      }
      break;
    }
    switch (s->state) {
      case BROTLI_STATE_UNINITED:
        /* Prepare to the first read. */
        if (!BrotliWarmupBitReader(br)) {
          result = BROTLI_DECODER_NEEDS_MORE_INPUT;
          break;
        }
        /* Decode window size. */
        result = DecodeWindowBits(s, br);  /* Reads 1..8 bits. */
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        if (s->large_window) {
          s->state = BROTLI_STATE_LARGE_WINDOW_BITS;
          break;
        }
        s->state = BROTLI_STATE_INITIALIZE;
        break;

      case BROTLI_STATE_LARGE_WINDOW_BITS: {
        brotli_reg_t bits;
        if (!BrotliSafeReadBits(br, 6, &bits)) {
          result = BROTLI_DECODER_NEEDS_MORE_INPUT;
          break;
        }
        s->window_bits = bits & 63u;
        if (s->window_bits < BROTLI_LARGE_MIN_WBITS ||
            s->window_bits > BROTLI_LARGE_MAX_WBITS) {
          result = BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_WINDOW_BITS);
          break;
        }
        s->state = BROTLI_STATE_INITIALIZE;
      }
      /* Fall through. */

      case BROTLI_STATE_INITIALIZE:
        BROTLI_LOG_UINT(s->window_bits);
        /* Maximum distance, see section 9.1. of the spec. */
        s->max_backward_distance = (1 << s->window_bits) - BROTLI_WINDOW_GAP;

        /* Allocate memory for both block_type_trees and block_len_trees. */
        s->block_type_trees = (HuffmanCode*)BROTLI_DECODER_ALLOC(s,
            sizeof(HuffmanCode) * 3 *
                (BROTLI_HUFFMAN_MAX_SIZE_258 + BROTLI_HUFFMAN_MAX_SIZE_26));
        if (s->block_type_trees == 0) {
          result = BROTLI_FAILURE(BROTLI_DECODER_ERROR_ALLOC_BLOCK_TYPE_TREES);
          break;
        }
        s->block_len_trees =
            s->block_type_trees + 3 * BROTLI_HUFFMAN_MAX_SIZE_258;

        s->state = BROTLI_STATE_METABLOCK_BEGIN;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_BEGIN:
        BrotliDecoderStateMetablockBegin(s);
        BROTLI_LOG_UINT(s->pos);
        s->state = BROTLI_STATE_METABLOCK_HEADER;
      /* Fall through. */

      case BROTLI_STATE_METABLOCK_HEADER:
        result = DecodeMetaBlockLength(s, br);  /* Reads 2 - 31 bits. */
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        BROTLI_LOG_UINT(s->is_last_metablock);
        BROTLI_LOG_UINT(s->meta_block_remaining_len);
        BROTLI_LOG_UINT(s->is_metadata);
        BROTLI_LOG_UINT(s->is_uncompressed);
        if (s->is_metadata || s->is_uncompressed) {
          if (!BrotliJumpToByteBoundary(br)) {
            result = BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_PADDING_1);
            break;
          }
        }
        if (s->is_metadata) {
          s->state = BROTLI_STATE_METADATA;
          if (s->metadata_start_func) {
            s->metadata_start_func(s->metadata_callback_opaque,
                                   (size_t)s->meta_block_remaining_len);
          }
          break;
        }
        if (s->meta_block_remaining_len == 0) {
          s->state = BROTLI_STATE_METABLOCK_DONE;
          break;
        }
        BrotliCalculateRingBufferSize(s);
        if (s->is_uncompressed) {
          s->state = BROTLI_STATE_UNCOMPRESSED;
          break;
        }
        s->state = BROTLI_STATE_BEFORE_COMPRESSED_METABLOCK_HEADER;
      /* Fall through. */

      case BROTLI_STATE_BEFORE_COMPRESSED_METABLOCK_HEADER: {
        BrotliMetablockHeaderArena* h = &s->arena.header;
        s->loop_counter = 0;
        /* Initialize compressed metablock header arena. */
        h->sub_loop_counter = 0;
        /* Make small negative indexes addressable. */
        h->symbol_lists =
            &h->symbols_lists_array[BROTLI_HUFFMAN_MAX_CODE_LENGTH + 1];
        h->substate_huffman = BROTLI_STATE_HUFFMAN_NONE;
        h->substate_tree_group = BROTLI_STATE_TREE_GROUP_NONE;
        h->substate_context_map = BROTLI_STATE_CONTEXT_MAP_NONE;
        s->state = BROTLI_STATE_HUFFMAN_CODE_0;
      }
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_CODE_0:
        if (s->loop_counter >= 3) {
          s->state = BROTLI_STATE_METABLOCK_HEADER_2;
          break;
        }
        /* Reads 1..11 bits. */
        result = DecodeVarLenUint8(s, br, &s->num_block_types[s->loop_counter]);
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        s->num_block_types[s->loop_counter]++;
        BROTLI_LOG_UINT(s->num_block_types[s->loop_counter]);
        if (s->num_block_types[s->loop_counter] < 2) {
          s->loop_counter++;
          break;
        }
        s->state = BROTLI_STATE_HUFFMAN_CODE_1;
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_CODE_1: {
        brotli_reg_t alphabet_size = s->num_block_types[s->loop_counter] + 2;
        int tree_offset = s->loop_counter * BROTLI_HUFFMAN_MAX_SIZE_258;
        result = ReadHuffmanCode(alphabet_size, alphabet_size,
            &s->block_type_trees[tree_offset], NULL, s);
        if (result != BROTLI_DECODER_SUCCESS) break;
        s->state = BROTLI_STATE_HUFFMAN_CODE_2;
      }
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_CODE_2: {
        brotli_reg_t alphabet_size = BROTLI_NUM_BLOCK_LEN_SYMBOLS;
        int tree_offset = s->loop_counter * BROTLI_HUFFMAN_MAX_SIZE_26;
        result = ReadHuffmanCode(alphabet_size, alphabet_size,
            &s->block_len_trees[tree_offset], NULL, s);
        if (result != BROTLI_DECODER_SUCCESS) break;
        s->state = BROTLI_STATE_HUFFMAN_CODE_3;
      }
      /* Fall through. */

      case BROTLI_STATE_HUFFMAN_CODE_3: {
        int tree_offset = s->loop_counter * BROTLI_HUFFMAN_MAX_SIZE_26;
        if (!SafeReadBlockLength(s, &s->block_length[s->loop_counter],
            &s->block_len_trees[tree_offset], br)) {
          result = BROTLI_DECODER_NEEDS_MORE_INPUT;
          break;
        }
        BROTLI_LOG_UINT(s->block_length[s->loop_counter]);
        s->loop_counter++;
        s->state = BROTLI_STATE_HUFFMAN_CODE_0;
        break;
      }

      case BROTLI_STATE_UNCOMPRESSED: {
        result = CopyUncompressedBlockToOutput(
            available_out, next_out, total_out, s);
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        s->state = BROTLI_STATE_METABLOCK_DONE;
        break;
      }

      case BROTLI_STATE_METADATA:
        result = SkipMetadataBlock(s);
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        s->state = BROTLI_STATE_METABLOCK_DONE;
        break;

      case BROTLI_STATE_METABLOCK_HEADER_2: {
        brotli_reg_t bits;
        if (!BrotliSafeReadBits(br, 6, &bits)) {
          result = BROTLI_DECODER_NEEDS_MORE_INPUT;
          break;
        }
        s->distance_postfix_bits = bits & BitMask(2);
        bits >>= 2;
        s->num_direct_distance_codes = bits << s->distance_postfix_bits;
        BROTLI_LOG_UINT(s->num_direct_distance_codes);
        BROTLI_LOG_UINT(s->distance_postfix_bits);
        s->context_modes =
            (uint8_t*)BROTLI_DECODER_ALLOC(s, (size_t)s->num_block_types[0]);
        if (s->context_modes == 0) {
          result = BROTLI_FAILURE(BROTLI_DECODER_ERROR_ALLOC_CONTEXT_MODES);
          break;
        }
        s->loop_counter = 0;
        s->state = BROTLI_STATE_CONTEXT_MODES;
      }
      /* Fall through. */

      case BROTLI_STATE_CONTEXT_MODES:
        result = ReadContextModes(s);
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        s->state = BROTLI_STATE_CONTEXT_MAP_1;
      /* Fall through. */

      case BROTLI_STATE_CONTEXT_MAP_1:
        result = DecodeContextMap(
            s->num_block_types[0] << BROTLI_LITERAL_CONTEXT_BITS,
            &s->num_literal_htrees, &s->context_map, s);
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        DetectTrivialLiteralBlockTypes(s);
        s->state = BROTLI_STATE_CONTEXT_MAP_2;
      /* Fall through. */

      case BROTLI_STATE_CONTEXT_MAP_2: {
        brotli_reg_t npostfix = s->distance_postfix_bits;
        brotli_reg_t ndirect = s->num_direct_distance_codes;
        brotli_reg_t distance_alphabet_size_max = BROTLI_DISTANCE_ALPHABET_SIZE(
            npostfix, ndirect, BROTLI_MAX_DISTANCE_BITS);
        brotli_reg_t distance_alphabet_size_limit = distance_alphabet_size_max;
        BROTLI_BOOL allocation_success = BROTLI_TRUE;
        if (s->large_window) {
          BrotliDistanceCodeLimit limit = BrotliCalculateDistanceCodeLimit(
              BROTLI_MAX_ALLOWED_DISTANCE, (uint32_t)npostfix,
              (uint32_t)ndirect);
          distance_alphabet_size_max = BROTLI_DISTANCE_ALPHABET_SIZE(
              npostfix, ndirect, BROTLI_LARGE_MAX_DISTANCE_BITS);
          distance_alphabet_size_limit = limit.max_alphabet_size;
        }
        result = DecodeContextMap(
            s->num_block_types[2] << BROTLI_DISTANCE_CONTEXT_BITS,
            &s->num_dist_htrees, &s->dist_context_map, s);
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        allocation_success &= BrotliDecoderHuffmanTreeGroupInit(
            s, &s->literal_hgroup, BROTLI_NUM_LITERAL_SYMBOLS,
            BROTLI_NUM_LITERAL_SYMBOLS, s->num_literal_htrees);
        allocation_success &= BrotliDecoderHuffmanTreeGroupInit(
            s, &s->insert_copy_hgroup, BROTLI_NUM_COMMAND_SYMBOLS,
            BROTLI_NUM_COMMAND_SYMBOLS, s->num_block_types[1]);
        allocation_success &= BrotliDecoderHuffmanTreeGroupInit(
            s, &s->distance_hgroup, distance_alphabet_size_max,
            distance_alphabet_size_limit, s->num_dist_htrees);
        if (!allocation_success) {
          return BROTLI_SAVE_ERROR_CODE(
              BROTLI_FAILURE(BROTLI_DECODER_ERROR_ALLOC_TREE_GROUPS));
        }
        s->loop_counter = 0;
        s->state = BROTLI_STATE_TREE_GROUP;
      }
      /* Fall through. */

      case BROTLI_STATE_TREE_GROUP: {
        HuffmanTreeGroup* hgroup = NULL;
        switch (s->loop_counter) {
          case 0: hgroup = &s->literal_hgroup; break;
          case 1: hgroup = &s->insert_copy_hgroup; break;
          case 2: hgroup = &s->distance_hgroup; break;
          default: return BROTLI_SAVE_ERROR_CODE(BROTLI_FAILURE(
              BROTLI_DECODER_ERROR_UNREACHABLE));  /* COV_NF_LINE */
        }
        result = HuffmanTreeGroupDecode(hgroup, s);
        if (result != BROTLI_DECODER_SUCCESS) break;
        s->loop_counter++;
        if (s->loop_counter < 3) {
          break;
        }
        s->state = BROTLI_STATE_BEFORE_COMPRESSED_METABLOCK_BODY;
      }
      /* Fall through. */

      case BROTLI_STATE_BEFORE_COMPRESSED_METABLOCK_BODY:
        PrepareLiteralDecoding(s);
        s->dist_context_map_slice = s->dist_context_map;
        s->htree_command = s->insert_copy_hgroup.htrees[0];
        if (!BrotliEnsureRingBuffer(s)) {
          result = BROTLI_FAILURE(BROTLI_DECODER_ERROR_ALLOC_RING_BUFFER_2);
          break;
        }
        CalculateDistanceLut(s);
        s->state = BROTLI_STATE_COMMAND_BEGIN;
      /* Fall through. */

      case BROTLI_STATE_COMMAND_BEGIN:
      /* Fall through. */
      case BROTLI_STATE_COMMAND_INNER:
      /* Fall through. */
      case BROTLI_STATE_COMMAND_POST_DECODE_LITERALS:
      /* Fall through. */
      case BROTLI_STATE_COMMAND_POST_WRAP_COPY:
        result = ProcessCommands(s);
        if (result == BROTLI_DECODER_NEEDS_MORE_INPUT) {
          result = SafeProcessCommands(s);
        }
        break;

      case BROTLI_STATE_COMMAND_INNER_WRITE:
      /* Fall through. */
      case BROTLI_STATE_COMMAND_POST_WRITE_1:
      /* Fall through. */
      case BROTLI_STATE_COMMAND_POST_WRITE_2:
        result = WriteRingBuffer(
            s, available_out, next_out, total_out, BROTLI_FALSE);
        if (result != BROTLI_DECODER_SUCCESS) {
          break;
        }
        WrapRingBuffer(s);
        if (s->ringbuffer_size == 1 << s->window_bits) {
          s->max_distance = s->max_backward_distance;
        }
        if (s->state == BROTLI_STATE_COMMAND_POST_WRITE_1) {
          BrotliDecoderCompoundDictionary* addon = s->compound_dictionary;
          if (addon && (addon->br_length != addon->br_copied)) {
            s->pos += CopyFromCompoundDictionary(s, s->pos);
            if (s->pos >= s->ringbuffer_size) continue;
          }
          if (s->meta_block_remaining_len == 0) {
            /* Next metablock, if any. */
            s->state = BROTLI_STATE_METABLOCK_DONE;
          } else {
            s->state = BROTLI_STATE_COMMAND_BEGIN;
          }
          break;
        } else if (s->state == BROTLI_STATE_COMMAND_POST_WRITE_2) {
          s->state = BROTLI_STATE_COMMAND_POST_WRAP_COPY;
        } else {  /* BROTLI_STATE_COMMAND_INNER_WRITE */
          if (s->loop_counter == 0) {
            if (s->meta_block_remaining_len == 0) {
              s->state = BROTLI_STATE_METABLOCK_DONE;
            } else {
              s->state = BROTLI_STATE_COMMAND_POST_DECODE_LITERALS;
            }
            break;
          }
          s->state = BROTLI_STATE_COMMAND_INNER;
        }
        break;

      case BROTLI_STATE_METABLOCK_DONE:
        if (s->meta_block_remaining_len < 0) {
          result = BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_BLOCK_LENGTH_2);
          break;
        }
        BrotliDecoderStateCleanupAfterMetablock(s);
        if (!s->is_last_metablock) {
          s->state = BROTLI_STATE_METABLOCK_BEGIN;
          break;
        }
        if (!BrotliJumpToByteBoundary(br)) {
          result = BROTLI_FAILURE(BROTLI_DECODER_ERROR_FORMAT_PADDING_2);
          break;
        }
        if (s->buffer_length == 0) {
          BrotliBitReaderUnload(br);
          *available_in = BrotliBitReaderGetAvailIn(br);
          *next_in = br->next_in;
        }
        s->state = BROTLI_STATE_DONE;
      /* Fall through. */

      case BROTLI_STATE_DONE:
        if (s->ringbuffer != 0) {
          result = WriteRingBuffer(
              s, available_out, next_out, total_out, BROTLI_TRUE);
          if (result != BROTLI_DECODER_SUCCESS) {
            break;
          }
        }
        return BROTLI_SAVE_ERROR_CODE(result);
    }
  }
  return BROTLI_SAVE_ERROR_CODE(result);
#undef BROTLI_SAVE_ERROR_CODE
}

BROTLI_BOOL BrotliDecoderHasMoreOutput(const BrotliDecoderState* s) {
  /* After unrecoverable error remaining output is considered nonsensical. */
  if ((int)s->error_code < 0) {
    return BROTLI_FALSE;
  }
  return TO_BROTLI_BOOL(
      s->ringbuffer != 0 && UnwrittenBytes(s, BROTLI_FALSE) != 0);
}

const uint8_t* BrotliDecoderTakeOutput(BrotliDecoderState* s, size_t* size) {
  uint8_t* result = 0;
  size_t available_out = *size ? *size : 1u << 24;
  size_t requested_out = available_out;
  BrotliDecoderErrorCode status;
  if ((s->ringbuffer == 0) || ((int)s->error_code < 0)) {
    *size = 0;
    return 0;
  }
  WrapRingBuffer(s);
  status = WriteRingBuffer(s, &available_out, &result, 0, BROTLI_TRUE);
  /* Either WriteRingBuffer returns those "success" codes... */
  if (status == BROTLI_DECODER_SUCCESS ||
      status == BROTLI_DECODER_NEEDS_MORE_OUTPUT) {
    *size = requested_out - available_out;
  } else {
    /* ... or stream is broken. Normally this should be caught by
       BrotliDecoderDecompressStream, this is just a safeguard. */
    if ((int)status < 0) SaveErrorCode(s, status, 0);
    *size = 0;
    result = 0;
  }
  return result;
}

BROTLI_BOOL BrotliDecoderIsUsed(const BrotliDecoderState* s) {
  return TO_BROTLI_BOOL(s->state != BROTLI_STATE_UNINITED ||
      BrotliGetAvailableBits(&s->br) != 0);
}

BROTLI_BOOL BrotliDecoderIsFinished(const BrotliDecoderState* s) {
  return TO_BROTLI_BOOL(s->state == BROTLI_STATE_DONE) &&
      !BrotliDecoderHasMoreOutput(s);
}

BrotliDecoderErrorCode BrotliDecoderGetErrorCode(const BrotliDecoderState* s) {
  return (BrotliDecoderErrorCode)s->error_code;
}

const char* BrotliDecoderErrorString(BrotliDecoderErrorCode c) {
  switch (c) {
#define BROTLI_ERROR_CODE_CASE_(PREFIX, NAME, CODE) \
    case BROTLI_DECODER ## PREFIX ## NAME: return #PREFIX #NAME;
#define BROTLI_NOTHING_
    BROTLI_DECODER_ERROR_CODES_LIST(BROTLI_ERROR_CODE_CASE_, BROTLI_NOTHING_)
#undef BROTLI_ERROR_CODE_CASE_
#undef BROTLI_NOTHING_
    default: return "INVALID";
  }
}

uint32_t BrotliDecoderVersion(void) {
  return BROTLI_VERSION;
}

void BrotliDecoderSetMetadataCallbacks(
    BrotliDecoderState* state,
    brotli_decoder_metadata_start_func start_func,
    brotli_decoder_metadata_chunk_func chunk_func, void* opaque) {
  state->metadata_start_func = start_func;
  state->metadata_chunk_func = chunk_func;
  state->metadata_callback_opaque = opaque;
}

/* Escalate internal functions visibility; for testing purposes only. */
#if defined(BROTLI_TEST)
BROTLI_BOOL BrotliSafeReadSymbolForTest(
    const HuffmanCode*, BrotliBitReader*, brotli_reg_t*);
BROTLI_BOOL BrotliSafeReadSymbolForTest(
    const HuffmanCode* table, BrotliBitReader* br, brotli_reg_t* result) {
  return SafeReadSymbol(table, br, result);
}
void BrotliInverseMoveToFrontTransformForTest(
    uint8_t*, brotli_reg_t, BrotliDecoderState*);
void BrotliInverseMoveToFrontTransformForTest(
    uint8_t* v, brotli_reg_t l, BrotliDecoderState* s) {
  InverseMoveToFrontTransform(v, l, s);
}
#endif

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/dec/huffman.c ---- */
/* Copyright 2013 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

/* Utilities for building Huffman decoding tables. */

#include "huffman.h"

#include "../common/constants.h"
#include "../common/platform.h"

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

#define BROTLI_REVERSE_BITS_MAX 8

#if defined(BROTLI_RBIT)
#define BROTLI_REVERSE_BITS_BASE \
  ((sizeof(brotli_reg_t) << 3) - BROTLI_REVERSE_BITS_MAX)
#else
#define BROTLI_REVERSE_BITS_BASE 0
static BROTLI_MODEL("small")
uint8_t kReverseBits[1 << BROTLI_REVERSE_BITS_MAX] = {
  0x00, 0x80, 0x40, 0xC0, 0x20, 0xA0, 0x60, 0xE0,
  0x10, 0x90, 0x50, 0xD0, 0x30, 0xB0, 0x70, 0xF0,
  0x08, 0x88, 0x48, 0xC8, 0x28, 0xA8, 0x68, 0xE8,
  0x18, 0x98, 0x58, 0xD8, 0x38, 0xB8, 0x78, 0xF8,
  0x04, 0x84, 0x44, 0xC4, 0x24, 0xA4, 0x64, 0xE4,
  0x14, 0x94, 0x54, 0xD4, 0x34, 0xB4, 0x74, 0xF4,
  0x0C, 0x8C, 0x4C, 0xCC, 0x2C, 0xAC, 0x6C, 0xEC,
  0x1C, 0x9C, 0x5C, 0xDC, 0x3C, 0xBC, 0x7C, 0xFC,
  0x02, 0x82, 0x42, 0xC2, 0x22, 0xA2, 0x62, 0xE2,
  0x12, 0x92, 0x52, 0xD2, 0x32, 0xB2, 0x72, 0xF2,
  0x0A, 0x8A, 0x4A, 0xCA, 0x2A, 0xAA, 0x6A, 0xEA,
  0x1A, 0x9A, 0x5A, 0xDA, 0x3A, 0xBA, 0x7A, 0xFA,
  0x06, 0x86, 0x46, 0xC6, 0x26, 0xA6, 0x66, 0xE6,
  0x16, 0x96, 0x56, 0xD6, 0x36, 0xB6, 0x76, 0xF6,
  0x0E, 0x8E, 0x4E, 0xCE, 0x2E, 0xAE, 0x6E, 0xEE,
  0x1E, 0x9E, 0x5E, 0xDE, 0x3E, 0xBE, 0x7E, 0xFE,
  0x01, 0x81, 0x41, 0xC1, 0x21, 0xA1, 0x61, 0xE1,
  0x11, 0x91, 0x51, 0xD1, 0x31, 0xB1, 0x71, 0xF1,
  0x09, 0x89, 0x49, 0xC9, 0x29, 0xA9, 0x69, 0xE9,
  0x19, 0x99, 0x59, 0xD9, 0x39, 0xB9, 0x79, 0xF9,
  0x05, 0x85, 0x45, 0xC5, 0x25, 0xA5, 0x65, 0xE5,
  0x15, 0x95, 0x55, 0xD5, 0x35, 0xB5, 0x75, 0xF5,
  0x0D, 0x8D, 0x4D, 0xCD, 0x2D, 0xAD, 0x6D, 0xED,
  0x1D, 0x9D, 0x5D, 0xDD, 0x3D, 0xBD, 0x7D, 0xFD,
  0x03, 0x83, 0x43, 0xC3, 0x23, 0xA3, 0x63, 0xE3,
  0x13, 0x93, 0x53, 0xD3, 0x33, 0xB3, 0x73, 0xF3,
  0x0B, 0x8B, 0x4B, 0xCB, 0x2B, 0xAB, 0x6B, 0xEB,
  0x1B, 0x9B, 0x5B, 0xDB, 0x3B, 0xBB, 0x7B, 0xFB,
  0x07, 0x87, 0x47, 0xC7, 0x27, 0xA7, 0x67, 0xE7,
  0x17, 0x97, 0x57, 0xD7, 0x37, 0xB7, 0x77, 0xF7,
  0x0F, 0x8F, 0x4F, 0xCF, 0x2F, 0xAF, 0x6F, 0xEF,
  0x1F, 0x9F, 0x5F, 0xDF, 0x3F, 0xBF, 0x7F, 0xFF
};
#endif  /* BROTLI_RBIT */

#define BROTLI_REVERSE_BITS_LOWEST \
  ((brotli_reg_t)1 << (BROTLI_REVERSE_BITS_MAX - 1 + BROTLI_REVERSE_BITS_BASE))

/* Returns reverse(num >> BROTLI_REVERSE_BITS_BASE, BROTLI_REVERSE_BITS_MAX),
   where reverse(value, len) is the bit-wise reversal of the len least
   significant bits of value. */
static BROTLI_INLINE brotli_reg_t BrotliReverseBits(brotli_reg_t num) {
#if defined(BROTLI_RBIT)
  return BROTLI_RBIT(num);
#else
  return kReverseBits[num];
#endif
}

/* Stores code in table[0], table[step], table[2*step], ..., table[end] */
/* Assumes that end is an integer multiple of step */
static BROTLI_INLINE void ReplicateValue(HuffmanCode* table,
                                         int step, int end,
                                         HuffmanCode code) {
  do {
    end -= step;
    table[end] = code;
  } while (end > 0);
}

/* Returns the table width of the next 2nd level table. |count| is the histogram
   of bit lengths for the remaining symbols, |len| is the code length of the
   next processed symbol. */
static BROTLI_INLINE int NextTableBitSize(const uint16_t* const count,
                                          int len, int root_bits) {
  int left = 1 << (len - root_bits);
  while (len < BROTLI_HUFFMAN_MAX_CODE_LENGTH) {
    left -= count[len];
    if (left <= 0) break;
    ++len;
    left <<= 1;
  }
  return len - root_bits;
}

void BrotliBuildCodeLengthsHuffmanTable(HuffmanCode* table,
                                        const uint8_t* const code_lengths,
                                        uint16_t* count) {
  HuffmanCode code;       /* current table entry */
  int symbol;             /* symbol index in original or sorted table */
  brotli_reg_t key;       /* prefix code */
  brotli_reg_t key_step;  /* prefix code addend */
  int step;               /* step size to replicate values in current table */
  int table_size;         /* size of current table */
  int sorted[BROTLI_CODE_LENGTH_CODES];  /* symbols sorted by code length */
  /* offsets in sorted table for each length */
  int offset[BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH + 1];
  int bits;
  int bits_count;
  BROTLI_DCHECK(BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH <=
                BROTLI_REVERSE_BITS_MAX);
  BROTLI_DCHECK(BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH == 5);

  /* Generate offsets into sorted symbol table by code length. */
  symbol = -1;
  bits = 1;
  /* BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH == 5 */
  BROTLI_REPEAT_5({
    symbol += count[bits];
    offset[bits] = symbol;
    bits++;
  });
  /* Symbols with code length 0 are placed after all other symbols. */
  offset[0] = BROTLI_CODE_LENGTH_CODES - 1;

  /* Sort symbols by length, by symbol order within each length. */
  symbol = BROTLI_CODE_LENGTH_CODES;
  do {
    BROTLI_REPEAT_6({
      symbol--;
      sorted[offset[code_lengths[symbol]]--] = symbol;
    });
  } while (symbol != 0);

  table_size = 1 << BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH;

  /* Special case: all symbols but one have 0 code length. */
  if (offset[0] == 0) {
    code = ConstructHuffmanCode(0, (uint16_t)sorted[0]);
    for (key = 0; key < (brotli_reg_t)table_size; ++key) {
      table[key] = code;
    }
    return;
  }

  /* Fill in table. */
  key = 0;
  key_step = BROTLI_REVERSE_BITS_LOWEST;
  symbol = 0;
  bits = 1;
  step = 2;
  do {
    for (bits_count = count[bits]; bits_count != 0; --bits_count) {
      code = ConstructHuffmanCode((uint8_t)bits, (uint16_t)sorted[symbol++]);
      ReplicateValue(&table[BrotliReverseBits(key)], step, table_size, code);
      key += key_step;
    }
    step <<= 1;
    key_step >>= 1;
  } while (++bits <= BROTLI_HUFFMAN_MAX_CODE_LENGTH_CODE_LENGTH);
}

uint32_t BrotliBuildHuffmanTable(HuffmanCode* root_table,
                                 int root_bits,
                                 const uint16_t* const symbol_lists,
                                 uint16_t* count) {
  HuffmanCode code;       /* current table entry */
  HuffmanCode* table;     /* next available space in table */
  int len;                /* current code length */
  int symbol;             /* symbol index in original or sorted table */
  brotli_reg_t key;       /* prefix code */
  brotli_reg_t key_step;  /* prefix code addend */
  brotli_reg_t sub_key;   /* 2nd level table prefix code */
  brotli_reg_t sub_key_step;  /* 2nd level table prefix code addend */
  int step;               /* step size to replicate values in current table */
  int table_bits;         /* key length of current table */
  int table_size;         /* size of current table */
  int total_size;         /* sum of root table size and 2nd level table sizes */
  int max_length = -1;
  int bits;
  int bits_count;

  BROTLI_DCHECK(root_bits <= BROTLI_REVERSE_BITS_MAX);
  BROTLI_DCHECK(BROTLI_HUFFMAN_MAX_CODE_LENGTH - root_bits <=
                BROTLI_REVERSE_BITS_MAX);

  while (symbol_lists[max_length] == 0xFFFF) max_length--;
  max_length += BROTLI_HUFFMAN_MAX_CODE_LENGTH + 1;

  table = root_table;
  table_bits = root_bits;
  table_size = 1 << table_bits;
  total_size = table_size;

  /* Fill in the root table. Reduce the table size to if possible,
     and create the repetitions by memcpy. */
  if (table_bits > max_length) {
    table_bits = max_length;
    table_size = 1 << table_bits;
  }
  key = 0;
  key_step = BROTLI_REVERSE_BITS_LOWEST;
  bits = 1;
  step = 2;
  do {
    symbol = bits - (BROTLI_HUFFMAN_MAX_CODE_LENGTH + 1);
    for (bits_count = count[bits]; bits_count != 0; --bits_count) {
      symbol = symbol_lists[symbol];
      code = ConstructHuffmanCode((uint8_t)bits, (uint16_t)symbol);
      ReplicateValue(&table[BrotliReverseBits(key)], step, table_size, code);
      key += key_step;
    }
    step <<= 1;
    key_step >>= 1;
  } while (++bits <= table_bits);

  /* If root_bits != table_bits then replicate to fill the remaining slots. */
  while (total_size != table_size) {
    memcpy(&table[table_size], &table[0],
           (size_t)table_size * sizeof(table[0]));
    table_size <<= 1;
  }

  /* Fill in 2nd level tables and add pointers to root table. */
  key_step = BROTLI_REVERSE_BITS_LOWEST >> (root_bits - 1);
  sub_key = (BROTLI_REVERSE_BITS_LOWEST << 1);
  sub_key_step = BROTLI_REVERSE_BITS_LOWEST;
  for (len = root_bits + 1, step = 2; len <= max_length; ++len) {
    symbol = len - (BROTLI_HUFFMAN_MAX_CODE_LENGTH + 1);
    for (; count[len] != 0; --count[len]) {
      if (sub_key == (BROTLI_REVERSE_BITS_LOWEST << 1U)) {
        table += table_size;
        table_bits = NextTableBitSize(count, len, root_bits);
        table_size = 1 << table_bits;
        total_size += table_size;
        sub_key = BrotliReverseBits(key);
        key += key_step;
        root_table[sub_key] = ConstructHuffmanCode(
            (uint8_t)(table_bits + root_bits),
            (uint16_t)(((size_t)(table - root_table)) - sub_key));
        sub_key = 0;
      }
      symbol = symbol_lists[symbol];
      code = ConstructHuffmanCode((uint8_t)(len - root_bits), (uint16_t)symbol);
      ReplicateValue(
          &table[BrotliReverseBits(sub_key)], step, table_size, code);
      sub_key += sub_key_step;
    }
    step <<= 1;
    sub_key_step >>= 1;
  }
  return (uint32_t)total_size;
}

uint32_t BrotliBuildSimpleHuffmanTable(HuffmanCode* table,
                                       int root_bits,
                                       uint16_t* val,
                                       uint32_t num_symbols) {
  uint32_t table_size = 1;
  const uint32_t goal_size = 1U << root_bits;
  switch (num_symbols) {
    case 0:
      table[0] = ConstructHuffmanCode(0, val[0]);
      break;
    case 1:
      if (val[1] > val[0]) {
        table[0] = ConstructHuffmanCode(1, val[0]);
        table[1] = ConstructHuffmanCode(1, val[1]);
      } else {
        table[0] = ConstructHuffmanCode(1, val[1]);
        table[1] = ConstructHuffmanCode(1, val[0]);
      }
      table_size = 2;
      break;
    case 2:
      table[0] = ConstructHuffmanCode(1, val[0]);
      table[2] = ConstructHuffmanCode(1, val[0]);
      if (val[2] > val[1]) {
        table[1] = ConstructHuffmanCode(2, val[1]);
        table[3] = ConstructHuffmanCode(2, val[2]);
      } else {
        table[1] = ConstructHuffmanCode(2, val[2]);
        table[3] = ConstructHuffmanCode(2, val[1]);
      }
      table_size = 4;
      break;
    case 3: {
      int i, k;
      for (i = 0; i < 3; ++i) {
        for (k = i + 1; k < 4; ++k) {
          if (val[k] < val[i]) {
            uint16_t t = val[k];
            val[k] = val[i];
            val[i] = t;
          }
        }
      }
      table[0] = ConstructHuffmanCode(2, val[0]);
      table[2] = ConstructHuffmanCode(2, val[1]);
      table[1] = ConstructHuffmanCode(2, val[2]);
      table[3] = ConstructHuffmanCode(2, val[3]);
      table_size = 4;
      break;
    }
    case 4: {
      if (val[3] < val[2]) {
        uint16_t t = val[3];
        val[3] = val[2];
        val[2] = t;
      }
      table[0] = ConstructHuffmanCode(1, val[0]);
      table[1] = ConstructHuffmanCode(2, val[1]);
      table[2] = ConstructHuffmanCode(1, val[0]);
      table[3] = ConstructHuffmanCode(3, val[2]);
      table[4] = ConstructHuffmanCode(1, val[0]);
      table[5] = ConstructHuffmanCode(2, val[1]);
      table[6] = ConstructHuffmanCode(1, val[0]);
      table[7] = ConstructHuffmanCode(3, val[3]);
      table_size = 8;
      break;
    }
  }
  while (table_size != goal_size) {
    memcpy(&table[table_size], &table[0],
           (size_t)table_size * sizeof(table[0]));
    table_size <<= 1;
  }
  return goal_size;
}

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/dec/prefix.c ---- */
/* Copyright 2025 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include "prefix.h"

#include "../common/platform.h"  /* IWYU pragma: keep */
#include "../common/static_init.h"

#if (BROTLI_STATIC_INIT != BROTLI_STATIC_INIT_NONE)
#include "../common/constants.h"
#endif

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

#if (BROTLI_STATIC_INIT == BROTLI_STATIC_INIT_NONE)
/* Embed kCmdLut. */
#include "prefix_inc.h"
#else
BROTLI_COLD BROTLI_BOOL BrotliDecoderInitCmdLut(CmdLutElement* items) {
  static const uint8_t kInsertLengthExtraBits[24] = {
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x02, 0x02, 0x03, 0x03,
      0x04, 0x04, 0x05, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0C, 0x0E, 0x18};
  static const uint8_t kCopyLengthExtraBits[24] = {
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x02, 0x02,
      0x03, 0x03, 0x04, 0x04, 0x05, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x18};
  static const uint8_t kCellPos[11] = {0, 1, 0, 1, 8, 9, 2, 16, 10, 17, 18};

  uint16_t insert_length_offsets[24];
  uint16_t copy_length_offsets[24];
  insert_length_offsets[0] = 0;
  copy_length_offsets[0] = 2;
  for (size_t i = 0; i < 23; ++i) {
    insert_length_offsets[i + 1] =
        insert_length_offsets[i] + (uint16_t)(1u << kInsertLengthExtraBits[i]);
    copy_length_offsets[i + 1] =
        copy_length_offsets[i] + (uint16_t)(1u << kCopyLengthExtraBits[i]);
  }

  for (size_t symbol = 0; symbol < BROTLI_NUM_COMMAND_SYMBOLS; ++symbol) {
    CmdLutElement* item = items + symbol;
    const size_t cell_idx = symbol >> 6;
    const size_t cell_pos = kCellPos[cell_idx];
    const size_t copy_code = ((cell_pos << 3) & 0x18) + (symbol & 0x7);
    const uint16_t copy_len_offset = copy_length_offsets[copy_code];
    const size_t insert_code = (cell_pos & 0x18) + ((symbol >> 3) & 0x7);
    item->copy_len_extra_bits = kCopyLengthExtraBits[copy_code];
    item->context = (copy_len_offset > 4) ? 3 : ((uint8_t)copy_len_offset - 2);
    item->copy_len_offset = copy_len_offset;
    item->distance_code = (cell_idx >= 2) ? -1 : 0;
    item->insert_len_extra_bits = kInsertLengthExtraBits[insert_code];
    item->insert_len_offset = insert_length_offsets[insert_code];
  }
  return BROTLI_TRUE;
}

BROTLI_MODEL("small")
CmdLutElement kCmdLut[BROTLI_NUM_COMMAND_SYMBOLS];
#endif  /* BROTLI_STATIC_INIT */

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/dec/state.c ---- */
/* Copyright 2015 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include "state.h"

#include "../common/dictionary.h"
#include "../common/platform.h"
#include "huffman.h"

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

#ifdef BROTLI_REPORTING
/* When BROTLI_REPORTING is defined extra reporting module have to be linked. */
void BrotliDecoderOnStart(const BrotliDecoderState* s);
void BrotliDecoderOnFinish(const BrotliDecoderState* s);
#define BROTLI_DECODER_ON_START(s) BrotliDecoderOnStart(s);
#define BROTLI_DECODER_ON_FINISH(s) BrotliDecoderOnFinish(s);
#else
#if !defined(BROTLI_DECODER_ON_START)
#define BROTLI_DECODER_ON_START(s) (void)(s);
#endif
#if !defined(BROTLI_DECODER_ON_FINISH)
#define BROTLI_DECODER_ON_FINISH(s) (void)(s);
#endif
#endif

BROTLI_BOOL BrotliDecoderStateInit(BrotliDecoderState* s,
    brotli_alloc_func alloc_func, brotli_free_func free_func, void* opaque) {
  BROTLI_DECODER_ON_START(s);
  if (!alloc_func) {
    s->alloc_func = BrotliDefaultAllocFunc;
    s->free_func = BrotliDefaultFreeFunc;
    s->memory_manager_opaque = 0;
  } else {
    s->alloc_func = alloc_func;
    s->free_func = free_func;
    s->memory_manager_opaque = opaque;
  }

  s->error_code = 0; /* BROTLI_DECODER_NO_ERROR */

  BrotliInitBitReader(&s->br);
  s->state = BROTLI_STATE_UNINITED;
  s->large_window = 0;
  s->substate_metablock_header = BROTLI_STATE_METABLOCK_HEADER_NONE;
  s->substate_uncompressed = BROTLI_STATE_UNCOMPRESSED_NONE;
  s->substate_decode_uint8 = BROTLI_STATE_DECODE_UINT8_NONE;
  s->substate_read_block_length = BROTLI_STATE_READ_BLOCK_LENGTH_NONE;

  s->buffer_length = 0;
  s->loop_counter = 0;
  s->pos = 0;
  s->rb_roundtrips = 0;
  s->partial_pos_out = 0;
  s->used_input = 0;

  s->block_type_trees = NULL;
  s->block_len_trees = NULL;
  s->ringbuffer = NULL;
  s->ringbuffer_size = 0;
  s->new_ringbuffer_size = 0;
  s->ringbuffer_mask = 0;

  s->context_map = NULL;
  s->context_modes = NULL;
  s->dist_context_map = NULL;
  s->context_map_slice = NULL;
  s->dist_context_map_slice = NULL;

  s->literal_hgroup.codes = NULL;
  s->literal_hgroup.htrees = NULL;
  s->insert_copy_hgroup.codes = NULL;
  s->insert_copy_hgroup.htrees = NULL;
  s->distance_hgroup.codes = NULL;
  s->distance_hgroup.htrees = NULL;

  s->is_last_metablock = 0;
  s->is_uncompressed = 0;
  s->is_metadata = 0;
  s->should_wrap_ringbuffer = 0;
  s->canny_ringbuffer_allocation = 1;

  s->window_bits = 0;
  s->max_distance = 0;
  s->dist_rb[0] = 16;
  s->dist_rb[1] = 15;
  s->dist_rb[2] = 11;
  s->dist_rb[3] = 4;
  s->dist_rb_idx = 0;
  s->block_type_trees = NULL;
  s->block_len_trees = NULL;

  s->mtf_upper_bound = 63;

  s->compound_dictionary = NULL;
  s->dictionary =
      BrotliSharedDictionaryCreateInstance(alloc_func, free_func, opaque);
  if (!s->dictionary) return BROTLI_FALSE;

  s->metadata_start_func = NULL;
  s->metadata_chunk_func = NULL;
  s->metadata_callback_opaque = 0;

  return BROTLI_TRUE;
}

void BrotliDecoderStateMetablockBegin(BrotliDecoderState* s) {
  s->meta_block_remaining_len = 0;
  s->block_length[0] = BROTLI_BLOCK_SIZE_CAP;
  s->block_length[1] = BROTLI_BLOCK_SIZE_CAP;
  s->block_length[2] = BROTLI_BLOCK_SIZE_CAP;
  s->num_block_types[0] = 1;
  s->num_block_types[1] = 1;
  s->num_block_types[2] = 1;
  s->block_type_rb[0] = 1;
  s->block_type_rb[1] = 0;
  s->block_type_rb[2] = 1;
  s->block_type_rb[3] = 0;
  s->block_type_rb[4] = 1;
  s->block_type_rb[5] = 0;
  s->context_map = NULL;
  s->context_modes = NULL;
  s->dist_context_map = NULL;
  s->context_map_slice = NULL;
  s->literal_htree = NULL;
  s->dist_context_map_slice = NULL;
  s->dist_htree_index = 0;
  s->context_lookup = NULL;
  s->literal_hgroup.codes = NULL;
  s->literal_hgroup.htrees = NULL;
  s->insert_copy_hgroup.codes = NULL;
  s->insert_copy_hgroup.htrees = NULL;
  s->distance_hgroup.codes = NULL;
  s->distance_hgroup.htrees = NULL;
}

void BrotliDecoderStateCleanupAfterMetablock(BrotliDecoderState* s) {
  BROTLI_DECODER_FREE(s, s->context_modes);
  BROTLI_DECODER_FREE(s, s->context_map);
  BROTLI_DECODER_FREE(s, s->dist_context_map);
  BROTLI_DECODER_FREE(s, s->literal_hgroup.htrees);
  BROTLI_DECODER_FREE(s, s->insert_copy_hgroup.htrees);
  BROTLI_DECODER_FREE(s, s->distance_hgroup.htrees);
}

void BrotliDecoderStateCleanup(BrotliDecoderState* s) {
  BrotliDecoderStateCleanupAfterMetablock(s);

  BROTLI_DECODER_ON_FINISH(s);

  BROTLI_DECODER_FREE(s, s->compound_dictionary);
  BrotliSharedDictionaryDestroyInstance(s->dictionary);
  s->dictionary = NULL;
  BROTLI_DECODER_FREE(s, s->ringbuffer);
  BROTLI_DECODER_FREE(s, s->block_type_trees);
}

BROTLI_BOOL BrotliDecoderHuffmanTreeGroupInit(BrotliDecoderState* s,
    HuffmanTreeGroup* group, brotli_reg_t alphabet_size_max,
    brotli_reg_t alphabet_size_limit, brotli_reg_t ntrees) {
  /* 376 = 256 (1-st level table) + 4 + 7 + 15 + 31 + 63 (2-nd level mix-tables)
     This number is discovered "unlimited" "enough" calculator; it is actually
     a wee bigger than required in several cases (especially for alphabets with
     less than 16 symbols). */
  const size_t max_table_size = alphabet_size_limit + 376;
  const size_t code_size = sizeof(HuffmanCode) * ntrees * max_table_size;
  const size_t htree_size = sizeof(HuffmanCode*) * ntrees;
  /* Pointer alignment is, hopefully, wider than sizeof(HuffmanCode). */
  HuffmanCode** p = (HuffmanCode**)BROTLI_DECODER_ALLOC(s,
      code_size + htree_size);
  group->alphabet_size_max = (uint16_t)alphabet_size_max;
  group->alphabet_size_limit = (uint16_t)alphabet_size_limit;
  group->num_htrees = (uint16_t)ntrees;
  group->htrees = p;
  group->codes = p ? (HuffmanCode*)(&p[ntrees]) : NULL;
  return !!p;
}

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/dec/static_init.c ---- */
/* Copyright 2025 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include "static_init.h"

#include "../common/platform.h"
#include "../common/static_init.h"

#if (BROTLI_STATIC_INIT != BROTLI_STATIC_INIT_NONE)
#include "../common/dictionary.h"
#include "prefix.h"
#endif

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

#if (BROTLI_STATIC_INIT != BROTLI_STATIC_INIT_NONE)
static BROTLI_BOOL DoBrotliDecoderStaticInit(void) {
  BROTLI_BOOL ok = BrotliDecoderInitCmdLut(kCmdLut);
  if (!ok) return BROTLI_FALSE;
  return BROTLI_TRUE;
}
#endif  /* BROTLI_STATIC_INIT_NONE */

#if (BROTLI_STATIC_INIT == BROTLI_STATIC_INIT_EARLY)
static BROTLI_BOOL kEarlyInitOk;
static __attribute__((constructor)) void BrotliDecoderStaticInitEarly(void) {
  kEarlyInitOk = DoBrotliDecoderStaticInit();
}
#elif (BROTLI_STATIC_INIT == BROTLI_STATIC_INIT_LAZY)
static BROTLI_BOOL kLazyInitOk;
void BrotliDecoderLazyStaticInitInner(void) {
  kLazyInitOk = DoBrotliDecoderStaticInit();
}
#endif  /* BROTLI_STATIC_INIT_EARLY */

BROTLI_BOOL BrotliDecoderEnsureStaticInit(void) {
#if (BROTLI_STATIC_INIT == BROTLI_STATIC_INIT_NONE)
  return BROTLI_TRUE;
#elif (BROTLI_STATIC_INIT == BROTLI_STATIC_INIT_EARLY)
  return kEarlyInitOk;
#else
  return kLazyInitOk;
#endif
}

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/common/constants.c ---- */
/* Copyright 2013 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include "constants.h"

const BROTLI_MODEL("small")
BrotliPrefixCodeRange _kBrotliPrefixCodeRanges[BROTLI_NUM_BLOCK_LEN_SYMBOLS] = {
    {1, 2},     {5, 2},     {9, 2},   {13, 2},    {17, 3},    {25, 3},
    {33, 3},    {41, 3},    {49, 4},  {65, 4},    {81, 4},    {97, 4},
    {113, 5},   {145, 5},   {177, 5}, {209, 5},   {241, 6},   {305, 6},
    {369, 7},   {497, 8},   {753, 9}, {1265, 10}, {2289, 11}, {4337, 12},
    {8433, 13}, {16625, 24}};

/* ---- vendor/c/common/context.c ---- */
#include "context.h"

#include "platform.h"

/* Common context lookup table for all context modes. */
const BROTLI_MODEL("small") uint8_t _kBrotliContextLookupTable[2048] = {
  /* CONTEXT_LSB6, last byte. */
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
  16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
  32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
  48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
  16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
  32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
  48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
  16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
  32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
  48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
  16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
  32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
  48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,

  /* CONTEXT_LSB6, second last byte, */
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,

  /* CONTEXT_MSB6, last byte. */
   0,  0,  0,  0,  1,  1,  1,  1,  2,  2,  2,  2,  3,  3,  3,  3,
   4,  4,  4,  4,  5,  5,  5,  5,  6,  6,  6,  6,  7,  7,  7,  7,
   8,  8,  8,  8,  9,  9,  9,  9, 10, 10, 10, 10, 11, 11, 11, 11,
  12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15,
  16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19,
  20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 23, 23, 23, 23,
  24, 24, 24, 24, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27,
  28, 28, 28, 28, 29, 29, 29, 29, 30, 30, 30, 30, 31, 31, 31, 31,
  32, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 35, 35,
  36, 36, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39,
  40, 40, 40, 40, 41, 41, 41, 41, 42, 42, 42, 42, 43, 43, 43, 43,
  44, 44, 44, 44, 45, 45, 45, 45, 46, 46, 46, 46, 47, 47, 47, 47,
  48, 48, 48, 48, 49, 49, 49, 49, 50, 50, 50, 50, 51, 51, 51, 51,
  52, 52, 52, 52, 53, 53, 53, 53, 54, 54, 54, 54, 55, 55, 55, 55,
  56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 59, 59,
  60, 60, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 63,

  /* CONTEXT_MSB6, second last byte, */
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,

  /* CONTEXT_UTF8, last byte. */
  /* ASCII range. */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  4,  4,  0,  0,  4,  0,  0,
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
   8, 12, 16, 12, 12, 20, 12, 16, 24, 28, 12, 12, 32, 12, 36, 12,
  44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 32, 32, 24, 40, 28, 12,
  12, 48, 52, 52, 52, 48, 52, 52, 52, 48, 52, 52, 52, 52, 52, 48,
  52, 52, 52, 52, 52, 48, 52, 52, 52, 52, 52, 24, 12, 28, 12, 12,
  12, 56, 60, 60, 60, 56, 60, 60, 60, 56, 60, 60, 60, 60, 60, 56,
  60, 60, 60, 60, 60, 56, 60, 60, 60, 60, 60, 24, 12, 28, 12,  0,
  /* UTF8 continuation byte range. */
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  /* UTF8 lead byte range. */
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,

  /* CONTEXT_UTF8 second last byte. */
  /* ASCII range. */
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1,
  1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1,
  1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 0,
  /* UTF8 continuation byte range. */
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  /* UTF8 lead byte range. */
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,

  /* CONTEXT_SIGNED, last byte, same as the above values shifted by 3 bits. */
   0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
  16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
  16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
  16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
  32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
  32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
  32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
  40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
  40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
  40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
  48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 56,

  /* CONTEXT_SIGNED, second last byte. */
  0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
  6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7,
};

/* ---- vendor/c/common/dictionary.c ---- */
/* Copyright 2013 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include "dictionary.h"
#include "platform.h"

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

#if !defined(BROTLI_EXTERNAL_DICTIONARY_DATA)
/* Embed kBrotliDictionaryData */
#include "dictionary_inc.h"
static const BROTLI_MODEL("small") BrotliDictionary kBrotliDictionary = {
#else
static BROTLI_MODEL("small") BrotliDictionary kBrotliDictionary = {
#endif
  /* size_bits_by_length */
  {
    0, 0, 0, 0, 10, 10, 11, 11,
    10, 10, 10, 10, 10, 9, 9, 8,
    7, 7, 8, 7, 7, 6, 6, 5,
    5, 0, 0, 0, 0, 0, 0, 0
  },

  /* offsets_by_length */
  {
    0, 0, 0, 0, 0, 4096, 9216, 21504,
    35840, 44032, 53248, 63488, 74752, 87040, 93696, 100864,
    104704, 106752, 108928, 113536, 115968, 118528, 119872, 121280,
    122016, 122784, 122784, 122784, 122784, 122784, 122784, 122784
  },

  /* data_size ==  sizeof(kBrotliDictionaryData) */
  122784,

  /* data */
#if defined(BROTLI_EXTERNAL_DICTIONARY_DATA)
  NULL
#else
  kBrotliDictionaryData
#endif
};

const BrotliDictionary* BrotliGetDictionary(void) {
  return &kBrotliDictionary;
}

void BrotliSetDictionaryData(const uint8_t* data) {
#if defined(BROTLI_EXTERNAL_DICTIONARY_DATA)
  if (!!data && !kBrotliDictionary.data) {
    kBrotliDictionary.data = data;
  }
#else
  BROTLI_UNUSED(data);  // Appease -Werror=unused-parameter
#endif
}

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/common/platform.c ---- */
/* Copyright 2016 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include "platform.h"

/* Default brotli_alloc_func */
void* BrotliDefaultAllocFunc(void* opaque, size_t size) {
  BROTLI_UNUSED(opaque);
  return malloc(size);
}

/* Default brotli_free_func */
void BrotliDefaultFreeFunc(void* opaque, void* address) {
  BROTLI_UNUSED(opaque);
  free(address);
}

/* ---- vendor/c/common/shared_dictionary.c ---- */
/* Copyright 2017 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

/* Shared Dictionary definition and utilities. */

#include <brotli/shared_dictionary.h>

#include "dictionary.h"
#include "platform.h"
#include "shared_dictionary_internal.h"

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

#if defined(BROTLI_EXPERIMENTAL)

#define BROTLI_NUM_ENCODED_LENGTHS (SHARED_BROTLI_MAX_DICTIONARY_WORD_LENGTH \
    - SHARED_BROTLI_MIN_DICTIONARY_WORD_LENGTH + 1)

/* Max allowed by spec */
#define BROTLI_MAX_SIZE_BITS 15u

/* Returns BROTLI_TRUE on success, BROTLI_FALSE on failure. */
static BROTLI_BOOL ReadBool(const uint8_t* encoded, size_t size, size_t* pos,
    BROTLI_BOOL* result) {
  uint8_t value;
  size_t position = *pos;
  if (position >= size) return BROTLI_FALSE;  /* past file end */
  value = encoded[position++];
  if (value > 1) return BROTLI_FALSE;  /* invalid bool */
  *result = TO_BROTLI_BOOL(value);
  *pos = position;
  return BROTLI_TRUE;  /* success */
}

/* Returns BROTLI_TRUE on success, BROTLI_FALSE on failure. */
static BROTLI_BOOL ReadUint8(const uint8_t* encoded, size_t size, size_t* pos,
    uint8_t* result) {
  size_t position = *pos;
  if (position + sizeof(uint8_t) > size) return BROTLI_FALSE;
  *result = encoded[position++];
  *pos = position;
  return BROTLI_TRUE;
}

/* Returns BROTLI_TRUE on success, BROTLI_FALSE on failure. */
static BROTLI_BOOL ReadUint16(const uint8_t* encoded, size_t size, size_t* pos,
    uint16_t* result) {
  size_t position = *pos;
  if (position + sizeof(uint16_t) > size) return BROTLI_FALSE;
  *result = BROTLI_UNALIGNED_LOAD16LE(&encoded[position]);
  position += 2;
  *pos = position;
  return BROTLI_TRUE;
}

/* Reads a varint into a uint32_t, and returns error if it's too large */
/* Returns BROTLI_TRUE on success, BROTLI_FALSE on failure. */
static BROTLI_BOOL ReadVarint32(const uint8_t* encoded, size_t size,
    size_t* pos, uint32_t* result) {
  int num = 0;
  uint8_t byte;
  *result = 0;
  for (;;) {
    if (*pos >= size) return BROTLI_FALSE;
    byte = encoded[(*pos)++];
    if (num == 4 && byte > 15) return BROTLI_FALSE;
    *result |= (uint32_t)(byte & 127) << (num * 7);
    if (byte < 128) return BROTLI_TRUE;
    num++;
  }
}

/* Returns the total length of word list. */
static size_t BrotliSizeBitsToOffsets(const uint8_t* size_bits_by_length,
    uint32_t* offsets_by_length) {
  uint32_t pos = 0;
  uint32_t i;
  for (i = 0; i <= SHARED_BROTLI_MAX_DICTIONARY_WORD_LENGTH; i++) {
    offsets_by_length[i] = pos;
    if (size_bits_by_length[i] != 0) {
      pos += i << size_bits_by_length[i];
    }
  }
  return pos;
}

static BROTLI_BOOL ParseWordList(size_t size, const uint8_t* encoded,
    size_t* pos, BrotliDictionary* out) {
  size_t offset;
  size_t i;
  size_t position = *pos;
  if (position + BROTLI_NUM_ENCODED_LENGTHS > size) {
    return BROTLI_FALSE;
  }

  memset(out->size_bits_by_length, 0, SHARED_BROTLI_MIN_DICTIONARY_WORD_LENGTH);
  memcpy(out->size_bits_by_length + SHARED_BROTLI_MIN_DICTIONARY_WORD_LENGTH,
      &encoded[position], BROTLI_NUM_ENCODED_LENGTHS);
  for (i = SHARED_BROTLI_MIN_DICTIONARY_WORD_LENGTH;
      i <= SHARED_BROTLI_MAX_DICTIONARY_WORD_LENGTH; i++) {
    if (out->size_bits_by_length[i] > BROTLI_MAX_SIZE_BITS) {
      return BROTLI_FALSE;
    }
  }
  position += BROTLI_NUM_ENCODED_LENGTHS;
  offset = BrotliSizeBitsToOffsets(
      out->size_bits_by_length, out->offsets_by_length);

  out->data = &encoded[position];
  out->data_size = offset;
  position += offset;
  if (position > size) return BROTLI_FALSE;
  *pos = position;
  return BROTLI_TRUE;
}

/* Computes the cutOffTransforms of a BrotliTransforms which already has the
   transforms data correctly filled in. */
static void ComputeCutoffTransforms(BrotliTransforms* transforms) {
  uint32_t i;
  for (i = 0; i < BROTLI_TRANSFORMS_MAX_CUT_OFF + 1; i++) {
    transforms->cutOffTransforms[i] = -1;
  }
  for (i = 0; i < transforms->num_transforms; i++) {
    const uint8_t* prefix = BROTLI_TRANSFORM_PREFIX(transforms, i);
    uint8_t type = BROTLI_TRANSFORM_TYPE(transforms, i);
    const uint8_t* suffix = BROTLI_TRANSFORM_SUFFIX(transforms, i);
    if (type <= BROTLI_TRANSFORM_OMIT_LAST_9 && *prefix == 0 && *suffix == 0 &&
        transforms->cutOffTransforms[type] == -1) {
      transforms->cutOffTransforms[type] = (int16_t)i;
    }
  }
}

static BROTLI_BOOL ParsePrefixSuffixTable(size_t size, const uint8_t* encoded,
    size_t* pos, BrotliTransforms* out, uint16_t* out_table,
    size_t* out_table_size) {
  size_t position = *pos;
  size_t offset = 0;
  size_t stringlet_count = 0;  /* NUM_PREFIX_SUFFIX */
  size_t data_length = 0;

  /* PREFIX_SUFFIX_LENGTH */
  if (!ReadUint16(encoded, size, &position, &out->prefix_suffix_size)) {
    return BROTLI_FALSE;
  }
  data_length = out->prefix_suffix_size;

  /* Must at least have space for null terminator. */
  if (data_length < 1) return BROTLI_FALSE;
  out->prefix_suffix = &encoded[position];
  if (position + data_length >= size) return BROTLI_FALSE;
  while (BROTLI_TRUE) {
    /* STRING_LENGTH */
    size_t stringlet_len = encoded[position + offset];
    out_table[stringlet_count] = (uint16_t)offset;
    stringlet_count++;
    offset++;
    if (stringlet_len == 0) {
      if (offset == data_length) {
        break;
      } else {
        return BROTLI_FALSE;
      }
    }
    if (stringlet_count > 255) return BROTLI_FALSE;
    offset += stringlet_len;
    if (offset >= data_length) return BROTLI_FALSE;
  }

  position += data_length;
  *pos = position;
  *out_table_size = (uint16_t)stringlet_count;
  return BROTLI_TRUE;
}

static BROTLI_BOOL ParseTransformsList(size_t size, const uint8_t* encoded,
    size_t* pos, BrotliTransforms* out, uint16_t* prefix_suffix_table,
    size_t* prefix_suffix_count) {
  uint32_t i;
  BROTLI_BOOL has_params = BROTLI_FALSE;
  BROTLI_BOOL prefix_suffix_ok = BROTLI_FALSE;
  size_t position = *pos;
  size_t stringlet_cnt = 0;
  if (position >= size) return BROTLI_FALSE;

  prefix_suffix_ok = ParsePrefixSuffixTable(
      size, encoded, &position, out, prefix_suffix_table, &stringlet_cnt);
  if (!prefix_suffix_ok) return BROTLI_FALSE;
  out->prefix_suffix_map = prefix_suffix_table;
  *prefix_suffix_count = stringlet_cnt;

  out->num_transforms = encoded[position++];
  out->transforms = &encoded[position];
  position += (size_t)out->num_transforms * 3;
  if (position > size) return BROTLI_FALSE;
  /* Check for errors and read extra parameters. */
  for (i = 0; i < out->num_transforms; i++) {
    uint8_t prefix_id = BROTLI_TRANSFORM_PREFIX_ID(out, i);
    uint8_t type = BROTLI_TRANSFORM_TYPE(out, i);
    uint8_t suffix_id = BROTLI_TRANSFORM_SUFFIX_ID(out, i);
    if (prefix_id >= stringlet_cnt) return BROTLI_FALSE;
    if (type >= BROTLI_NUM_TRANSFORM_TYPES) return BROTLI_FALSE;
    if (suffix_id >= stringlet_cnt) return BROTLI_FALSE;
    if (type == BROTLI_TRANSFORM_SHIFT_FIRST ||
        type == BROTLI_TRANSFORM_SHIFT_ALL) {
      has_params = BROTLI_TRUE;
    }
  }
  if (has_params) {
    out->params = &encoded[position];
    position += (size_t)out->num_transforms * 2;
    if (position > size) return BROTLI_FALSE;
    for (i = 0; i < out->num_transforms; i++) {
      uint8_t type = BROTLI_TRANSFORM_TYPE(out, i);
      if (type != BROTLI_TRANSFORM_SHIFT_FIRST &&
          type != BROTLI_TRANSFORM_SHIFT_ALL) {
        if (out->params[i * 2] != 0 || out->params[i * 2 + 1] != 0) {
          return BROTLI_FALSE;
        }
      }
    }
  } else {
    out->params = NULL;
  }
  ComputeCutoffTransforms(out);
  *pos = position;
  return BROTLI_TRUE;
}

static BROTLI_BOOL DryParseDictionary(const uint8_t* encoded,
    size_t size, uint32_t* num_prefix, BROTLI_BOOL* is_custom_static_dict) {
  size_t pos = 0;
  uint32_t chunk_size = 0;
  uint8_t num_word_lists;
  uint8_t num_transform_lists;
  *is_custom_static_dict = BROTLI_FALSE;
  *num_prefix = 0;

  /* Skip magic header bytes. */
  pos += 2;

  /* LZ77_DICTIONARY_LENGTH */
  if (!ReadVarint32(encoded, size, &pos, &chunk_size)) return BROTLI_FALSE;
  if (chunk_size != 0) {
    /* This limitation is not specified but the 32-bit Brotli decoder for now */
    if (chunk_size > 1073741823) return BROTLI_FALSE;
    *num_prefix = 1;
    if (pos + chunk_size > size) return BROTLI_FALSE;
    pos += chunk_size;
  }

  if (!ReadUint8(encoded, size, &pos, &num_word_lists)) {
    return BROTLI_FALSE;
  }
  if (!ReadUint8(encoded, size, &pos, &num_transform_lists)) {
    return BROTLI_FALSE;
  }

  if (num_word_lists > 0 || num_transform_lists > 0) {
    *is_custom_static_dict = BROTLI_TRUE;
  }

  return BROTLI_TRUE;
}

static BROTLI_BOOL ParseDictionary(const uint8_t* encoded, size_t size,
    BrotliSharedDictionary* dict) {
  uint32_t i;
  size_t pos = 0;
  uint32_t chunk_size = 0;
  size_t total_prefix_suffix_count = 0;
  size_t transform_list_start[SHARED_BROTLI_NUM_DICTIONARY_CONTEXTS];
  uint16_t temporary_prefix_suffix_table[256];

  /* Skip magic header bytes. */
  pos += 2;

  /* LZ77_DICTIONARY_LENGTH */
  if (!ReadVarint32(encoded, size, &pos, &chunk_size)) return BROTLI_FALSE;
  if (chunk_size != 0) {
    if (pos + chunk_size > size) return BROTLI_FALSE;
    dict->prefix_size[dict->num_prefix] = chunk_size;
    dict->prefix[dict->num_prefix] = &encoded[pos];
    dict->num_prefix++;
    /* LZ77_DICTIONARY_LENGTH bytes. */
    pos += chunk_size;
  }

  /* NUM_WORD_LISTS */
  if (!ReadUint8(encoded, size, &pos, &dict->num_word_lists)) {
    return BROTLI_FALSE;
  }
  if (dict->num_word_lists > SHARED_BROTLI_NUM_DICTIONARY_CONTEXTS) {
    return BROTLI_FALSE;
  }

  if (dict->num_word_lists != 0) {
    dict->words_instances = (BrotliDictionary*)dict->alloc_func(
        dict->memory_manager_opaque,
        dict->num_word_lists * sizeof(*dict->words_instances));
    if (!dict->words_instances) return BROTLI_FALSE;  /* OOM */
  }
  for (i = 0; i < dict->num_word_lists; i++) {
    if (!ParseWordList(size, encoded, &pos, &dict->words_instances[i])) {
      return BROTLI_FALSE;
    }
  }

  /* NUM_TRANSFORM_LISTS */
  if (!ReadUint8(encoded, size, &pos, &dict->num_transform_lists)) {
    return BROTLI_FALSE;
  }
  if (dict->num_transform_lists > SHARED_BROTLI_NUM_DICTIONARY_CONTEXTS) {
    return BROTLI_FALSE;
  }

  if (dict->num_transform_lists != 0) {
    dict->transforms_instances = (BrotliTransforms*)dict->alloc_func(
        dict->memory_manager_opaque,
        dict->num_transform_lists * sizeof(*dict->transforms_instances));
    if (!dict->transforms_instances) return BROTLI_FALSE;  /* OOM */
  }
  for (i = 0; i < dict->num_transform_lists; i++) {
    BROTLI_BOOL ok = BROTLI_FALSE;
    size_t prefix_suffix_count = 0;
    transform_list_start[i] = pos;
    dict->transforms_instances[i].prefix_suffix_map =
        temporary_prefix_suffix_table;
    ok = ParseTransformsList(
        size, encoded, &pos, &dict->transforms_instances[i],
        temporary_prefix_suffix_table, &prefix_suffix_count);
    if (!ok) return BROTLI_FALSE;
    total_prefix_suffix_count += prefix_suffix_count;
  }
  if (total_prefix_suffix_count != 0) {
    dict->prefix_suffix_maps = (uint16_t*)dict->alloc_func(
        dict->memory_manager_opaque,
        total_prefix_suffix_count * sizeof(*dict->prefix_suffix_maps));
    if (!dict->prefix_suffix_maps) return BROTLI_FALSE;  /* OOM */
  }
  total_prefix_suffix_count = 0;
  for (i = 0; i < dict->num_transform_lists; i++) {
    size_t prefix_suffix_count = 0;
    size_t position = transform_list_start[i];
    uint16_t* prefix_suffix_map =
      &dict->prefix_suffix_maps[total_prefix_suffix_count];
    BROTLI_BOOL ok = ParsePrefixSuffixTable(
        size, encoded, &position, &dict->transforms_instances[i],
        prefix_suffix_map, &prefix_suffix_count);
    if (!ok) return BROTLI_FALSE;
    dict->transforms_instances[i].prefix_suffix_map = prefix_suffix_map;
    total_prefix_suffix_count += prefix_suffix_count;
  }

  if (dict->num_word_lists != 0 || dict->num_transform_lists != 0) {
    if (!ReadUint8(encoded, size, &pos, &dict->num_dictionaries)) {
      return BROTLI_FALSE;
    }
    if (dict->num_dictionaries == 0 ||
        dict->num_dictionaries > SHARED_BROTLI_NUM_DICTIONARY_CONTEXTS) {
      return BROTLI_FALSE;
    }
    for (i = 0; i < dict->num_dictionaries; i++) {
      uint8_t words_index;
      uint8_t transforms_index;
      if (!ReadUint8(encoded, size, &pos, &words_index)) {
        return BROTLI_FALSE;
      }
      if (words_index > dict->num_word_lists) return BROTLI_FALSE;
      if (!ReadUint8(encoded, size, &pos, &transforms_index)) {
        return BROTLI_FALSE;
      }
      if (transforms_index > dict->num_transform_lists) return BROTLI_FALSE;
      dict->words[i] = words_index == dict->num_word_lists ?
          BrotliGetDictionary() : &dict->words_instances[words_index];
      dict->transforms[i] = transforms_index == dict->num_transform_lists ?
          BrotliGetTransforms(): &dict->transforms_instances[transforms_index];
    }
    /* CONTEXT_ENABLED */
    if (!ReadBool(encoded, size, &pos, &dict->context_based)) {
      return BROTLI_FALSE;
    }

    /* CONTEXT_MAP */
    if (dict->context_based) {
      for (i = 0; i < SHARED_BROTLI_NUM_DICTIONARY_CONTEXTS; i++) {
        if (!ReadUint8(encoded, size, &pos, &dict->context_map[i])) {
          return BROTLI_FALSE;
        }
        if (dict->context_map[i] >= dict->num_dictionaries) {
          return BROTLI_FALSE;
        }
      }
    }
  } else {
    dict->context_based = BROTLI_FALSE;
    dict->num_dictionaries = 1;
    dict->words[0] = BrotliGetDictionary();
    dict->transforms[0] = BrotliGetTransforms();
  }

  return BROTLI_TRUE;
}

/* Decodes shared dictionary and verifies correctness.
   Returns BROTLI_TRUE if dictionary is valid, BROTLI_FALSE otherwise.
   The BrotliSharedDictionary must already have been initialized. If the
   BrotliSharedDictionary already contains data, compound dictionaries
   will be appended, but an error will be returned if it already has
   custom words or transforms.
   TODO(lode): link to RFC for shared brotli once published. */
static BROTLI_BOOL DecodeSharedDictionary(
    const uint8_t* encoded, size_t size, BrotliSharedDictionary* dict) {
  uint32_t num_prefix = 0;
  BROTLI_BOOL is_custom_static_dict = BROTLI_FALSE;
  BROTLI_BOOL has_custom_static_dict =
      dict->num_word_lists > 0 || dict->num_transform_lists > 0;

  /* Check magic header bytes. */
  if (size < 2) return BROTLI_FALSE;
  if (encoded[0] != 0x91 || encoded[1] != 0) return BROTLI_FALSE;

  if (!DryParseDictionary(encoded, size, &num_prefix, &is_custom_static_dict)) {
    return BROTLI_FALSE;
  }

  if (num_prefix + dict->num_prefix > SHARED_BROTLI_MAX_COMPOUND_DICTS) {
    return BROTLI_FALSE;
  }

  /* Cannot combine different static dictionaries, only prefix dictionaries */
  if (has_custom_static_dict && is_custom_static_dict) return BROTLI_FALSE;

  return ParseDictionary(encoded, size, dict);
}

#endif  /* BROTLI_EXPERIMENTAL */

void BrotliSharedDictionaryDestroyInstance(
    BrotliSharedDictionary* dict) {
  if (!dict) {
    return;
  } else {
    brotli_free_func free_func = dict->free_func;
    void* opaque = dict->memory_manager_opaque;
    /* Cleanup. */
    free_func(opaque, dict->words_instances);
    free_func(opaque, dict->transforms_instances);
    free_func(opaque, dict->prefix_suffix_maps);
    /* Self-destruction. */
    free_func(opaque, dict);
  }
}

BROTLI_BOOL BrotliSharedDictionaryAttach(
    BrotliSharedDictionary* dict, BrotliSharedDictionaryType type,
    size_t data_size, const uint8_t data[BROTLI_ARRAY_PARAM(data_size)]) {
  if (!dict) {
    return BROTLI_FALSE;
  }
#if defined(BROTLI_EXPERIMENTAL)
  if (type == BROTLI_SHARED_DICTIONARY_SERIALIZED) {
    return DecodeSharedDictionary(data, data_size, dict);
  }
#endif  /* BROTLI_EXPERIMENTAL */
  if (type == BROTLI_SHARED_DICTIONARY_RAW) {
    if (dict->num_prefix >= SHARED_BROTLI_MAX_COMPOUND_DICTS) {
      return BROTLI_FALSE;
    }
    dict->prefix_size[dict->num_prefix] = data_size;
    dict->prefix[dict->num_prefix] = data;
    dict->num_prefix++;
    return BROTLI_TRUE;
  }
  return BROTLI_FALSE;
}

BrotliSharedDictionary* BrotliSharedDictionaryCreateInstance(
    brotli_alloc_func alloc_func, brotli_free_func free_func, void* opaque) {
  BrotliSharedDictionary* dict = 0;
  if (!alloc_func && !free_func) {
    dict = (BrotliSharedDictionary*)malloc(sizeof(BrotliSharedDictionary));
  } else if (alloc_func && free_func) {
    dict = (BrotliSharedDictionary*)alloc_func(
        opaque, sizeof(BrotliSharedDictionary));
  }
  if (dict == 0) {
    return 0;
  }

  /* TODO(eustas): explicitly initialize all the fields? */
  memset(dict, 0, sizeof(BrotliSharedDictionary));

  dict->context_based = BROTLI_FALSE;
  dict->num_dictionaries = 1;
  dict->num_word_lists = 0;
  dict->num_transform_lists = 0;

  dict->words[0] = BrotliGetDictionary();
  dict->transforms[0] = BrotliGetTransforms();

  dict->alloc_func = alloc_func ? alloc_func : BrotliDefaultAllocFunc;
  dict->free_func = free_func ? free_func : BrotliDefaultFreeFunc;
  dict->memory_manager_opaque = opaque;

  return dict;
}

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif

/* ---- vendor/c/common/transform.c ---- */
/* Copyright 2013 Google Inc. All Rights Reserved.

   Distributed under MIT license.
   See file LICENSE for detail or copy at https://opensource.org/licenses/MIT
*/

#include "platform.h"
#include "transform.h"

#if defined(__cplusplus) || defined(c_plusplus)
extern "C" {
#endif

/* RFC 7932 transforms string data */
static const BROTLI_MODEL("small") char kPrefixSuffix[217] =
      "\1 \2, \10 of the \4 of \2s \1.\5 and \4 "
/* 0x  _0 _2  __5        _E    _3  _6 _8     _E */
      "in \1\"\4 to \2\">\1\n\2. \1]\5 for \3 a \6 "
/* 2x     _3_ _5    _A_  _D_ _F  _2 _4     _A   _E */
      "that \1\'\6 with \6 from \4 by \1(\6. T"
/* 4x       _5_ _7      _E      _5    _A _C */
      "he \4 on \4 as \4 is \4ing \2\n\t\1:\3ed "
/* 6x     _3    _8    _D    _2    _7_ _ _A _C */
      "\2=\"\4 at \3ly \1,\2=\'\5.com/\7. This \5"
/* 8x  _0 _ _3    _8   _C _E _ _1     _7       _F */
      " not \3er \3al \4ful \4ive \5less \4es"
/* Ax       _5   _9   _D    _2    _7     _D */
      "t \4ize \2\xc2\xa0\4ous \5 the \2e "; /* \0 - implicit trailing zero. */
/* Cx    _2    _7___ ___ _A    _F     _5        _8 */

static const BROTLI_MODEL("small") uint16_t kPrefixSuffixMap[50] = {
  0x00, 0x02, 0x05, 0x0E, 0x13, 0x16, 0x18, 0x1E, 0x23, 0x25,
  0x2A, 0x2D, 0x2F, 0x32, 0x34, 0x3A, 0x3E, 0x45, 0x47, 0x4E,
  0x55, 0x5A, 0x5C, 0x63, 0x68, 0x6D, 0x72, 0x77, 0x7A, 0x7C,
  0x80, 0x83, 0x88, 0x8C, 0x8E, 0x91, 0x97, 0x9F, 0xA5, 0xA9,
  0xAD, 0xB2, 0xB7, 0xBD, 0xC2, 0xC7, 0xCA, 0xCF, 0xD5, 0xD8
};

/* RFC 7932 transforms */
static const BROTLI_MODEL("small") uint8_t kTransformsData[] = {
  49, BROTLI_TRANSFORM_IDENTITY, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 0,
   0, BROTLI_TRANSFORM_IDENTITY, 0,
  49, BROTLI_TRANSFORM_OMIT_FIRST_1, 49,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 0,
  49, BROTLI_TRANSFORM_IDENTITY, 47,
   0, BROTLI_TRANSFORM_IDENTITY, 49,
   4, BROTLI_TRANSFORM_IDENTITY, 0,
  49, BROTLI_TRANSFORM_IDENTITY, 3,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 6,
  49, BROTLI_TRANSFORM_OMIT_FIRST_2, 49,
  49, BROTLI_TRANSFORM_OMIT_LAST_1, 49,
   1, BROTLI_TRANSFORM_IDENTITY, 0,
  49, BROTLI_TRANSFORM_IDENTITY, 1,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 0,
  49, BROTLI_TRANSFORM_IDENTITY, 7,
  49, BROTLI_TRANSFORM_IDENTITY, 9,
  48, BROTLI_TRANSFORM_IDENTITY, 0,
  49, BROTLI_TRANSFORM_IDENTITY, 8,
  49, BROTLI_TRANSFORM_IDENTITY, 5,
  49, BROTLI_TRANSFORM_IDENTITY, 10,
  49, BROTLI_TRANSFORM_IDENTITY, 11,
  49, BROTLI_TRANSFORM_OMIT_LAST_3, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 13,
  49, BROTLI_TRANSFORM_IDENTITY, 14,
  49, BROTLI_TRANSFORM_OMIT_FIRST_3, 49,
  49, BROTLI_TRANSFORM_OMIT_LAST_2, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 15,
  49, BROTLI_TRANSFORM_IDENTITY, 16,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 12,
   5, BROTLI_TRANSFORM_IDENTITY, 49,
   0, BROTLI_TRANSFORM_IDENTITY, 1,
  49, BROTLI_TRANSFORM_OMIT_FIRST_4, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 18,
  49, BROTLI_TRANSFORM_IDENTITY, 17,
  49, BROTLI_TRANSFORM_IDENTITY, 19,
  49, BROTLI_TRANSFORM_IDENTITY, 20,
  49, BROTLI_TRANSFORM_OMIT_FIRST_5, 49,
  49, BROTLI_TRANSFORM_OMIT_FIRST_6, 49,
  47, BROTLI_TRANSFORM_IDENTITY, 49,
  49, BROTLI_TRANSFORM_OMIT_LAST_4, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 22,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 23,
  49, BROTLI_TRANSFORM_IDENTITY, 24,
  49, BROTLI_TRANSFORM_IDENTITY, 25,
  49, BROTLI_TRANSFORM_OMIT_LAST_7, 49,
  49, BROTLI_TRANSFORM_OMIT_LAST_1, 26,
  49, BROTLI_TRANSFORM_IDENTITY, 27,
  49, BROTLI_TRANSFORM_IDENTITY, 28,
   0, BROTLI_TRANSFORM_IDENTITY, 12,
  49, BROTLI_TRANSFORM_IDENTITY, 29,
  49, BROTLI_TRANSFORM_OMIT_FIRST_9, 49,
  49, BROTLI_TRANSFORM_OMIT_FIRST_7, 49,
  49, BROTLI_TRANSFORM_OMIT_LAST_6, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 21,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 1,
  49, BROTLI_TRANSFORM_OMIT_LAST_8, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 31,
  49, BROTLI_TRANSFORM_IDENTITY, 32,
  47, BROTLI_TRANSFORM_IDENTITY, 3,
  49, BROTLI_TRANSFORM_OMIT_LAST_5, 49,
  49, BROTLI_TRANSFORM_OMIT_LAST_9, 49,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 1,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 8,
   5, BROTLI_TRANSFORM_IDENTITY, 21,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 0,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 10,
  49, BROTLI_TRANSFORM_IDENTITY, 30,
   0, BROTLI_TRANSFORM_IDENTITY, 5,
  35, BROTLI_TRANSFORM_IDENTITY, 49,
  47, BROTLI_TRANSFORM_IDENTITY, 2,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 17,
  49, BROTLI_TRANSFORM_IDENTITY, 36,
  49, BROTLI_TRANSFORM_IDENTITY, 33,
   5, BROTLI_TRANSFORM_IDENTITY, 0,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 21,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 5,
  49, BROTLI_TRANSFORM_IDENTITY, 37,
   0, BROTLI_TRANSFORM_IDENTITY, 30,
  49, BROTLI_TRANSFORM_IDENTITY, 38,
   0, BROTLI_TRANSFORM_UPPERCASE_ALL, 0,
  49, BROTLI_TRANSFORM_IDENTITY, 39,
   0, BROTLI_TRANSFORM_UPPERCASE_ALL, 49,
  49, BROTLI_TRANSFORM_IDENTITY, 34,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 8,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 12,
   0, BROTLI_TRANSFORM_IDENTITY, 21,
  49, BROTLI_TRANSFORM_IDENTITY, 40,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 12,
  49, BROTLI_TRANSFORM_IDENTITY, 41,
  49, BROTLI_TRANSFORM_IDENTITY, 42,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 17,
  49, BROTLI_TRANSFORM_IDENTITY, 43,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 5,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 10,
   0, BROTLI_TRANSFORM_IDENTITY, 34,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 33,
  49, BROTLI_TRANSFORM_IDENTITY, 44,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 5,
  45, BROTLI_TRANSFORM_IDENTITY, 49,
   0, BROTLI_TRANSFORM_IDENTITY, 33,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 30,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 30,
  49, BROTLI_TRANSFORM_IDENTITY, 46,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 1,
  49, BROTLI_TRANSFORM_UPPERCASE_FIRST, 34,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 33,
   0, BROTLI_TRANSFORM_UPPERCASE_ALL, 30,
   0, BROTLI_TRANSFORM_UPPERCASE_ALL, 1,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 33,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 21,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 12,
   0, BROTLI_TRANSFORM_UPPERCASE_ALL, 5,
  49, BROTLI_TRANSFORM_UPPERCASE_ALL, 34,
   0, BROTLI_TRANSFORM_UPPERCASE_ALL, 12,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 30,
   0, BROTLI_TRANSFORM_UPPERCASE_ALL, 34,
   0, BROTLI_TRANSFORM_UPPERCASE_FIRST, 34,
};

static const BROTLI_MODEL("small")
BrotliTransforms kBrotliTransforms = {
  sizeof(kPrefixSuffix),
  (const uint8_t*)kPrefixSuffix,
  kPrefixSuffixMap,
  sizeof(kTransformsData) / (3 * sizeof(kTransformsData[0])),
  kTransformsData,
  NULL,  /* no extra parameters */
  {0, 12, 27, 23, 42, 63, 56, 48, 59, 64}
};

const BrotliTransforms* BrotliGetTransforms(void) {
  return &kBrotliTransforms;
}

static int ToUpperCase(uint8_t* p) {
  if (p[0] < 0xC0) {
    if (p[0] >= 'a' && p[0] <= 'z') {
      p[0] ^= 32;
    }
    return 1;
  }
  /* An overly simplified uppercasing model for UTF-8. */
  if (p[0] < 0xE0) {
    p[1] ^= 32;
    return 2;
  }
  /* An arbitrary transform for three byte characters. */
  p[2] ^= 5;
  return 3;
}

static int Shift(uint8_t* word, int word_len, uint16_t parameter) {
  /* Limited sign extension: scalar < (1 << 24). */
  uint32_t scalar =
      (parameter & 0x7FFFu) + (0x1000000u - (parameter & 0x8000u));
  if (word[0] < 0x80) {
    /* 1-byte rune / 0sssssss / 7 bit scalar (ASCII). */
    scalar += (uint32_t)word[0];
    word[0] = (uint8_t)(scalar & 0x7Fu);
    return 1;
  } else if (word[0] < 0xC0) {
    /* Continuation / 10AAAAAA. */
    return 1;
  } else if (word[0] < 0xE0) {
    /* 2-byte rune / 110sssss AAssssss / 11 bit scalar. */
    if (word_len < 2) return 1;
    scalar += (uint32_t)((word[1] & 0x3Fu) | ((word[0] & 0x1Fu) << 6u));
    word[0] = (uint8_t)(0xC0 | ((scalar >> 6u) & 0x1F));
    word[1] = (uint8_t)((word[1] & 0xC0) | (scalar & 0x3F));
    return 2;
  } else if (word[0] < 0xF0) {
    /* 3-byte rune / 1110ssss AAssssss BBssssss / 16 bit scalar. */
    if (word_len < 3) return word_len;
    scalar += (uint32_t)((word[2] & 0x3Fu) | ((word[1] & 0x3Fu) << 6u) |
        ((word[0] & 0x0Fu) << 12u));
    word[0] = (uint8_t)(0xE0 | ((scalar >> 12u) & 0x0F));
    word[1] = (uint8_t)((word[1] & 0xC0) | ((scalar >> 6u) & 0x3F));
    word[2] = (uint8_t)((word[2] & 0xC0) | (scalar & 0x3F));
    return 3;
  } else if (word[0] < 0xF8) {
    /* 4-byte rune / 11110sss AAssssss BBssssss CCssssss / 21 bit scalar. */
    if (word_len < 4) return word_len;
    scalar += (uint32_t)((word[3] & 0x3Fu) | ((word[2] & 0x3Fu) << 6u) |
        ((word[1] & 0x3Fu) << 12u) | ((word[0] & 0x07u) << 18u));
    word[0] = (uint8_t)(0xF0 | ((scalar >> 18u) & 0x07));
    word[1] = (uint8_t)((word[1] & 0xC0) | ((scalar >> 12u) & 0x3F));
    word[2] = (uint8_t)((word[2] & 0xC0) | ((scalar >> 6u) & 0x3F));
    word[3] = (uint8_t)((word[3] & 0xC0) | (scalar & 0x3F));
    return 4;
  }
  return 1;
}

int BrotliTransformDictionaryWord(uint8_t* dst, const uint8_t* word, int len,
    const BrotliTransforms* transforms, int transform_idx) {
  int idx = 0;
  const uint8_t* prefix = BROTLI_TRANSFORM_PREFIX(transforms, transform_idx);
  uint8_t type = BROTLI_TRANSFORM_TYPE(transforms, transform_idx);
  const uint8_t* suffix = BROTLI_TRANSFORM_SUFFIX(transforms, transform_idx);
  {
    int prefix_len = *prefix++;
    while (prefix_len--) { dst[idx++] = *prefix++; }
  }
  {
    const int t = type;
    int i = 0;
    if (t <= BROTLI_TRANSFORM_OMIT_LAST_9) {
      len -= t;
    } else if (t >= BROTLI_TRANSFORM_OMIT_FIRST_1
        && t <= BROTLI_TRANSFORM_OMIT_FIRST_9) {
      int skip = t - (BROTLI_TRANSFORM_OMIT_FIRST_1 - 1);
      word += skip;
      len -= skip;
    }
    while (i < len) { dst[idx++] = word[i++]; }
    if (t == BROTLI_TRANSFORM_UPPERCASE_FIRST) {
      ToUpperCase(&dst[idx - len]);
    } else if (t == BROTLI_TRANSFORM_UPPERCASE_ALL) {
      uint8_t* uppercase = &dst[idx - len];
      while (len > 0) {
        int step = ToUpperCase(uppercase);
        uppercase += step;
        len -= step;
      }
    } else if (t == BROTLI_TRANSFORM_SHIFT_FIRST) {
      uint16_t param = (uint16_t)(transforms->params[transform_idx * 2]
          + (transforms->params[transform_idx * 2 + 1] << 8u));
      Shift(&dst[idx - len], len, param);
    } else if (t == BROTLI_TRANSFORM_SHIFT_ALL) {
      uint16_t param = (uint16_t)(transforms->params[transform_idx * 2]
          + (transforms->params[transform_idx * 2 + 1] << 8u));
      uint8_t* shift = &dst[idx - len];
      while (len > 0) {
        int step = Shift(shift, len, param);
        shift += step;
        len -= step;
      }
    }
  }
  {
    int suffix_len = *suffix++;
    while (suffix_len--) { dst[idx++] = *suffix++; }
    return idx;
  }
}

#if defined(__cplusplus) || defined(c_plusplus)
}  /* extern "C" */
#endif


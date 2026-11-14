/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

   Exported entry points for testing the zstd functions in libzstd_huf.so,
   which are hidden, as they are in libzstd itself: build_zstd.sh compiles
   zstd's sources with -fvisibility=hidden, so that the calls between them
   are direct, and this file with the default visibility. */
#include <stddef.h>
#define HUF_STATIC_LINKING_ONLY
#define FSE_STATIC_LINKING_ONLY
#include "huf.h"
#include "fse.h"
#include "error_private.h"

#define API __attribute__((visibility("default")))

API size_t zhuf_decompress1x1(HUF_DTable *dctx, void *dst, size_t dstSize,
                              const void *cSrc, size_t cSrcSize,
                              void *workSpace, size_t wkspSize, int flags) {
  return HUF_decompress1X1_DCtx_wksp(dctx, dst, dstSize, cSrc, cSrcSize,
                                     workSpace, wkspSize, flags);
}

API size_t zhuf_readncount(short *normalizedCounter, unsigned *maxSVPtr,
                           unsigned *tableLogPtr, const void *rBuffer,
                           size_t rBuffSize) {
  return FSE_readNCount(normalizedCounter, maxSVPtr, tableLogPtr, rBuffer,
                        rBuffSize);
}

API size_t zhuf_readstats(BYTE *huffWeight, size_t hwSize, U32 *rankStats,
                          U32 *nbSymbolsPtr, U32 *tableLogPtr,
                          const void *src, size_t srcSize) {
  return HUF_readStats(huffWeight, hwSize, rankStats, nbSymbolsPtr,
                       tableLogPtr, src, srcSize);
}

API unsigned zhuf_iserror(size_t code) { return ERR_isError(code); }

API const char *zhuf_errorname(size_t code) { return ERR_getErrorName(code); }

/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

   Test driver for zstd's Huffman decoding of literals.
   Reads commands from stdin, one per line, and prints one result line each:
     D n HEX        HUF_decompress1X1_DCtx_wksp into a buffer of n bytes
                    -> "OK HEXOUT" or "ERR name"
     Q flags n HEX  HUF_readDTableX1_wksp, and HUF_decompress4X_usingDTable
                    of the rest into a buffer of n bytes, with the flags
                    given (32 for HUF_flags_disableFast)
                    -> "OK HEXOUT" or "ERR name"
     C maxsv log HEX  HUF_compress1X_repeat of the bytes (for test inputs)
                    -> "OK HEX", "NONE" (not compressed) or "ERR name"
     E maxsv log HEX  HUF_compress4X_repeat of the bytes (for test inputs)
                    -> "OK HEX", "NONE" (not compressed) or "ERR name"
     N HEX          FSE_readNCount with maxSymbolValue 255
                    -> "OK size maxsv tablelog c0 c1 ..." or "ERR name"
     S HEX          HUF_readStats -> "OK size nbsym tablelog w0 w1 ..."
                    or "ERR name"
     W HEX          HUF_writeCTable_wksp for the code lengths given as one
                    byte per symbol 0 .. maxsv (0 for absent)
                    -> "OK HEX" or "ERR name"
     F al maxsv c0 .. cmaxsv HEX
                    FSE_writeNCount of the normalized counts c0 ..., then
                    FSE_compress_usingCTable of the bytes with that table
                    -> "OK HEX", "NONE" (not compressed) or "ERR name"
   Inputs and outputs are copied to heap blocks of their exact sizes, so
   that a sanitizer build detects any access outside them. D also checks
   the 16 bytes after the output.

   Built with -DZHUF_LIB, D, N and S use the functions of the library
   libzstd_huf.so made by ../../arm/zstd/build_zstd.sh, through its exported
   entry points, and Q, which has none, answers "ERR unsupported";
   otherwise they use zstd's functions linked in directly. C, E, W and F,
   which make test inputs, always use the encoder linked in.               */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define HUF_STATIC_LINKING_ONLY
#define FSE_STATIC_LINKING_ONLY
#include "huf.h"
#include "fse.h"
#include "error_private.h"

#ifdef ZHUF_LIB
size_t zhuf_decompress1x1(HUF_DTable *, void *, size_t, const void *, size_t,
                          void *, size_t, int);
size_t zhuf_readncount(short *, unsigned *, unsigned *, const void *, size_t);
size_t zhuf_readstats(BYTE *, size_t, U32 *, U32 *, U32 *, const void *,
                      size_t);
#define DECOMPRESS1X1 zhuf_decompress1x1
#define READNCOUNT zhuf_readncount
#define READSTATS zhuf_readstats
#else
#define DECOMPRESS1X1 HUF_decompress1X1_DCtx_wksp
#define READNCOUNT FSE_readNCount
#define READSTATS HUF_readStats
#endif

static unsigned char inb[1 << 20], outb[1 << 20];

static size_t unhex(const char *s, unsigned char *b) {
  size_t n = 0;
  while (s[0] && s[1] && s[0] != '\n') {
    unsigned x; sscanf(s, "%2x", &x); b[n++] = (unsigned char)x; s += 2;
  }
  return n;
}
static void hex(const unsigned char *b, size_t n) {
  for (size_t i = 0; i < n; i++) printf("%02x", b[i]);
}
static char line[1 << 22];

static unsigned char *copy(const unsigned char *b, size_t n) {
  unsigned char *c = malloc(n ? n : 1);
  memcpy(c, b, n);
  return c;
}

int main(void) {
  static HUF_DTable dt[HUF_DTABLE_SIZE(12)];
  static U32 wksp[HUF_DECOMPRESS_WORKSPACE_SIZE_U32];
  static U64 cwksp[HUF_WORKSPACE_SIZE_U64];
  while (fgets(line, sizeof line, stdin)) {
    char *p = line;
    if (p[0] == 'D') {
      size_t n = strtoul(p + 2, &p, 10);
      size_t len = unhex(p + 1, inb);
      unsigned char *in = copy(inb, len), *out = malloc(n + 16);
      dt[0] = (HUF_DTable)(12 * 0x1000001);
      memset(out, 0xAA, n + 16);
      size_t r = DECOMPRESS1X1(dt, out, n, in, len, wksp,
                                             sizeof wksp, 0);
      for (size_t i = n; i < n + 16; i++)
        if (out[i] != 0xAA) { printf("OOB "); break; }
      if (ERR_isError(r)) printf("ERR %s\n", ERR_getErrorName(r));
      else { printf("OK "); hex(out, r); printf("\n"); }
      free(in); free(out);
    } else if (p[0] == 'Q') {
      int flags = (int)strtol(p + 2, &p, 10);
      size_t n = strtoul(p + 1, &p, 10);
      size_t len = unhex(p + 1, inb);
#ifdef ZHUF_LIB
      (void)flags; (void)n; (void)len;
      printf("ERR unsupported\n");
#else
      unsigned char *in = copy(inb, len), *out = malloc(n + 16);
      dt[0] = (HUF_DTable)(12 * 0x1000001);
      memset(out, 0xAA, n + 16);
      size_t h = HUF_readDTableX1_wksp(dt, in, len, wksp, sizeof wksp, flags);
      size_t r = ERR_isError(h) ? h : h >= len ? ERROR(srcSize_wrong) :
        HUF_decompress4X_usingDTable(out, n, in + h, len - h, dt, flags);
      for (size_t i = n; i < n + 16; i++)
        if (out[i] != 0xAA) { printf("OOB "); break; }
      if (ERR_isError(r)) printf("ERR %s\n", ERR_getErrorName(r));
      else { printf("OK "); hex(out, r); printf("\n"); }
      free(in); free(out);
#endif
    } else if (p[0] == 'C' || p[0] == 'E') {
      unsigned maxsv = strtoul(p + 2, &p, 10);
      unsigned lg = strtoul(p + 1, &p, 10);
      size_t len = unhex(p + 1, inb);
      HUF_repeat rep = HUF_repeat_none;
      size_t r;
      if (line[0] == 'C')
        r = HUF_compress1X_repeat(outb, sizeof outb, inb, len, maxsv, lg,
                                  cwksp, sizeof cwksp, NULL, &rep, 0);
      else
        r = HUF_compress4X_repeat(outb, sizeof outb, inb, len, maxsv, lg,
                                  cwksp, sizeof cwksp, NULL, &rep, 0);
      if (ERR_isError(r)) printf("ERR %s\n", ERR_getErrorName(r));
      else if (r == 0 || r == 1) printf("NONE %zu\n", r);
      else { printf("OK "); hex(outb, r); printf("\n"); }
    } else if (p[0] == 'N') {
      size_t len = unhex(p + 2, inb);
      unsigned char *in = copy(inb, len);
      short nc[256]; unsigned maxsv = 255, tl = 0;
      size_t r = READNCOUNT(nc, &maxsv, &tl, in, len);
      free(in);
      if (ERR_isError(r)) printf("ERR %s\n", ERR_getErrorName(r));
      else {
        printf("OK %zu %u %u", r, maxsv, tl);
        for (unsigned i = 0; i <= maxsv; i++) printf(" %d", nc[i]);
        printf("\n");
      }
    } else if (p[0] == 'S') {
      size_t len = unhex(p + 2, inb);
      unsigned char *in = copy(inb, len);
      unsigned char w[256]; U32 rank[16], nb = 0, tl = 0;
      size_t r = READSTATS(w, 256, rank, &nb, &tl, in, len);
      free(in);
      if (ERR_isError(r)) printf("ERR %s\n", ERR_getErrorName(r));
      else {
        printf("OK %zu %u %u", r, nb, tl);
        for (unsigned i = 0; i < nb; i++) printf(" %u", w[i]);
        printf("\n");
      }
    } else if (p[0] == 'W') {
      size_t len = unhex(p + 2, inb);
      HUF_CElt ct[HUF_CTABLE_SIZE_ST(255)] = {0};
      unsigned lg = 0;
      for (size_t i = 0; i < len && i < 256; i++) {
        ct[1 + i] = inb[i];
        if (inb[i] > lg) lg = inb[i];
      }
      size_t r = len == 0 || len > 256 ? ERROR(GENERIC) :
        HUF_writeCTable_wksp(outb, 300, ct, (unsigned)(len - 1), lg, cwksp,
                             sizeof cwksp);
      if (ERR_isError(r)) printf("ERR %s\n", ERR_getErrorName(r));
      else { printf("OK "); hex(outb, r); printf("\n"); }
    } else if (p[0] == 'F') {
      static FSE_CTable ct[FSE_CTABLE_SIZE_U32(12, 255)];
      static U32 bw[FSE_BUILD_CTABLE_WORKSPACE_SIZE_U32(255, 12)];
      short nc[256] = {0};
      unsigned al = strtoul(p + 2, &p, 10);
      unsigned msv = strtoul(p + 1, &p, 10);
      for (unsigned i = 0; i <= msv && i < 256; i++)
        nc[i] = (short)strtol(p + 1, &p, 10);
      size_t len = unhex(p + 1, inb);
      size_t h = msv > 255 || al > 12 ? ERROR(GENERIC) :
        FSE_writeNCount(outb, 600, nc, msv, al);
      size_t r = ERR_isError(h) ? h :
        FSE_buildCTable_wksp(ct, nc, msv, al, bw, sizeof bw);
      size_t c = ERR_isError(r) ? r :
        FSE_compress_usingCTable(outb + h, 600, inb, len, ct);
      if (ERR_isError(c)) printf("ERR %s\n", ERR_getErrorName(c));
      else if (c == 0) printf("NONE\n");
      else { printf("OK "); hex(outb, h + c); printf("\n"); }
    } else continue;
    fflush(stdout);
  }
  return 0;
}

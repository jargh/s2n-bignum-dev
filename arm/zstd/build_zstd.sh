#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build zstd's Huffman and FSE decoding (lib/common/entropy_common.c,
# lib/common/fse_decompress.c, lib/decompress/huf_decompress.c and
# lib/common/error_private.c) as a shared library for AArch64, as described
# in README.md, with the exported test entry points of zhuf_api.c, and the
# test program zhuf_run from ../../tests/zstd/zhuf_run.c linked with it. The
# test program zhuf_run_direct is linked with the same object files of the
# decoding instead, for the functions that the library does not export. A
# record of the toolchain and the hashes is written to OUT/toolchain.txt.
#
# usage: GCC=<compiler> build_zstd.sh ZSTD OUT
#
# where ZSTD is a checkout of zstd and OUT a directory for the results.
# The compiler used for the transcription was gcc 12.3.0 from nixpkgs
# commit b134951a (legacyPackages.aarch64-linux.gcc12), run under qemu-user.
set -euo pipefail
GCC=${GCC:?set GCC to the AArch64 compiler}
HERE=$(dirname "$(realpath "$0")")
LIB=$(realpath "$1")/lib
OUT=$(realpath -m "$2")
# As zstd's lib/Makefile builds libzstd.so, but -O2 for -O3 and without the
# stack protector, which the nixpkgs compiler wrapper enables by default.
CFLAGS="-O2 -fPIC -fvisibility=hidden -fno-stack-protector -Wa,--noexecstack"
CPPFLAGS="-DXXH_NAMESPACE=ZSTD_ -DDEBUGLEVEL=0 -I$LIB -I$LIB/common"
SRCS="common/entropy_common.c common/fse_decompress.c
      decompress/huf_decompress.c common/error_private.c"
mkdir -p "$OUT/lib" "$OUT/run"
cd "$OUT"
for f in $SRCS; do
  "$GCC" $CFLAGS $CPPFLAGS -c "$LIB/$f" -o "lib/$(basename "$f" .c).o"
done
"$GCC" -O2 -fPIC $CPPFLAGS -c "$HERE/zhuf_api.c" -o lib/zhuf_api.o
"$GCC" -shared -Wl,-soname,libzstd_huf.so -o libzstd_huf.so lib/*.o
# The test program has its own copy of zstd's encoder (and of the functions
# that it uses), to make test inputs; its decoding uses libzstd_huf.so.
for f in compress/huf_compress.c compress/fse_compress.c compress/hist.c \
         common/entropy_common.c common/fse_decompress.c \
         common/error_private.c; do
  "$GCC" -O2 $CPPFLAGS -c "$LIB/$f" -o "run/$(basename "$f" .c).o"
done
"$GCC" -O2 -DZHUF_LIB $CPPFLAGS "$HERE/../../tests/zstd/zhuf_run.c" run/*.o \
  -L. -lzstd_huf -Wl,-rpath,'$ORIGIN' -o zhuf_run
"$GCC" -O2 $CPPFLAGS "$HERE/../../tests/zstd/zhuf_run.c" \
  lib/entropy_common.o lib/fse_decompress.o lib/huf_decompress.o \
  lib/error_private.o run/huf_compress.o run/fse_compress.o run/hist.o \
  -o zhuf_run_direct
{
  echo "source: zstd $(git -C "$LIB" log -1 --format=%H 2>/dev/null ||
                       echo unknown)"
  for f in $SRCS; do echo "$f sha256: $(sha256sum "$LIB/$f" | cut -d' ' -f1)"
  done
  "$GCC" --version | head -1
  echo "CFLAGS: $CFLAGS"
  echo "CPPFLAGS: -DXXH_NAMESPACE=ZSTD_ -DDEBUGLEVEL=0"
  echo "libzstd_huf.so sha256: $(sha256sum libzstd_huf.so | cut -d' ' -f1)"
} > toolchain.txt
cat toolchain.txt

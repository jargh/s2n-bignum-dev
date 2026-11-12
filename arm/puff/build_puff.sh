#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build zlib's contrib/puff/puff.c as a shared library for AArch64, as
# described in README.md, and the test program puff_run from
# ../../tests/deflate/puff_run.c linked with it. A record of the toolchain
# and the hashes is written to OUT/toolchain.txt.
#
# usage: GCC=<compiler> build_puff.sh ZLIB OUT
#
# where ZLIB is a checkout of zlib and OUT a directory for the results.
# The compiler used for puff_gcc12_O2.S was gcc 12.3.0 from nixpkgs commit
# b134951a (legacyPackages.aarch64-linux.gcc12), run under qemu-user.
set -euo pipefail
GCC=${GCC:?set GCC to the AArch64 compiler}
HERE=$(dirname "$(realpath "$0")")
SRC=$(realpath "$1")/contrib/puff
OUT=$(realpath -m "$2")
CFLAGS="-O2 -fPIC -fno-stack-protector"
mkdir -p "$OUT"
cd "$OUT"
cp "$SRC/puff.c" "$SRC/puff.h" .
"$GCC" $CFLAGS -c puff.c -o puff.o
"$GCC" -shared -Wl,-soname,libpuff.so -o libpuff.so puff.o
"$GCC" -O2 -I. "$HERE/../../tests/deflate/puff_run.c" -L. -lpuff \
  -Wl,-rpath,'$ORIGIN' -o puff_run
{
  echo "source: zlib $(git -C "$SRC" log -1 --format=%H) contrib/puff"
  echo "puff.c sha256: $(sha256sum puff.c | cut -d' ' -f1)"
  "$GCC" --version | head -1
  echo "CFLAGS: $CFLAGS"
  echo "libpuff.so sha256: $(sha256sum libpuff.so | cut -d' ' -f1)"
} > toolchain.txt
cat toolchain.txt

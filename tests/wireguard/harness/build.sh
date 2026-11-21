#!/bin/sh
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build the test harness for the WireGuard image in the build directory
# OUTDIR of arm/wireguard/build.sh: OUTDIR/test/wg_offsets.h and
# OUTDIR/test/wg_harness (an AArch64 executable; run it with
# qemu-aarch64 -L /usr/aarch64-linux-gnu on other hosts).
#
# Usage: build.sh OUTDIR

set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OUT=$(CDPATH= cd -- "$1" && pwd)
CROSS=${CROSS_COMPILE:-aarch64-linux-gnu-}
mkdir -p "$OUT/test"
sh "$HERE/../../../arm/wireguard/gen_offsets.sh" "$OUT" |
  awk '{ printf "#define WG_%s %s\n", $1, $2 }' > "$OUT/test/wg_offsets.h"
${CROSS}gcc -O1 -g -Wall -Wextra -Wno-unused-parameter -rdynamic \
  -I"$OUT/test" -o "$OUT/test/wg_harness" "$HERE/wg_harness.c" \
  "$OUT/test/curve25519-hacl64.o" "$OUT/test/siphash.o" -ldl

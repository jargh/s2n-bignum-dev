#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build the objects under test with the rules of arm/Makefile (which
# preprocess from stdin, check for x18 and assemble for the SHA3
# extension), or of x86/Makefile on x86_64, and collect them in WORK/obj,
# together with the randomized API in C (randomized.c). With CTFLAGS
# set, e.g. CTFLAGS=-DMLKEM_CT_TESTING, the per-level files are
# preprocessed with those flags too, the same way, and the objects go to
# WORK/obj_ct instead.
#
# usage: build.sh
set -e
. "$(dirname "$0")/env.sh"
O=$WORK/obj${CTFLAGS:+_ct}
OBJS=""
for n in $NATIVE2_OBJS; do OBJS="$OBJS mlkem_native2/$n.o"; done
for n in $LEAF_OBJS; do OBJS="$OBJS mlkem/mlkem_$n.o"; done
for n in $SHA3_OBJS; do OBJS="$OBJS sha3/$n.o"; done
make -s -C "$REPO/$ARCHDIR" $OBJS
rm -rf "$O"; mkdir -p "$O"
for o in $OBJS; do cp "$REPO/$ARCHDIR/$o" "$O/"; done
if [ -n "${CTFLAGS:-}" ]; then
  for L in 512 768 1024; do
    if [ -f "$REPO/$ARCHDIR/mlkem_native2/mlkem$L.S" ]; then
      (cd "$REPO/$ARCHDIR" &&
       asm_with mlkem_native2/mlkem$L.S "$CTFLAGS" "$O/mlkem$L.o")
    fi
  done
fi
$CC -O2 -Wall -Wextra $CF_CFLAGS -c "$T/randomized.c" \
  -o "$O/mlkem_native2_randomized.o"
echo "built $(ls "$O" | wc -l) objects in $O"

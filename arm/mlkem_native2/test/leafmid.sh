#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# The tests of the leaves and of the middle layer (test_leaf, test_mid)
# on the objects of a build: natively, under memcheck with fewer
# iterations (if there is a VALGRIND), and with BTI enforced. The
# randomized API is left out of the link.
#
# usage: leafmid.sh [OBJDIR]   (default WORK/obj)
# environment: LEAF_ITER (default 10000), MID_ITER (default 2000)
set -u
. "$(dirname "$0")/env.sh"
O=$(readlink -f "${1:-$WORK/obj}")
B=$WORK/build/leafmid; rm -rf "$B"; mkdir -p "$B"
OBJS=$(ls $O/*.o | grep -v randomized)
REF=$WORK/ref/out/libref.a
REFBTI=$WORK/ref/out_bti/libref.a
CCF="$CC -O2 -Wall -Wextra -I $REPO/arm/mlkem_native2"
st=0
$CCF -o $B/test_leaf $T/test_leaf.c $T/no_randombytes.c $OBJS $REF || exit 1
$CCF -o $B/test_mid $T/test_mid.c $OBJS $REF || exit 1
$CCF $BTI_FLAGS -o $B/test_leaf_bti $T/test_leaf.c $T/no_randombytes.c \
  $OBJS $REFBTI 2> $B/bti_link.log || exit 1
$CCF $BTI_FLAGS -o $B/test_mid_bti $T/test_mid.c $OBJS $REFBTI \
  2>> $B/bti_link.log || exit 1
echo "leafmid:"
$B/test_leaf ${LEAF_ITER:-10000} > $B/leaf.log 2>&1; result test_leaf $?
$B/test_mid ${MID_ITER:-2000} > $B/mid.log 2>&1; result test_mid $?
if [ -n "$VALGRIND" ]; then
  $VALGRIND -q --error-exitcode=1 $B/test_leaf 200 > $B/leaf_vg.log 2>&1
  result "test_leaf (memcheck)" $?
  $VALGRIND -q --error-exitcode=1 $B/test_mid 50 > $B/mid_vg.log 2>&1
  result "test_mid (memcheck)" $?
else
  result "memcheck (no VALGRIND)" skip
fi
r=0
$B/test_leaf_bti 100 > $B/leaf_bti.log 2>&1 || r=1
$B/test_mid_bti 20 > $B/mid_bti.log 2>&1 || r=1
result "BTI enforced (test_leaf, test_mid)" $r
[ $st = 0 ] && echo "leafmid: OK" || echo "leafmid: FAIL (logs in $B)"
exit $st

#!/bin/sh
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Print the offsets and sizes of wg_offsets.c as "NAME VALUE" lines, by
# compiling it with Kbuild's saved command for noise.o in the build
# directory OUTDIR of build.sh.
#
# Usage: gen_offsets.sh OUTDIR

set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OBJ=$(CDPATH= cd -- "$1/obj" && pwd)
SRC=$(ls -d "$1"/linux-*)
CMD=$(sed -n 's/^savedcmd_drivers\/net\/wireguard\/noise\.o := //p' \
        "$OBJ/drivers/net/wireguard/.noise.o.cmd")
CMD=$(echo "$CMD" | sed -e 's/ -Wp,-MMD,[^ ]*//' \
  -e "s# -c -o drivers/net/wireguard/noise\.o [^ ]*noise\.c# -S -o - $HERE/wg_offsets.c#" \
  -e 's/KBUILD_BASENAME=[^ ]*/KBUILD_BASENAME="\\"wg_offsets\\""/')
cd "$OBJ"
eval "$CMD -I$SRC/drivers/net/wireguard" | sed -n 's/^->\([a-z0-9_]*\) #\{0,1\}\([0-9]*\).*/\1 \2/p'

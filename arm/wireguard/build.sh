#!/bin/sh
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build the AArch64 image of the WireGuard handshake from a Linux release.
#
# Usage: build.sh TARBALL OUTDIR
#
#   TARBALL  linux-6.18.64.tar.xz from cdn.kernel.org (checked by SHA-256)
#   OUTDIR   build directory; gets linux-6.18.64/ (the sources), obj/ (the
#            kernel build), objs/ (the objects linked) and wireguard.so
#
# The objects are compiled by the kernel's own build system with an arm64
# defconfig plus WireGuard, minus the features that the AArch64 model does
# not cover (stack protector, pointer authentication and BTI in the kernel),
# and with the portable C versions of the crypto library (see
# wg_generic_crypto.h). The environment variable CROSS_COMPILE gives the
# toolchain prefix (default aarch64-linux-gnu-).

set -eu

VERSION=6.18.64
SHA256=020d45510c539972e6f14c5c71566878d3b7ef56fb082b3e09134f2ebaade562

TARBALL=$1
OUT=$2
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
CROSS=${CROSS_COMPILE:-aarch64-linux-gnu-}

echo "$SHA256  $TARBALL" | sha256sum -c -
mkdir -p "$OUT"
OUT=$(CDPATH= cd -- "$OUT" && pwd)
SRC=$OUT/linux-$VERSION
OBJ=$OUT/obj
[ -d "$SRC" ] || tar -C "$OUT" -xf "$TARBALL"

KMAKE="make -s -C $SRC O=$OBJ ARCH=arm64 CROSS_COMPILE=$CROSS"

$KMAKE defconfig
"$SRC/scripts/config" --file "$OBJ/.config" \
  -e NET -e INET -e WIREGUARD \
  -d STACKPROTECTOR -d STACKPROTECTOR_STRONG \
  -d ARM64_PTR_AUTH_KERNEL -d ARM64_BTI_KERNEL \
  -d FUNCTION_TRACER
$KMAKE olddefconfig
$KMAKE -j8 prepare

# The objects of the image: the handshake, cookies and the index and
# public-key tables of WireGuard, and the parts of the crypto library
# that they use.

WG="noise cookie peerlookup"
LIB="blake2s chacha chacha-block-generic chacha20poly1305 poly1305
     poly1305-donna64 curve25519 memneq utils"
TARGETS=""
for f in $WG; do TARGETS="$TARGETS drivers/net/wireguard/$f.o"; done
for f in $LIB; do TARGETS="$TARGETS lib/crypto/$f.o"; done

(cd "$OBJ" && rm -f $TARGETS)
$KMAKE -j8 KCFLAGS="-include $HERE/wg_generic_crypto.h" $TARGETS

# Link them, with the kernel data of wg_env.S, into a shared object at
# address 0, so that calls of kernel functions go through the PLT. The
# sections that only hold metadata for the kernel are dropped (see
# wireguard.lds).

mkdir -p "$OUT/objs"
for t in $TARGETS; do cp "$OBJ/$t" "$OUT/objs/"; done
${CROSS}gcc -c -o "$OUT/objs/wg_env.o" "$HERE/wg_env.S"

(cd "$OUT/objs" &&
 ${CROSS}ld -shared -Bsymbolic --build-id=none \
   -z max-page-size=4096 -z common-page-size=4096 -z noexecstack \
   -soname wireguard.so -T "$HERE/wireguard.lds" -o ../wireguard.so \
   noise.o cookie.o peerlookup.o blake2s.o chacha.o \
   chacha-block-generic.o chacha20poly1305.o poly1305.o \
   poly1305-donna64.o curve25519.o memneq.o utils.o wg_env.o)

# For the tests only: kernel code that the image calls but does not
# contain, the implementation of curve25519_generic (HACL*), which the
# proofs treat as a contract, and SipHash, which the public-key table uses.

$KMAKE -j8 KCFLAGS="-include $HERE/wg_generic_crypto.h" \
  lib/crypto/curve25519-hacl64.o lib/siphash.o
mkdir -p "$OUT/test"
cp "$OBJ/lib/crypto/curve25519-hacl64.o" "$OBJ/lib/siphash.o" "$OUT/test/"

sha256sum "$OUT/wireguard.so"

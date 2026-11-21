/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/* Use the portable C code of the crypto library: drop the arch glue
   that 6.18's lib/crypto/Kconfig forces on for arm64. Passed as
   KCFLAGS=-include so it comes after kconfig.h/autoconf.h. */
#undef CONFIG_CRYPTO_LIB_CHACHA_ARCH
#undef CONFIG_CRYPTO_LIB_POLY1305_ARCH
#undef CONFIG_CRYPTO_LIB_BLAKE2S_ARCH
#undef CONFIG_CRYPTO_LIB_CURVE25519_ARCH

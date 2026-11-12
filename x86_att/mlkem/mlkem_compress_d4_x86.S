// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 4 bits and pack them
// Inputs a[256] (signed 16-bit words), data[32] (bytes);
// output r[128] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^4 / 3329) mod 2^4 (Compress_4 of FIPS
// 203, section 4.2.1), and the 256 results are packed 4 bits each in
// order, least significant first (ByteEncode_4), as in mlkem-native's
// mlk_poly_compress_d4. The table data is mlkem-native's
// mlk_compress_d4_data (as in the mlkem_native2 constants block), and
// a and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_compress_d4_avx2_asm, unchanged.
//
// extern void mlkem_compress_d4_x86(uint8_t r[S2N_BIGNUM_STATIC 128],
//                                   const int16_t a[S2N_BIGNUM_STATIC 256],
//                                   const uint8_t data[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d4_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d4_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d4_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_compress_d4_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(64)
        CFI_STACKSAVEU(%xmm6,0)
        CFI_STACKSAVEU(%xmm7,16)
        CFI_STACKSAVEU(%xmm8,32)
        CFI_STACKSAVE(%rdi,48)
        CFI_STACKSAVE(%rsi,56)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

        movl    $0x4ebf4ebf, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movl    $0x2000200, %eax
        vmovd   %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1
        movl    $0xf000f, %eax
        vmovd   %eax, %xmm2
        vpbroadcastd %xmm2, %ymm2
        movl    $0x10011001, %eax
        vmovd   %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3
        vmovdqa (%rdx), %ymm4
        vmovdqa (%rsi), %ymm5
        vmovdqa 0x20(%rsi), %ymm6
        vmovdqa 0x40(%rsi), %ymm7
        vmovdqa 0x60(%rsi), %ymm8
        vpmulhw %ymm0, %ymm5, %ymm5
        vpmulhw %ymm0, %ymm6, %ymm6
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm5, %ymm5
        vpmulhrsw %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm5, %ymm5
        vpand   %ymm2, %ymm6, %ymm6
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm6, %ymm5, %ymm5
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm5, %ymm5
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpackuswb %ymm7, %ymm5, %ymm5
        vpermd  %ymm5, %ymm4, %ymm5
        vmovdqu %ymm5, (%rdi)
        vmovdqa 0x80(%rsi), %ymm5
        vmovdqa 0xa0(%rsi), %ymm6
        vmovdqa 0xc0(%rsi), %ymm7
        vmovdqa 0xe0(%rsi), %ymm8
        vpmulhw %ymm0, %ymm5, %ymm5
        vpmulhw %ymm0, %ymm6, %ymm6
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm5, %ymm5
        vpmulhrsw %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm5, %ymm5
        vpand   %ymm2, %ymm6, %ymm6
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm6, %ymm5, %ymm5
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm5, %ymm5
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpackuswb %ymm7, %ymm5, %ymm5
        vpermd  %ymm5, %ymm4, %ymm5
        vmovdqu %ymm5, 0x20(%rdi)
        vmovdqa 0x100(%rsi), %ymm5
        vmovdqa 0x120(%rsi), %ymm6
        vmovdqa 0x140(%rsi), %ymm7
        vmovdqa 0x160(%rsi), %ymm8
        vpmulhw %ymm0, %ymm5, %ymm5
        vpmulhw %ymm0, %ymm6, %ymm6
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm5, %ymm5
        vpmulhrsw %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm5, %ymm5
        vpand   %ymm2, %ymm6, %ymm6
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm6, %ymm5, %ymm5
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm5, %ymm5
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpackuswb %ymm7, %ymm5, %ymm5
        vpermd  %ymm5, %ymm4, %ymm5
        vmovdqu %ymm5, 0x40(%rdi)
        vmovdqa 0x180(%rsi), %ymm5
        vmovdqa 0x1a0(%rsi), %ymm6
        vmovdqa 0x1c0(%rsi), %ymm7
        vmovdqa 0x1e0(%rsi), %ymm8
        vpmulhw %ymm0, %ymm5, %ymm5
        vpmulhw %ymm0, %ymm6, %ymm6
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm5, %ymm5
        vpmulhrsw %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm5, %ymm5
        vpand   %ymm2, %ymm6, %ymm6
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm6, %ymm5, %ymm5
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm5, %ymm5
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpackuswb %ymm7, %ymm5, %ymm5
        vpermd  %ymm5, %ymm4, %ymm5
        vmovdqu %ymm5, 0x60(%rdi)
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOADU(%xmm8,32)
        CFI_STACKLOAD(%rdi,48)
        CFI_STACKLOAD(%rsi,56)
        CFI_INC_RSP(64)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d4_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

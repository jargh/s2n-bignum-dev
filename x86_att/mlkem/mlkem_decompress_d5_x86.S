// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpack 5-bit ML-KEM compressed coefficients and decompress them
// Inputs a[160], data[96] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 5-bit fields u[i], least significant first
// (ByteDecode_5), and each is mapped to round(u[i] * 3329 / 2^5),
// rounding halves up (Decompress_5 of FIPS 203, section 4.2.1), which
// is in the range 0 <= r[i] < 3329. This is mlkem-native's
// mlk_poly_decompress_d5. The table data is mlkem-native's
// mlk_decompress_d5_data (as in the mlkem_native2 constants block),
// and r and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_decompress_d5_avx2_asm, unchanged.
//
// extern void mlkem_decompress_d5_x86(int16_t r[S2N_BIGNUM_STATIC 256],
//     const uint8_t a[S2N_BIGNUM_STATIC 160],
//     const uint8_t data[S2N_BIGNUM_STATIC 96]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d5_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d5_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d5_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_decompress_d5_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(%rdi,0)
        CFI_STACKSAVE(%rsi,8)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

        movl    $0xd010d01, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        vmovdqa (%rdx), %ymm1
        vmovdqa 0x20(%rdx), %ymm2
        vmovdqa 0x40(%rdx), %ymm3
        vmovq    (%rsi), %xmm4
        vpinsrw $0x4,  0x8(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, (%rdi)
        vmovq    0xa(%rsi), %xmm4
        vpinsrw $0x4,  0x12(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x20(%rdi)
        vmovq    0x14(%rsi), %xmm4
        vpinsrw $0x4,  0x1c(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x40(%rdi)
        vmovq    0x1e(%rsi), %xmm4
        vpinsrw $0x4,  0x26(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x60(%rdi)
        vmovq    0x28(%rsi), %xmm4
        vpinsrw $0x4,  0x30(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x80(%rdi)
        vmovq    0x32(%rsi), %xmm4
        vpinsrw $0x4,  0x3a(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0xa0(%rdi)
        vmovq    0x3c(%rsi), %xmm4
        vpinsrw $0x4,  0x44(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0xc0(%rdi)
        vmovq    0x46(%rsi), %xmm4
        vpinsrw $0x4,  0x4e(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0xe0(%rdi)
        vmovq    0x50(%rsi), %xmm4
        vpinsrw $0x4,  0x58(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x100(%rdi)
        vmovq    0x5a(%rsi), %xmm4
        vpinsrw $0x4,  0x62(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x120(%rdi)
        vmovq    0x64(%rsi), %xmm4
        vpinsrw $0x4,  0x6c(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x140(%rdi)
        vmovq    0x6e(%rsi), %xmm4
        vpinsrw $0x4,  0x76(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x160(%rdi)
        vmovq    0x78(%rsi), %xmm4
        vpinsrw $0x4,  0x80(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x180(%rdi)
        vmovq    0x82(%rsi), %xmm4
        vpinsrw $0x4,  0x8a(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x1a0(%rdi)
        vmovq    0x8c(%rsi), %xmm4
        vpinsrw $0x4,  0x94(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x1c0(%rdi)
        vmovq    0x96(%rsi), %xmm4
        vpinsrw $0x4,  0x9e(%rsi), %xmm4, %xmm4
        vinserti128 $0x1, %xmm4, %ymm4, %ymm4
        vpshufb %ymm1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmullw %ymm3, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x1e0(%rdi)
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(%rdi,0)
        CFI_STACKLOAD(%rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d5_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

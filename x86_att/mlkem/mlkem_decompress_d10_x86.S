// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpack 10-bit ML-KEM compressed coefficients and decompress them
// Inputs a[320], data[32] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 10-bit fields u[i], least significant first
// (ByteDecode_10), and each is mapped to round(u[i] * 3329 / 2^10),
// rounding halves up (Decompress_10 of FIPS 203, section 4.2.1), which
// is in the range 0 <= r[i] < 3329. This is mlkem-native's
// mlk_poly_decompress_d10. The table data is mlkem-native's
// mlk_decompress_d10_data (as in the mlkem_native2 constants block),
// and r and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_decompress_d10_avx2_asm, unchanged.
//
// extern void mlkem_decompress_d10_x86(int16_t r[S2N_BIGNUM_STATIC 256],
//     const uint8_t a[S2N_BIGNUM_STATIC 320],
//     const uint8_t data[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d10_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d10_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d10_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_decompress_d10_x86):
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

        movl    $0xd013404, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movl    $0x4, %eax
        vmovq   %rax, %xmm1
        vpbroadcastq %xmm1, %ymm1
        movl    $0x7fe01ff8, %eax
        vmovd   %eax, %xmm2
        vpbroadcastd %xmm2, %ymm2
        vmovdqa (%rdx), %ymm3
        vmovdqu (%rsi), %xmm4
        vmovd    0x10(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, (%rdi)
        vmovdqu 0x14(%rsi), %xmm4
        vmovd    0x24(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x20(%rdi)
        vmovdqu 0x28(%rsi), %xmm4
        vmovd    0x38(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x40(%rdi)
        vmovdqu 0x3c(%rsi), %xmm4
        vmovd    0x4c(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x60(%rdi)
        vmovdqu 0x50(%rsi), %xmm4
        vmovd    0x60(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x80(%rdi)
        vmovdqu 0x64(%rsi), %xmm4
        vmovd    0x74(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0xa0(%rdi)
        vmovdqu 0x78(%rsi), %xmm4
        vmovd    0x88(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0xc0(%rdi)
        vmovdqu 0x8c(%rsi), %xmm4
        vmovd    0x9c(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0xe0(%rdi)
        vmovdqu 0xa0(%rsi), %xmm4
        vmovd    0xb0(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x100(%rdi)
        vmovdqu 0xb4(%rsi), %xmm4
        vmovd    0xc4(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x120(%rdi)
        vmovdqu 0xc8(%rsi), %xmm4
        vmovd    0xd8(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x140(%rdi)
        vmovdqu 0xdc(%rsi), %xmm4
        vmovd    0xec(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x160(%rdi)
        vmovdqu 0xf0(%rsi), %xmm4
        vmovd    0x100(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x180(%rdi)
        vmovdqu 0x104(%rsi), %xmm4
        vmovd    0x114(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x1a0(%rdi)
        vmovdqu 0x118(%rsi), %xmm4
        vmovd    0x128(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x1c0(%rdi)
        vmovdqu 0x12c(%rsi), %xmm4
        vmovd    0x13c(%rsi), %xmm5
        vinserti128 $0x1, %xmm5, %ymm4, %ymm4
        vpermq  $0x94, %ymm4, %ymm4
        vpshufb %ymm3, %ymm4, %ymm4
        vpsllvd %ymm1, %ymm4, %ymm4
        vpsrlw  $0x1, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpmulhrsw %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 0x1e0(%rdi)
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(%rdi,0)
        CFI_STACKLOAD(%rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d10_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Unpack 11-bit ML-KEM compressed coefficients and decompress them
// Inputs a[352], data[128] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 11-bit fields u[i], least significant first
// (ByteDecode_11), and each is mapped to round(u[i] * 3329 / 2^11),
// rounding halves up (Decompress_11 of FIPS 203, section 4.2.1), which
// is in the range 0 <= r[i] < 3329. This is mlkem-native's
// mlk_poly_decompress_d11. The table data is mlkem-native's
// mlk_decompress_d11_data (as in the mlkem_native2 constants block),
// and r and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_decompress_d11_avx2_asm, unchanged.
//
// extern void mlkem_decompress_d11_x86(int16_t r[S2N_BIGNUM_STATIC 256],
//     const uint8_t a[S2N_BIGNUM_STATIC 352],
//     const uint8_t data[S2N_BIGNUM_STATIC 128]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d11_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d11_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d11_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_decompress_d11_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(48)
        CFI_STACKSAVEU(%xmm6,0)
        CFI_STACKSAVEU(%xmm7,16)
        CFI_STACKSAVE(%rdi,32)
        CFI_STACKSAVE(%rsi,40)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

        movl    $0xd010d01, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movl    $0x7ff07ff0, %eax
        vmovd   %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1
        vmovdqa (%rdx), %ymm2
        vmovdqa 0x20(%rdx), %ymm3
        vmovdqa 0x40(%rdx), %ymm4
        vmovdqa 0x60(%rdx), %ymm5
        vmovdqu (%rsi), %xmm6
        vmovd    0x10(%rsi), %xmm7
        vpinsrw $0x2,  0x14(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, (%rdi)
        vmovdqu 0x16(%rsi), %xmm6
        vmovd    0x26(%rsi), %xmm7
        vpinsrw $0x2,  0x2a(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x20(%rdi)
        vmovdqu 0x2c(%rsi), %xmm6
        vmovd    0x3c(%rsi), %xmm7
        vpinsrw $0x2,  0x40(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x40(%rdi)
        vmovdqu 0x42(%rsi), %xmm6
        vmovd    0x52(%rsi), %xmm7
        vpinsrw $0x2,  0x56(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x60(%rdi)
        vmovdqu 0x58(%rsi), %xmm6
        vmovd    0x68(%rsi), %xmm7
        vpinsrw $0x2,  0x6c(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x80(%rdi)
        vmovdqu 0x6e(%rsi), %xmm6
        vmovd    0x7e(%rsi), %xmm7
        vpinsrw $0x2,  0x82(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0xa0(%rdi)
        vmovdqu 0x84(%rsi), %xmm6
        vmovd    0x94(%rsi), %xmm7
        vpinsrw $0x2,  0x98(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0xc0(%rdi)
        vmovdqu 0x9a(%rsi), %xmm6
        vmovd    0xaa(%rsi), %xmm7
        vpinsrw $0x2,  0xae(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0xe0(%rdi)
        vmovdqu 0xb0(%rsi), %xmm6
        vmovd    0xc0(%rsi), %xmm7
        vpinsrw $0x2,  0xc4(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x100(%rdi)
        vmovdqu 0xc6(%rsi), %xmm6
        vmovd    0xd6(%rsi), %xmm7
        vpinsrw $0x2,  0xda(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x120(%rdi)
        vmovdqu 0xdc(%rsi), %xmm6
        vmovd    0xec(%rsi), %xmm7
        vpinsrw $0x2,  0xf0(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x140(%rdi)
        vmovdqu 0xf2(%rsi), %xmm6
        vmovd    0x102(%rsi), %xmm7
        vpinsrw $0x2,  0x106(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x160(%rdi)
        vmovdqu 0x108(%rsi), %xmm6
        vmovd    0x118(%rsi), %xmm7
        vpinsrw $0x2,  0x11c(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x180(%rdi)
        vmovdqu 0x11e(%rsi), %xmm6
        vmovd    0x12e(%rsi), %xmm7
        vpinsrw $0x2,  0x132(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x1a0(%rdi)
        vmovdqu 0x134(%rsi), %xmm6
        vmovd    0x144(%rsi), %xmm7
        vpinsrw $0x2,  0x148(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x1c0(%rdi)
        vmovdqu 0x14a(%rsi), %xmm6
        vmovd    0x15a(%rsi), %xmm7
        vpinsrw $0x2,  0x15e(%rsi), %xmm7, %xmm7
        vinserti128 $0x1, %xmm7, %ymm6, %ymm6
        vpermq  $0x94, %ymm6, %ymm6
        vpshufb %ymm2, %ymm6, %ymm6
        vpsrlvd %ymm3, %ymm6, %ymm6
        vpsrlvq %ymm4, %ymm6, %ymm6
        vpmullw %ymm5, %ymm6, %ymm6
        vpsrlw  $0x1, %ymm6, %ymm6
        vpand   %ymm1, %ymm6, %ymm6
        vpmulhrsw %ymm0, %ymm6, %ymm6
        vmovdqu %ymm6, 0x1e0(%rdi)
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOAD(%rdi,32)
        CFI_STACKLOAD(%rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d11_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

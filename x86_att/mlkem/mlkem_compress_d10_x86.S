// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 10 bits and pack them
// Inputs a[256] (signed 16-bit words), data[32] (bytes);
// output r[320] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^10 / 3329) mod 2^10 (Compress_10 of FIPS
// 203, section 4.2.1), and the 256 results are packed 10 bits each in
// order, least significant first (ByteEncode_10), as in mlkem-native's
// mlk_poly_compress_d10. The table data is mlkem-native's
// mlk_compress_d10_data (as in the mlkem_native2 constants block), and
// a and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_compress_d10_avx2_asm, unchanged.
//
// extern void mlkem_compress_d10_x86(uint8_t r[S2N_BIGNUM_STATIC 320],
//     const int16_t a[S2N_BIGNUM_STATIC 256],
//     const uint8_t data[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d10_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d10_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d10_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_compress_d10_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(%xmm6,0)
        CFI_STACKSAVEU(%xmm7,16)
        CFI_STACKSAVEU(%xmm8,32)
        CFI_STACKSAVEU(%xmm9,48)
        CFI_STACKSAVEU(%xmm10,64)
        CFI_STACKSAVE(%rdi,80)
        CFI_STACKSAVE(%rsi,88)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

        movl    $0x4ebf4ebf, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        vpsllw  $0x3, %ymm0, %ymm1
        movl    $0xf000f, %eax
        vmovd   %eax, %xmm2
        vpbroadcastd %xmm2, %ymm2
        movl    $0x10001000, %eax
        vmovd   %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3
        movl    $0x3ff03ff, %eax
        vmovd   %eax, %xmm4
        vpbroadcastd %xmm4, %ymm4
        movabsq $0x400000104000001, %rax
        vmovq   %rax, %xmm5
        vpbroadcastq %xmm5, %ymm5
        movl    $0xc, %eax
        vmovq   %rax, %xmm6
        vpbroadcastq %xmm6, %ymm6
        vmovdqa (%rdx), %ymm7
        vmovdqa (%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, (%rdi)
        vmovd   %xmm9,  0x10(%rdi)
        vmovdqa 0x20(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x14(%rdi)
        vmovd   %xmm9,  0x24(%rdi)
        vmovdqa 0x40(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x28(%rdi)
        vmovd   %xmm9,  0x38(%rdi)
        vmovdqa 0x60(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x3c(%rdi)
        vmovd   %xmm9,  0x4c(%rdi)
        vmovdqa 0x80(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x50(%rdi)
        vmovd   %xmm9,  0x60(%rdi)
        vmovdqa 0xa0(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x64(%rdi)
        vmovd   %xmm9,  0x74(%rdi)
        vmovdqa 0xc0(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x78(%rdi)
        vmovd   %xmm9,  0x88(%rdi)
        vmovdqa 0xe0(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x8c(%rdi)
        vmovd   %xmm9,  0x9c(%rdi)
        vmovdqa 0x100(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0xa0(%rdi)
        vmovd   %xmm9,  0xb0(%rdi)
        vmovdqa 0x120(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0xb4(%rdi)
        vmovd   %xmm9,  0xc4(%rdi)
        vmovdqa 0x140(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0xc8(%rdi)
        vmovd   %xmm9,  0xd8(%rdi)
        vmovdqa 0x160(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0xdc(%rdi)
        vmovd   %xmm9,  0xec(%rdi)
        vmovdqa 0x180(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0xf0(%rdi)
        vmovd   %xmm9,  0x100(%rdi)
        vmovdqa 0x1a0(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x104(%rdi)
        vmovd   %xmm9,  0x114(%rdi)
        vmovdqa 0x1c0(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x118(%rdi)
        vmovd   %xmm9,  0x128(%rdi)
        vmovdqa 0x1e0(%rsi), %ymm8
        vpmullw %ymm1, %ymm8, %ymm9
        vpaddw  %ymm2, %ymm8, %ymm10
        vpsllw  $0x3, %ymm8, %ymm8
        vpmulhw %ymm0, %ymm8, %ymm8
        vpsubw  %ymm10, %ymm9, %ymm10
        vpandn  %ymm10, %ymm9, %ymm9
        vpsrlw  $0xf, %ymm9, %ymm9
        vpsubw  %ymm9, %ymm8, %ymm8
        vpmulhrsw %ymm3, %ymm8, %ymm8
        vpand   %ymm4, %ymm8, %ymm8
        vpmaddwd %ymm5, %ymm8, %ymm8
        vpsllvd %ymm6, %ymm8, %ymm8
        vpsrlq  $0xc, %ymm8, %ymm8
        vpshufb %ymm7, %ymm8, %ymm8
        vextracti128 $0x1, %ymm8, %xmm9
        vpblendw $0xe0, %xmm9, %xmm8, %xmm8
        vmovdqu %xmm8, 0x12c(%rdi)
        vmovd   %xmm9,  0x13c(%rdi)
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOADU(%xmm8,32)
        CFI_STACKLOADU(%xmm9,48)
        CFI_STACKLOADU(%xmm10,64)
        CFI_STACKLOAD(%rdi,80)
        CFI_STACKLOAD(%rsi,88)
        CFI_INC_RSP(96)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d10_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

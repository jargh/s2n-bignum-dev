// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 5 bits and pack them
// Inputs a[256] (signed 16-bit words), data[32] (bytes);
// output r[160] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^5 / 3329) mod 2^5 (Compress_5 of FIPS
// 203, section 4.2.1), and the 256 results are packed 5 bits each in
// order, least significant first (ByteEncode_5), as in mlkem-native's
// mlk_poly_compress_d5. The table data is mlkem-native's
// mlk_compress_d5_data (as in the mlkem_native2 constants block), and
// a and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_compress_d5_avx2_asm, unchanged.
//
// extern void mlkem_compress_d5_x86(uint8_t r[S2N_BIGNUM_STATIC 160],
//                                   const int16_t a[S2N_BIGNUM_STATIC 256],
//                                   const uint8_t data[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d5_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d5_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d5_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_compress_d5_x86):
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
        movl    $0x4000400, %eax
        vmovd   %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1
        movl    $0x1f001f, %eax
        vmovd   %eax, %xmm2
        vpbroadcastd %xmm2, %ymm2
        movl    $0x20012001, %eax
        vmovd   %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3
        movl    $0x4000001, %eax
        vmovd   %eax, %xmm4
        vpbroadcastd %xmm4, %ymm4
        movl    $0xc, %eax
        vmovq   %rax, %xmm5
        vpbroadcastq %xmm5, %ymm5
        vmovdqa (%rdx), %ymm6
        vmovdqa (%rsi), %ymm7
        vmovdqa 0x20(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, (%rdi)
        vmovd   %xmm8,  0x10(%rdi)
        vmovdqa 0x40(%rsi), %ymm7
        vmovdqa 0x60(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, 0x14(%rdi)
        vmovd   %xmm8,  0x24(%rdi)
        vmovdqa 0x80(%rsi), %ymm7
        vmovdqa 0xa0(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, 0x28(%rdi)
        vmovd   %xmm8,  0x38(%rdi)
        vmovdqa 0xc0(%rsi), %ymm7
        vmovdqa 0xe0(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, 0x3c(%rdi)
        vmovd   %xmm8,  0x4c(%rdi)
        vmovdqa 0x100(%rsi), %ymm7
        vmovdqa 0x120(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, 0x50(%rdi)
        vmovd   %xmm8,  0x60(%rdi)
        vmovdqa 0x140(%rsi), %ymm7
        vmovdqa 0x160(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, 0x64(%rdi)
        vmovd   %xmm8,  0x74(%rdi)
        vmovdqa 0x180(%rsi), %ymm7
        vmovdqa 0x1a0(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, 0x78(%rdi)
        vmovd   %xmm8,  0x88(%rdi)
        vmovdqa 0x1c0(%rsi), %ymm7
        vmovdqa 0x1e0(%rsi), %ymm8
        vpmulhw %ymm0, %ymm7, %ymm7
        vpmulhw %ymm0, %ymm8, %ymm8
        vpmulhrsw %ymm1, %ymm7, %ymm7
        vpmulhrsw %ymm1, %ymm8, %ymm8
        vpand   %ymm2, %ymm7, %ymm7
        vpand   %ymm2, %ymm8, %ymm8
        vpackuswb %ymm8, %ymm7, %ymm7
        vpmaddubsw %ymm3, %ymm7, %ymm7
        vpmaddwd %ymm4, %ymm7, %ymm7
        vpsllvd %ymm5, %ymm7, %ymm7
        vpsrlvq %ymm5, %ymm7, %ymm7
        vpshufb %ymm6, %ymm7, %ymm7
        vextracti128 $0x1, %ymm7, %xmm8
        vpblendvb %xmm6, %xmm8, %xmm7, %xmm7
        vmovdqu %xmm7, 0x8c(%rdi)
        vmovd   %xmm8,  0x9c(%rdi)
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

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d5_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 11 bits and pack them
// Inputs a[256] (signed 16-bit words), data[64] (bytes);
// output r[352] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^11 / 3329) mod 2^11 (Compress_11 of FIPS
// 203, section 4.2.1), and the 256 results are packed 11 bits each in
// order, least significant first (ByteEncode_11), as in mlkem-native's
// mlk_poly_compress_d11. The table data is mlkem-native's
// mlk_compress_d11_data (as in the mlkem_native2 constants block), and
// a and data must be 32-byte aligned. This is mlkem-native's
// mlk_poly_compress_d11_avx2_asm, unchanged.
//
// extern void mlkem_compress_d11_x86(uint8_t r[S2N_BIGNUM_STATIC 352],
//     const int16_t a[S2N_BIGNUM_STATIC 256],
//     const uint8_t data[S2N_BIGNUM_STATIC 64]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = data
// Microsoft x64 ABI:   RCX = r, RDX = a, R8 = data
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d11_x86)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d11_x86)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d11_x86)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_compress_d11_x86):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(112)
        CFI_STACKSAVEU(%xmm6,0)
        CFI_STACKSAVEU(%xmm7,16)
        CFI_STACKSAVEU(%xmm8,32)
        CFI_STACKSAVEU(%xmm9,48)
        CFI_STACKSAVEU(%xmm10,64)
        CFI_STACKSAVEU(%xmm11,80)
        CFI_STACKSAVE(%rdi,96)
        CFI_STACKSAVE(%rsi,104)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

        movl    $0x4ebf4ebf, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        vpsllw  $0x3, %ymm0, %ymm1
        movl    $0x240024, %eax
        vmovd   %eax, %xmm2
        vpbroadcastd %xmm2, %ymm2
        movl    $0x20002000, %eax
        vmovd   %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3
        movl    $0x7ff07ff, %eax
        vmovd   %eax, %xmm4
        vpbroadcastd %xmm4, %ymm4
        movabsq $0x800000108000001, %rax
        vmovq   %rax, %xmm5
        vpbroadcastq %xmm5, %ymm5
        movl    $0xa, %eax
        vmovq   %rax, %xmm6
        vpbroadcastq %xmm6, %ymm6
        vmovdqa (%rdx), %ymm7
        vmovdqa 0x20(%rdx), %ymm8
        vmovdqa (%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, (%rdi)
        vmovd   %xmm10,  0x10(%rdi)
        vpextrw $0x2, %xmm10,  0x14(%rdi)
        vmovdqa 0x20(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x16(%rdi)
        vmovd   %xmm10,  0x26(%rdi)
        vpextrw $0x2, %xmm10,  0x2a(%rdi)
        vmovdqa 0x40(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x2c(%rdi)
        vmovd   %xmm10,  0x3c(%rdi)
        vpextrw $0x2, %xmm10,  0x40(%rdi)
        vmovdqa 0x60(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x42(%rdi)
        vmovd   %xmm10,  0x52(%rdi)
        vpextrw $0x2, %xmm10,  0x56(%rdi)
        vmovdqa 0x80(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x58(%rdi)
        vmovd   %xmm10,  0x68(%rdi)
        vpextrw $0x2, %xmm10,  0x6c(%rdi)
        vmovdqa 0xa0(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x6e(%rdi)
        vmovd   %xmm10,  0x7e(%rdi)
        vpextrw $0x2, %xmm10,  0x82(%rdi)
        vmovdqa 0xc0(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x84(%rdi)
        vmovd   %xmm10,  0x94(%rdi)
        vpextrw $0x2, %xmm10,  0x98(%rdi)
        vmovdqa 0xe0(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x9a(%rdi)
        vmovd   %xmm10,  0xaa(%rdi)
        vpextrw $0x2, %xmm10,  0xae(%rdi)
        vmovdqa 0x100(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0xb0(%rdi)
        vmovd   %xmm10,  0xc0(%rdi)
        vpextrw $0x2, %xmm10,  0xc4(%rdi)
        vmovdqa 0x120(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0xc6(%rdi)
        vmovd   %xmm10,  0xd6(%rdi)
        vpextrw $0x2, %xmm10,  0xda(%rdi)
        vmovdqa 0x140(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0xdc(%rdi)
        vmovd   %xmm10,  0xec(%rdi)
        vpextrw $0x2, %xmm10,  0xf0(%rdi)
        vmovdqa 0x160(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0xf2(%rdi)
        vmovd   %xmm10,  0x102(%rdi)
        vpextrw $0x2, %xmm10,  0x106(%rdi)
        vmovdqa 0x180(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x108(%rdi)
        vmovd   %xmm10,  0x118(%rdi)
        vpextrw $0x2, %xmm10,  0x11c(%rdi)
        vmovdqa 0x1a0(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x11e(%rdi)
        vmovd   %xmm10,  0x12e(%rdi)
        vpextrw $0x2, %xmm10,  0x132(%rdi)
        vmovdqa 0x1c0(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x134(%rdi)
        vmovd   %xmm10,  0x144(%rdi)
        vpextrw $0x2, %xmm10,  0x148(%rdi)
        vmovdqa 0x1e0(%rsi), %ymm9
        vpmullw %ymm1, %ymm9, %ymm10
        vpaddw  %ymm2, %ymm9, %ymm11
        vpsllw  $0x3, %ymm9, %ymm9
        vpmulhw %ymm0, %ymm9, %ymm9
        vpsubw  %ymm11, %ymm10, %ymm11
        vpandn  %ymm11, %ymm10, %ymm10
        vpsrlw  $0xf, %ymm10, %ymm10
        vpsubw  %ymm10, %ymm9, %ymm9
        vpmulhrsw %ymm3, %ymm9, %ymm9
        vpand   %ymm4, %ymm9, %ymm9
        vpmaddwd %ymm5, %ymm9, %ymm9
        vpsllvd %ymm6, %ymm9, %ymm9
        vpsrldq $0x8, %ymm9, %ymm10
        vpsrlvq %ymm7, %ymm9, %ymm9
        vpsllq  $0x22, %ymm10, %ymm10
        vpaddq  %ymm10, %ymm9, %ymm9
        vpshufb %ymm8, %ymm9, %ymm9
        vextracti128 $0x1, %ymm9, %xmm10
        vpblendvb %xmm8, %xmm10, %xmm9, %xmm9
        vmovdqu %xmm9, 0x14a(%rdi)
        vmovd   %xmm10,  0x15a(%rdi)
        vpextrw $0x2, %xmm10,  0x15e(%rdi)
        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOADU(%xmm8,32)
        CFI_STACKLOADU(%xmm9,48)
        CFI_STACKLOADU(%xmm10,64)
        CFI_STACKLOADU(%xmm11,80)
        CFI_STACKLOAD(%rdi,96)
        CFI_STACKLOAD(%rsi,104)
        CFI_INC_RSP(112)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d11_x86)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

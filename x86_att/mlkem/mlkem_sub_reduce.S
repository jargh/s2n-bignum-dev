// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Subtract ML-KEM polynomials and reduce the coefficients
// Inputs r[256], a[256] (signed 16-bit words);
// output r[256] (signed 16-bit words)
//
// Sets r[i] := (r[i] - a[i]) mod 3329 in the range 0 <= r[i] < 3329, for
// inputs with |r[i] - a[i]| < 2^15. This is mlkem-native's mlk_poly_sub
// followed by mlk_poly_reduce.
//
// extern void mlkem_sub_reduce(int16_t r[S2N_BIGNUM_STATIC 256],
//                              const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard x86-64 ABI: RDI = r, RSI = a
// Microsoft x64 ABI:   RCX = r, RDX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_sub_reduce)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_sub_reduce)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_sub_reduce)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_sub_reduce):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(96)
        CFI_STACKSAVEU(%xmm6,0)
        CFI_STACKSAVEU(%xmm7,16)
        CFI_STACKSAVEU(%xmm8,32)
        CFI_STACKSAVEU(%xmm9,48)
        CFI_STACKSAVEU(%xmm12,64)
        CFI_STACKSAVE(%rdi,80)
        CFI_STACKSAVE(%rsi,88)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// %ymm0 = 3329 and %ymm1 = 20159 in each word

        movl    $0xd010d01, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movl    $0x4ebf4ebf, %eax
        vmovd   %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1

// Coefficients 0..127

        vmovdqu 0(%rdi), %ymm2
        vmovdqu 32(%rdi), %ymm3
        vmovdqu 64(%rdi), %ymm4
        vmovdqu 96(%rdi), %ymm5
        vmovdqu 128(%rdi), %ymm6
        vmovdqu 160(%rdi), %ymm7
        vmovdqu 192(%rdi), %ymm8
        vmovdqu 224(%rdi), %ymm9
        vpsubw  0(%rsi), %ymm2, %ymm2
        vpsubw  32(%rsi), %ymm3, %ymm3
        vpsubw  64(%rsi), %ymm4, %ymm4
        vpsubw  96(%rsi), %ymm5, %ymm5
        vpsubw  128(%rsi), %ymm6, %ymm6
        vpsubw  160(%rsi), %ymm7, %ymm7
        vpsubw  192(%rsi), %ymm8, %ymm8
        vpsubw  224(%rsi), %ymm9, %ymm9
        vpmulhw %ymm1, %ymm2, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm2, %ymm2
        vpmulhw %ymm1, %ymm3, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm3, %ymm3
        vpmulhw %ymm1, %ymm4, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm4, %ymm4
        vpmulhw %ymm1, %ymm5, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm5, %ymm5
        vpmulhw %ymm1, %ymm6, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm6, %ymm6
        vpmulhw %ymm1, %ymm7, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm7, %ymm7
        vpmulhw %ymm1, %ymm8, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm8, %ymm8
        vpmulhw %ymm1, %ymm9, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm9, %ymm9
        vpsubw  %ymm0, %ymm2, %ymm2
        vpsraw  $15, %ymm2, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm2, %ymm2
        vpsubw  %ymm0, %ymm3, %ymm3
        vpsraw  $15, %ymm3, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm3, %ymm3
        vpsubw  %ymm0, %ymm4, %ymm4
        vpsraw  $15, %ymm4, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm4, %ymm4
        vpsubw  %ymm0, %ymm5, %ymm5
        vpsraw  $15, %ymm5, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm5, %ymm5
        vpsubw  %ymm0, %ymm6, %ymm6
        vpsraw  $15, %ymm6, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm6, %ymm6
        vpsubw  %ymm0, %ymm7, %ymm7
        vpsraw  $15, %ymm7, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm7, %ymm7
        vpsubw  %ymm0, %ymm8, %ymm8
        vpsraw  $15, %ymm8, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm8, %ymm8
        vpsubw  %ymm0, %ymm9, %ymm9
        vpsraw  $15, %ymm9, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm9, %ymm9
        vmovdqu %ymm2, 0(%rdi)
        vmovdqu %ymm3, 32(%rdi)
        vmovdqu %ymm4, 64(%rdi)
        vmovdqu %ymm5, 96(%rdi)
        vmovdqu %ymm6, 128(%rdi)
        vmovdqu %ymm7, 160(%rdi)
        vmovdqu %ymm8, 192(%rdi)
        vmovdqu %ymm9, 224(%rdi)

// Coefficients 128..255

        vmovdqu 256(%rdi), %ymm2
        vmovdqu 288(%rdi), %ymm3
        vmovdqu 320(%rdi), %ymm4
        vmovdqu 352(%rdi), %ymm5
        vmovdqu 384(%rdi), %ymm6
        vmovdqu 416(%rdi), %ymm7
        vmovdqu 448(%rdi), %ymm8
        vmovdqu 480(%rdi), %ymm9
        vpsubw  256(%rsi), %ymm2, %ymm2
        vpsubw  288(%rsi), %ymm3, %ymm3
        vpsubw  320(%rsi), %ymm4, %ymm4
        vpsubw  352(%rsi), %ymm5, %ymm5
        vpsubw  384(%rsi), %ymm6, %ymm6
        vpsubw  416(%rsi), %ymm7, %ymm7
        vpsubw  448(%rsi), %ymm8, %ymm8
        vpsubw  480(%rsi), %ymm9, %ymm9
        vpmulhw %ymm1, %ymm2, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm2, %ymm2
        vpmulhw %ymm1, %ymm3, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm3, %ymm3
        vpmulhw %ymm1, %ymm4, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm4, %ymm4
        vpmulhw %ymm1, %ymm5, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm5, %ymm5
        vpmulhw %ymm1, %ymm6, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm6, %ymm6
        vpmulhw %ymm1, %ymm7, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm7, %ymm7
        vpmulhw %ymm1, %ymm8, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm8, %ymm8
        vpmulhw %ymm1, %ymm9, %ymm12
        vpsraw  $10, %ymm12, %ymm12
        vpmullw %ymm0, %ymm12, %ymm12
        vpsubw  %ymm12, %ymm9, %ymm9
        vpsubw  %ymm0, %ymm2, %ymm2
        vpsraw  $15, %ymm2, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm2, %ymm2
        vpsubw  %ymm0, %ymm3, %ymm3
        vpsraw  $15, %ymm3, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm3, %ymm3
        vpsubw  %ymm0, %ymm4, %ymm4
        vpsraw  $15, %ymm4, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm4, %ymm4
        vpsubw  %ymm0, %ymm5, %ymm5
        vpsraw  $15, %ymm5, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm5, %ymm5
        vpsubw  %ymm0, %ymm6, %ymm6
        vpsraw  $15, %ymm6, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm6, %ymm6
        vpsubw  %ymm0, %ymm7, %ymm7
        vpsraw  $15, %ymm7, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm7, %ymm7
        vpsubw  %ymm0, %ymm8, %ymm8
        vpsraw  $15, %ymm8, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm8, %ymm8
        vpsubw  %ymm0, %ymm9, %ymm9
        vpsraw  $15, %ymm9, %ymm12
        vpand   %ymm0, %ymm12, %ymm12
        vpaddw  %ymm12, %ymm9, %ymm9
        vmovdqu %ymm2, 256(%rdi)
        vmovdqu %ymm3, 288(%rdi)
        vmovdqu %ymm4, 320(%rdi)
        vmovdqu %ymm5, 352(%rdi)
        vmovdqu %ymm6, 384(%rdi)
        vmovdqu %ymm7, 416(%rdi)
        vmovdqu %ymm8, 448(%rdi)
        vmovdqu %ymm9, 480(%rdi)

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOADU(%xmm8,32)
        CFI_STACKLOADU(%xmm9,48)
        CFI_STACKLOADU(%xmm12,64)
        CFI_STACKLOAD(%rdi,80)
        CFI_STACKLOAD(%rsi,88)
        CFI_INC_RSP(96)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_sub_reduce)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

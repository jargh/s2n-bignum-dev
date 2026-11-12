// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Sample from the centered binomial distribution with eta = 2 for ML-KEM
// Input buf[128] (bytes); output r[256] (signed 16-bit words)
//
// Each input byte b = buf[i], with bits b_0 (least significant) to b_7,
// gives two coefficients, each in the range -2..2:
//
//   r[2*i]   = (b_0 + b_1) - (b_2 + b_3)
//   r[2*i+1] = (b_4 + b_5) - (b_6 + b_7)
//
// This is SamplePolyCBD_2 of FIPS 203 (Algorithm 8) on the 128 bytes, as in
// mlkem-native's mlk_poly_cbd2.
//
// extern void mlkem_cbd2(int16_t r[S2N_BIGNUM_STATIC 256],
//                        const uint8_t buf[S2N_BIGNUM_STATIC 128]);
//
// Standard x86-64 ABI: RDI = r, RSI = buf
// Microsoft x64 ABI:   RCX = r, RDX = buf
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_cbd2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_cbd2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_cbd2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_cbd2):
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
#endif

// %ymm0 = 0x000f in each word, %ymm1 = 0x8000 in each word,
// %ymm2 = the table T2 in each lane, %ymm3 = 2 in each word

        movl    $0xf000f, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movl    $0x80008000, %eax
        vmovd   %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1
        movabsq $0x0302020104030302, %rax
        vmovq   %rax, %xmm2
        movabsq $0x0201010003020201, %rax
        vpinsrq $1, %rax, %xmm2, %xmm2
        vinserti128 $1, %xmm2, %ymm2, %ymm2
        movl    $0x20002, %eax
        vmovd   %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3

// For each 8 bytes, 16 coefficients

        vpmovzxbd  0(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 0(%rdi)
        vpmovzxbd  8(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 32(%rdi)
        vpmovzxbd  16(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 64(%rdi)
        vpmovzxbd  24(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 96(%rdi)
        vpmovzxbd  32(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 128(%rdi)
        vpmovzxbd  40(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 160(%rdi)
        vpmovzxbd  48(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 192(%rdi)
        vpmovzxbd  56(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 224(%rdi)
        vpmovzxbd  64(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 256(%rdi)
        vpmovzxbd  72(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 288(%rdi)
        vpmovzxbd  80(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 320(%rdi)
        vpmovzxbd  88(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 352(%rdi)
        vpmovzxbd  96(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 384(%rdi)
        vpmovzxbd  104(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 416(%rdi)
        vpmovzxbd  112(%rsi), %ymm4
        vpslld  $12, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vpor    %ymm1, %ymm4, %ymm4
        vpshufb %ymm4, %ymm2, %ymm4
        vpsubw  %ymm3, %ymm4, %ymm4
        vmovdqu %ymm4, 448(%rdi)
        vpmovzxbd  120(%rsi), %ymm6
        vpslld  $12, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm0, %ymm6, %ymm6
        vpor    %ymm1, %ymm6, %ymm6
        vpshufb %ymm6, %ymm2, %ymm6
        vpsubw  %ymm3, %ymm6, %ymm6
        vmovdqu %ymm6, 480(%rdi)

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOAD(%rdi,32)
        CFI_STACKLOAD(%rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_cbd2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

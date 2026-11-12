// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert a 32-byte message to an ML-KEM polynomial
// Input msg[32] (bytes); output r[256] (signed 16-bit words)
//
// Coefficient 8 * i + j is 1665 = (3329 + 1) / 2 if bit j of msg[i] is
// set and 0 otherwise, i.e. Decompress_1 of FIPS 203 (section 4.2.1)
// applied to ByteDecode_1(msg), as in mlkem-native's mlk_poly_frommsg.
//
// extern void mlkem_frommsg(int16_t r[S2N_BIGNUM_STATIC 256],
//                           const uint8_t msg[S2N_BIGNUM_STATIC 32]);
//
// Standard x86-64 ABI: RDI = r, RSI = msg
// Microsoft x64 ABI:   RCX = r, RDX = msg
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_frommsg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_frommsg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_frommsg)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_frommsg):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(%rdi,0)
        CFI_STACKSAVE(%rsi,8)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// %ymm0 = 1665 in each word, %ymm1 = 2^(15-k) in word k

        movl    $0x6810681, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movabsq $0x1000200040008000, %rax
        vmovq   %rax, %xmm1
        movabsq $0x0100020004000800, %rax
        vpinsrq $1, %rax, %xmm1, %xmm1
        movabsq $0x0010002000400080, %rax
        vmovq   %rax, %xmm2
        movabsq $0x0001000200040008, %rax
        vpinsrq $1, %rax, %xmm2, %xmm2
        vinserti128 $1, %xmm2, %ymm1, %ymm1

// For each 16-bit chunk of the message, 16 coefficients

        vpbroadcastw  0(%rsi), %ymm2
        vpmullw %ymm1, %ymm2, %ymm2
        vpsraw  $15, %ymm2, %ymm2
        vpand   %ymm0, %ymm2, %ymm2
        vmovdqu %ymm2, 0(%rdi)
        vpbroadcastw  2(%rsi), %ymm3
        vpmullw %ymm1, %ymm3, %ymm3
        vpsraw  $15, %ymm3, %ymm3
        vpand   %ymm0, %ymm3, %ymm3
        vmovdqu %ymm3, 32(%rdi)
        vpbroadcastw  4(%rsi), %ymm4
        vpmullw %ymm1, %ymm4, %ymm4
        vpsraw  $15, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 64(%rdi)
        vpbroadcastw  6(%rsi), %ymm5
        vpmullw %ymm1, %ymm5, %ymm5
        vpsraw  $15, %ymm5, %ymm5
        vpand   %ymm0, %ymm5, %ymm5
        vmovdqu %ymm5, 96(%rdi)
        vpbroadcastw  8(%rsi), %ymm2
        vpmullw %ymm1, %ymm2, %ymm2
        vpsraw  $15, %ymm2, %ymm2
        vpand   %ymm0, %ymm2, %ymm2
        vmovdqu %ymm2, 128(%rdi)
        vpbroadcastw  10(%rsi), %ymm3
        vpmullw %ymm1, %ymm3, %ymm3
        vpsraw  $15, %ymm3, %ymm3
        vpand   %ymm0, %ymm3, %ymm3
        vmovdqu %ymm3, 160(%rdi)
        vpbroadcastw  12(%rsi), %ymm4
        vpmullw %ymm1, %ymm4, %ymm4
        vpsraw  $15, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 192(%rdi)
        vpbroadcastw  14(%rsi), %ymm5
        vpmullw %ymm1, %ymm5, %ymm5
        vpsraw  $15, %ymm5, %ymm5
        vpand   %ymm0, %ymm5, %ymm5
        vmovdqu %ymm5, 224(%rdi)
        vpbroadcastw  16(%rsi), %ymm2
        vpmullw %ymm1, %ymm2, %ymm2
        vpsraw  $15, %ymm2, %ymm2
        vpand   %ymm0, %ymm2, %ymm2
        vmovdqu %ymm2, 256(%rdi)
        vpbroadcastw  18(%rsi), %ymm3
        vpmullw %ymm1, %ymm3, %ymm3
        vpsraw  $15, %ymm3, %ymm3
        vpand   %ymm0, %ymm3, %ymm3
        vmovdqu %ymm3, 288(%rdi)
        vpbroadcastw  20(%rsi), %ymm4
        vpmullw %ymm1, %ymm4, %ymm4
        vpsraw  $15, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 320(%rdi)
        vpbroadcastw  22(%rsi), %ymm5
        vpmullw %ymm1, %ymm5, %ymm5
        vpsraw  $15, %ymm5, %ymm5
        vpand   %ymm0, %ymm5, %ymm5
        vmovdqu %ymm5, 352(%rdi)
        vpbroadcastw  24(%rsi), %ymm2
        vpmullw %ymm1, %ymm2, %ymm2
        vpsraw  $15, %ymm2, %ymm2
        vpand   %ymm0, %ymm2, %ymm2
        vmovdqu %ymm2, 384(%rdi)
        vpbroadcastw  26(%rsi), %ymm3
        vpmullw %ymm1, %ymm3, %ymm3
        vpsraw  $15, %ymm3, %ymm3
        vpand   %ymm0, %ymm3, %ymm3
        vmovdqu %ymm3, 416(%rdi)
        vpbroadcastw  28(%rsi), %ymm4
        vpmullw %ymm1, %ymm4, %ymm4
        vpsraw  $15, %ymm4, %ymm4
        vpand   %ymm0, %ymm4, %ymm4
        vmovdqu %ymm4, 448(%rdi)
        vpbroadcastw  30(%rsi), %ymm5
        vpmullw %ymm1, %ymm5, %ymm5
        vpsraw  $15, %ymm5, %ymm5
        vpand   %ymm0, %ymm5, %ymm5
        vmovdqu %ymm5, 480(%rdi)

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(%rdi,0)
        CFI_STACKLOAD(%rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_frommsg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

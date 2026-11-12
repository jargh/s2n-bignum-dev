// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert an ML-KEM polynomial to a 32-byte message
// Input a[256] (signed 16-bit words); output msg[32] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Bit j of msg[i] is round(2 * a[8 * i + j] / 3329) mod 2, i.e. 1 exactly
// when 833 <= a[8 * i + j] <= 2496: ByteEncode_1 of Compress_1 (FIPS 203,
// section 4.2.1), as in mlkem-native's mlk_poly_tomsg.
//
// extern void mlkem_tomsg(uint8_t msg[S2N_BIGNUM_STATIC 32],
//                         const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard x86-64 ABI: RDI = msg, RSI = a
// Microsoft x64 ABI:   RCX = msg, RDX = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_tomsg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_tomsg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_tomsg)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_tomsg):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(%rdi,0)
        CFI_STACKSAVE(%rsi,8)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// %ymm0 = 833 and %ymm1 = 2497 in each word

        movl    $0x3410341, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
        movl    $0x9c109c1, %eax
        vmovd   %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1

// For each pair of vectors, 32 coefficients to 4 bytes

        vmovdqu 0(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 32(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 0(%rdi)
        vmovdqu 64(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 96(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 4(%rdi)
        vmovdqu 128(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 160(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 8(%rdi)
        vmovdqu 192(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 224(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 12(%rdi)
        vmovdqu 256(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 288(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 16(%rdi)
        vmovdqu 320(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 352(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 20(%rdi)
        vmovdqu 384(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 416(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 24(%rdi)
        vmovdqu 448(%rsi), %ymm2
        vpsubw  %ymm0, %ymm2, %ymm3
        vpsubw  %ymm1, %ymm2, %ymm2
        vpandn  %ymm2, %ymm3, %ymm2
        vpsrlw  $15, %ymm2, %ymm2
        vmovdqu 480(%rsi), %ymm4
        vpsubw  %ymm0, %ymm4, %ymm5
        vpsubw  %ymm1, %ymm4, %ymm4
        vpandn  %ymm4, %ymm5, %ymm4
        vpsrlw  $15, %ymm4, %ymm4
        vpackuswb %ymm4, %ymm2, %ymm2
        vpermq  $0xd8, %ymm2, %ymm2
        vpsllw  $7, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movl    %eax, 28(%rdi)

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(%rdi,0)
        CFI_STACKLOAD(%rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_tomsg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

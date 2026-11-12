// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Sample from the centered binomial distribution with eta = 3 for ML-KEM
// Input buf[192] (bytes); output r[256] (signed 16-bit words)
//
// Each group of 3 input bytes, the 24-bit little-endian number t, gives
// four coefficients, each in the range -3..3: with t_k the bits of t,
//
//   r[4*i+j] = (t_6j + t_6j+1 + t_6j+2) - (t_6j+3 + t_6j+4 + t_6j+5)
//
// for group i = 0..63 and j = 0..3. This is SamplePolyCBD_3 of FIPS 203
// (Algorithm 8) on the 192 bytes, as in mlkem-native's mlk_poly_cbd3.
//
// extern void mlkem_cbd3(int16_t r[S2N_BIGNUM_STATIC 256],
//                        const uint8_t buf[S2N_BIGNUM_STATIC 192]);
//
// Standard x86-64 ABI: RDI = r, RSI = buf
// Microsoft x64 ABI:   RCX = r, RDX = buf
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_cbd3)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_cbd3)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_cbd3)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_cbd3):
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
#endif

// %ymm0 = the byte selection in each lane, %ymm1 = the shifts 0, 4,
// %ymm2 = 0x003f003f in each dword, %ymm3 = 7 in each word,
// %ymm8 = the popcounts of 0..7 in each lane, %ymm9 = the byte
// selection for the last vector

        movabsq $0x8080020180800100, %rax
        vmovq   %rax, %xmm0
        movabsq $0x8080050480800403, %rax
        vpinsrq $1, %rax, %xmm0, %xmm0
        vinserti128 $1, %xmm0, %ymm0, %ymm0
        movl    $0x4, %eax
        vmovd   %eax, %xmm1
        vpbroadcastd %xmm1, %ymm1
        vpsllq  $32, %ymm1, %ymm1
        movl    $0x3f003f, %eax
        vmovd   %eax, %xmm2
        vpbroadcastd %xmm2, %ymm2
        movl    $0x70007, %eax
        vmovd   %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3
        movabsq $0x0302020102010100, %rax
        vmovq   %rax, %xmm8
        movabsq $0x0000000000000000, %rax
        vpinsrq $1, %rax, %xmm8, %xmm8
        vinserti128 $1, %xmm8, %ymm8, %ymm8
        movabsq $0x8080060580800504, %rax
        vmovq   %rax, %xmm9
        movabsq $0x8080090880800807, %rax
        vpinsrq $1, %rax, %xmm9, %xmm9
        movabsq $0x80800c0b80800b0a, %rax
        vmovq   %rax, %xmm10
        movabsq $0x80800f0e80800e0d, %rax
        vpinsrq $1, %rax, %xmm10, %xmm10
        vinserti128 $1, %xmm10, %ymm9, %ymm9

// For each 12 bytes, 16 coefficients

        vmovdqu 0(%rsi), %xmm4
        vinserti128 $1,  6(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 0(%rdi)
        vmovdqu 12(%rsi), %xmm6
        vinserti128 $1,  18(%rsi), %ymm6, %ymm6
        vpshufb %ymm0, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 32(%rdi)
        vmovdqu 24(%rsi), %xmm4
        vinserti128 $1,  30(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 64(%rdi)
        vmovdqu 36(%rsi), %xmm6
        vinserti128 $1,  42(%rsi), %ymm6, %ymm6
        vpshufb %ymm0, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 96(%rdi)
        vmovdqu 48(%rsi), %xmm4
        vinserti128 $1,  54(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 128(%rdi)
        vmovdqu 60(%rsi), %xmm6
        vinserti128 $1,  66(%rsi), %ymm6, %ymm6
        vpshufb %ymm0, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 160(%rdi)
        vmovdqu 72(%rsi), %xmm4
        vinserti128 $1,  78(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 192(%rdi)
        vmovdqu 84(%rsi), %xmm6
        vinserti128 $1,  90(%rsi), %ymm6, %ymm6
        vpshufb %ymm0, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 224(%rdi)
        vmovdqu 96(%rsi), %xmm4
        vinserti128 $1,  102(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 256(%rdi)
        vmovdqu 108(%rsi), %xmm6
        vinserti128 $1,  114(%rsi), %ymm6, %ymm6
        vpshufb %ymm0, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 288(%rdi)
        vmovdqu 120(%rsi), %xmm4
        vinserti128 $1,  126(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 320(%rdi)
        vmovdqu 132(%rsi), %xmm6
        vinserti128 $1,  138(%rsi), %ymm6, %ymm6
        vpshufb %ymm0, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 352(%rdi)
        vmovdqu 144(%rsi), %xmm4
        vinserti128 $1,  150(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 384(%rdi)
        vmovdqu 156(%rsi), %xmm6
        vinserti128 $1,  162(%rsi), %ymm6, %ymm6
        vpshufb %ymm0, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 416(%rdi)
        vmovdqu 168(%rsi), %xmm4
        vinserti128 $1,  174(%rsi), %ymm4, %ymm4
        vpshufb %ymm0, %ymm4, %ymm4
        vpsrlvd %ymm1, %ymm4, %ymm4
        vpslld  $10, %ymm4, %ymm5
        vpor    %ymm5, %ymm4, %ymm4
        vpand   %ymm2, %ymm4, %ymm4
        vpsrlw  $3, %ymm4, %ymm5
        vpand   %ymm3, %ymm4, %ymm4
        vpshufb %ymm4, %ymm8, %ymm4
        vpshufb %ymm5, %ymm8, %ymm5
        vpsubw  %ymm5, %ymm4, %ymm4
        vmovdqu %ymm4, 448(%rdi)
        vmovdqu 176(%rsi), %xmm6
        vinserti128 $1, %xmm6, %ymm6, %ymm6
        vpshufb %ymm9, %ymm6, %ymm6
        vpsrlvd %ymm1, %ymm6, %ymm6
        vpslld  $10, %ymm6, %ymm7
        vpor    %ymm7, %ymm6, %ymm6
        vpand   %ymm2, %ymm6, %ymm6
        vpsrlw  $3, %ymm6, %ymm7
        vpand   %ymm3, %ymm6, %ymm6
        vpshufb %ymm6, %ymm8, %ymm6
        vpshufb %ymm7, %ymm8, %ymm7
        vpsubw  %ymm7, %ymm6, %ymm6
        vmovdqu %ymm6, 480(%rdi)

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

S2N_BN_SIZE_DIRECTIVE(mlkem_cbd3)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

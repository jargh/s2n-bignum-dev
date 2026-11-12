// Copyright (c) 2017-2025 The OpenSSL Project Authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Written by Andy Polyakov, @dot-asm, initially for use in the OpenSSL
// project (keccak1600-avx2.pl).

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, with AVX2
// Input a[25], rc[24]; output a[25]
//
// The input/output argument is a 25-element Keccak array, replaced by its
// Keccak-f1600 permutation with the round constants rc, as by
// sha3_keccak_f1600 (this is the same function, with AVX2). The lane
// A[0][0] is in all four quadwords of ymm0 and the other 24 lanes in
// ymm1-ymm6, four in each, in an order in which pi is intra-register:
// with the lanes A[y][x] = a[5 y + x] (quadwords 0..3),
//
//   ymm1  A[0][1]  A[0][2]  A[0][3]  A[0][4]
//   ymm2  A[2][0]  A[4][0]  A[1][0]  A[3][0]
//   ymm3  A[3][1]  A[1][2]  A[4][3]  A[2][4]
//   ymm4  A[2][1]  A[4][2]  A[1][3]  A[3][4]
//   ymm5  A[4][1]  A[3][2]  A[2][3]  A[1][4]
//   ymm6  A[1][1]  A[2][2]  A[3][3]  A[4][4]
//
// and the state is gathered into that order at the start and scattered
// back at the end. The rotation counts of rho (vpsllvq and vpsrlvq)
// are in a table after the code, read RIP-relatively.
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
// extern void sha3_keccak_f1600_alt(uint64_t a[S2N_BIGNUM_STATIC 25],
//                                   const uint64_t rc[S2N_BIGNUM_STATIC 24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak_f1600_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak_f1600_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak_f1600_alt)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak_f1600_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(176)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVEU(xmm8,32)
        CFI_STACKSAVEU(xmm9,48)
        CFI_STACKSAVEU(xmm10,64)
        CFI_STACKSAVEU(xmm11,80)
        CFI_STACKSAVEU(xmm12,96)
        CFI_STACKSAVEU(xmm13,112)
        CFI_STACKSAVEU(xmm14,128)
        CFI_STACKSAVEU(xmm15,144)
        CFI_STACKSAVE(rdi,160)
        CFI_STACKSAVE(rsi,168)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// The rotation tables (biased by 96 as in OpenSSL, for 8-bit offsets)
// and the state

        lea     r8, [rip+sha3_keccak_f1600_alt_rhotates_left+96]
        lea     r9, [rip+sha3_keccak_f1600_alt_rhotates_right+96]
        vpbroadcastq ymm0, QWORD PTR [rdi]
        vmovdqu ymm1, YMMWORD PTR [rdi+8]
        vmovq   xmm2, QWORD PTR [rdi+80]
        vpinsrq xmm2, xmm2, QWORD PTR [rdi+160], 1
        vmovq   xmm7, QWORD PTR [rdi+40]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+120], 1
        vinserti128 ymm2, ymm2, xmm7, 1
        vmovq   xmm3, QWORD PTR [rdi+128]
        vpinsrq xmm3, xmm3, QWORD PTR [rdi+56], 1
        vmovq   xmm7, QWORD PTR [rdi+184]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+112], 1
        vinserti128 ymm3, ymm3, xmm7, 1
        vmovq   xmm4, QWORD PTR [rdi+88]
        vpinsrq xmm4, xmm4, QWORD PTR [rdi+176], 1
        vmovq   xmm7, QWORD PTR [rdi+64]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+152], 1
        vinserti128 ymm4, ymm4, xmm7, 1
        vmovq   xmm5, QWORD PTR [rdi+168]
        vpinsrq xmm5, xmm5, QWORD PTR [rdi+136], 1
        vmovq   xmm7, QWORD PTR [rdi+104]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+72], 1
        vinserti128 ymm5, ymm5, xmm7, 1
        vmovq   xmm6, QWORD PTR [rdi+48]
        vpinsrq xmm6, xmm6, QWORD PTR [rdi+96], 1
        vmovq   xmm7, QWORD PTR [rdi+144]
        vpinsrq xmm7, xmm7, QWORD PTR [rdi+192], 1
        vinserti128 ymm6, ymm6, xmm7, 1

        mov     eax, 24

// The 24 rounds

        .balign 32
sha3_keccak_f1600_alt_loop:

// Theta

        vpunpcklqdq ymm13, ymm2, ymm2
        vpunpckhqdq ymm7, ymm2, ymm2
        vpxor   ymm12, ymm5, ymm3
        vpxor   ymm9, ymm4, ymm6
        vpxor   ymm12, ymm12, ymm1
        vpxor   ymm12, ymm12, ymm9
        vpermq  ymm11, ymm12, 0x93
        vpxor   ymm13, ymm13, ymm7
        vpermq  ymm7, ymm13, 0x4e
        vpsrlq  ymm8, ymm12, 63
        vpaddq  ymm9, ymm12, ymm12
        vpor    ymm8, ymm8, ymm9
        vpermq  ymm15, ymm8, 0x39
        vpxor   ymm14, ymm8, ymm11
        vpermq  ymm14, ymm14, 0x00
        vpxor   ymm13, ymm13, ymm0
        vpxor   ymm13, ymm13, ymm7
        vpsrlq  ymm7, ymm13, 63
        vpaddq  ymm8, ymm13, ymm13
        vpor    ymm8, ymm8, ymm7
        vpxor   ymm2, ymm2, ymm14
        vpxor   ymm0, ymm0, ymm14
        vpblendd ymm15, ymm15, ymm8, 0xc0
        vpblendd ymm11, ymm11, ymm13, 0x03
        vpxor   ymm15, ymm15, ymm11

// Rho + pi + pre-chi shuffle

        vpsllvq ymm10, ymm2, YMMWORD PTR [r8-96]
        vpsrlvq ymm2, ymm2, YMMWORD PTR [r9-96]
        vpor    ymm2, ymm2, ymm10
        vpxor   ymm3, ymm3, ymm15
        vpsllvq ymm11, ymm3, YMMWORD PTR [r8-32]
        vpsrlvq ymm3, ymm3, YMMWORD PTR [r9-32]
        vpor    ymm3, ymm3, ymm11
        vpxor   ymm4, ymm4, ymm15
        vpsllvq ymm12, ymm4, YMMWORD PTR [r8]
        vpsrlvq ymm4, ymm4, YMMWORD PTR [r9]
        vpor    ymm4, ymm4, ymm12
        vpxor   ymm5, ymm5, ymm15
        vpsllvq ymm13, ymm5, YMMWORD PTR [r8+32]
        vpsrlvq ymm5, ymm5, YMMWORD PTR [r9+32]
        vpor    ymm5, ymm5, ymm13
        vpxor   ymm6, ymm6, ymm15
        vpermq  ymm10, ymm2, 0x8d
        vpermq  ymm11, ymm3, 0x8d
        vpsllvq ymm14, ymm6, YMMWORD PTR [r8+64]
        vpsrlvq ymm8, ymm6, YMMWORD PTR [r9+64]
        vpor    ymm8, ymm8, ymm14
        vpxor   ymm1, ymm1, ymm15
        vpermq  ymm12, ymm4, 0x1b
        vpermq  ymm13, ymm5, 0x72
        vpsllvq ymm15, ymm1, YMMWORD PTR [r8-64]
        vpsrlvq ymm9, ymm1, YMMWORD PTR [r9-64]
        vpor    ymm9, ymm9, ymm15

// Chi

        vpsrldq ymm14, ymm8, 8
        vpandn  ymm7, ymm8, ymm14
        vpblendd ymm3, ymm9, ymm13, 0x0c
        vpblendd ymm15, ymm11, ymm9, 0x0c
        vpblendd ymm5, ymm10, ymm11, 0x0c
        vpblendd ymm14, ymm9, ymm10, 0x0c
        vpblendd ymm3, ymm3, ymm11, 0x30
        vpblendd ymm15, ymm15, ymm12, 0x30
        vpblendd ymm5, ymm5, ymm9, 0x30
        vpblendd ymm14, ymm14, ymm13, 0x30
        vpblendd ymm3, ymm3, ymm12, 0xc0
        vpblendd ymm15, ymm15, ymm13, 0xc0
        vpblendd ymm5, ymm5, ymm13, 0xc0
        vpblendd ymm14, ymm14, ymm11, 0xc0
        vpandn  ymm3, ymm3, ymm15
        vpandn  ymm5, ymm5, ymm14
        vpblendd ymm6, ymm12, ymm9, 0x0c
        vpblendd ymm15, ymm10, ymm12, 0x0c
        vpxor   ymm3, ymm3, ymm10
        vpblendd ymm6, ymm6, ymm10, 0x30
        vpblendd ymm15, ymm15, ymm11, 0x30
        vpxor   ymm5, ymm5, ymm12
        vpblendd ymm6, ymm6, ymm11, 0xc0
        vpblendd ymm15, ymm15, ymm9, 0xc0
        vpandn  ymm6, ymm6, ymm15
        vpxor   ymm6, ymm6, ymm13
        vpermq  ymm4, ymm8, 0x1e
        vpblendd ymm15, ymm4, ymm0, 0x30
        vpermq  ymm1, ymm8, 0x39
        vpblendd ymm1, ymm1, ymm0, 0xc0
        vpandn  ymm1, ymm1, ymm15
        vpblendd ymm2, ymm11, ymm12, 0x0c
        vpblendd ymm14, ymm13, ymm11, 0x0c
        vpblendd ymm2, ymm2, ymm13, 0x30
        vpblendd ymm14, ymm14, ymm10, 0x30
        vpblendd ymm2, ymm2, ymm10, 0xc0
        vpblendd ymm14, ymm14, ymm12, 0xc0
        vpandn  ymm2, ymm2, ymm14
        vpxor   ymm2, ymm2, ymm9
        vpermq  ymm7, ymm7, 0x00
        vpermq  ymm3, ymm3, 0x1b
        vpermq  ymm5, ymm5, 0x8d
        vpermq  ymm6, ymm6, 0x72
        vpblendd ymm4, ymm13, ymm10, 0x0c
        vpblendd ymm14, ymm12, ymm13, 0x0c
        vpblendd ymm4, ymm4, ymm12, 0x30
        vpblendd ymm14, ymm14, ymm9, 0x30
        vpblendd ymm4, ymm4, ymm9, 0xc0
        vpblendd ymm14, ymm14, ymm10, 0xc0
        vpandn  ymm4, ymm4, ymm14
        vpxor   ymm0, ymm0, ymm7
        vpxor   ymm1, ymm1, ymm8
        vpxor   ymm4, ymm4, ymm11

// Iota

        vpbroadcastq ymm7, QWORD PTR [rsi]
        vpxor   ymm0, ymm0, ymm7
        add     rsi, 8
        dec     eax
        jnz     sha3_keccak_f1600_alt_loop

// Store the state

        vmovq   QWORD PTR [rdi], xmm0
        vmovdqu YMMWORD PTR [rdi+8], ymm1
        vmovq   QWORD PTR [rdi+80], xmm2
        vpextrq QWORD PTR [rdi+160], xmm2, 1
        vextracti128 xmm7, ymm2, 1
        vmovq   QWORD PTR [rdi+40], xmm7
        vpextrq QWORD PTR [rdi+120], xmm7, 1
        vmovq   QWORD PTR [rdi+128], xmm3
        vpextrq QWORD PTR [rdi+56], xmm3, 1
        vextracti128 xmm7, ymm3, 1
        vmovq   QWORD PTR [rdi+184], xmm7
        vpextrq QWORD PTR [rdi+112], xmm7, 1
        vmovq   QWORD PTR [rdi+88], xmm4
        vpextrq QWORD PTR [rdi+176], xmm4, 1
        vextracti128 xmm7, ymm4, 1
        vmovq   QWORD PTR [rdi+64], xmm7
        vpextrq QWORD PTR [rdi+152], xmm7, 1
        vmovq   QWORD PTR [rdi+168], xmm5
        vpextrq QWORD PTR [rdi+136], xmm5, 1
        vextracti128 xmm7, ymm5, 1
        vmovq   QWORD PTR [rdi+104], xmm7
        vpextrq QWORD PTR [rdi+72], xmm7, 1
        vmovq   QWORD PTR [rdi+48], xmm6
        vpextrq QWORD PTR [rdi+96], xmm6, 1
        vextracti128 xmm7, ymm6, 1
        vmovq   QWORD PTR [rdi+144], xmm7
        vpextrq QWORD PTR [rdi+192], xmm7, 1

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOADU(xmm8,32)
        CFI_STACKLOADU(xmm9,48)
        CFI_STACKLOADU(xmm10,64)
        CFI_STACKLOADU(xmm11,80)
        CFI_STACKLOADU(xmm12,96)
        CFI_STACKLOADU(xmm13,112)
        CFI_STACKLOADU(xmm14,128)
        CFI_STACKLOADU(xmm15,144)
        CFI_STACKLOAD(rdi,160)
        CFI_STACKLOAD(rsi,168)
        CFI_INC_RSP(176)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha3_keccak_f1600_alt)

// The rotation counts, left and right, of the lanes of ymm2, ymm1,
// ymm3, ymm4, ymm5 and ymm6 (as in OpenSSL)

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 32
sha3_keccak_f1600_alt_rhotates_left:
        .quad   3, 18, 36, 41
        .quad   1, 62, 28, 27
        .quad   45, 6, 56, 39
        .quad   10, 61, 55, 8
        .quad   2, 15, 25, 20
        .quad   44, 43, 21, 14
sha3_keccak_f1600_alt_rhotates_right:
        .quad   61, 46, 28, 23
        .quad   63, 2, 36, 37
        .quad   19, 58, 8, 25
        .quad   54, 3, 9, 56
        .quad   62, 49, 39, 44
        .quad   20, 21, 43, 50

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

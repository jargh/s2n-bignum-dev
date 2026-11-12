// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Uniform rejection sampling for ML-KEM, appending to a partial result,
// with AVX-512
// Inputs r[n], n, *buf (unsigned bytes), buflen; output r[256] (signed
// 16-bit words), return
//
// extern uint64_t mlkem_rej_uniform_alt_VARIABLE_TIME_avx512
//                     (int16_t r[S2N_BIGNUM_STATIC 256],uint64_t n,
//                      const uint8_t *buf,uint64_t buflen);
//
// The same function as mlkem_rej_uniform_alt_VARIABLE_TIME, without its
// table, for processors with AVX-512F and AVX-512BW: starting
// from n <= 256 entries already in r, interprets the buffer as packed
// 12-bit numbers with a length of buflen bytes, assumed to be a multiple
// of 24, and appends to r[0..n-1] those numbers from it that are < 3329,
// in the order of appearance, up to a total of 256, returning the new
// total n'. The entries r[n'..255] may be overwritten with other values.
// This is not constant time: the time depends on how much of the buffer
// is needed.
//
// Standard x86-64 ABI: RDI = r, RSI = n, RDX = buf, RCX = buflen
// Microsoft x64 ABI:   RCX = r, RDX = n, R8 = buf, R9 = buflen
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME_avx512)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME_avx512)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME_avx512)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME_avx512):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(rdi,0)
        CFI_STACKSAVE(rsi,8)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Each 24 bytes of the buffer give 16 fields, one in each dword of zmm0:
// lanes 0 and 1 of zmm0 get bytes 0-15, lanes 2 and 3 bytes 8-23, and
// zmm16 has the byte pair of each field in the low bytes of its dword
// (the other bytes are cleared later). zmm17 = 0x0fff and zmm18 = 3329
// in each dword, k2 = lanes 2 and 3, k3 = the odd dwords. r8 = the bytes
// left, rdi points at r[n].

        mov     r8, rcx
        movabs  rax, 0x0504040302010100
        vmovq   xmm1, rax
        movabs  rax, 0x0b0a0a0908070706
        vpinsrq xmm1, xmm1, rax, 1
        movabs  rax, 0x0908080706050504
        vmovq   xmm2, rax
        movabs  rax, 0x0f0e0e0d0c0b0b0a
        vpinsrq xmm2, xmm2, rax, 1
        vinserti128 ymm1, ymm1, xmm2, 1
        vpmovzxwd zmm16, ymm1
        mov     eax, 0xfff
        vpbroadcastd zmm17, eax
        mov     eax, 3329
        vpbroadcastd zmm18, eax
        mov     eax, 0xff00
        kmovw   k2, eax
        mov     eax, 0xaaaa
        kmovw   k3, eax
        lea     rdi, [rdi+2*rsi]

        sub     r8, 24
        jb      mlkem_rej_uniform_alt_avx512_end
        cmp     rsi, 240
        ja      mlkem_rej_uniform_alt_avx512_last

// The 16 fields, as dwords: the low 12 bits of the byte pair for the even
// fields and the high 12 bits for the odd ones. k1 = those < 3329 (the
// signs of the fields - 3329), and they are packed into the low dwords of
// zmm0, then the low words of r (writing 16 words, since there is room
// for them). The loop continues while there are 24 more bytes and n <= 240.
// It is 32-byte aligned, with no branch crossing or ending at a 32-byte
// boundary, so that cores with the fix for Intel's JCC erratum keep it in
// the decoded instruction cache.

        .balign 32
mlkem_rej_uniform_alt_avx512_loop:
        vbroadcasti32x4 zmm0, [rdx]
        vbroadcasti32x4 zmm0{k2}, [rdx+8]
        add     rdx, 24
        vpshufb zmm0, zmm0, zmm16
        vpsrld  zmm0{k3}, zmm0, 4
        vpandd  zmm0, zmm0, zmm17
        vpcmpgtd k1, zmm18, zmm0
        vpcompressd zmm0{k1}{z}, zmm0
        vpmovdw [rdi], zmm0
        kmovw   eax, k1
        popcnt  eax, eax
        lea     rdi, [rdi+2*rax]
        add     rsi, rax
        sub     r8, 24
        jb      mlkem_rej_uniform_alt_avx512_end
        cmp     rsi, 240
        jbe     mlkem_rej_uniform_alt_avx512_loop

// Otherwise (240 < n), while n < 256 and there are 24 more bytes, the
// same, writing only the 256 - n words that fit and adding min(c, 256 - n)
// to n for the c fields < 3329

mlkem_rej_uniform_alt_avx512_last:
        cmp     rsi, 256
        jae     mlkem_rej_uniform_alt_avx512_end
        vbroadcasti32x4 zmm0, [rdx]
        vbroadcasti32x4 zmm0{k2}, [rdx+8]
        add     rdx, 24
        vpshufb zmm0, zmm0, zmm16
        vpsrld  zmm0{k3}, zmm0, 4
        vpandd  zmm0, zmm0, zmm17
        vpcmpgtd k1, zmm18, zmm0
        vpcompressd zmm0{k1}{z}, zmm0
        mov     ecx, 256
        sub     ecx, esi
        mov     eax, 1
        shl     eax, cl
        dec     eax
        kmovw   k4, eax
        vpmovdw [rdi]{k4}, zmm0
        kmovw   eax, k1
        popcnt  eax, eax
        cmp     eax, ecx
        cmova   eax, ecx
        lea     rdi, [rdi+2*rax]
        add     rsi, rax
        sub     r8, 24
        jae     mlkem_rej_uniform_alt_avx512_last

mlkem_rej_uniform_alt_avx512_end:
        mov     rax, rsi

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(rdi,0)
        CFI_STACKLOAD(rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME_avx512)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

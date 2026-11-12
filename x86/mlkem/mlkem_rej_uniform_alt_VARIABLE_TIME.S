// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Uniform rejection sampling for ML-KEM, appending to a partial result
// Inputs r[n], n, *buf (unsigned bytes), buflen, table (unsigned bytes);
// output r[256] (signed 16-bit words), return
//
// extern uint64_t mlkem_rej_uniform_alt_VARIABLE_TIME
//                     (int16_t r[S2N_BIGNUM_STATIC 256],uint64_t n,
//                      const uint8_t *buf,uint64_t buflen,
//                      const uint8_t *table);
//
// Like mlkem_rej_uniform_VARIABLE_TIME, with the same table, but starting
// from n <= 256 entries already in r: interprets the buffer as packed
// 12-bit numbers with a length of buflen bytes, assumed to be a multiple
// of 24, and appends to r[0..n-1] those numbers from it that are < 3329,
// in the order of appearance, up to a total of 256, returning the new
// total n'. With n = 0 this is the non-alt function, except that the
// entries r[n'..255] may be overwritten with other values (the non-alt
// version zeroes them). This is not constant time: the time depends on
// how much of the buffer is needed.
//
// Standard x86-64 ABI: RDI = r, RSI = n, RDX = buf, RCX = buflen,
//                      R8 = table
// Microsoft x64 ABI:   RCX = r, RDX = n, R8 = buf, R9 = buflen,
//                      [RSP+40] = table
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        .text
        .balign 32

S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(48)
        CFI_STACKSAVEU(xmm6,0)
        CFI_STACKSAVEU(xmm7,16)
        CFI_STACKSAVE(rdi,32)
        CFI_STACKSAVE(rsi,40)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+88]
#endif

// ymm3 = 3329 in each word, ymm5 = 0x0fff in each word, ymm6 = the
// byte pairs of the fields (lane 1 from 4 bytes in); rdi points at
// r[n], and there are 32 bytes on the stack for the last steps

        mov     eax, 0xd010d01
        vmovd   xmm3, eax
        vpbroadcastd ymm3, xmm3
        mov     eax, 0xfff0fff
        vmovd   xmm5, eax
        vpbroadcastd ymm5, xmm5
        movabs  rax, 0x0504040302010100
        vmovq   xmm6, rax
        movabs  rax, 0x0b0a0a0908070706
        vpinsrq xmm6, xmm6, rax, 1
        movabs  rax, 0x0908080706050504
        vmovq   xmm7, rax
        movabs  rax, 0x0f0e0e0d0c0b0b0a
        vpinsrq xmm7, xmm7, rax, 1
        vinserti128 ymm6, ymm6, xmm7, 1
        lea     rdi, [rdi+2*rsi]
        sub     rsp, 32

mlkem_rej_uniform_alt_loop:
        cmp     rcx, 24
        jb      mlkem_rej_uniform_alt_end
        cmp     rsi, 256
        jae     mlkem_rej_uniform_alt_end
        sub     rcx, 24

// The 16 fields, those < 3329, and the masks m0 (r9) and m1 (r10)
// of the two lanes, with their popcounts c0 (r11) and c1 (rax)

        vmovdqu xmm0, [rdx]
        vinserti128 ymm0, ymm0, XMMWORD PTR [rdx+8], 1
        add     rdx, 24
        vpshufb ymm0, ymm0, ymm6
        vpsrlw  ymm1, ymm0, 4
        vpand   ymm0, ymm0, ymm5
        vpblendw ymm0, ymm0, ymm1, 0xaa
        vpcmpgtw ymm2, ymm3, ymm0
        vpsrlw  ymm2, ymm2, 8
        vpackuswb ymm2, ymm2, ymm2
        vpmovmskb eax, ymm2
        movzx   r9d, al
        shr     eax, 16
        movzx   r10d, al
        xor     r11d, r11d
        popcnt  r11d, r9d
        xor     eax, eax
        popcnt  eax, r10d

// Compact each lane with its table entry

        shl     r9d, 4
        shl     r10d, 4
        vmovdqu xmm4, [r8+r9]
        vinserti128 ymm4, ymm4, XMMWORD PTR [r8+r10], 1
        vpshufb ymm0, ymm0, ymm4

// Directly to r while there is room for 16 more entries

        cmp     rsi, 240
        ja      mlkem_rej_uniform_alt_last
        vmovdqu [rdi], xmm0
        vextracti128 [rdi+2*r11], ymm0, 1
        add     r11, rax
        lea     rdi, [rdi+2*r11]
        add     rsi, r11
        jmp     mlkem_rej_uniform_alt_loop

// Otherwise through the stack, copying min(c0 + c1, 256 - n) entries

mlkem_rej_uniform_alt_last:
        vmovdqu [rsp], xmm0
        vextracti128 [rsp+2*r11], ymm0, 1
        add     r11, rax
        mov     eax, 256
        sub     rax, rsi
        cmp     r11, rax
        cmova   r11, rax
        add     rsi, r11
        xor     r9d, r9d
        test    r11, r11
        jz      mlkem_rej_uniform_alt_loop
mlkem_rej_uniform_alt_copy:
        movzx   eax, WORD PTR [rsp+2*r9]
        mov     [rdi], ax
        add     rdi, 2
        inc     r9
        cmp     r9, r11
        jb      mlkem_rej_uniform_alt_copy
        jmp     mlkem_rej_uniform_alt_loop

mlkem_rej_uniform_alt_end:
        add     rsp, 32
        mov     rax, rsi

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(xmm6,0)
        CFI_STACKLOADU(xmm7,16)
        CFI_STACKLOAD(rdi,32)
        CFI_STACKLOAD(rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

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

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME):
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
        movq    %r8, %rdx
        movq    %r9, %rcx
        movq    88(%rsp), %r8
#endif

// %ymm3 = 3329 in each word, %ymm5 = 0x0fff in each word, %ymm6 = the
// byte pairs of the fields (lane 1 from 4 bytes in); %rdi points at
// r[n], and there are 32 bytes on the stack for the last steps

        movl    $0xd010d01, %eax
        vmovd   %eax, %xmm3
        vpbroadcastd %xmm3, %ymm3
        movl    $0xfff0fff, %eax
        vmovd   %eax, %xmm5
        vpbroadcastd %xmm5, %ymm5
        movabsq $0x0504040302010100, %rax
        vmovq   %rax, %xmm6
        movabsq $0x0b0a0a0908070706, %rax
        vpinsrq $1, %rax, %xmm6, %xmm6
        movabsq $0x0908080706050504, %rax
        vmovq   %rax, %xmm7
        movabsq $0x0f0e0e0d0c0b0b0a, %rax
        vpinsrq $1, %rax, %xmm7, %xmm7
        vinserti128 $1, %xmm7, %ymm6, %ymm6
        leaq    (%rdi,%rsi,2), %rdi
        subq    $32, %rsp

mlkem_rej_uniform_alt_loop:
        cmpq    $24, %rcx
        jb      mlkem_rej_uniform_alt_end
        cmpq    $256, %rsi
        jae     mlkem_rej_uniform_alt_end
        subq    $24, %rcx

// The 16 fields, those < 3329, and the masks m0 (%r9) and m1 (%r10)
// of the two lanes, with their popcounts c0 (%r11) and c1 (%rax)

        vmovdqu (%rdx), %xmm0
        vinserti128 $1,  8(%rdx), %ymm0, %ymm0
        addq    $24, %rdx
        vpshufb %ymm6, %ymm0, %ymm0
        vpsrlw  $4, %ymm0, %ymm1
        vpand   %ymm5, %ymm0, %ymm0
        vpblendw $0xaa, %ymm1, %ymm0, %ymm0
        vpcmpgtw %ymm0, %ymm3, %ymm2
        vpsrlw  $8, %ymm2, %ymm2
        vpackuswb %ymm2, %ymm2, %ymm2
        vpmovmskb %ymm2, %eax
        movzx   %al, %r9d
        shrl    $16, %eax
        movzx   %al, %r10d
        xorl    %r11d, %r11d
        popcnt  %r9d, %r11d
        xorl    %eax, %eax
        popcnt  %r10d, %eax

// Compact each lane with its table entry

        shll    $4, %r9d
        shll    $4, %r10d
        vmovdqu (%r8,%r9), %xmm4
        vinserti128 $1,  (%r8,%r10), %ymm4, %ymm4
        vpshufb %ymm4, %ymm0, %ymm0

// Directly to r while there is room for 16 more entries

        cmpq    $240, %rsi
        ja      mlkem_rej_uniform_alt_last
        vmovdqu %xmm0, (%rdi)
        vextracti128 $1, %ymm0, (%rdi,%r11,2)
        addq    %rax, %r11
        leaq    (%rdi,%r11,2), %rdi
        addq    %r11, %rsi
        jmp     mlkem_rej_uniform_alt_loop

// Otherwise through the stack, copying min(c0 + c1, 256 - n) entries

mlkem_rej_uniform_alt_last:
        vmovdqu %xmm0, (%rsp)
        vextracti128 $1, %ymm0, (%rsp,%r11,2)
        addq    %rax, %r11
        movl    $256, %eax
        subq    %rsi, %rax
        cmpq    %rax, %r11
        cmova   %rax, %r11
        addq    %r11, %rsi
        xorl    %r9d, %r9d
        testq   %r11, %r11
        jz      mlkem_rej_uniform_alt_loop
mlkem_rej_uniform_alt_copy:
        movzwl (%rsp,%r9,2), %eax
        movw    %ax, (%rdi)
        addq    $2, %rdi
        incq    %r9
        cmpq    %r11, %r9
        jb      mlkem_rej_uniform_alt_copy
        jmp     mlkem_rej_uniform_alt_loop

mlkem_rej_uniform_alt_end:
        addq    $32, %rsp
        movq    %rsi, %rax

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOAD(%rdi,32)
        CFI_STACKLOAD(%rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_sqr_p521(uint64_t z[static 9], const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sqr_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sqr_p521)
        .text

#define z %rdi
#define x %rsi

// A zero register

#define zero %rbp
#define zeroe %ebp

// mulpadd(high,low,i) adds %rdx * x[i] to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using %rax and %rcx as temporaries.

#define mulpadd(high,low,I)             \
        mulxq   I(x), %rax, %rcx ;        \
        adcxq   %rax, low ;               \
        adoxq   %rcx, high

// mulpade(high,low,i) adds %rdx * x[i] to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using %rax as a temporary, assuming high created from scratch
// and that zero has value zero.

#define mulpade(high,low,I)             \
        mulxq   I(x), %rax, high ;       \
        adcxq   %rax, low ;               \
        adoxq   zero, high

S2N_BN_SYMBOL(bignum_sqr_p521):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Save more registers to play with and make temporary space on stack

        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        subq    $64, %rsp

// Do a basic 8x8 squaring stashing in %rsp[0..7] but keeping the
// top half in the usual rotating register window %r15,...,%r8. Except
// for the lack of full writeback this is the same as bignum_sqr_8_16.

        xorl    zeroe, zeroe

        movq    (x), %rdx
        mulxq   8(x), %r9, %rax
        movq    %r9, 8(%rsp)
        mulxq   16(x), %r10, %rcx
        adcxq   %rax, %r10
        movq    %r10, 16(%rsp)
        mulxq   24(x), %r11, %rax
        adcxq   %rcx, %r11
        mulxq   32(x), %r12, %rcx
        adcxq   %rax, %r12
        mulxq   40(x), %r13, %rax
        adcxq   %rcx, %r13
        mulxq   48(x), %r14, %rcx
        adcxq   %rax, %r14
        mulxq   56(x), %r15, %r8
        adcxq   %rcx, %r15
        adcxq   zero, %r8

        xorl    zeroe, zeroe
        movq    8(x), %rdx
        mulpadd(%r12,%r11,16)
        movq    %r11, 24(%rsp)
        mulpadd(%r13,%r12,24)
        movq    %r12, 32(%rsp)
        mulpadd(%r14,%r13,32)
        mulpadd(%r15,%r14,40)
        mulpadd(%r8,%r15,48)
        mulpade(%r9,%r8,56)
        movq    32(x), %rdx
        mulpade(%r10,%r9,40)
        adcxq   zero, %r10

        xorl    zeroe, zeroe
        movq    16(x), %rdx
        mulpadd(%r14,%r13,24)
        movq    %r13, 40(%rsp)
        mulpadd(%r15,%r14,32)
        movq    %r14, 48(%rsp)
        mulpadd(%r8,%r15,40)
        mulpadd(%r9,%r8,48)
        mulpadd(%r10,%r9,56)
        movq    48(x), %rdx
        mulpade(%r11,%r10,32)
        mulpade(%r12,%r11,40)
        adcxq   zero, %r12

        xorl    zeroe, zeroe
        movq    24(x), %rdx
        mulpadd(%r8,%r15,32)
        movq    %r15, 56(%rsp)
        mulpadd(%r9,%r8,40)
        mulpadd(%r10,%r9,48)
        mulpadd(%r11,%r10,56)
        movq    56(x), %rdx
        mulpadd(%r12,%r11,32)
        mulpade(%r13,%r12,40)
        mulpade(%r14,%r13,48)
        adcxq   zero, %r14

        xorl    zeroe, zeroe
        movq    (x), %rdx
        mulxq   %rdx, %rax, %rcx
        movq    %rax, (%rsp)
        movq    8(%rsp), %rax
        adcxq   %rax, %rax
        adoxq   %rcx, %rax
        movq    %rax, 8(%rsp)

        movq    16(%rsp), %rax
        movq    8(x), %rdx
        mulxq   %rdx, %rdx, %rcx
        adcxq   %rax, %rax
        adoxq   %rdx, %rax
        movq    %rax, 16(%rsp)
        movq    24(%rsp), %rax
        adcxq   %rax, %rax
        adoxq   %rcx, %rax
        movq    %rax, 24(%rsp)

        movq    32(%rsp), %rax
        movq    16(x), %rdx
        mulxq   %rdx, %rdx, %rcx
        adcxq   %rax, %rax
        adoxq   %rdx, %rax
        movq    %rax, 32(%rsp)
        movq    40(%rsp), %rax
        adcxq   %rax, %rax
        adoxq   %rcx, %rax
        movq    %rax, 40(%rsp)

        movq    48(%rsp), %rax
        movq    24(x), %rdx
        mulxq   %rdx, %rdx, %rcx
        adcxq   %rax, %rax
        adoxq   %rdx, %rax
        movq    %rax, 48(%rsp)
        movq    56(%rsp), %rax
        adcxq   %rax, %rax
        adoxq   %rcx, %rax
        movq    %rax, 56(%rsp)

        movq    32(x), %rdx
        mulxq   %rdx, %rdx, %rcx
        adcxq   %r8, %r8
        adoxq   %rdx, %r8
        adcxq   %r9, %r9
        adoxq   %rcx, %r9

        movq    40(x), %rdx
        mulxq   %rdx, %rdx, %rcx
        adcxq   %r10, %r10
        adoxq   %rdx, %r10
        adcxq   %r11, %r11
        adoxq   %rcx, %r11

        movq    48(x), %rdx
        mulxq   %rdx, %rdx, %rcx
        adcxq   %r12, %r12
        adoxq   %rdx, %r12
        adcxq   %r13, %r13
        adoxq   %rcx, %r13

        movq    56(x), %rdx
        mulxq   %rdx, %rdx, %r15
        adcxq   %r14, %r14
        adoxq   %rdx, %r14
        adcxq   zero, %r15
        adoxq   zero, %r15

// Augment the high part with the contribution from the top little word C.
// If we write the input as 2^512 * C + x then we are otherwise just doing
// x^2, so we need to add to the high part 2^512 * C^2 + (2 * C) * x.
// The initial doubling add of C also clears the CF and OF flags as desired.
// We extend the window now to the 9-element %rbp,%r15,%r14,...,%r8.

        movq    64(x), %rdx
        movq    %rdx, %rbp
        imulq   %rbp, %rbp
        addq    %rdx, %rdx
        mulpadd(%r9,%r8,0)
        mulpadd(%r10,%r9,8)
        mulpadd(%r11,%r10,16)
        mulpadd(%r12,%r11,24)
        mulpadd(%r13,%r12,32)
        mulpadd(%r14,%r13,40)
        mulpadd(%r15,%r14,48)
        mulxq  56(x), %rax, %rcx
        adcxq  %rax, %r15
        adoxq  %rcx, %rbp
        adcq   $0, %rbp

// Rotate the upper portion right 9 bits since 2^512 == 2^-9 (mod p_521)
// Let rotated result %rbp,%r15,%r14,...,%r8 be h (high) and %rsp[0..7] be l (low)

        movq    %r8, %rax
        andq    $0x1FF, %rax
        shrdq   $9, %r9, %r8
        shrdq   $9, %r10, %r9
        shrdq   $9, %r11, %r10
        shrdq   $9, %r12, %r11
        shrdq   $9, %r13, %r12
        shrdq   $9, %r14, %r13
        shrdq   $9, %r15, %r14
        shrdq   $9, %rbp, %r15
        shrq    $9, %rbp
        addq    %rax, %rbp

// Force carry-in then add to get s = h + l + 1
// but actually add all 1s in the top 53 bits to get simple carry out

        stc
        adcq    (%rsp), %r8
        adcq    8(%rsp), %r9
        adcq    16(%rsp), %r10
        adcq    24(%rsp), %r11
        adcq    32(%rsp), %r12
        adcq    40(%rsp), %r13
        adcq    48(%rsp), %r14
        adcq    56(%rsp), %r15
        adcq    $~0x1FF, %rbp

// Now CF is set <=> h + l + 1 >= 2^521 <=> h + l >= p_521,
// in which case the lower 521 bits are already right. Otherwise if
// CF is clear, we want to subtract 1. Hence subtract the complement
// of the carry flag then mask the top word, which scrubs the
// padding in either case. Write digits back as they are created.

        cmc
        sbbq    $0, %r8
        movq    %r8, (z)
        sbbq    $0, %r9
        movq    %r9, 8(z)
        sbbq    $0, %r10
        movq    %r10, 16(z)
        sbbq    $0, %r11
        movq    %r11, 24(z)
        sbbq    $0, %r12
        movq    %r12, 32(z)
        sbbq    $0, %r13
        movq    %r13, 40(z)
        sbbq    $0, %r14
        movq    %r14, 48(z)
        sbbq    $0, %r15
        movq    %r15, 56(z)
        sbbq    $0, %rbp
        andq    $0x1FF, %rbp
        movq    %rbp, 64(z)

// Restore registers and return

        addq    $64, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbp

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

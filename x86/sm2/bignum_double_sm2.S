// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Double modulo p_sm2, z := (2 * x) mod p_sm2, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_double_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_double_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_double_sm2)
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9

#define n1 r10
#define n3 r11
#define c rax

#define n1short r10d

S2N_BN_SYMBOL(bignum_double_sm2):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the input and double it so that 2^256 * c + [d3;d2;d1;d0] = 2 * x
// Could also consider using shld to decouple carries

        xor     c, c
        mov     d0, [x]
        add     d0, d0
        mov     d1, [x+8]
        adc     d1, d1
        mov     d2, [x+16]
        adc     d2, d2
        mov     d3, [x+24]
        adc     d3, d3
        adc     c, c

// Now subtract 2^256 * c + [d3;d3;d1;d1] = 2 * x - p_sm2
// The constants n1 and n3 in [n3; -1; n1; -1] = p_sm2 are saved for later

        sub     d0, -1
        mov     n1, 0xffffffff00000000
        sbb     d1, n1
        sbb     d2, -1
        mov     n3, 0xfffffffeffffffff
        sbb     d3, n3

// Since by hypothesis x < p_sm2 we know 2 * x - p_sm2 < 2^256, so the top
// carry c actually gives us a bitmask for 2 * x - p_sm2 < 0, which we
// now use to make a masked p_sm2' = [n3; c; n1; c]

        sbb     c, 0
        and     n1, c
        and     n3, c

// Do the corrective addition and copy to output

        add     d0, c
        mov     [z], d0
        adc     d1, n1
        mov     [z+8], d1
        adc     d2, c
        mov     [z+16], d2
        adc     d3, n3
        mov     [z+24], d3

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

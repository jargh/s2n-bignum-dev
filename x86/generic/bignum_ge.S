// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x >= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_ge(uint64_t m, const uint64_t *x, uint64_t n,
//                              const uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = x, R8 = n, R9 = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ge)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ge)
        .text

#define m rdi
#define x rsi
#define n rdx
#define y rcx
#define i r8
#define a rax

#define ashort eax



S2N_BN_SYMBOL(bignum_ge):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Zero the main index counter for both branches

        xor     i, i

// Speculatively form m := m - n and do case split

        sub     m, n
        jc      bignum_ge_ylonger

// The case where x is longer or of the same size (m >= n)

        inc     m
        test    n, n
        jz      bignum_ge_xtest
bignum_ge_xmainloop:
        mov     a, [x+8*i]
        sbb     a, [y+8*i]
        inc     i
        dec     n
        jnz     bignum_ge_xmainloop
        jmp     bignum_ge_xtest
bignum_ge_xtoploop:
        mov     a, [x+8*i]
        sbb     a, 0
        inc     i
bignum_ge_xtest:
        dec     m
        jnz     bignum_ge_xtoploop
        sbb     a, a
        inc     a
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

// The case where y is longer (n > m)

bignum_ge_ylonger:
        add     m, n
        sub     n, m
        test    m, m
        jz      bignum_ge_ytoploop
bignum_ge_ymainloop:
        mov     a, [x+8*i]
        sbb     a, [y+8*i]
        inc     i
        dec     m
        jnz     bignum_ge_ymainloop
bignum_ge_ytoploop:
        mov     ashort, 0
        sbb     a, [y+8*i]
        inc     i
        dec     n
        jnz     bignum_ge_ytoploop

        sbb     a, a
        inc     a
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

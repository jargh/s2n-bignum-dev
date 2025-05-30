// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x > y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_gt(uint64_t m, const uint64_t *x, uint64_t n,
//                              const uint64_t *y);
//
// Standard ARM ABI: X0 = m, X1 = x, X2 = n, X3 = y, returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_gt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_gt)
        .text
        .balign 4

#define m x0
#define x x1
#define n x2
#define y x3
#define i x4
#define a x5
#define d x6


S2N_BN_SYMBOL(bignum_gt):

// Zero the main index counter for both branches

        mov     i, xzr

// Speculatively form n := n - m and do case split

        subs    n, n, m
        bcc     bignum_gt_ylonger

// The case where y is longer or of the same size (n >= m)
// Note that CF=1 initially by the fact that we reach this point

        cbz     m, bignum_gt_xtest
bignum_gt_xmainloop:
        ldr     a, [y, i, lsl #3]
        ldr     d, [x, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_gt_xmainloop
bignum_gt_xtest:
        cbz     n, bignum_gt_xskip
bignum_gt_xtoploop:
        ldr     a, [y, i, lsl #3]
        sbcs    xzr, a, xzr
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_gt_xtoploop
bignum_gt_xskip:
        cset    x0, cc
        ret

// The case where x is longer (m > n)
// The first "adds" also makes sure CF=1 initially in this branch

bignum_gt_ylonger:
        adds    n, n, m
        cbz     n, bignum_gt_ytoploop
        sub     m, m, n
bignum_gt_ymainloop:
        ldr     a, [y, i, lsl #3]
        ldr     d, [x, i, lsl #3]
        sbcs    xzr, a, d
        add     i, i, #1
        sub     n, n, #1
        cbnz    n, bignum_gt_ymainloop
bignum_gt_ytoploop:
        ldr     a, [x, i, lsl #3]
        sbcs    xzr, xzr, a
        add     i, i, #1
        sub     m, m, #1
        cbnz    m, bignum_gt_ytoploop

        cset    x0, cc
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

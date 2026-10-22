// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Uniform random integer below a bound from a buffer of random words
// Inputs s, x[n]; output z[1] and function return
//
//    extern uint64_t lemire_random_VARIABLE_TIME
//      (uint64_t z[S2N_BIGNUM_STATIC 1], uint64_t s, uint64_t n,
//       const uint64_t *x);
//
// This uses Lemire's "nearly divisionless" method (Daniel Lemire, "Fast
// Random Integer Generation in an Interval", ACM Transactions on Modeling
// and Computer Simulation 29(1), 2019) to turn uniformly distributed
// 64-bit words x[0], x[1], ... into a uniformly distributed integer in
// the range 0 <= *z < s, where s is assumed nonzero. Each word x[i] is
// tried in turn by forming the 128-bit product x[i] * s. If its low half
// l satisfies l >= 2^64 mod s then the word is accepted and *z is set to
// the high half, otherwise the word is rejected and the next one tried.
// The threshold 2^64 mod s is only computed, using a division, in the
// case l < s, which for a uniformly distributed word happens only with
// probability s / 2^64. On success the return value is the number k of
// words consumed, with 1 <= k <= n. If all n words are rejected then the
// return value is 0 and *z is not written.
//
// This is *not* a constant-time function: the time taken depends on how
// many words are rejected and on whether the division is needed.
//
// Standard ARM ABI: X0 = z, X1 = s, X2 = n, X3 = x, returns X0
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(lemire_random_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(lemire_random_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(lemire_random_VARIABLE_TIME)
        .text
        .balign 4

#define z x0
#define s x1
#define n x2
#define x x3

#define a x4
#define l x5
#define h x6
#define k x7
#define t x8
#define q x9

S2N_BN_SYMBOL(lemire_random_VARIABLE_TIME):
        CFI_START

// If n = 0 there are no words to try, so return 0 at once.

        cbz     n, Llemire_random_VARIABLE_TIME_fail

// Form h:l = x[0] * s and set k = 1, the number of words consumed.
// If l >= s then a fortiori l >= 2^64 mod s so the word is accepted
// without needing to compute that threshold.

        ldr     a, [x]
        mul     l, a, s
        umulh   h, a, s
        mov     k, #1
        cmp     l, s
        bcs     Llemire_random_VARIABLE_TIME_accept

// Compute the threshold t = 2^64 mod s as (2^64 - s) mod s. Here s > l >= 0
// so s is nonzero (though in any case UDIV by zero would not trap on Arm).

        neg     t, s
        udiv    q, t, s
        msub    t, q, s, t

// Main loop, with h:l = x[k-1] * s and x[0], ..., x[k-2] all rejected.
// If l >= t then x[k-1] is accepted. Otherwise fail if all n words are
// already used, or else try x[k].

Llemire_random_VARIABLE_TIME_loop:
        cmp     l, t
        bcs     Llemire_random_VARIABLE_TIME_accept
        cmp     k, n
        bcs     Llemire_random_VARIABLE_TIME_fail
        ldr     a, [x, k, lsl #3]
        add     k, k, #1
        mul     l, a, s
        umulh   h, a, s
        b       Llemire_random_VARIABLE_TIME_loop

Llemire_random_VARIABLE_TIME_fail:
        mov     k, xzr
        b       Llemire_random_VARIABLE_TIME_end

// Accept x[k-1]: write the high half of the product and return k

Llemire_random_VARIABLE_TIME_accept:
        str     h, [z]

Llemire_random_VARIABLE_TIME_end:
        mov     x0, k
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(lemire_random_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

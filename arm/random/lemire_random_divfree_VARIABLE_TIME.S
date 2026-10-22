// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Uniform random integer below a bound from a buffer of random words,
// without using any division instruction
// Inputs s, x[n]; output z[1] and function return
//
//    extern uint64_t lemire_random_divfree_VARIABLE_TIME
//      (uint64_t z[S2N_BIGNUM_STATIC 1], uint64_t s, uint64_t n,
//       const uint64_t *x);
//
// This has the same specification as lemire_random_VARIABLE_TIME and uses
// the same "nearly divisionless" method (Daniel Lemire, "Fast Random Integer
// Generation in an Interval", ACM Transactions on Modeling and Computer
// Simulation 29(1), 2019) to turn uniformly distributed 64-bit words x[0],
// x[1], ... into a uniformly distributed integer in the range 0 <= *z < s,
// where s is assumed nonzero. Each word x[i] is tried in turn by forming the
// 128-bit product x[i] * s. If its low half l satisfies l >= 2^64 mod s then
// the word is accepted and *z is set to the high half, otherwise the word is
// rejected and the next one tried. The threshold 2^64 mod s is only computed
// in the case l < s, which for a uniformly distributed word happens only
// with probability s / 2^64. On success the return value is the number k of
// words consumed, with 1 <= k <= n. If all n words are rejected then the
// return value is 0 and *z is not written.
//
// The difference is that here the threshold is computed without division,
// from a reciprocal approximation obtained by Newton iteration (using
// exactly the code of word_recip) followed by a single correction, which is
// a fixed sequence of operations independent of s. This is still *not* a
// constant-time function, since the time taken depends on how many words
// are rejected and on whether the threshold is needed at all, but that is
// the only variation.
//
// Standard ARM ABI: X0 = z, X1 = s, X2 = n, X3 = x, returns X0
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)
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

// Copies of s, n and x kept while computing the threshold, since the
// reciprocal code uses x0, ..., x4. The main loop then uses these copies.
// Similarly z is saved in zz and later restored, and c holds clz(s).

#define zz x9
#define ss x10
#define nn x11
#define xx x12
#define c x13

S2N_BN_SYMBOL(lemire_random_divfree_VARIABLE_TIME):
        CFI_START

// If n = 0 there are no words to try, so return 0 at once.

        cbz     n, Llemire_random_divfree_VARIABLE_TIME_fail

// Form h:l = x[0] * s and set k = 1, the number of words consumed.
// If l >= s then a fortiori l >= 2^64 mod s so the word is accepted
// without needing to compute that threshold.

        ldr     a, [x]
        mul     l, a, s
        umulh   h, a, s
        mov     k, #1
        cmp     l, s
        bcs     Llemire_random_divfree_VARIABLE_TIME_accept

// Otherwise we need the threshold. Save z, s, n and x, and normalize s,
// which is nonzero here since s > l >= 0, by shifting it left c = clz(s)
// places to get x0 = d = 2^c * s with 2^63 <= d < 2^64.

        mov     zz, z
        mov     ss, s
        mov     nn, n
        mov     xx, x

        clz     c, s
        lsl     x0, s, c

// Compute the reciprocal 2^64 + x0 = ceil(2^128 / d) - 1 of d = x0.
// This is exactly the code of word_recip (except for its final return),
// which modifies x0, ..., x4, and it is used here verbatim so that its
// correctness proof applies.

        lsr     x2, x0, #16
        eor     x1, x2, #0x1FFFFFFFFFFFF
        add     x2, x2, #1
        lsr     x1, x1, #32
        msub    x4, x2, x1, xzr
        lsr     x3, x4, #49
        mul     x3, x3, x3
        lsr     x4, x4, #34
        add     x4, x3, x4
        orr     x3, x3, #0x40000000
        mul     x3, x4, x3
        lsr     x3, x3, #30
        lsl     x4, x1, #30
        madd    x1, x1, x3, x4
        lsr     x1, x1, #30
        msub    x4, x2, x1, xzr
        lsr     x4, x4, #24
        mul     x4, x4, x1
        lsl     x1, x1, #16
        lsr     x4, x4, #24
        add     x1, x1, x4
        msub    x4, x2, x1, xzr
        lsr     x4, x4, #32
        mul     x4, x4, x1
        lsl     x1, x1, #31
        lsr     x4, x4, #17
        add     x1, x1, x4
        mul     x3, x0, x1
        umulh   x4, x0, x1
        extr    x3, x4, x3, #60
        lsr     x4, x1, #33
        mvn     x3, x3
        mul     x3, x4, x3
        lsl     x1, x1, #1
        lsr     x3, x3, #33
        add     x1, x1, x3
        adds    x3, x1, #1
        cinv    x3, x3, eq
        umulh   x4, x0, x3
        adds    x4, x4, x0
        csel    x0, x1, x3, cs

// Get q = floor((2^64 + x0) / 2^(64 - c)), either floor(2^64 / s) or one
// less, by a right shift of 1 that brings in the implicit 1 bit, followed
// by a right shift of 63 - c places, that count being c XOR 63.

        eor     c, c, #63
        lsr     x0, x0, #1
        orr     x0, x0, #0x8000000000000000
        lsr     x0, x0, c

// Now t' = 2^64 - q * s satisfies 1 <= t' <= s and is congruent to 2^64
// modulo s, so the threshold is t = t' - s if t' >= s, otherwise t = t'.

        mneg    t, x0, ss
        subs    a, t, ss
        csel    t, a, t, cs

// Restore z, with the product x[0] * s and k = 1 still intact

        mov     z, zz

// Main loop, with h:l = x[k-1] * s and x[0], ..., x[k-2] all rejected.
// If l >= t then x[k-1] is accepted. Otherwise fail if all n words are
// already used, or else try x[k].

Llemire_random_divfree_VARIABLE_TIME_loop:
        cmp     l, t
        bcs     Llemire_random_divfree_VARIABLE_TIME_accept
        cmp     k, nn
        bcs     Llemire_random_divfree_VARIABLE_TIME_fail
        ldr     a, [xx, k, lsl #3]
        add     k, k, #1
        mul     l, a, ss
        umulh   h, a, ss
        b       Llemire_random_divfree_VARIABLE_TIME_loop

Llemire_random_divfree_VARIABLE_TIME_fail:
        mov     k, xzr
        b       Llemire_random_divfree_VARIABLE_TIME_end

// Accept x[k-1]: write the high half of the product and return k

Llemire_random_divfree_VARIABLE_TIME_accept:
        str     h, [z]

Llemire_random_divfree_VARIABLE_TIME_end:
        mov     x0, k
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

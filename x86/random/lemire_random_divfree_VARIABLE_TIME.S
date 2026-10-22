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
// Standard x86-64 ABI: RDI = z, RSI = s, RDX = n, RCX = x, returns RAX
// Microsoft x64 ABI:   RCX = z, RDX = s, R8 = n, R9 = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)
        .text

#define z rdi
#define s rsi
#define x rcx

#define n r8
#define k r10

// Copies of x, z and s kept while computing the threshold, since the
// reciprocal code uses rdi as its input and modifies rax, rcx, rdx and rsi.
// The main loop then uses the copies xx and ss, and t for the threshold.

#define xx r9
#define zz r10
#define ss r11

#define t rsi

S2N_BN_SYMBOL(lemire_random_divfree_VARIABLE_TIME):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Move n out of rdx, which is used by the multiplications. If n = 0 there
// are no words to try, so return 0 at once.

        mov     n, rdx
        xor     eax, eax
        test    n, n
        jz      Llemire_random_divfree_VARIABLE_TIME_end

// Form rdx:rax = x[0] * s and set k = 1, the number of words consumed.
// If the low half l = rax satisfies l >= s then a fortiori l >= 2^64 mod s
// so the word is accepted without needing to compute that threshold.

        mov     rax, [x]
        mul     s
        mov     k, 1
        cmp     rax, s
        jnc     Llemire_random_divfree_VARIABLE_TIME_accept

// Otherwise we need the threshold. Save x, z and s, and normalize s, which
// is nonzero here since s > l >= 0, by shifting it left c = clz(s) places
// to get d = 2^c * s with 2^63 <= d < 2^64. This uses bsr, which gives
// 63 - c, rather than lzcnt, to stay within the base x86-64 instruction set.

        mov     xx, x
        mov     zz, z
        mov     ss, s

        bsr     rcx, s
        xor     rcx, 63
        mov     rdi, s
        shl     rdi, cl

// Compute the reciprocal 2^64 + rax = ceil(2^128 / d) - 1 of d = rdi.
// This is exactly the code of word_recip, which modifies rax, rcx, rdx and
// rsi, and it is used here verbatim so that its correctness proof applies.

        mov     rsi, rdi
        mov     rcx, 0x1FFFFFFFFFFFF
        shr     rsi, 16
        xor     rcx, rsi
        inc     rsi
        shr     rcx, 32
        mov     rdx, rsi
        imul    rdx, rcx
        neg     rdx
        mov     rax, rdx
        shr     rax, 49
        imul    rax, rax
        shr     rdx, 34
        add     rdx, rax
        or      rax, 0x40000000
        imul    rax, rdx
        shr     rax, 30
        imul    rax, rcx
        shl     rcx, 30
        add     rcx, rax
        shr     rcx, 30
        mov     rdx, rsi
        imul    rdx, rcx
        neg     rdx
        shr     rdx, 24
        imul    rdx, rcx
        shl     rcx, 16
        shr     rdx, 24
        add     rcx, rdx
        mov     rdx, rsi
        imul    rdx, rcx
        neg     rdx
        shr     rdx, 32
        imul    rdx, rcx
        shl     rcx, 31
        shr     rdx, 17
        add     rcx, rdx
        mov     rax, rdi
        mul     rcx
        shrd    rax, rdx, 60
        mov     rdx, rcx
        shr     rdx, 33
        not     rax
        imul    rax, rdx
        shl     rcx, 1
        shr     rax, 33
        add     rcx, rax
        add     rcx, 1
        mov     rax, rdi
        sbb     rcx, 0
        mul     rcx
        mov     rax, rcx
        add     rdx, rdi
        sbb     rax, 0

// Get q = floor((2^64 + rax) / 2^(64 - c)), either floor(2^64 / s) or one
// less, by a right shift of 1 that brings in the implicit 1 bit, followed
// by a right shift of 63 - c places, that count being recomputed by bsr.

        bsr     rcx, ss
        mov     edx, 1
        shrd    rax, rdx, 1
        shr     rax, cl

// Now t' = 2^64 - q * s satisfies 1 <= t' <= s and is congruent to 2^64
// modulo s, so the threshold is t = t' - s if t' >= s, otherwise t = t'.

        imul    rax, ss
        neg     rax
        mov     t, rax
        sub     t, ss
        cmovc   t, rax

// Restore z, recompute rdx:rax = x[0] * s and reset k = 1

        mov     z, zz
        mov     rax, [xx]
        mul     ss
        mov     k, 1

// Main loop, with rdx:rax = x[k-1] * s and x[0], ..., x[k-2] all rejected.
// If the low half l = rax satisfies l >= t then x[k-1] is accepted.
// Otherwise fail if all n words are already used, or else try x[k].

Llemire_random_divfree_VARIABLE_TIME_loop:
        cmp     rax, t
        jnc     Llemire_random_divfree_VARIABLE_TIME_accept
        cmp     k, n
        jnc     Llemire_random_divfree_VARIABLE_TIME_fail
        mov     rax, [xx+8*k]
        add     k, 1
        mul     ss
        jmp     Llemire_random_divfree_VARIABLE_TIME_loop

Llemire_random_divfree_VARIABLE_TIME_fail:
        xor     eax, eax
        jmp     Llemire_random_divfree_VARIABLE_TIME_end

// Accept x[k-1]: write the high half of the product and return k

Llemire_random_divfree_VARIABLE_TIME_accept:
        mov     [z], rdx
        mov     rax, k

Llemire_random_divfree_VARIABLE_TIME_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(lemire_random_divfree_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

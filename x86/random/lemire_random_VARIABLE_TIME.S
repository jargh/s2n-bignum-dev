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
// Standard x86-64 ABI: RDI = z, RSI = s, RDX = n, RCX = x, returns RAX
// Microsoft x64 ABI:   RCX = z, RDX = s, R8 = n, R9 = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(lemire_random_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(lemire_random_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(lemire_random_VARIABLE_TIME)
        .text

#define z rdi
#define s rsi
#define x rcx

#define n r8
#define h r9
#define k r10
#define t r11

S2N_BN_SYMBOL(lemire_random_VARIABLE_TIME):
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
        jz      Llemire_random_VARIABLE_TIME_end

// Form rdx:rax = x[0] * s and set k = 1, the number of words consumed.
// If the low half l = rax satisfies l >= s then a fortiori l >= 2^64 mod s
// so the word is accepted without needing to compute that threshold.

        mov     rax, [x]
        mul     s
        mov     k, 1
        cmp     rax, s
        jnc     Llemire_random_VARIABLE_TIME_accept

// Compute the threshold t = 2^64 mod s as (2^64 - s) mod s, the remainder
// of 0:(2^64 - s) divided by s. This cannot raise a #DE exception since
// here s > l >= 0 so s is nonzero, and the high half of the dividend is 0.

        mov     h, rdx
        mov     t, rax
        mov     rax, s
        neg     rax
        xor     edx, edx
        div     s
        mov     rax, t
        mov     t, rdx
        mov     rdx, h

// Main loop, with rdx:rax = x[k-1] * s and x[0], ..., x[k-2] all rejected.
// If the low half l = rax satisfies l >= t then x[k-1] is accepted.
// Otherwise fail if all n words are already used, or else try x[k].

Llemire_random_VARIABLE_TIME_loop:
        cmp     rax, t
        jnc     Llemire_random_VARIABLE_TIME_accept
        cmp     k, n
        jnc     Llemire_random_VARIABLE_TIME_fail
        mov     rax, [x+8*k]
        add     k, 1
        mul     s
        jmp     Llemire_random_VARIABLE_TIME_loop

Llemire_random_VARIABLE_TIME_fail:
        xor     eax, eax
        jmp     Llemire_random_VARIABLE_TIME_end

// Accept x[k-1]: write the high half of the product and return k

Llemire_random_VARIABLE_TIME_accept:
        mov     [z], rdx
        mov     rax, k

Llemire_random_VARIABLE_TIME_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(lemire_random_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

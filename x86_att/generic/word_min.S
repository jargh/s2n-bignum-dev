// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Return minimum of two unsigned 64-bit words
// Inputs a, b; output function return
//
//    extern uint64_t word_min(uint64_t a, uint64_t b);
//
// Standard x86-64 ABI: RDI = a, RSI = b, returns RAX
// Microsoft x64 ABI:   RCX = a, RDX = b, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(word_min)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(word_min)
        .text

#define a %rdi
#define b %rsi

S2N_BN_SYMBOL(word_min):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

        movq    a, %rax
        cmpq    b, a
        cmovncq b, %rax
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

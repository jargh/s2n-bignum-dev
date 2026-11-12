// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Check that bytes encode ML-KEM polynomials with reduced coefficients
// Input a[384*k] (bytes), k; output function return
//
// Returns 1 if each of the 256 * k 12-bit little-endian fields of the
// 384 * k bytes, two to each group of 3 bytes, is less than 3329, and
// 0 otherwise. Thus 1 means that ByteEncode_12(ByteDecode_12(a)) = a for
// each 384-byte polynomial, the modulus check of an encapsulation key in
// FIPS 203 (section 7.2), as done by mlkem-native's mlk_kem_check_pk. The
// time taken depends only on k.
//
// extern uint64_t mlkem_check_encoding(const uint8_t *a, uint64_t k);
//
// Standard x86-64 ABI: RDI = a, RSI = k
// Microsoft x64 ABI:   RCX = a, RDX = k
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_check_encoding)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_check_encoding)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_check_encoding)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_check_encoding):
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
#endif

// %ymm0 = 3328 in each word, %ymm5 = 0x0fff in each word,
// %ymm6 = the byte pairs of the fields (lane 1 from 4 bytes in),
// %ymm4 = the accumulator of fields > 3328

        movl    $0xd000d00, %eax
        vmovd   %eax, %xmm0
        vpbroadcastd %xmm0, %ymm0
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
        vpxor   %ymm4, %ymm4, %ymm4
        testq   %rsi, %rsi
        jz      mlkem_check_encoding_done

mlkem_check_encoding_loop:
        vmovdqu 0(%rdi), %xmm1
        vinserti128 $1,  8(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 24(%rdi), %xmm3
        vinserti128 $1,  32(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        vmovdqu 48(%rdi), %xmm1
        vinserti128 $1,  56(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 72(%rdi), %xmm3
        vinserti128 $1,  80(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        vmovdqu 96(%rdi), %xmm1
        vinserti128 $1,  104(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 120(%rdi), %xmm3
        vinserti128 $1,  128(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        vmovdqu 144(%rdi), %xmm1
        vinserti128 $1,  152(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 168(%rdi), %xmm3
        vinserti128 $1,  176(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        vmovdqu 192(%rdi), %xmm1
        vinserti128 $1,  200(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 216(%rdi), %xmm3
        vinserti128 $1,  224(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        vmovdqu 240(%rdi), %xmm1
        vinserti128 $1,  248(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 264(%rdi), %xmm3
        vinserti128 $1,  272(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        vmovdqu 288(%rdi), %xmm1
        vinserti128 $1,  296(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 312(%rdi), %xmm3
        vinserti128 $1,  320(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        vmovdqu 336(%rdi), %xmm1
        vinserti128 $1,  344(%rdi), %ymm1, %ymm1
        vpshufb %ymm6, %ymm1, %ymm1
        vpsrlw  $4, %ymm1, %ymm2
        vpand   %ymm5, %ymm1, %ymm1
        vpblendw $0xaa, %ymm2, %ymm1, %ymm1
        vpcmpgtw %ymm0, %ymm1, %ymm1
        vpor    %ymm1, %ymm4, %ymm4
        vmovdqu 360(%rdi), %xmm3
        vinserti128 $1,  368(%rdi), %ymm3, %ymm3
        vpshufb %ymm6, %ymm3, %ymm3
        vpsrlw  $4, %ymm3, %ymm7
        vpand   %ymm5, %ymm3, %ymm3
        vpblendw $0xaa, %ymm7, %ymm3, %ymm3
        vpcmpgtw %ymm0, %ymm3, %ymm3
        vpor    %ymm3, %ymm4, %ymm4
        addq    $384, %rdi
        decq    %rsi
        jnz     mlkem_check_encoding_loop

mlkem_check_encoding_done:
        xorl    %eax, %eax
        vptest  %ymm4, %ymm4
        setz    %al

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOADU(%xmm6,0)
        CFI_STACKLOADU(%xmm7,16)
        CFI_STACKLOAD(%rdi,32)
        CFI_STACKLOAD(%rsi,40)
        CFI_INC_RSP(48)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_check_encoding)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

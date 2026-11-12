// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, with AVX-512F
// Input a[25], rc[24]; output a[25]
//
// The input/output argument is a 25-element Keccak array, replaced by its
// Keccak-f1600 permutation with the round constants rc, as by
// sha3_keccak_f1600 (this is the same function, for processors with
// AVX-512F).
//
// The state is in five zmm registers, five lanes (x, y) in the low five
// quadwords of each. The registers hold the sets S(a, c), register r the
// lanes (c r + a y, y) for y = 0..4, with (a, c) = (2, 1), (3, 4) and
// (4, 3) at the start of the three rounds of each group, in one of two
// orders: T, quadword p holding the lane with x = p, in which theta is a
// vertical XOR of the registers, and K, quadword q holding the lane with
// y = q, in which the registers r, r + d and r + 2d (d = 1/c) hold the
// lanes (x, y), (x + 1, y) and (x + 2, y) of chi in each quadword. pi
// maps each set onto the next, register r onto register r, so it moves
// no lane between registers: vpermq goes from T to K after rho and back
// after chi. After the third round of a group, S(1, 4), masked blends
// and vpermi2q change the sets back to S(2, 1). The index vectors and
// the rotation counts are in a table after the code, read RIP-relatively.
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
// extern void sha3_keccak_f1600_avx512
//   (uint64_t a[S2N_BIGNUM_STATIC 25],
//    const uint64_t rc[S2N_BIGNUM_STATIC 24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak_f1600_avx512)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak_f1600_avx512)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak_f1600_avx512)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak_f1600_avx512):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_DEC_RSP(16)
        CFI_STACKSAVE(rdi,0)
        CFI_STACKSAVE(rsi,8)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// The constant vectors, the theta index vectors, the masks of single
// positions (k1-k5) and of the five lanes (k6), and the rows of the
// state, then 20 blends into the sets of the first round

        lea     rax, [rip+sha3_keccak_f1600_avx512_consts]
        vmovdqa64 zmm30, ZMMWORD PTR [rax+2240]
        vmovdqa64 zmm31, ZMMWORD PTR [rax+2304]
        mov     edx, 1
        kmovw   k1, edx
        mov     edx, 2
        kmovw   k2, edx
        mov     edx, 4
        kmovw   k3, edx
        mov     edx, 8
        kmovw   k4, edx
        mov     edx, 16
        kmovw   k5, edx
        mov     edx, 0x1f
        kmovw   k6, edx
        mov     ecx, 4
        vmovdqu64 zmm20{k6}{z}, ZMMWORD PTR [rdi+0]
        vmovdqu64 zmm21{k6}{z}, ZMMWORD PTR [rdi+40]
        vmovdqu64 zmm22{k6}{z}, ZMMWORD PTR [rdi+80]
        vmovdqu64 zmm23{k6}{z}, ZMMWORD PTR [rdi+120]
        vmovdqu64 zmm24{k6}{z}, ZMMWORD PTR [rdi+160]
        vpblendmq zmm0{k2}, zmm20, zmm23
        vmovdqa64 zmm0{k3}, zmm21
        vmovdqa64 zmm0{k4}, zmm24
        vmovdqa64 zmm0{k5}, zmm22
        vpblendmq zmm1{k2}, zmm22, zmm20
        vmovdqa64 zmm1{k3}, zmm23
        vmovdqa64 zmm1{k4}, zmm21
        vmovdqa64 zmm1{k5}, zmm24
        vpblendmq zmm2{k2}, zmm24, zmm22
        vmovdqa64 zmm2{k3}, zmm20
        vmovdqa64 zmm2{k4}, zmm23
        vmovdqa64 zmm2{k5}, zmm21
        vpblendmq zmm3{k2}, zmm21, zmm24
        vmovdqa64 zmm3{k3}, zmm22
        vmovdqa64 zmm3{k4}, zmm20
        vmovdqa64 zmm3{k5}, zmm23
        vpblendmq zmm4{k2}, zmm23, zmm21
        vmovdqa64 zmm4{k3}, zmm24
        vmovdqa64 zmm4{k4}, zmm22
        vmovdqa64 zmm4{k5}, zmm20

// The loop: two groups of three rounds

        .balign 32
sha3_keccak_f1600_avx512_loop:

// Round 1 of the group, on S(2, 1) in T: theta

        vpxorq  zmm5, zmm1, zmm2
        vpternlogq zmm5, zmm3, zmm4, 0x96
        vpxorq  zmm5, zmm5, zmm0
        vprolq  zmm17, zmm5, 1
        vpermq  zmm16, zmm30, zmm5
        vpermq  zmm17, zmm31, zmm17
        vpternlogq zmm0, zmm16, zmm17, 0x96
        vpternlogq zmm1, zmm16, zmm17, 0x96
        vpternlogq zmm2, zmm16, zmm17, 0x96
        vpternlogq zmm3, zmm16, zmm17, 0x96
        vpternlogq zmm4, zmm16, zmm17, 0x96

// rho, and pi: to the K order of S(3, 4)

        vprolvq zmm0, zmm0, ZMMWORD PTR [rax+0]
        vprolvq zmm1, zmm1, ZMMWORD PTR [rax+64]
        vprolvq zmm2, zmm2, ZMMWORD PTR [rax+128]
        vprolvq zmm3, zmm3, ZMMWORD PTR [rax+192]
        vprolvq zmm4, zmm4, ZMMWORD PTR [rax+256]
        vmovdqa64 zmm25, ZMMWORD PTR [rax+320]
        vpermq  zmm0, zmm25, zmm0
        vmovdqa64 zmm26, ZMMWORD PTR [rax+384]
        vpermq  zmm4, zmm26, zmm4
        vmovdqa64 zmm27, ZMMWORD PTR [rax+448]
        vpermq  zmm3, zmm27, zmm3
        vmovdqa64 zmm28, ZMMWORD PTR [rax+512]
        vpermq  zmm2, zmm28, zmm2
        vmovdqa64 zmm29, ZMMWORD PTR [rax+576]
        vpermq  zmm1, zmm29, zmm1

// iota and chi (x + 1 in register r + 4)

        vmovdqa64 zmm18, zmm0
        vmovdqa64 zmm19, zmm4
        vpxorq  zmm0{k1}, zmm0, QWORD PTR [rsi+0]{1to8}
        vpternlogq zmm0, zmm4, zmm3, 0xd2
        vpternlogq zmm4, zmm3, zmm2, 0xd2
        vpternlogq zmm3, zmm2, zmm1, 0xd2
        vpternlogq zmm2, zmm1, zmm18, 0xd2
        vpternlogq zmm1, zmm18, zmm19, 0xd2

// Back to the T order

        vmovdqa64 zmm25, ZMMWORD PTR [rax+640]
        vpermq  zmm0, zmm25, zmm0
        vmovdqa64 zmm26, ZMMWORD PTR [rax+704]
        vpermq  zmm1, zmm26, zmm1
        vmovdqa64 zmm27, ZMMWORD PTR [rax+768]
        vpermq  zmm2, zmm27, zmm2
        vmovdqa64 zmm28, ZMMWORD PTR [rax+832]
        vpermq  zmm3, zmm28, zmm3
        vmovdqa64 zmm29, ZMMWORD PTR [rax+896]
        vpermq  zmm4, zmm29, zmm4

// Round 2 of the group, on S(3, 4) in T: theta

        vpxorq  zmm5, zmm1, zmm2
        vpternlogq zmm5, zmm3, zmm4, 0x96
        vpxorq  zmm5, zmm5, zmm0
        vprolq  zmm17, zmm5, 1
        vpermq  zmm16, zmm30, zmm5
        vpermq  zmm17, zmm31, zmm17
        vpternlogq zmm0, zmm16, zmm17, 0x96
        vpternlogq zmm1, zmm16, zmm17, 0x96
        vpternlogq zmm2, zmm16, zmm17, 0x96
        vpternlogq zmm3, zmm16, zmm17, 0x96
        vpternlogq zmm4, zmm16, zmm17, 0x96

// rho, and pi: to the K order of S(4, 3)

        vprolvq zmm0, zmm0, ZMMWORD PTR [rax+960]
        vprolvq zmm1, zmm1, ZMMWORD PTR [rax+1024]
        vprolvq zmm2, zmm2, ZMMWORD PTR [rax+1088]
        vprolvq zmm3, zmm3, ZMMWORD PTR [rax+1152]
        vprolvq zmm4, zmm4, ZMMWORD PTR [rax+1216]
        vmovdqa64 zmm25, ZMMWORD PTR [rax+640]
        vpermq  zmm0, zmm25, zmm0
        vmovdqa64 zmm26, ZMMWORD PTR [rax+832]
        vpermq  zmm2, zmm26, zmm2
        vmovdqa64 zmm27, ZMMWORD PTR [rax+704]
        vpermq  zmm4, zmm27, zmm4
        vmovdqa64 zmm28, ZMMWORD PTR [rax+896]
        vpermq  zmm1, zmm28, zmm1
        vmovdqa64 zmm29, ZMMWORD PTR [rax+768]
        vpermq  zmm3, zmm29, zmm3

// iota and chi (x + 1 in register r + 2)

        vmovdqa64 zmm18, zmm0
        vmovdqa64 zmm19, zmm2
        vpxorq  zmm0{k1}, zmm0, QWORD PTR [rsi+8]{1to8}
        vpternlogq zmm0, zmm2, zmm4, 0xd2
        vpternlogq zmm2, zmm4, zmm1, 0xd2
        vpternlogq zmm4, zmm1, zmm3, 0xd2
        vpternlogq zmm1, zmm3, zmm18, 0xd2
        vpternlogq zmm3, zmm18, zmm19, 0xd2

// Back to the T order

        vmovdqa64 zmm25, ZMMWORD PTR [rax+1280]
        vpermq  zmm0, zmm25, zmm0
        vmovdqa64 zmm26, ZMMWORD PTR [rax+1344]
        vpermq  zmm1, zmm26, zmm1
        vmovdqa64 zmm27, ZMMWORD PTR [rax+1408]
        vpermq  zmm2, zmm27, zmm2
        vmovdqa64 zmm28, ZMMWORD PTR [rax+1472]
        vpermq  zmm3, zmm28, zmm3
        vmovdqa64 zmm29, ZMMWORD PTR [rax+1536]
        vpermq  zmm4, zmm29, zmm4

// Round 3 of the group, on S(4, 3) in T: theta

        vpxorq  zmm5, zmm1, zmm2
        vpternlogq zmm5, zmm3, zmm4, 0x96
        vpxorq  zmm5, zmm5, zmm0
        vprolq  zmm17, zmm5, 1
        vpermq  zmm16, zmm30, zmm5
        vpermq  zmm17, zmm31, zmm17
        vpternlogq zmm0, zmm16, zmm17, 0x96
        vpternlogq zmm1, zmm16, zmm17, 0x96
        vpternlogq zmm2, zmm16, zmm17, 0x96
        vpternlogq zmm3, zmm16, zmm17, 0x96
        vpternlogq zmm4, zmm16, zmm17, 0x96

// rho, and pi: to the K order of S(1, 4)

        vprolvq zmm0, zmm0, ZMMWORD PTR [rax+1600]
        vprolvq zmm1, zmm1, ZMMWORD PTR [rax+1664]
        vprolvq zmm2, zmm2, ZMMWORD PTR [rax+1728]
        vprolvq zmm3, zmm3, ZMMWORD PTR [rax+1792]
        vprolvq zmm4, zmm4, ZMMWORD PTR [rax+1856]
        vmovdqa64 zmm25, ZMMWORD PTR [rax+1280]
        vpermq  zmm0, zmm25, zmm0
        vmovdqa64 zmm26, ZMMWORD PTR [rax+1408]
        vpermq  zmm4, zmm26, zmm4
        vmovdqa64 zmm27, ZMMWORD PTR [rax+1536]
        vpermq  zmm3, zmm27, zmm3
        vmovdqa64 zmm28, ZMMWORD PTR [rax+1344]
        vpermq  zmm2, zmm28, zmm2
        vmovdqa64 zmm29, ZMMWORD PTR [rax+1472]
        vpermq  zmm1, zmm29, zmm1

// iota and chi (x + 1 in register r + 4)

        vmovdqa64 zmm18, zmm0
        vmovdqa64 zmm19, zmm4
        vpxorq  zmm0{k1}, zmm0, QWORD PTR [rsi+16]{1to8}
        vpternlogq zmm0, zmm4, zmm3, 0xd2
        vpternlogq zmm4, zmm3, zmm2, 0xd2
        vpternlogq zmm3, zmm2, zmm1, 0xd2
        vpternlogq zmm2, zmm1, zmm18, 0xd2
        vpternlogq zmm1, zmm18, zmm19, 0xd2

// From S(1, 4) in K to S(2, 1) in T, in the other registers

        vpblendmq zmm25{k4}, zmm0, zmm2
        vmovdqa64 zmm25{k2}, zmm4
        vpblendmq zmm18{k3}, zmm1, zmm3
        vmovdqa64 zmm20, ZMMWORD PTR [rax+1920]
        vpermi2q zmm20, zmm25, zmm18
        vpblendmq zmm26{k1}, zmm2, zmm4
        vmovdqa64 zmm26{k4}, zmm1
        vpblendmq zmm19{k5}, zmm3, zmm0
        vmovdqa64 zmm21, ZMMWORD PTR [rax+1984]
        vpermi2q zmm21, zmm26, zmm19
        vpblendmq zmm27{k3}, zmm4, zmm1
        vmovdqa64 zmm27{k1}, zmm3
        vpblendmq zmm18{k2}, zmm0, zmm2
        vmovdqa64 zmm22, ZMMWORD PTR [rax+2048]
        vpermi2q zmm22, zmm27, zmm18
        vpblendmq zmm28{k5}, zmm1, zmm3
        vmovdqa64 zmm28{k3}, zmm0
        vpblendmq zmm19{k4}, zmm2, zmm4
        vmovdqa64 zmm23, ZMMWORD PTR [rax+2112]
        vpermi2q zmm23, zmm28, zmm19
        vpblendmq zmm29{k2}, zmm3, zmm0
        vmovdqa64 zmm29{k5}, zmm2
        vpblendmq zmm18{k1}, zmm4, zmm1
        vmovdqa64 zmm24, ZMMWORD PTR [rax+2176]
        vpermi2q zmm24, zmm29, zmm18

// Round 1 of the group, on S(2, 1) in T: theta

        vpxorq  zmm5, zmm21, zmm22
        vpternlogq zmm5, zmm23, zmm24, 0x96
        vpxorq  zmm5, zmm5, zmm20
        vprolq  zmm17, zmm5, 1
        vpermq  zmm16, zmm30, zmm5
        vpermq  zmm17, zmm31, zmm17
        vpternlogq zmm20, zmm16, zmm17, 0x96
        vpternlogq zmm21, zmm16, zmm17, 0x96
        vpternlogq zmm22, zmm16, zmm17, 0x96
        vpternlogq zmm23, zmm16, zmm17, 0x96
        vpternlogq zmm24, zmm16, zmm17, 0x96

// rho, and pi: to the K order of S(3, 4)

        vprolvq zmm20, zmm20, ZMMWORD PTR [rax+0]
        vprolvq zmm21, zmm21, ZMMWORD PTR [rax+64]
        vprolvq zmm22, zmm22, ZMMWORD PTR [rax+128]
        vprolvq zmm23, zmm23, ZMMWORD PTR [rax+192]
        vprolvq zmm24, zmm24, ZMMWORD PTR [rax+256]
        vmovdqa64 zmm25, ZMMWORD PTR [rax+320]
        vpermq  zmm20, zmm25, zmm20
        vmovdqa64 zmm26, ZMMWORD PTR [rax+384]
        vpermq  zmm24, zmm26, zmm24
        vmovdqa64 zmm27, ZMMWORD PTR [rax+448]
        vpermq  zmm23, zmm27, zmm23
        vmovdqa64 zmm28, ZMMWORD PTR [rax+512]
        vpermq  zmm22, zmm28, zmm22
        vmovdqa64 zmm29, ZMMWORD PTR [rax+576]
        vpermq  zmm21, zmm29, zmm21

// iota and chi (x + 1 in register r + 4)

        vmovdqa64 zmm18, zmm20
        vmovdqa64 zmm19, zmm24
        vpxorq  zmm20{k1}, zmm20, QWORD PTR [rsi+24]{1to8}
        vpternlogq zmm20, zmm24, zmm23, 0xd2
        vpternlogq zmm24, zmm23, zmm22, 0xd2
        vpternlogq zmm23, zmm22, zmm21, 0xd2
        vpternlogq zmm22, zmm21, zmm18, 0xd2
        vpternlogq zmm21, zmm18, zmm19, 0xd2

// Back to the T order

        vmovdqa64 zmm25, ZMMWORD PTR [rax+640]
        vpermq  zmm20, zmm25, zmm20
        vmovdqa64 zmm26, ZMMWORD PTR [rax+704]
        vpermq  zmm21, zmm26, zmm21
        vmovdqa64 zmm27, ZMMWORD PTR [rax+768]
        vpermq  zmm22, zmm27, zmm22
        vmovdqa64 zmm28, ZMMWORD PTR [rax+832]
        vpermq  zmm23, zmm28, zmm23
        vmovdqa64 zmm29, ZMMWORD PTR [rax+896]
        vpermq  zmm24, zmm29, zmm24

// Round 2 of the group, on S(3, 4) in T: theta

        vpxorq  zmm5, zmm21, zmm22
        vpternlogq zmm5, zmm23, zmm24, 0x96
        vpxorq  zmm5, zmm5, zmm20
        vprolq  zmm17, zmm5, 1
        vpermq  zmm16, zmm30, zmm5
        vpermq  zmm17, zmm31, zmm17
        vpternlogq zmm20, zmm16, zmm17, 0x96
        vpternlogq zmm21, zmm16, zmm17, 0x96
        vpternlogq zmm22, zmm16, zmm17, 0x96
        vpternlogq zmm23, zmm16, zmm17, 0x96
        vpternlogq zmm24, zmm16, zmm17, 0x96

// rho, and pi: to the K order of S(4, 3)

        vprolvq zmm20, zmm20, ZMMWORD PTR [rax+960]
        vprolvq zmm21, zmm21, ZMMWORD PTR [rax+1024]
        vprolvq zmm22, zmm22, ZMMWORD PTR [rax+1088]
        vprolvq zmm23, zmm23, ZMMWORD PTR [rax+1152]
        vprolvq zmm24, zmm24, ZMMWORD PTR [rax+1216]
        vmovdqa64 zmm25, ZMMWORD PTR [rax+640]
        vpermq  zmm20, zmm25, zmm20
        vmovdqa64 zmm26, ZMMWORD PTR [rax+832]
        vpermq  zmm22, zmm26, zmm22
        vmovdqa64 zmm27, ZMMWORD PTR [rax+704]
        vpermq  zmm24, zmm27, zmm24
        vmovdqa64 zmm28, ZMMWORD PTR [rax+896]
        vpermq  zmm21, zmm28, zmm21
        vmovdqa64 zmm29, ZMMWORD PTR [rax+768]
        vpermq  zmm23, zmm29, zmm23

// iota and chi (x + 1 in register r + 2)

        vmovdqa64 zmm18, zmm20
        vmovdqa64 zmm19, zmm22
        vpxorq  zmm20{k1}, zmm20, QWORD PTR [rsi+32]{1to8}
        vpternlogq zmm20, zmm22, zmm24, 0xd2
        vpternlogq zmm22, zmm24, zmm21, 0xd2
        vpternlogq zmm24, zmm21, zmm23, 0xd2
        vpternlogq zmm21, zmm23, zmm18, 0xd2
        vpternlogq zmm23, zmm18, zmm19, 0xd2

// Back to the T order

        vmovdqa64 zmm25, ZMMWORD PTR [rax+1280]
        vpermq  zmm20, zmm25, zmm20
        vmovdqa64 zmm26, ZMMWORD PTR [rax+1344]
        vpermq  zmm21, zmm26, zmm21
        vmovdqa64 zmm27, ZMMWORD PTR [rax+1408]
        vpermq  zmm22, zmm27, zmm22
        vmovdqa64 zmm28, ZMMWORD PTR [rax+1472]
        vpermq  zmm23, zmm28, zmm23
        vmovdqa64 zmm29, ZMMWORD PTR [rax+1536]
        vpermq  zmm24, zmm29, zmm24

// Round 3 of the group, on S(4, 3) in T: theta

        vpxorq  zmm5, zmm21, zmm22
        vpternlogq zmm5, zmm23, zmm24, 0x96
        vpxorq  zmm5, zmm5, zmm20
        vprolq  zmm17, zmm5, 1
        vpermq  zmm16, zmm30, zmm5
        vpermq  zmm17, zmm31, zmm17
        vpternlogq zmm20, zmm16, zmm17, 0x96
        vpternlogq zmm21, zmm16, zmm17, 0x96
        vpternlogq zmm22, zmm16, zmm17, 0x96
        vpternlogq zmm23, zmm16, zmm17, 0x96
        vpternlogq zmm24, zmm16, zmm17, 0x96

// rho, and pi: to the K order of S(1, 4)

        vprolvq zmm20, zmm20, ZMMWORD PTR [rax+1600]
        vprolvq zmm21, zmm21, ZMMWORD PTR [rax+1664]
        vprolvq zmm22, zmm22, ZMMWORD PTR [rax+1728]
        vprolvq zmm23, zmm23, ZMMWORD PTR [rax+1792]
        vprolvq zmm24, zmm24, ZMMWORD PTR [rax+1856]
        vmovdqa64 zmm25, ZMMWORD PTR [rax+1280]
        vpermq  zmm20, zmm25, zmm20
        vmovdqa64 zmm26, ZMMWORD PTR [rax+1408]
        vpermq  zmm24, zmm26, zmm24
        vmovdqa64 zmm27, ZMMWORD PTR [rax+1536]
        vpermq  zmm23, zmm27, zmm23
        vmovdqa64 zmm28, ZMMWORD PTR [rax+1344]
        vpermq  zmm22, zmm28, zmm22
        vmovdqa64 zmm29, ZMMWORD PTR [rax+1472]
        vpermq  zmm21, zmm29, zmm21

// iota and chi (x + 1 in register r + 4)

        vmovdqa64 zmm18, zmm20
        vmovdqa64 zmm19, zmm24
        vpxorq  zmm20{k1}, zmm20, QWORD PTR [rsi+40]{1to8}
        vpternlogq zmm20, zmm24, zmm23, 0xd2
        vpternlogq zmm24, zmm23, zmm22, 0xd2
        vpternlogq zmm23, zmm22, zmm21, 0xd2
        vpternlogq zmm22, zmm21, zmm18, 0xd2
        vpternlogq zmm21, zmm18, zmm19, 0xd2
        add     rsi, 48
        dec     ecx
        jz      sha3_keccak_f1600_avx512_done

// From S(1, 4) in K to S(2, 1) in T

        vpblendmq zmm25{k4}, zmm20, zmm22
        vmovdqa64 zmm25{k2}, zmm24
        vpblendmq zmm18{k3}, zmm21, zmm23
        vmovdqa64 zmm0, ZMMWORD PTR [rax+1920]
        vpermi2q zmm0, zmm25, zmm18
        vpblendmq zmm26{k1}, zmm22, zmm24
        vmovdqa64 zmm26{k4}, zmm21
        vpblendmq zmm19{k5}, zmm23, zmm20
        vmovdqa64 zmm1, ZMMWORD PTR [rax+1984]
        vpermi2q zmm1, zmm26, zmm19
        vpblendmq zmm27{k3}, zmm24, zmm21
        vmovdqa64 zmm27{k1}, zmm23
        vpblendmq zmm18{k2}, zmm20, zmm22
        vmovdqa64 zmm2, ZMMWORD PTR [rax+2048]
        vpermi2q zmm2, zmm27, zmm18
        vpblendmq zmm28{k5}, zmm21, zmm23
        vmovdqa64 zmm28{k3}, zmm20
        vpblendmq zmm19{k4}, zmm22, zmm24
        vmovdqa64 zmm3, ZMMWORD PTR [rax+2112]
        vpermi2q zmm3, zmm28, zmm19
        vpblendmq zmm29{k2}, zmm23, zmm20
        vmovdqa64 zmm29{k5}, zmm22
        vpblendmq zmm18{k1}, zmm24, zmm21
        vmovdqa64 zmm4, ZMMWORD PTR [rax+2176]
        vpermi2q zmm4, zmm29, zmm18
        jmp     sha3_keccak_f1600_avx512_loop

sha3_keccak_f1600_avx512_done:

// From S(1, 4) in K to the rows, and store them

        vmovdqa64 zmm25, ZMMWORD PTR [rax+320]
        vpermq  zmm20, zmm25, zmm20
        vmovdqa64 zmm26, ZMMWORD PTR [rax+384]
        vpermq  zmm21, zmm26, zmm21
        vmovdqa64 zmm27, ZMMWORD PTR [rax+448]
        vpermq  zmm22, zmm27, zmm22
        vmovdqa64 zmm28, ZMMWORD PTR [rax+512]
        vpermq  zmm23, zmm28, zmm23
        vmovdqa64 zmm29, ZMMWORD PTR [rax+576]
        vpermq  zmm24, zmm29, zmm24
        vpblendmq zmm0{k2}, zmm20, zmm24
        vmovdqa64 zmm0{k3}, zmm23
        vmovdqa64 zmm0{k4}, zmm22
        vmovdqa64 zmm0{k5}, zmm21
        vpblendmq zmm1{k2}, zmm21, zmm20
        vmovdqa64 zmm1{k3}, zmm24
        vmovdqa64 zmm1{k4}, zmm23
        vmovdqa64 zmm1{k5}, zmm22
        vpblendmq zmm2{k2}, zmm22, zmm21
        vmovdqa64 zmm2{k3}, zmm20
        vmovdqa64 zmm2{k4}, zmm24
        vmovdqa64 zmm2{k5}, zmm23
        vpblendmq zmm3{k2}, zmm23, zmm22
        vmovdqa64 zmm3{k3}, zmm21
        vmovdqa64 zmm3{k4}, zmm20
        vmovdqa64 zmm3{k5}, zmm24
        vpblendmq zmm4{k2}, zmm24, zmm23
        vmovdqa64 zmm4{k3}, zmm22
        vmovdqa64 zmm4{k4}, zmm21
        vmovdqa64 zmm4{k5}, zmm20
        vmovdqu64 ZMMWORD PTR [rdi+0]{k6}, zmm0
        vmovdqu64 ZMMWORD PTR [rdi+40]{k6}, zmm1
        vmovdqu64 ZMMWORD PTR [rdi+80]{k6}, zmm2
        vmovdqu64 ZMMWORD PTR [rdi+120]{k6}, zmm3
        vmovdqu64 ZMMWORD PTR [rdi+160]{k6}, zmm4

        vzeroupper

#if WINDOWS_ABI
        CFI_STACKLOAD(rdi,0)
        CFI_STACKLOAD(rsi,8)
        CFI_INC_RSP(16)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha3_keccak_f1600_avx512)

// The constant vectors

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 64
sha3_keccak_f1600_avx512_consts:
        .quad   0, 45, 6, 56, 39, 0, 0, 0
        .quad   3, 1, 15, 55, 14, 0, 0, 0
        .quad   18, 10, 62, 21, 20, 0, 0, 0
        .quad   36, 2, 43, 28, 8, 0, 0, 0
        .quad   41, 44, 61, 25, 27, 0, 0, 0
        .quad   0, 1, 2, 3, 4, 5, 6, 7
        .quad   1, 2, 3, 4, 0, 5, 6, 7
        .quad   2, 3, 4, 0, 1, 5, 6, 7
        .quad   3, 4, 0, 1, 2, 5, 6, 7
        .quad   4, 0, 1, 2, 3, 5, 6, 7
        .quad   0, 2, 4, 1, 3, 5, 6, 7
        .quad   2, 4, 1, 3, 0, 5, 6, 7
        .quad   4, 1, 3, 0, 2, 5, 6, 7
        .quad   1, 3, 0, 2, 4, 5, 6, 7
        .quad   3, 0, 2, 4, 1, 5, 6, 7
        .quad   0, 10, 61, 55, 8, 0, 0, 0
        .quad   3, 2, 6, 21, 27, 0, 0, 0
        .quad   18, 44, 15, 28, 39, 0, 0, 0
        .quad   36, 45, 62, 25, 14, 0, 0, 0
        .quad   41, 1, 43, 56, 20, 0, 0, 0
        .quad   0, 4, 3, 2, 1, 5, 6, 7
        .quad   3, 2, 1, 0, 4, 5, 6, 7
        .quad   1, 0, 4, 3, 2, 5, 6, 7
        .quad   4, 3, 2, 1, 0, 5, 6, 7
        .quad   2, 1, 0, 4, 3, 5, 6, 7
        .quad   0, 2, 15, 25, 20, 0, 0, 0
        .quad   41, 10, 6, 28, 14, 0, 0, 0
        .quad   36, 1, 61, 21, 39, 0, 0, 0
        .quad   18, 45, 43, 55, 27, 0, 0, 0
        .quad   3, 44, 62, 56, 8, 0, 0, 0
        .quad   0, 3, 1, 12, 10, 5, 6, 7
        .quad   2, 0, 3, 9, 12, 5, 6, 7
        .quad   4, 2, 0, 11, 9, 5, 6, 7
        .quad   1, 4, 2, 8, 11, 5, 6, 7
        .quad   3, 1, 4, 10, 8, 5, 6, 7
        .quad   4, 0, 1, 2, 3, 5, 6, 7
        .quad   1, 2, 3, 4, 0, 5, 6, 7

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on NIST curve P-256 in Montgomery-Jacobian coordinates
//
//    extern void p256_montjmixadd(uint64_t p3[static 12],
//                                 const uint64_t p1[static 12],
//                                 const uint64_t p2[static 8]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity.
//
// Standard ARM ABI: X0 = p3, X1 = p1, X2 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p256_montjmixadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p256_montjmixadd)

        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence

#define input_z x17
#define input_x x19
#define input_y x20

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x, #0
#define y_1 input_x, #NUMSIZE
#define z_1 input_x, #(2*NUMSIZE)

#define x_2 input_y, #0
#define y_2 input_y, #NUMSIZE

#define x_3 input_z, #0
#define y_3 input_z, #NUMSIZE
#define z_3 input_z, #(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define zp2 sp, #(NUMSIZE*0)
#define ww sp, #(NUMSIZE*0)
#define resx sp, #(NUMSIZE*0)

#define yd sp, #(NUMSIZE*1)
#define y2a sp, #(NUMSIZE*1)

#define x2a sp, #(NUMSIZE*2)
#define zzx2 sp, #(NUMSIZE*2)

#define zz sp, #(NUMSIZE*3)
#define t1 sp, #(NUMSIZE*3)

#define t2 sp, #(NUMSIZE*4)
#define zzx1 sp, #(NUMSIZE*4)
#define resy sp, #(NUMSIZE*4)

#define xd sp, #(NUMSIZE*5)
#define resz sp, #(NUMSIZE*5)

#define NSPACE (NUMSIZE*6)

// Corresponds to bignum_montmul_p256 but uses x0 in place of x17

#define montmul_p256(P0,P1,P2)                  \
        ldp     x3, x4, [P1] __LF                  \
        ldp     x5, x6, [P1+16] __LF               \
        ldp     x7, x8, [P2] __LF                  \
        ldp     x9, x10, [P2+16] __LF              \
        mul     x11, x3, x7 __LF                   \
        mul     x13, x4, x8 __LF                   \
        umulh   x12, x3, x7 __LF                   \
        adds    x16, x11, x13 __LF                 \
        umulh   x14, x4, x8 __LF                   \
        adcs    x0, x12, x14 __LF                  \
        adcs    x14, x14, xzr __LF                 \
        adds    x12, x12, x16 __LF                 \
        adcs    x13, x13, x0 __LF                  \
        adcs    x14, x14, xzr __LF                 \
        subs    x15, x3, x4 __LF                   \
        cneg    x15, x15, lo __LF                  \
        csetm   x1, lo __LF                        \
        subs    x0, x8, x7 __LF                    \
        cneg    x0, x0, lo __LF                    \
        mul     x16, x15, x0 __LF                  \
        umulh   x0, x15, x0 __LF                   \
        cinv    x1, x1, lo __LF                    \
        eor     x16, x16, x1 __LF                  \
        eor     x0, x0, x1 __LF                    \
        cmn     x1, #1 __LF                        \
        adcs    x12, x12, x16 __LF                 \
        adcs    x13, x13, x0 __LF                  \
        adc     x14, x14, x1 __LF                  \
        lsl     x0, x11, #32 __LF                  \
        subs    x1, x11, x0 __LF                   \
        lsr     x16, x11, #32 __LF                 \
        sbc     x11, x11, x16 __LF                 \
        adds    x12, x12, x0 __LF                  \
        adcs    x13, x13, x16 __LF                 \
        adcs    x14, x14, x1 __LF                  \
        adc     x11, x11, xzr __LF                 \
        lsl     x0, x12, #32 __LF                  \
        subs    x1, x12, x0 __LF                   \
        lsr     x16, x12, #32 __LF                 \
        sbc     x12, x12, x16 __LF                 \
        adds    x13, x13, x0 __LF                  \
        adcs    x14, x14, x16 __LF                 \
        adcs    x11, x11, x1 __LF                  \
        adc     x12, x12, xzr __LF                 \
        stp     x13, x14, [P0] __LF                \
        stp     x11, x12, [P0+16] __LF             \
        mul     x11, x5, x9 __LF                   \
        mul     x13, x6, x10 __LF                  \
        umulh   x12, x5, x9 __LF                   \
        adds    x16, x11, x13 __LF                 \
        umulh   x14, x6, x10 __LF                  \
        adcs    x0, x12, x14 __LF                  \
        adcs    x14, x14, xzr __LF                 \
        adds    x12, x12, x16 __LF                 \
        adcs    x13, x13, x0 __LF                  \
        adcs    x14, x14, xzr __LF                 \
        subs    x15, x5, x6 __LF                   \
        cneg    x15, x15, lo __LF                  \
        csetm   x1, lo __LF                        \
        subs    x0, x10, x9 __LF                   \
        cneg    x0, x0, lo __LF                    \
        mul     x16, x15, x0 __LF                  \
        umulh   x0, x15, x0 __LF                   \
        cinv    x1, x1, lo __LF                    \
        eor     x16, x16, x1 __LF                  \
        eor     x0, x0, x1 __LF                    \
        cmn     x1, #1 __LF                        \
        adcs    x12, x12, x16 __LF                 \
        adcs    x13, x13, x0 __LF                  \
        adc     x14, x14, x1 __LF                  \
        subs    x3, x5, x3 __LF                    \
        sbcs    x4, x6, x4 __LF                    \
        ngc     x5, xzr __LF                       \
        cmn     x5, #1 __LF                        \
        eor     x3, x3, x5 __LF                    \
        adcs    x3, x3, xzr __LF                   \
        eor     x4, x4, x5 __LF                    \
        adcs    x4, x4, xzr __LF                   \
        subs    x7, x7, x9 __LF                    \
        sbcs    x8, x8, x10 __LF                   \
        ngc     x9, xzr __LF                       \
        cmn     x9, #1 __LF                        \
        eor     x7, x7, x9 __LF                    \
        adcs    x7, x7, xzr __LF                   \
        eor     x8, x8, x9 __LF                    \
        adcs    x8, x8, xzr __LF                   \
        eor     x10, x5, x9 __LF                   \
        ldp     x15, x1, [P0] __LF                 \
        adds    x15, x11, x15 __LF                 \
        adcs    x1, x12, x1 __LF                   \
        ldp     x5, x9, [P0+16] __LF               \
        adcs    x5, x13, x5 __LF                   \
        adcs    x9, x14, x9 __LF                   \
        adc     x2, xzr, xzr __LF                  \
        mul     x11, x3, x7 __LF                   \
        mul     x13, x4, x8 __LF                   \
        umulh   x12, x3, x7 __LF                   \
        adds    x16, x11, x13 __LF                 \
        umulh   x14, x4, x8 __LF                   \
        adcs    x0, x12, x14 __LF                  \
        adcs    x14, x14, xzr __LF                 \
        adds    x12, x12, x16 __LF                 \
        adcs    x13, x13, x0 __LF                  \
        adcs    x14, x14, xzr __LF                 \
        subs    x3, x3, x4 __LF                    \
        cneg    x3, x3, lo __LF                    \
        csetm   x4, lo __LF                        \
        subs    x0, x8, x7 __LF                    \
        cneg    x0, x0, lo __LF                    \
        mul     x16, x3, x0 __LF                   \
        umulh   x0, x3, x0 __LF                    \
        cinv    x4, x4, lo __LF                    \
        eor     x16, x16, x4 __LF                  \
        eor     x0, x0, x4 __LF                    \
        cmn     x4, #1 __LF                        \
        adcs    x12, x12, x16 __LF                 \
        adcs    x13, x13, x0 __LF                  \
        adc     x14, x14, x4 __LF                  \
        cmn     x10, #1 __LF                       \
        eor     x11, x11, x10 __LF                 \
        adcs    x11, x11, x15 __LF                 \
        eor     x12, x12, x10 __LF                 \
        adcs    x12, x12, x1 __LF                  \
        eor     x13, x13, x10 __LF                 \
        adcs    x13, x13, x5 __LF                  \
        eor     x14, x14, x10 __LF                 \
        adcs    x14, x14, x9 __LF                  \
        adcs    x3, x2, x10 __LF                   \
        adcs    x4, x10, xzr __LF                  \
        adc     x10, x10, xzr __LF                 \
        adds    x13, x13, x15 __LF                 \
        adcs    x14, x14, x1 __LF                  \
        adcs    x3, x3, x5 __LF                    \
        adcs    x4, x4, x9 __LF                    \
        adc     x10, x10, x2 __LF                  \
        lsl     x0, x11, #32 __LF                  \
        subs    x1, x11, x0 __LF                   \
        lsr     x16, x11, #32 __LF                 \
        sbc     x11, x11, x16 __LF                 \
        adds    x12, x12, x0 __LF                  \
        adcs    x13, x13, x16 __LF                 \
        adcs    x14, x14, x1 __LF                  \
        adc     x11, x11, xzr __LF                 \
        lsl     x0, x12, #32 __LF                  \
        subs    x1, x12, x0 __LF                   \
        lsr     x16, x12, #32 __LF                 \
        sbc     x12, x12, x16 __LF                 \
        adds    x13, x13, x0 __LF                  \
        adcs    x14, x14, x16 __LF                 \
        adcs    x11, x11, x1 __LF                  \
        adc     x12, x12, xzr __LF                 \
        adds    x3, x3, x11 __LF                   \
        adcs    x4, x4, x12 __LF                   \
        adc     x10, x10, xzr __LF                 \
        add     x2, x10, #1 __LF                   \
        lsl     x16, x2, #32 __LF                  \
        adds    x4, x4, x16 __LF                   \
        adc     x10, x10, xzr __LF                 \
        neg     x15, x2 __LF                       \
        sub     x16, x16, #1 __LF                  \
        subs    x13, x13, x15 __LF                 \
        sbcs    x14, x14, x16 __LF                 \
        sbcs    x3, x3, xzr __LF                   \
        sbcs    x4, x4, x2 __LF                    \
        sbcs    x7, x10, x2 __LF                   \
        adds    x13, x13, x7 __LF                  \
        mov     x10, #4294967295 __LF              \
        and     x10, x10, x7 __LF                  \
        adcs    x14, x14, x10 __LF                 \
        adcs    x3, x3, xzr __LF                   \
        mov     x10, #-4294967295 __LF             \
        and     x10, x10, x7 __LF                  \
        adc     x4, x4, x10 __LF                   \
        stp     x13, x14, [P0] __LF                \
        stp     x3, x4, [P0+16]

// Corresponds to bignum_montsqr_p256 but uses x0 in place of x17

#define montsqr_p256(P0,P1)                     \
        ldp     x2, x3, [P1] __LF                  \
        ldp     x4, x5, [P1+16] __LF               \
        umull   x15, w2, w2 __LF                   \
        lsr     x11, x2, #32 __LF                  \
        umull   x16, w11, w11 __LF                 \
        umull   x11, w2, w11 __LF                  \
        adds    x15, x15, x11, lsl #33 __LF        \
        lsr     x11, x11, #31 __LF                 \
        adc     x16, x16, x11 __LF                 \
        umull   x0, w3, w3 __LF                    \
        lsr     x11, x3, #32 __LF                  \
        umull   x1, w11, w11 __LF                  \
        umull   x11, w3, w11 __LF                  \
        mul     x12, x2, x3 __LF                   \
        umulh   x13, x2, x3 __LF                   \
        adds    x0, x0, x11, lsl #33 __LF          \
        lsr     x11, x11, #31 __LF                 \
        adc     x1, x1, x11 __LF                   \
        adds    x12, x12, x12 __LF                 \
        adcs    x13, x13, x13 __LF                 \
        adc     x1, x1, xzr __LF                   \
        adds    x16, x16, x12 __LF                 \
        adcs    x0, x0, x13 __LF                   \
        adc     x1, x1, xzr __LF                   \
        lsl     x12, x15, #32 __LF                 \
        subs    x13, x15, x12 __LF                 \
        lsr     x11, x15, #32 __LF                 \
        sbc     x15, x15, x11 __LF                 \
        adds    x16, x16, x12 __LF                 \
        adcs    x0, x0, x11 __LF                   \
        adcs    x1, x1, x13 __LF                   \
        adc     x15, x15, xzr __LF                 \
        lsl     x12, x16, #32 __LF                 \
        subs    x13, x16, x12 __LF                 \
        lsr     x11, x16, #32 __LF                 \
        sbc     x16, x16, x11 __LF                 \
        adds    x0, x0, x12 __LF                   \
        adcs    x1, x1, x11 __LF                   \
        adcs    x15, x15, x13 __LF                 \
        adc     x16, x16, xzr __LF                 \
        mul     x6, x2, x4 __LF                    \
        mul     x14, x3, x5 __LF                   \
        umulh   x8, x2, x4 __LF                    \
        subs    x10, x2, x3 __LF                   \
        cneg    x10, x10, lo __LF                  \
        csetm   x13, lo __LF                       \
        subs    x12, x5, x4 __LF                   \
        cneg    x12, x12, lo __LF                  \
        mul     x11, x10, x12 __LF                 \
        umulh   x12, x10, x12 __LF                 \
        cinv    x13, x13, lo __LF                  \
        eor     x11, x11, x13 __LF                 \
        eor     x12, x12, x13 __LF                 \
        adds    x7, x6, x8 __LF                    \
        adc     x8, x8, xzr __LF                   \
        umulh   x9, x3, x5 __LF                    \
        adds    x7, x7, x14 __LF                   \
        adcs    x8, x8, x9 __LF                    \
        adc     x9, x9, xzr __LF                   \
        adds    x8, x8, x14 __LF                   \
        adc     x9, x9, xzr __LF                   \
        cmn     x13, #1 __LF                       \
        adcs    x7, x7, x11 __LF                   \
        adcs    x8, x8, x12 __LF                   \
        adc     x9, x9, x13 __LF                   \
        adds    x6, x6, x6 __LF                    \
        adcs    x7, x7, x7 __LF                    \
        adcs    x8, x8, x8 __LF                    \
        adcs    x9, x9, x9 __LF                    \
        adc     x10, xzr, xzr __LF                 \
        adds    x6, x6, x0 __LF                    \
        adcs    x7, x7, x1 __LF                    \
        adcs    x8, x8, x15 __LF                   \
        adcs    x9, x9, x16 __LF                   \
        adc     x10, x10, xzr __LF                 \
        lsl     x12, x6, #32 __LF                  \
        subs    x13, x6, x12 __LF                  \
        lsr     x11, x6, #32 __LF                  \
        sbc     x6, x6, x11 __LF                   \
        adds    x7, x7, x12 __LF                   \
        adcs    x8, x8, x11 __LF                   \
        adcs    x9, x9, x13 __LF                   \
        adcs    x10, x10, x6 __LF                  \
        adc     x6, xzr, xzr __LF                  \
        lsl     x12, x7, #32 __LF                  \
        subs    x13, x7, x12 __LF                  \
        lsr     x11, x7, #32 __LF                  \
        sbc     x7, x7, x11 __LF                   \
        adds    x8, x8, x12 __LF                   \
        adcs    x9, x9, x11 __LF                   \
        adcs    x10, x10, x13 __LF                 \
        adcs    x6, x6, x7 __LF                    \
        adc     x7, xzr, xzr __LF                  \
        mul     x11, x4, x4 __LF                   \
        adds    x8, x8, x11 __LF                   \
        mul     x12, x5, x5 __LF                   \
        umulh   x11, x4, x4 __LF                   \
        adcs    x9, x9, x11 __LF                   \
        adcs    x10, x10, x12 __LF                 \
        umulh   x12, x5, x5 __LF                   \
        adcs    x6, x6, x12 __LF                   \
        adc     x7, x7, xzr __LF                   \
        mul     x11, x4, x5 __LF                   \
        umulh   x12, x4, x5 __LF                   \
        adds    x11, x11, x11 __LF                 \
        adcs    x12, x12, x12 __LF                 \
        adc     x13, xzr, xzr __LF                 \
        adds    x9, x9, x11 __LF                   \
        adcs    x10, x10, x12 __LF                 \
        adcs    x6, x6, x13 __LF                   \
        adcs    x7, x7, xzr __LF                   \
        mov     x11, #4294967295 __LF              \
        adds    x5, x8, #1 __LF                    \
        sbcs    x11, x9, x11 __LF                  \
        mov     x13, #-4294967295 __LF             \
        sbcs    x12, x10, xzr __LF                 \
        sbcs    x13, x6, x13 __LF                  \
        sbcs    xzr, x7, xzr __LF                  \
        csel    x8, x5, x8, hs __LF                \
        csel    x9, x11, x9, hs __LF               \
        csel    x10, x12, x10, hs __LF             \
        csel    x6, x13, x6, hs __LF               \
        stp     x8, x9, [P0] __LF                  \
        stp     x10, x6, [P0+16]

// Corresponds exactly to bignum_sub_p256

#define sub_p256(P0,P1,P2)                      \
        ldp     x5, x6, [P1] __LF                  \
        ldp     x4, x3, [P2] __LF                  \
        subs    x5, x5, x4 __LF                    \
        sbcs    x6, x6, x3 __LF                    \
        ldp     x7, x8, [P1+16] __LF               \
        ldp     x4, x3, [P2+16] __LF               \
        sbcs    x7, x7, x4 __LF                    \
        sbcs    x8, x8, x3 __LF                    \
        csetm   x3, cc __LF                        \
        adds    x5, x5, x3 __LF                    \
        mov     x4, #0xffffffff __LF               \
        and     x4, x4, x3 __LF                    \
        adcs    x6, x6, x4 __LF                    \
        adcs    x7, x7, xzr __LF                   \
        mov     x4, #0xffffffff00000001 __LF       \
        and     x4, x4, x3 __LF                    \
        adc     x8, x8, x4 __LF                    \
        stp     x5, x6, [P0] __LF                  \
        stp     x7, x8, [P0+16]

S2N_BN_SYMBOL(p256_montjmixadd):

// Save regs and make room on stack for temporary variables

        stp     x19, x20, [sp, #-16]!
        sub     sp, sp, NSPACE

// Move the input arguments to stable places

        mov     input_z, x0
        mov     input_x, x1
        mov     input_y, x2

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        montsqr_p256(zp2,z_1)
        montmul_p256(y2a,z_1,y_2)

        montmul_p256(x2a,zp2,x_2)
        montmul_p256(y2a,zp2,y2a)

        sub_p256(xd,x2a,x_1)
        sub_p256(yd,y2a,y_1)

        montsqr_p256(zz,xd)
        montsqr_p256(ww,yd)

        montmul_p256(zzx1,zz,x_1)
        montmul_p256(zzx2,zz,x2a)

        sub_p256(resx,ww,zzx1)
        sub_p256(t1,zzx2,zzx1)

        montmul_p256(resz,xd,z_1)

        sub_p256(resx,resx,zzx2)

        sub_p256(t2,zzx1,resx)

        montmul_p256(t1,t1,y_1)
        montmul_p256(t2,yd,t2)

        sub_p256(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        ldp     x0, x1, [z_1]
        ldp     x2, x3, [z_1+16]
        orr     x4, x0, x1
        orr     x5, x2, x3
        orr     x4, x4, x5
        cmp     x4, xzr

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with a z = 1 coordinate (in
// Montgomery form so not the simple constant 1 but rather 2^256 - p_256),
// hence giving 0 + p2 = p2 for the final result.

        ldp     x0, x1, [resx]
        ldp     x12, x13, [x_2]
        csel    x0, x0, x12, ne
        csel    x1, x1, x13, ne
        ldp     x2, x3, [resx+16]
        ldp     x12, x13, [x_2+16]
        csel    x2, x2, x12, ne
        csel    x3, x3, x13, ne

        ldp     x4, x5, [resy]
        ldp     x12, x13, [y_2]
        csel    x4, x4, x12, ne
        csel    x5, x5, x13, ne
        ldp     x6, x7, [resy+16]
        ldp     x12, x13, [y_2+16]
        csel    x6, x6, x12, ne
        csel    x7, x7, x13, ne

        ldp     x8, x9, [resz]
        mov     x12, #0x0000000000000001
        mov     x13, #0xffffffff00000000
        csel    x8, x8, x12, ne
        csel    x9, x9, x13, ne
        ldp     x10, x11, [resz+16]
        mov     x12, #0xffffffffffffffff
        mov     x13, #0x00000000fffffffe
        csel    x10, x10, x12, ne
        csel    x11, x11, x13, ne

        stp     x0, x1, [x_3]
        stp     x2, x3, [x_3+16]
        stp     x4, x5, [y_3]
        stp     x6, x7, [y_3+16]
        stp     x8, x9, [z_3]
        stp     x10, x11, [z_3+16]

// Restore registers and return

        add     sp, sp, NSPACE
        ldp     x19, x20, [sp], 16
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif

// Copyright (c) Meta Platforms, Inc. and affiliates (zstd, see README.md)
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The code and read-only data of libzstd_huf.so (gcc 12, -O2)
//
// This is a transcription of libzstd_huf.so, zstd's Huffman and FSE
// decoding compiled by gcc 12 as a shared library (see README.md), as
// loaded at an address that is a multiple of 4096: the start of its first
// segment, from address 0 up to the end of the read-only data. The ELF
// header and dynamic linking information at the start are given as data,
// as are the padding and the read-only data at the end, while the
// procedure linkage table and the code are given as instructions. The ADRP
// instructions, which compute addresses of pages relative to that of the
// instruction, are given as words, as are the branches to addresses
// outside the code. The labels are named after the addresses in the
// binary.
// ----------------------------------------------------------------------------

        .text
        .balign 4

// ELF header and dynamic linking information (0x0 to 0x620)

// memcpy@GLIBC_2.17 (0x0 bytes)
// __cxa_finalize@GLIBC_2.17 (0x0 bytes)
// memset@GLIBC_2.17 (0x0 bytes)
        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x00000000000112a8
        .quad   0x0038004000000000
        .quad   0x001a001b00400006
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00000000000086b8
        .quad   0x00000000000086b8
        .quad   0x0000000000010000
        .quad   0x0000000600000001
        .quad   0x000000000000fdc0
        .quad   0x000000000001fdc0
        .quad   0x000000000001fdc0
        .quad   0x0000000000000268
        .quad   0x0000000000000270
        .quad   0x0000000000010000
        .quad   0x0000000600000002
        .quad   0x000000000000fdd0
        .quad   0x000000000001fdd0
        .quad   0x000000000001fdd0
        .quad   0x00000000000001f0
        .quad   0x00000000000001f0
        .quad   0x0000000000000008
        .quad   0x000000046474e550
        .quad   0x0000000000007d00
        .quad   0x0000000000007d00
        .quad   0x0000000000007d00
        .quad   0x000000000000015c
        .quad   0x000000000000015c
        .quad   0x0000000000000004
        .quad   0x000000066474e551
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000010
        .quad   0x000000046474e552
        .quad   0x000000000000fdc0
        .quad   0x000000000001fdc0
        .quad   0x000000000001fdc0
        .quad   0x0000000000000240
        .quad   0x0000000000000240
        .quad   0x0000000000000001
        .quad   0x0000000e00000003
        .quad   0x0000000800000007
        .quad   0x000000000000000d
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000030000000c
        .quad   0x0000000a00000006
        .quad   0x000000090000000b
        .quad   0x0000000000000004
        .quad   0x0000000000000005
        .quad   0x0000000900000003
        .quad   0x0000000600000001
        .quad   0x8211148000001048
        .quad   0x0000000b00000009
        .quad   0xbb8d8a8c0000000c
        .quad   0x06c500edf311aff1
        .quad   0x6f668e67206921b4
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0009000300000000
        .quad   0x0000000000000600
        .quad   0x0000000000000000
        .quad   0x0015000300000000
        .quad   0x0000000000020020
        .quad   0x0000000000000000
        .quad   0x0000001200000055
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000002000000010
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000002200000046
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000120000005c
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000002000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000200000002c
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000b001200000086
        .quad   0x0000000000007520
        .quad   0x0000000000000004
        .quad   0x000b001200000063
        .quad   0x0000000000007510
        .quad   0x0000000000000004
        .quad   0x000b0012000000a2
        .quad   0x0000000000007530
        .quad   0x000000000000000c
        .quad   0x000b001200000076
        .quad   0x0000000000007514
        .quad   0x0000000000000004
        .quad   0x000b001200000095
        .quad   0x0000000000007524
        .quad   0x000000000000000c
        .quad   0x5f6e6f6d675f5f00
        .quad   0x005f5f7472617473
        .quad   0x7265645f4d54495f
        .quad   0x5472657473696765
        .quad   0x6154656e6f6c434d
        .quad   0x4d54495f00656c62
        .quad   0x657473696765725f
        .quad   0x656e6f6c434d5472
        .quad   0x5f5f00656c626154
        .quad   0x616e69665f617863
        .quad   0x6d656d00657a696c
        .quad   0x736d656d00797063
        .quad   0x5f6675687a007465
        .quad   0x6572706d6f636564
        .quad   0x687a003178317373
        .quad   0x6e646165725f6675
        .quad   0x687a00746e756f63
        .quad   0x73646165725f6675
        .quad   0x75687a0073746174
        .quad   0x6f72726573695f66
        .quad   0x655f6675687a0072
        .quad   0x656d616e726f7272
        .quad   0x6f732e6362696c00
        .quad   0x737a62696c00362e
        .quad   0x732e6675685f6474
        .quad   0x5f4342494c47006f
        .quad   0x696e2f0037312e32
        .quad   0x2f65726f74732f78
        .quad   0x6134723633716161
        .quad   0x6d30687362663934
        .quad   0x32767a696a627762
        .quad   0x6d7a717a3468726a
        .quad   0x322d6362696c672d
        .quad   0x6c2f32352d39332e
        .quad   0x2f78696e2f3a6269
        .quad   0x376c2f65726f7473
        .quad   0x39397a7762676b38
        .quad   0x6e37763379663939
        .quad   0x79796a6271676172
        .quad   0x672d336d64363039
        .quad   0x2e332e32312d6363
        .quad   0x696c2f62696c2d30
        .quad   0x0000000000000062
        .quad   0x0002000200010002
        .quad   0x0001000100010001
        .quad   0x0000000100010001
        .quad   0x000000b100010001
        .quad   0x0000000000000010
        .quad   0x0002000006969197
        .quad   0x00000000000000ca
        .quad   0x000000000001fdc0
        .quad   0x0000000000000403
        .quad   0x0000000000000760
        .quad   0x000000000001fdc8
        .quad   0x0000000000000403
        .quad   0x0000000000000710
        .quad   0x0000000000020020
        .quad   0x0000000000000403
        .quad   0x0000000000020020
        .quad   0x000000000001ffc8
        .quad   0x0000000400000401
        .quad   0x0000000000000000
        .quad   0x000000000001ffd0
        .quad   0x0000000500000401
        .quad   0x0000000000000000
        .quad   0x000000000001ffd8
        .quad   0x0000000700000401
        .quad   0x0000000000000000
        .quad   0x000000000001ffe0
        .quad   0x0000000800000401
        .quad   0x0000000000000000
        .quad   0x0000000000020000
        .quad   0x0000000300000402
        .quad   0x0000000000000000
        .quad   0x0000000000020008
        .quad   0x0000000500000402
        .quad   0x0000000000000000
        .quad   0x0000000000020010
        .quad   0x0000000600000402
        .quad   0x0000000000000000
        .quad   0x0000000000020018
        .quad   0x0000000700000402
        .quad   0x0000000000000000
// _init (0x0 bytes)
        .quad   0xa9bf7bfdd503201f
        .quad   0x9400001d910003fd
        .quad   0xd65f03c0a8c17bfd
        .quad   0x0000000000000000

// The procedure linkage table and the code (0x620 to 0x753c)
// .plt
        stp     x16, x30, [sp, #-16]!
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4088]
        add     x16, x16, #0xff8
        br      x17
        nop
        nop
        nop
L0640:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16]
        add     x16, x16, #0x0
        br      x17
L0650:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16, #8]
        add     x16, x16, #0x8
        br      x17
L0660:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16, #16]
        add     x16, x16, #0x10
        br      x17
L0670:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16, #24]
        add     x16, x16, #0x18
        br      x17

// call_weak_fn (0x14 bytes)
L0680:
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4056]
        cbz     x0,L0690
        b       L0670
L0690:
        ret
        nop
        nop
        nop

// deregister_tm_clones (0x0 bytes)
L06a0:
        .inst   0x90000100  // adrp x0, 0x20000
        add     x0, x0, #0x28
        .inst   0x90000101  // adrp x1, 0x20000
        add     x1, x1, #0x28
        cmp     x1, x0
        b.eq    L06cc
        .inst   0xf00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4040]
        cbz     x1,L06cc
        mov     x16, x1
        br      x16
L06cc:
        ret

// register_tm_clones (0x0 bytes)
L06d0:
        .inst   0x90000100  // adrp x0, 0x20000
        add     x0, x0, #0x28
        .inst   0x90000101  // adrp x1, 0x20000
        add     x1, x1, #0x28
        sub     x1, x1, x0
        lsr     x2, x1, #63
        add     x1, x2, x1, asr #3
        asr     x1, x1, #1
        cbz     x1,L0708
        .inst   0xf00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4064]
        cbz     x2,L0708
        mov     x16, x2
        br      x16
L0708:
        ret
        nop

// __do_global_dtors_aux (0x0 bytes)
L0710:
        stp     x29, x30, [sp, #-32]!
        mov     x29, sp
        str     x19, [sp, #16]
        .inst   0x90000113  // adrp x19, 0x20000
        ldrb    w0, [x19, #40]
        cbnz    w0,L074c
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4048]
        cbz     x0,L0740
        .inst   0x90000100  // adrp x0, 0x20000
        ldr     x0, [x0, #32]
        bl      L0650
L0740:
        bl      L06a0
        mov     w0, #0x1
        strb    w0, [x19, #40]
L074c:
        ldr     x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
        nop
        nop

// frame_dummy (0x0 bytes)
L0760:
        b       L06d0
        nop
        nop
        nop

// HUF_readStats_body_default (0x1d0 bytes)
L0770:
        cbz     x6,L08c0
        stp     x29, x30, [sp, #-64]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x20, x2
        mov     x19, x0
        stp     x21, x22, [sp, #32]
        mov     x22, x3
        mov     x21, x4
        str     x23, [sp, #48]
        mov     x2, x5
        ldrb    w3, [x5]
        cmp     x3, #0x7f
        b.ls    L0870
        sub     x0, x3, #0x7e
        sub     x8, x3, #0x7f
        lsr     x3, x0, #1
        add     x23, x3, #0x1
        cmp     x6, x23
        b.cc    L0938
        cmp     x1, x8
        b.ls    L0854
        add     x3, x19, #0x1
        mov     x1, #0x0
L07d0:
        lsr     w6, w1, #1
        add     w6, w6, #0x1
        ldrb    w0, [x2, w6, uxtw]
        lsr     w0, w0, #4
        strb    w0, [x19, x1]
        ldrb    w0, [x2, w6, uxtw]
        and     w0, w0, #0xf
        strb    w0, [x3, x1]
        add     x1, x1, #0x2
        cmp     x8, x1
        b.hi    L07d0
        movi    v0.4s, #0x0
        str     wzr, [x20, #48]
        stp     q0, q0, [x20]
        str     q0, [x20, #32]
L080c:
        mov     w2, #0x0
        mov     w0, #0x0
        mov     x1, #0x0
        mov     w3, #0x1
        b       L0844
L0820:
        ldr     w5, [x20, x6, lsl #2]
        add     w5, w5, #0x1
        str     w5, [x20, x6, lsl #2]
        ldrb    w5, [x19, x1]
        mov     w1, w2
        lsl     w5, w3, w5
        add     w0, w0, w5, asr #1
        cmp     x1, x8
        b.cs    L08cc
L0844:
        ldrb    w6, [x19, x1]
        add     w2, w2, #0x1
        cmp     w6, #0xc
        b.ls    L0820
L0854:
        mov     x8, #0xffffffffffffffec
L0858:
        ldp     x19, x20, [sp, #16]
        mov     x0, x8
        ldp     x21, x22, [sp, #32]
        ldr     x23, [sp, #48]
        ldp     x29, x30, [sp], #64
        ret
L0870:
        add     x23, x3, #0x1
        mov     x8, #0xffffffffffffffb8
        cmp     x6, x23
        b.cc    L0858
        ldr     x6, [sp, #64]
        mov     x5, x7
        add     x2, x2, #0x1
        sub     x1, x1, #0x1
        mov     w7, #0x0
        mov     w4, #0x6
        bl      L10f4
        mov     x8, x0
        cmn     x0, #0x78
        b.hi    L0858
        movi    v0.4s, #0x0
        str     wzr, [x20, #48]
        stp     q0, q0, [x20]
        str     q0, [x20, #32]
        cbnz    x0,L080c
        b       L0854
L08c0:
        mov     x8, #0xffffffffffffffb8
        mov     x0, x8
        ret
L08cc:
        cbz     w0,L0854
        clz     w1, w0
        mov     w2, #0x20
        sub     w1, w2, w1
        cmp     w1, #0xc
        b.hi    L0854
        lsl     w3, w3, w1
        sub     w0, w3, w0
        clz     w4, w0
        mov     w3, #0x80000000
        str     w1, [x21]
        lsr     w1, w3, w4
        cmp     w0, w1
        b.ne    L0854
        sub     w0, w2, w4
        strb    w0, [x19, x8]
        ldr     w1, [x20, x0, lsl #2]
        add     w1, w1, #0x1
        str     w1, [x20, x0, lsl #2]
        ldr     w0, [x20, #4]
        cmp     w0, #0x1
        b.ls    L0854
        tbnz    w0, #0,L0854
        add     w0, w8, #0x1
        mov     x8, x23
        str     w0, [x22]
        b       L0858
L0938:
        mov     x8, #0xffffffffffffffb8
        b       L0858

// FSE_readNCount_body_default (0x2cc bytes)
L0940:
        stp     x29, x30, [sp, #-80]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x20, x0
        ldr     w19, [x1]
        stp     x21, x22, [sp, #32]
        mov     x21, x1
        mov     x22, x3
        stp     x23, x24, [sp, #48]
        mov     x24, x4
        mov     x23, x2
        cmp     x4, #0x7
        b.hi    L09cc
        add     x3, sp, #0x48
        mov     x2, x4
        mov     x1, x22
        mov     x0, x3
        str     xzr, [sp, #72]
        bl      L0640
        mov     x3, x0
        mov     x2, x23
        mov     x1, x21
        mov     x0, x20
        mov     x4, #0x8
        bl      L0940
        cmp     x24, x0
        mov     x2, #0xffffffffffffff88
        ccmp    x0, x2, #0x2, cc
        mov     x1, #0xffffffffffffffec
        csel    x0, x0, x1, hi
L09b8:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x29, x30, [sp], #80
        ret
L09cc:
        add     w2, w19, #0x1
        mov     w1, #0x0
        add     w19, w19, #0x1
        lsl     x2, x2, #1
        bl      L0660
        ldr     w4, [x22]
        mov     x0, #0xffffffffffffffd4
        and     w10, w4, #0xf
        add     w2, w10, #0x5
        cmp     w2, #0xf
        b.hi    L09b8
        add     x1, x22, x24
        mov     w3, #0x1
        lsl     w9, w3, w2
        lsr     w4, w4, #4
        add     w10, w10, #0x6
        sub     x0, x1, #0x7
        add     w8, w9, w3
        sub     x13, x1, #0x4
        mov     x5, x22
        mov     w6, #0x0
        mov     w14, #0x4
        mov     w12, #0x20
        mov     w11, #0x1f
        str     w2, [x23]
L0a30:
        lsl     w7, w9, #1
        sub     w2, w9, #0x1
        sub     w7, w7, #0x1
        and     w2, w2, w4
        sub     w15, w7, w8
        cmp     w2, w15
        b.cs    L0ad4
L0a4c:
        sub     w4, w10, #0x1
        add     w4, w4, w14
L0a54:
        subs    w2, w2, #0x1
        strh    w2, [x20, w6, uxtw #1]
        sub     w7, w8, w2
        add     w8, w8, w2
        csel    w8, w8, w7, mi
        add     w6, w6, #0x1
        cmp     w8, w9
        b.ge    L0a8c
        cmp     w8, #0x1
        b.le    L0b9c
        clz     w10, w8
        sub     w9, w11, w10
        sub     w10, w12, w10
        lsl     w9, w3, w9
L0a8c:
        cmp     w19, w6
        b.ls    L0b9c
        asr     w7, w4, #3
        add     x7, x5, w7, sxtw
        cmp     x5, x0
        b.hi    L0b80
L0aa4:
        and     w14, w4, #0x7
        mov     x5, x7
L0aac:
        ldr     w4, [x5]
        lsr     w4, w4, w14
        cbz     w2,L0b04
        lsl     w7, w9, #1
        sub     w2, w9, #0x1
        sub     w7, w7, #0x1
        and     w2, w2, w4
        sub     w15, w7, w8
        cmp     w2, w15
        b.cc    L0a4c
L0ad4:
        and     w2, w7, w4
        add     w4, w14, w10
        sub     w15, w2, w15
        cmp     w2, w9
        csel    w2, w15, w2, ge
        b       L0a54
L0aec:
        add     w6, w6, #0x24
        cmp     x5, x0
        b.hi    L0b6c
        add     x5, x5, #0x3
L0afc:
        ldr     w4, [x5]
        lsr     w4, w4, w14
L0b04:
        mvn     w2, w4
        orr     w2, w2, #0x80000000
        rbit    w2, w2
        clz     w2, w2
        lsr     w7, w2, #1
        cmp     w2, #0x17
        b.hi    L0aec
        lsl     w2, w7, #1
        mov     x15, x5
        add     w7, w2, w7
        add     w14, w2, w14
        add     w7, w7, w6
        lsr     w2, w4, w2
        and     w2, w2, #0x3
        add     w4, w14, #0x2
        add     w6, w2, w7
        cmp     w19, w6
        b.ls    L0b9c
        asr     w2, w4, #3
        add     x5, x5, w2, sxtw
        cmp     x15, x0
        b.hi    L0bec
L0b5c:
        and     w14, w4, #0x7
L0b60:
        ldr     w4, [x5]
        lsr     w4, w4, w14
        b       L0a30
L0b6c:
        sub     x2, x0, x5
        sub     x5, x1, #0x4
        sub     w2, w14, w2, lsl #3
        and     w14, w2, #0x1f
        b       L0afc
L0b80:
        cmp     x13, x7
        b.cs    L0aa4
        sub     x14, x13, x5
        mov     x5, x13
        sub     w14, w4, w14, lsl #3
        and     w14, w14, #0x1f
        b       L0aac
L0b9c:
        mov     x0, #0xffffffffffffffec
        cmp     w8, #0x1
        b.ne    L09b8
        mov     x0, #0xffffffffffffffd0
        cmp     w19, w6
        b.cc    L09b8
        mov     x0, #0xffffffffffffffec
        cmp     w4, #0x20
        b.gt    L09b8
        add     w0, w4, #0x7
        sub     w6, w6, #0x1
        str     w6, [x21]
        asr     w0, w0, #3
        ldp     x19, x20, [sp, #16]
        add     x0, x5, w0, sxtw
        ldp     x23, x24, [sp, #48]
        sub     x0, x0, x22
        ldp     x21, x22, [sp, #32]
        ldp     x29, x30, [sp], #80
        ret
L0bec:
        sub     x7, x1, #0x4
        cmp     x7, x5
        b.cs    L0b5c
        sub     x2, x7, x15
        mov     x5, x7
        sub     w2, w4, w2, lsl #3
        and     w14, w2, #0x1f
        b       L0b60
        nop

// FSE_versionNumber (0x8 bytes)
L0c10:
        mov     w0, #0x384
        ret
        nop
        nop

// FSE_isError (0xc bytes)
L0c20:
        cmn     x0, #0x78
        cset    w0, hi
        ret
        nop

// FSE_getErrorName (0xc bytes)
L0c30:
        cmn     x0, #0x78
        csneg   w0, wzr, w0, ls
        b       L0cb0
        nop

// HUF_isError (0xc bytes)
L0c40:
        cmn     x0, #0x78
        cset    w0, hi
        ret
        nop

// HUF_getErrorName (0xc bytes)
L0c50:
        cmn     x0, #0x78
        csneg   w0, wzr, w0, ls
        b       L0cb0
        nop

// FSE_readNCount_bmi2 (0x4 bytes)
L0c60:
        b       L0940

// FSE_readNCount (0x4 bytes)
L0c64:
        b       L0940
        nop
        nop

// HUF_readStats (0x28 bytes)
L0c70:
        sub     sp, sp, #0x390
        mov     x7, #0x36c
        stp     x29, x30, [sp, #16]
        add     x29, sp, #0x10
        str     x7, [sp]
        add     x7, sp, #0x20
        bl      L0770
        ldp     x29, x30, [sp, #16]
        add     sp, sp, #0x390
        ret
        nop
        nop

// HUF_readStats_wksp (0x4 bytes)
L0ca0:
        b       L0770
        nop
        nop
        nop

// ERR_getErrorString (0x1d0 bytes)
L0cb0:
        cmp     w0, #0x6b
        b.ls    L0cc4
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0xad0
        ret
L0cc4:
        .inst   0xf0000021  // adrp x1, 0x7000
        add     x1, x1, #0xae8
        ldrb    w1, [x1, w0, uxtw]
        .inst   0x10000060  // adr x0, 0xcdc
        add     x1, x0, w1, sxtb #2
        br      x1
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0xaa8
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0xa68
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0xa50
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0xa30
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0xa00
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x9e0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x990
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x940
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x918
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x900
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x8e0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x730
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x708
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x6e8
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x758
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x848
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x818
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x7f0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x7c0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x790
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x6c8
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x6a0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x688
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x8b0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x898
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x880
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x648
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x620
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x600
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x5d0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x5b0
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x598
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x578
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x568
        ret
        .inst   0xf0000020  // adrp x0, 0x7000
        add     x0, x0, #0x550
        ret

// FSE_buildDTable_internal (0x268 bytes)
L0e80:
        mov     w16, w2
        mov     x7, #0x1
        add     w6, w16, #0x1
        lsl     x8, x7, x3
        add     x8, x8, #0x8
        mov     x14, x0
        add     x6, x8, x6, lsl #1
        add     x17, x16, x7
        cmp     x6, x5
        mov     x0, #0xffffffffffffffd2
        cset    w10, hi
        cmp     w2, #0xff
        cset    w5, hi
        orr     w10, w10, w5
        cbnz    w10,L1030
        mov     x0, #0xffffffffffffffd4
        cmp     w3, #0xc
        b.hi    L1030
        sub     w0, w3, #0x1
        mov     w13, w3
        lsl     w15, w7, w3
        mov     w12, w7
        sub     w6, w15, #0x1
        lsl     w7, w7, w0
        sxth    w11, w7
        mov     w5, w6
        add     x9, x14, #0x4
        movk    w13, #0x1, lsl #16
        mov     x7, #0x0
        b       L0f18
L0ef8:
        cmp     w8, w11
        strh    w0, [x4, x7, lsl #1]
        csel    w12, w12, wzr, lt
        add     x0, x7, #0x1
        mov     w10, #0x1
        cmp     x16, x7
        b.eq    L0f48
L0f14:
        mov     x7, x0
L0f18:
        ldrsh   w8, [x1, x7, lsl #1]
        and     w0, w8, #0xffff
        cmn     w8, #0x1
        b.ne    L0ef8
        add     x8, x9, w5, uxtw #2
        mov     w0, #0x1
        sub     w5, w5, #0x1
        strb    w7, [x8, #2]
        strh    w0, [x4, x7, lsl #1]
        add     x0, x7, #0x1
        cmp     x16, x7
        b.ne    L0f14
L0f48:
        cbz     w10,L0f50
        bfi     w13, w12, #16, #16
L0f50:
        str     w13, [x14]
        cmp     w5, w6
        b.eq    L1034
        lsr     w7, w15, #3
        mov     x13, #0x0
        add     w7, w7, w15, lsr #1
        mov     w2, #0x0
        add     w7, w7, #0x3
L0f70:
        ldrsh   w11, [x1, x13, lsl #1]
        and     w12, w13, #0xff
        mov     w8, #0x0
        cmp     w11, #0x0
        b.le    L0fbc
        nop
L0f88:
        add     x10, x9, w2, uxtw #2
        add     w2, w2, w7
        and     w2, w2, w6
        strb    w12, [x10, #2]
        cmp     w5, w2
        b.cs    L0fb0
L0fa0:
        add     w2, w2, w7
        and     w2, w2, w6
        cmp     w5, w2
        b.cc    L0fa0
L0fb0:
        add     w8, w8, #0x1
        cmp     w8, w11
        b.ne    L0f88
L0fbc:
        add     x0, x13, #0x1
        cmp     x16, x13
        b.eq    L0fd0
        mov     x13, x0
        b       L0f70
L0fd0:
        mov     x0, #0xffffffffffffffff
        cbnz    w2,L1030
L0fd8:
        add     x14, x14, #0x8
        and     w3, w3, #0xff
        add     x6, x14, w6, uxtw #2
        and     w15, w15, #0xffff
        mov     w7, #0x1f
        nop
L0ff0:
        ldrb    w2, [x9, #2]
        lsl     x2, x2, #1
        ldrh    w1, [x4, x2]
        clz     w0, w1
        add     w5, w1, #0x1
        sub     w0, w7, w0
        strh    w5, [x4, x2]
        sub     w0, w3, w0
        and     w0, w0, #0xff
        strb    w0, [x9, #3]
        lsl     w0, w1, w0
        sub     w0, w0, w15
        strh    w0, [x9], #4
        cmp     x6, x9
        b.ne    L0ff0
        mov     x0, #0x0
L1030:
        ret
L1034:
        lsr     w13, w15, #3
        add     x0, x1, #0x2
        add     w13, w13, w15, lsr #1
        mov     x7, x1
        add     x10, x4, x17, lsl #1
        add     w13, w13, #0x3
        mov     w12, w6
        add     x11, x0, w2, uxtw #1
        mov     x16, #0x101010101010101
        mov     x2, #0x0
        mov     x0, #0x0
L1060:
        ldrsh   w5, [x7]
        add     x8, x10, x0
        str     x2, [x10, x0]
        mov     x1, #0x8
        cmp     w5, #0x8
        b.le    L1088
L1078:
        str     x2, [x8, x1]
        add     x1, x1, #0x8
        cmp     w5, w1
        b.gt    L1078
L1088:
        add     x7, x7, #0x2
        add     x0, x0, w5, sxtw
        add     x2, x2, x16
        cmp     x11, x7
        b.ne    L1060
        sxtw    x11, w15
        add     x8, x10, #0x1
        mov     x0, #0x0
        mov     x1, #0x0
L10ac:
        and     x5, x12, x1
        add     x1, x13, x1
        and     x2, x12, x1
        ldrb    w7, [x10, x0]
        add     x5, x9, x5, lsl #2
        add     x1, x13, x1
        add     x2, x9, x2, lsl #2
        and     x1, x1, x12
        strb    w7, [x5, #2]
        ldrb    w5, [x8, x0]
        add     x0, x0, #0x2
        strb    w5, [x2, #2]
        cmp     x11, x0
        b.hi    L10ac
        b       L0fd8
        nop
        nop

// FSE_buildDTable_wksp (0x4 bytes)
L10f0:
        b       L0e80

// FSE_decompress_wksp_bmi2 (0xb2c bytes)
L10f4:
        stp     x29, x30, [sp, #-96]!
        mov     x18, #0xffffffffffffffff
        mov     x29, sp
        str     x25, [sp, #64]
        mov     x25, x6
        mov     w6, #0xff
        str     w6, [sp, #92]
        cmp     x25, #0x1ff
        b.ls    L1588
        stp     x19, x20, [sp, #16]
        mov     x19, x5
        mov     x20, x2
        mov     w5, #0x0
        stp     x21, x22, [sp, #32]
        mov     x21, x1
        mov     x22, x3
        add     x1, sp, #0x5c
        stp     x23, x24, [sp, #48]
        mov     x23, x0
        mov     w24, w4
        mov     x0, x19
        mov     x4, x3
        mov     x3, x2
        add     x2, sp, #0x58
        bl      L0c60
        mov     x18, x0
        cmn     x0, #0x78
        b.hi    L157c
        ldr     w3, [sp, #88]
        cmp     w24, w3
        b.cc    L1598
        ldr     w2, [sp, #92]
        mov     w4, #0x1
        mov     x1, #0x1
        lsl     w4, w4, w3
        add     w0, w2, #0x1
        lsl     x1, x1, x3
        add     x1, x1, #0xb
        sxtw    x4, w4
        add     x0, x1, w0, uxtw #1
        add     x1, x4, #0x83
        add     x0, x1, x0, lsr #2
        cmp     x25, x0, lsl #2
        b.cc    L1598
        add     x4, x4, #0x81
        mov     x1, x19
        add     x0, x19, #0x200
        lsl     x4, x4, #2
        sub     x5, x25, x4
        add     x4, x19, x4
        bl      L0e80
        cmn     x0, #0x78
        b.hi    L15b8
        ldrh    w0, [x19, #514]
        add     x21, x23, x21
        add     x20, x20, x18
        sub     x5, x21, #0x3
        sub     x18, x22, x18
        cbnz    w0,L163c
        cbz     x18,L1b24
        add     x0, x20, x18
        ldurb   w0, [x0, #-1]
        cmp     x18, #0x7
        b.ls    L15cc
        cbz     w0,L1a10
        cmn     x18, #0x78
        b.hi    L157c
        sub     x18, x18, #0x8
        clz     w0, w0
        sub     w2, w0, #0x17
        add     x9, x20, x18
        ldr     x7, [x20, x18]
L1214:
        .inst   0xd0000026  // adrp x6, 0x7000
        ldrh    w4, [x19, #512]
        add     x0, x6, #0xb60
        add     x0, x0, #0x10
        add     w2, w2, w4
        mov     x1, x4
        neg     w3, w2
        ldr     w10, [x0, x4, lsl #2]
        lsr     x3, x7, x3
        and     x3, x3, x10
        cmp     w2, #0x40
        b.hi    L19d8
        add     x8, x20, #0x8
        cmp     x8, x9
        b.ls    L1bac
        mov     x4, x20
        cmp     x20, x9
        b.eq    L1284
        lsr     w4, w2, #3
        lsr     w0, w2, #3
        sub     x4, x9, x4
        cmp     x20, x4
        b.ls    L127c
        sub     x4, x9, x20
        mov     w0, w4
        sub     x4, x9, w4, uxtw
L127c:
        ldr     x7, [x4]
        sub     w2, w2, w0, lsl #3
L1284:
        add     w2, w2, w1
        add     x19, x19, #0x204
        neg     w0, w2
        lsr     x0, x7, x0
        and     x12, x0, x10
        cmp     w2, #0x40
        b.hi    L19d8
        cmp     x4, x8
        b.cs    L1b98
        cmp     x20, x4
        b.eq    L1320
        lsr     w0, w2, #3
        lsr     w1, w2, #3
        sub     x0, x4, x0
        cmp     x20, x0
        b.ls    L12d0
        sub     x0, x4, x20
        mov     w1, w0
        sub     x0, x4, w0, uxtw
L12d0:
        sub     w2, w2, w1, lsl #3
        ldr     x7, [x0]
        cmp     w2, #0x40
        b.hi    L19d8
L12e0:
        cmp     x8, x0
        b.ls    L1bc0
        cmp     x20, x0
        b.eq    L1c10
        lsr     w4, w2, #3
        lsr     w1, w2, #3
        sub     x4, x0, x4
        cmp     x20, x4
        b.ls    L1310
        sub     x4, x0, x20
        mov     w1, w4
        sub     x4, x0, w4, uxtw
L1310:
        sub     w2, w2, w1, lsl #3
        ldr     x7, [x4]
        cmp     w2, #0x40
        b.hi    L1a00
L1320:
        add     x10, x6, #0xb60
        mov     x9, x23
        add     x10, x10, #0x10
        b       L1414
L1330:
        ldr     x7, [x1]
        cmp     x9, x5
        sub     w2, w2, w0, lsl #3
        cset    w11, cc
        mov     x4, x1
L1344:
        lsl     x0, x3, #2
        lsl     x13, x12, #2
        add     x1, x19, x0
        add     x14, x19, x13
        cbz     w11,L144c
        ldrb    w3, [x1, #3]
        add     x9, x9, #0x4
        ldrb    w1, [x1, #2]
        ldrh    w12, [x19, x0]
        add     w0, w3, w2
        sturb   w1, [x9, #-4]
        neg     w1, w0
        ldr     w15, [x10, x3, lsl #2]
        ldrb    w11, [x14, #3]
        lsr     x1, x7, x1
        and     x1, x1, x15
        ldrh    w2, [x19, x13]
        add     w3, w11, w0
        add     x1, x1, x12
        neg     w0, w3
        ldr     w11, [x10, x11, lsl #2]
        lsl     x1, x1, #2
        lsr     x0, x7, x0
        and     x0, x0, x11
        ldrb    w11, [x14, #2]
        add     x0, x0, x2
        add     x2, x19, x1
        sturb   w11, [x9, #-3]
        lsl     x0, x0, #2
        ldrb    w12, [x2, #2]
        add     x11, x19, x0
        ldrb    w14, [x2, #3]
        ldrh    w13, [x19, x1]
        sturb   w12, [x9, #-2]
        add     w1, w14, w3
        neg     w3, w1
        ldrb    w15, [x11, #3]
        ldrh    w12, [x19, x0]
        lsr     x3, x7, x3
        add     w2, w15, w1
        ldr     w14, [x10, x14, lsl #2]
        neg     w0, w2
        ldrb    w11, [x11, #2]
        ldr     w1, [x10, x15, lsl #2]
        and     x3, x3, x14
        lsr     x0, x7, x0
        sturb   w11, [x9, #-1]
        and     x0, x0, x1
        add     x3, x3, x13
        add     x12, x0, x12
        cmp     w2, #0x40
        b.hi    L1a08
L1414:
        lsr     w1, w2, #3
        cmp     x4, x8
        b.cs    L1624
        sub     x1, x4, x1
        cmp     x20, x4
        b.eq    L144c
        lsr     w0, w2, #3
        cmp     x20, x1
        b.ls    L1330
        sub     w1, w4, w20
        sub     x0, x4, x20
        sub     x4, x4, x1
        sub     w2, w2, w0, lsl #3
        ldr     x7, [x4]
L144c:
        sub     x10, x21, #0x2
        cmp     x9, x10
        b.hi    L1b38
        sub     x21, x21, #0x1
        add     x6, x6, #0xb60
        sub     x0, x21, x9
        add     x6, x6, #0x10
        and     x0, x0, #0xfffffffffffffffe
        add     x11, x9, x0
L1470:
        lsl     x3, x3, #2
        add     x5, x19, x3
        ldrh    w13, [x19, x3]
        ldrb    w1, [x5, #3]
        ldrb    w14, [x5, #2]
        mov     w5, w1
        add     w0, w1, w2
        neg     w3, w0
        strb    w14, [x9]
        ldr     w1, [x6, x5, lsl #2]
        lsr     x3, x7, x3
        and     x3, x3, x1
        add     x3, x3, x13
        cmp     w0, #0x40
        b.hi    L1a3c
        cmp     x8, x4
        b.ls    L19c4
        mov     x1, x20
        cmp     x20, x4
        b.eq    L14e8
        lsr     w1, w0, #3
        lsr     w2, w0, #3
        sub     x1, x4, x1
        cmp     x20, x1
        b.ls    L14e0
        sub     x1, x4, x20
        mov     w2, w1
        sub     x1, x4, w1, uxtw
L14e0:
        ldr     x7, [x1]
        sub     w0, w0, w2, lsl #3
L14e8:
        cmp     x9, x11
        b.eq    L1b38
        lsl     x12, x12, #2
        add     x5, x9, #0x2
        add     x4, x19, x12
        ldrh    w12, [x19, x12]
        ldrb    w2, [x4, #3]
        ldrb    w13, [x4, #2]
        mov     w4, w2
        add     w2, w2, w0
        neg     w0, w2
        sturb   w13, [x5, #-1]
        ldr     w4, [x6, x4, lsl #2]
        lsr     x0, x7, x0
        and     x0, x0, x4
        add     x12, x0, x12
        cmp     w2, #0x40
        b.hi    L1ad8
        cmp     x8, x1
        b.ls    L19ec
        mov     x4, x20
        cmp     x20, x1
        b.eq    L156c
        lsr     w4, w2, #3
        lsr     w0, w2, #3
        sub     x4, x1, x4
        cmp     x20, x4
        b.ls    L1564
        sub     x4, x1, x20
        mov     w0, w4
        sub     x4, x1, w4, uxtw
L1564:
        ldr     x7, [x4]
        sub     w2, w2, w0, lsl #3
L156c:
        cmp     x5, x10
        b.hi    L1b38
        mov     x9, x5
        b       L1470
L157c:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
L1588:
        mov     x0, x18
        ldr     x25, [sp, #64]
        ldp     x29, x30, [sp], #96
        ret
L1598:
        ldp     x19, x20, [sp, #16]
        mov     x18, #0xffffffffffffffd4
        ldp     x21, x22, [sp, #32]
        mov     x0, x18
        ldp     x23, x24, [sp, #48]
        ldr     x25, [sp, #64]
        ldp     x29, x30, [sp], #96
        ret
L15b8:
        ldp     x19, x20, [sp, #16]
        mov     x18, x0
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        b       L1588
L15cc:
        ldrb    w7, [x20]
        cmp     x18, #0x5
        b.eq    L1b18
        b.hi    L1b00
        cmp     x18, #0x3
        b.eq    L15f4
        cmp     x18, #0x4
        b.ne    L19b8
L15ec:
        ldrb    w1, [x20, #3]
        add     x7, x7, x1, lsl #24
L15f4:
        ldrb    w1, [x20, #2]
        add     x7, x7, x1, lsl #16
L15fc:
        ldrb    w1, [x20, #1]
        add     x7, x7, x1, lsl #8
L1604:
        cbz     w0,L19d8
        mov     w2, #0x8
        sub     w2, w2, w18
        clz     w0, w0
        mov     x9, x20
        add     w2, w0, w2, lsl #3
        sub     w2, w2, #0x17
        b       L1214
L1624:
        sub     x4, x4, x1
        cmp     x9, x5
        and     w2, w2, #0x7
        cset    w11, cc
        ldr     x7, [x4]
        b       L1344
L163c:
        cbz     x18,L1b24
        add     x0, x20, x18
        ldurb   w0, [x0, #-1]
        cmp     x18, #0x7
        b.ls    L1a60
        cbz     w0,L1a10
        cmn     x18, #0x78
        b.hi    L157c
        sub     x18, x18, #0x8
        clz     w0, w0
        sub     w2, w0, #0x17
        add     x4, x20, x18
        ldr     x8, [x20, x18]
L1670:
        .inst   0xd0000026  // adrp x6, 0x7000
        ldrh    w7, [x19, #512]
        add     x3, x6, #0xb60
        add     x3, x3, #0x10
        add     w2, w7, w2
        mov     x1, x7
        neg     w0, w2
        ldr     w3, [x3, x7, lsl #2]
        lsr     x0, x8, x0
        and     x0, x0, x3
        cmp     w2, #0x40
        b.hi    L19d8
        add     x12, x20, #0x8
        cmp     x12, x4
        b.ls    L1bfc
        mov     x9, x20
        cmp     x20, x4
        b.eq    L16e0
        lsr     w9, w2, #3
        lsr     w7, w2, #3
        sub     x9, x4, x9
        cmp     x20, x9
        b.ls    L16d8
        sub     x9, x4, x20
        mov     w7, w9
        sub     x9, x4, w9, uxtw
L16d8:
        ldr     x8, [x9]
        sub     w2, w2, w7, lsl #3
L16e0:
        add     w1, w1, w2
        add     x19, x19, #0x204
        neg     w2, w1
        lsr     x2, x8, x2
        and     x13, x2, x3
        cmp     w1, #0x40
        b.hi    L19d8
        cmp     x12, x9
        b.ls    L1be8
        cmp     x20, x9
        b.eq    L177c
        lsr     w2, w1, #3
        lsr     w3, w1, #3
        sub     x2, x9, x2
        cmp     x20, x2
        b.ls    L172c
        sub     x2, x9, x20
        mov     w3, w2
        sub     x2, x9, w2, uxtw
L172c:
        sub     w1, w1, w3, lsl #3
        ldr     x8, [x2]
        cmp     w1, #0x40
        b.hi    L19d8
L173c:
        cmp     x12, x2
        b.ls    L1bd4
        cmp     x20, x2
        b.eq    L1c18
        lsr     w9, w1, #3
        lsr     w3, w1, #3
        sub     x9, x2, x9
        cmp     x20, x9
        b.ls    L176c
        sub     x9, x2, x20
        mov     w3, w9
        sub     x9, x2, w9, uxtw
L176c:
        sub     w1, w1, w3, lsl #3
        ldr     x8, [x9]
        cmp     w1, #0x40
        b.hi    L19a8
L177c:
        mov     x10, x23
        b       L1858
L1784:
        ldr     x8, [x3]
        cmp     x10, x5
        sub     w1, w1, w2, lsl #3
        cset    w11, cc
        mov     x9, x3
L1798:
        lsl     x4, x0, #2
        lsl     x3, x13, #2
        add     x7, x19, x4
        add     x14, x19, x3
        lsl     x2, x8, x1
        cbz     w11,L1890
        ldrb    w0, [x7, #3]
        add     x10, x10, #0x4
        ldrb    w7, [x7, #2]
        ldrh    w4, [x19, x4]
        sturb   w7, [x10, #-4]
        neg     w7, w0
        add     w0, w0, w1
        ldrb    w1, [x14, #3]
        lsr     x2, x2, x7
        add     x2, x2, x4
        ldrh    w11, [x19, x3]
        neg     w4, w1
        lsl     x3, x8, x0
        lsl     x2, x2, #2
        ldrb    w7, [x14, #2]
        lsr     x3, x3, x4
        add     x4, x19, x2
        add     x3, x3, x11
        sturb   w7, [x10, #-3]
        add     w1, w1, w0
        lsl     x3, x3, #2
        ldrb    w13, [x4, #2]
        add     x7, x19, x3
        ldrh    w11, [x19, x2]
        ldrb    w4, [x4, #3]
        lsl     x0, x8, x1
        sturb   w13, [x10, #-2]
        add     w2, w4, w1
        neg     w4, w4
        ldrb    w1, [x7, #3]
        ldrh    w13, [x19, x3]
        lsl     x3, x8, x2
        ldrb    w14, [x7, #2]
        neg     w7, w1
        add     w1, w1, w2
        sturb   w14, [x10, #-1]
        lsr     x2, x3, x7
        add     x13, x2, x13
        lsr     x0, x0, x4
        add     x0, x0, x11
        cmp     w1, #0x40
        b.hi    L19b0
L1858:
        lsr     w3, w1, #3
        cmp     x9, x12
        b.cs    L1a24
        sub     x3, x9, x3
        cmp     x20, x9
        b.eq    L1890
        lsr     w2, w1, #3
        cmp     x20, x3
        b.ls    L1784
        sub     w3, w9, w20
        sub     x2, x9, x20
        sub     x9, x9, x3
        sub     w1, w1, w2, lsl #3
        ldr     x8, [x9]
L1890:
        sub     x7, x21, #0x2
        cmp     x10, x7
        b.hi    L1b38
        sub     x6, x21, #0x1
        sub     x6, x6, x10
        and     x6, x6, #0xfffffffffffffffe
        add     x6, x10, x6
L18ac:
        lsl     x0, x0, #2
        lsl     x2, x8, x1
        add     x4, x19, x0
        ldrh    w0, [x19, x0]
        ldrb    w3, [x4, #3]
        ldrb    w5, [x4, #2]
        neg     w4, w3
        add     w3, w1, w3
        strb    w5, [x10]
        lsr     x1, x2, x4
        add     x0, x1, x0
        cmp     w3, #0x40
        b.hi    L1b4c
        cmp     x12, x9
        b.ls    L1ac4
        mov     x2, x20
        cmp     x20, x9
        b.eq    L191c
        lsr     w2, w3, #3
        lsr     w1, w3, #3
        sub     x2, x9, x2
        cmp     x20, x2
        b.ls    L1914
        sub     x2, x9, x20
        mov     w1, w2
        sub     x2, x9, w2, uxtw
L1914:
        ldr     x8, [x2]
        sub     w3, w3, w1, lsl #3
L191c:
        cmp     x6, x10
        b.eq    L1b38
        lsl     x13, x13, #2
        add     x5, x10, #0x2
        add     x9, x19, x13
        lsl     x4, x8, x3
        ldrh    w13, [x19, x13]
        ldrb    w1, [x9, #3]
        ldrb    w11, [x9, #2]
        neg     w9, w1
        add     w1, w3, w1
        sturb   w11, [x5, #-1]
        lsr     x3, x4, x9
        add     x13, x3, x13
        cmp     w1, #0x40
        b.hi    L1b60
        cmp     x12, x2
        b.ls    L1aec
        mov     x9, x20
        cmp     x20, x2
        b.eq    L1998
        lsr     w9, w1, #3
        lsr     w3, w1, #3
        sub     x9, x2, x9
        cmp     x20, x9
        b.ls    L1990
        sub     x9, x2, x20
        mov     w3, w9
        sub     x9, x2, w9, uxtw
L1990:
        ldr     x8, [x9]
        sub     w1, w1, w3, lsl #3
L1998:
        cmp     x5, x7
        b.hi    L1b38
        mov     x10, x5
        b       L18ac
L19a8:
        mov     x10, x23
        nop
L19b0:
        add     x9, x6, #0xb60
        b       L1890
L19b8:
        cmp     x18, #0x2
        b.eq    L15fc
        b       L1604
L19c4:
        lsr     w1, w0, #3
        and     w0, w0, #0x7
        sub     x1, x4, x1
        ldr     x7, [x1]
        b       L14e8
L19d8:
        ldp     x19, x20, [sp, #16]
        mov     x18, #0xffffffffffffffec
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        b       L1588
L19ec:
        lsr     w4, w2, #3
        and     w2, w2, #0x7
        sub     x4, x1, x4
        ldr     x7, [x4]
        b       L156c
L1a00:
        mov     x9, x23
        nop
L1a08:
        add     x4, x6, #0xb60
        b       L144c
L1a10:
        ldp     x19, x20, [sp, #16]
        mov     x18, #0xffffffffffffffff
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        b       L1588
L1a24:
        sub     x9, x9, x3
        cmp     x10, x5
        and     w1, w1, #0x7
        cset    w11, cc
        ldr     x8, [x9]
        b       L1798
L1a3c:
        add     x0, x19, x12, lsl #2
        add     x18, x9, #0x2
        ldrb    w0, [x0, #2]
        strb    w0, [x9, #1]
L1a4c:
        ldp     x19, x20, [sp, #16]
        sub     x18, x18, x23
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        b       L1588
L1a60:
        ldrb    w8, [x20]
        cmp     x18, #0x5
        b.eq    L1b8c
        b.hi    L1b74
        cmp     x18, #0x3
        b.eq    L1a88
        cmp     x18, #0x4
        b.ne    L1ab8
L1a80:
        ldrb    w1, [x20, #3]
        add     x8, x8, x1, lsl #24
L1a88:
        ldrb    w1, [x20, #2]
        add     x8, x8, x1, lsl #16
L1a90:
        ldrb    w1, [x20, #1]
        add     x8, x8, x1, lsl #8
L1a98:
        cbz     w0,L19d8
        mov     w2, #0x8
        sub     w2, w2, w18
        clz     w0, w0
        mov     x4, x20
        add     w2, w0, w2, lsl #3
        sub     w2, w2, #0x17
        b       L1670
L1ab8:
        cmp     x18, #0x2
        b.eq    L1a90
        b       L1a98
L1ac4:
        lsr     w2, w3, #3
        and     w3, w3, #0x7
        sub     x2, x9, x2
        ldr     x8, [x2]
        b       L191c
L1ad8:
        add     x3, x19, x3, lsl #2
        add     x18, x9, #0x3
        ldrb    w0, [x3, #2]
        strb    w0, [x9, #2]
        b       L1a4c
L1aec:
        lsr     w9, w1, #3
        and     w1, w1, #0x7
        sub     x9, x2, x9
        ldr     x8, [x9]
        b       L1998
L1b00:
        cmp     x18, #0x6
        b.eq    L1b10
        ldrb    w1, [x20, #6]
        add     x7, x7, x1, lsl #48
L1b10:
        ldrb    w1, [x20, #5]
        add     x7, x7, x1, lsl #40
L1b18:
        ldrb    w1, [x20, #4]
        add     x7, x7, x1, lsl #32
        b       L15ec
L1b24:
        ldp     x19, x20, [sp, #16]
        mov     x18, #0xffffffffffffffb8
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        b       L1588
L1b38:
        ldp     x19, x20, [sp, #16]
        mov     x18, #0xffffffffffffffba
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        b       L1588
L1b4c:
        add     x2, x19, x13, lsl #2
        add     x18, x10, #0x2
        ldrb    w0, [x2, #2]
        strb    w0, [x10, #1]
        b       L1a4c
L1b60:
        add     x0, x19, x0, lsl #2
        add     x18, x10, #0x3
        ldrb    w0, [x0, #2]
        strb    w0, [x10, #2]
        b       L1a4c
L1b74:
        cmp     x18, #0x6
        b.eq    L1b84
        ldrb    w1, [x20, #6]
        add     x8, x8, x1, lsl #48
L1b84:
        ldrb    w1, [x20, #5]
        add     x8, x8, x1, lsl #40
L1b8c:
        ldrb    w1, [x20, #4]
        add     x8, x8, x1, lsl #32
        b       L1a80
L1b98:
        lsr     w0, w2, #3
        and     w2, w2, #0x7
        sub     x0, x4, x0
        ldr     x7, [x0]
        b       L12e0
L1bac:
        lsr     w4, w2, #3
        and     w2, w2, #0x7
        sub     x4, x9, x4
        ldr     x7, [x4]
        b       L1284
L1bc0:
        lsr     w4, w2, #3
        and     w2, w2, #0x7
        sub     x4, x0, x4
        ldr     x7, [x4]
        b       L1320
L1bd4:
        lsr     w9, w1, #3
        and     w1, w1, #0x7
        sub     x9, x2, x9
        ldr     x8, [x9]
        b       L177c
L1be8:
        lsr     w2, w1, #3
        and     w1, w1, #0x7
        sub     x2, x9, x2
        ldr     x8, [x2]
        b       L173c
L1bfc:
        lsr     w9, w2, #3
        and     w2, w2, #0x7
        sub     x9, x4, x9
        ldr     x8, [x9]
        b       L16e0
L1c10:
        mov     x4, x20
        b       L1320
L1c18:
        mov     x9, x20
        b       L177c

// BIT_reloadDStream_internal (0x30 bytes)
L1c20:
        mov     x1, x0
        mov     w0, #0x0
        ldr     w3, [x1, #8]
        ldr     x2, [x1, #16]
        and     w4, w3, #0x7
        lsr     w3, w3, #3
        str     w4, [x1, #8]
        sub     x2, x2, x3
        str     x2, [x1, #16]
        ldr     x2, [x2]
        str     x2, [x1]
        ret

// HUF_fillDTableX2ForWeight (0x188 bytes)
L1c50:
        sub     w4, w4, w3
        mov     w7, #0x1
        and     w4, w4, #0x1f
        and     w5, w5, #0xffff
        lsl     w7, w7, w4
        cmp     w4, #0x2
        b.eq    L1d00
        cmp     w7, #0x4
        b.hi    L1cb8
        cbz     w4,L1d94
        cmp     w4, #0x1
        b.ne    L1d3c
        lsl     w4, w6, #24
        add     w3, w4, w3, lsl #16
        cmp     x1, x2
        b.eq    L1cb4
L1c90:
        ldrb    w4, [x1], #1
        cmp     w6, #0x1
        add     w7, w5, w4, lsl #8
        csel    w4, w7, w4, ne
        add     w4, w4, w3
        stp     w4, w4, [x0]
        add     x0, x0, #0x8
        cmp     x2, x1
        b.ne    L1c90
L1cb4:
        ret
L1cb8:
        cmp     w4, #0x3
        b.ne    L1d3c
        lsl     w4, w6, #24
        add     w4, w4, w3, lsl #16
        cmp     x1, x2
        b.eq    L1cb4
L1cd0:
        ldrb    w3, [x1], #1
        cmp     w6, #0x1
        add     w7, w5, w3, lsl #8
        csel    w3, w7, w3, ne
        add     w3, w4, w3
        add     x3, x3, x3, lsl #32
        stp     x3, x3, [x0]
        stp     x3, x3, [x0, #16]
        add     x0, x0, #0x20
        cmp     x2, x1
        b.ne    L1cd0
        b       L1cb4
L1d00:
        lsl     w4, w6, #24
        add     w4, w4, w3, lsl #16
        cmp     x1, x2
        b.eq    L1cb4
L1d10:
        ldrb    w3, [x1], #1
        cmp     w6, #0x1
        add     w7, w5, w3, lsl #8
        csel    w3, w7, w3, ne
        add     w3, w4, w3
        add     x3, x3, x3, lsl #32
        stp     x3, x3, [x0]
        add     x0, x0, #0x10
        cmp     x2, x1
        b.ne    L1d10
        b       L1cb4
L1d3c:
        cmp     x1, x2
        b.eq    L1cb4
        lsl     w4, w6, #24
        ubfiz   x8, x7, #2, #32
        add     w7, w4, w3, lsl #16
L1d50:
        ldrb    w3, [x1]
        cmp     w6, #0x1
        add     x4, x0, x8
        add     w9, w5, w3, lsl #8
        csel    w3, w9, w3, ne
        add     w3, w3, w7
        add     x3, x3, x3, lsl #32
        nop
L1d70:
        stp     x3, x3, [x0]
        stp     x3, x3, [x0, #16]
        add     x0, x0, #0x20
        cmp     x4, x0
        b.ne    L1d70
        add     x1, x1, #0x1
        cmp     x2, x1
        b.ne    L1d50
        ret
L1d94:
        cmp     x1, x2
        b.eq    L1cb4
        lsl     w4, w6, #24
        sub     x2, x2, x1
        add     w3, w4, w3, lsl #16
        mov     x7, #0x0
        nop
L1db0:
        ldrb    w4, [x1, x7]
        cmp     w6, #0x1
        add     w8, w5, w4, lsl #8
        csel    w4, w8, w4, ne
        add     w4, w4, w3
        str     w4, [x0, x7, lsl #2]
        add     x7, x7, #0x1
        cmp     x2, x7
        b.ne    L1db0
        ret
        nop
        nop

// HUF_DecompressFastArgs_init (0x17c bytes)
L1de0:
        ldr     w7, [x5]
        mov     x6, x0
        add     x11, x1, x2
        cmp     x2, #0x0
        b.le    L1f44
        cmp     x4, #0x9
        b.ls    L1f54
L1dfc:
        ubfx    x7, x7, #16, #8
        cmp     w7, #0xb
        b.eq    L1e10
L1e08:
        mov     x0, #0x0
        ret
L1e10:
        ldrh    w7, [x3]
        add     x0, x3, #0x6
        ldrh    w10, [x3, #2]
        ldrh    w12, [x3, #4]
        add     x9, x0, x7
        add     x8, x9, x10
        stp     x0, x9, [x6, #120]
        add     x13, x8, x12
        stp     x8, x13, [x6, #136]
        cmp     x7, #0x7
        ccmp    x10, #0x7, #0x0, hi
        b.ls    L1e08
        add     x7, x7, x10
        sub     x0, x4, #0x6
        sub     x0, x0, x7
        cmp     x12, #0x7
        sub     x0, x0, x12
        ccmp    x0, #0x7, #0x0, hi
        b.ls    L1e08
        cmp     x4, x0
        b.cc    L1f54
        add     x2, x2, #0x3
        sub     x4, x4, #0x8
        add     x7, x3, x4
        sub     x15, x9, #0x8
        lsr     x2, x2, #2
        sub     x14, x8, #0x8
        add     x10, x1, x2
        sub     x12, x13, #0x8
        add     x0, x10, x2
        stp     x15, x14, [x6]
        add     x2, x0, x2
        stp     x12, x7, [x6, #16]
        stp     x1, x10, [x6, #32]
        stp     x0, x2, [x6, #48]
        cmp     x2, x11
        b.cs    L1e08
        ldurb   w0, [x9, #-1]
        add     x5, x5, #0x4
        ldur    x1, [x9, #-8]
        clz     w2, w0
        cmp     w0, #0x0
        sub     w2, w2, #0x17
        csel    w2, w2, wzr, ne
        orr     x1, x1, #0x1
        mov     x0, #0x1
        lsl     x1, x1, x2
        str     x1, [x6, #64]
        ldurb   w9, [x8, #-1]
        ldur    x1, [x8, #-8]
        clz     w2, w9
        cmp     w9, #0x0
        sub     w2, w2, #0x17
        csel    w2, w2, wzr, ne
        orr     x1, x1, x0
        lsl     x1, x1, x2
        str     x1, [x6, #72]
        ldurb   w8, [x13, #-1]
        ldur    x1, [x13, #-8]
        clz     w2, w8
        cmp     w8, #0x0
        sub     w2, w2, #0x17
        csel    w2, w2, wzr, ne
        orr     x1, x1, x0
        lsl     x1, x1, x2
        str     x1, [x6, #80]
        ldrb    w7, [x7, #7]
        ldr     x1, [x3, x4]
        clz     w2, w7
        cmp     w7, #0x0
        sub     w2, w2, #0x17
        csel    w2, w2, wzr, ne
        orr     x1, x1, x0
        stp     x3, x11, [x6, #104]
        lsl     x1, x1, x2
        stp     x1, x5, [x6, #88]
        ret
L1f44:
        b.eq    L1e08
        mov     x11, x1
        cmp     x4, #0x9
        b.hi    L1dfc
L1f54:
        mov     x0, #0xffffffffffffffec
        ret
        nop

// HUF_decompress4X2_usingDTable_internal_fast_c_loop (0x544 bytes)
L1f60:
        stp     x29, x30, [sp, #-320]!
        add     x12, x0, #0x20
        add     x10, x0, #0x40
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        add     x11, sp, #0x100
        add     x4, sp, #0xc0
        stp     x21, x22, [sp, #32]
        add     x13, sp, #0x120
        mov     x7, x0
        stp     x23, x24, [sp, #48]
        mov     w18, #0x0
        stp     x25, x26, [sp, #64]
        stp     x27, x28, [sp, #80]
        add     x27, sp, #0xe0
        ldp     q0, q1, [x10]
        str     x4, [sp, #184]
        ldp     q2, q3, [x12]
        ldp     q4, q5, [x0]
        stp     q0, q1, [x11]
        stp     q2, q3, [x4]
        ldur    q0, [sp, #200]
        stp     q4, q5, [x13]
        ldr     x3, [x11, #8]
        str     q0, [sp, #224]
        ldr     x8, [sp, #192]
        ldr     x1, [sp, #256]
        ldr     x30, [sp, #288]
        ldp     x25, x24, [x13, #8]
        stp     x12, x7, [sp, #152]
        ldp     x2, x26, [x11, #16]
        stp     x13, x11, [sp, #168]
        ldp     x0, x5, [x0, #96]
        mov     x23, x25
        ldr     x28, [x13, #24]
        mov     x25, x30
        ldr     x6, [x7, #112]
        mov     x30, x27
        stp     x5, x10, [sp, #136]
        ldr     x5, [x4, #24]
        str     x5, [sp, #240]
        str     x6, [sp, #248]
L2008:
        ldr     x6, [sp, #136]
        mov     x9, #0x1
        sub     x7, x25, x6
        mov     x6, #0x2493
        movk    x6, #0x9249, lsl #16
        movk    x6, #0x4924, lsl #32
        movk    x6, #0x2492, lsl #48
        umulh   x6, x7, x6
        sub     x7, x7, x6
        add     x7, x6, x7, lsr #1
        lsr     x7, x7, #2
L2034:
        lsl     x6, x9, #3
        add     x9, x9, #0x1
        add     x10, x4, x6
        add     x11, x30, x6
        ldur    x10, [x10, #-8]
        ldur    x6, [x11, #-8]
        sub     x6, x6, x10
        mov     x10, #0xcccccccccccccccc
        movk    x10, #0xcccd
        umulh   x6, x6, x10
        lsr     x6, x6, #3
        cmp     x7, x6
        csel    x7, x7, x6, ls
        cmp     x9, #0x5
        b.ne    L2034
        add     x7, x7, x7, lsl #2
        add     x6, x5, x7
        str     x6, [sp, #96]
        cmp     x6, x5
        b.eq    L2440
        cmp     x23, x25
        b.cc    L2440
        cmp     x24, x23
        b.cc    L2440
        cmp     x28, x24
        b.cc    L2440
        ldp     x7, x6, [x4, #8]
        stp     x4, x30, [sp, #120]
        nop
L20a8:
        lsr     x4, x1, #53
        lsr     x10, x3, #53
        lsr     x14, x2, #53
        lsl     x4, x4, #2
        str     x5, [sp, #112]
        add     x9, x0, x4
        lsl     x10, x10, #2
        add     x15, x0, x10
        lsl     x14, x14, #2
        ldrh    w13, [x0, x4]
        add     x4, x0, x14
        ldrb    w11, [x9, #2]
        lsr     x12, x26, #53
        ldrb    w17, [x9, #3]
        strh    w13, [x8]
        lsl     x12, x12, #2
        lsl     x1, x1, x11
        add     x9, x0, x12
        ldrb    w11, [x15, #2]
        lsr     x13, x1, #53
        ldrh    w16, [x0, x10]
        add     x10, x8, w17, uxtb
        ldrb    w19, [x15, #3]
        lsl     x13, x13, #2
        strh    w16, [x7]
        lsl     x11, x3, x11
        add     x16, x0, x13
        lsr     x15, x11, #53
        ldrb    w3, [x4, #2]
        ldrh    w18, [x0, x14]
        lsl     x15, x15, #2
        ldrb    w20, [x4, #3]
        add     x14, x7, w19, uxtb
        strh    w18, [x6]
        lsl     x3, x2, x3
        add     x2, x0, x15
        lsr     x4, x3, #53
        ldrb    w18, [x16, #2]
        ldrh    w22, [x0, x13]
        lsl     x4, x4, #2
        ldrb    w16, [x16, #3]
        add     x21, x0, x4
        strh    w22, [x8, w17, uxtw]
        lsl     x1, x1, x18
        lsr     x8, x1, #53
        add     x13, x6, w20, uxtb
        ldrh    w22, [x0, x15]
        add     x18, x10, w16, uxtb
        ldrb    w15, [x2, #2]
        lsl     x8, x8, #2
        ldrb    w17, [x2, #3]
        strh    w22, [x7, w19, uxtw]
        add     x19, x0, x8
        lsl     x2, x11, x15
        ldrb    w22, [x21, #2]
        lsr     x7, x2, #53
        ldrh    w4, [x0, x4]
        add     x11, x14, w17, uxtb
        ldrb    w15, [x21, #3]
        lsl     x7, x7, #2
        strh    w4, [x6, w20, uxtw]
        lsl     x3, x3, x22
        add     x6, x0, x7
        lsr     x4, x3, #53
        ldrb    w21, [x19, #2]
        ldrh    w22, [x0, x8]
        lsl     x4, x4, #2
        ldrb    w19, [x19, #3]
        add     x20, x0, x4
        strh    w22, [x10, w16, uxtw]
        lsl     x1, x1, x21
        add     x8, x13, w15, uxtb
        ldrb    w22, [x6, #2]
        add     x10, x18, w19, uxtb
        ldrh    w21, [x0, x7]
        lsr     x7, x1, #53
        ldrb    w16, [x6, #3]
        lsl     x2, x2, x22
        lsl     x7, x7, #2
        lsr     x6, x2, #53
        strh    w21, [x14, w17, uxtw]
        ldrh    w22, [x0, x4]
        add     x21, x0, x7
        ldrb    w4, [x20, #2]
        lsl     x6, x6, #2
        ldrb    w14, [x20, #3]
        add     x20, x0, x6
        strh    w22, [x13, w15, uxtw]
        add     x17, x11, w16, uxtb
        lsl     x4, x3, x4
        ldrh    w22, [x0, x7]
        lsr     x7, x4, #53
        ldrb    w3, [x21, #2]
        add     x15, x8, w14, uxtb
        ldrb    w13, [x21, #3]
        lsl     x7, x7, #2
        strh    w22, [x18, w19, uxtw]
        add     x21, x0, x7
        lsl     x1, x1, x3
        ldrb    w3, [x20, #2]
        add     x19, x10, w13, uxtb
        ldrh    w22, [x0, x6]
        lsr     x6, x1, #53
        ldrb    w18, [x20, #3]
        strh    w22, [x11, w16, uxtw]
        lsl     x3, x2, x3
        lsl     x6, x6, #2
        ldrh    w2, [x0, x7]
        lsr     x7, x3, #53
        ldrb    w11, [x21, #2]
        add     x22, x0, x6
        ldrb    w16, [x21, #3]
        lsl     x7, x7, #2
        strh    w2, [x8, w14, uxtw]
        add     x21, x0, x7
        lsl     x11, x4, x11
        add     x20, x17, w18, uxtb
        ldrh    w6, [x0, x6]
        lsr     x4, x11, #53
        ldrb    w2, [x22, #2]
        add     x14, x15, w16, uxtb
        ldrb    w8, [x22, #3]
        lsl     x4, x4, #2
        strh    w6, [x10, w13, uxtw]
        add     x6, x0, x4
        lsl     x2, x1, x2
        rbit    x2, x2
        ldrb    w10, [x21, #2]
        clz     x2, x2
        ldrh    w27, [x0, x7]
        add     x8, x19, w8, uxtb
        ldrb    w7, [x21, #3]
        sub     x25, x25, x2, lsr #3
        strh    w27, [x17, w18, uxtw]
        lsl     x10, x3, x10
        rbit    x10, x10
        and     w2, w2, #0x7
        ldrh    w3, [x0, x4]
        clz     x10, x10
        ldrb    w1, [x6, #2]
        add     x7, x20, w7, uxtb
        ldrb    w6, [x6, #3]
        sub     x23, x23, x10, lsr #3
        strh    w3, [x15, w16, uxtw]
        and     w10, w10, #0x7
        str     w3, [sp, #104]
        lsl     x11, x11, x1
        ldrb    w4, [x9, #2]
        add     x6, x14, w6, uxtb
        ldrh    w3, [x0, x12]
        rbit    x11, x11
        str     w3, [sp, #108]
        clz     x11, x11
        lsl     x4, x26, x4
        ldrb    w1, [x9, #3]
        strh    w3, [x5]
        lsr     x3, x4, #53
        ldr     x19, [x23]
        lsl     x3, x3, #2
        add     x12, x0, x3
        add     x9, x5, w1, uxtb
        sub     x24, x24, x11, lsr #3
        and     w11, w11, #0x7
        ldrh    w22, [x0, x3]
        ldrb    w3, [x12, #2]
        ldrb    w14, [x12, #3]
        strh    w22, [x5, w1, uxtw]
        lsl     x4, x4, x3
        lsr     x3, x4, #53
        add     x12, x9, w14, uxtb
        ldr     x1, [x25]
        lsl     x3, x3, #2
        add     x13, x0, x3
        orr     x1, x1, #0x1
        ldrh    w21, [x0, x3]
        orr     x3, x19, #0x1
        ldrb    w5, [x13, #2]
        lsl     x1, x1, x2
        ldrb    w13, [x13, #3]
        lsl     x3, x3, x10
        strh    w21, [x9, w14, uxtw]
        lsl     x4, x4, x5
        lsr     x5, x4, #53
        add     x10, x12, w13, uxtb
        ldr     x2, [x24]
        lsl     x5, x5, #2
        add     x19, x0, x5
        orr     x2, x2, #0x1
        ldrh    w20, [x0, x5]
        ldrb    w5, [x19, #2]
        lsl     x2, x2, x11
        ldrb    w11, [x19, #3]
        strh    w20, [x12, w13, uxtw]
        lsl     x4, x4, x5
        lsr     x19, x4, #53
        add     x30, x10, w11, uxtb
        lsl     x19, x19, #2
        add     x5, x0, x19
        ldrh    w19, [x0, x19]
        ldrb    w26, [x5, #2]
        ldrb    w5, [x5, #3]
        strh    w19, [x10, w11, uxtw]
        lsl     x4, x4, x26
        rbit    x4, x4
        clz     x4, x4
        add     x5, x30, w5, uxtb
        sub     x28, x28, x4, lsr #3
        and     w4, w4, #0x7
        ldr     x26, [x28]
        orr     x26, x26, #0x1
        lsl     x26, x26, x4
        ldr     x4, [sp, #96]
        cmp     x4, x5
        b.hi    L20a8
        ldp     x4, x30, [sp, #120]
        str     x6, [x4, #16]
        ldr     x6, [sp, #112]
        strh    w27, [x17, w18, uxtw]
        ldrh    w17, [sp, #104]
        mov     w18, #0x1
        strh    w17, [x15, w16, uxtw]
        stp     x8, x7, [x4]
        ldrh    w7, [sp, #108]
        strh    w7, [x6]
        strh    w22, [x9]
        strh    w21, [x9, w14, uxtw]
        strh    w20, [x12, w13, uxtw]
        strh    w19, [x10, w11, uxtw]
        str     x5, [x4, #24]
        b       L2008
L2440:
        ldp     x10, x12, [sp, #144]
        mov     x30, x25
        ldp     x7, x13, [sp, #160]
        ldr     x11, [sp, #176]
        cbz     w18,L246c
        stp     x3, x2, [x11, #8]
        stp     x23, x24, [x13, #8]
        str     x26, [x11, #24]
        str     x28, [x13, #24]
        str     x1, [sp, #256]
        str     x30, [sp, #288]
L246c:
        ldr     x0, [sp, #184]
        ldp     q4, q5, [x11]
        ldp     q2, q3, [x13]
        ldp     q0, q1, [x0]
        stp     q4, q5, [x10]
        stp     q2, q3, [x7]
        stp     q0, q1, [x12]
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldp     x29, x30, [sp], #320
        ret

// HUF_decompress4X1_usingDTable_internal_fast_c_loop (0x3a4 bytes)
L24a4:
        stp     x29, x30, [sp, #-192]!
        mov     x29, sp
        ldp     q2, q3, [x0]
        stp     x21, x22, [sp, #32]
        add     x21, x0, #0x20
        ldp     x5, x30, [x0, #96]
        add     x16, sp, #0x80
        stp     x19, x20, [sp, #16]
        add     x15, sp, #0xa0
        mov     x19, #0x2493
        ldp     q0, q1, [x21]
        stp     q2, q3, [x16]
        movk    x19, #0x9249, lsl #16
        ldr     x10, [sp, #128]
        movk    x19, #0x4924, lsl #32
        ldr     x18, [x0, #112]
        sub     x1, x10, x30
        stp     q0, q1, [x15]
        movk    x19, #0x2492, lsl #48
        mov     x20, #0xcccccccccccccccc
        ldr     x6, [x15, #24]
        umulh   x3, x1, x19
        movk    x20, #0xcccd
        add     x22, x0, #0x40
        sub     x2, x18, x6
        sub     x14, x1, x3
        add     x17, sp, #0x60
        add     x14, x3, x14, lsr #1
        umulh   x1, x2, x20
        lsr     x14, x14, #2
        ldp     q0, q1, [x22]
        lsr     x1, x1, #2
        cmp     x14, x1
        csel    x14, x14, x1, ls
        stp     q0, q1, [x17]
        add     x14, x14, x14, lsl #2
        add     x14, x6, x14
        cmp     x6, x14
        b.eq    L280c
        ldr     x9, [sp, #160]
        stp     x25, x26, [sp, #64]
        mov     w4, #0x0
        ldr     x25, [sp, #96]
        stp     x23, x24, [sp, #48]
        ldp     x8, x7, [x15, #8]
        ldp     x11, x12, [x16, #8]
        ldp     x3, x2, [x17, #8]
        ldr     x13, [x16, #24]
        ldr     x1, [x17, #24]
        str     x27, [sp, #80]
        nop
L2570:
        cmp     x11, x10
        b.cc    L2834
        cmp     x11, x12
        b.hi    L2834
        cmp     x12, x13
        b.hi    L2834
L2588:
        lsr     x4, x25, #53
        lsr     x23, x3, #53
        lsr     x26, x2, #53
        lsr     x24, x1, #53
        add     x6, x6, #0x5
        add     x9, x9, #0x5
        ldrh    w4, [x5, x4, lsl #1]
        add     x8, x8, #0x5
        add     x7, x7, #0x5
        asr     w27, w4, #8
        sturb   w27, [x9, #-5]
        lsl     x4, x25, x4
        ldrh    w23, [x5, x23, lsl #1]
        lsr     x25, x4, #53
        asr     w27, w23, #8
        sturb   w27, [x8, #-5]
        lsl     x3, x3, x23
        ldrh    w23, [x5, x26, lsl #1]
        lsr     x26, x3, #53
        asr     w27, w23, #8
        sturb   w27, [x7, #-5]
        lsl     x23, x2, x23
        ldrh    w2, [x5, x24, lsl #1]
        lsr     x24, x23, #53
        asr     w27, w2, #8
        sturb   w27, [x6, #-5]
        lsl     x1, x1, x2
        ldrh    w2, [x5, x25, lsl #1]
        lsr     x25, x1, #53
        asr     w27, w2, #8
        sturb   w27, [x9, #-4]
        lsl     x4, x4, x2
        ldrh    w26, [x5, x26, lsl #1]
        lsr     x2, x4, #53
        asr     w27, w26, #8
        sturb   w27, [x8, #-4]
        lsl     x3, x3, x26
        ldrh    w26, [x5, x24, lsl #1]
        lsr     x24, x3, #53
        asr     w27, w26, #8
        sturb   w27, [x7, #-4]
        lsl     x23, x23, x26
        ldrh    w26, [x5, x25, lsl #1]
        lsr     x25, x23, #53
        asr     w27, w26, #8
        sturb   w27, [x6, #-4]
        lsl     x1, x1, x26
        ldrh    w26, [x5, x2, lsl #1]
        lsr     x2, x1, #53
        asr     w27, w26, #8
        sturb   w27, [x9, #-3]
        lsl     x4, x4, x26
        ldrh    w26, [x5, x24, lsl #1]
        lsr     x24, x4, #53
        asr     w27, w26, #8
        sturb   w27, [x8, #-3]
        lsl     x3, x3, x26
        ldrh    w26, [x5, x25, lsl #1]
        lsr     x25, x3, #53
        asr     w27, w26, #8
        sturb   w27, [x7, #-3]
        lsl     x23, x23, x26
        ldrh    w26, [x5, x2, lsl #1]
        lsr     x2, x23, #53
        asr     w27, w26, #8
        sturb   w27, [x6, #-3]
        lsl     x1, x1, x26
        ldrh    w26, [x5, x24, lsl #1]
        lsr     x24, x1, #53
        asr     w27, w26, #8
        sturb   w27, [x9, #-2]
        lsl     x4, x4, x26
        ldrh    w25, [x5, x25, lsl #1]
        lsr     x26, x4, #53
        asr     w27, w25, #8
        sturb   w27, [x8, #-2]
        lsl     x3, x3, x25
        ldrh    w2, [x5, x2, lsl #1]
        lsr     x25, x3, #53
        asr     w27, w2, #8
        sturb   w27, [x7, #-2]
        lsl     x2, x23, x2
        ldrh    w23, [x5, x24, lsl #1]
        lsr     x24, x2, #53
        asr     w27, w23, #8
        sturb   w27, [x6, #-2]
        lsl     x1, x1, x23
        ldrh    w26, [x5, x26, lsl #1]
        lsr     x23, x1, #53
        asr     w27, w26, #8
        sturb   w27, [x9, #-1]
        lsl     x4, x4, x26
        rbit    x4, x4
        ldrh    w25, [x5, x25, lsl #1]
        clz     x4, x4
        sub     x10, x10, x4, lsr #3
        and     w4, w4, #0x7
        asr     w26, w25, #8
        sturb   w26, [x8, #-1]
        lsl     x3, x3, x25
        rbit    x3, x3
        ldrh    w25, [x5, x24, lsl #1]
        clz     x3, x3
        and     w24, w3, #0x7
        sub     x11, x11, x3, lsr #3
        asr     w3, w25, #8
        sturb   w3, [x7, #-1]
        lsl     x2, x2, x25
        rbit    x2, x2
        ldrh    w3, [x5, x23, lsl #1]
        clz     x2, x2
        sub     x12, x12, x2, lsr #3
        and     w2, w2, #0x7
        lsl     x1, x1, x3
        rbit    x1, x1
        clz     x1, x1
        asr     w3, w3, #8
        sturb   w3, [x6, #-1]
        sub     x13, x13, x1, lsr #3
        and     w1, w1, #0x7
        ldr     x25, [x10]
        ldr     x3, [x11]
        orr     x25, x25, #0x1
        ldr     x26, [x12]
        orr     x3, x3, #0x1
        ldr     x23, [x13]
        orr     x26, x26, #0x1
        lsl     x25, x25, x4
        orr     x23, x23, #0x1
        lsl     x3, x3, x24
        lsl     x2, x26, x2
        lsl     x1, x23, x1
        cmp     x6, x14
        b.cc    L2588
        sub     x23, x10, x30
        sub     x14, x18, x6
        mov     w4, #0x1
        umulh   x24, x23, x19
        umulh   x14, x14, x20
        sub     x23, x23, x24
        add     x23, x24, x23, lsr #1
        lsr     x14, x14, #2
        lsr     x23, x23, #2
        cmp     x14, x23
        csel    x14, x14, x23, ls
        add     x14, x14, x14, lsl #2
        add     x14, x6, x14
        cmp     x6, x14
        b.ne    L2570
L27dc:
        str     x25, [sp, #96]
        ldp     x25, x26, [sp, #64]
        str     x10, [sp, #128]
        ldp     x23, x24, [sp, #48]
        str     x9, [sp, #160]
        ldr     x27, [sp, #80]
        stp     x8, x7, [x15, #8]
        stp     x11, x12, [x16, #8]
        stp     x3, x2, [x17, #8]
        str     x6, [x15, #24]
        str     x13, [x16, #24]
        str     x1, [x17, #24]
L280c:
        ldp     q4, q5, [x17]
        ldp     q2, q3, [x16]
        ldp     q0, q1, [x15]
        stp     q4, q5, [x22]
        stp     q2, q3, [x0]
        stp     q0, q1, [x21]
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x29, x30, [sp], #192
        ret
L2834:
        cbnz    w4,L27dc
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldr     x27, [sp, #80]
        b       L280c
        nop
        nop

// HUF_decompress1X1_usingDTable_internal.constprop.0 (0x2dc bytes)
L2850:
        cmp     x1, #0x0
        add     x10, x0, x1
        ldrb    w11, [x4, #2]
        mov     x5, x0
        csel    x10, x10, x0, gt
        add     x6, x4, #0x4
        cbz     x3,L2afc
        add     x0, x2, x3
        add     x12, x2, #0x8
        ldurb   w7, [x0, #-1]
        cmp     x3, #0x7
        b.hi    L29cc
        ldrb    w4, [x2]
        cmp     x3, #0x5
        b.eq    L2af0
        b.hi    L2ad8
        cmp     x3, #0x3
        b.eq    L28a8
        cmp     x3, #0x4
        b.ne    L2a90
L28a0:
        ldrb    w0, [x2, #3]
        add     x4, x4, x0, lsl #24
L28a8:
        ldrb    w0, [x2, #2]
        add     x4, x4, x0, lsl #16
L28b0:
        ldrb    w0, [x2, #1]
        add     x4, x4, x0, lsl #8
L28b8:
        cbz     w7,L2a88
        mov     w0, #0x8
        sub     w3, w0, w3
        clz     w7, w7
        sub     x0, x10, x5
        add     w3, w7, w3, lsl #3
        sub     w3, w3, #0x17
        cmp     x0, #0x3
        b.le    L2a9c
        mov     x7, x2
L28e0:
        neg     w9, w11
        sub     x13, x10, #0x3
        and     w9, w9, #0x3f
        b       L2990
L28f0:
        sub     w3, w3, w4, lsl #3
        mov     x7, x0
        ldr     x4, [x0]
        cmp     x5, x13
        b.cs    L2a38
L2904:
        lsl     x0, x4, x3
        add     x5, x5, #0x4
        lsr     x0, x0, x9
        lsl     x0, x0, #1
        add     x14, x6, x0
        ldrb    w8, [x6, x0]
        ldrb    w0, [x14, #1]
        add     w8, w8, w3
        sturb   w0, [x5, #-4]
        lsl     x0, x4, x8
        lsr     x0, x0, x9
        lsl     x0, x0, #1
        add     x14, x6, x0
        ldrb    w3, [x6, x0]
        ldrb    w0, [x14, #1]
        add     w3, w3, w8
        sturb   w0, [x5, #-3]
        lsl     x0, x4, x3
        lsr     x0, x0, x9
        lsl     x0, x0, #1
        add     x14, x6, x0
        ldrb    w8, [x6, x0]
        ldrb    w0, [x14, #1]
        add     w8, w8, w3
        sturb   w0, [x5, #-2]
        lsl     x0, x4, x8
        lsr     x0, x0, x9
        lsl     x0, x0, #1
        add     x14, x6, x0
        ldrb    w3, [x6, x0]
        ldrb    w0, [x14, #1]
        add     w3, w3, w8
        sturb   w0, [x5, #-1]
        cmp     w3, #0x40
        b.hi    L2acc
L2990:
        lsr     w0, w3, #3
        cmp     x12, x7
        b.ls    L2ab4
        sub     x0, x7, x0
        cmp     x2, x7
        b.eq    L2aa8
        lsr     w4, w3, #3
        cmp     x2, x0
        b.ls    L28f0
        sub     w4, w7, w2
        sub     x0, x7, x2
        sub     x7, x7, x4
        sub     w3, w3, w0, lsl #3
        ldr     x4, [x7]
        b       L2a38
L29cc:
        mov     x0, #0xffffffffffffffff
        cbz     w7,L2a8c
        cmn     x3, #0x78
        b.hi    L2b24
        sub     x0, x3, #0x8
        clz     w7, w7
        sub     x8, x10, x5
        sub     w3, w7, #0x17
        add     x7, x2, x0
        ldr     x4, [x2, x0]
        cmp     x8, #0x3
        b.gt    L28e0
        mov     x0, x7
L2a00:
        cmp     x12, x0
        b.ls    L2b04
        cmp     x2, x0
        b.eq    L2aa4
        lsr     w7, w3, #3
        lsr     w8, w3, #3
        sub     x7, x0, x7
        cmp     x2, x7
        b.ls    L2a30
        sub     x7, x0, x2
        mov     w8, w7
        sub     x7, x0, w7, uxtw
L2a30:
        ldr     x4, [x7]
        sub     w3, w3, w8, lsl #3
L2a38:
        cmp     x10, x5
        b.ls    L2a70
L2a40:
        neg     w11, w11
        and     w11, w11, #0x3f
L2a48:
        lsl     x0, x4, x3
        lsr     x0, x0, x11
        lsl     x0, x0, #1
        add     x8, x6, x0
        ldrb    w0, [x6, x0]
        ldrb    w8, [x8, #1]
        strb    w8, [x5], #1
        add     w3, w3, w0
        cmp     x10, x5
        b.ne    L2a48
L2a70:
        cmp     x2, x7
        b.ne    L2a88
L2a78:
        mov     x0, x1
        cmp     w3, #0x40
        b.eq    L2a8c
        nop
L2a88:
        mov     x0, #0xffffffffffffffec
L2a8c:
        ret
L2a90:
        cmp     x3, #0x2
        b.eq    L28b0
        b       L28b8
L2a9c:
        mov     x0, x2
        b       L2a00
L2aa4:
        mov     x7, x2
L2aa8:
        cmp     x10, x5
        b.hi    L2a40
        b       L2a78
L2ab4:
        sub     x7, x7, x0
        and     w3, w3, #0x7
        ldr     x4, [x7]
        cmp     x5, x13
        b.cc    L2904
        b       L2a38
L2acc:
        .inst   0xb0000027  // adrp x7, 0x7000
        add     x7, x7, #0xbf0
        b       L2a38
L2ad8:
        cmp     x3, #0x6
        b.eq    L2ae8
        ldrb    w0, [x2, #6]
        add     x4, x4, x0, lsl #48
L2ae8:
        ldrb    w0, [x2, #5]
        add     x4, x4, x0, lsl #40
L2af0:
        ldrb    w0, [x2, #4]
        add     x4, x4, x0, lsl #32
        b       L28a0
L2afc:
        mov     x0, #0xffffffffffffffb8
        ret
L2b04:
        lsr     w7, w3, #3
        and     w3, w3, #0x7
        sub     x7, x0, x7
        ldr     x4, [x7]
        cmp     x5, x10
        b.cc    L2a40
        mov     x0, #0xffffffffffffffec
        b       L2a8c
L2b24:
        mov     x0, x3
        ret
        nop

// HUF_decompress1X2_usingDTable_internal.constprop.0 (0x588 bytes)
L2b30:
        mov     x6, x0
        cbz     x3,L30a0
        add     x0, x2, x3
        add     x11, x2, #0x8
        ldurb   w8, [x0, #-1]
        cmp     x3, #0x7
        b.hi    L2cfc
        ldrb    w7, [x2]
        cmp     x3, #0x5
        b.eq    L3094
        b.hi    L307c
        cmp     x3, #0x3
        b.eq    L2b74
        cmp     x3, #0x4
        b.ne    L2eb0
L2b6c:
        ldrb    w0, [x2, #3]
        add     x7, x7, x0, lsl #24
L2b74:
        ldrb    w0, [x2, #2]
        add     x7, x7, x0, lsl #16
L2b7c:
        ldrb    w0, [x2, #1]
        add     x7, x7, x0, lsl #8
L2b84:
        cbz     w8,L2ea8
        mov     w5, #0x8
        sub     w5, w5, w3
        clz     w8, w8
        ldrb    w9, [x4, #2]
        add     w5, w8, w5, lsl #3
        mov     x3, x2
        sub     w5, w5, #0x17
        add     x0, x4, #0x4
        cmp     x1, #0x0
        b.le    L2d30
L2bb0:
        add     x10, x6, x1
        cmp     x1, #0x7
        b.ls    L30a8
        cmp     w9, #0xb
        b.hi    L2ebc
        neg     w8, w9
        sub     x13, x10, #0x9
        and     w8, w8, #0x3f
        b       L2cbc
L2bd4:
        cmp     x6, x13
        sub     w5, w5, w7, lsl #3
        ldr     x7, [x4]
        cset    w12, cc
        mov     x3, x4
L2be8:
        lsl     x4, x7, x5
        cbz     w12,L2cf4
        lsr     x4, x4, x8
        lsl     x4, x4, #2
        add     x12, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x6]
        ldrb    w4, [x12, #2]
        ldrb    w14, [x12, #3]
        add     w5, w4, w5
        add     x16, x6, x14
        lsl     x4, x7, x5
        lsr     x4, x4, x8
        lsl     x4, x4, #2
        add     x12, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x6, x14]
        ldrb    w6, [x12, #2]
        ldrb    w15, [x12, #3]
        add     w6, w6, w5
        add     x14, x16, x15
        lsl     x4, x7, x6
        lsr     x4, x4, x8
        lsl     x4, x4, #2
        add     x12, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x16, x15]
        ldrb    w5, [x12, #2]
        ldrb    w12, [x12, #3]
        add     w5, w5, w6
        add     x16, x14, x12
        lsl     x4, x7, x5
        lsr     x4, x4, x8
        lsl     x4, x4, #2
        add     x6, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x14, x12]
        ldrb    w12, [x6, #2]
        ldrb    w15, [x6, #3]
        add     w12, w12, w5
        add     x6, x16, x15
        lsl     x4, x7, x12
        lsr     x4, x4, x8
        lsl     x4, x4, #2
        add     x14, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x16, x15]
        ldrb    w5, [x14, #2]
        ldrb    w4, [x14, #3]
        add     w5, w5, w12
        add     x6, x6, x4
        cmp     w5, #0x40
        b.hi    L3064
L2cbc:
        lsr     w4, w5, #3
        cmp     x11, x3
        b.ls    L304c
        sub     x4, x3, x4
        cmp     x2, x3
        b.eq    L2cf4
        lsr     w7, w5, #3
        cmp     x2, x4
        b.ls    L2bd4
        sub     w7, w3, w2
        sub     x4, x3, x2
        sub     x3, x3, x7
        sub     w5, w5, w4, lsl #3
        ldr     x7, [x3]
L2cf4:
        sub     x8, x10, x6
        b       L2d74
L2cfc:
        mov     x0, #0xffffffffffffffff
        cbz     w8,L2eac
        clz     w8, w8
        sub     w5, w8, #0x17
        cmn     x3, #0x78
        b.hi    L30b0
        sub     x0, x3, #0x8
        ldrb    w9, [x4, #2]
        add     x3, x2, x0
        ldr     x7, [x2, x0]
        add     x0, x4, #0x4
        cmp     x1, #0x0
        b.gt    L2bb0
L2d30:
        mov     x10, x6
        mov     x8, #0x0
L2d38:
        cmp     x11, x3
        b.ls    L2fc8
        cmp     x2, x3
        b.eq    L2fd8
        lsr     w4, w5, #3
        lsr     w12, w5, #3
        sub     x4, x3, x4
        cmp     x2, x4
        b.ls    L2d68
        sub     x4, x3, x2
        mov     w12, w4
        sub     x4, x3, w4, uxtw
L2d68:
        ldr     x7, [x4]
        sub     w5, w5, w12, lsl #3
        mov     x3, x4
L2d74:
        cmp     x8, #0x1
        b.ls    L2e58
        sub     x13, x10, #0x2
        cmp     w5, #0x40
        b.hi    L3028
L2d88:
        neg     w14, w9
        and     w14, w14, #0x3f
        b       L2ddc
L2d94:
        cmp     x6, x13
        sub     w5, w5, w7, lsl #3
        ldr     x7, [x4]
        cset    w8, ls
        mov     x3, x4
L2da8:
        lsl     x4, x7, x5
        cbz     w8,L2e14
        lsr     x4, x4, x14
        lsl     x4, x4, #2
        add     x8, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x6]
        ldrb    w12, [x8, #2]
        ldrb    w4, [x8, #3]
        add     w5, w5, w12
        add     x6, x6, x4
        cmp     w5, #0x40
        b.hi    L3028
L2ddc:
        lsr     w4, w5, #3
        cmp     x11, x3
        b.ls    L3008
        sub     x4, x3, x4
        cmp     x2, x3
        b.eq    L2e14
        lsr     w7, w5, #3
        cmp     x2, x4
        b.ls    L2d94
        sub     w7, w3, w2
        sub     x4, x3, x2
        sub     x3, x3, x7
        sub     w5, w5, w4, lsl #3
        ldr     x7, [x3]
L2e14:
        cmp     x6, x13
        b.hi    L2e58
        neg     w12, w9
        and     w12, w12, #0x3f
        nop
L2e28:
        lsl     x4, x7, x5
        lsr     x4, x4, x12
        lsl     x4, x4, #2
        add     x8, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x6]
        ldrb    w11, [x8, #3]
        ldrb    w4, [x8, #2]
        add     x6, x6, x11
        add     w5, w5, w4
        cmp     x6, x13
        b.ls    L2e28
L2e58:
        cmp     x6, x10
        b.cs    L2ff0
        neg     w9, w9
        lsl     x4, x7, x5
        lsr     x4, x4, x9
        lsl     x4, x4, #2
        add     x7, x0, x4
        ldrb    w0, [x0, x4]
        strb    w0, [x6]
        ldrb    w0, [x7, #3]
        cmp     w0, #0x1
        b.eq    L2fe8
        cmp     w5, #0x3f
        b.hi    L2ff0
        ldrb    w0, [x7, #2]
        add     w5, w5, w0
        cmp     w5, #0x40
        b.ls    L2ff0
        cmp     x2, x3
        b.eq    L3000
L2ea8:
        mov     x0, #0xffffffffffffffec
L2eac:
        ret
L2eb0:
        cmp     x3, #0x2
        b.eq    L2b7c
        b       L2b84
L2ebc:
        neg     w12, w9
        sub     x13, x10, #0x7
        and     w12, w12, #0x3f
        b       L2f8c
L2ecc:
        cmp     x6, x13
        sub     w5, w5, w7, lsl #3
        ldr     x7, [x4]
        cset    w8, cc
        mov     x3, x4
L2ee0:
        lsl     x4, x7, x5
        cbz     w8,L2cf4
        lsr     x4, x4, x12
        lsl     x4, x4, #2
        add     x14, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x6]
        ldrb    w8, [x14, #2]
        ldrb    w16, [x14, #3]
        add     w8, w8, w5
        add     x15, x6, x16
        lsl     x4, x7, x8
        lsr     x4, x4, x12
        lsl     x4, x4, #2
        add     x14, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x6, x16]
        ldrb    w5, [x14, #2]
        ldrb    w14, [x14, #3]
        add     w5, w5, w8
        add     x16, x15, x14
        lsl     x4, x7, x5
        lsr     x4, x4, x12
        lsl     x4, x4, #2
        add     x6, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x15, x14]
        ldrb    w8, [x6, #2]
        ldrb    w15, [x6, #3]
        add     w8, w8, w5
        add     x6, x16, x15
        lsl     x4, x7, x8
        lsr     x4, x4, x12
        lsl     x4, x4, #2
        add     x14, x0, x4
        ldrh    w4, [x0, x4]
        strh    w4, [x16, x15]
        ldrb    w5, [x14, #2]
        ldrb    w4, [x14, #3]
        add     w5, w5, w8
        add     x6, x6, x4
        cmp     w5, #0x40
        b.hi    L3064
L2f8c:
        lsr     w4, w5, #3
        cmp     x11, x3
        b.ls    L3034
        sub     x4, x3, x4
        cmp     x2, x3
        b.eq    L2cf4
        lsr     w7, w5, #3
        cmp     x2, x4
        b.ls    L2ecc
        sub     w7, w3, w2
        sub     x4, x3, x2
        sub     x3, x3, x7
        sub     w5, w5, w4, lsl #3
        ldr     x7, [x3]
        b       L2cf4
L2fc8:
        lsr     w4, w5, #3
        and     w5, w5, #0x7
        sub     x3, x3, x4
        ldr     x7, [x3]
L2fd8:
        sub     x13, x10, #0x2
        cmp     x8, #0x1
        b.hi    L2d88
        b       L2e58
L2fe8:
        ldrb    w0, [x7, #2]
        add     w5, w5, w0
L2ff0:
        cmp     x2, x3
        b.ne    L2ea8
        cmp     w5, #0x40
        b.ne    L2ea8
L3000:
        mov     x0, x1
        ret
L3008:
        sub     x3, x3, x4
        cmp     x6, x13
        and     w5, w5, #0x7
        cset    w8, ls
        ldr     x7, [x3]
        b       L2da8
L3020:
        sub     x13, x10, #0x2
        nop
L3028:
        .inst   0x90000023  // adrp x3, 0x7000
        add     x3, x3, #0xbf0
        b       L2e14
L3034:
        sub     x3, x3, x4
        cmp     x6, x13
        and     w5, w5, #0x7
        cset    w8, cc
        ldr     x7, [x3]
        b       L2ee0
L304c:
        sub     x3, x3, x4
        cmp     x6, x13
        and     w5, w5, #0x7
        cset    w12, cc
        ldr     x7, [x3]
        b       L2be8
L3064:
        sub     x3, x10, x6
        cmp     x3, #0x1
        b.hi    L3020
        .inst   0x90000023  // adrp x3, 0x7000
        add     x3, x3, #0xbf0
        b       L2e58
L307c:
        cmp     x3, #0x6
        b.eq    L308c
        ldrb    w0, [x2, #6]
        add     x7, x7, x0, lsl #48
L308c:
        ldrb    w0, [x2, #5]
        add     x7, x7, x0, lsl #40
L3094:
        ldrb    w0, [x2, #4]
        add     x7, x7, x0, lsl #32
        b       L2b6c
L30a0:
        mov     x0, #0xffffffffffffffb8
        ret
L30a8:
        mov     x8, x1
        b       L2d38
L30b0:
        mov     x0, x3
        ret
        nop
        nop

// HUF_decompress4X2_usingDTable_internal (0x223c bytes)
L30c0:
        stp     x29, x30, [sp, #-496]!
        mov     x18, x3
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x19, x0
        mov     x20, x1
        stp     x21, x22, [sp, #32]
        mov     x22, x2
        stp     x23, x24, [sp, #48]
        mov     x23, x4
        tbnz    w5, #5,L32d0
        cmp     x1, #0x0
        add     x21, x0, x1
        add     x24, sp, #0x158
        csel    x21, x21, x0, gt
        mov     x5, x4
        mov     x0, x24
        mov     x4, x3
        mov     x3, x2
        mov     x2, x1
        mov     x1, x19
        bl      L1de0
        cmn     x0, #0x78
        b.hi    L333c
        cbz     x0,L32d0
        mov     x0, x24
        bl      L1f60
        add     x9, x20, #0x3
        add     x5, x23, #0x4
        mov     x0, x24
        mov     w10, #0x4
        lsr     x9, x9, #2
L3140:
        ldr     x8, [x0, #32]
        sub     x1, x21, x19
        cmp     x9, x1
        add     x19, x19, x9
        csel    x7, x19, x21, ls
        cmp     x7, x8
        b.cc    L3338
        ldr     x1, [x0, #120]
        ldr     x3, [x0]
        sub     x1, x1, #0x8
        cmp     x3, x1
        b.cc    L3338
        ldr     x2, [x0, #64]
        sub     x6, x7, x8
        ldr     x11, [sp, #448]
        rbit    x2, x2
        clz     x2, x2
        ldr     x4, [x3]
        mov     w1, w2
        add     x12, x11, #0x8
        cmp     x6, #0x7
        b.le    L3494
        mov     x2, x8
        sub     x13, x7, #0x9
        b       L328c
L31a4:
        cmp     x2, x13
        sub     w1, w1, w4, lsl #3
        ldr     x4, [x6]
        cset    w14, cc
        mov     x3, x6
L31b8:
        lsl     x6, x4, x1
        cbz     w14,L32c4
        lsr     x6, x6, #53
        lsl     x6, x6, #2
        add     x15, x5, x6
        ldrh    w6, [x5, x6]
        strh    w6, [x2]
        ldrb    w14, [x15, #2]
        ldrb    w6, [x15, #3]
        add     w14, w14, w1
        add     x15, x2, x6
        lsl     x1, x4, x14
        lsr     x1, x1, #53
        lsl     x1, x1, #2
        add     x16, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x2, x6]
        ldrb    w6, [x16, #2]
        ldrb    w2, [x16, #3]
        add     w6, w6, w14
        add     x17, x15, x2
        lsl     x1, x4, x6
        lsr     x1, x1, #53
        lsl     x1, x1, #2
        add     x14, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x15, x2]
        ldrb    w2, [x14, #2]
        ldrb    w15, [x14, #3]
        add     w2, w2, w6
        add     x16, x17, x15
        lsl     x1, x4, x2
        lsr     x1, x1, #53
        lsl     x1, x1, #2
        add     x14, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x17, x15]
        ldrb    w6, [x14, #2]
        ldrb    w15, [x14, #3]
        add     w6, w6, w2
        add     x2, x16, x15
        lsl     x1, x4, x6
        lsr     x1, x1, #53
        lsl     x1, x1, #2
        add     x14, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x16, x15]
        ldrb    w1, [x14, #2]
        ldrb    w14, [x14, #3]
        add     w1, w1, w6
        add     x2, x2, x14
        cmp     w1, #0x40
        b.hi    L34e4
L328c:
        lsr     w6, w1, #3
        cmp     x12, x3
        b.ls    L347c
        sub     x6, x3, x6
        cmp     x11, x3
        b.eq    L3350
        lsr     w4, w1, #3
        cmp     x6, x11
        b.cs    L31a4
        sub     w6, w3, w11
        sub     x4, x3, x11
        sub     x3, x3, x6
        sub     w1, w1, w4, lsl #3
        ldr     x4, [x3]
L32c4:
        mov     x13, x3
        sub     x6, x7, x2
        b       L34cc
L32d0:
        cmp     x20, #0x5
        ccmp    x18, #0x9, #0x0, hi
        b.ls    L3338
        add     x11, x20, #0x3
        ldrh    w6, [x22, #2]
        ldrh    w3, [x22]
        add     x14, x19, x20
        ldrh    w10, [x22, #4]
        lsr     x11, x11, #2
        add     x12, x19, x11
        ldr     w8, [x23]
        add     x0, x6, w3, uxth
        add     x13, x12, x11
        sub     x2, x18, w10, uxth
        add     x11, x13, x11
        sub     x2, x2, x0
        cmp     x14, x11
        sub     x0, x2, #0x6
        cset    w1, cc
        cmp     x18, x0
        mov     x7, x6
        cset    w9, cc
        mov     x4, x3
        mov     x5, x10
        orr     w1, w1, w9
        cbz     w1,L34f8
L3338:
        mov     x0, #0xffffffffffffffec
L333c:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x29, x30, [sp], #496
        ret
L3350:
        sub     x6, x7, x2
        cmp     x6, #0x1
        b.ls    L3418
L335c:
        sub     x15, x7, #0x2
        b       L33ac
L3364:
        cmp     x2, x15
        sub     w1, w1, w4, lsl #3
        ldr     x4, [x6]
        cset    w13, ls
        mov     x3, x6
L3378:
        lsl     x6, x4, x1
        cbz     w13,L3410
        lsr     x6, x6, #53
        lsl     x6, x6, #2
        add     x13, x5, x6
        ldrh    w6, [x5, x6]
        strh    w6, [x2]
        ldrb    w14, [x13, #2]
        ldrb    w6, [x13, #3]
        add     w1, w1, w14
        add     x2, x2, x6
        cmp     w1, #0x40
        b.hi    L3410
L33ac:
        lsr     w6, w1, #3
        cmp     x12, x3
        b.ls    L3464
        sub     x6, x3, x6
        cmp     x11, x3
        b.eq    L3410
        lsr     w4, w1, #3
        cmp     x6, x11
        b.cs    L3364
        sub     x11, x3, x11
        sub     x3, x3, w11, uxtw
        sub     w1, w1, w11, lsl #3
        ldr     x4, [x3]
        cmp     x2, x15
        b.hi    L3418
L33e8:
        lsl     x3, x4, x1
        lsr     x3, x3, #53
        lsl     x3, x3, #2
        add     x6, x5, x3
        ldrh    w3, [x5, x3]
        strh    w3, [x2]
        ldrb    w11, [x6, #3]
        ldrb    w3, [x6, #2]
        add     x2, x2, x11
        add     w1, w1, w3
L3410:
        cmp     x2, x15
        b.ls    L33e8
L3418:
        cmp     x7, x2
        b.ls    L3434
        lsl     x1, x4, x1
        lsr     x1, x1, #53
        lsl     x1, x1, #2
        ldrb    w1, [x5, x1]
        strb    w1, [x2], #1
L3434:
        ldr     x19, [x0, #32]
        sub     x2, x2, x8
        add     x19, x19, x2
        str     x19, [x0, #32]
        cmp     x7, x19
        b.ne    L3338
        add     x0, x0, #0x8
        subs    w10, w10, #0x1
        b.ne    L3140
        cbz     x20,L3338
        mov     x0, x20
        b       L333c
L3464:
        sub     x3, x3, x6
        cmp     x2, x15
        and     w1, w1, #0x7
        cset    w13, ls
        ldr     x4, [x3]
        b       L3378
L347c:
        sub     x3, x3, x6
        cmp     x2, x13
        and     w1, w1, #0x7
        cset    w14, cc
        ldr     x4, [x3]
        b       L31b8
L3494:
        cmp     x3, x12
        b.cs    L45ac
        cmp     x3, x11
        b.eq    L39e0
        sub     x13, x3, x2, lsr #3
        lsr     w1, w2, #3
        cmp     x13, x11
        b.cs    L34c0
        sub     x13, x3, x11
        mov     w1, w13
        sub     x13, x3, w13, uxtw
L34c0:
        ldr     x4, [x13]
        sub     w1, w2, w1, lsl #3
        mov     x2, x8
L34cc:
        cmp     x6, #0x1
        b.ls    L3418
        cmp     w1, #0x40
        b.ls    L52ec
        sub     x15, x7, #0x2
        b       L3410
L34e4:
        sub     x3, x7, x2
        cmp     x3, #0x1
        b.ls    L3418
        sub     x15, x7, #0x2
        b       L3410
L34f8:
        cbz     x3,L462c
        add     x18, x22, #0x6
        stp     x27, x28, [sp, #80]
        add     x15, x18, x3
        add     x28, x22, #0xe
        stp     x18, x28, [sp, #248]
        ldurb   w17, [x15, #-1]
        cmp     x3, #0x7
        b.ls    L39fc
        sub     x3, x3, #0x8
        add     x9, x18, x3
        str     x9, [sp, #240]
        ldr     x9, [x18, x3]
        str     x9, [sp, #224]
        cbz     w17,L39f0
        clz     w3, w17
        sub     w3, w3, #0x17
L353c:
        str     w3, [sp, #232]
        cbz     x6,L4628
        add     x9, x15, x6
        add     x16, x15, #0x8
        str     x16, [sp, #96]
        stp     x15, x16, [sp, #288]
        ldurb   w16, [x9, #-1]
        cmp     x6, #0x7
        b.ls    L45c8
        sub     x6, x6, #0x8
        add     x4, x15, x6
        str     x4, [sp, #280]
        ldr     x4, [x15, x6]
        str     x4, [sp, #264]
        cbz     w16,L39f0
        clz     w4, w16
        sub     w22, w4, #0x17
L3580:
        str     w22, [sp, #272]
        cbz     x10,L4628
        add     x24, x9, x10
        add     x4, x9, #0x8
        str     x4, [sp, #104]
        stp     x9, x4, [sp, #328]
        ldurb   w16, [x24, #-1]
        cmp     x10, #0x7
        b.ls    L4664
        sub     x10, x10, #0x8
        add     x4, x9, x10
        str     x4, [sp, #320]
        ldr     x4, [x9, x10]
        str     x4, [sp, #304]
        cbz     w16,L39f0
        clz     w4, w16
        sub     w21, w4, #0x17
L35c4:
        str     w21, [sp, #312]
        cbz     x0,L4628
        add     x4, x24, x2
        add     x6, x24, #0x8
        str     x6, [sp, #112]
        stp     x24, x6, [sp, #368]
        ldurb   w4, [x4, #-7]
        cmp     x0, #0x7
        b.ls    L46f4
        sub     x2, x2, #0xe
        add     x5, x24, x2
        str     x5, [sp, #360]
        ldr     x2, [x24, x2]
        str     x2, [sp, #344]
        cbz     w4,L39f0
        clz     w2, w4
        sub     w2, w2, #0x17
        str     w2, [sp, #352]
        cmn     x0, #0x78
        b.hi    L47c4
L3614:
        sub     x2, x14, #0x7
        sub     x0, x14, x11
        str     x2, [sp, #120]
        add     x5, x23, #0x4
        ubfx    x23, x8, #16, #8
        cmp     x0, #0x7
        b.le    L3a8c
        cmp     x2, x11
        b.ls    L3a8c
        ldr     x0, [sp, #224]
        stp     x25, x26, [sp, #64]
        neg     w2, w23
        ldr     x4, [sp, #264]
        mov     x10, x11
        ldr     x25, [sp, #304]
        mov     x6, x13
        ldr     x26, [sp, #320]
        mov     x7, x12
        ldr     x27, [sp, #344]
        and     w2, w2, #0x3f
        ldr     x30, [sp, #360]
        stp     wzr, wzr, [sp, #132]
        ldr     x16, [sp, #240]
        str     w1, [sp, #140]
        ldr     x17, [sp, #280]
        stp     x14, x18, [sp, #144]
        ldr     w8, [sp, #352]
        mov     x18, x26
        mov     x14, x25
        stp     x12, x13, [sp, #160]
        mov     x12, x0
        mov     x13, x4
        str     x11, [sp, #176]
        mov     x11, x27
        stp     wzr, w23, [sp, #184]
        stp     x20, x15, [sp, #192]
        mov     x15, x30
        stp     x9, x24, [sp, #208]
        b       L3750
L36b0:
        lsr     w0, w3, #3
        and     w3, w3, #0x7
        sub     x16, x16, x0
        mov     w1, #0x1
        mov     w0, #0x0
        str     w1, [sp, #140]
        ldr     x12, [x16]
L36cc:
        ldr     x1, [sp, #96]
        cmp     x1, x17
        b.hi    L47cc
        lsr     w1, w22, #3
        and     w22, w22, #0x7
        sub     x17, x17, x1
        mov     w4, #0x1
        str     w4, [sp, #132]
        ldr     x13, [x17]
L36f0:
        ldr     x1, [sp, #104]
        cmp     x1, x18
        b.hi    L485c
        lsr     w1, w21, #3
        and     w21, w21, #0x7
        sub     x18, x18, x1
        mov     w4, #0x1
        str     w4, [sp, #136]
        ldr     x14, [x18]
L3714:
        ldr     x1, [sp, #112]
        cmp     x1, x15
        b.hi    L47d4
        lsr     w1, w8, #3
        cmp     w0, #0x0
        sub     x15, x15, x1
        cset    w0, eq
        ldr     x1, [sp, #120]
        and     w8, w8, #0x7
        ldr     x11, [x15]
        cmp     x1, x10
        cset    w1, hi
        ands    w0, w0, w1
        str     w0, [sp, #184]
        b.eq    L4bbc
L3750:
        lsl     x0, x12, x3
        lsr     x0, x0, x2
        lsl     x0, x0, #2
        lsl     x4, x13, x22
        lsr     x4, x4, x2
        add     x1, x5, x0
        lsl     x4, x4, #2
        lsl     x25, x14, x21
        ldrh    w0, [x5, x0]
        lsr     x25, x25, x2
        strh    w0, [x19]
        add     x20, x5, x4
        lsl     x25, x25, #2
        lsl     x0, x11, x8
        ldrb    w9, [x1, #2]
        lsr     x0, x0, x2
        ldrh    w4, [x5, x4]
        add     x24, x5, x25
        ldrb    w1, [x1, #3]
        add     w9, w9, w3
        strh    w4, [x7]
        lsl     x0, x0, #2
        lsl     x23, x12, x9
        add     x3, x5, x0
        ldrb    w4, [x20, #2]
        lsr     x23, x23, x2
        ldrh    w25, [x5, x25]
        lsl     x23, x23, #2
        ldrb    w20, [x20, #3]
        add     w4, w4, w22
        strh    w25, [x6]
        add     x22, x5, x23
        ldrb    w30, [x24, #2]
        ldrh    w25, [x5, x0]
        lsl     x0, x13, x4
        ldrb    w27, [x24, #3]
        add     w30, w30, w21
        strh    w25, [x10]
        lsr     x0, x0, x2
        lsl     x0, x0, #2
        lsl     x21, x14, x30
        ldrb    w26, [x3, #2]
        ldrh    w23, [x5, x23]
        ldrb    w3, [x3, #3]
        add     w26, w26, w8
        strh    w23, [x19, x1]
        lsr     x8, x21, x2
        lsl     x8, x8, #2
        add     x23, x5, x0
        ldrh    w21, [x5, x0]
        lsl     x0, x11, x26
        ldrb    w24, [x22, #2]
        lsr     x0, x0, x2
        ldrb    w25, [x22, #3]
        lsl     x0, x0, #2
        strh    w21, [x7, x20]
        add     w24, w24, w9
        add     x22, x5, x8
        add     x1, x19, x1
        ldrh    w9, [x5, x8]
        lsl     x8, x12, x24
        ldrb    w21, [x23, #2]
        lsr     x8, x8, x2
        ldrb    w23, [x23, #3]
        lsl     x8, x8, #2
        strh    w9, [x6, x27]
        add     w21, w21, w4
        add     x9, x5, x0
        add     x4, x7, x20
        ldrh    w7, [x5, x0]
        lsl     x0, x13, x21
        ldrb    w20, [x22, #2]
        lsr     x0, x0, x2
        ldrb    w22, [x22, #3]
        lsl     x0, x0, #2
        strh    w7, [x10, x3]
        add     w20, w20, w30
        add     x7, x5, x8
        add     x6, x6, x27
        ldrb    w19, [x9, #2]
        add     x3, x10, x3
        ldrb    w9, [x9, #3]
        add     x10, x1, x25
        ldrh    w8, [x5, x8]
        add     w19, w19, w26
        strh    w8, [x1, x25]
        add     x26, x5, x0
        lsl     x8, x14, x20
        lsr     x8, x8, x2
        ldrh    w27, [x5, x0]
        lsl     x8, x8, #2
        ldrb    w0, [x7, #2]
        lsl     x1, x11, x19
        ldrb    w7, [x7, #3]
        strh    w27, [x4, x23]
        add     w24, w0, w24
        lsr     x0, x1, x2
        add     x4, x4, x23
        ldrb    w1, [x26, #2]
        lsl     x0, x0, #2
        ldrh    w27, [x5, x8]
        add     x23, x5, x0
        ldrb    w25, [x26, #3]
        add     x26, x5, x8
        strh    w27, [x6, x22]
        add     w8, w1, w21
        lsl     x1, x12, x24
        add     x6, x6, x22
        ldrh    w0, [x5, x0]
        lsr     x1, x1, x2
        lsl     x1, x1, #2
        ldrb    w27, [x26, #2]
        ldrb    w21, [x26, #3]
        add     x30, x5, x1
        strh    w0, [x3, x9]
        lsl     x0, x13, x8
        lsr     x0, x0, x2
        add     w20, w27, w20
        lsl     x0, x0, #2
        add     x9, x3, x9
        ldrh    w3, [x5, x1]
        lsl     x1, x14, x20
        ldrb    w26, [x23, #2]
        lsr     x22, x1, x2
        ldrb    w23, [x23, #3]
        lsl     x22, x22, #2
        strh    w3, [x10, x7]
        add     w26, w26, w19
        add     x27, x5, x0
        add     x19, x10, x7
        ldrh    w1, [x5, x0]
        add     x10, x9, x23
        ldrb    w3, [x30, #2]
        ldrb    w30, [x30, #3]
        strh    w1, [x4, x25]
        lsl     x1, x11, x26
        lsr     x1, x1, x2
        add     x4, x4, x25
        ldrh    w7, [x5, x22]
        lsl     x1, x1, #2
        ldrb    w0, [x27, #2]
        add     x25, x5, x22
        ldrb    w27, [x27, #3]
        add     w3, w3, w24
        strh    w7, [x6, x21]
        add     x24, x5, x1
        add     x6, x6, x21
        add     w22, w0, w8
        ldrh    w1, [x5, x1]
        add     x19, x19, x30
        ldrb    w0, [x25, #3]
        add     x7, x4, x27
        ldrb    w21, [x25, #2]
        strh    w1, [x9, x23]
        add     x6, x6, x0
        add     w21, w21, w20
        ldrb    w0, [x24, #2]
        ldrb    w1, [x24, #3]
        add     w8, w0, w26
        add     x10, x10, x1
        cmp     x28, x16
        b.ls    L36b0
        mov     w0, #0x3
        b       L36cc
L39e0:
        mov     x2, x8
        cmp     x6, #0x1
        b.gt    L335c
        b       L3418
L39f0:
        ldp     x27, x28, [sp, #80]
        mov     x0, #0xffffffffffffffff
        b       L333c
L39fc:
        ldrb    w9, [x22, #6]
        str     x9, [sp, #224]
        str     x18, [sp, #240]
        cmp     w3, #0x5
        b.eq    L3a74
        b.hi    L3a5c
        cmp     w3, #0x3
        b.eq    L3a2c
        cmp     w3, #0x4
        b.ne    L3a80
L3a24:
        ldrb    w3, [x22, #9]
        add     x9, x9, x3, lsl #24
L3a2c:
        ldrb    w3, [x22, #8]
        add     x9, x9, x3, lsl #16
L3a34:
        ldrb    w16, [x22, #7]
        add     x9, x9, x16, lsl #8
        str     x9, [sp, #224]
L3a40:
        cbz     w17,L45a0
        mov     w9, #0x8
        sub     w9, w9, w4
        clz     w3, w17
        add     w3, w3, w9, lsl #3
        sub     w3, w3, #0x17
        b       L353c
L3a5c:
        cmp     w3, #0x6
        b.eq    L3a6c
        ldrb    w3, [x22, #12]
        add     x9, x9, x3, lsl #48
L3a6c:
        ldrb    w3, [x22, #11]
        add     x9, x9, x3, lsl #40
L3a74:
        ldrb    w3, [x22, #10]
        add     x9, x9, x3, lsl #32
        b       L3a24
L3a80:
        cmp     w3, #0x2
        b.eq    L3a34
        b       L3a40
L3a8c:
        mov     x10, x11
        mov     x6, x13
        mov     x7, x12
L3a98:
        cmp     x13, x7
        ccmp    x12, x19, #0x0, cs
        cset    w8, cc
        cmp     x11, x6
        cset    w0, cc
        orr     w8, w8, w0
        cbnz    w8,L45a0
        sub     x21, x12, x19
        stp     x25, x26, [sp, #64]
        ldr     w0, [sp, #232]
        cmp     x21, #0x7
        b.le    L4b50
        cmp     w23, #0xb
        b.ls    L50b8
        cmp     w0, #0x40
        b.hi    L4b40
        neg     w16, w23
        sub     x25, x12, #0x7
        ldr     x1, [sp, #224]
        and     w16, w16, #0x3f
        ldr     x3, [sp, #240]
        mov     w2, #0x0
        b       L3bb4
L3af4:
        cmp     x19, x25
        sub     w0, w0, w1, lsl #3
        ldr     x1, [x4]
        cset    w2, cc
        mov     x3, x4
L3b08:
        lsl     x4, x1, x0
        cbz     w2,L3bec
        lsr     x4, x4, x16
        lsl     x4, x4, #2
        add     x21, x5, x4
        ldrh    w4, [x5, x4]
        strh    w4, [x19]
        ldrb    w17, [x21, #2]
        ldrb    w22, [x21, #3]
        add     w17, w17, w0
        add     x4, x19, x22
        lsl     x0, x1, x17
        lsr     x0, x0, x16
        lsl     x0, x0, #2
        add     x21, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x22]
        ldrb    w19, [x21, #2]
        ldrb    w22, [x21, #3]
        add     w19, w19, w17
        add     x17, x4, x22
        lsl     x0, x1, x19
        lsr     x0, x0, x16
        lsl     x0, x0, #2
        add     x21, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x4, x22]
        ldrb    w4, [x21, #2]
        ldrb    w22, [x21, #3]
        add     w4, w4, w19
        add     x19, x17, x22
        lsl     x0, x1, x4
        lsr     x0, x0, x16
        lsl     x0, x0, #2
        add     x21, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x17, x22]
        ldrb    w0, [x21, #2]
        ldrb    w17, [x21, #3]
        add     w0, w0, w4
        add     x19, x19, x17
        cmp     w0, #0x40
        b.hi    L4b34
L3bb4:
        lsr     w4, w0, #3
        cmp     x28, x3
        b.ls    L4ba4
        sub     x4, x3, x4
        cmp     x18, x3
        b.eq    L48c8
        lsr     w1, w0, #3
        cmp     x18, x4
        b.ls    L3af4
L3bd8:
        sub     w2, w3, w18
        sub     x1, x3, x18
        sub     x3, x3, x2
        sub     w0, w0, w1, lsl #3
        ldr     x1, [x3]
L3bec:
        sub     x21, x12, x19
        str     x1, [sp, #224]
        str     w0, [sp, #232]
        str     x3, [sp, #240]
L3bfc:
        cmp     x21, #0x1
        b.ls    L4c30
        ldr     w0, [sp, #232]
        sub     x4, x12, #0x2
        .inst   0x90000021  // adrp x1, 0x7000
        cmp     w0, #0x40
        b.hi    L497c
        ldr     x17, [sp, #240]
        neg     w16, w23
        ldr     x2, [sp, #224]
        and     w16, w16, #0x3f
        mov     x21, x17
        mov     w3, #0x0
        b       L3c7c
L3c34:
        cmp     x19, x4
        sub     w0, w0, w2, lsl #3
        ldr     x2, [x1]
        cset    w3, ls
        mov     x21, x1
L3c48:
        lsl     x1, x2, x0
        cbz     w3,L3cb4
        lsr     x1, x1, x16
        lsl     x1, x1, #2
        add     x22, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x19]
        ldrb    w25, [x22, #2]
        ldrb    w1, [x22, #3]
        add     w0, w25, w0
        add     x19, x19, x1
        cmp     w0, #0x40
        b.hi    L4970
L3c7c:
        lsr     w1, w0, #3
        cmp     x28, x21
        b.ls    L4958
        sub     x1, x21, x1
        cmp     x18, x21
        b.eq    L489c
        lsr     w2, w0, #3
        cmp     x18, x1
        b.ls    L3c34
        sub     w2, w21, w18
        sub     x1, x21, x18
        sub     x21, x21, x2
        sub     w0, w0, w1, lsl #3
        ldr     x2, [x21]
L3cb4:
        str     x2, [sp, #224]
        str     w0, [sp, #232]
        str     x21, [sp, #240]
L3cc0:
        cmp     x19, x4
        b.hi    L3d0c
        ldr     x16, [sp, #224]
        neg     w3, w23
        ldr     w2, [sp, #232]
        and     w3, w3, #0x3f
L3cd8:
        lsl     x0, x16, x2
        lsr     x0, x0, x3
        lsl     x0, x0, #2
        add     x1, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19]
        ldrb    w17, [x1, #3]
        ldrb    w0, [x1, #2]
        add     x19, x19, x17
        add     w2, w2, w0
        cmp     x19, x4
        b.ls    L3cd8
        str     w2, [sp, #232]
L3d0c:
        cmp     x12, x19
        b.ls    L3d64
        ldr     x0, [sp, #224]
        neg     w2, w23
        ldr     w1, [sp, #232]
        lsl     x0, x0, x1
        lsr     x0, x0, x2
        lsl     x0, x0, #2
        add     x2, x5, x0
        ldrb    w0, [x5, x0]
        strb    w0, [x19]
        ldrb    w0, [x2, #3]
        cmp     w0, #0x1
        b.eq    L5234
        cmp     w1, #0x3f
        b.hi    L3d64
        ldrb    w0, [x2, #2]
        mov     w2, #0x40
        add     w0, w0, w1
        cmp     w0, #0x41
        csel    w0, w0, w2, cc
        str     w0, [sp, #232]
L3d64:
        sub     x19, x13, x7
        ldr     w0, [sp, #272]
        cmp     x19, #0x7
        b.le    L49f4
        cmp     w23, #0xb
        b.ls    L4df8
        cmp     w0, #0x40
        b.hi    L49e4
        neg     w12, w23
        sub     x16, x13, #0x7
        ldr     x2, [sp, #264]
        and     w12, w12, #0x3f
        ldr     x4, [sp, #280]
        mov     w3, #0x0
        b       L3e60
L3da0:
        ldr     x2, [x17]
        cmp     x7, x16
        sub     w1, w0, w1, lsl #3
        cset    w3, cc
        mov     x4, x17
L3db4:
        lsl     x0, x2, x1
        cbz     w3,L3e9c
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x7]
        ldrb    w0, [x17, #2]
        ldrb    w22, [x17, #3]
        add     w1, w0, w1
        add     x17, x7, x22
        lsl     x0, x2, x1
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x19, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x7, x22]
        ldrb    w7, [x19, #2]
        ldrb    w25, [x19, #3]
        add     w7, w7, w1
        add     x19, x17, x25
        lsl     x0, x2, x7
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x22, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x17, x25]
        ldrb    w1, [x22, #2]
        ldrb    w22, [x22, #3]
        add     w1, w1, w7
        add     x7, x19, x22
        lsl     x0, x2, x1
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x22]
        ldrb    w0, [x17, #2]
        ldrb    w17, [x17, #3]
        add     w0, w0, w1
        add     x7, x7, x17
        cmp     w0, #0x40
        b.hi    L49d8
L3e60:
        ldr     x1, [sp, #96]
        lsr     w17, w0, #3
        cmp     x1, x4
        b.ls    L4c60
        sub     x17, x4, x17
        cmp     x15, x4
        b.eq    L4940
        lsr     w1, w0, #3
        cmp     x15, x17
        b.ls    L3da0
L3e88:
        sub     w2, w4, w15
        sub     x1, x4, x15
        sub     x4, x4, x2
        sub     w1, w0, w1, lsl #3
        ldr     x2, [x4]
L3e9c:
        sub     x19, x13, x7
        str     x2, [sp, #264]
        str     w1, [sp, #272]
        str     x4, [sp, #280]
L3eac:
        cmp     x19, #0x1
        b.ls    L4ca0
        ldr     w0, [sp, #272]
        sub     x4, x13, #0x2
        .inst   0x90000021  // adrp x1, 0x7000
        cmp     w0, #0x40
        b.hi    L49ac
        ldr     x17, [sp, #280]
        neg     w16, w23
        ldr     x22, [sp, #96]
        and     w16, w16, #0x3f
        ldr     x2, [sp, #264]
        mov     x12, x17
        mov     w3, #0x0
        b       L3f30
L3ee8:
        cmp     x7, x4
        sub     w0, w0, w2, lsl #3
        ldr     x2, [x1]
        cset    w3, ls
        mov     x12, x1
L3efc:
        lsl     x1, x2, x0
        cbz     w3,L3f68
        lsr     x1, x1, x16
        lsl     x1, x1, #2
        add     x19, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x7]
        ldrb    w25, [x19, #2]
        ldrb    w1, [x19, #3]
        add     w0, w25, w0
        add     x7, x7, x1
        cmp     w0, #0x40
        b.hi    L49a0
L3f30:
        lsr     w1, w0, #3
        cmp     x22, x12
        b.ls    L4928
        sub     x1, x12, x1
        cmp     x15, x12
        b.eq    L4888
        lsr     w2, w0, #3
        cmp     x15, x1
        b.ls    L3ee8
        sub     w2, w12, w15
        sub     x1, x12, x15
        sub     x12, x12, x2
        sub     w0, w0, w1, lsl #3
        ldr     x2, [x12]
L3f68:
        str     x2, [sp, #264]
        str     w0, [sp, #272]
        str     x12, [sp, #280]
L3f74:
        cmp     x7, x4
        b.hi    L3fc0
        ldr     x16, [sp, #264]
        neg     w2, w23
        ldr     w3, [sp, #272]
        and     w2, w2, #0x3f
L3f8c:
        lsl     x0, x16, x3
        lsr     x0, x0, x2
        lsl     x0, x0, #2
        add     x1, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x7]
        ldrb    w17, [x1, #3]
        ldrb    w0, [x1, #2]
        add     x7, x7, x17
        add     w3, w3, w0
        cmp     x7, x4
        b.ls    L3f8c
        str     w3, [sp, #272]
L3fc0:
        cmp     x13, x7
        b.ls    L4018
        ldr     x0, [sp, #264]
        neg     w2, w23
        ldr     w1, [sp, #272]
        lsl     x0, x0, x1
        lsr     x0, x0, x2
        lsl     x0, x0, #2
        add     x2, x5, x0
        ldrb    w0, [x5, x0]
        strb    w0, [x7]
        ldrb    w0, [x2, #3]
        cmp     w0, #0x1
        b.eq    L5224
        cmp     w1, #0x3f
        b.hi    L4018
        ldrb    w0, [x2, #2]
        mov     w2, #0x40
        add     w0, w0, w1
        cmp     w0, #0x41
        csel    w0, w0, w2, cc
        str     w0, [sp, #272]
L4018:
        sub     x13, x11, x6
        ldr     w0, [sp, #312]
        cmp     x13, #0x7
        b.le    L4adc
        cmp     w23, #0xb
        b.ls    L4ca8
        cmp     w0, #0x40
        b.hi    L4acc
        neg     w7, w23
        sub     x13, x11, #0x7
        ldr     x2, [sp, #304]
        and     w7, w7, #0x3f
        ldr     x4, [sp, #320]
        mov     w3, #0x0
        b       L4114
L4054:
        ldr     x2, [x16]
        cmp     x6, x13
        sub     w1, w0, w1, lsl #3
        cset    w3, cc
        mov     x4, x16
L4068:
        lsl     x0, x2, x1
        cbz     w3,L4150
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x16, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x6]
        ldrb    w0, [x16, #2]
        ldrb    w19, [x16, #3]
        add     w1, w0, w1
        add     x16, x6, x19
        lsl     x0, x2, x1
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x6, x19]
        ldrb    w6, [x17, #2]
        ldrb    w22, [x17, #3]
        add     w6, w6, w1
        add     x19, x16, x22
        lsl     x0, x2, x6
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x16, x22]
        ldrb    w1, [x17, #2]
        ldrb    w17, [x17, #3]
        add     w1, w1, w6
        add     x6, x19, x17
        lsl     x0, x2, x1
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x16, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x17]
        ldrb    w0, [x16, #2]
        ldrb    w16, [x16, #3]
        add     w0, w0, w1
        add     x6, x6, x16
        cmp     w0, #0x40
        b.hi    L4ac0
L4114:
        ldr     x1, [sp, #104]
        lsr     w16, w0, #3
        cmp     x4, x1
        b.cs    L4c78
        sub     x16, x4, x16
        cmp     x9, x4
        b.eq    L48f8
        lsr     w1, w0, #3
        cmp     x9, x16
        b.ls    L4054
L413c:
        sub     w2, w4, w9
        sub     x1, x4, x9
        sub     x4, x4, x2
        sub     w1, w0, w1, lsl #3
        ldr     x2, [x4]
L4150:
        sub     x13, x11, x6
        str     x2, [sp, #304]
        str     w1, [sp, #312]
        str     x4, [sp, #320]
L4160:
        cmp     x13, #0x1
        b.ls    L4c90
        ldr     w0, [sp, #312]
        sub     x4, x11, #0x2
        .inst   0xf0000001  // adrp x1, 0x7000
        cmp     w0, #0x40
        b.hi    L49c8
        ldr     x7, [sp, #320]
        neg     w16, w23
        ldr     x19, [sp, #104]
        and     w16, w16, #0x3f
        ldr     x2, [sp, #304]
        mov     x13, x7
        mov     w3, #0x0
        b       L41e4
L419c:
        cmp     x6, x4
        sub     w0, w0, w2, lsl #3
        ldr     x2, [x1]
        cset    w3, ls
        mov     x13, x1
L41b0:
        lsl     x1, x2, x0
        cbz     w3,L421c
        lsr     x1, x1, x16
        lsl     x1, x1, #2
        add     x17, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x6]
        ldrb    w22, [x17, #2]
        ldrb    w1, [x17, #3]
        add     w0, w22, w0
        add     x6, x6, x1
        cmp     w0, #0x40
        b.hi    L49bc
L41e4:
        lsr     w1, w0, #3
        cmp     x13, x19
        b.cs    L48e0
        sub     x1, x13, x1
        cmp     x13, x9
        b.eq    L4870
        lsr     w2, w0, #3
        cmp     x9, x1
        b.ls    L419c
        sub     w2, w13, w9
        sub     x1, x13, x9
        sub     x13, x13, x2
        sub     w0, w0, w1, lsl #3
        ldr     x2, [x13]
L421c:
        mov     x7, x13
        str     x2, [sp, #304]
        str     w0, [sp, #312]
        str     x13, [sp, #320]
L422c:
        cmp     x6, x4
        b.hi    L4278
        ldr     x16, [sp, #304]
        neg     w3, w23
        ldr     w1, [sp, #312]
        and     w3, w3, #0x3f
L4244:
        lsl     x0, x16, x1
        lsr     x0, x0, x3
        lsl     x0, x0, #2
        add     x2, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x6]
        ldrb    w13, [x2, #3]
        ldrb    w0, [x2, #2]
        add     x6, x6, x13
        add     w1, w1, w0
        cmp     x6, x4
        b.ls    L4244
        str     w1, [sp, #312]
L4278:
        cmp     x11, x6
        b.ls    L42d0
        ldr     x0, [sp, #304]
        neg     w2, w23
        ldr     w1, [sp, #312]
        lsl     x0, x0, x1
        lsr     x0, x0, x2
        lsl     x0, x0, #2
        add     x2, x5, x0
        ldrb    w0, [x5, x0]
        strb    w0, [x6]
        ldrb    w0, [x2, #3]
        cmp     w0, #0x1
        b.eq    L5204
        cmp     w1, #0x3f
        b.hi    L42d0
        ldrb    w0, [x2, #2]
        mov     w2, #0x40
        add     w0, w0, w1
        cmp     w0, #0x41
        csel    w0, w0, w2, cc
        str     w0, [sp, #312]
L42d0:
        sub     x6, x14, x10
        ldr     w0, [sp, #352]
        cmp     x6, #0x7
        b.ls    L4a68
        cmp     w23, #0xb
        b.ls    L4f48
        cmp     w0, #0x40
        b.hi    L4a58
        neg     w6, w23
        mov     w3, #0x0
        ldr     x11, [sp, #120]
        and     w6, w6, #0x3f
        ldr     x2, [sp, #344]
        ldr     x4, [sp, #360]
        b       L43cc
L430c:
        cmp     x11, x10
        sub     w0, w0, w2, lsl #3
        ldr     x2, [x1]
        cset    w3, hi
        mov     x4, x1
L4320:
        lsl     x1, x2, x0
        cbz     w3,L4408
        lsr     x1, x1, x6
        lsl     x1, x1, #2
        add     x13, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x10]
        ldrb    w1, [x13, #2]
        ldrb    w17, [x13, #3]
        add     w1, w1, w0
        add     x16, x10, x17
        lsl     x0, x2, x1
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x13, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x10, x17]
        ldrb    w10, [x13, #2]
        ldrb    w19, [x13, #3]
        add     w10, w10, w1
        add     x17, x16, x19
        lsl     x0, x2, x10
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x13, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x16, x19]
        ldrb    w1, [x13, #2]
        ldrb    w16, [x13, #3]
        add     w1, w1, w10
        add     x10, x17, x16
        lsl     x0, x2, x1
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x13, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x17, x16]
        ldrb    w0, [x13, #2]
        ldrb    w13, [x13, #3]
        add     w0, w0, w1
        add     x10, x10, x13
        cmp     w0, #0x40
        b.hi    L4a4c
L43cc:
        ldr     x13, [sp, #112]
        lsr     w1, w0, #3
        cmp     x13, x4
        b.ls    L4c38
        sub     x1, x4, x1
        cmp     x24, x4
        b.eq    L48b0
        lsr     w2, w0, #3
        cmp     x24, x1
        b.ls    L430c
L43f4:
        sub     w2, w4, w24
        sub     x1, x4, x24
        sub     x4, x4, x2
        sub     w0, w0, w1, lsl #3
        ldr     x2, [x4]
L4408:
        sub     x6, x14, x10
        str     x2, [sp, #344]
        str     w0, [sp, #352]
        str     x4, [sp, #360]
L4418:
        cmp     x6, #0x1
        b.ls    L4c98
        ldr     w0, [sp, #352]
        sub     x4, x14, #0x2
        .inst   0xf0000001  // adrp x1, 0x7000
        cmp     w0, #0x40
        b.hi    L4998
        ldr     x1, [sp, #360]
        neg     w11, w23
        ldr     x17, [sp, #112]
        and     w11, w11, #0x3f
        ldr     x2, [sp, #344]
        mov     x3, x1
        b       L4498
L4450:
        cmp     x10, x4
        sub     w0, w0, w2, lsl #3
        ldr     x2, [x6]
        cset    w8, ls
        mov     x3, x6
L4464:
        lsl     x6, x2, x0
        cbz     w8,L44d0
        lsr     x6, x6, x11
        lsl     x6, x6, #2
        add     x13, x5, x6
        ldrh    w6, [x5, x6]
        strh    w6, [x10]
        ldrb    w16, [x13, #2]
        ldrb    w6, [x13, #3]
        add     w0, w16, w0
        add     x10, x10, x6
        cmp     w0, #0x40
        b.hi    L498c
L4498:
        lsr     w6, w0, #3
        cmp     x3, x17
        b.cs    L4910
        sub     x6, x3, x6
        cmp     x24, x3
        b.eq    L4864
        lsr     w2, w0, #3
        cmp     x24, x6
        b.ls    L4450
        sub     w2, w3, w24
        sub     x1, x3, x24
        sub     x3, x3, x2
        sub     w0, w0, w1, lsl #3
        ldr     x2, [x3]
L44d0:
        str     x2, [sp, #344]
        str     w0, [sp, #352]
L44d8:
        cmp     x10, x4
        b.hi    L4524
        ldr     x11, [sp, #344]
        neg     w6, w23
        ldr     w1, [sp, #352]
        and     w6, w6, #0x3f
L44f0:
        lsl     x0, x11, x1
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x2, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x10]
        ldrb    w8, [x2, #3]
        ldrb    w0, [x2, #2]
        add     x10, x10, x8
        add     w1, w1, w0
        cmp     x10, x4
        b.ls    L44f0
        str     w1, [sp, #352]
L4524:
        cmp     x14, x10
        b.ls    L457c
        ldr     x0, [sp, #344]
        neg     w2, w23
        ldr     w1, [sp, #352]
        lsl     x0, x0, x1
        lsr     x0, x0, x2
        lsl     x0, x0, #2
        add     x2, x5, x0
        ldrb    w0, [x5, x0]
        strb    w0, [x10]
        ldrb    w0, [x2, #3]
        cmp     w0, #0x1
        b.eq    L5214
        cmp     w1, #0x3f
        b.hi    L457c
        ldrb    w0, [x2, #2]
        mov     w2, #0x40
        add     w0, w0, w1
        cmp     w0, #0x41
        csel    w0, w0, w2, cc
        str     w0, [sp, #352]
L457c:
        mov     w2, #0x0
        cmp     x18, x21
        b.eq    L50a8
L4588:
        mov     w1, #0x0
        cmp     x15, x12
        b.eq    L5098
L4594:
        cmp     x9, x7
        b.eq    L4788
L459c:
        ldp     x25, x26, [sp, #64]
L45a0:
        mov     x0, #0xffffffffffffffec
        ldp     x27, x28, [sp, #80]
        b       L333c
L45ac:
        sub     x3, x3, x2, lsr #3
        and     w1, w2, #0x7
        mov     x2, x8
        ldr     x4, [x3]
        cmp     x6, #0x1
        b.gt    L335c
        b       L3418
L45c8:
        ldrb    w6, [x18, w4, uxtw]
        str     x6, [sp, #264]
        str     x15, [sp, #280]
        cmp     w7, #0x5
        b.eq    L464c
        b.hi    L4634
        cmp     w7, #0x3
        b.eq    L45f8
        cmp     w7, #0x4
        b.ne    L4658
L45f0:
        ldrb    w4, [x15, #3]
        add     x6, x6, x4, lsl #24
L45f8:
        ldrb    w4, [x15, #2]
        add     x6, x6, x4, lsl #16
L4600:
        ldrb    w4, [x15, #1]
        add     x4, x6, x4, lsl #8
        str     x4, [sp, #264]
L460c:
        cbz     w16,L45a0
        mov     w22, #0x8
        sub     w22, w22, w7
        clz     w4, w16
        add     w22, w4, w22, lsl #3
        sub     w22, w22, #0x17
        b       L3580
L4628:
        ldp     x27, x28, [sp, #80]
L462c:
        mov     x0, #0xffffffffffffffb8
        b       L333c
L4634:
        cmp     w7, #0x6
        b.eq    L4644
        ldrb    w4, [x15, #6]
        add     x6, x6, x4, lsl #48
L4644:
        ldrb    w4, [x15, #5]
        add     x6, x6, x4, lsl #40
L464c:
        ldrb    w4, [x15, #4]
        add     x6, x6, x4, lsl #32
        b       L45f0
L4658:
        cmp     w7, #0x2
        b.eq    L4600
        b       L460c
L4664:
        ldrb    w4, [x15, w7, uxtw]
        str     x4, [sp, #304]
        str     x9, [sp, #320]
        cmp     w5, #0x5
        b.eq    L46dc
        b.hi    L46c4
        cmp     w5, #0x3
        b.eq    L4694
        cmp     w5, #0x4
        b.ne    L46e8
L468c:
        ldrb    w6, [x9, #3]
        add     x4, x4, x6, lsl #24
L4694:
        ldrb    w6, [x9, #2]
        add     x4, x4, x6, lsl #16
L469c:
        ldrb    w6, [x9, #1]
        add     x6, x4, x6, lsl #8
        str     x6, [sp, #304]
L46a8:
        cbz     w16,L45a0
        mov     w21, #0x8
        sub     w21, w21, w5
        clz     w4, w16
        add     w4, w4, w21, lsl #3
        sub     w21, w4, #0x17
        b       L35c4
L46c4:
        cmp     w5, #0x6
        b.eq    L46d4
        ldrb    w6, [x9, #6]
        add     x4, x4, x6, lsl #48
L46d4:
        ldrb    w6, [x9, #5]
        add     x4, x4, x6, lsl #40
L46dc:
        ldrb    w6, [x9, #4]
        add     x4, x4, x6, lsl #32
        b       L468c
L46e8:
        cmp     w5, #0x2
        b.eq    L469c
        b       L46a8
L46f4:
        ldrb    w2, [x9, w5, uxtw]
        str     x2, [sp, #344]
        str     x24, [sp, #360]
        cmp     x0, #0x5
        b.eq    L4770
        b.hi    L4758
        cmp     x0, #0x3
        b.eq    L4724
        cmp     x0, #0x4
        b.ne    L477c
L471c:
        ldrb    w5, [x24, #3]
        add     x2, x2, x5, lsl #24
L4724:
        ldrb    w5, [x24, #2]
        add     x2, x2, x5, lsl #16
L472c:
        ldrb    w5, [x24, #1]
        add     x2, x2, x5, lsl #8
        str     x2, [sp, #344]
L4738:
        cbz     w4,L45a0
        mov     w2, #0x8
        sub     w2, w2, w0
        clz     w0, w4
        add     w0, w0, w2, lsl #3
        sub     w0, w0, #0x17
        str     w0, [sp, #352]
        b       L3614
L4758:
        cmp     x0, #0x6
        b.eq    L4768
        ldrb    w5, [x24, #6]
        add     x2, x2, x5, lsl #48
L4768:
        ldrb    w5, [x24, #5]
        add     x2, x2, x5, lsl #40
L4770:
        ldrb    w5, [x24, #4]
        add     x2, x2, x5, lsl #32
        b       L471c
L477c:
        cmp     x0, #0x2
        b.eq    L472c
        b       L4738
L4788:
        ldr     w0, [sp, #312]
        cmp     x24, x3
        b.ne    L459c
        cmp     w0, #0x40
        ldr     w3, [sp, #352]
        cset    w0, eq
        and     w0, w0, w2
        cmp     w3, #0x40
        and     w0, w0, w1
        cset    w1, ne
        eor     w0, w0, #0x1
        orr     w0, w1, w0
        cbnz    w0,L459c
        ldp     x25, x26, [sp, #64]
        mov     x0, x20
L47c4:
        ldp     x27, x28, [sp, #80]
        b       L333c
L47cc:
        mov     w0, #0x3
        b       L36f0
L47d4:
        ldr     w1, [sp, #140]
        mov     x2, x15
        str     w3, [sp, #232]
        mov     x4, x11
        str     w22, [sp, #272]
        mov     x0, x12
        str     w21, [sp, #312]
        mov     x25, x13
        str     w8, [sp, #352]
        mov     x26, x18
        ldp     x12, x13, [sp, #160]
        mov     x27, x14
        ldp     x14, x18, [sp, #144]
        ldr     x11, [sp, #176]
        ldp     x20, x15, [sp, #192]
        ldp     x9, x24, [sp, #208]
        ldr     w23, [sp, #188]
        cbz     w1,L4824
        str     x0, [sp, #224]
        str     x16, [sp, #240]
L4824:
        ldr     w0, [sp, #132]
        cbz     w0,L4834
        str     x25, [sp, #264]
        str     x17, [sp, #280]
L4834:
        ldr     w0, [sp, #136]
        cbz     w0,L4844
        str     x27, [sp, #304]
        str     x26, [sp, #320]
L4844:
        ldr     w0, [sp, #184]
        cbz     w0,L52f4
L484c:
        ldp     x25, x26, [sp, #64]
        str     x4, [sp, #344]
        str     x2, [sp, #360]
        b       L3a98
L485c:
        mov     w0, #0x3
        b       L3714
L4864:
        cbnz    w8,L44d0
        mov     x3, x1
        b       L44d8
L4870:
        cbz     w3,L422c
        mov     x7, x9
        str     x2, [sp, #304]
        str     w0, [sp, #312]
        str     x9, [sp, #320]
        b       L422c
L4888:
        cbz     w3,L4c58
        str     x2, [sp, #264]
        str     w0, [sp, #272]
        str     x15, [sp, #280]
        b       L3f74
L489c:
        cbz     w3,L4c50
        str     x2, [sp, #224]
        str     w0, [sp, #232]
        str     x18, [sp, #240]
        b       L3cc0
L48b0:
        sub     x6, x14, x10
        cbz     w3,L4418
        str     x2, [sp, #344]
        str     w0, [sp, #352]
        str     x24, [sp, #360]
        b       L4418
L48c8:
        sub     x21, x12, x19
        cbz     w2,L3bfc
        str     x1, [sp, #224]
        str     w0, [sp, #232]
        str     x18, [sp, #240]
        b       L3bfc
L48e0:
        sub     x13, x13, x1
        cmp     x6, x4
        and     w0, w0, #0x7
        cset    w3, ls
        ldr     x2, [x13]
        b       L41b0
L48f8:
        sub     x13, x11, x6
        cbz     w3,L4160
        str     x2, [sp, #304]
        str     w0, [sp, #312]
        str     x9, [sp, #320]
        b       L4160
L4910:
        sub     x3, x3, x6
        cmp     x10, x4
        and     w0, w0, #0x7
        cset    w8, ls
        ldr     x2, [x3]
        b       L4464
L4928:
        sub     x12, x12, x1
        cmp     x7, x4
        and     w0, w0, #0x7
        cset    w3, ls
        ldr     x2, [x12]
        b       L3efc
L4940:
        sub     x19, x13, x7
        cbz     w3,L3eac
        str     x2, [sp, #264]
        str     w0, [sp, #272]
        str     x15, [sp, #280]
        b       L3eac
L4958:
        sub     x21, x21, x1
        cmp     x19, x4
        and     w0, w0, #0x7
        cset    w3, ls
        ldr     x2, [x21]
        b       L3c48
L4970:
        .inst   0xf0000001  // adrp x1, 0x7000
        str     x2, [sp, #224]
        str     w0, [sp, #232]
L497c:
        add     x1, x1, #0xbf0
        str     x1, [sp, #240]
        mov     x21, x1
        b       L3cc0
L498c:
        .inst   0xf0000001  // adrp x1, 0x7000
        str     x2, [sp, #344]
        str     w0, [sp, #352]
L4998:
        add     x3, x1, #0xbf0
        b       L44d8
L49a0:
        .inst   0xf0000001  // adrp x1, 0x7000
        str     x2, [sp, #264]
        str     w0, [sp, #272]
L49ac:
        add     x1, x1, #0xbf0
        str     x1, [sp, #280]
        mov     x12, x1
        b       L3f74
L49bc:
        .inst   0xf0000001  // adrp x1, 0x7000
        str     x2, [sp, #304]
        str     w0, [sp, #312]
L49c8:
        add     x1, x1, #0xbf0
        str     x1, [sp, #320]
        mov     x7, x1
        b       L422c
L49d8:
        sub     x19, x13, x7
        str     x2, [sp, #264]
        str     w0, [sp, #272]
L49e4:
        .inst   0xf0000001  // adrp x1, 0x7000
        add     x1, x1, #0xbf0
        str     x1, [sp, #280]
        b       L3eac
L49f4:
        cmp     w0, #0x40
        b.hi    L5250
        ldr     x2, [sp, #96]
        ldr     x1, [sp, #280]
        cmp     x1, x2
        b.cs    L52d8
        cmp     x15, x1
        b.eq    L3eac
        lsr     w3, w0, #3
        lsr     w2, w0, #3
        sub     x4, x1, x3
        cmp     x15, x4
        b.ls    L4a30
        sub     w2, w1, w15
        sub     w3, w1, w15
L4a30:
        sub     x1, x1, x3
        sub     w2, w0, w2, lsl #3
        str     w2, [sp, #272]
        str     x1, [sp, #280]
        ldr     x0, [x1]
        str     x0, [sp, #264]
        b       L3eac
L4a4c:
        sub     x6, x14, x10
        str     x2, [sp, #344]
        str     w0, [sp, #352]
L4a58:
        .inst   0xf0000001  // adrp x1, 0x7000
        add     x1, x1, #0xbf0
        str     x1, [sp, #360]
        b       L4418
L4a68:
        cmp     w0, #0x40
        b.hi    L52bc
        ldr     x2, [sp, #112]
        ldr     x1, [sp, #360]
        cmp     x1, x2
        b.cs    L52b0
        cmp     x24, x1
        b.eq    L4418
        lsr     w3, w0, #3
        lsr     w2, w0, #3
        sub     x4, x1, x3
        cmp     x24, x4
        b.ls    L4aa4
        sub     w2, w1, w24
        sub     w3, w1, w24
L4aa4:
        sub     x1, x1, x3
        sub     w2, w0, w2, lsl #3
        ldr     x0, [x1]
        str     x0, [sp, #344]
        str     w2, [sp, #352]
        str     x1, [sp, #360]
        b       L4418
L4ac0:
        sub     x13, x11, x6
        str     x2, [sp, #304]
        str     w0, [sp, #312]
L4acc:
        .inst   0xf0000001  // adrp x1, 0x7000
        add     x1, x1, #0xbf0
        str     x1, [sp, #320]
        b       L4160
L4adc:
        cmp     w0, #0x40
        b.hi    L5294
        ldr     x2, [sp, #104]
        ldr     x1, [sp, #320]
        cmp     x1, x2
        b.cs    L5244
        cmp     x9, x1
        b.eq    L4160
        lsr     w3, w0, #3
        lsr     w2, w0, #3
        sub     x4, x1, x3
        cmp     x9, x4
        b.ls    L4b18
        sub     w2, w1, w9
        sub     w3, w1, w9
L4b18:
        sub     x1, x1, x3
        sub     w2, w0, w2, lsl #3
        str     w2, [sp, #312]
        str     x1, [sp, #320]
        ldr     x0, [x1]
        str     x0, [sp, #304]
        b       L4160
L4b34:
        sub     x21, x12, x19
        str     x1, [sp, #224]
        str     w0, [sp, #232]
L4b40:
        .inst   0xf0000001  // adrp x1, 0x7000
        add     x1, x1, #0xbf0
        str     x1, [sp, #240]
        b       L3bfc
L4b50:
        cmp     w0, #0x40
        b.hi    L5278
        ldr     x1, [sp, #240]
        cmp     x1, x28
        b.cs    L526c
        cmp     x18, x1
        b.eq    L3bfc
        lsr     w3, w0, #3
        lsr     w2, w0, #3
        sub     x4, x1, x3
        cmp     x18, x4
        b.ls    L4b88
        sub     w2, w1, w18
        sub     w3, w1, w18
L4b88:
        sub     x1, x1, x3
        sub     w2, w0, w2, lsl #3
        str     w2, [sp, #232]
        str     x1, [sp, #240]
        ldr     x0, [x1]
        str     x0, [sp, #224]
        b       L3bfc
L4ba4:
        sub     x3, x3, x4
        cmp     x19, x25
        and     w0, w0, #0x7
        cset    w2, cc
        ldr     x1, [x3]
        b       L3b08
L4bbc:
        ldr     w1, [sp, #140]
        mov     x2, x15
        str     w3, [sp, #232]
        mov     x4, x11
        str     w22, [sp, #272]
        mov     x0, x12
        str     w21, [sp, #312]
        mov     x25, x13
        str     w8, [sp, #352]
        mov     x26, x18
        ldp     x12, x13, [sp, #160]
        mov     x27, x14
        ldp     x14, x18, [sp, #144]
        ldr     x11, [sp, #176]
        ldp     x20, x15, [sp, #192]
        ldp     x9, x24, [sp, #208]
        ldr     w23, [sp, #188]
        cbz     w1,L4c0c
        str     x0, [sp, #224]
        str     x16, [sp, #240]
L4c0c:
        ldr     w0, [sp, #132]
        cbz     w0,L4c1c
        str     x25, [sp, #264]
        str     x17, [sp, #280]
L4c1c:
        ldr     w0, [sp, #136]
        cbz     w0,L484c
        str     x27, [sp, #304]
        str     x26, [sp, #320]
        b       L484c
L4c30:
        ldr     x21, [sp, #240]
        b       L3d0c
L4c38:
        sub     x4, x4, x1
        cmp     x11, x10
        and     w0, w0, #0x7
        cset    w3, hi
        ldr     x2, [x4]
        b       L4320
L4c50:
        mov     x21, x17
        b       L3cc0
L4c58:
        mov     x12, x17
        b       L3f74
L4c60:
        sub     x4, x4, x17
        cmp     x7, x16
        and     w1, w0, #0x7
        cset    w3, cc
        ldr     x2, [x4]
        b       L3db4
L4c78:
        sub     x4, x4, x16
        cmp     x6, x13
        and     w1, w0, #0x7
        cset    w3, cc
        ldr     x2, [x4]
        b       L4068
L4c90:
        ldr     x7, [sp, #320]
        b       L4278
L4c98:
        ldr     x3, [sp, #360]
        b       L4524
L4ca0:
        ldr     x12, [sp, #280]
        b       L3fc0
L4ca8:
        cmp     w0, #0x40
        b.hi    L4acc
        neg     w7, w23
        sub     x13, x11, #0x9
        ldr     x2, [sp, #304]
        and     w7, w7, #0x3f
        ldr     x4, [sp, #320]
        mov     w3, #0x0
        b       L4db4
L4ccc:
        ldr     x2, [x16]
        cmp     x6, x13
        sub     w1, w0, w1, lsl #3
        cset    w3, cc
        mov     x4, x16
L4ce0:
        lsl     x0, x2, x1
        cbz     w3,L4150
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x6]
        ldrb    w16, [x17, #2]
        ldrb    w22, [x17, #3]
        add     w16, w16, w1
        add     x19, x6, x22
        lsl     x0, x2, x16
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x6, x22]
        ldrb    w1, [x17, #2]
        ldrb    w6, [x17, #3]
        add     w1, w1, w16
        add     x17, x19, x6
        lsl     x0, x2, x1
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x16, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x6]
        ldrb    w6, [x16, #2]
        ldrb    w22, [x16, #3]
        add     w6, w6, w1
        add     x19, x17, x22
        lsl     x0, x2, x6
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x16, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x17, x22]
        ldrb    w1, [x16, #2]
        ldrb    w17, [x16, #3]
        add     w1, w1, w6
        add     x6, x19, x17
        lsl     x0, x2, x1
        lsr     x0, x0, x7
        lsl     x0, x0, #2
        add     x16, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x17]
        ldrb    w0, [x16, #2]
        ldrb    w16, [x16, #3]
        add     w0, w0, w1
        add     x6, x6, x16
        cmp     w0, #0x40
        b.hi    L4ac0
L4db4:
        ldr     x1, [sp, #104]
        lsr     w16, w0, #3
        cmp     x1, x4
        b.ls    L4de0
        sub     x16, x4, x16
        cmp     x9, x4
        b.eq    L48f8
        lsr     w1, w0, #3
        cmp     x9, x16
        b.hi    L413c
        b       L4ccc
L4de0:
        sub     x4, x4, x16
        cmp     x6, x13
        and     w1, w0, #0x7
        cset    w3, cc
        ldr     x2, [x4]
        b       L4ce0
L4df8:
        cmp     w0, #0x40
        b.hi    L49e4
        neg     w12, w23
        sub     x16, x13, #0x9
        ldr     x2, [sp, #264]
        and     w12, w12, #0x3f
        ldr     x4, [sp, #280]
        mov     w3, #0x0
        b       L4f04
L4e1c:
        ldr     x2, [x17]
        cmp     x7, x16
        sub     w1, w0, w1, lsl #3
        cset    w3, cc
        mov     x4, x17
L4e30:
        lsl     x0, x2, x1
        cbz     w3,L3e9c
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x19, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x7]
        ldrb    w17, [x19, #2]
        ldrb    w25, [x19, #3]
        add     w17, w17, w1
        add     x19, x7, x25
        lsl     x0, x2, x17
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x22, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x7, x25]
        ldrb    w1, [x22, #2]
        ldrb    w7, [x22, #3]
        add     w1, w1, w17
        add     x17, x19, x7
        lsl     x0, x2, x1
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x22, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x7]
        ldrb    w7, [x22, #2]
        ldrb    w25, [x22, #3]
        add     w7, w7, w1
        add     x19, x17, x25
        lsl     x0, x2, x7
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x22, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x17, x25]
        ldrb    w1, [x22, #2]
        ldrb    w22, [x22, #3]
        add     w1, w1, w7
        add     x7, x19, x22
        lsl     x0, x2, x1
        lsr     x0, x0, x12
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x22]
        ldrb    w0, [x17, #2]
        ldrb    w17, [x17, #3]
        add     w0, w0, w1
        add     x7, x7, x17
        cmp     w0, #0x40
        b.hi    L49d8
L4f04:
        ldr     x1, [sp, #96]
        lsr     w17, w0, #3
        cmp     x1, x4
        b.ls    L4f30
        sub     x17, x4, x17
        cmp     x15, x4
        b.eq    L4940
        lsr     w1, w0, #3
        cmp     x15, x17
        b.hi    L3e88
        b       L4e1c
L4f30:
        sub     x4, x4, x17
        cmp     x7, x16
        and     w1, w0, #0x7
        cset    w3, cc
        ldr     x2, [x4]
        b       L4e30
L4f48:
        cmp     w0, #0x40
        b.hi    L4a58
        neg     w6, w23
        sub     x11, x14, #0x9
        ldr     x2, [sp, #344]
        and     w6, w6, #0x3f
        ldr     x4, [sp, #360]
        mov     w3, #0x0
        b       L5054
L4f6c:
        cmp     x10, x11
        sub     w0, w0, w2, lsl #3
        ldr     x2, [x1]
        cset    w3, cc
        mov     x4, x1
L4f80:
        lsl     x1, x2, x0
        cbz     w3,L4408
        lsr     x1, x1, x6
        lsl     x1, x1, #2
        add     x16, x5, x1
        ldrh    w1, [x5, x1]
        strh    w1, [x10]
        ldrb    w13, [x16, #2]
        ldrb    w1, [x16, #3]
        add     w13, w13, w0
        add     x16, x10, x1
        lsl     x0, x2, x13
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x10, x1]
        ldrb    w1, [x17, #2]
        ldrb    w10, [x17, #3]
        add     w1, w1, w13
        add     x19, x16, x10
        lsl     x0, x2, x1
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x13, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x16, x10]
        ldrb    w10, [x13, #2]
        ldrb    w16, [x13, #3]
        add     w10, w10, w1
        add     x17, x19, x16
        lsl     x0, x2, x10
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x13, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x16]
        ldrb    w1, [x13, #2]
        ldrb    w16, [x13, #3]
        add     w1, w1, w10
        add     x10, x17, x16
        lsl     x0, x2, x1
        lsr     x0, x0, x6
        lsl     x0, x0, #2
        add     x13, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x17, x16]
        ldrb    w0, [x13, #2]
        ldrb    w13, [x13, #3]
        add     w0, w0, w1
        add     x10, x10, x13
        cmp     w0, #0x40
        b.hi    L4a4c
L5054:
        ldr     x13, [sp, #112]
        lsr     w1, w0, #3
        cmp     x13, x4
        b.ls    L5080
        sub     x1, x4, x1
        cmp     x24, x4
        b.eq    L48b0
        lsr     w2, w0, #3
        cmp     x24, x1
        b.hi    L43f4
        b       L4f6c
L5080:
        sub     x4, x4, x1
        cmp     x10, x11
        and     w0, w0, #0x7
        cset    w3, cc
        ldr     x2, [x4]
        b       L4f80
L5098:
        ldr     w0, [sp, #272]
        cmp     w0, #0x40
        cset    w1, eq
        b       L4594
L50a8:
        ldr     w0, [sp, #232]
        cmp     w0, #0x40
        cset    w2, eq
        b       L4588
L50b8:
        cmp     w0, #0x40
        b.hi    L4b40
        neg     w4, w23
        sub     x26, x12, #0x9
        ldr     x1, [sp, #224]
        and     w4, w4, #0x3f
        ldr     x3, [sp, #240]
        mov     w2, #0x0
        b       L51c4
L50dc:
        cmp     x19, x26
        sub     w0, w0, w1, lsl #3
        ldr     x1, [x16]
        cset    w2, cc
        mov     x3, x16
L50f0:
        lsl     x16, x1, x0
        cbz     w2,L3bec
        lsr     x16, x16, x4
        lsl     x16, x16, #2
        add     x17, x5, x16
        ldrh    w16, [x5, x16]
        strh    w16, [x19]
        ldrb    w16, [x17, #2]
        ldrb    w22, [x17, #3]
        add     w16, w16, w0
        add     x17, x19, x22
        lsl     x0, x1, x16
        lsr     x0, x0, x4
        lsl     x0, x0, #2
        add     x21, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x19, x22]
        ldrb    w19, [x21, #2]
        ldrb    w22, [x21, #3]
        add     w19, w19, w16
        add     x16, x17, x22
        lsl     x0, x1, x19
        lsr     x0, x0, x4
        lsl     x0, x0, #2
        add     x21, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x17, x22]
        ldrb    w17, [x21, #2]
        ldrb    w22, [x21, #3]
        add     w17, w17, w19
        add     x21, x16, x22
        lsl     x0, x1, x17
        lsr     x0, x0, x4
        lsl     x0, x0, #2
        add     x19, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x16, x22]
        ldrb    w16, [x19, #2]
        ldrb    w22, [x19, #3]
        add     w16, w16, w17
        add     x19, x21, x22
        lsl     x0, x1, x16
        lsr     x0, x0, x4
        lsl     x0, x0, #2
        add     x17, x5, x0
        ldrh    w0, [x5, x0]
        strh    w0, [x21, x22]
        ldrb    w0, [x17, #2]
        ldrb    w17, [x17, #3]
        add     w0, w0, w16
        add     x19, x19, x17
        cmp     w0, #0x40
        b.hi    L4b34
L51c4:
        lsr     w16, w0, #3
        cmp     x28, x3
        b.ls    L51ec
        sub     x16, x3, x16
        cmp     x18, x3
        b.eq    L48c8
        lsr     w1, w0, #3
        cmp     x18, x16
        b.hi    L3bd8
        b       L50dc
L51ec:
        sub     x3, x3, x16
        cmp     x19, x26
        and     w0, w0, #0x7
        cset    w2, cc
        ldr     x1, [x3]
        b       L50f0
L5204:
        ldrb    w0, [x2, #2]
        add     w0, w0, w1
        str     w0, [sp, #312]
        b       L42d0
L5214:
        ldrb    w0, [x2, #2]
        add     w0, w0, w1
        str     w0, [sp, #352]
        b       L457c
L5224:
        ldrb    w0, [x2, #2]
        add     w0, w0, w1
        str     w0, [sp, #272]
        b       L4018
L5234:
        ldrb    w0, [x2, #2]
        add     w0, w0, w1
        str     w0, [sp, #232]
        b       L3d64
L5244:
        add     x0, sp, #0x130
        bl      L1c20
        b       L4160
L5250:
        .inst   0xd0000001  // adrp x1, 0x7000
        add     x12, x1, #0xbf0
        str     x12, [sp, #280]
        cmp     x19, #0x1
        b.le    L3fc0
        sub     x4, x13, #0x2
        b       L49ac
L526c:
        add     x0, sp, #0xe0
        bl      L1c20
        b       L3bfc
L5278:
        .inst   0xd0000001  // adrp x1, 0x7000
        add     x0, x1, #0xbf0
        str     x0, [sp, #240]
        cmp     x21, #0x1
        b.le    L52e4
        sub     x4, x12, #0x2
        b       L497c
L5294:
        .inst   0xd0000001  // adrp x1, 0x7000
        add     x7, x1, #0xbf0
        str     x7, [sp, #320]
        cmp     x13, #0x1
        b.le    L4278
        sub     x4, x11, #0x2
        b       L49c8
L52b0:
        add     x0, sp, #0x158
        bl      L1c20
        b       L4418
L52bc:
        .inst   0xd0000001  // adrp x1, 0x7000
        add     x3, x1, #0xbf0
        cmp     x6, #0x1
        b.ls    L4524
        sub     x4, x14, #0x2
        add     x3, x1, #0xbf0
        b       L44d8
L52d8:
        add     x0, sp, #0x108
        bl      L1c20
        b       L3eac
L52e4:
        mov     x21, x0
        b       L3d0c
L52ec:
        mov     x3, x13
        b       L335c
L52f4:
        ldp     x25, x26, [sp, #64]
        b       L3a98
        nop

// HUF_decompress4X1_usingDTable_internal (0x13d4 bytes)
L5300:
        stp     x29, x30, [sp, #-496]!
        mov     x18, x2
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x19, x0
        mov     x20, x1
        stp     x21, x22, [sp, #32]
        mov     x22, x4
        stp     x23, x24, [sp, #48]
        mov     x23, x3
        tbnz    w5, #5,L5458
        cmp     x1, #0x0
        add     x21, x0, x1
        add     x24, sp, #0x158
        csel    x21, x21, x0, gt
        mov     x5, x4
        mov     x0, x24
        mov     x4, x3
        mov     x3, x2
        mov     x2, x1
        mov     x1, x19
        bl      L1de0
        cmn     x0, #0x78
        b.hi    L5444
        cbz     x0,L5458
        mov     x0, x24
        bl      L24a4
        add     x9, x20, #0x3
        add     x5, x22, #0x4
        mov     w10, #0x4
        lsr     x9, x9, #2
L537c:
        ldr     x3, [x0, #32]
        sub     x1, x21, x19
        cmp     x9, x1
        add     x19, x19, x9
        csel    x8, x19, x21, ls
        cmp     x8, x3
        b.cc    L5440
        ldr     x1, [x0, #120]
        ldr     x6, [x0]
        sub     x1, x1, #0x8
        cmp     x6, x1
        b.cc    L5440
        ldr     x2, [x0, #64]
        sub     x11, x8, x3
        ldr     x12, [sp, #448]
        rbit    x2, x2
        clz     x2, x2
        sub     x14, x8, #0x3
        ldr     x4, [x6]
        mov     w1, w2
        add     x13, x12, #0x8
        cmp     x11, #0x3
        b.gt    L59c0
        cmp     x6, x13
        b.cs    L5af0
        cmp     x6, x12
        b.eq    L59f4
        sub     x4, x6, x2, lsr #3
        lsr     w1, w2, #3
        cmp     x4, x12
        b.cs    L5404
        sub     x12, x6, x12
        mov     w1, w12
        sub     x4, x6, w12, uxtw
L5404:
        ldr     x4, [x4]
        sub     w1, w2, w1, lsl #3
        cmp     x8, x3
        b.hi    L5a00
        nop
L5418:
        ldr     x19, [x0, #32]
        add     x19, x19, x11
        str     x19, [x0, #32]
        cmp     x8, x19
        b.ne    L5440
        add     x0, x0, #0x8
        subs    w10, w10, #0x1
        b.ne    L537c
        cbnz    x20,L5b60
        nop
L5440:
        mov     x0, #0xffffffffffffffec
L5444:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x29, x30, [sp], #496
        ret
L5458:
        cmp     x20, #0x5
        ccmp    x23, #0x9, #0x0, hi
        b.ls    L5440
        add     x6, x20, #0x3
        ldrh    w5, [x18, #2]
        ldrh    w12, [x18]
        add     x9, x19, x20
        ldrh    w17, [x18, #4]
        lsr     x6, x6, #2
        add     x7, x19, x6
        ldr     w14, [x22]
        add     x0, x5, w12, uxth
        add     x8, x7, x6
        sub     x3, x23, w17, uxth
        add     x6, x8, x6
        sub     x3, x3, x0
        cmp     x9, x6
        sub     x0, x3, #0x6
        cset    w1, cc
        cmp     x23, x0
        mov     x13, x5
        cset    w10, cc
        mov     x2, x12
        mov     x4, x17
        orr     w1, w1, w10
        cbnz    w1,L5440
        cbz     x12,L5b6c
        add     x11, x18, #0x6
        stp     x25, x26, [sp, #64]
        add     x10, x11, x12
        add     x16, x18, #0xe
        stp     x11, x16, [sp, #248]
        ldurb   w15, [x10, #-1]
        cmp     x12, #0x7
        b.ls    L5a54
        sub     x12, x12, #0x8
        add     x18, x11, x12
        str     x18, [sp, #240]
        ldr     x12, [x11, x12]
        str     x12, [sp, #224]
        cbz     w15,L5a48
        clz     w15, w15
        sub     w26, w15, #0x17
L5504:
        str     w26, [sp, #232]
        cbz     x5,L5b68
        add     x15, x10, x5
        add     x12, x10, #0x8
        str     x12, [sp, #104]
        stp     x10, x12, [sp, #288]
        ldurb   w12, [x15, #-1]
        cmp     x5, #0x7
        b.ls    L5b00
        sub     x5, x5, #0x8
        add     x2, x10, x5
        str     x2, [sp, #280]
        ldr     x2, [x10, x5]
        str     x2, [sp, #264]
        cbz     w12,L5a48
        clz     w12, w12
        sub     w2, w12, #0x17
L5548:
        str     w2, [sp, #272]
        cbz     x17,L5b68
        stp     x27, x28, [sp, #80]
        add     x27, x15, x17
        add     x5, x15, #0x8
        str     x5, [sp, #128]
        stp     x15, x5, [sp, #328]
        ldurb   w5, [x27, #-1]
        cmp     x17, #0x7
        b.ls    L5ba4
        sub     x17, x17, #0x8
        add     x12, x15, x17
        str     x12, [sp, #320]
        ldr     x12, [x15, x17]
        str     x12, [sp, #304]
        cbz     w5,L5a44
        clz     w5, w5
        sub     w17, w5, #0x17
L5590:
        str     w17, [sp, #312]
        cbz     x0,L642c
        add     x5, x27, x3
        add     x12, x27, #0x8
        str     x12, [sp, #136]
        stp     x27, x12, [sp, #368]
        ldurb   w5, [x5, #-7]
        cmp     x0, #0x7
        b.ls    L5c44
        sub     x3, x3, #0xe
        add     x4, x27, x3
        str     x4, [sp, #360]
        ldr     x3, [x27, x3]
        str     x3, [sp, #344]
        cbz     w5,L5a44
        clz     w3, w5
        sub     w3, w3, #0x17
        str     w3, [sp, #352]
        cmn     x0, #0x78
        b.hi    L62ec
L55e0:
        sub     x3, x9, #0x3
        sub     x0, x9, x6
        str     x3, [sp, #112]
        add     x5, x22, #0x4
        ubfx    x23, x14, #16, #8
        cmp     x0, #0x7
        b.le    L5cd8
        cmp     x3, x6
        b.ls    L5cd8
        ldr     x4, [sp, #240]
        neg     w3, w23
        ldr     x28, [sp, #360]
        and     w3, w3, #0x3f
        ldr     x22, [sp, #224]
        mov     x12, x6
        ldr     x21, [sp, #264]
        mov     x14, x8
        ldr     x24, [sp, #280]
        mov     x13, x7
        ldr     x30, [sp, #304]
        str     wzr, [sp, #124]
        ldr     x25, [sp, #320]
        stp     x9, x11, [sp, #144]
        ldr     w0, [sp, #352]
        ldr     x18, [sp, #344]
        mov     x11, x28
        stp     x7, x8, [sp, #160]
        str     x6, [sp, #176]
        stp     wzr, w23, [sp, #184]
        mov     x23, x4
        stp     x20, x10, [sp, #192]
        ldr     x20, [sp, #104]
        stp     x15, x27, [sp, #208]
        mov     w15, #0x0
        ldp     x27, x10, [sp, #128]
        b       L56fc
L5670:
        lsr     w0, w26, #3
        and     w26, w26, #0x7
        sub     x23, x23, x0
        mov     w1, #0x1
        mov     w0, #0x0
        ldr     x22, [x23]
L5688:
        cmp     x20, x24
        b.hi    L6378
        lsr     w6, w2, #3
        and     w2, w2, #0x7
        sub     x24, x24, x6
        mov     w7, #0x1
        str     w7, [sp, #184]
        ldr     x21, [x24]
L56a8:
        cmp     x27, x25
        b.hi    L6370
        lsr     w6, w17, #3
        and     w17, w17, #0x7
        sub     x25, x25, x6
        mov     w7, #0x1
        str     w7, [sp, #124]
        ldr     x30, [x25]
L56c8:
        cmp     x10, x11
        b.hi    L62f8
        cmp     w0, #0x0
        lsr     w6, w4, #3
        ldr     x0, [sp, #112]
        sub     x11, x11, x6
        cset    w6, eq
        cmp     x0, x12
        and     w0, w4, #0x7
        cset    w4, hi
        ldr     x18, [x11]
        ands    w15, w6, w4
        b.eq    L65fc
L56fc:
        lsl     x8, x22, x26
        add     x19, x19, #0x4
        lsr     x8, x8, x3
        add     x13, x13, #0x4
        lsl     x8, x8, #1
        lsl     x4, x21, x2
        add     x9, x5, x8
        lsr     x4, x4, x3
        lsl     x4, x4, #1
        lsl     x6, x30, x17
        add     x7, x5, x4
        ldrb    w8, [x5, x8]
        ldrb    w9, [x9, #1]
        lsr     x6, x6, x3
        sturb   w9, [x19, #-4]
        lsl     x6, x6, #1
        add     w8, w8, w26
        add     x9, x5, x6
        ldrb    w28, [x7, #1]
        lsl     x26, x18, x0
        ldrb    w7, [x5, x4]
        lsr     x4, x26, x3
        sturb   w28, [x13, #-4]
        lsl     x4, x4, #1
        add     w7, w7, w2
        add     x26, x5, x4
        ldrb    w9, [x9, #1]
        lsl     x2, x22, x8
        ldrb    w6, [x5, x6]
        lsr     x2, x2, x3
        strb    w9, [x14]
        lsl     x2, x2, #1
        add     x9, x5, x2
        add     w6, w6, w17
        ldrb    w28, [x26, #1]
        lsl     x26, x21, x7
        ldrb    w17, [x5, x4]
        lsr     x4, x26, x3
        strb    w28, [x12]
        lsl     x4, x4, #1
        add     w17, w17, w0
        add     x26, x5, x4
        ldrb    w28, [x9, #1]
        lsl     x0, x30, x6
        ldrb    w9, [x5, x2]
        lsr     x0, x0, x3
        sturb   w28, [x19, #-3]
        lsl     x2, x0, #1
        add     x28, x5, x2
        lsl     x0, x18, x17
        ldrb    w26, [x26, #1]
        add     w9, w9, w8
        lsr     x0, x0, x3
        ldrb    w8, [x5, x4]
        sturb   w26, [x13, #-3]
        lsl     x0, x0, #1
        add     x26, x5, x0
        lsl     x4, x22, x9
        ldrb    w28, [x28, #1]
        add     w8, w8, w7
        ldrb    w7, [x5, x2]
        lsr     x2, x4, x3
        strb    w28, [x14, #1]
        lsl     x2, x2, #1
        add     w7, w7, w6
        add     x4, x5, x2
        ldrb    w28, [x26, #1]
        lsl     x26, x21, x8
        ldrb    w6, [x5, x0]
        lsr     x0, x26, x3
        strb    w28, [x12, #1]
        lsl     x0, x0, #1
        add     w6, w6, w17
        add     x26, x5, x0
        ldrb    w28, [x4, #1]
        lsl     x4, x30, x7
        ldrb    w17, [x5, x2]
        lsr     x4, x4, x3
        lsl     x2, x18, x6
        sturb   w28, [x19, #-2]
        add     w17, w17, w9
        lsl     x4, x4, #1
        lsr     x2, x2, x3
        ldrb    w28, [x26, #1]
        ldrb    w9, [x5, x0]
        lsl     x2, x2, #1
        add     x26, x5, x4
        lsl     x0, x22, x17
        sturb   w28, [x13, #-2]
        add     x28, x5, x2
        add     w9, w9, w8
        lsr     x0, x0, x3
        ldrb    w8, [x5, x4]
        lsl     x0, x0, #1
        ldrb    w26, [x26, #1]
        add     x14, x14, #0x4
        sturb   w26, [x14, #-2]
        add     x26, x5, x0
        ldrb    w4, [x28, #1]
        lsl     x28, x21, x9
        add     w8, w8, w7
        ldrb    w7, [x5, x2]
        lsr     x2, x28, x3
        strb    w4, [x12, #2]
        lsl     x2, x2, #1
        lsl     x4, x30, x8
        ldrb    w28, [x26, #1]
        add     x26, x5, x2
        ldrb    w0, [x5, x0]
        add     w7, w7, w6
        lsr     x4, x4, x3
        sturb   w28, [x19, #-1]
        lsl     x6, x4, #1
        lsl     x4, x18, x7
        ldrb    w26, [x26, #1]
        add     x28, x5, x6
        ldrb    w2, [x5, x2]
        lsr     x4, x4, x3
        sturb   w26, [x13, #-1]
        lsl     x4, x4, #1
        add     w26, w0, w17
        add     x0, x5, x4
        ldrb    w28, [x28, #1]
        add     x12, x12, #0x4
        ldrb    w17, [x5, x6]
        add     w2, w2, w9
        sturb   w28, [x14, #-1]
        add     w17, w17, w8
        ldrb    w4, [x5, x4]
        ldrb    w0, [x0, #1]
        sturb   w0, [x12, #-1]
        add     w4, w4, w7
        cmp     x16, x23
        b.ls    L5670
        mov     w0, #0x3
        b       L5688
L591c:
        cmp     x3, x14
        sub     w1, w1, w4, lsl #3
        ldr     x4, [x2]
        cset    w7, cc
        mov     x6, x2
L5930:
        lsl     x2, x4, x1
        cbz     w7,L59f4
        lsr     x2, x2, #53
        add     x3, x3, #0x4
        lsl     x2, x2, #1
        add     x7, x5, x2
        ldrb    w2, [x5, x2]
        ldrb    w7, [x7, #1]
        add     w2, w2, w1
        sturb   w7, [x3, #-4]
        lsl     x1, x4, x2
        lsr     x1, x1, #53
        lsl     x1, x1, #1
        add     x15, x5, x1
        ldrb    w7, [x5, x1]
        ldrb    w1, [x15, #1]
        add     w7, w7, w2
        sturb   w1, [x3, #-3]
        lsl     x1, x4, x7
        lsr     x1, x1, #53
        lsl     x1, x1, #1
        add     x15, x5, x1
        ldrb    w2, [x5, x1]
        ldrb    w1, [x15, #1]
        add     w2, w2, w7
        sturb   w1, [x3, #-2]
        lsl     x1, x4, x2
        lsr     x1, x1, #53
        lsl     x1, x1, #1
        add     x7, x5, x1
        ldrb    w1, [x5, x1]
        ldrb    w7, [x7, #1]
        add     w1, w1, w2
        sturb   w7, [x3, #-1]
        cmp     w1, #0x40
        b.hi    L59f4
L59c0:
        lsr     w2, w1, #3
        cmp     x13, x6
        b.ls    L5a2c
        sub     x2, x6, x2
        cmp     x12, x6
        b.eq    L59f4
        lsr     w4, w1, #3
        cmp     x2, x12
        b.cs    L591c
        sub     x12, x6, x12
        sub     x6, x6, w12, uxtw
        sub     w1, w1, w12, lsl #3
        ldr     x4, [x6]
L59f4:
        cmp     x8, x3
        b.ls    L5418
        nop
L5a00:
        lsl     x2, x4, x1
        lsr     x2, x2, #53
        lsl     x2, x2, #1
        add     x6, x5, x2
        ldrb    w2, [x5, x2]
        ldrb    w6, [x6, #1]
        strb    w6, [x3], #1
        add     w1, w1, w2
        cmp     x8, x3
        b.ne    L5a00
        b       L5418
L5a2c:
        sub     x6, x6, x2
        cmp     x3, x14
        and     w1, w1, #0x7
        cset    w7, cc
        ldr     x4, [x6]
        b       L5930
L5a44:
        ldp     x27, x28, [sp, #80]
L5a48:
        mov     x0, #0xffffffffffffffff
        ldp     x25, x26, [sp, #64]
        b       L5444
L5a54:
        ldrb    w12, [x18, #6]
        str     x12, [sp, #224]
        str     x11, [sp, #240]
        cmp     w2, #0x5
        b.eq    L5acc
        b.hi    L5ab4
        cmp     w2, #0x3
        b.eq    L5a84
        cmp     w2, #0x4
        b.ne    L5ad8
L5a7c:
        ldrb    w21, [x18, #9]
        add     x12, x12, x21, lsl #24
L5a84:
        ldrb    w21, [x18, #8]
        add     x12, x12, x21, lsl #16
L5a8c:
        ldrb    w18, [x18, #7]
        add     x12, x12, x18, lsl #8
        str     x12, [sp, #224]
L5a98:
        cbz     w15,L5ae4
        mov     w26, #0x8
        sub     w26, w26, w2
        clz     w15, w15
        add     w26, w15, w26, lsl #3
        sub     w26, w26, #0x17
        b       L5504
L5ab4:
        cmp     w2, #0x6
        b.eq    L5ac4
        ldrb    w21, [x18, #12]
        add     x12, x12, x21, lsl #48
L5ac4:
        ldrb    w21, [x18, #11]
        add     x12, x12, x21, lsl #40
L5acc:
        ldrb    w21, [x18, #10]
        add     x12, x12, x21, lsl #32
        b       L5a7c
L5ad8:
        cmp     w2, #0x2
        b.eq    L5a8c
        b       L5a98
L5ae4:
        ldp     x25, x26, [sp, #64]
        mov     x0, #0xffffffffffffffec
        b       L5444
L5af0:
        sub     x6, x6, x2, lsr #3
        and     w1, w2, #0x7
        ldr     x4, [x6]
        b       L59f4
L5b00:
        ldrb    w2, [x11, w2, uxtw]
        str     x2, [sp, #264]
        str     x10, [sp, #280]
        cmp     w13, #0x5
        b.eq    L5b8c
        b.hi    L5b74
        cmp     w13, #0x3
        b.eq    L5b30
        cmp     w13, #0x4
        b.ne    L5b98
L5b28:
        ldrb    w5, [x10, #3]
        add     x2, x2, x5, lsl #24
L5b30:
        ldrb    w5, [x10, #2]
        add     x2, x2, x5, lsl #16
L5b38:
        ldrb    w5, [x10, #1]
        add     x2, x2, x5, lsl #8
        str     x2, [sp, #264]
L5b44:
        cbz     w12,L5ae4
        mov     w2, #0x8
        sub     w2, w2, w13
        clz     w12, w12
        add     w2, w12, w2, lsl #3
        sub     w2, w2, #0x17
        b       L5548
L5b60:
        mov     x0, x20
        b       L5444
L5b68:
        ldp     x25, x26, [sp, #64]
L5b6c:
        mov     x0, #0xffffffffffffffb8
        b       L5444
L5b74:
        cmp     w13, #0x6
        b.eq    L5b84
        ldrb    w5, [x10, #6]
        add     x2, x2, x5, lsl #48
L5b84:
        ldrb    w5, [x10, #5]
        add     x2, x2, x5, lsl #40
L5b8c:
        ldrb    w5, [x10, #4]
        add     x2, x2, x5, lsl #32
        b       L5b28
L5b98:
        cmp     w13, #0x2
        b.eq    L5b38
        b       L5b44
L5ba4:
        ldrb    w12, [x10, w13, uxtw]
        str     x12, [sp, #304]
        str     x15, [sp, #320]
        cmp     w4, #0x5
        b.eq    L5c2c
        b.hi    L5c14
        cmp     w4, #0x3
        b.eq    L5bd4
        cmp     w4, #0x4
        b.ne    L5c38
L5bcc:
        ldrb    w13, [x15, #3]
        add     x12, x12, x13, lsl #24
L5bd4:
        ldrb    w13, [x15, #2]
        add     x12, x12, x13, lsl #16
L5bdc:
        ldrb    w13, [x15, #1]
        add     x12, x12, x13, lsl #8
        str     x12, [sp, #304]
L5be8:
        cbz     w5,L5c04
        mov     w17, #0x8
        sub     w17, w17, w4
        clz     w5, w5
        add     w17, w5, w17, lsl #3
        sub     w17, w17, #0x17
        b       L5590
L5c04:
        ldp     x25, x26, [sp, #64]
        mov     x0, #0xffffffffffffffec
        ldp     x27, x28, [sp, #80]
        b       L5444
L5c14:
        cmp     w4, #0x6
        b.eq    L5c24
        ldrb    w13, [x15, #6]
        add     x12, x12, x13, lsl #48
L5c24:
        ldrb    w13, [x15, #5]
        add     x12, x12, x13, lsl #40
L5c2c:
        ldrb    w13, [x15, #4]
        add     x12, x12, x13, lsl #32
        b       L5bcc
L5c38:
        cmp     w4, #0x2
        b.eq    L5bdc
        b       L5be8
L5c44:
        ldrb    w3, [x15, w4, uxtw]
        str     x3, [sp, #344]
        str     x27, [sp, #360]
        cmp     x0, #0x5
        b.eq    L5cc0
        b.hi    L5ca8
        cmp     x0, #0x3
        b.eq    L5c74
        cmp     x0, #0x4
        b.ne    L5ccc
L5c6c:
        ldrb    w4, [x27, #3]
        add     x3, x3, x4, lsl #24
L5c74:
        ldrb    w4, [x27, #2]
        add     x3, x3, x4, lsl #16
L5c7c:
        ldrb    w4, [x27, #1]
        add     x3, x3, x4, lsl #8
        str     x3, [sp, #344]
L5c88:
        cbz     w5,L5c04
        mov     w3, #0x8
        sub     w0, w3, w0
        clz     w5, w5
        add     w0, w5, w0, lsl #3
        sub     w0, w0, #0x17
        str     w0, [sp, #352]
        b       L55e0
L5ca8:
        cmp     x0, #0x6
        b.eq    L5cb8
        ldrb    w4, [x27, #6]
        add     x3, x3, x4, lsl #48
L5cb8:
        ldrb    w4, [x27, #5]
        add     x3, x3, x4, lsl #40
L5cc0:
        ldrb    w4, [x27, #4]
        add     x3, x3, x4, lsl #32
        b       L5c6c
L5ccc:
        cmp     x0, #0x2
        b.eq    L5c7c
        b       L5c88
L5cd8:
        mov     x12, x6
        mov     x14, x8
        mov     x13, x7
L5ce4:
        cmp     x8, x13
        ccmp    x7, x19, #0x0, cs
        cset    w18, cc
        cmp     x6, x14
        cset    w0, cc
        orr     w18, w18, w0
        cbnz    w18,L5c04
        sub     x1, x7, x19
        ldr     w0, [sp, #232]
        cmp     x1, #0x3
        b.le    L6534
        cmp     w0, #0x40
        b.hi    L6524
        ldr     x17, [sp, #240]
        neg     w4, w23
        ldr     x1, [sp, #224]
        and     w4, w4, #0x3f
        sub     x22, x7, #0x3
        mov     x21, x17
        mov     w3, #0x0
        b       L5ddc
L5d38:
        cmp     x19, x22
        sub     w0, w0, w1, lsl #3
        ldr     x1, [x2]
        cset    w3, cc
        mov     x21, x2
L5d4c:
        lsl     x2, x1, x0
        cbz     w3,L5e14
        lsr     x2, x2, x4
        add     x19, x19, #0x4
        lsl     x2, x2, #1
        add     x24, x5, x2
        ldrb    w2, [x5, x2]
        ldrb    w24, [x24, #1]
        add     w2, w2, w0
        sturb   w24, [x19, #-4]
        lsl     x0, x1, x2
        lsr     x0, x0, x4
        lsl     x0, x0, #1
        add     x25, x5, x0
        ldrb    w24, [x5, x0]
        ldrb    w0, [x25, #1]
        add     w24, w24, w2
        sturb   w0, [x19, #-3]
        lsl     x0, x1, x24
        lsr     x0, x0, x4
        lsl     x0, x0, #1
        add     x25, x5, x0
        ldrb    w2, [x5, x0]
        ldrb    w0, [x25, #1]
        add     w2, w2, w24
        sturb   w0, [x19, #-2]
        lsl     x0, x1, x2
        lsr     x0, x0, x4
        lsl     x0, x0, #1
        add     x24, x5, x0
        ldrb    w0, [x5, x0]
        ldrb    w24, [x24, #1]
        add     w0, w0, w2
        sturb   w24, [x19, #-1]
        cmp     w0, #0x40
        b.hi    L651c
L5ddc:
        lsr     w2, w0, #3
        cmp     x16, x21
        b.ls    L63c8
        sub     x2, x21, x2
        cmp     x11, x21
        b.eq    L63b4
        lsr     w1, w0, #3
        cmp     x11, x2
        b.ls    L5d38
        sub     w2, w21, w11
        sub     x1, x21, x11
        sub     x21, x21, x2
        sub     w0, w0, w1, lsl #3
        ldr     x1, [x21]
L5e14:
        str     x1, [sp, #224]
        str     w0, [sp, #232]
        str     x21, [sp, #240]
L5e20:
        cmp     x7, x19
        b.ls    L5e64
        ldr     x3, [sp, #224]
        neg     w2, w23
        ldr     w1, [sp, #232]
        and     w2, w2, #0x3f
L5e38:
        lsl     x0, x3, x1
        lsr     x0, x0, x2
        lsl     x0, x0, #1
        add     x4, x5, x0
        ldrb    w0, [x5, x0]
        ldrb    w4, [x4, #1]
        strb    w4, [x19], #1
        add     w1, w1, w0
        cmp     x7, x19
        b.ne    L5e38
        str     w1, [sp, #232]
L5e64:
        sub     x1, x8, x13
        ldr     w0, [sp, #272]
        cmp     x1, #0x3
        b.le    L6458
        cmp     w0, #0x40
        b.hi    L6444
        ldr     x4, [sp, #280]
        neg     w2, w23
        ldr     x19, [sp, #104]
        and     w2, w2, #0x3f
        ldr     x1, [sp, #264]
        sub     x16, x8, #0x3
        mov     x7, x4
        mov     w3, #0x0
        b       L5f44
L5ea0:
        sub     w0, w0, w1, lsl #3
        mov     x7, x17
        ldr     x1, [x17]
        cmp     x13, x16
        b.cs    L640c
L5eb4:
        lsl     x17, x1, x0
        add     x13, x13, #0x4
        lsr     x17, x17, x2
        mov     w3, #0x1
        lsl     x17, x17, #1
        add     x22, x5, x17
        ldrb    w17, [x5, x17]
        ldrb    w22, [x22, #1]
        add     w17, w17, w0
        sturb   w22, [x13, #-4]
        lsl     x0, x1, x17
        lsr     x0, x0, x2
        lsl     x0, x0, #1
        add     x24, x5, x0
        ldrb    w22, [x5, x0]
        ldrb    w0, [x24, #1]
        add     w22, w22, w17
        sturb   w0, [x13, #-3]
        lsl     x0, x1, x22
        lsr     x0, x0, x2
        lsl     x0, x0, #1
        add     x24, x5, x0
        ldrb    w17, [x5, x0]
        ldrb    w0, [x24, #1]
        add     w17, w17, w22
        sturb   w0, [x13, #-2]
        lsl     x0, x1, x17
        lsr     x0, x0, x2
        lsl     x0, x0, #1
        add     x22, x5, x0
        ldrb    w0, [x5, x0]
        ldrb    w22, [x22, #1]
        add     w0, w0, w17
        sturb   w22, [x13, #-1]
        cmp     w0, #0x40
        b.hi    L643c
L5f44:
        lsr     w17, w0, #3
        cmp     x19, x7
        b.ls    L63f8
        sub     x17, x7, x17
        cmp     x10, x7
        b.eq    L6394
        lsr     w1, w0, #3
        cmp     x10, x17
        b.ls    L5ea0
        sub     w1, w7, w10
        sub     x19, x7, x10
        sub     x7, x7, x1
        sub     w19, w0, w19, lsl #3
        ldr     x1, [x7]
L5f7c:
        str     x1, [sp, #264]
        str     w19, [sp, #272]
        str     x7, [sp, #280]
L5f88:
        cmp     x8, x13
        b.ls    L5fcc
        ldr     x4, [sp, #264]
        neg     w2, w23
        ldr     w1, [sp, #272]
        and     w2, w2, #0x3f
L5fa0:
        lsl     x0, x4, x1
        lsr     x0, x0, x2
        lsl     x0, x0, #1
        add     x3, x5, x0
        ldrb    w0, [x5, x0]
        ldrb    w3, [x3, #1]
        strb    w3, [x13], #1
        add     w1, w1, w0
        cmp     x8, x13
        b.ne    L5fa0
        str     w1, [sp, #272]
L5fcc:
        sub     x0, x6, x14
        ldr     w1, [sp, #312]
        cmp     x0, #0x3
        b.le    L65a4
        cmp     w1, #0x40
        b.hi    L6590
        ldr     x4, [sp, #320]
        neg     w3, w23
        ldr     x16, [sp, #128]
        and     w3, w3, #0x3f
        ldr     x0, [sp, #304]
        sub     x13, x6, #0x3
        mov     x8, x4
        mov     w2, #0x0
        b       L60ac
L6008:
        cmp     x14, x13
        sub     w17, w1, w0, lsl #3
        ldr     x0, [x19]
        cset    w2, cc
        mov     x8, x19
L601c:
        lsl     x1, x0, x17
        cbz     w2,L60e4
        lsr     x1, x1, x3
        add     x14, x14, #0x4
        lsl     x1, x1, #1
        add     x19, x5, x1
        ldrb    w1, [x5, x1]
        ldrb    w19, [x19, #1]
        add     w17, w1, w17
        sturb   w19, [x14, #-4]
        lsl     x1, x0, x17
        lsr     x1, x1, x3
        lsl     x1, x1, #1
        add     x22, x5, x1
        ldrb    w19, [x5, x1]
        ldrb    w1, [x22, #1]
        add     w19, w19, w17
        sturb   w1, [x14, #-3]
        lsl     x1, x0, x19
        lsr     x1, x1, x3
        lsl     x1, x1, #1
        add     x22, x5, x1
        ldrb    w17, [x5, x1]
        ldrb    w1, [x22, #1]
        add     w17, w17, w19
        sturb   w1, [x14, #-2]
        lsl     x1, x0, x17
        lsr     x1, x1, x3
        lsl     x1, x1, #1
        add     x19, x5, x1
        ldrb    w1, [x5, x1]
        ldrb    w19, [x19, #1]
        add     w1, w1, w17
        sturb   w19, [x14, #-1]
        cmp     w1, #0x40
        b.hi    L6588
L60ac:
        lsr     w19, w1, #3
        cmp     x8, x16
        b.cs    L63e0
        sub     x19, x8, x19
        cmp     x15, x8
        b.eq    L6380
        lsr     w0, w1, #3
        cmp     x15, x19
        b.ls    L6008
        sub     w0, w8, w15
        sub     x17, x8, x15
        sub     x8, x8, x0
        sub     w17, w1, w17, lsl #3
        ldr     x0, [x8]
L60e4:
        str     x0, [sp, #304]
        str     w17, [sp, #312]
        str     x8, [sp, #320]
L60f0:
        cmp     x6, x14
        b.ls    L6134
        ldr     x4, [sp, #304]
        neg     w2, w23
        ldr     w1, [sp, #312]
        and     w2, w2, #0x3f
L6108:
        lsl     x0, x4, x1
        lsr     x0, x0, x2
        lsl     x0, x0, #1
        add     x3, x5, x0
        ldrb    w0, [x5, x0]
        ldrb    w3, [x3, #1]
        strb    w3, [x14], #1
        add     w1, w1, w0
        cmp     x6, x14
        b.ne    L6108
        str     w1, [sp, #312]
L6134:
        sub     x1, x9, x12
        ldr     w0, [sp, #352]
        cmp     x1, #0x3
        b.le    L64c4
        cmp     w0, #0x40
        b.hi    L64b8
        ldr     x1, [sp, #360]
        neg     w4, w23
        ldr     x13, [sp, #112]
        and     w4, w4, #0x3f
        ldr     x14, [sp, #136]
        mov     x3, x1
        ldr     x2, [sp, #344]
        b       L6210
L616c:
        cmp     x13, x12
        sub     w0, w0, w2, lsl #3
        ldr     x2, [x6]
        cset    w18, hi
        mov     x3, x6
L6180:
        lsl     x6, x2, x0
        cbz     w18,L6248
        lsr     x6, x6, x4
        add     x12, x12, #0x4
        lsl     x6, x6, #1
        add     x16, x5, x6
        ldrb    w6, [x5, x6]
        ldrb    w16, [x16, #1]
        add     w6, w6, w0
        sturb   w16, [x12, #-4]
        lsl     x0, x2, x6
        lsr     x0, x0, x4
        lsl     x0, x0, #1
        add     x17, x5, x0
        ldrb    w16, [x5, x0]
        ldrb    w0, [x17, #1]
        add     w16, w16, w6
        sturb   w0, [x12, #-3]
        lsl     x0, x2, x16
        lsr     x0, x0, x4
        lsl     x0, x0, #1
        add     x17, x5, x0
        ldrb    w6, [x5, x0]
        ldrb    w0, [x17, #1]
        add     w6, w6, w16
        sturb   w0, [x12, #-2]
        lsl     x0, x2, x6
        lsr     x0, x0, x4
        lsl     x0, x0, #1
        add     x16, x5, x0
        ldrb    w0, [x5, x0]
        ldrb    w16, [x16, #1]
        add     w0, w0, w6
        sturb   w16, [x12, #-1]
        cmp     w0, #0x40
        b.hi    L64b0
L6210:
        lsr     w6, w0, #3
        cmp     x3, x14
        b.cs    L6414
        sub     x6, x3, x6
        cmp     x27, x3
        b.eq    L63a8
        lsr     w2, w0, #3
        cmp     x27, x6
        b.ls    L616c
        sub     w2, w3, w27
        sub     x1, x3, x27
        sub     x3, x3, x2
        sub     w0, w0, w1, lsl #3
        ldr     x2, [x3]
L6248:
        str     x2, [sp, #344]
        str     w0, [sp, #352]
L6250:
        cmp     x9, x12
        b.ls    L6294
        ldr     x6, [sp, #344]
        neg     w4, w23
        ldr     w1, [sp, #352]
        and     w4, w4, #0x3f
L6268:
        lsl     x0, x6, x1
        lsr     x0, x0, x4
        lsl     x0, x0, #1
        add     x2, x5, x0
        ldrb    w0, [x5, x0]
        ldrb    w2, [x2, #1]
        strb    w2, [x12], #1
        add     w1, w1, w0
        cmp     x9, x12
        b.ne    L6268
        str     w1, [sp, #352]
L6294:
        mov     w2, #0x0
        cmp     x11, x21
        b.eq    L6684
L62a0:
        mov     w1, #0x0
        cmp     x10, x7
        b.eq    L6664
L62ac:
        cmp     x15, x8
        b.ne    L5c04
        ldr     w0, [sp, #312]
        cmp     x27, x3
        b.ne    L5c04
        cmp     w0, #0x40
        ldr     w3, [sp, #352]
        cset    w0, eq
        and     w0, w0, w2
        cmp     w3, #0x40
        and     w0, w0, w1
        cset    w1, ne
        eor     w0, w0, #0x1
        orr     w0, w1, w0
        cbnz    w0,L5c04
        mov     x0, x20
L62ec:
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        b       L5444
L62f8:
        mov     x28, x11
        str     w26, [sp, #232]
        ldp     x9, x11, [sp, #144]
        str     w15, [sp, #144]
        str     w2, [sp, #272]
        mov     x0, x23
        str     w17, [sp, #312]
        str     w4, [sp, #352]
        ldp     x7, x8, [sp, #160]
        ldr     x6, [sp, #176]
        ldp     x20, x10, [sp, #192]
        ldr     x15, [sp, #208]
        ldr     x27, [sp, #216]
        ldr     w23, [sp, #188]
        cbz     w1,L633c
        str     x22, [sp, #224]
        str     x0, [sp, #240]
L633c:
        ldr     w0, [sp, #184]
        cbz     w0,L634c
        str     x21, [sp, #264]
        str     x24, [sp, #280]
L634c:
        ldr     w0, [sp, #124]
        cbz     w0,L635c
        str     x30, [sp, #304]
        str     x25, [sp, #320]
L635c:
        ldr     w0, [sp, #144]
        cbz     w0,L5ce4
L6364:
        str     x18, [sp, #344]
        str     x28, [sp, #360]
        b       L5ce4
L6370:
        mov     w0, #0x3
        b       L56c8
L6378:
        mov     w0, #0x3
        b       L56a8
L6380:
        cbz     w2,L6674
        str     x0, [sp, #304]
        str     w1, [sp, #312]
        str     x15, [sp, #320]
        b       L60f0
L6394:
        cbz     w3,L667c
        str     x1, [sp, #264]
        str     w0, [sp, #272]
        str     x10, [sp, #280]
        b       L5f88
L63a8:
        cbnz    w18,L6248
        mov     x3, x1
        b       L6250
L63b4:
        cbz     w3,L665c
        str     x1, [sp, #224]
        str     w0, [sp, #232]
        str     x11, [sp, #240]
        b       L5e20
L63c8:
        sub     x21, x21, x2
        cmp     x19, x22
        and     w0, w0, #0x7
        cset    w3, cc
        ldr     x1, [x21]
        b       L5d4c
L63e0:
        sub     x8, x8, x19
        cmp     x14, x13
        and     w17, w1, #0x7
        cset    w2, cc
        ldr     x0, [x8]
        b       L601c
L63f8:
        sub     x7, x7, x17
        and     w0, w0, #0x7
        ldr     x1, [x7]
        cmp     x13, x16
        b.cc    L5eb4
L640c:
        mov     w19, w0
        b       L5f7c
L6414:
        sub     x3, x3, x6
        cmp     x13, x12
        and     w0, w0, #0x7
        cset    w18, hi
        ldr     x2, [x3]
        b       L6180
L642c:
        ldp     x25, x26, [sp, #64]
        mov     x0, #0xffffffffffffffb8
        ldp     x27, x28, [sp, #80]
        b       L5444
L643c:
        str     x1, [sp, #264]
        str     w0, [sp, #272]
L6444:
        .inst   0xb0000000  // adrp x0, 0x7000
        add     x0, x0, #0xbf0
        mov     x7, x0
        str     x0, [sp, #280]
        b       L5f88
L6458:
        cmp     w0, #0x40
        b.hi    L6444
        ldr     x1, [sp, #104]
        ldr     x7, [sp, #280]
        cmp     x7, x1
        b.cs    L66c4
        cmp     x10, x7
        b.eq    L5f88
        lsr     w2, w0, #3
        lsr     w1, w0, #3
        sub     x3, x7, x2
        cmp     x10, x3
        b.ls    L6494
        sub     w1, w7, w10
        sub     w2, w7, w10
L6494:
        sub     x7, x7, x2
        sub     w1, w0, w1, lsl #3
        str     w1, [sp, #272]
        str     x7, [sp, #280]
        ldr     x0, [x7]
        str     x0, [sp, #264]
        b       L5f88
L64b0:
        str     x2, [sp, #344]
        str     w0, [sp, #352]
L64b8:
        .inst   0xb0000003  // adrp x3, 0x7000
        add     x3, x3, #0xbf0
        b       L6250
L64c4:
        cmp     w0, #0x40
        b.hi    L64b8
        ldr     x1, [sp, #136]
        ldr     x3, [sp, #360]
        cmp     x3, x1
        b.cs    L66a4
        cmp     x27, x3
        b.eq    L6250
        lsr     w2, w0, #3
        lsr     w1, w0, #3
        sub     x4, x3, x2
        cmp     x27, x4
        b.ls    L6500
        sub     w1, w3, w27
        sub     w2, w3, w27
L6500:
        sub     x3, x3, x2
        sub     w1, w0, w1, lsl #3
        ldr     x0, [x3]
        str     x0, [sp, #344]
        str     w1, [sp, #352]
        str     x3, [sp, #360]
        b       L6250
L651c:
        str     x1, [sp, #224]
        str     w0, [sp, #232]
L6524:
        .inst   0xb0000015  // adrp x21, 0x7000
        add     x21, x21, #0xbf0
        str     x21, [sp, #240]
        b       L5e20
L6534:
        cmp     w0, #0x40
        b.hi    L6524
        ldr     x21, [sp, #240]
        cmp     x21, x16
        b.cs    L6694
        cmp     x11, x21
        b.eq    L5e20
        lsr     w2, w0, #3
        lsr     w1, w0, #3
        sub     x3, x21, x2
        cmp     x11, x3
        b.ls    L656c
        sub     w1, w21, w11
        sub     w2, w21, w11
L656c:
        sub     x21, x21, x2
        sub     w1, w0, w1, lsl #3
        str     w1, [sp, #232]
        str     x21, [sp, #240]
        ldr     x0, [x21]
        str     x0, [sp, #224]
        b       L5e20
L6588:
        str     x0, [sp, #304]
        str     w1, [sp, #312]
L6590:
        .inst   0xb0000000  // adrp x0, 0x7000
        add     x0, x0, #0xbf0
        mov     x8, x0
        str     x0, [sp, #320]
        b       L60f0
L65a4:
        cmp     w1, #0x40
        b.hi    L6590
        ldr     x0, [sp, #128]
        ldr     x8, [sp, #320]
        cmp     x8, x0
        b.cs    L66b4
        cmp     x15, x8
        b.eq    L60f0
        lsr     w2, w1, #3
        lsr     w0, w1, #3
        sub     x3, x8, x2
        cmp     x15, x3
        b.ls    L65e0
        sub     w0, w8, w15
        sub     w2, w8, w15
L65e0:
        sub     x8, x8, x2
        sub     w0, w1, w0, lsl #3
        str     w0, [sp, #312]
        str     x8, [sp, #320]
        ldr     x0, [x8]
        str     x0, [sp, #304]
        b       L60f0
L65fc:
        str     w26, [sp, #232]
        mov     x28, x11
        str     w2, [sp, #272]
        mov     x3, x23
        str     w17, [sp, #312]
        str     w0, [sp, #352]
        ldp     x9, x11, [sp, #144]
        ldp     x7, x8, [sp, #160]
        ldr     x6, [sp, #176]
        ldp     x20, x10, [sp, #192]
        ldp     x15, x27, [sp, #208]
        ldr     w23, [sp, #188]
        cbz     w1,L6638
        str     x22, [sp, #224]
        str     x3, [sp, #240]
L6638:
        ldr     w0, [sp, #184]
        cbz     w0,L6648
        str     x21, [sp, #264]
        str     x24, [sp, #280]
L6648:
        ldr     w0, [sp, #124]
        cbz     w0,L6364
        str     x30, [sp, #304]
        str     x25, [sp, #320]
        b       L6364
L665c:
        mov     x21, x17
        b       L5e20
L6664:
        ldr     w0, [sp, #272]
        cmp     w0, #0x40
        cset    w1, eq
        b       L62ac
L6674:
        mov     x8, x4
        b       L60f0
L667c:
        mov     x7, x4
        b       L5f88
L6684:
        ldr     w0, [sp, #232]
        cmp     w0, #0x40
        cset    w2, eq
        b       L62a0
L6694:
        add     x0, sp, #0xe0
        bl      L1c20
        ldr     x21, [sp, #240]
        b       L5e20
L66a4:
        add     x0, sp, #0x158
        bl      L1c20
        ldr     x3, [sp, #360]
        b       L6250
L66b4:
        add     x0, sp, #0x130
        bl      L1c20
        ldr     x8, [sp, #320]
        b       L60f0
L66c4:
        add     x0, sp, #0x108
        bl      L1c20
        ldr     x7, [sp, #280]
        b       L5f88

// HUF_readDTableX1_wksp (0x4b4 bytes)
L66d4:
        sub     sp, sp, #0x70
        stp     x29, x30, [sp, #16]
        add     x29, sp, #0x10
        stp     x21, x22, [sp, #48]
        stp     wzr, wzr, [sp, #104]
        cmp     x4, #0x5d3
        b.ls    L6b78
        str     w5, [sp, #8]
        add     x22, x3, #0x4d4
        stp     x19, x20, [sp, #32]
        mov     x20, x0
        mov     x0, #0x36c
        str     x0, [sp]
        mov     x19, x3
        mov     x6, x2
        add     x7, x3, #0x68
        mov     x5, x1
        add     x4, sp, #0x68
        add     x3, sp, #0x6c
        mov     x2, x19
        mov     x0, x22
        mov     x1, #0x100
        bl      L0ca0
        mov     x21, x0
        cmn     x0, #0x78
        b.ls    L6754
        ldp     x19, x20, [sp, #32]
L6740:
        mov     x0, x21
        ldp     x29, x30, [sp, #16]
        ldp     x21, x22, [sp, #48]
        add     sp, sp, #0x70
        ret
L6754:
        stp     x23, x24, [sp, #64]
        stp     x25, x26, [sp, #80]
        mov     w26, #0xb
        ldr     w25, [x20]
        ldp     w7, w23, [sp, #104]
        and     w24, w25, #0xff
        add     w24, w24, #0x1
        cmp     w24, w26
        csel    w26, w24, w26, ls
        cmp     w7, w26
        b.hi    L67fc
        b.cs    L67f8
        sub     w3, w26, w7
        mov     x1, x19
        add     x4, x19, w23, uxtw
        cbz     w23,L67bc
        nop
L6798:
        ldrb    w0, [x1, #1236]
        add     x1, x1, #0x1
        add     w2, w0, w3
        cmp     w0, #0x0
        and     w2, w2, #0xff
        csel    w0, w2, w0, ne
        strb    w0, [x1, #1235]
        cmp     x1, x4
        b.ne    L6798
L67bc:
        ubfiz   x0, x26, #2, #9
        add     x0, x19, x0
        cmp     w26, w3
        b.ls    L67e0
        nop
L67d0:
        ldr     w1, [x19, w7, uxtw #2]
        subs    w7, w7, #0x1
        str     w1, [x0], #-4
        b.ne    L67d0
L67e0:
        sub     w0, w3, #0x1
        ubfiz   x2, x3, #2, #32
        mov     w1, #0x0
        sub     x0, x2, x0, lsl #2
        add     x0, x19, x0
        bl      L0660
L67f8:
        mov     w7, w26
L67fc:
        str     w7, [sp, #104]
        cmp     w24, w7
        b.cc    L6b6c
        and     w25, w25, #0xffff00ff
        and     w9, w7, #0xff
        sub     w8, w23, #0x3
        add     x4, x19, #0x34
        bfi     w25, w9, #16, #8
        mov     x0, #0x0
        mov     w1, #0x0
        str     w25, [x20]
L6828:
        ldr     w2, [x19, x0, lsl #2]
        str     w1, [x4, x0, lsl #2]
        add     x0, x0, #0x1
        add     w1, w1, w2
        cmp     w7, w0
        b.ge    L6828
        cmp     w8, #0x0
        b.le    L6b80
        mov     x6, x22
        mov     w5, #0x0
L6850:
        mov     x1, #0x0
L6854:
        ldrb    w4, [x6, x1]
        add     w0, w5, w1
        add     x1, x1, #0x1
        add     x4, x19, x4, lsl #2
        ldr     w2, [x4, #52]
        add     w3, w2, #0x1
        str     w3, [x4, #52]
        add     x2, x19, w2, uxtw
        strb    w0, [x2, #980]
        cmp     x1, #0x4
        b.ne    L6854
        add     w5, w5, #0x4
        add     x6, x6, #0x4
        cmp     w8, w5
        b.gt    L6850
        sub     w0, w23, #0x4
        and     w0, w0, #0xfffffffc
        add     w0, w0, #0x4
L689c:
        ldr     w8, [x19]
        cmp     w23, w0
        b.le    L68dc
        sxtw    x3, w0
        add     x3, x3, #0x4d4
        add     x3, x19, x3
L68b4:
        ldrb    w2, [x3], #1
        add     x2, x19, x2, lsl #2
        ldr     w1, [x2, #52]
        add     w4, w1, #0x1
        str     w4, [x2, #52]
        add     x1, x19, w1, uxtw
        strb    w0, [x1, #980]
        add     w0, w0, #0x1
        cmp     w23, w0
        b.ne    L68b4
L68dc:
        add     w9, w9, #0x1
        mov     x0, #0x1
        mov     x15, #0x4
        add     w7, w7, #0x1
        mov     w13, w0
        add     x14, x19, x0
        add     x11, x20, x15
        add     x10, x20, #0x24
        add     x16, x20, #0x6
        and     w12, w9, #0xff
        mov     w9, #0x0
L6908:
        lsl     w5, w13, w0
        sub     w3, w12, w0
        asr     w5, w5, #1
        ldr     w6, [x19, x0, lsl #2]
        and     w3, w3, #0xff
        cmp     w5, #0x4
        b.eq    L6b0c
        b.gt    L69b8
        cmp     w5, #0x1
        b.eq    L6ab0
        cmp     w5, #0x2
        b.ne    L6a24
        cmp     w6, #0x0
        b.le    L6984
        sxtw    x2, w8
        sub     w17, w6, #0x1
        add     x17, x17, x2
        add     x1, x20, w9, sxtw #1
        add     x17, x17, x14
        add     x2, x19, x2
        add     x1, x1, #0x4
        nop
L6960:
        ldrb    w4, [x2, #980]
        add     x2, x2, #0x1
        strb    w3, [x1]
        add     x1, x1, #0x4
        sturb   w4, [x1, #-3]
        sturb   w3, [x1, #-2]
        sturb   w4, [x1, #-1]
        cmp     x17, x2
        b.ne    L6960
L6984:
        add     x0, x0, #0x1
        madd    w9, w6, w5, w9
        add     w8, w8, w6
        cmp     w7, w0
        b.hi    L6908
L6998:
        ldp     x29, x30, [sp, #16]
        mov     x0, x21
        ldp     x19, x20, [sp, #32]
        ldp     x21, x22, [sp, #48]
        ldp     x23, x24, [sp, #64]
        ldp     x25, x26, [sp, #80]
        add     sp, sp, #0x70
        ret
L69b8:
        cmp     w5, #0x8
        b.ne    L6a24
        cmp     w6, #0x0
        b.le    L6984
        sxtw    x1, w8
        add     x22, x15, w9, sxtw #1
        add     x1, x1, #0x3d4
        add     x22, x20, x22
        add     x4, x19, x1
        mov     x2, #0x0
L69e0:
        ldrb    w1, [x4, x2]
        lsl     x17, x2, #4
        add     x2, x2, #0x1
        add     w1, w3, w1, lsl #8
        sbfiz   x18, x1, #16, #32
        add     x1, x18, w1, sxtw
        add     x1, x1, x1, lsl #32
        dup     v0.2d, x1
        str     q0, [x22, x17]
        cmp     w6, w2
        b.gt    L69e0
        add     x0, x0, #0x1
        madd    w9, w6, w5, w9
        add     w8, w8, w6
        cmp     w7, w0
        b.hi    L6908
        b       L6998
L6a24:
        cmp     w6, #0x0
        b.le    L6984
        sxtw    x17, w8
        sub     w30, w6, #0x1
        add     x30, x30, x17
        sub     w22, w5, #0x1
        add     x30, x30, x14
        add     x17, x19, x17
        and     x22, x22, #0xfffffff0
        sxtw    x23, w5
        sxtw    x18, w9
L6a50:
        ldrb    w2, [x17, #980]
        add     x4, x22, x18
        add     x1, x11, x18, lsl #1
        add     x4, x10, x4, lsl #1
        add     w2, w3, w2, lsl #8
        sbfiz   x24, x2, #16, #32
        add     x2, x24, w2, sxtw
        add     x2, x2, x2, lsl #32
        dup     v0.2d, x2
        nop
L6a78:
        stp     q0, q0, [x1]
        add     x1, x1, #0x20
        cmp     x1, x4
        b.ne    L6a78
        add     x17, x17, #0x1
        add     x18, x18, x23
        cmp     x17, x30
        b.ne    L6a50
        add     x0, x0, #0x1
        madd    w9, w6, w5, w9
        add     w8, w8, w6
        cmp     w7, w0
        b.hi    L6908
        b       L6998
L6ab0:
        cmp     w6, #0x0
        b.le    L6984
        sxtw    x2, w9
        sub     w17, w6, #0x1
        add     x1, x2, #0x2
        add     x17, x17, x2
        add     x2, x19, w8, sxtw
        add     x1, x20, x1, lsl #1
        add     x17, x16, x17, lsl #1
        nop
L6ad8:
        ldrb    w4, [x2, #980]
        add     x1, x1, #0x2
        sturb   w3, [x1, #-2]
        add     x2, x2, #0x1
        sturb   w4, [x1, #-1]
        cmp     x17, x1
        b.ne    L6ad8
        add     x0, x0, #0x1
        madd    w9, w6, w5, w9
        add     w8, w8, w6
        cmp     w7, w0
        b.hi    L6908
        b       L6998
L6b0c:
        cmp     w6, #0x0
        b.le    L6984
        sxtw    x1, w8
        add     x18, x15, w9, sxtw #1
        add     x1, x1, #0x3d4
        add     x18, x20, x18
        add     x4, x19, x1
        mov     x2, #0x0
        nop
L6b30:
        ldrb    w1, [x4, x2]
        add     w1, w3, w1, lsl #8
        sbfiz   x17, x1, #16, #32
        add     x1, x17, w1, sxtw
        add     x1, x1, x1, lsl #32
        str     x1, [x18, x2, lsl #3]
        add     x2, x2, #0x1
        cmp     w6, w2
        b.gt    L6b30
        add     x0, x0, #0x1
        madd    w9, w6, w5, w9
        add     w8, w8, w6
        cmp     w7, w0
        b.hi    L6908
        b       L6998
L6b6c:
        ldp     x19, x20, [sp, #32]
        ldp     x23, x24, [sp, #64]
        ldp     x25, x26, [sp, #80]
L6b78:
        mov     x21, #0xffffffffffffffd4
        b       L6740
L6b80:
        mov     w0, #0x0
        b       L689c
        nop
        nop

// HUF_readDTableX2_wksp (0x534 bytes)
L6b90:
        sub     sp, sp, #0xd0
        stp     x29, x30, [sp, #16]
        add     x29, sp, #0x10
        stp     x25, x26, [sp, #80]
        stp     x27, x28, [sp, #96]
        mov     x28, #0xffffffffffffffff
        ldr     w25, [x0]
        cmp     x4, #0x84b
        b.ls    L7000
        movi    v0.4s, #0x0
        mov     x6, x2
        add     x2, x3, #0x270
        stp     x19, x20, [sp, #32]
        and     w19, w25, #0xff
        stp     x23, x24, [sp, #64]
        mov     x23, x0
        add     x0, x3, #0x2a4
        str     wzr, [x2, #48]
        mov     x20, x3
        stp     q0, q0, [x2]
        str     q0, [x2, #32]
        str     q0, [x0, #32]
        stp     q0, q0, [x0]
        stur    q0, [x0, #44]
        cmp     w19, #0xc
        b.hi    L701c
        mov     x0, #0x36c
        str     x0, [sp]
        str     w5, [sp, #8]
        add     x7, x3, #0x4e0
        stp     x21, x22, [sp, #48]
        add     x21, x3, #0x3e0
        mov     x5, x1
        add     x4, sp, #0xc8
        add     x3, sp, #0xcc
        mov     x0, x21
        mov     x1, #0x100
        bl      L0ca0
        mov     x28, x0
        cmn     x0, #0x78
        b.hi    L7064
        ldr     w12, [sp, #200]
        cmp     w12, w19
        b.hi    L7018
        cmp     w19, #0xc
        and     w15, w25, #0xff
        ccmp    w12, #0xc, #0x4, eq
        add     w6, w19, #0x1
        b.eq    L6c60
        mov     w15, #0xb
        mov     w19, w15
        mov     w6, #0xc
L6c60:
        mov     w0, w12
        add     w5, w12, #0x1
        add     x0, x0, #0x9c
        ldr     w0, [x20, x0, lsl #2]
        cbnz    w0,L7088
        mov     w14, w12
L6c78:
        sub     w0, w14, #0x1
        mov     w4, w14
        mov     x14, x0
        add     x0, x0, #0x9c
        ldr     w0, [x20, x0, lsl #2]
        cbz     w0,L6c78
        sub     w6, w6, w5
        sub     w27, w5, w14
        add     w6, w6, w14
L6c9c:
        add     x3, x20, #0x2a8
        cmp     w4, #0x1
        b.ls    L70ac
        sub     w8, w4, #0x2
        add     x2, x20, #0x278
        add     x0, x20, #0x274
        mov     w1, #0x0
        add     x8, x2, w8, uxtw #2
        nop
L6cc0:
        ldr     w2, [x0]
        mov     w7, w1
        add     x0, x0, #0x4
        str     w7, [x0, #52]
        add     w1, w1, w2
        cmp     x8, x0
        b.ne    L6cc0
        ldr     w8, [sp, #204]
        str     w1, [x20, #680]
        str     w1, [x3, w4, uxtw #2]
        cbz     w8,L709c
L6cec:
        mov     w8, w8
        mov     x0, #0x0
        nop
L6cf8:
        ldrb    w2, [x21, x0]
        ldr     w1, [x3, x2, lsl #2]
        add     w7, w1, #0x1
        str     w7, [x3, x2, lsl #2]
        add     x1, x20, w1, uxtw
        strb    w0, [x1, #736]
        add     x0, x0, #0x1
        cmp     x8, x0
        b.ne    L6cf8
        sub     w0, w19, w12
        str     wzr, [x20, #680]
        sub     w8, w0, #0x1
        cmp     w4, #0x1
        b.ls    L6d5c
L6d30:
        add     w8, w8, w4
        add     x3, x20, #0x4
        mov     w2, #0x0
        nop
L6d40:
        ldr     w1, [x3, #624]
        str     w2, [x3], #4
        lsl     w1, w1, w0
        add     w0, w0, #0x1
        add     w2, w2, w1
        cmp     w8, w0
        b.ne    L6d40
L6d5c:
        cmp     w27, w6
        b.cs    L6da8
        mov     w3, #0x34
        mov     w2, w27
        umaddl  x3, w27, w3, x20
L6d70:
        cmp     w4, #0x1
        b.ls    L7040
L6d78:
        mov     x0, #0x1
        nop
L6d80:
        ldr     w1, [x20, x0, lsl #2]
        lsr     w1, w1, w2
        str     w1, [x3, x0, lsl #2]
        add     x0, x0, #0x1
        cmp     w4, w0
        b.hi    L6d80
        add     w2, w2, #0x1
        add     x3, x3, #0x34
        cmp     w2, w6
        b.ne    L6d78
L6da8:
        add     w16, w14, #0x1
        add     w5, w12, w5
        add     x13, x20, #0x2e0
        cmp     w16, #0x1
        b.le    L6fe4
        sub     w0, w12, w14
        lsl     w22, w12, #1
        add     x10, x20, #0x4
        sub     w11, w19, w12
        lsl     w0, w0, #1
        sub     w14, w22, w14
        add     x24, x23, #0x4
        sub     w21, w5, w19
        add     w22, w22, #0x1
        mov     x18, x10
        str     w16, [sp, #128]
        str     w27, [sp, #136]
        stp     w15, w25, [sp, #168]
        mov     w15, w0
        stp     x28, x23, [sp, #176]
        mov     w23, w12
        mov     w12, w11
        b       L6e44
L6e04:
        add     x2, x13, w2, sxtw
        add     x1, x13, w1, sxtw
        add     x0, x24, w0, uxtw #2
        mov     w4, w19
        mov     w3, w23
        mov     w6, #0x1
        mov     w5, #0x0
        bl      L1c50
L6e24:
        sub     w14, w14, #0x1
        add     x18, x18, #0x4
        add     w12, w12, #0x1
        sub     w23, w23, #0x1
        sub     w21, w21, #0x1
        sub     w22, w22, #0x1
        cmp     w15, w14
        b.eq    L6fdc
L6e44:
        ldr     w3, [sp, #136]
        ldr     w0, [x18]
        ldr     w1, [x18, #676]
        ldr     w2, [x18, #680]
        cmp     w12, w3
        b.cc    L6e04
        and     w3, w12, #0x1f
        cmp     w21, #0x0
        mov     w10, w0
        mov     w0, #0x1
        csinc   w11, w21, wzr, gt
        lsl     w5, w0, w3
        cmp     w1, w2
        b.eq    L6e24
        sbfiz   x28, x11, #2, #32
        mov     w26, #0x34
        sxtw    x6, w1
        sub     w2, w2, #0x1
        sub     w25, w2, w1
        add     x27, x20, x6
        umaddl  x26, w23, w26, x28
        add     x28, x28, #0x2a8
        add     x1, x20, #0x1
        add     x25, x25, x6
        add     x26, x20, x26
        add     x28, x20, x28
        mov     w0, #0x1000000
        stp     w15, w23, [sp, #140]
        mov     w15, w11
        stp     x18, x20, [sp, #152]
        mov     w18, w10
        mov     x20, x27
        mov     w10, w3
        add     x25, x25, x1
        add     w0, w0, w23, lsl #16
        str     w5, [sp, #116]
        str     x25, [sp, #120]
        str     w0, [sp, #132]
        str     w12, [sp, #148]
L6ee0:
        sbfiz   x6, x18, #2, #32
        ldrb    w12, [x20, #736]
        add     x23, x24, x6
        cmp     w21, #0x1
        b.le    L6f48
        ldr     w0, [sp, #132]
        ldr     w1, [x26]
        add     w0, w12, w0
        add     x0, x0, x0, lsl #32
        dup     v0.2d, x0
        cmp     w10, #0x1
        b.eq    L705c
        cmp     w10, #0x2
        b.eq    L7054
        cmp     w1, #0x0
        b.le    L6f48
        sub     w1, w1, #0x1
        mov     w2, #0x20
        mov     x0, x23
        lsr     w1, w1, #3
        add     w1, w1, #0x1
        umaddl  x1, w1, w2, x23
L6f38:
        stp     q0, q0, [x0]
        add     x0, x0, #0x20
        cmp     x0, x1
        b.ne    L6f38
L6f48:
        ldr     w0, [sp, #128]
        sub     w27, w22, w15
        mov     x25, x28
        mov     x11, x26
        cmp     w0, w15
        b.le    L6f98
L6f60:
        ldpsw   x1, x2, [x25, #-4]
        mov     w3, w27
        ldr     w0, [x11], #4
        mov     w5, w12
        mov     w4, w19
        add     x2, x13, x2
        add     x1, x13, x1
        mov     w6, #0x2
        add     x0, x23, x0, lsl #2
        sub     w27, w27, #0x1
        bl      L1c50
        add     x25, x25, #0x4
        cmp     w14, w27
        b.ne    L6f60
L6f98:
        ldr     w0, [sp, #116]
        add     x20, x20, #0x1
        add     w18, w18, w0
        ldr     x0, [sp, #120]
        cmp     x0, x20
        b.ne    L6ee0
        ldp     x18, x20, [sp, #152]
        sub     w14, w14, #0x1
        ldp     w15, w23, [sp, #140]
        sub     w21, w21, #0x1
        ldr     w12, [sp, #148]
        sub     w22, w22, #0x1
        sub     w23, w23, #0x1
        add     x18, x18, #0x4
        add     w12, w12, #0x1
        cmp     w15, w14
        b.ne    L6e44
L6fdc:
        ldp     x28, x23, [sp, #176]
        ldp     w15, w25, [sp, #168]
L6fe4:
        bfi     w25, w15, #16, #8
        mov     w0, #0x1
        bfi     w25, w0, #8, #8
        str     w25, [x23]
        ldp     x19, x20, [sp, #32]
        ldp     x21, x22, [sp, #48]
        ldp     x23, x24, [sp, #64]
L7000:
        mov     x0, x28
        ldp     x29, x30, [sp, #16]
        ldp     x25, x26, [sp, #80]
        ldp     x27, x28, [sp, #96]
        add     sp, sp, #0xd0
        ret
L7018:
        ldp     x21, x22, [sp, #48]
L701c:
        mov     x28, #0xffffffffffffffd4
        ldp     x29, x30, [sp, #16]
        mov     x0, x28
        ldp     x19, x20, [sp, #32]
        ldp     x23, x24, [sp, #64]
        ldp     x25, x26, [sp, #80]
        ldp     x27, x28, [sp, #96]
        add     sp, sp, #0xd0
        ret
L7040:
        add     w2, w2, #0x1
        add     x3, x3, #0x34
        cmp     w2, w6
        b.ne    L6d70
        b       L6da8
L7054:
        str     q0, [x24, x6]
        b       L6f48
L705c:
        str     x0, [x24, x6]
        b       L6f48
L7064:
        ldp     x29, x30, [sp, #16]
        mov     x0, x28
        ldp     x19, x20, [sp, #32]
        ldp     x21, x22, [sp, #48]
        ldp     x23, x24, [sp, #64]
        ldp     x25, x26, [sp, #80]
        ldp     x27, x28, [sp, #96]
        add     sp, sp, #0xd0
        ret
L7088:
        mov     w6, w19
        mov     w4, w5
        mov     w14, w12
        mov     w27, #0x1
        b       L6c9c
L709c:
        sub     w0, w19, w12
        str     wzr, [x20, #680]
        sub     w8, w0, #0x1
        b       L6d30
L70ac:
        ldr     w8, [sp, #204]
        str     wzr, [x20, #680]
        str     wzr, [x3, w4, uxtw #2]
        cbnz    w8,L6cec
        str     wzr, [x20, #680]
        b       L6d5c

// HUF_decompress1X2_DCtx_wksp (0x90 bytes)
L70c4:
        stp     x29, x30, [sp, #-64]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x20, x3
        mov     x19, x4
        mov     x3, x5
        mov     x4, x6
        mov     w5, w7
        stp     x21, x22, [sp, #32]
        mov     x21, x1
        mov     x22, x2
        mov     x1, x20
        mov     x2, x19
        str     x23, [sp, #48]
        mov     x23, x0
        bl      L6b90
        cmn     x0, #0x78
        b.hi    L7140
        cmp     x19, x0
        b.ls    L713c
        sub     x3, x19, x0
        add     x2, x20, x0
        ldp     x19, x20, [sp, #16]
        mov     x4, x23
        ldr     x23, [sp, #48]
        mov     x1, x22
        mov     x0, x21
        ldp     x21, x22, [sp, #32]
        ldp     x29, x30, [sp], #64
        b       L2b30
L713c:
        mov     x0, #0xffffffffffffffb8
L7140:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldr     x23, [sp, #48]
        ldp     x29, x30, [sp], #64
        ret

// HUF_selectDecoder (0x78 bytes)
L7154:
        cmp     x1, x0
        b.cs    L71a0
        lsl     x1, x1, #4
        .inst   0x90000002  // adrp x2, 0x7000
        add     x2, x2, #0xbf0
        add     x2, x2, #0x10
        udiv    x1, x1, x0
        lsr     x0, x0, #8
        ubfiz   x1, x1, #4, #32
        add     x5, x2, x1
        ldr     w3, [x2, x1]
        ldp     w2, w4, [x5, #4]
        ldr     w1, [x5, #12]
        madd    w1, w1, w0, w4
        madd    w0, w2, w0, w3
        add     w1, w1, w1, lsr #5
        cmp     w0, w1
        cset    w0, hi
        ret
L71a0:
        lsr     x0, x0, #8
        mov     w4, #0x69f
        mov     w1, #0xca
        mov     w2, #0xb9
        mov     w3, #0x584
        madd    w1, w1, w0, w4
        madd    w0, w2, w0, w3
        add     w1, w1, w1, lsr #5
        cmp     w0, w1
        cset    w0, hi
        ret
        nop

// HUF_decompress1X_DCtx_wksp (0x158 bytes)
L71d0:
        cbz     x2,L72b8
        stp     x29, x30, [sp, #-64]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x19, x4
        mov     x20, x2
        cmp     x2, x4
        b.cc    L72f0
        stp     x21, x22, [sp, #32]
        mov     x21, x3
        str     x23, [sp, #48]
        mov     x23, x1
        b.eq    L7318
        cmp     x4, #0x1
        b.eq    L72d4
        mov     x8, x5
        mov     x1, x4
        mov     x22, x0
        mov     x0, x2
        bl      L7154
        mov     w5, w7
        mov     x4, x6
        mov     x3, x8
        mov     x2, x19
        mov     x1, x21
        cbz     w0,L7278
        mov     x0, x22
        bl      L6b90
        cmn     x0, #0x78
        b.hi    L72c0
        cmp     x19, x0
        b.ls    L7300
        sub     x3, x19, x0
        add     x2, x21, x0
        mov     x4, x22
        mov     x1, x20
        ldp     x19, x20, [sp, #16]
        mov     x0, x23
        ldp     x21, x22, [sp, #32]
        ldr     x23, [sp, #48]
        ldp     x29, x30, [sp], #64
        b       L2b30
L7278:
        mov     x0, x22
        bl      L66d4
        cmn     x0, #0x78
        b.hi    L72c0
        cmp     x19, x0
        b.ls    L7300
        sub     x3, x19, x0
        add     x2, x21, x0
        mov     x4, x22
        mov     x1, x20
        ldp     x19, x20, [sp, #16]
        mov     x0, x23
        ldp     x21, x22, [sp, #32]
        ldr     x23, [sp, #48]
        ldp     x29, x30, [sp], #64
        b       L2850
L72b8:
        mov     x0, #0xffffffffffffffba
        ret
L72c0:
        ldp     x21, x22, [sp, #32]
        ldr     x23, [sp, #48]
L72c8:
        ldp     x19, x20, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
L72d4:
        ldrb    w1, [x3]
        mov     x0, x23
        bl      L0660
L72e0:
        ldp     x21, x22, [sp, #32]
        mov     x0, x20
        ldr     x23, [sp, #48]
        b       L72c8
L72f0:
        ldp     x19, x20, [sp, #16]
        mov     x0, #0xffffffffffffffec
        ldp     x29, x30, [sp], #64
        ret
L7300:
        ldp     x19, x20, [sp, #16]
        mov     x0, #0xffffffffffffffb8
        ldp     x21, x22, [sp, #32]
        ldr     x23, [sp, #48]
        ldp     x29, x30, [sp], #64
        ret
L7318:
        mov     x1, x3
        mov     x0, x23
        bl      L0640
        b       L72e0
        nop
        nop

// HUF_decompress1X_usingDTable (0x10 bytes)
L7330:
        ldrb    w5, [x4, #1]
        cbz     w5,L733c
        b       L2b30
L733c:
        b       L2850

// HUF_decompress1X1_DCtx_wksp (0x90 bytes)
L7340:
        stp     x29, x30, [sp, #-64]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x20, x3
        mov     x19, x4
        mov     x3, x5
        mov     x4, x6
        mov     w5, w7
        stp     x21, x22, [sp, #32]
        mov     x21, x1
        mov     x22, x2
        mov     x1, x20
        mov     x2, x19
        str     x23, [sp, #48]
        mov     x23, x0
        bl      L66d4
        cmn     x0, #0x78
        b.hi    L73bc
        cmp     x19, x0
        b.ls    L73b8
        sub     x3, x19, x0
        add     x2, x20, x0
        ldp     x19, x20, [sp, #16]
        mov     x4, x23
        ldr     x23, [sp, #48]
        mov     x1, x22
        mov     x0, x21
        ldp     x21, x22, [sp, #32]
        ldp     x29, x30, [sp], #64
        b       L2850
L73b8:
        mov     x0, #0xffffffffffffffb8
L73bc:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldr     x23, [sp, #48]
        ldp     x29, x30, [sp], #64
        ret

// HUF_decompress4X_usingDTable (0x10 bytes)
L73d0:
        ldrb    w6, [x4, #1]
        cbz     w6,L73dc
        b       L30c0
L73dc:
        b       L5300

// HUF_decompress4X_hufOnly_wksp (0x128 bytes)
L73e0:
        cbz     x2,L74c4
        stp     x29, x30, [sp, #-64]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        mov     x19, x4
        cbz     x4,L74f8
        mov     x8, x5
        mov     x20, x2
        stp     x21, x22, [sp, #32]
        mov     x21, x3
        mov     x22, x0
        mov     x0, x2
        stp     x23, x24, [sp, #48]
        mov     x23, x1
        mov     x1, x4
        bl      L7154
        mov     w24, w7
        mov     x4, x6
        mov     x3, x8
        mov     w5, w7
        mov     x2, x19
        mov     x1, x21
        cbz     w0,L7480
        mov     x0, x22
        bl      L6b90
        cmn     x0, #0x78
        b.hi    L74cc
        cmp     x19, x0
        b.ls    L74e0
        sub     x3, x19, x0
        add     x2, x21, x0
        mov     w5, w24
        mov     x4, x22
        ldp     x21, x22, [sp, #32]
        mov     x1, x20
        ldp     x19, x20, [sp, #16]
        mov     x0, x23
        ldp     x23, x24, [sp, #48]
        ldp     x29, x30, [sp], #64
        b       L30c0
L7480:
        mov     x0, x22
        bl      L66d4
        cmn     x0, #0x78
        b.hi    L74cc
        cmp     x19, x0
        b.ls    L74e0
        sub     x3, x19, x0
        add     x2, x21, x0
        mov     w5, w24
        mov     x4, x22
        ldp     x21, x22, [sp, #32]
        mov     x1, x20
        ldp     x19, x20, [sp, #16]
        mov     x0, x23
        ldp     x23, x24, [sp, #48]
        ldp     x29, x30, [sp], #64
        b       L5300
L74c4:
        mov     x0, #0xffffffffffffffba
        ret
L74cc:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x29, x30, [sp], #64
        ret
L74e0:
        ldp     x19, x20, [sp, #16]
        mov     x0, #0xffffffffffffffb8
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x29, x30, [sp], #64
        ret
L74f8:
        ldp     x19, x20, [sp, #16]
        mov     x0, #0xffffffffffffffec
        ldp     x29, x30, [sp], #64
        ret
        nop
        nop

// zhuf_decompress1x1 (0x4 bytes)
L7510:
        b       L7340

// zhuf_readncount (0x4 bytes)
L7514:
        b       L0c64
        nop
        nop

// zhuf_readstats (0x4 bytes)
L7520:
        b       L0c70

// zhuf_iserror (0xc bytes)
L7524:
        cmn     x0, #0x78
        cset    w0, hi
        ret

// zhuf_errorname (0xc bytes)
L7530:
        cmn     x0, #0x78
        csneg   w0, wzr, w0, ls
        b       L0cb0

// Padding (0x753c to 0x7550)

// _fini (0x0 bytes)
        .word   0xd503201f
        .quad   0x910003fda9bf7bfd
        .quad   0xd65f03c0a8c17bfd

// The read-only data (0x7550 to 0x7d00)

        .quad   0x726f727265206f4e
        .quad   0x6574636574656420
        .quad   0x0000000000000064
        .quad   0x672820726f727245
        .quad   0x0029636972656e65
        .quad   0x206e776f6e6b6e55
        .quad   0x656420656d617266
        .quad   0x726f747069726373
        .quad   0x0000000000000000
        .quad   0x206e6f6973726556
        .quad   0x7070757320746f6e
        .quad   0x000000646574726f
        .quad   0x726f707075736e55
        .quad   0x6d61726620646574
        .quad   0x656d617261702065
        .quad   0x0000000000726574
        .quad   0x657220656d617246
        .quad   0x7420736572697571
        .quad   0x206863756d206f6f
        .quad   0x662079726f6d656d
        .quad   0x646f63656420726f
        .quad   0x0000000000676e69
        .quad   0x726f632061746144
        .quad   0x206e6f6974707572
        .quad   0x6465746365746564
        .quad   0x0000000000000000
        .quad   0x6465726f74736552
        .quad   0x6f64206174616420
        .quad   0x616d2074276e7365
        .quad   0x6365686320686374
        .quad   0x000000006d75736b
        .quad   0x6f20726564616548
        .quad   0x61726574694c2066
        .quad   0x636f6c622027736c
        .quad   0x276e73656f64206b
        .quad   0x6365707365722074
        .quad   0x74616d726f662074
        .quad   0x6966696365707320
        .quad   0x00006e6f69746163
        .quad   0x726f707075736e55
        .quad   0x6172617020646574
        .quad   0x000000726574656d
        .quad   0x726f707075736e55
        .quad   0x626d6f6320646574
        .quad   0x206e6f6974616e69
        .quad   0x6d6172617020666f
        .quad   0x0000007372657465
        .quad   0x6574656d61726150
        .quad   0x74756f2073692072
        .quad   0x6e756f6220666f20
        .quad   0x0000000000000064
        .quad   0x20747865746e6f43
        .quad   0x6220646c756f6873
        .quad   0x662074696e692065
        .quad   0x0000000074737269
        .quad   0x697461636f6c6c41
        .quad   0x726f727265206e6f
        .quad   0x6520746f6e203a20
        .quad   0x656d206867756f6e
        .quad   0x0000000079726f6d
        .quad   0x636170536b726f77
        .quad   0x7265666675622065
        .quad   0x20746f6e20736920
        .quad   0x6e6520656772616c
        .quad   0x000000006867756f
        .quad   0x6f6974617265704f
        .quad   0x756120746f6e206e
        .quad   0x64657a69726f6874
        .quad   0x7272756320746120
        .quad   0x636f727020746e65
        .quad   0x7320676e69737365
        .quad   0x0000000065676174
        .quad   0x676f4c656c626174
        .quad   0x6572697571657220
        .quad   0x756d206f6f742073
        .quad   0x726f6d656d206863
        .quad   0x75736e75203a2079
        .quad   0x00646574726f7070
        .quad   0x726f707075736e55
        .quad   0x2078616d20646574
        .quad   0x56206c6f626d7953
        .quad   0x74203a2065756c61
        .quad   0x656772616c206f6f
        .quad   0x0000000000000000
        .quad   0x6569666963657053
        .quad   0x6d795378616d2064
        .quad   0x65756c61566c6f62
        .quad   0x206f6f7420736920
        .quad   0x0000006c6c616d73
        .quad   0x646f6d2073696854
        .quad   0x746f6e6e61632065
        .quad   0x746172656e656720
        .quad   0x636e75206e612065
        .quad   0x6573736572706d6f
        .quad   0x006b636f6c622064
        .quad   0x2064656764656c70
        .quad   0x7320726566667562
        .quad   0x7974696c69626174
        .quad   0x697469646e6f6320
        .quad   0x6f6e207369206e6f
        .quad   0x6365707365722074
        .quad   0x0000000000646574
        .quad   0x616e6f6974636944
        .quad   0x6f63207369207972
        .quad   0x0064657470757272
        .quad   0x616e6f6974636944
        .quad   0x616d73696d207972
        .quad   0x0000000000686374
        .quad   0x6320746f6e6e6143
        .quad   0x6944206574616572
        .quad   0x7972616e6f697463
        .quad   0x7270206d6f726620
        .quad   0x732064656469766f
        .quad   0x000073656c706d61
        .quad   0x74616e6974736544
        .quad   0x66667562206e6f69
        .quad   0x6f74207369207265
        .quad   0x006c6c616d73206f
        .quad   0x657a697320637253
        .quad   0x6f636e6920736920
        .quad   0x0000007463657272
        .quad   0x6f6974617265704f
        .quad   0x4c554e206e6f206e
        .quad   0x6e6974736564204c
        .quad   0x7562206e6f697461
        .quad   0x0000000072656666
        .quad   0x6f6974617265704f
        .quad   0x6e206564616d206e
        .quad   0x6572676f7270206f
        .quad   0x207265766f207373
        .quad   0x656c7069746c756d
        .quad   0x202c736c6c616320
        .quad   0x6f206f7420657564
        .quad   0x7562207475707475
        .quad   0x6965622072656666
        .quad   0x006c6c756620676e
        .quad   0x6f6974617265704f
        .quad   0x6e206564616d206e
        .quad   0x6572676f7270206f
        .quad   0x207265766f207373
        .quad   0x656c7069746c756d
        .quad   0x202c736c6c616320
        .quad   0x69206f7420657564
        .quad   0x696562207475706e
        .quad   0x7974706d6520676e
        .quad   0x0000000000000000
        .quad   0x6e6920656d617246
        .quad   0x7420736920786564
        .quad   0x656772616c206f6f
        .quad   0x0000000000000000
        .quad   0x65204f2f49206e41
        .quad   0x63636f20726f7272
        .quad   0x6877206465727275
        .quad   0x6964616572206e65
        .quad   0x696b6565732f676e
        .quad   0x000000000000676e
        .quad   0x74616e6974736544
        .quad   0x66667562206e6f69
        .quad   0x7277207369207265
        .quad   0x0000000000676e6f
        .quad   0x6220656372756f53
        .quad   0x7369207265666675
        .quad   0x0000676e6f727720
        .quad   0x656c2d6b636f6c42
        .quad   0x65747865206c6576
        .quad   0x716573206c616e72
        .quad   0x72702065636e6575
        .quad   0x722072656375646f
        .quad   0x2064656e72757465
        .quad   0x726f727265206e61
        .quad   0x00000065646f6320
        .quad   0x6c616e7265747845
        .quad   0x636e657571657320
        .quad   0x6e20657261207365
        .quad   0x64696c617620746f
        .quad   0x0000000000000000
        .quad   0x6669636570736e55
        .quad   0x6f72726520646569
        .quad   0x000065646f632072
        .quad   0xf7f7f7f7f7f76366
        .quad   0xf75af75df760f7f7
        .quad   0xf751f754f7f7f757
        .quad   0xf74bf7f7f7f7f74e
        .quad   0xf7f7f7f7f745f748
        .quad   0xf736f739f73c3f42
        .quad   0xf7f7f7f7f72d3033
        .quad   0xf727f72af7f7f7f7
        .quad   0xf71ef7f7f721f724
        .quad   0xf7f7f7f7f718f71b
        .quad   0xf7f7f7f7f712f715
        .quad   0xf7f7f7f7f7f7f7f7
        .quad   0xf70cf70ff7f7f7f7
        .quad   0x0000000000030609
        .quad   0x0000000000000000
// zeroFilled.0 (0x8 bytes)
        .quad   0x0000000000000000
        .quad   0x0000000000000000
// BIT_mask (0x80 bytes)
        .quad   0x0000000100000000
        .quad   0x0000000700000003
        .quad   0x0000001f0000000f
        .quad   0x0000007f0000003f
        .quad   0x000001ff000000ff
        .quad   0x000007ff000003ff
        .quad   0x00001fff00000fff
        .quad   0x00007fff00003fff
        .quad   0x0001ffff0000ffff
        .quad   0x0007ffff0003ffff
        .quad   0x001fffff000fffff
        .quad   0x007fffff003fffff
        .quad   0x01ffffff00ffffff
        .quad   0x07ffffff03ffffff
        .quad   0x1fffffff0fffffff
        .quad   0x7fffffff3fffffff
// zeroFilled.0 (0x8 bytes)
        .quad   0x0000000000000000
        .quad   0x0000000000000000
// algoTime (0x100 bytes)
        .quad   0x0000000000000000
        .quad   0x0000000100000001
        .quad   0x0000000000000000
        .quad   0x0000000100000001
        .quad   0x000000d800000096
        .quad   0x000000770000017d
        .quad   0x000000cd000000aa
        .quad   0x0000007000000202
        .quad   0x000000c7000000b1
        .quad   0x0000006e0000021b
        .quad   0x000000c2000000c5
        .quad   0x0000006b00000284
        .quad   0x000000c0000000dd
        .quad   0x0000006b000002df
        .quad   0x000000bd00000100
        .quad   0x0000006a00000371
        .quad   0x000000bc00000167
        .quad   0x0000006d0000048f
        .quad   0x000000bb00000246
        .quad   0x0000007200000622
        .quad   0x000000bb000002b0
        .quad   0x0000007a000006b0
        .quad   0x000000ba00000339
        .quad   0x00000088000007ad
        .quad   0x000000b9000003d0
        .quad   0x0000009600000853
        .quad   0x000000ba0000049c
        .quad   0x000000af00000816
        .quad   0x000000b900000561
        .quad   0x000000ca000006c3
        .quad   0x000000b900000584
        .quad   0x000000ca0000069f

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif

// Copyright (C) 2002-2013 Mark Adler (puff.c, see README.md)
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The code and read-only data of libpuff.so (gcc 12, -O2)
//
// This is a transcription of libpuff.so, zlib's contrib/puff/puff.c
// compiled by gcc 12 as a shared library (see README.md), as loaded at an
// address that is a multiple of 4096: the start of its first segment, from
// address 0 up to the end of the read-only data. The ELF header and dynamic
// linking information at the start are given as data, as are the padding
// and the read-only data at the end, while the procedure linkage table and
// the code are given as instructions. The ADRP instructions, which compute
// addresses of pages relative to that of the instruction, are given as
// words, as are the branches to addresses outside the code. The labels are
// named after the addresses in the binary.
// ----------------------------------------------------------------------------

        .text
        .balign 4

// ELF header and dynamic linking information (0x0 to 0x550)

// _setjmp@GLIBC_2.17 (0x0 bytes)
// __cxa_finalize@GLIBC_2.17 (0x0 bytes)
// longjmp@GLIBC_2.17 (0x0 bytes)
        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x0000000000010b80
        .quad   0x0038004000000000
        .quad   0x001a001b00400006
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00000000000013c0
        .quad   0x00000000000013c0
        .quad   0x0000000000010000
        .quad   0x0000000600000001
        .quad   0x000000000000fdc0
        .quad   0x000000000001fdc0
        .quad   0x000000000001fdc0
        .quad   0x000000000000026c
        .quad   0x0000000000000560
        .quad   0x0000000000010000
        .quad   0x0000000600000002
        .quad   0x000000000000fdd0
        .quad   0x000000000001fdd0
        .quad   0x000000000001fdd0
        .quad   0x00000000000001f0
        .quad   0x00000000000001f0
        .quad   0x0000000000000008
        .quad   0x000000046474e550
        .quad   0x00000000000011d8
        .quad   0x00000000000011d8
        .quad   0x00000000000011d8
        .quad   0x0000000000000054
        .quad   0x0000000000000054
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
        .quad   0x0000000a00000003
        .quad   0x0000000800000006
        .quad   0x0000000000000005
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000003
        .quad   0x0000000700000009
        .quad   0x0000000000000004
        .quad   0x0000000900000002
        .quad   0x0000000600000001
        .quad   0x0040001000000000
        .quad   0x0000000000000009
        .quad   0x000000007c9c7937
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0009000300000000
        .quad   0x0000000000000530
        .quad   0x0000000000000000
        .quad   0x0015000300000000
        .quad   0x0000000000020020
        .quad   0x0000000000000000
        .quad   0x0000001200000062
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000002000000010
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000002200000046
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000002000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001200000055
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000200000002c
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000b00120000005d
        .quad   0x0000000000000ad0
        .quad   0x00000000000005c8
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
        .quad   0x6e6f6c00657a696c
        .quad   0x66757000706d6a67
        .quad   0x6d6a7465735f0066
        .quad   0x732e6362696c0070
        .quad   0x7062696c00362e6f
        .quad   0x47006f732e666675
        .quad   0x312e325f4342494c
        .quad   0x732f78696e2f0037
        .quad   0x7161612f65726f74
        .quad   0x6639346134723633
        .quad   0x6277626d30687362
        .quad   0x68726a32767a696a
        .quad   0x6c672d6d7a717a34
        .quad   0x39332e322d636269
        .quad   0x3a62696c2f32352d
        .quad   0x6f74732f78696e2f
        .quad   0x676b38376c2f6572
        .quad   0x66393939397a7762
        .quad   0x6761726e37763379
        .quad   0x36303979796a6271
        .quad   0x2d6363672d336d64
        .quad   0x6c2d302e332e3231
        .quad   0x000062696c2f6269
        .quad   0x0002000000000000
        .quad   0x0002000100020001
        .quad   0x0000000000010001
        .quad   0x0000006a00010001
        .quad   0x0000000000000010
        .quad   0x0002000006969197
        .quad   0x000000000000007f
        .quad   0x000000000001fdc0
        .quad   0x0000000000000403
        .quad   0x0000000000000690
        .quad   0x000000000001fdc8
        .quad   0x0000000000000403
        .quad   0x0000000000000640
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
        .quad   0x0000000600000401
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

// The procedure linkage table and the code (0x550 to 0x1098)
// .plt
        stp     x16, x30, [sp, #-16]!
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4088]
        add     x16, x16, #0xff8
        br      x17
        nop
        nop
        nop
L0570:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16]
        add     x16, x16, #0x0
        br      x17
L0580:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16, #8]
        add     x16, x16, #0x8
        br      x17
L0590:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16, #16]
        add     x16, x16, #0x10
        br      x17
L05a0:
        .inst   0x90000110  // adrp x16, 0x20000
        ldr     x17, [x16, #24]
        add     x16, x16, #0x18
        br      x17

// call_weak_fn (0x14 bytes)
L05b0:
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4056]
        cbz     x0,L05c0
        b       L0590
L05c0:
        ret
        nop
        nop
        nop

// deregister_tm_clones (0x0 bytes)
L05d0:
        .inst   0x90000100  // adrp x0, 0x20000
        add     x0, x0, #0x30
        .inst   0x90000101  // adrp x1, 0x20000
        add     x1, x1, #0x30
        cmp     x1, x0
        b.eq    L05fc
        .inst   0xf00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4040]
        cbz     x1,L05fc
        mov     x16, x1
        br      x16
L05fc:
        ret

// register_tm_clones (0x0 bytes)
L0600:
        .inst   0x90000100  // adrp x0, 0x20000
        add     x0, x0, #0x30
        .inst   0x90000101  // adrp x1, 0x20000
        add     x1, x1, #0x30
        sub     x1, x1, x0
        lsr     x2, x1, #63
        add     x1, x2, x1, asr #3
        asr     x1, x1, #1
        cbz     x1,L0638
        .inst   0xf00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4064]
        cbz     x2,L0638
        mov     x16, x2
        br      x16
L0638:
        ret
        nop

// __do_global_dtors_aux (0x0 bytes)
L0640:
        stp     x29, x30, [sp, #-32]!
        mov     x29, sp
        str     x19, [sp, #16]
        .inst   0x90000113  // adrp x19, 0x20000
        ldrb    w0, [x19, #48]
        cbnz    w0,L067c
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4048]
        cbz     x0,L0670
        .inst   0x90000100  // adrp x0, 0x20000
        ldr     x0, [x0, #32]
        bl      L0580
L0670:
        bl      L05d0
        mov     w0, #0x1
        strb    w0, [x19, #48]
L067c:
        ldr     x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
        nop
        nop

// frame_dummy (0x0 bytes)
L0690:
        b       L0600
        nop
        nop
        nop

// construct (0xfc bytes)
L06a0:
        ldr     x5, [x0]
        mov     x9, x0
        stp     xzr, xzr, [x5]
        stp     xzr, xzr, [x5, #16]
        cmp     w2, #0x0
        b.le    L06dc
        mov     x6, x1
        add     x7, x1, w2, sxtw #1
L06c0:
        ldrsh   x3, [x6], #2
        lsl     x3, x3, #1
        ldrh    w4, [x5, x3]
        add     w4, w4, #0x1
        strh    w4, [x5, x3]
        cmp     x7, x6
        b.ne    L06c0
L06dc:
        ldrsh   w3, [x5]
        mov     w0, #0x0
        cmp     w3, w2
        b.eq    L0798
        ldrsh   w0, [x5, #2]
        mov     w3, #0x2
        subs    w0, w3, w0
        b.mi    L0798
        add     x4, x5, #0x4
        add     x7, x5, #0x20
        b       L0714
L0708:
        ldrsh   w3, [x4], #2
        subs    w0, w6, w3
        b.mi    L0798
L0714:
        lsl     w6, w0, #1
        cmp     x4, x7
        b.ne    L0708
        sub     sp, sp, #0x20
        add     x5, x5, #0x2
        mov     x8, sp
        mov     x4, #0x0
        mov     w3, #0x0
        strh    wzr, [sp, #2]
L0738:
        ldrh    w7, [x5, x4]
        add     x6, x8, x4
        add     x4, x4, #0x2
        add     w3, w3, w7
        sxth    w3, w3
        strh    w3, [x6, #4]
        cmp     x4, #0x1c
        b.ne    L0738
        cmp     w2, #0x0
        b.le    L0790
        sxtw    x4, w2
        mov     x2, #0x0
L0768:
        ldrsh   w3, [x1, x2, lsl #1]
        cbz     w3,L0784
        ldr     x6, [x9, #8]
        ldrsh   w5, [x8, w3, sxtw #1]
        add     w7, w5, #0x1
        strh    w7, [x8, w3, sxtw #1]
        strh    w2, [x6, w5, sxtw #1]
L0784:
        add     x2, x2, #0x1
        cmp     x2, x4
        b.ne    L0768
L0790:
        add     sp, sp, #0x20
        ret
L0798:
        ret
        nop

// bits (0x88 bytes)
L07a0:
        ldp     w3, w2, [x0, #48]
        mov     x4, x0
        sxtw    x5, w3
        cmp     w1, w2
        b.le    L07f4
        ldp     x7, x3, [x0, #32]
        b       L07c0
L07bc:
        mov     x3, x0
L07c0:
        cmp     x7, x3
        b.eq    L0814
        ldr     x6, [x4, #24]
        add     x0, x3, #0x1
        str     x0, [x4, #40]
        ldrb    w3, [x6, x3]
        lsl     x3, x3, x2
        add     w2, w2, #0x8
        str     w2, [x4, #52]
        orr     x5, x5, x3
        cmp     w2, w1
        b.lt    L07bc
        mov     w3, w5
L07f4:
        mov     x0, #0x1
        sub     w2, w2, w1
        lsl     x0, x0, x1
        sub     w0, w0, #0x1
        asr     x5, x5, x1
        and     w0, w0, w3
        stp     w5, w2, [x4, #48]
        ret
L0814:
        stp     x29, x30, [sp, #-16]!
        add     x0, x4, #0x38
        mov     w1, #0x1
        mov     x29, sp
        bl      L05a0
        nop
        nop

// decode (0xd0 bytes)
L0830:
        ldr     x3, [x1]
        mov     w10, #0x0
        ldp     w6, w13, [x0, #48]
        add     x3, x3, #0x2
        mov     w5, #0x0
        mov     w4, #0x0
        mov     w2, w13
        mov     w7, #0x1
        mov     w9, #0x10
        mov     w12, #0x8
L0858:
        cbnz    w2,L088c
L085c:
        subs    w2, w9, w7
        b.eq    L08c4
        ldp     x8, x6, [x0, #32]
        cmp     x6, x8
        b.eq    L08ec
        ldr     x8, [x0, #24]
        add     x11, x6, #0x1
        str     x11, [x0, #40]
        cmp     w2, #0x8
        csel    w2, w2, w12, le
        ldrb    w6, [x8, x6]
        cbz     w2,L085c
L088c:
        and     w8, w6, #0x1
        asr     w6, w6, #1
        orr     w4, w8, w4
        ldrsh   w8, [x3], #2
        sub     w11, w4, w8
        cmp     w11, w5
        b.lt    L08cc
        add     w5, w5, w8
        sub     w2, w2, #0x1
        add     w10, w10, w8
        lsl     w4, w4, #1
        lsl     w5, w5, #1
        add     w7, w7, #0x1
        b       L0858
L08c4:
        mov     w0, #0xfffffff6
        ret
L08cc:
        ldr     x3, [x1, #8]
        sub     w1, w4, w5
        add     w1, w1, w10
        sub     w2, w13, w7
        and     w2, w2, #0x7
        stp     w6, w2, [x0, #48]
        ldrsh   w0, [x3, w1, sxtw #1]
        ret
L08ec:
        stp     x29, x30, [sp, #-16]!
        add     x0, x0, #0x38
        mov     w1, #0x1
        mov     x29, sp
        bl      L05a0

// codes (0x1cc bytes)
L0900:
        stp     x29, x30, [sp, #-96]!
        mov     x29, sp
        stp     x21, x22, [sp, #32]
        .inst   0xb0000015  // adrp x21, 0x1000
        add     x21, x21, #0xb0
        mov     x22, x2
        stp     x19, x20, [sp, #16]
        mov     x20, x1
        stp     x23, x24, [sp, #48]
        add     x23, x21, #0x40
        add     x24, x21, #0xc0
        stp     x25, x26, [sp, #64]
        add     x25, x21, #0x80
        stp     x27, x28, [sp, #80]
        mov     x28, x0
        nop
L0940:
        mov     x1, x20
        mov     x0, x28
        bl      L0830
        mov     w19, w0
        tbnz    w0, #31,L0998
L0954:
        cmp     w0, #0xff
        b.gt    L09b8
        ldr     x1, [x28]
        ldr     x0, [x28, #16]
        cbz     x1,L097c
        ldr     x2, [x28, #8]
        cmp     x2, x0
        b.eq    L0ab4
        strb    w19, [x1, x0]
        ldr     x0, [x28, #16]
L097c:
        add     x0, x0, #0x1
        str     x0, [x28, #16]
        mov     x1, x20
        mov     x0, x28
        bl      L0830
        mov     w19, w0
        tbz     w0, #31,L0954
L0998:
        ldp     x21, x22, [sp, #32]
        mov     w0, w19
        ldp     x19, x20, [sp, #16]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldp     x29, x30, [sp], #96
        ret
L09b8:
        cmp     w0, #0x100
        b.eq    L0a2c
        sub     w19, w0, #0x101
        cmp     w19, #0x1c
        b.gt    L0abc
        ldrsh   w1, [x23, w19, sxtw #1]
        mov     x0, x28
        ldrsh   w26, [x21, w19, sxtw #1]
        bl      L07a0
        add     w26, w26, w0
        mov     x1, x22
        mov     x0, x28
        bl      L0830
        mov     w19, w0
        tbnz    w0, #31,L0998
        ldrsh   w1, [x24, w0, sxtw #1]
        mov     x0, x28
        ldrsh   w27, [x25, w19, sxtw #1]
        bl      L07a0
        add     w4, w27, w0
        ldr     x2, [x28, #16]
        cmp     x4, x2
        b.hi    L0ac4
        ldr     x0, [x28]
        add     x1, x2, w26, sxtw
        cbnz    x0,L0a50
        str     x1, [x28, #16]
L0a24:
        cmp     w19, #0x100
        b.ne    L0940
L0a2c:
        mov     w19, #0x0
        mov     w0, w19
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldp     x29, x30, [sp], #96
        ret
L0a50:
        ldr     x3, [x28, #8]
        cmp     x3, x1
        b.cc    L0ab4
        cbz     w26,L0a24
        sub     x3, x2, x4
        sub     w1, w26, #0x2
        ldrb    w3, [x0, x3]
        strb    w3, [x0, x2]
        ldr     x3, [x28, #16]
        add     x3, x3, #0x1
        str     x3, [x28, #16]
        cmp     w26, #0x1
        b.eq    L0a24
        nop
L0a88:
        ldr     x2, [x28]
        sub     x0, x3, x4
        sub     w1, w1, #0x1
        ldrb    w0, [x2, x0]
        strb    w0, [x2, x3]
        ldr     x3, [x28, #16]
        add     x3, x3, #0x1
        str     x3, [x28, #16]
        cmn     w1, #0x1
        b.ne    L0a88
        b       L0a24
L0ab4:
        mov     w19, #0x1
        b       L0998
L0abc:
        mov     w19, #0xfffffff6
        b       L0998
L0ac4:
        mov     w19, #0xfffffff5
        b       L0998
        nop

// puff (0x5c8 bytes)
L0ad0:
        sub     sp, sp, #0x990
        mov     x4, x1
        stp     x29, x30, [sp]
        mov     x29, sp
        stp     x1, x3, [sp, #112]
        mov     x1, x0
        add     x0, sp, #0x158
        str     x1, [sp, #288]
        ldr     x1, [x4]
        str     x1, [sp, #296]
        ldr     x1, [x3]
        stp     x19, x20, [sp, #16]
        stp     x21, x22, [sp, #32]
        stp     x23, x24, [sp, #48]
        stp     x25, x26, [sp, #64]
        stp     x27, x28, [sp, #80]
        stp     xzr, x2, [sp, #304]
        str     x1, [sp, #320]
        str     xzr, [sp, #328]
        str     xzr, [sp, #336]
        bl      L0570
        str     w0, [sp, #108]
        cbnz    w0,L1034
        .inst   0xb0000013  // adrp x19, 0x1000
        add     x19, x19, #0xb0
        add     x19, x19, #0x100
        .inst   0x90000100  // adrp x0, 0x20000
        add     x0, x0, #0x28
        str     x0, [sp, #96]
        nop
L0b48:
        add     x21, sp, #0x120
        mov     w1, #0x1
        mov     x0, x21
        bl      L07a0
        mov     w1, #0x2
        mov     w20, w0
        mov     x0, x21
        bl      L07a0
        cbz     w0,L0c94
        cmp     w0, #0x1
        b.eq    L0f00
        cmp     w0, #0x2
        b.ne    L1060
        add     x5, sp, #0xa0
        add     x4, sp, #0x290
        add     x3, sp, #0xc0
        add     x2, sp, #0xe0
        mov     w1, #0x5
        mov     x0, x21
        stp     x5, x4, [sp, #128]
        stp     x3, x2, [sp, #144]
        bl      L07a0
        mov     w1, #0x5
        add     w25, w0, #0x101
        mov     x0, x21
        bl      L07a0
        add     w26, w0, #0x1
        mov     w1, #0x4
        mov     x0, x21
        bl      L07a0
        cmp     w25, #0x11e
        ccmp    w26, #0x1e, #0x0, le
        b.gt    L1078
        add     w24, w0, #0x5
        add     x22, sp, #0x718
        mov     x27, #0x1
        mov     w23, #0x3
        cmn     w0, #0x3
        b.ge    L0bec
        b       L1008
L0be8:
        mov     x27, x2
L0bec:
        mov     w1, w23
        mov     x0, x21
        bl      L07a0
        add     x1, x19, x27, lsl #1
        add     x2, x27, #0x1
        ldursh  x1, [x1, #-2]
        strh    w0, [x22, x1, lsl #1]
        cmp     x24, x2
        b.ne    L0be8
        mov     w0, w27
        cmp     w27, #0x13
        b.eq    L0c3c
L0c1c:
        sxtw    x0, w0
        add     x2, sp, #0x718
        nop
L0c28:
        ldrsh   x1, [x19, x0, lsl #1]
        add     x0, x0, #0x1
        strh    wzr, [x2, x1, lsl #1]
        cmp     w0, #0x13
        b.ne    L0c28
L0c3c:
        add     x23, sp, #0x718
        add     x24, sp, #0x80
        mov     x1, x23
        mov     x0, x24
        mov     w2, #0x13
        bl      L06a0
        cbz     w0,L0d84
        mov     w0, #0xfffffffc
L0c5c:
        ldr     x2, [sp, #112]
        ldr     x1, [sp, #304]
        str     x1, [x2]
        ldr     x2, [sp, #120]
        ldr     x1, [sp, #328]
        str     x1, [x2]
L0c74:
        ldp     x29, x30, [sp]
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        add     sp, sp, #0x990
        ret
L0c94:
        ldp     x5, x0, [sp, #320]
        str     xzr, [sp, #336]
        add     x4, x0, #0x4
        cmp     x4, x5
        b.hi    L1034
        ldr     x3, [sp, #312]
        add     x2, x0, #0x1
        str     x2, [sp, #328]
        add     x1, x0, #0x2
        add     x6, x0, #0x3
        ldrb    w7, [x3, x0]
        str     x1, [sp, #328]
        ldrb    w2, [x3, x2]
        str     x6, [sp, #328]
        orr     w2, w7, w2, lsl #8
        ldrb    w7, [x3, x1]
        mvn     w1, w2
        cmp     w7, w1, uxtb
        b.ne    L1058
        str     x4, [sp, #328]
        ubfx    x1, x1, #8, #8
        ldrb    w6, [x3, x6]
        cmp     w6, w1
        b.ne    L1058
        add     x6, x4, w2, uxth
        mov     w1, w2
        cmp     x5, x6
        b.cc    L1034
        ldr     x7, [sp, #288]
        ldr     x5, [sp, #304]
        add     x1, x1, x5
        cbz     x7,L0ff8
        ldr     x6, [sp, #296]
        cmp     x6, x1
        b.cc    L1010
        cbz     w2,L0d78
        add     x1, x0, #0x5
        add     x0, x5, #0x1
        str     x0, [sp, #304]
        sub     w0, w2, #0x2
        str     x1, [sp, #328]
        ldrb    w1, [x3, x4]
        strb    w1, [x7, x5]
        cmp     w2, #0x1
        b.eq    L0d78
L0d48:
        ldp     x1, x4, [sp, #304]
        sub     w0, w0, #0x1
        ldr     x2, [sp, #328]
        ldr     x3, [sp, #288]
        add     x5, x2, #0x1
        add     x6, x1, #0x1
        str     x6, [sp, #304]
        str     x5, [sp, #328]
        ldrb    w2, [x4, x2]
        strb    w2, [x3, x1]
        cmn     w0, #0x1
        b.ne    L0d48
L0d78:
        cbz     w20,L0b48
L0d7c:
        ldr     w0, [sp, #108]
        b       L0c5c
L0d84:
        add     w21, w25, w26
        add     x22, sp, #0x120
        mov     w28, #0x0
        mov     w27, #0x0
        cmp     w21, #0x0
        b.gt    L0db0
        b       L0e30
L0da0:
        strh    w0, [x23, w28, sxtw #1]
        add     w28, w28, #0x1
L0da8:
        cmp     w28, w21
        b.ge    L0e30
L0db0:
        mov     x1, x24
        mov     x0, x22
        bl      L0830
        tbnz    w0, #31,L0c5c
        cmp     w0, #0xf
        b.le    L0da0
        cmp     w0, #0x10
        b.eq    L0eb0
        cmp     w0, #0x11
        b.eq    L0ee8
        mov     x0, x22
        mov     w1, #0x7
        bl      L07a0
        add     w0, w0, #0xb
        mov     w3, w27
L0dec:
        add     w1, w0, w28
        cmp     w1, w21
        b.gt    L0ee0
L0df8:
        sub     w4, w0, #0x1
        cbz     w0,L0da8
        sxth    w3, w3
        add     x1, x23, w28, sxtw #1
        mov     w0, w4
        nop
L0e10:
        sub     w0, w0, #0x1
        strh    w3, [x1], #2
        cmn     w0, #0x1
        b.ne    L0e10
        add     w2, w28, #0x1
        add     w28, w2, w4
        cmp     w28, w21
        b.lt    L0db0
L0e30:
        ldrsh   w0, [sp, #2328]
        cbz     w0,L1090
        mov     w2, w25
        add     x1, sp, #0x718
        add     x0, sp, #0x80
        bl      L06a0
        cmp     w0, #0x0
        cbz     w0,L0e68
        b.lt    L1088
        ldrsh   w0, [sp, #160]
        ldrsh   w1, [sp, #162]
        add     w0, w0, w1
        cmp     w25, w0
        b.ne    L1088
L0e68:
        add     x1, sp, #0x718
        mov     w2, w26
        add     x1, x1, w25, sxtw #1
        add     x0, sp, #0x90
        bl      L06a0
        cmp     w0, #0x0
        cbz     w0,L0e9c
        b.lt    L1080
        ldrsh   w0, [sp, #192]
        ldrsh   w1, [sp, #194]
        add     w0, w0, w1
        cmp     w26, w0
        b.ne    L1080
L0e9c:
        add     x2, sp, #0x90
        add     x1, sp, #0x80
        add     x0, sp, #0x120
        bl      L0900
        b       L0fe8
L0eb0:
        cbz     w28,L1070
        sub     w3, w28, #0x1
        mov     w1, #0x2
        mov     x0, x22
        ldrsh   w3, [x23, w3, sxtw #1]
        str     w3, [sp, #104]
        bl      L07a0
        add     w0, w0, #0x3
        add     w1, w0, w28
        ldr     w3, [sp, #104]
        cmp     w1, w21
        b.le    L0df8
L0ee0:
        mov     w0, #0xfffffffa
        b       L0fe8
L0ee8:
        mov     x0, x22
        mov     w1, #0x3
        bl      L07a0
        add     w0, w0, #0x3
        mov     w3, w27
        b       L0dec
L0f00:
        ldr     x0, [sp, #96]
        ldr     w0, [x0]
        cbz     w0,L0fd4
        .inst   0x90000104  // adrp x4, 0x20000
        add     x2, x4, #0x40
        add     x10, sp, #0x4d0
        add     x5, x2, #0x10
        movi    v0.8h, #0x8
        mov     x0, x10
        add     x1, sp, #0x5f0
        str     x5, [x4, #64]
        add     x6, x2, #0x30
        add     x5, x2, #0x280
        add     x4, x2, #0x2a0
        str     x6, [x2, #8]
        str     x5, [x2, #624]
        str     x4, [x2, #632]
        nop
L0f48:
        str     q0, [x0], #16
        cmp     x0, x1
        b.ne    L0f48
        movi    v0.8h, #0x9
        add     x1, x10, #0xe0
        mov     x0, x10
L0f60:
        add     x0, x0, #0x10
        str     q0, [x0, #272]
        cmp     x0, x1
        b.ne    L0f60
        movi    v0.8h, #0x7
        add     x1, sp, #0x4d0
        movi    v1.8h, #0x8
        .inst   0x90000100  // adrp x0, 0x20000
        mov     w2, #0x120
        add     x0, x0, #0x40
        str     q0, [sp, #1744]
        str     q0, [sp, #1760]
        str     q0, [sp, #1776]
        str     q1, [sp, #1792]
        bl      L06a0
        add     x1, x10, #0x3c
        mov     w0, #0x5
        nop
L0fa8:
        strh    w0, [x10], #2
        cmp     x10, x1
        b.ne    L0fa8
        .inst   0x90000100  // adrp x0, 0x20000
        add     x0, x0, #0x40
        add     x0, x0, #0x270
        add     x1, sp, #0x4d0
        mov     w2, #0x1e
        bl      L06a0
        ldr     x0, [sp, #96]
        str     wzr, [x0]
L0fd4:
        .inst   0x90000101  // adrp x1, 0x20000
        add     x1, x1, #0x40
        add     x2, x1, #0x270
        add     x0, sp, #0x120
        bl      L0900
L0fe8:
        cmp     w0, #0x0
        cbz     w0,L0d78
        b.gt    L0c74
        b       L0c5c
L0ff8:
        str     x1, [sp, #304]
        str     x6, [sp, #328]
        cbz     w20,L0b48
        b       L0d7c
L1008:
        ldr     w0, [sp, #108]
        b       L0c1c
L1010:
        ldp     x29, x30, [sp]
        mov     w0, #0x1
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        add     sp, sp, #0x990
        ret
L1034:
        ldp     x29, x30, [sp]
        mov     w0, #0x2
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        add     sp, sp, #0x990
        ret
L1058:
        mov     w0, #0xfffffffe
        b       L0c5c
L1060:
        mov     w0, #0xffffffff
        str     w0, [sp, #108]
        ldr     w0, [sp, #108]
        b       L0c5c
L1070:
        mov     w0, #0xfffffffb
        b       L0fe8
L1078:
        mov     w0, #0xfffffffd
        b       L0c5c
L1080:
        mov     w0, #0xfffffff8
        b       L0c5c
L1088:
        mov     w0, #0xfffffff9
        b       L0c5c
L1090:
        mov     w0, #0xfffffff7
        b       L0c5c

// Padding (0x1098 to 0x10b0)

// _fini (0x0 bytes)
        .quad   0xa9bf7bfdd503201f
        .quad   0xa8c17bfd910003fd
        .quad   0x00000000d65f03c0

// The read-only data (0x10b0 to 0x11d6)

// lens.4 (0x3a bytes)
        .quad   0x0006000500040003
        .quad   0x000a000900080007
        .quad   0x0011000f000d000b
        .quad   0x001f001b00170013
        .quad   0x003b0033002b0023
        .quad   0x0073006300530043
        .quad   0x00e300c300a30083
        .quad   0x0000000000000102
// lext.3 (0x3a bytes)
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0001000100010001
        .quad   0x0002000200020002
        .quad   0x0003000300030003
        .quad   0x0004000400040004
        .quad   0x0005000500050005
        .quad   0x0000000000000000
// dists.2 (0x3c bytes)
        .quad   0x0004000300020001
        .quad   0x000d000900070005
        .quad   0x0031002100190011
        .quad   0x00c1008100610041
        .quad   0x0301020101810101
        .quad   0x0c01080106010401
        .quad   0x3001200118011001
        .quad   0x0000000060014001
// dext.1 (0x3c bytes)
        .quad   0x0000000000000000
        .quad   0x0002000200010001
        .quad   0x0004000400030003
        .quad   0x0006000600050005
        .quad   0x0008000800070007
        .quad   0x000a000a00090009
        .quad   0x000c000c000b000b
        .quad   0x00000000000d000d
// order.0 (0x26 bytes)
        .quad   0x0000001200110010
        .quad   0x0006000900070008
        .quad   0x0004000b0005000a
        .quad   0x0002000d0003000c
        .quad   0x0000000f0001000e

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif

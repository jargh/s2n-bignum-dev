(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function puff(dest,destlen,source,sourcelen) of zlib's                *)
(* contrib/puff/puff.c, at 0xad0 in the image, which decompresses the        *)
(* DEFLATE data (RFC 1951) of *sourcelen bytes at source into the buffer of  *)
(* *destlen bytes at dest, block by block, gcc having inlined the decoding   *)
(* of stored blocks and of blocks with the fixed codes and with dynamic      *)
(* codes (stored, fixed and dynamic in puff.c). It returns 0 if the data     *)
(* decodes and the output fits, after storing the numbers of bytes written   *)
(* and read in *destlen and *sourcelen, 2 if the input runs out (bits and    *)
(* decode then call longjmp(s.env,1), back to the setjmp at the start), 1 if *)
(* the output does not fit, and a negative number if the data is not valid.  *)
(*                                                                           *)
(* PUFF_CORRECT says that if it returns 0 then the output and the number of  *)
(* bytes read are those of the (unique) decoding deflate_decode, and that    *)
(* otherwise there is no decoding whose output fits in the buffer. It        *)
(* assumes the contracts of setjmp and longjmp, which the code calls through *)
(* the GOT at pc + 0x20000 and pc + 0x20018, and keeps the invariant         *)
(* puff_fixed_tables about the tables of the fixed codes, which puff builds  *)
(* in the data of the image (at pc + 0x20040) when it first needs them.      *)
(*                                                                           *)
(* The proof follows the loop over the blocks, at 0xb48, with the invariant  *)
(* puff_inv n for n bits left in the input, and each block through the       *)
(* dispatch on the block type (puff_dispatch) and its end (puff_blockend),   *)
(* and the loops in the blocks with ENSURES_LOOP_EXIT and                    *)
(* ENSURES_WHILE_MEASURE. The calls of bits, decode, construct and codes use *)
(* their correctness theorems, and the theory of the specification gives the *)
(* decoding of a stream one block at a time.                                 *)
(*                                                                           *)
(* In the listing, in hex, 0x570 is _setjmp (by the PLT), 0x7a0 bits, 0x830  *)
(* decode, 0x6a0 construct and 0x900 codes. In the frame, from sp after the  *)
(* sub at 0xad0, the state s is at sp + 0x120 and its env at sp + 0x158,     *)
(* lencode and distcode are at sp + 0x80 and sp + 0x90, with their counts    *)
(* and symbols at sp + 0xa0, sp + 0x290, sp + 0xc0 and sp + 0xe0, the code   *)
(* lengths of a dynamic block at sp + 0x718, and those of the fixed codes at *)
(* sp + 0x4d0. x19 points to the order of the code length code lengths, at   *)
(* 0x11b0.                                                                   *)
(*                                                                           *)
(* ad0: sub   sp, sp, #0x990          db4: mov   x0, x22                     *)
(* ad4: mov   x4, x1                  db8: bl    0x830 (decode)              *)
(* ad8: stp   x29, x30, [sp]          dbc: tbnz  w0, #31, 0xc5c              *)
(* adc: mov   x29, sp                 dc0: cmp   w0, #0xf                    *)
(* ae0: stp   x1, x3, [sp, #112]      dc4: b.le  0xda0                       *)
(* ae4: mov   x1, x0                  dc8: cmp   w0, #0x10                   *)
(* ae8: add   x0, sp, #0x158          dcc: b.eq  0xeb0                       *)
(* aec: str   x1, [sp, #288]          dd0: cmp   w0, #0x11                   *)
(* af0: ldr   x1, [x4]                dd4: b.eq  0xee8                       *)
(* af4: str   x1, [sp, #296]          dd8: mov   x0, x22                     *)
(* af8: ldr   x1, [x3]                ddc: mov   w1, #0x7                    *)
(* afc: stp   x19, x20, [sp, #16]     de0: bl    0x7a0 (bits)                *)
(* b00: stp   x21, x22, [sp, #32]     de4: add   w0, w0, #0xb                *)
(* b04: stp   x23, x24, [sp, #48]     de8: mov   w3, w27                     *)
(* b08: stp   x25, x26, [sp, #64]     dec: add   w1, w0, w28                 *)
(* b0c: stp   x27, x28, [sp, #80]     df0: cmp   w1, w21                     *)
(* b10: stp   xzr, x2, [sp, #304]     df4: b.gt  0xee0                       *)
(* b14: str   x1, [sp, #320]          df8: sub   w4, w0, #0x1                *)
(* b18: str   xzr, [sp, #328]         dfc: cbz   w0, 0xda8                   *)
(* b1c: str   xzr, [sp, #336]         e00: sxth  w3, w3                      *)
(* b20: bl    0x570 (setjmp)          e04: add   x1, x23, w28, sxtw #1       *)
(* b24: str   w0, [sp, #108]          e08: mov   w0, w4                      *)
(* b28: cbnz  w0, 0x1034              e0c: nop                               *)
(* b2c: adrp  x19, 0x1000             e10: sub   w0, w0, #0x1                *)
(* b30: add   x19, x19, #0xb0         e14: strh  w3, [x1], #2                *)
(* b34: add   x19, x19, #0x100        e18: cmn   w0, #0x1                    *)
(* b38: adrp  x0, 0x20000             e1c: b.ne  0xe10                       *)
(* b3c: add   x0, x0, #0x28           e20: add   w2, w28, #0x1               *)
(* b40: str   x0, [sp, #96]           e24: add   w28, w2, w4                 *)
(* b44: nop                           e28: cmp   w28, w21                    *)
(* b48: add   x21, sp, #0x120         e2c: b.lt  0xdb0                       *)
(* b4c: mov   w1, #0x1                e30: ldrsh w0, [sp, #2328]             *)
(* b50: mov   x0, x21                 e34: cbz   w0, 0x1090                  *)
(* b54: bl    0x7a0 (bits)            e38: mov   w2, w25                     *)
(* b58: mov   w1, #0x2                e3c: add   x1, sp, #0x718              *)
(* b5c: mov   w20, w0                 e40: add   x0, sp, #0x80               *)
(* b60: mov   x0, x21                 e44: bl    0x6a0 (construct)           *)
(* b64: bl    0x7a0 (bits)            e48: cmp   w0, #0x0                    *)
(* b68: cbz   w0, 0xc94               e4c: cbz   w0, 0xe68                   *)
(* b6c: cmp   w0, #0x1                e50: b.lt  0x1088                      *)
(* b70: b.eq  0xf00                   e54: ldrsh w0, [sp, #160]              *)
(* b74: cmp   w0, #0x2                e58: ldrsh w1, [sp, #162]              *)
(* b78: b.ne  0x1060                  e5c: add   w0, w0, w1                  *)
(* b7c: add   x5, sp, #0xa0           e60: cmp   w25, w0                     *)
(* b80: add   x4, sp, #0x290          e64: b.ne  0x1088                      *)
(* b84: add   x3, sp, #0xc0           e68: add   x1, sp, #0x718              *)
(* b88: add   x2, sp, #0xe0           e6c: mov   w2, w26                     *)
(* b8c: mov   w1, #0x5                e70: add   x1, x1, w25, sxtw #1        *)
(* b90: mov   x0, x21                 e74: add   x0, sp, #0x90               *)
(* b94: stp   x5, x4, [sp, #128]      e78: bl    0x6a0 (construct)           *)
(* b98: stp   x3, x2, [sp, #144]      e7c: cmp   w0, #0x0                    *)
(* b9c: bl    0x7a0 (bits)            e80: cbz   w0, 0xe9c                   *)
(* ba0: mov   w1, #0x5                e84: b.lt  0x1080                      *)
(* ba4: add   w25, w0, #0x101         e88: ldrsh w0, [sp, #192]              *)
(* ba8: mov   x0, x21                 e8c: ldrsh w1, [sp, #194]              *)
(* bac: bl    0x7a0 (bits)            e90: add   w0, w0, w1                  *)
(* bb0: add   w26, w0, #0x1           e94: cmp   w26, w0                     *)
(* bb4: mov   w1, #0x4                e98: b.ne  0x1080                      *)
(* bb8: mov   x0, x21                 e9c: add   x2, sp, #0x90               *)
(* bbc: bl    0x7a0 (bits)            ea0: add   x1, sp, #0x80               *)
(* bc0: cmp   w25, #0x11e             ea4: add   x0, sp, #0x120              *)
(* bc4: ccmp  w26, #0x1e, #0x0, le    ea8: bl    0x900 (codes)               *)
(* bc8: b.gt  0x1078                  eac: b     0xfe8                       *)
(* bcc: add   w24, w0, #0x5           eb0: cbz   w28, 0x1070                 *)
(* bd0: add   x22, sp, #0x718         eb4: sub   w3, w28, #0x1               *)
(* bd4: mov   x27, #0x1               eb8: mov   w1, #0x2                    *)
(* bd8: mov   w23, #0x3               ebc: mov   x0, x22                     *)
(* bdc: cmn   w0, #0x3                ec0: ldrsh w3, [x23, w3, sxtw #1]      *)
(* be0: b.ge  0xbec                   ec4: str   w3, [sp, #104]              *)
(* be4: b     0x1008                  ec8: bl    0x7a0 (bits)                *)
(* be8: mov   x27, x2                 ecc: add   w0, w0, #0x3                *)
(* bec: mov   w1, w23                 ed0: add   w1, w0, w28                 *)
(* bf0: mov   x0, x21                 ed4: ldr   w3, [sp, #104]              *)
(* bf4: bl    0x7a0 (bits)            ed8: cmp   w1, w21                     *)
(* bf8: add   x1, x19, x27, lsl #1    edc: b.le  0xdf8                       *)
(* bfc: add   x2, x27, #0x1           ee0: mov   w0, #0xfffffffa             *)
(* c00: ldurshx1, [x1, #-2]           ee4: b     0xfe8                       *)
(* c04: strh  w0, [x22, x1, lsl #1]   ee8: mov   x0, x22                     *)
(* c08: cmp   x24, x2                 eec: mov   w1, #0x3                    *)
(* c0c: b.ne  0xbe8                   ef0: bl    0x7a0 (bits)                *)
(* c10: mov   w0, w27                 ef4: add   w0, w0, #0x3                *)
(* c14: cmp   w27, #0x13              ef8: mov   w3, w27                     *)
(* c18: b.eq  0xc3c                   efc: b     0xdec                       *)
(* c1c: sxtw  x0, w0                  f00: ldr   x0, [sp, #96]               *)
(* c20: add   x2, sp, #0x718          f04: ldr   w0, [x0]                    *)
(* c24: nop                           f08: cbz   w0, 0xfd4                   *)
(* c28: ldrsh x1, [x19, x0, lsl #1]   f0c: adrp  x4, 0x20000                 *)
(* c2c: add   x0, x0, #0x1            f10: add   x2, x4, #0x40               *)
(* c30: strh  wzr, [x2, x1, lsl #1]   f14: add   x10, sp, #0x4d0             *)
(* c34: cmp   w0, #0x13               f18: add   x5, x2, #0x10               *)
(* c38: b.ne  0xc28                   f1c: movi  v0.8h, #0x8                 *)
(* c3c: add   x23, sp, #0x718         f20: mov   x0, x10                     *)
(* c40: add   x24, sp, #0x80          f24: add   x1, sp, #0x5f0              *)
(* c44: mov   x1, x23                 f28: str   x5, [x4, #64]               *)
(* c48: mov   x0, x24                 f2c: add   x6, x2, #0x30               *)
(* c4c: mov   w2, #0x13               f30: add   x5, x2, #0x280              *)
(* c50: bl    0x6a0 (construct)       f34: add   x4, x2, #0x2a0              *)
(* c54: cbz   w0, 0xd84               f38: str   x6, [x2, #8]                *)
(* c58: mov   w0, #0xfffffffc         f3c: str   x5, [x2, #624]              *)
(* c5c: ldr   x2, [sp, #112]          f40: str   x4, [x2, #632]              *)
(* c60: ldr   x1, [sp, #304]          f44: nop                               *)
(* c64: str   x1, [x2]                f48: str   q0, [x0], #16               *)
(* c68: ldr   x2, [sp, #120]          f4c: cmp   x0, x1                      *)
(* c6c: ldr   x1, [sp, #328]          f50: b.ne  0xf48                       *)
(* c70: str   x1, [x2]                f54: movi  v0.8h, #0x9                 *)
(* c74: ldp   x29, x30, [sp]          f58: add   x1, x10, #0xe0              *)
(* c78: ldp   x19, x20, [sp, #16]     f5c: mov   x0, x10                     *)
(* c7c: ldp   x21, x22, [sp, #32]     f60: add   x0, x0, #0x10               *)
(* c80: ldp   x23, x24, [sp, #48]     f64: str   q0, [x0, #272]              *)
(* c84: ldp   x25, x26, [sp, #64]     f68: cmp   x0, x1                      *)
(* c88: ldp   x27, x28, [sp, #80]     f6c: b.ne  0xf60                       *)
(* c8c: add   sp, sp, #0x990          f70: movi  v0.8h, #0x7                 *)
(* c90: ret                           f74: add   x1, sp, #0x4d0              *)
(* c94: ldp   x5, x0, [sp, #320]      f78: movi  v1.8h, #0x8                 *)
(* c98: str   xzr, [sp, #336]         f7c: adrp  x0, 0x20000                 *)
(* c9c: add   x4, x0, #0x4            f80: mov   w2, #0x120                  *)
(* ca0: cmp   x4, x5                  f84: add   x0, x0, #0x40               *)
(* ca4: b.hi  0x1034                  f88: str   q0, [sp, #1744]             *)
(* ca8: ldr   x3, [sp, #312]          f8c: str   q0, [sp, #1760]             *)
(* cac: add   x2, x0, #0x1            f90: str   q0, [sp, #1776]             *)
(* cb0: str   x2, [sp, #328]          f94: str   q1, [sp, #1792]             *)
(* cb4: add   x1, x0, #0x2            f98: bl    0x6a0 (construct)           *)
(* cb8: add   x6, x0, #0x3            f9c: add   x1, x10, #0x3c              *)
(* cbc: ldrb  w7, [x3, x0]            fa0: mov   w0, #0x5                    *)
(* cc0: str   x1, [sp, #328]          fa4: nop                               *)
(* cc4: ldrb  w2, [x3, x2]            fa8: strh  w0, [x10], #2               *)
(* cc8: str   x6, [sp, #328]          fac: cmp   x10, x1                     *)
(* ccc: orr   w2, w7, w2, lsl #8      fb0: b.ne  0xfa8                       *)
(* cd0: ldrb  w7, [x3, x1]            fb4: adrp  x0, 0x20000                 *)
(* cd4: mvn   w1, w2                  fb8: add   x0, x0, #0x40               *)
(* cd8: cmp   w7, w1, uxtb            fbc: add   x0, x0, #0x270              *)
(* cdc: b.ne  0x1058                  fc0: add   x1, sp, #0x4d0              *)
(* ce0: str   x4, [sp, #328]          fc4: mov   w2, #0x1e                   *)
(* ce4: ubfx  x1, x1, #8, #8          fc8: bl    0x6a0 (construct)           *)
(* ce8: ldrb  w6, [x3, x6]            fcc: ldr   x0, [sp, #96]               *)
(* cec: cmp   w6, w1                  fd0: str   wzr, [x0]                   *)
(* cf0: b.ne  0x1058                  fd4: adrp  x1, 0x20000                 *)
(* cf4: add   x6, x4, w2, uxth        fd8: add   x1, x1, #0x40               *)
(* cf8: mov   w1, w2                  fdc: add   x2, x1, #0x270              *)
(* cfc: cmp   x5, x6                  fe0: add   x0, sp, #0x120              *)
(* d00: b.cc  0x1034                  fe4: bl    0x900 (codes)               *)
(* d04: ldr   x7, [sp, #288]          fe8: cmp   w0, #0x0                    *)
(* d08: ldr   x5, [sp, #304]          fec: cbz   w0, 0xd78                   *)
(* d0c: add   x1, x1, x5              ff0: b.gt  0xc74                       *)
(* d10: cbz   x7, 0xff8               ff4: b     0xc5c                       *)
(* d14: ldr   x6, [sp, #296]          ff8: str   x1, [sp, #304]              *)
(* d18: cmp   x6, x1                  ffc: str   x6, [sp, #328]              *)
(* d1c: b.cc  0x1010                  1000: cbz   w20, 0xb48                 *)
(* d20: cbz   w2, 0xd78               1004: b     0xd7c                      *)
(* d24: add   x1, x0, #0x5            1008: ldr   w0, [sp, #108]             *)
(* d28: add   x0, x5, #0x1            100c: b     0xc1c                      *)
(* d2c: str   x0, [sp, #304]          1010: ldp   x29, x30, [sp]             *)
(* d30: sub   w0, w2, #0x2            1014: mov   w0, #0x1                   *)
(* d34: str   x1, [sp, #328]          1018: ldp   x19, x20, [sp, #16]        *)
(* d38: ldrb  w1, [x3, x4]            101c: ldp   x21, x22, [sp, #32]        *)
(* d3c: strb  w1, [x7, x5]            1020: ldp   x23, x24, [sp, #48]        *)
(* d40: cmp   w2, #0x1                1024: ldp   x25, x26, [sp, #64]        *)
(* d44: b.eq  0xd78                   1028: ldp   x27, x28, [sp, #80]        *)
(* d48: ldp   x1, x4, [sp, #304]      102c: add   sp, sp, #0x990             *)
(* d4c: sub   w0, w0, #0x1            1030: ret                              *)
(* d50: ldr   x2, [sp, #328]          1034: ldp   x29, x30, [sp]             *)
(* d54: ldr   x3, [sp, #288]          1038: mov   w0, #0x2                   *)
(* d58: add   x5, x2, #0x1            103c: ldp   x19, x20, [sp, #16]        *)
(* d5c: add   x6, x1, #0x1            1040: ldp   x21, x22, [sp, #32]        *)
(* d60: str   x6, [sp, #304]          1044: ldp   x23, x24, [sp, #48]        *)
(* d64: str   x5, [sp, #328]          1048: ldp   x25, x26, [sp, #64]        *)
(* d68: ldrb  w2, [x4, x2]            104c: ldp   x27, x28, [sp, #80]        *)
(* d6c: strb  w2, [x3, x1]            1050: add   sp, sp, #0x990             *)
(* d70: cmn   w0, #0x1                1054: ret                              *)
(* d74: b.ne  0xd48                   1058: mov   w0, #0xfffffffe            *)
(* d78: cbz   w20, 0xb48              105c: b     0xc5c                      *)
(* d7c: ldr   w0, [sp, #108]          1060: mov   w0, #0xffffffff            *)
(* d80: b     0xc5c                   1064: str   w0, [sp, #108]             *)
(* d84: add   w21, w25, w26           1068: ldr   w0, [sp, #108]             *)
(* d88: add   x22, sp, #0x120         106c: b     0xc5c                      *)
(* d8c: mov   w28, #0x0               1070: mov   w0, #0xfffffffb            *)
(* d90: mov   w27, #0x0               1074: b     0xfe8                      *)
(* d94: cmp   w21, #0x0               1078: mov   w0, #0xfffffffd            *)
(* d98: b.gt  0xdb0                   107c: b     0xc5c                      *)
(* d9c: b     0xe30                   1080: mov   w0, #0xfffffff8            *)
(* da0: strh  w0, [x23, w28, sxtw #1] 1084: b     0xc5c                      *)
(* da4: add   w28, w28, #0x1          1088: mov   w0, #0xfffffff9            *)
(* da8: cmp   w28, w21                108c: b     0xc5c                      *)
(* dac: b.ge  0xe30                   1090: mov   w0, #0xfffffff7            *)
(* db0: mov   x1, x24                                                        *)
(* ========================================================================= *)

needs "arm/proofs/puff_construct_gcc12_O2.ml";;
needs "arm/proofs/puff_codes_gcc12_O2.ml";;


(* ------------------------------------------------------------------------- *)
(* The tables of the fixed codes, which puff builds in the data of the image *)
(* when it decodes the first block with the fixed codes, and the flag virgin *)
(* that says so. The invariant is that when virgin is 0, the tables,         *)
(* whatever the values in memory are, are those of the fixed codes.          *)
(* ------------------------------------------------------------------------- *)

let puff_fixed_tables = new_definition
 `puff_fixed_tables pc (s:armstate) <=>
    ?vflag lc ls dc ds lcv lsv dcv dsv.
      read (memory :> bytes32(word_add (word pc) (word 0x20028))) s = vflag /\
      read (memory :> bytes64(word_add (word pc) (word 0x20040))) s = lc /\
      read (memory :> bytes64(word_add (word pc) (word 0x20048))) s = ls /\
      read (memory :> bytes(word_add (word pc) (word 0x20050),32)) s = lcv /\
      read (memory :> bytes(word_add (word pc) (word 0x20070),576)) s = lsv /\
      read (memory :> bytes64(word_add (word pc) (word 0x202b0))) s = dc /\
      read (memory :> bytes64(word_add (word pc) (word 0x202b8))) s = ds /\
      read (memory :> bytes(word_add (word pc) (word 0x202c0),32)) s = dcv /\
      read (memory :> bytes(word_add (word pc) (word 0x202e0),60)) s = dsv /\
      (vflag = word 0
       ==> ?lcnts lsyms dcnts dsyms.
             lc = word_add (word pc) (word 0x20050) /\
             ls = word_add (word pc) (word 0x20070) /\
             dc = word_add (word pc) (word 0x202c0) /\
             ds = word_add (word pc) (word 0x202e0) /\
             lcv = num_of_wordlist lcnts /\ lsv = num_of_wordlist lsyms /\
             dcv = num_of_wordlist dcnts /\ dsv = num_of_wordlist dsyms /\
             LENGTH lsyms = 288 /\ LENGTH dsyms = 30 /\
             huffman_table deflate_fixed_ll lcnts lsyms /\
             huffman_table (REPLICATE 30 5) dcnts dsyms)`;;

let FIXED_TABLES_INTRO_TAC =
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV
    (REWRITE_CONV[puff_fixed_tables])))) THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
   [`vflag:int32`; `lc:int64`; `ls:int64`; `dc:int64`; `ds:int64`;
    `lcv:num`; `lsv:num`; `dcv:num`; `dsv:num`] THEN
  GLOBALIZE_PRECONDITION_TAC;;

let FIXED_TABLES_KEEP_TAC =
  REWRITE_TAC[puff_fixed_tables] THEN
  MAP_EVERY EXISTS_TAC
   [`vflag:int32`; `lc:int64`; `ls:int64`; `dc:int64`; `ds:int64`;
    `lcv:num`; `lsv:num`; `dcv:num`; `dsv:num`] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The frame of puff, with the context that setjmp saves in s.env, and the   *)
(* invariant puff_inv n of the loop over the blocks, at 0xb48, for n bits    *)
(* left after the blocks decoded so far.                                     *)
(* ------------------------------------------------------------------------- *)

let puff_sctx = `[ctx_x19:int64; ctx_x20; ctx_x21; ctx_x22; ctx_x23; ctx_x24;
  ctx_x25; ctx_x26; ctx_x27; ctx_x28; word_sub stackpointer (word 2448);
  word (pc + 2852); word_sub stackpointer (word 2448); ctx_d8; ctx_d9;
  ctx_d10; ctx_d11; ctx_d12; ctx_d13; ctx_d14; ctx_d15]`;;

let puff_inv = subst [puff_sctx,`sctx:int64 list`] `\n s.
  ?outk pk.
   aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
   read PC s = word(pc + 0xb48) /\
   read SP s = word_sub stackpointer (word 2448) /\
   read X29 s = word_sub stackpointer (word 2448) /\
   read X19 s = word_add (word pc) (word 4528) /\
   read (Q8 :> bottomhalf) s = ctx_d8 /\ read (Q9 :> bottomhalf) s = ctx_d9 /\
   read (Q10 :> bottomhalf) s = ctx_d10 /\
   read (Q11 :> bottomhalf) s = ctx_d11 /\
   read (Q12 :> bottomhalf) s = ctx_d12 /\
   read (Q13 :> bottomhalf) s = ctx_d13 /\
   read (Q14 :> bottomhalf) s = ctx_d14 /\
   read (Q15 :> bottomhalf) s = ctx_d15 /\
   read (memory :> bytes64(word_sub stackpointer (word 2448))) s = ctx_x29 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 8))) s = returnaddress /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 16))) s = ctx_x19 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 24))) s = ctx_x20 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 32))) s = ctx_x21 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 40))) s = ctx_x22 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 48))) s = ctx_x23 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 56))) s = ctx_x24 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 64))) s = ctx_x25 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 72))) s = ctx_x26 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 80))) s = ctx_x27 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 88))) s = ctx_x28 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 96))) s =
   word_add (word pc) (word 131112) /\
   read (memory :> bytes32(word_add (word_sub stackpointer (word 2448))
                                    (word 108))) s = word 0 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 112))) s = destlen /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 120))) s = sourcelen /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 288))) s = dest /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 296))) s = word outlen /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 304))) s = word(LENGTH outk) /\
   read (memory :> bytes(dest,LENGTH outk)) s = num_of_bytelist outk /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 312))) s = source /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 320))) s = word(LENGTH l) /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 328))) s = word((pk + 7) DIV 8) /\
   read (memory :> bytes32(word_add (word_sub stackpointer (word 2448))
                                    (word 336))) s =
   word(deflate_bits l pk (8 * ((pk + 7) DIV 8) - pk)) /\
   read (memory :> bytes32(word_add (word_sub stackpointer (word 2448))
                                    (word 340))) s =
   word(8 * ((pk + 7) DIV 8) - pk) /\
   read (memory :> bytes(source,LENGTH l)) s = num_of_bytelist l /\
   read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                  (word 344),312)) s =
   (enc:int64 list->num) sctx /\
   read (memory :> bytes64(word_add (word pc) (word 131072))) s = fs /\
   read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
   read (memory :> bytes(ea,el)) s = ev /\
   puff_fixed_tables pc s /\
   pk <= 8 * LENGTH l /\ n = 8 * LENGTH l - pk /\ LENGTH outk <= outlen /\
   (!r. deflate_blocks l ([],0) r <=> deflate_blocks l (outk,pk) r)`;;

let puff_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE_JMP_CONTEXT ,,
  MAYCHANGE [memory :> bytes(word_sub stackpointer (word 2448),2448);
             memory :> bytes(word_sub stackpointer (word 2464),16);
             memory :> bytes(word_sub stackpointer (word 2480),32);
             memory :> bytes(word_sub stackpointer (word 2544),96);
             memory :> bytes(word_sub stackpointer (word 2560),16);
             memory :> bytes(dest,outlen);
             memory :> bytes(destlen,8); memory :> bytes(sourcelen,8);
             memory :> bytes(word_add (word pc) (word 131112),4);
             memory :> bytes(word_add (word pc) (word 131136),732)]`;;

let PUFF_FRAME_TAC =
  REWRITE_TAC(map (fun k -> WORD_RULE (subst [mk_small_numeral k,`k:num`;
      mk_small_numeral (2560 - k),`d:num`]
     `word_sub (stackpointer:int64) (word k) =
      word_add (word_sub stackpointer (word 2560)) (word d)`))
    [2448; 2464; 2480; 2544]) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE_JMP_CONTEXT;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC;;

let PUFF_SETJMP_TAC env n =
  JMP_VALUES_GHOST_TAC THEN
  W(fun (asl,w as gl) ->
    let ctx = jmp_values gl in
    let s = rand w in
    let ret = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
      is_eq t && lhs t = list_mk_icomb "read" [`X30`; s]) asl))) in
    FIRST_ASSUM(fun th ->
      match strip_comb(concl th) with
        Const("setjmp_contract",_),[_;_;_;_;_] ->
          MP_TAC(SPECL [env; ret; ctx] (REWRITE_RULE[setjmp_contract] th))
      | _ -> NO_TAC)) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; jmp_context; CONS_11;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC PUFF_EXEC ("s"^string_of_int n) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC);;

(* From the entry to the loop over the blocks, through the call of setjmp.   *)

let PUFF_ENTRY_TAC =
  FIXED_TABLES_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--22) THEN PUFF_ADRP_TAC THEN
  PUFF_STEPS_TAC (23--25) THEN
  PUFF_SETJMP_TAC
   `word_add (word_sub stackpointer (word 2448)) (word 344):int64` 26 THEN
  PUFF_STEPS_TAC (27--29) THEN PUFF_ADRP_TAC THEN PUFF_STEPS_TAC (30--32) THEN
  PUFF_ADRP_TAC THEN PUFF_STEPS_TAC (33--35) THEN
  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] o
    check (fun th -> is_eq(concl th) && lhs(concl th) =
      `read (memory :> bytes64 (word_add (word_sub stackpointer (word 2448))
                                         (word 336))) s35`)) THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `8 * LENGTH(l:byte list)` THEN BETA_TAC THEN
  MAP_EVERY EXISTS_TAC [`[]:byte list`; `0`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[LENGTH; num_of_bytelist; READ_COMPONENT_COMPOSE;
                  READ_BYTES_TRIVIAL; deflate_bits; LE_0; SUB_0] THEN
  FIXED_TABLES_KEEP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The header of a block, from 0xb48 to the dispatch on the block type at    *)
(* 0xb68 (puff_dispatch), and the end of a block, at 0xd78 (puff_blockend).  *)
(* ------------------------------------------------------------------------- *)

let puff_state =
  let cjs = conjuncts(snd(strip_exists(body(body puff_inv)))) in
  let drop t =
    t = `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc` ||
    (is_eq t && (lhs t = `read PC s` || lhs t = `n:num`)) || is_forall t in
  list_mk_conj(filter (not o drop) cjs);;

let puff_dispatch = mk_abs(`s:armstate`,
  list_mk_exists([`last:num`; `btype:num`],
   list_mk_conj
    [`last < 2 /\ btype < 4 /\ pk + 3 <= 8 * LENGTH(l:byte list) /\
      (deflate_bit l pk <=> last = 1) /\ deflate_bits l (pk + 1) 2 = btype`;
     `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
     `read PC s = word(pc + 2920)`;
     `read X0 s = word btype /\ read X20 s = word last /\
      read X21 s = word_add (word_sub stackpointer (word 2448)) (word 288)`;
     subst [`pk + 3`,`pk:num`] puff_state]));;

(*** PUFF_CALL_TAC for arguments that are offsets from the frame of puff ***)

let PUFF_FRAME_CALL_TAC th vars n =
  JMP_VALUES_GHOST_TAC THEN
  W(fun gl ->
    let ctx0 = jmp_values gl in
    let vars' = map (fun v -> if v = `ctx0:int64 list` then ctx0 else v)
                    vars in
    MP_TAC(ISPECL vars' th)) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; puff_input; puff_table; jmp_context; CONS_11;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE_JMP_CONTEXT;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ARM_BIGSTEP_TAC PUFF_EXEC ("s"^string_of_int n) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC);;

let PUFF_BITS_VARS need p ret =
  [`word_add (word_sub stackpointer (word 2448)) (word 288):int64`; need;
   `l:byte list`; `source:int64`; p; `fl:int64`; `ea:int64`;
   `el:num`; `ev:num`; `enc:int64 list->num`; puff_sctx;
   `ctx0:int64 list`; `pc:num`; ret;
   `word_sub stackpointer (word 2448):int64`];;

let PUFF_ITER_INTRO_TAC =
  X_GEN_TAC `n:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `outk:byte list` THEN
  ENSURES_EXISTS_PRE_TAC `pk:num` THEN
  GLOBALIZE_PRECONDITION_TAC;;

let PUFF_SP_RESTORE = WORD_RULE
  `word_add (word_sub (x:int64) (word 2448)) (word 2448) = x`;;

(*** A longjmp back to the setjmp of puff, after the call at step n, then  ***)
(*** the return of 2; sel selects the disjunct for the return, and tac     ***)
(*** proves that there is no decoding                                      ***)

let PUFF_ESCAPE_TAC sel n tac =
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV EL_CONV)) THEN
  PUFF_STEPS_TAC ((n+1)--(n+11)) THEN ENSURES_FINAL_STATE_TAC THEN sel THEN
  REWRITE_TAC[jmp_context; CONS_11] THEN ASM_REWRITE_TAC[PUFF_SP_RESTORE] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [FIXED_TABLES_KEEP_TAC; tac];;

(*** No decoding, when the stream ends before the block header ***)

let NO_HEADER_TAC =
  REWRITE_TAC[deflate_decode] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DEFLATE_BLOCKS_STEP] THEN STRIP_TAC THEN
  SIMPLE_ARITH_TAC;;

let PUFF_HEADER_TAC =
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  PUFF_STEPS_TAC (1--4) THEN
  PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
   (PUFF_BITS_VARS `1` `pk:num` `word(pc + 2904):int64`) 5 THENL
   [ALL_TAC; PUFF_ESCAPE_TAC (DISJ2_TAC THEN DISJ2_TAC) 5 NO_HEADER_TAC] THEN
  SUBGOAL_THEN `deflate_bits l pk 1 < 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; `pk:num`; `1`] DEFLATE_BITS_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  PUFF_STEPS_TAC (6--9) THEN
  PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
   (PUFF_BITS_VARS `2` `pk + 1` `word(pc + 2920):int64`) 10 THENL
   [ALL_TAC; PUFF_ESCAPE_TAC (DISJ2_TAC THEN DISJ2_TAC) 10 NO_HEADER_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(pk + 1) + 2 = pk + 3`]) THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`deflate_bits l pk 1`; `deflate_bits l (pk + 1) 2`] THEN
  ASM_REWRITE_TAC[DEFLATE_BITS_1] THEN
  REWRITE_TAC[GSYM DEFLATE_BITS_1] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; `pk + 1`; `2`] DEFLATE_BITS_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[DEFLATE_BITS_1] THEN BOOL_CASES_TAC `deflate_bit l pk` THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC;
    FIXED_TABLES_KEEP_TAC];;

let PUFF_RETURN_TAC sel steps tac =
  PUFF_STEPS_TAC steps THEN ENSURES_FINAL_STATE_TAC THEN sel THEN
  REWRITE_TAC[jmp_context; CONS_11] THEN ASM_REWRITE_TAC[PUFF_SP_RESTORE] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [FIXED_TABLES_KEEP_TAC; tac];;

let NO_BLOCK_TAC =
  REWRITE_TAC[deflate_decode] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DEFLATE_BLOCKS_STEP] THEN
  ASM_REWRITE_TAC[deflate_block; ARITH_EQ];;

let puff_blockend = mk_abs(`s:armstate`,
  list_mk_exists([`outk':byte list`; `pk':num`],
   list_mk_conj
    [`pk < pk' /\ pk' <= 8 * LENGTH(l:byte list) /\
      LENGTH(outk':byte list) <= outlen /\
      (last = 1
       ==> !r. deflate_blocks l (outk,pk) r <=> r = (outk',pk')) /\
      (last = 0
       ==> !r. deflate_blocks l (outk,pk) r <=>
               deflate_blocks l (outk',pk') r)`;
     `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
     `read PC s = word(pc + 0xd78)`;
     `read X20 s = word last`;
     subst [`outk':byte list`,`outk:byte list`; `pk':num`,`pk:num`]
           puff_state]));;

let PUFF_BLOCKEND_TAC =
  ENSURES_EXISTS_PRE_TAC `outk':byte list` THEN
  ENSURES_EXISTS_PRE_TAC `pk':num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN FIXED_TABLES_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ASM_CASES_TAC `last = 0` THENL
   [PUFF_STEPS_TAC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `last = 0`; ARITH_EQ]) THEN
    ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `8 * LENGTH(l:byte list) - pk'` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`outk':byte list`; `pk':num`] THEN
    ASM_REWRITE_TAC[] THEN FIXED_TABLES_KEEP_TAC;
    SUBGOAL_THEN `last = 1` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
    PUFF_STEPS_TAC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN DISJ2_TAC THEN
    REWRITE_TAC[jmp_context; CONS_11] THEN
    ASM_REWRITE_TAC[PUFF_SP_RESTORE] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [FIXED_TABLES_KEEP_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`outk':byte list`; `(pk' + 7) DIV 8`] THEN
    ASM_REWRITE_TAC[deflate_decode] THEN EXISTS_TAC `pk':num` THEN
    ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Stored blocks, from 0xc94: the length LEN and its complement NLEN, then   *)
(* the copy of LEN bytes, through the point stored_mid before the copy.      *)
(* ------------------------------------------------------------------------- *)

let STORED_NLEN_LO = prove
 (`!b:byte len.
     len < 65536
     ==> (val(word_sub (word_zx (word (val b):int64):int32)
                       (word_zx(word_zx(word_zx(word_zx
                         (word_not(word len:int32)):int64):int32):byte):int32))
          = 0 <=>
          val b = (65535 - len) MOD 256)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_NOT;
              DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `x < 256 ==> x < 4294967296 /\ x < 18446744073709551616`;
   ARITH_RULE `len < 65536 ==> len < 4294967296`;
   ARITH_RULE `4294967295 - len < 4294967296 /\
               4294967295 - len < 18446744073709551616`] THEN
  SUBGOAL_THEN `4294967295 - len = 16776960 * 256 + (65535 - len)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]] THEN
  SIMP_TAC[MOD_LT; MOD_MOD_REFL; ARITH_RULE `x MOD 256 < 4294967296`;
           MOD_LT_EQ; ARITH_EQ] THEN
  MP_TAC(SPECL [`65535 - len`; `256`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ARITH_RULE
   `x < 256 ==> x < 4294967296`]);;

let STORED_NLEN_HI = prove
 (`!b:byte len.
     len < 65536
     ==> (val(word_sub (word_zx (word (val b):int64):int32)
                       (word_zx(word_subword(word_zx
                         (word_not(word len:int32)):int64) (8,8):int64):int32))
          = 0 <=>
          val b = (65535 - len) DIV 256)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_NOT;
              VAL_WORD_SUBWORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `x < 256 ==> x < 4294967296 /\ x < 18446744073709551616`;
   ARITH_RULE `len < 65536 ==> len < 4294967296`;
   ARITH_RULE `4294967295 - len < 4294967296 /\
               4294967295 - len < 18446744073709551616`] THEN
  SUBGOAL_THEN `4294967295 - len = (16776960 + (65535 - len) DIV 256) * 256 +
                                   (65535 - len) MOD 256`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`65535 - len`; `256`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_LT_EQ; ARITH_EQ; DIV_LT; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `16776960 = 65535 * 256`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] MOD_MULT_ADD] THEN
  SUBGOAL_THEN `(65535 - len) DIV 256 < 256` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 256 ==> x < 4294967296`]);;

let BYTES2_EQ = prove
 (`!a b n. a < 256 ==> (a + 256 * b = n <=> a = n MOD 256 /\ b = n DIV 256)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[DIVMOD_ADD_MULT];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN ARITH_TAC]);;

let VAL_BOUND_BYTE = prove
 (`!b:byte. val b < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let NO_STORED_TAC =
  REWRITE_TAC[deflate_decode] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DEFLATE_BLOCKS_STEP] THEN
  ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk + 3`; `k:num`]
               DEFLATE_STORED_BYTES_ALT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  SIMP_TAC[BYTES2_EQ; VAL_BOUND_BYTE] THEN
  ASM_REWRITE_TAC[] THEN TRY SIMPLE_ARITH_TAC;;

let NO_STORED_FIT_TAC =
  REWRITE_TAC[deflate_decode; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`out:byte list`; `m:num`] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DEFLATE_BLOCKS_STEP] THEN
  ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk + 3`; `k:num`]
               DEFLATE_STORED_BYTES_ALT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN SUBST_VARS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_THEN(SUBST_ALL_TAC o CONJUNCT1) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH_LIST_OF_SEQ]);
    DISCH_THEN(MP_TAC o MATCH_MP DEFLATE_BLOCKS_LENGTH) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ]] THEN
  SIMPLE_ARITH_TAC;;

(*** The frame without the position in the stream and the output ***)

let puff_frame_state =
  let drop t = free_in `outk:byte list` t || free_in `pk:num` t in
  list_mk_conj(filter (not o drop) (conjuncts puff_state));;

(*** In the copy loop of a stored block at 0xd48, with i + 1 of the len    ***)
(*** bytes from byte k + 4 of the input copied                             ***)

let stored_copy_state = list_mk_conj
 [`(i < len - 1 ==> read X0 s = word(len - 2 - i)) /\
   read X20 s = word last /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 304))) s =
   word(LENGTH(outk:byte list) + i + 1) /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 328))) s = word(k + 4 + i + 1) /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                    (word 336))) s = word 0 /\
   read (memory :> bytes(dest,LENGTH outk + i + 1)) s =
   num_of_bytelist(APPEND outk (list_of_seq (\j. EL (k + 4 + j) l) (i + 1)))`;
  puff_frame_state];;

let stored_copy = mk_abs(`i:num`,mk_abs(`s:armstate`,
  mk_conj(stored_copy_state,`read ZF s <=> i = len - 1`)));;

(*** The end of a stored block at 0xd78, after len bytes are copied ***)

let STORED_END_TAC sel len =
  let outk' = subst [len,`len:num`]
    `APPEND outk (list_of_seq (\j. EL (k + 4 + j) l) len):byte list`
  and pk' = subst [len,`len:num`] `8 * (k + 4 + len)` in
  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] o
    check (fun th -> is_eq(concl th) &&
      can (term_match [] `read (memory :> bytes64 (word_add
             (word_sub stackpointer (word 2448)) (word 336))) s`)
          (lhs(concl th)))) THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; outk'; pk';
                `last:num`; `0`] DEFLATE_BLOCKS_AFTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
    MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk + 3`; `k:num`]
                 DEFLATE_STORED_BYTES_ALT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
    STRIP_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN sel THEN
  MAP_EVERY EXISTS_TAC [outk'; pk'] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ; LIST_OF_SEQ_1;
                  CONJUNCT1 list_of_seq; APPEND_NIL] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[ARITH_RULE `(8 * n + 7) DIV 8 = n`; SUB_REFL; deflate_bits;
              ARITH_RULE `8 * n - 8 * n = 0`; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN FIXED_TABLES_KEEP_TAC;;

let stored_mid = mk_abs(`s:armstate`,
  mk_exists(`len:num`,
   list_mk_conj
    [`2 <= len /\ len < 65536 /\
      val(EL k l:byte) + 256 * val(EL (k + 1) l:byte) = len /\
      val(EL (k + 2) l:byte) + 256 * val(EL (k + 3) l:byte) = 65535 - len /\
      k + 4 + len <= LENGTH(l:byte list) /\
      LENGTH(outk:byte list) + len <= outlen`;
     `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
     `read PC s = word(pc + 0xd48)`;
     rhs(concl((REWRITE_CONV[ADD_CLAUSES; SUB_0; ARITH_RULE `0 + 1 = 1`] THENC
                NUM_REDUCE_CONV)
                (subst [`0`,`i:num`] stored_copy_state)))]));;

let STORED_HEAD_TAC =
  let sel3 = DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC
  and sel2 = DISJ2_TAC THEN DISJ1_TAC in
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  PUFF_STEPS_TAC (1--5) THEN
  ASM_CASES_TAC `k + 4 <= LENGTH(l:byte list)` THEN PUFF_STEPS_TAC [6] THENL
   [ALL_TAC; PUFF_RETURN_TAC sel3 (7--15) NO_STORED_TAC] THEN
  MAP_EVERY (fun i ->
    MP_TAC(ISPECL [`source:int64`; `l:byte list`; i; `s6:armstate`]
                  READ_MEMORY_BYTES8_BYTELIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC])
   [`k:num`; `k + 1`; `k + 2`; `k + 3`] THEN
  PUFF_STEPS_TAC (7--19) THEN
  SUBGOAL_THEN `val(EL k l:byte) + 256 * val(EL (k + 1) l:byte) < 65536`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `EL k l:byte` VAL_BOUND_BYTE) THEN
    MP_TAC(ISPEC `EL (k + 1) l:byte` VAL_BOUND_BYTE) THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = `val(EL k l:byte) + 256 * val(EL (k + 1) l:byte) < 65536`
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP STORED_NLEN_LO th])
    else failwith "") THEN
  ASM_CASES_TAC
   `val(EL (k + 2) l:byte) =
    (65535 - (val(EL k l:byte) + 256 * val(EL (k + 1) l:byte))) MOD 256` THEN
  PUFF_STEPS_TAC [20] THENL
   [ALL_TAC; PUFF_RETURN_TAC sel3 (21--36) NO_STORED_TAC] THEN
  PUFF_STEPS_TAC (21--24) THEN
  FIRST_ASSUM(fun th ->
    if concl th = `val(EL k l:byte) + 256 * val(EL (k + 1) l:byte) < 65536`
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP STORED_NLEN_HI th])
    else failwith "") THEN
  ASM_CASES_TAC
   `val(EL (k + 3) l:byte) =
    (65535 - (val(EL k l:byte) + 256 * val(EL (k + 1) l:byte))) DIV 256` THEN
  PUFF_STEPS_TAC [25] THENL
   [ALL_TAC; PUFF_RETURN_TAC sel3 (26--41) NO_STORED_TAC] THEN
  SUBGOAL_THEN `val(EL (k + 2) l:byte) + 256 * val(EL (k + 3) l:byte) =
                65535 - (val(EL k l:byte) + 256 * val(EL (k + 1) l:byte))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[BYTES2_EQ; VAL_BOUND_BYTE]; ALL_TAC] THEN
  ABBREV_TAC `len = val(EL k l:byte) + 256 * val(EL (k + 1) l:byte)` THEN
  PUFF_STEPS_TAC (26--28) THEN
  ASM_CASES_TAC `k + 4 + len <= LENGTH(l:byte list)` THEN
  PUFF_STEPS_TAC [29] THENL
   [ALL_TAC; PUFF_RETURN_TAC sel3 (30--38) NO_STORED_TAC] THEN
  PUFF_STEPS_TAC (30--35) THEN
  ASM_CASES_TAC `LENGTH(outk:byte list) + len <= outlen` THEN
  PUFF_STEPS_TAC [36] THENL
   [ALL_TAC; PUFF_RETURN_TAC sel3 (37--45) NO_STORED_FIT_TAC] THEN
  ASM_CASES_TAC `len = 0` THENL
   [PUFF_STEPS_TAC [37] THEN STORED_END_TAC sel2 `0`; ALL_TAC] THEN
  PUFF_STEPS_TAC (37--42) THEN
  MP_TAC(ISPECL [`source:int64`; `l:byte list`; `k + 4`; `s42:armstate`]
                READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  PUFF_STEPS_TAC (43--44) THEN
  MP_TAC(ISPECL [`dest:int64`; `outk:byte list`; `EL (k + 4) l:byte`;
                 `s44:armstate`] READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN
  ASM_CASES_TAC `len = 1` THEN PUFF_STEPS_TAC (45--46) THENL
   [STORED_END_TAC sel2 `1`; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN EXISTS_TAC `len:num` THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ_1; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;
    MP_TAC(SPECL [`65535 - len`; `256`] DIVISION) THEN ARITH_TAC;
    FIXED_TABLES_KEEP_TAC];;

let STORED_COPY_TAC =
  ENSURES_EXISTS_PRE_TAC `len:num` THEN GLOBALIZE_PRECONDITION_TAC THEN
  SUBGOAL_THEN `~(len - 1 = 0)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `len - 1` `pc + 0xd48` `pc + 0xd74` stored_copy THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SIMP_TAC[];
      SUBSUMED_ID_MAYCHANGE_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(ASSUME_TAC o C MP (ASSUME `i < len - 1`)) THEN
    MP_TAC(ISPECL [`source:int64`; `l:byte list`; `k + 4 + i + 1`;
                   `s0:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    PUFF_STEPS_TAC (1--11) THEN
    MP_TAC(ISPECL [`dest:int64`;
      `APPEND outk (list_of_seq (\j. EL (k + 4 + j) l) (i + 1)):byte list`;
      `EL (k + 4 + i + 1) l:byte`; `s11:armstate`]
      READ_MEMORY_BYTELIST_SNOC) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN
    ASM_REWRITE_TAC[WORD_VAL] THEN
    SUBGOAL_THEN
     `APPEND (APPEND outk (list_of_seq (\j. EL (k + 4 + j) l) (i + 1)))
             [EL (k + 4 + i + 1) l] =
      APPEND outk (list_of_seq (\j. EL (k + 4 + j) l) ((i + 1) + 1)):byte list`
    SUBST1_TAC THENL
     [REWRITE_TAC[LIST_OF_SEQ_SNOC; GSYM APPEND_ASSOC]; DISCH_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[ARITH_RULE
     `LENGTH(outk:byte list) + (i + 1) + 1 = (LENGTH outk + i + 1) + 1`;
     ARITH_RULE `k + 4 + (i + 1) + 1 = (k + 4 + i + 1) + 1`] THEN
    ASM_REWRITE_TAC[WORD_ZX_ZX_32_64] THEN
    REWRITE_TAC[WORD_RULE `word_add (word_sub (x:int32) y) y = x`] THEN
    REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      FIXED_TABLES_KEEP_TAC;
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      SIMPLE_ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(ASSUME_TAC o C MP (ASSUME `i < len - 1`)) THEN
    PUFF_STEPS_TAC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIXED_TABLES_KEEP_TAC;
    SUBGOAL_THEN `(len - 1) + 1 = len` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
    PUFF_STEPS_TAC [1] THEN STORED_END_TAC DISJ1_TAC `len:num`];;

let STORED_TAC =
  ABBREV_TAC `k = ((pk + 3) + 7) DIV 8` THEN
  SUBGOAL_THEN `k <= LENGTH(l:byte list)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(val(dest:int64) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC stored_mid THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    STORED_HEAD_TAC; STORED_COPY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Blocks with the fixed codes, from 0xf00: the tables, built if virgin is   *)
(* not 0, then the call of codes at 0xfe4, through the point fixed_ready at  *)
(* 0xfd4.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** The fixed tables, built ***)

let fixed_tables_state = `
  read (memory :> bytes32(word_add (word pc) (word 131112))) s = word 0 /\
  read (memory :> bytes64(word_add (word pc) (word 131136))) s =
  word_add (word pc) (word 131152) /\
  read (memory :> bytes64(word_add (word pc) (word 131144))) s =
  word_add (word pc) (word 131184) /\
  read (memory :> bytes(word_add (word pc) (word 131152),32)) s =
  num_of_wordlist(lcnts:int16 list) /\
  read (memory :> bytes(word_add (word pc) (word 131184),576)) s =
  num_of_wordlist(lsyms:int16 list) /\
  read (memory :> bytes64(word_add (word pc) (word 131760))) s =
  word_add (word pc) (word 131776) /\
  read (memory :> bytes64(word_add (word pc) (word 131768))) s =
  word_add (word pc) (word 131808) /\
  read (memory :> bytes(word_add (word pc) (word 131776),32)) s =
  num_of_wordlist(dcnts:int16 list) /\
  read (memory :> bytes(word_add (word pc) (word 131808),60)) s =
  num_of_wordlist(dsyms:int16 list)`;;

(*** At 0xfd4 in a fixed block, with the tables ready ***)

let fixed_ready = mk_abs(`s:armstate`,
  list_mk_exists([`lcnts:int16 list`; `lsyms:int16 list`;
                  `dcnts:int16 list`; `dsyms:int16 list`],
   list_mk_conj
    [`huffman_table deflate_fixed_ll lcnts lsyms /\ LENGTH lsyms = 288 /\
      huffman_table (REPLICATE 30 5) dcnts dsyms /\ LENGTH dsyms = 30`;
     `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
     `read PC s = word(pc + 0xfd4)`;
     `read X20 s = word last`;
     fixed_tables_state;
     let drop t = can (find_term (fun u -> try fst(dest_const u) =
                        "puff_fixed_tables" with _ -> false)) t in
     list_mk_conj(filter (not o drop)
       (conjuncts(subst [`pk + 3`,`pk:num`] puff_state)))]));;

(*** From the tables in puff_fixed_tables, when the flag is 0 ***)

let FIXED_TABLES_VALID_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `vflag:int32 = word 0`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lcnts:int16 list` (X_CHOOSE_THEN
    `lsyms:int16 list` (X_CHOOSE_THEN `dcnts:int16 list` (X_CHOOSE_THEN
    `dsyms:int16 list` STRIP_ASSUME_TAC)))) THEN
  SUBST_ALL_TAC(ASSUME `lc = word_add (word pc) (word 131152):int64`) THEN
  SUBST_ALL_TAC(ASSUME `ls = word_add (word pc) (word 131184):int64`) THEN
  SUBST_ALL_TAC(ASSUME `dc = word_add (word pc) (word 131776):int64`) THEN
  SUBST_ALL_TAC(ASSUME `ds = word_add (word pc) (word 131808):int64`) THEN
  SUBST_ALL_TAC(ASSUME `lcv = num_of_wordlist(lcnts:int16 list)`) THEN
  SUBST_ALL_TAC(ASSUME `lsv = num_of_wordlist(lsyms:int16 list)`) THEN
  SUBST_ALL_TAC(ASSUME `dcv = num_of_wordlist(dcnts:int16 list)`) THEN
  SUBST_ALL_TAC(ASSUME `dsv = num_of_wordlist(dsyms:int16 list)`);;

let NUM_OF_WORDLIST_FIXED_LL = prove
 (`num_of_wordlist(MAP (word:num->int16) deflate_fixed_ll) =
   nsum (0..287) (\i. (if i < 144 then 8 else if i < 256 then 9
                       else if i < 280 then 7 else 8) * 2 EXP (16 * i))`,
  REWRITE_TAC[deflate_fixed_ll; NUM_OF_WORDLIST_LIST_OF_SEQ16] THEN
  REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** A call of construct at step n, specialized at vars, with the          ***)
(*** rewrites ths to evaluate the length of the code lengths               ***)

let PUFF_CONSTRUCT_CALL_TAC ths vars n =
  MP_TAC(ISPECL vars PUFF_CONSTRUCT_CORRECT) THEN
  REWRITE_TAC ths THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ARM_BIGSTEP_TAC PUFF_EXEC ("s"^string_of_int n);;

let PUFF_CODES_VARS lh lcnt lsym ll lcnts lsyms dh dcnt dsym dl dcnts dsyms
                    ret =
  [`word_add (word_sub stackpointer (word 2448)) (word 288):int64`;
   lh; lcnt; lsym; ll; lcnts; lsyms; dh; dcnt; dsym; dl; dcnts; dsyms;
   `l:byte list`; `source:int64`; `pk + 3`; `dest:int64`; `outlen:num`;
   `outk:byte list`; `fl:int64`; `ea:int64`; `el:num`; `ev:num`;
   `enc:int64 list->num`; puff_sctx; `ctx0:int64 list`; `pc:num`; ret;
   `word_sub stackpointer (word 2448):int64`];;

let FIXED_TABLES_NEW_TAC =
  REWRITE_TAC[puff_fixed_tables] THEN
  MAP_EVERY EXISTS_TAC
   [`word 0:int32`; `word_add (word pc) (word 131152):int64`;
    `word_add (word pc) (word 131184):int64`;
    `word_add (word pc) (word 131776):int64`;
    `word_add (word pc) (word 131808):int64`;
    `num_of_wordlist(lcnts:int16 list)`; `num_of_wordlist(lsyms:int16 list)`;
    `num_of_wordlist(dcnts:int16 list)`; `num_of_wordlist(dsyms:int16 list)`]
  THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`lcnts:int16 list`; `lsyms:int16 list`;
                        `dcnts:int16 list`; `dsyms:int16 list`] THEN
  ASM_REWRITE_TAC[];;

let NO_FIXED_TAC =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `1`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ; deflate_fixed_dl;
                    GSYM DEFLATE_CODES_FIXED_DL] THEN
    REWRITE_TAC[GSYM NOT_LE] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_neg(concl th) && is_exists(rand(concl th)))) THEN
    MESON_TAC[];
    SIMP_TAC[]];;

let NO_FIXED_AT_ALL_TAC =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `1`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK_AT_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ; deflate_fixed_dl;
                    GSYM DEFLATE_CODES_FIXED_DL] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_neg(concl th) && is_exists(rand(concl th)))) THEN
    MESON_TAC[];
    SIMP_TAC[]];;

let PUFF_RETURN_TABS_TAC tabtac sel steps tac =
  PUFF_STEPS_TAC steps THEN ENSURES_FINAL_STATE_TAC THEN sel THEN
  REWRITE_TAC[jmp_context; CONS_11] THEN ASM_REWRITE_TAC[PUFF_SP_RESTORE] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [tabtac; tac];;

let PUFF_ESCAPE_TABS_TAC tabtac sel n tac =
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV EL_CONV)) THEN
  PUFF_STEPS_TAC ((n+1)--(n+11)) THEN ENSURES_FINAL_STATE_TAC THEN sel THEN
  REWRITE_TAC[jmp_context; CONS_11] THEN ASM_REWRITE_TAC[PUFF_SP_RESTORE] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [tabtac; tac];;

(*** Replace the numeral N in the assumption tm = N by tgt, where conv     ***)
(*** proves tgt = N                                                        ***)

let CHUNKS_TO_TAC conv tgt tm =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = tm
    then ASSUME_TAC(TRANS th (SYM(conv tgt)))
    else failwith "CHUNKS_TO_TAC");;

let FIXED_LL_CONV tm =
  (REWRITE_CONV[NUM_OF_WORDLIST_FIXED_LL] THENC EXPAND_NSUM_CONV THENC
   NUM_REDUCE_CONV) tm;;

let DISCARD_BYTES128_TAC =
  W(fun (asl,w) ->
    let bad th =
      let t = concl th in
      is_eq t && can (find_term (fun u ->
        try fst(dest_const u) = "bytes128" with _ -> false)) (lhs t) in
    let rec go asl = match asl with
        [] -> ALL_TAC
      | (_,th)::t ->
          if bad th then UNDISCH_THEN (concl th) (K ALL_TAC) THEN go t
          else go t in
    go asl);;

let FIXED_HEAD_TAC =
  let sp = `word_sub stackpointer (word 2448):int64` in
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  PUFF_STEPS_TAC (1--5) THEN
  ASM_CASES_TAC `vflag:int32 = word 0` THENL
   [SUBGOAL_THEN `val(vflag:int32) = 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    PUFF_STEPS_TAC [6] THEN FIXED_TABLES_VALID_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`lcnts:int16 list`; `lsyms:int16 list`;
                          `dcnts:int16 list`; `dsyms:int16 list`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(val(vflag:int32) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    PUFF_STEPS_TAC [6] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(vflag:int32) = 0)`]) THEN
    PUFF_STEPS_TAC [7] THEN PUFF_ADRP_TAC THEN
    MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (8--137) THEN
    PUFF_STEPS_TAC [138] THEN PUFF_ADRP_TAC THEN
    MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (139--145)
    THEN
    CHUNKS_TAC READ_MEMORY_BYTES_CHUNK128 "bytes128" 16 sp 1232 36
      `s145:armstate` THEN
    CHUNKS_TO_TAC FIXED_LL_CONV
     `num_of_wordlist(MAP (word:num->int16) deflate_fixed_ll)`
     `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                     (word 1232),576)) s145` THEN
    ASSUME_TAC(CONJUNCT1 DEFLATE_FIXED_BOUND) THEN
    PUFF_CONSTRUCT_CALL_TAC [LENGTH_DEFLATE_FIXED_LL; HUFFMAN_KRAFT_FIXED_LL]
     [`word_add (word pc) (word 131136):int64`;
      `word_add (word pc) (word 131152):int64`;
      `word_add (word pc) (word 131184):int64`;
      `word_add (word_sub stackpointer (word 2448)) (word 1232):int64`;
      `deflate_fixed_ll`; `pc:num`; `word(pc + 3996):int64`; sp] 146 THEN
    DISCARD_BYTES128_TAC THEN
    MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (147--239)
    THEN
    PUFF_STEPS_TAC [240] THEN PUFF_ADRP_TAC THEN
    MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (241--245)
    THEN
    CHUNKS_TAC READ_MEMORY_BYTES_CHUNK16 "bytes16" 2 sp 1232 30
      `s245:armstate` THEN
    CHUNKS_TO_TAC (RAND_CONV(RAND_CONV REPLICATE_EXPAND_CONV) THENC
       REWRITE_CONV[MAP; num_of_wordlist; VAL_WORD; DIMINDEX_16] THENC
       NUM_REDUCE_CONV)
     `num_of_wordlist(MAP (word:num->int16) (REPLICATE 30 5))`
     `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                     (word 1232),60)) s245` THEN
    ASSUME_TAC ALL_DIST_BOUND THEN
    PUFF_CONSTRUCT_CALL_TAC [LENGTH_REPLICATE; HUFFMAN_KRAFT_DIST]
     [`word_add (word pc) (word 131760):int64`;
      `word_add (word pc) (word 131776):int64`;
      `word_add (word pc) (word 131808):int64`;
      `word_add (word_sub stackpointer (word 2448)) (word 1232):int64`;
      `REPLICATE 30 5`; `pc:num`; `word(pc + 4044):int64`; sp] 246 THEN
    MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) [247;248]
    THEN
    ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`huffman_counts deflate_fixed_ll`; `syms:int16 list`;
      `huffman_counts (REPLICATE 30 5)`; `syms':int16 list`] THEN
    ASM_REWRITE_TAC[]];;

let FIXED_CODES_TAC =
  ENSURES_EXISTS_PRE_TAC `lcnts:int16 list` THEN
  ENSURES_EXISTS_PRE_TAC `lsyms:int16 list` THEN
  ENSURES_EXISTS_PRE_TAC `dcnts:int16 list` THEN
  ENSURES_EXISTS_PRE_TAC `dsyms:int16 list` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  MAP_EVERY ASSUME_TAC [CONJUNCT1 DEFLATE_FIXED_BOUND; ALL_DIST_BOUND;
    LENGTH_DEFLATE_FIXED_LL; HUFFMAN_KRAFT_FIXED_LL; HUFFMAN_KRAFT_DIST;
    ISPECL [`30`; `5`] LENGTH_REPLICATE] THEN
  ENSURES_INIT_TAC "s0" THEN
  PUFF_STEPS_TAC [1] THEN PUFF_ADRP_TAC THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (2--5) THEN
  PUFF_CALL_THS_TAC
   [ASSUME `LENGTH(lsyms:int16 list) = 288`;
    ASSUME `LENGTH(dsyms:int16 list) = 30`;
    LENGTH_DEFLATE_FIXED_LL; LENGTH_REPLICATE; HUFFMAN_KRAFT_FIXED_LL;
    HUFFMAN_KRAFT_DIST]
   PUFF_CODES_CORRECT
   (PUFF_CODES_VARS `word_add (word pc) (word 131136):int64`
      `word_add (word pc) (word 131152):int64`
      `word_add (word pc) (word 131184):int64` `deflate_fixed_ll`
      `lcnts:int16 list` `lsyms:int16 list`
      `word_add (word pc) (word 131760):int64`
      `word_add (word pc) (word 131776):int64`
      `word_add (word pc) (word 131808):int64` `REPLICATE 30 5`
      `dcnts:int16 list` `dsyms:int16 list` `word(pc + 4072):int64`) 6
  THENL
   [ABBREV_TAC `x0v = read X0 s6` THEN
    ASM_CASES_TAC `word_zx(x0v:int64):int32 = word 0` THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `word_zx(x0v:int64):int32 = word 0`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `out:byte list` (X_CHOOSE_THEN `q:num`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `val(word_zx(x0v:int64):int32) = 0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
      PUFF_STEPS_TAC (7--8) THEN
      MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`;
                    `out:byte list`; `q:num`; `last:num`; `1`]
                   DEFLATE_BLOCKS_AFTER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[deflate_block; ARITH_EQ; deflate_fixed_dl] THEN
        REWRITE_TAC[GSYM DEFLATE_CODES_FIXED_DL] THEN ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
      FIRST_ASSUM(fun th ->
        if can (term_match [] `deflate_codes l ll dl (outk,pk + 3) (out,q)`)
               (concl th)
        then MP_TAC(MATCH_MP DEFLATE_CODES_LENGTH th) THEN
             MP_TAC(MATCH_MP DEFLATE_CODES_BOUND th)
        else failwith "") THEN REPEAT STRIP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`out:byte list`; `q:num`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN
      FIXED_TABLES_NEW_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `~(word_zx(x0v:int64):int32 = word 0)`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(val(word_zx(x0v:int64):int32) = 0)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
      PUFF_STEPS_TAC (7--8) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; INT_SUB_RZERO]) THEN
      ASM_CASES_TAC `ival(word_zx(x0v:int64):int32) < &0` THEN
      PUFF_STEPS_TAC [9] THENL
       [PUFF_RETURN_TABS_TAC FIXED_TABLES_NEW_TAC (DISJ2_TAC THEN DISJ2_TAC)
          (10--24) NO_FIXED_TAC;
        PUFF_RETURN_TABS_TAC FIXED_TABLES_NEW_TAC (DISJ2_TAC THEN DISJ2_TAC)
          (10--17) NO_FIXED_TAC]];
    PUFF_ESCAPE_TABS_TAC FIXED_TABLES_NEW_TAC (DISJ2_TAC THEN DISJ2_TAC) 6
      NO_FIXED_AT_ALL_TAC];;

let FIXED_TAC =
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC fixed_ready THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    FIXED_HEAD_TAC; FIXED_CODES_TAC];;

(* ------------------------------------------------------------------------- *)
(* Blocks with dynamic codes, from 0xb7c: the header with HLIT, HDIST and    *)
(* HCLEN, giving nlen, ndist and ncode, up to loop A at 0xbec (dyn_a 0).     *)
(* ------------------------------------------------------------------------- *)

let NO_DYN_TAC =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `2`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK_AT_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP DEFLATE_DYNAMIC_HEADER) THEN
    SIMPLE_ARITH_TAC;
    SIMP_TAC[]];;

let BITS_BOUND_TAC p n =
  let b = mk_comb(mk_comb(mk_comb(`deflate_bits`,`l:byte list`),p),
                  mk_small_numeral n) in
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` b
                 (mk_small_numeral(1 lsl n))) ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; p; mk_small_numeral n]
           DEFLATE_BITS_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC];;

(*** The tables lencode and distcode of a dynamic block, on the stack ***)

let dyn_headers = `
  read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                   (word 128))) s =
  word_add (word_sub stackpointer (word 2448)) (word 160) /\
  read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                   (word 136))) s =
  word_add (word_sub stackpointer (word 2448)) (word 656) /\
  read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                   (word 144))) s =
  word_add (word_sub stackpointer (word 2448)) (word 192) /\
  read (memory :> bytes64(word_add (word_sub stackpointer (word 2448))
                                   (word 152))) s =
  word_add (word_sub stackpointer (word 2448)) (word 224)`;;

(*** Loop A at 0xbec, reading the code length code lengths, after j of     ***)
(*** them, then at 0xc10 after ncode of them                               ***)

let dyn_a = mk_abs(`j:num`,mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
  `read PC s = word(if j < ncode then pc + 0xbec else pc + 0xc10)`;
  `read X21 s = word_add (word_sub stackpointer (word 2448)) (word 288) /\
   read X20 s = word last /\
   read X22 s = word_add (word_sub stackpointer (word 2448)) (word 1816) /\
   read X23 s = word 3 /\ read X24 s = word(ncode + 1) /\
   read X25 s = word nlen /\ read X26 s = word ndist /\
   read X27 s = word(if j < ncode then j + 1 else ncode)`;
  dyn_headers;
  `?c. LENGTH c = 19 /\
       read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                      (word 1816),38)) s =
       num_of_wordlist c /\
       !i. i < j
           ==> EL (EL i deflate_clen_order) c =
               word(deflate_bits l (p3 + 14 + 3 * i) 3):int16`;
  subst [`p3 + 14 + 3 * j`,`pk:num`] puff_state]));;

let DYN_ABBREV_TAC =
  ABBREV_TAC `p3 = pk + 3` THEN
  ABBREV_TAC `nlen = deflate_bits l p3 5 + 257` THEN
  ABBREV_TAC `ndist = deflate_bits l (p3 + 5) 5 + 1` THEN
  ABBREV_TAC `ncode = deflate_bits l (p3 + 10) 4 + 4` THEN
  SUBGOAL_THEN `4 <= ncode /\ ncode <= 19` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ncode" THEN
    MP_TAC(SPECL [`l:byte list`; `p3 + 10`; `4`] DEFLATE_BITS_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ARITH_TAC;
    ALL_TAC];;

let dyn_a0 = mk_abs(`s:armstate`,
  rhs(concl((RATOR_CONV BETA_CONV THENC BETA_CONV)
    (mk_comb(mk_comb(dyn_a,`0`),`s:armstate`)))));;

(*** The header of a dynamic block, up to the checks of nlen and ndist,    ***)
(*** then loop A (DYN_HEAD_TAC), when nlen <= 286 /\ ndist <= 30, or the   ***)
(*** return of -3 (DYN_HEAD_NEG_TAC)                                       ***)

let DYN_HEAD_PREFIX_TAC sel =
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--14) THEN
  PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
   (PUFF_BITS_VARS `5` `p3:num` `word(pc + 2976):int64`) 15 THENL
   [ALL_TAC; PUFF_ESCAPE_TAC sel 15 NO_DYN_TAC] THEN
  BITS_BOUND_TAC `p3:num` 5 THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (16--19) THEN
  PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
   (PUFF_BITS_VARS `5` `p3 + 5` `word(pc + 2992):int64`) 20 THENL
   [ALL_TAC; PUFF_ESCAPE_TAC sel 20 NO_DYN_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(p3 + 5) + 5 = p3 + 10`]) THEN
  BITS_BOUND_TAC `p3 + 5` 5 THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (21--24) THEN
  PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
   (PUFF_BITS_VARS `4` `p3 + 10` `word(pc + 3008):int64`) 25 THENL
   [ALL_TAC; PUFF_ESCAPE_TAC sel 25 NO_DYN_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(p3 + 10) + 4 = p3 + 14`]) THEN
  BITS_BOUND_TAC `p3 + 10` 4;;

let DYN_HEAD_TAC =
  DYN_HEAD_PREFIX_TAC (DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC) THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (26--34) THEN
  IVAL_SMALL_TAC THEN
  MP_TAC(SPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
                `19`; `s34:armstate`] WORDLIST16_FROM_MEMORY) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:int16 list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < ncode` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    EXISTS_TAC `c:int16 list` THEN ASM_REWRITE_TAC[];
    FIXED_TABLES_KEEP_TAC];;

let DYN_HEAD_NEG_TAC =
  let sel = DISJ2_TAC THEN DISJ2_TAC in
  DYN_HEAD_PREFIX_TAC sel THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM] o
    check (fun th -> concl th = `~(nlen <= 286 /\ ndist <= 30)`)) THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (26--28) THEN
  PUFF_RETURN_TAC sel (29--44) NO_DYN_TAC;;

(* ------------------------------------------------------------------------- *)
(* Loop A, reading the ncode code length code lengths, at 0xbec, and loop B, *)
(* at 0xc28, setting the others to 0, up to 0xc3c (dyn_cl).                  *)
(* ------------------------------------------------------------------------- *)

(*** The order of the code length code lengths, at 0x11b0 ***)

let PUFF_ORDER_BYTES = prove
 (`num_of_bytelist(SUB_LIST(4528,38) puff_gcc12_O2_mc) =
   num_of_wordlist(MAP (word:num->int16) deflate_clen_order)`,
  REWRITE_TAC[puff_gcc12_O2_mc; deflate_clen_order] THEN
  CONV_TAC(ONCE_DEPTH_CONV SUB_LIST_CONV) THEN
  REWRITE_TAC[MAP; num_of_bytelist; num_of_wordlist; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let PUFF_ORDER_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc
          ==> read (memory :> bytes(word_add (word pc) (word 4528),38)) s =
              num_of_wordlist(MAP (word:num->int16) deflate_clen_order)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_bytes_loaded] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM PUFF_ORDER_BYTES] THEN
  MP_TAC(ISPECL [`s:armstate`; `word pc:int64`; `puff_gcc12_O2_mc`;
                 `4528`; `38`] BYTES_LOADED_SUB_LIST) THEN
  ASM_REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_SUB_LIST;
                  LENGTH_PUFF_GCC12_O2_MC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(*** The element idx of the order table, in state s ***)

let ORDER_ELEMENT_TAC idx s =
  let lth = ASSUME(list_mk_comb
    (`aligned_bytes_loaded:armstate->int64->byte list->bool`,
     [s; `word pc:int64`; `puff_gcc12_O2_mc`])) in
  let tth = MATCH_MP PUFF_ORDER_LOADED lth in
  MP_TAC(ISPECL [`word_add (word pc) (word 4528):int64`;
                 `MAP (word:num->int16) deflate_clen_order`; `19`;
                 idx; s] READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[tth; LENGTH_MAP; DEFLATE_CLEN_ORDER_BOUNDS] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word:num->int16`; idx; `deflate_clen_order`] EL_MAP) THEN
  REWRITE_TAC[DEFLATE_CLEN_ORDER_BOUNDS] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN DISCH_TAC;;

(*** The address of the ldursh of order[i], from x1 = order + 2 * (i + 1) ***)

let ORDER_ADDR_TAC i =
  let tm = subst [i,`i:num`]
   `word_add (word_add (word pc) (word (4528 + 2 * (i + 1))))
             (word 18446744073709551614):int64 =
    word_add (word pc) (word (4528 + 2 * i))` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE
     `pc + (4528 + 2 * (i + 1)) + 18446744073709551614 =
      1 * 18446744073709551616 + (pc + 4528 + 2 * i)`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC];;

(*** At 0xc3c in a dynamic block, with the code length code lengths cl     ***)
(*** in lengths[0..18]                                                     ***)

let dyn_cl = mk_abs(`s:armstate`,
  mk_exists(`cl:num list`, list_mk_conj
   [`LENGTH cl = 19 /\ ALL (\x. x <= 7) cl /\
     (!i. i < 19
          ==> EL (EL i deflate_clen_order) cl =
              if i < ncode then deflate_bits l (p3 + 14 + 3 * i) 3 else 0)`;
    `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
    `read PC s = word(pc + 0xc3c)`;
    `read X20 s = word last /\ read X25 s = word nlen /\
     read X26 s = word ndist`;
    dyn_headers;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 1816),38)) s =
     num_of_wordlist(MAP (word:num->int16) cl)`;
    subst [`p3 + 14 + 3 * ncode`,`pk:num`] puff_state]));;

(*** The final state of an iteration of loop A ***)

let DYN_A_ITER_END_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `(p3 + 14 + 3 * i) + 3 = p3 + 14 + 3 * (i + 1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THENL
   [EXISTS_TAC `list_of_seq (\m. if m = t
                                 then word(deflate_bits l (p3 + 14 + 3 * i) 3)
                                 else EL m c:int16) 19` THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `EL j deflate_clen_order < 19` ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 DEFLATE_CLEN_ORDER_BOUNDS) THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    ASM_CASES_TAC `j:num = i` THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THENL
       [MP_TAC(SPECL [`j:num`; `i:num`] DEFLATE_CLEN_ORDER_INJ) THEN
        ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC]];
    FIXED_TABLES_KEEP_TAC];;

(*** An iteration of loop A, from 0xbec, reading the code length code      ***)
(*** length for order[i]                                                   ***)

let DYN_A_ITER_TAC =
  let sel = DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC in
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ASSUME `i < ncode`] THEN
  ENSURES_EXISTS_PRE_TAC `c:int16 list` THEN GLOBALIZE_PRECONDITION_TAC THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--3) THEN
  PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
   (PUFF_BITS_VARS `3` `p3 + 14 + 3 * i` `word(pc + 3064):int64`) 4 THENL
   [ALL_TAC; PUFF_ESCAPE_TAC sel 4 NO_DYN_TAC] THEN
  BITS_BOUND_TAC `p3 + 14 + 3 * i` 3 THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (5--6) THEN
  ORDER_ELEMENT_TAC `i:num` `s6:armstate` THEN ORDER_ADDR_TAC `i:num` THEN
  PUFF_STEPS_TAC [7] THEN
  SUBGOAL_THEN `EL i deflate_clen_order < 19` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 DEFLATE_CLEN_ORDER_BOUNDS) THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SMALL_WORD_TAC THEN
  ABBREV_TAC `t = EL i deflate_clen_order` THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `c:int16 list`; `t:num`; `s7:armstate`] READ_MEMORY_WORDLIST16_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REG_ABBREV_TAC `X1` `v:int64` `word t:int64` THEN
  SUBGOAL_THEN `val(v:int64) = t` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word t:int64 = v`)) THEN
    MATCH_MP_TAC VAL_WORD_SMALL THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PUFF_STEPS_TAC [8] THEN
  SUBGOAL_THEN
   `word_add (word_sub stackpointer (word 2448)) (word (1816 + 2 * t)):int64 =
    word_add (word_add (word_sub stackpointer (word 2448)) (word 1816))
             (word (2 * t))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `c:int16 list`;
    `list_of_seq (\m. if m = t then word(deflate_bits l (p3 + 14 + 3 * i) 3)
                      else EL m c:int16) 19`;
    `t:num`; `s8:armstate`] READ_MEMORY_WORDLIST16_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_CASES_TAC `i + 1 < ncode` THENL
   [PUFF_STEPS_TAC (9--11) THEN DYN_A_ITER_END_TAC;
    PUFF_STEPS_TAC (9--10) THEN DYN_A_ITER_END_TAC];;

(*** Loop B at 0xc28, zeroing lengths[order[ncode + j]], then at 0xc3c ***)

let dyn_b = mk_abs(`j:num`,mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
  `read PC s = word(if ncode + j < 19 then pc + 0xc28 else pc + 0xc3c)`;
  `read X0 s = word(ncode + j) /\
   (ncode + j < 19
    ==> read X2 s =
        word_add (word_sub stackpointer (word 2448)) (word 1816)) /\
   read X20 s = word last /\ read X25 s = word nlen /\
   read X26 s = word ndist`;
  dyn_headers;
  `?c. LENGTH c = 19 /\
       read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                      (word 1816),38)) s =
       num_of_wordlist c /\
       !i. i < ncode + j
           ==> EL (EL i deflate_clen_order) c =
               word(if i < ncode then deflate_bits l (p3 + 14 + 3 * i) 3
                    else 0):int16`;
  subst [`p3 + 14 + 3 * ncode`,`pk:num`] puff_state]));;

(*** From 0xc10 to the head of loop B, or to 0xc3c if ncode = 19 ***)

let DYN_B_ENTRY_TAC =
  let fin =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `c:int16 list` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
      FIXED_TABLES_KEEP_TAC] in
  BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  ENSURES_EXISTS_PRE_TAC `c:int16 list` THEN GLOBALIZE_PRECONDITION_TAC THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `ncode < 19` THENL
   [PUFF_STEPS_TAC (1--6) THEN fin; PUFF_STEPS_TAC (1--3) THEN fin];;

(*** The final state of an iteration of loop B ***)

let DYN_B_ITER_END_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `(ncode + i) + 1 = ncode + i + 1`]) THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THENL
   [EXISTS_TAC `list_of_seq (\m. if m = t then word 0 else EL m c:int16)
                            19` THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `EL j deflate_clen_order < 19` ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 DEFLATE_CLEN_ORDER_BOUNDS) THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    ASM_CASES_TAC `j = ncode + i` THENL
     [ASM_REWRITE_TAC[ARITH_RULE `~(ncode + i < ncode)`];
      COND_CASES_TAC THENL
       [MP_TAC(SPECL [`j:num`; `ncode + i`] DEFLATE_CLEN_ORDER_INJ) THEN
        ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC]];
    FIXED_TABLES_KEEP_TAC];;

(*** An iteration of loop B, from 0xc28 ***)

let DYN_B_ITER_TAC =
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `ncode + i < 19` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `ncode + i < 19`] THEN
  ENSURES_EXISTS_PRE_TAC `c:int16 list` THEN GLOBALIZE_PRECONDITION_TAC THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ORDER_ELEMENT_TAC `ncode + i` `s0:armstate` THEN
  SUBGOAL_THEN `val(word(ncode + i):int64) = ncode + i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_SMALL THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EL (ncode + i) deflate_clen_order < 19` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 DEFLATE_CLEN_ORDER_BOUNDS) THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PUFF_STEPS_TAC [1] THEN
  ABBREV_TAC `t = EL (ncode + i) deflate_clen_order` THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `c:int16 list`; `t:num`; `s1:armstate`] READ_MEMORY_WORDLIST16_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REG_ABBREV_TAC `X1` `v:int64` `word t:int64` THEN
  SUBGOAL_THEN `val(v:int64) = t` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word t:int64 = v`)) THEN
    MATCH_MP_TAC VAL_WORD_SMALL THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PUFF_STEPS_TAC (2--3) THEN
  SUBGOAL_THEN
   `word_add (word_sub stackpointer (word 2448)) (word (1816 + 2 * t)):int64 =
    word_add (word_add (word_sub stackpointer (word 2448)) (word 1816))
             (word (2 * t))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `c:int16 list`;
    `list_of_seq (\m. if m = t then word 0 else EL m c:int16) 19`;
    `t:num`; `s3:armstate`] READ_MEMORY_WORDLIST16_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_CASES_TAC `ncode + i + 1 < 19` THEN
  PUFF_STEPS_TAC (4--5) THEN DYN_B_ITER_END_TAC;;

(*** The value of a code length code length as stored ***)

let VAL_WORD_CLEN = prove
 (`!l p b. val(word(if b then deflate_bits l p 3 else 0):int16) =
           (if b then deflate_bits l p 3 else 0) /\
           (if b then deflate_bits l p 3 else 0) <= 7`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `3`] DEFLATE_BITS_BOUND) THEN
  COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD_0; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VAL_WORD_SMALL THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(*** From the end of loop B to dyn_cl ***)

let DYN_B_EXIT_TAC =
  BETA_TAC THEN
  SUBGOAL_THEN `ncode + (19 - ncode) = 19` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LT_REFL] THEN
  MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL
   [ALL_TAC; SUBSUMED_ID_MAYCHANGE_TAC] THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  DISJ1_TAC THEN EXISTS_TAC `MAP (val:int16->num) c` THEN
  SUBGOAL_THEN `MAP (word:num->int16) (MAP val c) = c` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MAP_o; o_DEF; WORD_VAL; MAP_ID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN
    MP_TAC(SPEC `k:num` DEFLATE_CLEN_ORDER_SURJ) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num`
     (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
    ASM_SIMP_TAC[VAL_WORD_CLEN];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `EL j deflate_clen_order < 19` ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 DEFLATE_CLEN_ORDER_BOUNDS) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; VAL_WORD_CLEN]];;

(* ------------------------------------------------------------------------- *)
(* The table of the code length code, by construct, which must be complete   *)
(* (or empty, when decoding fails later), up to 0xd84 (dyn_ctab).            *)
(* ------------------------------------------------------------------------- *)

(*** At 0xd84 in a dynamic block, with the table of the code length code ***)

let dyn_ctab = mk_abs(`s:armstate`,
  list_mk_exists([`cl:num list`; `csyms:int16 list`], list_mk_conj
   [`LENGTH cl = 19 /\ ALL (\x. x <= 7) cl /\
     (!i. i < 19
          ==> EL (EL i deflate_clen_order) cl =
              if i < ncode then deflate_bits l (p3 + 14 + 3 * i) 3 else 0) /\
     huffman_kraft cl <= 2 EXP 15 /\
     (huffman_kraft cl = 2 EXP 15 \/ ALL (\x. x = 0) cl) /\
     LENGTH csyms = 19 /\ huffman_table cl (huffman_counts cl) csyms`;
    `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
    `read PC s = word(pc + 0xd84)`;
    `read X20 s = word last /\
     read X23 s = word_add (word_sub stackpointer (word 2448)) (word 1816) /\
     read X24 s = word_add (word_sub stackpointer (word 2448)) (word 128) /\
     read X25 s = word nlen /\ read X26 s = word ndist`;
    dyn_headers;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 160),32)) s =
     num_of_wordlist(huffman_counts cl) /\
     read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 656),38)) s =
     num_of_wordlist(csyms:int16 list)`;
    subst [`p3 + 14 + 3 * ncode`,`pk:num`] puff_state]));;

(*** No decoding when the code length code lengths cl are not complete ***)

let NO_CL_TAC =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `2`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK_AT_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
    MAP_EVERY X_GEN_TAC [`out:byte list`; `q:num`] THEN
    MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `p3:num`;
                  `(out,q):byte list#num`; `nlen:num`; `ndist:num`;
                  `ncode:num`; `cl:num list`] DEFLATE_DYNAMIC_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]];;

(*** From 0xc3c, building the table of the code length code ***)

let DYN_CL_TAC =
  let sel = DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC
  and sp = `word_sub stackpointer (word 2448):int64` in
  ENSURES_EXISTS_PRE_TAC `cl:num list` THEN GLOBALIZE_PRECONDITION_TAC THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--6) THEN
  SUBGOAL_THEN `ALL (\x. x <= 15) (cl:num list)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x <= 7) (cl:num list)` THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    ALL_TAC] THEN
  PUFF_CONSTRUCT_CALL_TAC [ASSUME `LENGTH(cl:num list) = 19`]
   [`word_add (word_sub stackpointer (word 2448)) (word 128):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 160):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 656):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `cl:num list`; `pc:num`; `word(pc + 3156):int64`; sp] 7 THEN
  ASM_CASES_TAC `huffman_kraft cl <= 32768` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = `huffman_kraft cl <= 32768`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `csyms:int16 list` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `huffman_kraft cl = 32768 \/ ALL (\x. x = 0) cl` THENL
     [SUBGOAL_THEN `(if ALL (\x. x = 0) cl then 0
                     else 32768 - huffman_kraft cl) = 0`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [COND_CASES_TAC THEN ASM_MESON_TAC[SUB_REFL]; ALL_TAC] THEN
      PUFF_STEPS_TAC [8] THEN
      ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN BETA_TAC THEN
      MAP_EVERY EXISTS_TAC [`cl:num list`; `csyms:int16 list`] THEN
      ASM_REWRITE_TAC[] THEN FIXED_TABLES_KEEP_TAC;
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [ASSUME `~ALL (\x. x = 0) (cl:num list)`]) THEN
      PUFF_RETURN_TAC sel (8--23) NO_CL_TAC];
    SUBGOAL_THEN `~(huffman_kraft cl = 32768)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = `32768 < huffman_kraft cl`)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `~(val(word_zx(read X0 s7):int32) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_EQ_0] THEN DISCH_TAC THEN
      UNDISCH_TAC `ival(word_zx(read X0 s7):int32) < &0` THEN
      ASM_REWRITE_TAC[IVAL_WORD_0] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    PUFF_RETURN_TAC sel (8--23) NO_CL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Loop C, at 0xdb0, reading the code lengths, with the repeats by loop D at *)
(* 0xe10, up to 0xe30 (dyn_lens).                                            *)
(* ------------------------------------------------------------------------- *)

(*** The tables of the code length code, on the stack ***)

let dyn_ctabs = `
  read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                 (word 160),32)) s =
  num_of_wordlist(huffman_counts cl) /\
  read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                 (word 656),38)) s =
  num_of_wordlist(csyms:int16 list)`;;

(*** Loop C at 0xdb0, reading the code lengths, with lens read so far up   ***)
(*** to position p, for the measure m = nlen + ndist - LENGTH lens         ***)

let dyn_c = mk_abs(`m:num`,mk_abs(`s:armstate`,
  list_mk_exists([`lens:num list`; `p:num`], list_mk_conj
   [`m = (nlen + ndist) - LENGTH lens /\ LENGTH lens < nlen + ndist /\
     ALL (\x. x <= 15) lens /\
     (!r. deflate_lengths l cl (nlen + ndist) ([],p3 + 14 + 3 * ncode) r <=>
          deflate_lengths l cl (nlen + ndist) (lens,p) r)`;
    `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
    `read PC s = word(pc + 0xdb0)`;
    `read X20 s = word last /\ read X21 s = word(nlen + ndist) /\
     read X22 s = word_add (word_sub stackpointer (word 2448)) (word 288) /\
     read X23 s = word_add (word_sub stackpointer (word 2448)) (word 1816) /\
     read X24 s = word_add (word_sub stackpointer (word 2448)) (word 128) /\
     read X25 s = word nlen /\ read X26 s = word ndist /\
     read X27 s = word 0 /\ read X28 s = word(LENGTH(lens:num list))`;
    dyn_headers; dyn_ctabs;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 1816),2 * LENGTH lens)) s =
     num_of_wordlist(MAP (word:num->int16) lens)`;
    subst [`p:num`,`pk:num`] puff_state])));;

(*** At 0xe30, after all the code lengths lens, up to position q ***)

let dyn_lens = mk_abs(`s:armstate`,
  list_mk_exists([`lens:num list`; `q:num`], list_mk_conj
   [`LENGTH lens = nlen + ndist /\ ALL (\x. x <= 15) lens /\
     huffman_kraft cl = 2 EXP 15 /\
     (!r. deflate_lengths l cl (nlen + ndist) ([],p3 + 14 + 3 * ncode) r <=>
          r = (lens,q))`;
    `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
    `read PC s = word(pc + 0xe30)`;
    `read X20 s = word last /\ read X25 s = word nlen /\
     read X26 s = word ndist`;
    dyn_headers;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 1816),2 * (nlen + ndist))) s =
     num_of_wordlist(MAP (word:num->int16) lens)`;
    subst [`q:num`,`pk:num`] puff_state]));;

(*** From 0xd84 to the head of loop C ***)

let DYN_C_ENTRY_TAC =
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `nlen + ndist` THEN BETA_TAC THEN
  MAP_EVERY EXISTS_TAC [`[]:num list`; `p3 + 14 + 3 * ncode`] THEN
  ASM_REWRITE_TAC[LENGTH; ALL; SUB_0; MAP; MULT_CLAUSES; num_of_wordlist;
                  READ_MEMORY_BYTES_TRIVIAL] THEN
  REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN FIXED_TABLES_KEEP_TAC;;

(*** The variables for a call of decode with the code length code ***)

let PUFF_DECODE_VARS p ret =
  [`word_add (word_sub stackpointer (word 2448)) (word 288):int64`;
   `word_add (word_sub stackpointer (word 2448)) (word 128):int64`;
   `word_add (word_sub stackpointer (word 2448)) (word 160):int64`;
   `word_add (word_sub stackpointer (word 2448)) (word 656):int64`;
   `cl:num list`; `huffman_counts cl`; `csyms:int16 list`;
   `l:byte list`; `source:int64`; p; `fl:int64`; `ea:int64`;
   `el:num`; `ev:num`; `enc:int64 list->num`; puff_sctx;
   `ctx0:int64 list`; `pc:num`; ret;
   `word_sub stackpointer (word 2448):int64`];;

(*** No decoding when the code lengths are not decoded from (lens,p),      ***)
(*** which tac proves, given the invariant relating it to the start        ***)

let NO_LENGTHS_TAC tac =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `2`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK_AT_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
    MAP_EVERY X_GEN_TAC [`out0:byte list`; `q0:num`] THEN
    MATCH_MP_TAC DEFLATE_DYNAMIC_NO_LENGTHS THEN
    MAP_EVERY EXISTS_TAC
     [`nlen:num`; `ndist:num`; `ncode:num`; `cl:num list`] THEN
    ASM_REWRITE_TAC[] THEN TRY DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`lens1:num list`; `q1:num`] THEN
    ASM_REWRITE_TAC[] THEN tac;
    SIMP_TAC[]];;

(*** The registers in loop C, with lens the code lengths so far ***)

let dyn_regs = `
  read X20 s = word last /\ read X21 s = word(nlen + ndist) /\
  read X22 s = word_add (word_sub stackpointer (word 2448)) (word 288) /\
  read X23 s = word_add (word_sub stackpointer (word 2448)) (word 1816) /\
  read X24 s = word_add (word_sub stackpointer (word 2448)) (word 128) /\
  read X25 s = word nlen /\ read X26 s = word ndist /\
  read X27 s = word 0 /\ read X28 s = word(LENGTH(lens:num list))`;;

(*** At 0xdf8, to repeat v k times after lens, then continue from q ***)

let dyn_fill = mk_abs(`s:armstate`,
  list_mk_exists([`k:num`; `v:num`; `q:num`], list_mk_conj
   [`3 <= k /\ k <= 138 /\ v <= 15 /\ LENGTH lens + k <= nlen + ndist /\
     huffman_kraft cl = 2 EXP 15 /\
     (!r. deflate_lengths l cl (nlen + ndist) ([],p3 + 14 + 3 * ncode) r <=>
          deflate_lengths l cl (nlen + ndist)
            (APPEND lens (REPLICATE k v),q) r)`;
    `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
    `read PC s = word(pc + 0xdf8)`;
    `read X0 s = word k /\ read X3 s = word v`;
    dyn_regs; dyn_headers; dyn_ctabs;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 1816),2 * LENGTH lens)) s =
     num_of_wordlist(MAP (word:num->int16) lens)`;
    subst [`q:num`,`pk:num`] puff_state]));;

(*** The selector of the return disjunct inside loop C ***)

let DYN_C_SEL = DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
                DISJ2_TAC;;

(*** The code length repeat 17 or 18 (zeros), at step 5 after decode:      ***)
(*** rule DEFLATE_LENGTHS_REP17/18, nb extra bits, base b, steps from      ***)
(*** step 6 to the bl of bits, the return address of bits ret, and the     ***)
(*** steps after the count check to the return                             ***)

let DYN_C_ZEROS_TAC rule nb b nbl ret nret =
  let nbt = mk_small_numeral nb and bt = mk_small_numeral b in
  let bits = list_mk_comb(`deflate_bits`,[`l:byte list`; `q:num`; nbt]) in
  let k = mk_binop `(+):num->num->num` bits bt in
  let kth = ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` bt bits, k)) in
  let ncall = nbl + 1 in
  let rth = SPECL [`l:byte list`; `cl:num list`; `nlen + ndist`;
                   `lens:num list`; `p:num`; `q:num`] rule in
  let rth' = SPECL [`l:byte list`; `cl:num list`; `nlen + ndist`;
                    `lens:num list`; `p:num`; `q:num`;
                    `(lens1,q1):num list#num`] rule in
  let check = mk_binop `(<=):num->num->bool`
    (mk_binop `(+):num->num->num` `LENGTH(lens:num list)`
      (mk_binop `(+):num->num->num` bt bits)) `nlen + ndist` in
  PUFF_STEPS_TAC (6--nbl) THEN
  PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
   (PUFF_BITS_VARS nbt `q:num` ret) ncall THENL
   [BITS_BOUND_TAC `q:num` nb THEN
    ASM_CASES_TAC check THEN
    PUFF_STEPS_TAC ((ncall+1)--(ncall+6-(if nb = 7 then 1 else 0))) THENL
     [MP_TAC rth THEN ASM_REWRITE_TAC[kth] THEN DISCH_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN BETA_TAC THEN
      MAP_EVERY EXISTS_TAC [k; `0`; mk_binop `(+):num->num->num` `q:num` nbt]
      THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN
      TRY(CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN FIXED_TABLES_KEEP_TAC;
      PUFF_RETURN_TAC DYN_C_SEL nret
       (NO_LENGTHS_TAC
         (MP_TAC rth' THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
          ASM_REWRITE_TAC[]))];
    PUFF_ESCAPE_TAC DYN_C_SEL ncall
     (NO_LENGTHS_TAC
       (MP_TAC rth' THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b /\ c)`) THEN SIMPLE_ARITH_TAC))];;

(*** The code length code is complete once a symbol is decoded ***)

let KRAFT_TAC =
  SUBGOAL_THEN `huffman_kraft cl = 2 EXP 15`
   (fun th -> ASSUME_TAC th THEN
              ASSUME_TAC(CONV_RULE(RAND_CONV NUM_REDUCE_CONV) th)) THENL
   [FIRST_ASSUM(fun th ->
      match strip_comb(concl th) with
        Const("huffman_decode",_),[_;lens;_;_;_] when lens = `cl:num list` ->
          MP_TAC(MATCH_MP HUFFMAN_DECODE_NOT_ALL_ZERO th)
      | _ -> failwith "KRAFT_TAC") THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = `huffman_kraft cl = 2 EXP 15 \/ ALL (\x. x = 0) cl`)) THEN
    CONV_TAC TAUT;
    ALL_TAC];;

(*** A literal code length c, at step 5 after decode ***)

let DYN_C_LITERAL_TAC =
  PUFF_STEPS_TAC (6--7) THEN
  SXTW_ABBREV_TAC `X28` `v28:int64` `LENGTH(lens:num list)` THEN
  PUFF_STEPS_TAC [8] THEN
  UNDISCH_THEN `word(LENGTH(lens:num list)):int64 = v28` (SUBST_ALL_TAC o SYM)
  THEN
  SUBGOAL_THEN
   `word_add (word_sub stackpointer (word 2448))
             (word (1816 + 2 * LENGTH lens)):int64 =
    word_add (word_add (word_sub stackpointer (word 2448)) (word 1816))
             (word (2 * LENGTH(lens:num list)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `lens:num list`; `c:num`; `s8:armstate`] READ_MEMORY_LENGTHS_SNOC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `n + SUC 0 = n + 1`] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `cl:num list`; `nlen + ndist`; `lens:num list`;
                `p:num`; `c:num`; `q:num`] DEFLATE_LENGTHS_LITERAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  PUFF_STEPS_TAC [9] THEN
  ASM_CASES_TAC `LENGTH(lens:num list) + 1 < nlen + ndist` THEN
  PUFF_STEPS_TAC (10--11) THENL
   [ENSURES_FINAL_STATE_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(nlen + ndist) - (LENGTH(lens:num list) + 1)` THEN
    BETA_TAC THEN CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`APPEND lens [c:num]`; `q:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `n + SUC 0 = n + 1`;
                ALL_APPEND; ALL] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMPLE_ARITH_TAC; FIXED_TABLES_KEEP_TAC];
    SUBGOAL_THEN `LENGTH(lens:num list) + 1 = nlen + ndist` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`l:byte list`; `cl:num list`; `nlen + ndist`;
                  `APPEND lens [c:num]`; `q:num`] DEFLATE_LENGTHS_DONE) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `n + SUC 0 = n + 1`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_THEN `LENGTH(lens:num list) + 1 = nlen + ndist`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ENSURES_FINAL_STATE_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    BETA_TAC THEN MAP_EVERY EXISTS_TAC [`APPEND lens [c:num]`; `q:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `n + SUC 0 = n + 1`;
                ALL_APPEND; ALL] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN
    TRY(CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN FIXED_TABLES_KEEP_TAC];;

(*** The code length repeat 16 (the last length), at step 5 ***)

let DYN_C_REP16_TAC =
  let rth = SPECL [`l:byte list`; `cl:num list`; `nlen + ndist`;
                   `lens:num list`; `p:num`; `q:num`] DEFLATE_LENGTHS_REP16
  and rth' = SPECL [`l:byte list`; `cl:num list`; `nlen + ndist`;
                    `lens:num list`; `p:num`; `q:num`;
                    `(lens1,q1):num list#num`] DEFLATE_LENGTHS_REP16 in
  PUFF_STEPS_TAC (6--9) THEN
  ASM_CASES_TAC `LENGTH(lens:num list) = 0` THENL
   [PUFF_STEPS_TAC [10] THEN
    PUFF_RETURN_TAC DYN_C_SEL (11--30)
     (NO_LENGTHS_TAC
       (MP_TAC rth' THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]));
    PUFF_STEPS_TAC (10--13) THEN
    ABBREV_TAC `v = EL (LENGTH lens - 1) (lens:num list)` THEN
    SUBGOAL_THEN `v <= 15` ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN
      UNDISCH_TAC `ALL (\x. x <= 15) (lens:num list)` THEN
      REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN MATCH_MP_TAC THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
      `MAP (word:num->int16) lens`; `LENGTH(lens:num list)`;
      `LENGTH(lens:num list) - 1`; `s13:armstate`]
     READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; ARITH_RULE `~(n = 0) ==> n - 1 < n`] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
    SXTW_ABBREV_TAC `X3` `v3:int64` `LENGTH(lens:num list) - 1` THEN
    PUFF_STEPS_TAC [14] THEN
    UNDISCH_THEN `word(LENGTH(lens:num list) - 1):int64 = v3`
     (SUBST_ALL_TAC o SYM) THEN
    PUFF_STEPS_TAC (15--16) THEN
    PUFF_FRAME_CALL_TAC PUFF_BITS_CORRECT
     (PUFF_BITS_VARS `2` `q:num` `word(pc + 3788):int64`) 17 THENL
     [BITS_BOUND_TAC `q:num` 2 THEN
      ASM_CASES_TAC
       `LENGTH(lens:num list) + 3 + deflate_bits l q 2 <= nlen + ndist` THEN
      PUFF_STEPS_TAC (18--22) THENL
       [SUBGOAL_THEN `~(lens:num list = [])` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
        SUBGOAL_THEN `LAST(lens:num list) = v` ASSUME_TAC THENL
         [EXPAND_TAC "v" THEN MATCH_MP_TAC LAST_EL THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC rth THEN
        ASM_REWRITE_TAC[ARITH_RULE
         `3 + deflate_bits l q 2 = deflate_bits l q 2 + 3`] THEN
        DISCH_TAC THEN
        ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN BETA_TAC THEN
        MAP_EVERY EXISTS_TAC [`deflate_bits l q 2 + 3`; `v:num`; `q + 2`] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN
        TRY(CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN FIXED_TABLES_KEEP_TAC;
        PUFF_RETURN_TAC DYN_C_SEL (23--42)
         (NO_LENGTHS_TAC
           (MP_TAC rth' THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
            ASM_REWRITE_TAC[]))];
      PUFF_ESCAPE_TAC DYN_C_SEL 17
       (NO_LENGTHS_TAC
         (MP_TAC rth' THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
          MATCH_MP_TAC(TAUT `~b ==> ~(a /\ b /\ c /\ d)`) THEN
          SIMPLE_ARITH_TAC))]];;

(*** From the head of loop C to dyn_fill, the next iteration or the end ***)

let DYN_C_HEAD_TAC =
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--3) THEN
  PUFF_CALL_THS_TAC
   [ASSUME `LENGTH(csyms:int16 list) = 19`; ASSUME `LENGTH(cl:num list) = 19`]
   PUFF_DECODE_CORRECT (PUFF_DECODE_VARS `p:num` `word(pc + 3516):int64`) 4
  THENL
   [DECODE_FACTS_TAC `p:num` THEN KRAFT_TAC THEN
    PUFF_STEPS_TAC [5] THEN BIT31_DECIDE_TAC THEN
    ASM_CASES_TAC `c < 16` THENL
     [DYN_C_LITERAL_TAC;
      SUBGOAL_THEN `c = 16 \/ c = 17 \/ c = 18` MP_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
       [DYN_C_REP16_TAC;
        DYN_C_ZEROS_TAC DEFLATE_LENGTHS_REP17 3 3 14
          `word(pc + 3828):int64` (22--41);
        DYN_C_ZEROS_TAC DEFLATE_LENGTHS_REP18 7 11 14
          `word(pc + 3556):int64` (21--40)]];
    ABBREV_TAC `x0v = read X0 s4` THEN
    PUFF_RETURN_TAC DYN_C_SEL (5--19)
     (NO_LENGTHS_TAC
       (MATCH_MP_TAC DEFLATE_LENGTHS_NODECODE THEN ASM_REWRITE_TAC[]));
    PUFF_ESCAPE_TAC DYN_C_SEL 4
     (NO_LENGTHS_TAC
       (MATCH_MP_TAC DEFLATE_LENGTHS_NODECODE THEN ASM_REWRITE_TAC[]))];;

(*** Loop D at 0xe10, after j of the k copies of v, then at 0xe20 ***)

let dyn_d = mk_abs(`j:num`,mk_abs(`s:armstate`, list_mk_conj
  [`aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
   `read PC s = word(if j < k then pc + 0xe10 else pc + 0xe20)`;
   `(j < k ==> read X0 s = word(k - 1 - j)) /\
    read X1 s = word_add (word_sub stackpointer (word 2448))
                         (word(1816 + 2 * (LENGTH(lens:num list) + j))) /\
    read X3 s = word v /\ read X4 s = word(k - 1)`;
   dyn_regs; dyn_headers; dyn_ctabs;
   `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                   (word 1816),2 * (LENGTH lens + j))) s =
    num_of_wordlist(MAP (word:num->int16) (APPEND lens (REPLICATE j v)))`;
   subst [`q:num`,`pk:num`] puff_state]));;

(*** From 0xdf8 to the head of loop D ***)

let DYN_D_ENTRY_TAC =
  BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0; REPLICATE; APPEND_NIL] THEN
  SUBGOAL_THEN `0 < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN FIXED_TABLES_KEEP_TAC;;

(*** An iteration of loop D, storing the copy j of v ***)

let DYN_D_ITER_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ASSUME `j < k`] THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `j + 1 < k` THENL
   [ALL_TAC;
    SUBGOAL_THEN `k - 1 - j = 0` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [SIMPLE_ARITH_TAC; ALL_TAC]] THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--2) THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `APPEND lens (REPLICATE j (v:num))`; `v:num`; `s2:armstate`]
   READ_MEMORY_LENGTHS_SNOC) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; WORD_ADD_ASSOC_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; GSYM REPLICATE_SNOC; LENGTH;
              ARITH_RULE `(n + j) + SUC 0 = n + j + 1`] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (3--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `k - 1 - j - 1 = k - 1 - (j + 1)`;
    ARITH_RULE `(1816 + 2 * (n + j)) + 2 = 1816 + 2 * (n + j + 1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
  FIXED_TABLES_KEEP_TAC;;

(*** From 0xe20 after loop D, to the head of loop C or to 0xe30 ***)

let DYN_D_EXIT_TAC =
  BETA_TAC THEN REWRITE_TAC[LT_REFL] THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--2) THEN
  SUBGOAL_THEN `(LENGTH(lens:num list) + 1) + (k - 1) = LENGTH lens + k`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(lens:num list) + k < nlen + ndist` THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (3--4) THENL
   [ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(nlen + ndist) - (LENGTH(lens:num list) + k)` THEN
    BETA_TAC THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`APPEND lens (REPLICATE k (v:num))`; `q:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; ALL_APPEND;
                ALL_REPLICATE] THEN
    ASM_REWRITE_TAC[] THEN FIXED_TABLES_KEEP_TAC;
    SUBGOAL_THEN `LENGTH(lens:num list) + k = nlen + ndist` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`l:byte list`; `cl:num list`; `nlen + ndist`;
                  `APPEND lens (REPLICATE k (v:num))`; `q:num`]
                 DEFLATE_LENGTHS_DONE) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    UNDISCH_THEN `LENGTH(lens:num list) + k = nlen + ndist`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ENSURES_FINAL_STATE_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN BETA_TAC THEN
    MAP_EVERY EXISTS_TAC [`APPEND lens (REPLICATE k (v:num))`; `q:num`] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; ALL_APPEND;
                ALL_REPLICATE] THEN
    ASM_REWRITE_TAC[] THEN FIXED_TABLES_KEEP_TAC];;

(*** From dyn_fill at 0xdf8, the repeat of v k times by loop D ***)

let DYN_FILL_TAC =
  ENSURES_EXISTS_PRE_TAC `k:num` THEN ENSURES_EXISTS_PRE_TAC `v:num` THEN
  ENSURES_EXISTS_PRE_TAC `q:num` THEN GLOBALIZE_PRECONDITION_TAC THEN
  UNDISCH_THEN
   `!r. deflate_lengths l cl (nlen + ndist) ([],p3 + 14 + 3 * ncode) r <=>
        deflate_lengths l cl (nlen + ndist) (lens,p) r` (K ALL_TAC) THEN
  MATCH_MP_TAC(ISPECL [`k:num`; dyn_d] ENSURES_LOOP_EXIT) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    DYN_D_ENTRY_TAC; DYN_D_ITER_TAC; DYN_D_EXIT_TAC];;

(*** An iteration of loop C ***)

let DYN_C_ITER_TAC =
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `lens:num list` THEN
  ENSURES_EXISTS_PRE_TAC `p:num` THEN GLOBALIZE_PRECONDITION_TAC THEN
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC dyn_fill THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    DYN_C_HEAD_TAC; DYN_FILL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The tables of the literal/length and distance codes, built by construct,  *)
(* and the call of codes at 0xea8, through 0xe68 (dyn_lc) and 0xe9c          *)
(* (dyn_dc).                                                                 *)
(* ------------------------------------------------------------------------- *)

(*** At 0xe68, with the table of the literal/length code ll ***)

let dyn_lc = mk_abs(`s:armstate`,
  mk_exists(`lsyms:int16 list`, list_mk_conj
   [`~(EL 256 lens = 0) /\ huffman_ok (list_of_seq (\i. EL i lens) nlen) /\
     LENGTH(lsyms:int16 list) = nlen /\
     huffman_table (list_of_seq (\i. EL i lens) nlen)
       (huffman_counts (list_of_seq (\i. EL i lens) nlen)) lsyms`;
    `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
    `read PC s = word(pc + 0xe68)`;
    `read X20 s = word last /\ read X25 s = word nlen /\
     read X26 s = word ndist`;
    dyn_headers;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 160),32)) s =
     num_of_wordlist(huffman_counts
                      (list_of_seq (\i. EL i (lens:num list)) nlen)) /\
     read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 656),2 * nlen)) s =
     num_of_wordlist(lsyms:int16 list)`;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 1816),2 * (nlen + ndist))) s =
     num_of_wordlist(MAP (word:num->int16) lens)`;
    subst [`q:num`,`pk:num`] puff_state]));;

(*** No decoding, given the code lengths lens and the fact tac shows ***)

let NO_DYN_LENS_TAC tac =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `2`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK_AT_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
    MAP_EVERY X_GEN_TAC [`out0:byte list`; `q0:num`] THEN
    MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `p3:num`;
                  `(out0,q0):byte list#num`; `nlen:num`; `ndist:num`;
                  `ncode:num`; `cl:num list`; `lens:num list`; `q:num`]
                 DEFLATE_DYNAMIC_LENS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN tac;
    SIMP_TAC[]];;

(*** After construct(h,lengths,n) at step c for the code ll, the checks    ***)
(*** of puff, with fin to finish at the next part, and the -7 or -8        ***)
(*** returns; ll0 and n0 in the quotations stand for ll and n              ***)

let DYN_TABLE_CHECK_TAC ll n c cnt fin =
  let sel = REPEAT DISJ2_TAC in
  let i t = subst [ll,`ll0:num list`; n,`n0:num`] t in
  let s = mk_var("s"^string_of_int c,`:armstate`)
  and s3 = mk_var("s"^string_of_int (c+3),`:armstate`) in
  let x0 = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                           `X0`),s) in
  let cnta = mk_comb(mk_comb(`word_add:int64->int64->int64`,
                       `word_sub stackpointer (word 2448):int64`),
                     mk_comb(`word:num->int64`,mk_small_numeral cnt)) in
  let nookf =
    REWRITE_TAC[huffman_ok] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] in
  let ret steps =
    PUFF_RETURN_TAC sel steps (NO_DYN_LENS_TAC(ASM_REWRITE_TAC[])) in
  ASM_CASES_TAC (i `huffman_kraft ll0 <= 32768`) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = i `huffman_kraft ll0 <= 32768`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `syms:int16 list` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC (i `huffman_kraft ll0 = 32768 \/ ALL (\x. x = 0) ll0`) THENL
     [SUBGOAL_THEN
       (i `(if ALL (\x. x = 0) ll0 then 0 else 32768 - huffman_kraft ll0) = 0`)
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [COND_CASES_TAC THEN ASM_MESON_TAC[SUB_REFL]; ALL_TAC] THEN
      SUBGOAL_THEN (i `huffman_ok ll0`) ASSUME_TAC THENL
       [REWRITE_TAC[huffman_ok] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
          concl th =
          i `huffman_kraft ll0 = 32768 \/ ALL (\x. x = 0) ll0`)) THEN
        ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          concl th = i `ALL (\x. x = 0) ll0`)) THEN
        MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
        ALL_TAC] THEN
      PUFF_STEPS_TAC ((c+1)--(c+2)) THEN fin;
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM] o
        check (fun th -> concl th =
          i `~(huffman_kraft ll0 = 32768 \/ ALL (\x. x = 0) ll0)`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (i `~ALL (\x. x = 0) ll0`)]) THEN
      PUFF_STEPS_TAC ((c+1)--(c+3)) THEN
      MP_TAC(ISPECL [cnta; i `huffman_counts ll0`; `16`; `0`; s3]
                    READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
      MP_TAC(ISPECL [cnta; i `huffman_counts ll0`; `16`; `1`; s3]
                    READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      ASM_REWRITE_TAC[LENGTH_HUFFMAN_COUNTS] THEN
      SIMP_TAC[EL_HUFFMAN_COUNTS; ARITH] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_NUM; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REPEAT DISCH_TAC THEN
      MP_TAC(ISPECL [ll; `0`] HUFFMAN_COUNT_LE_LENGTH) THEN
      MP_TAC(ISPECL [ll; `1`] HUFFMAN_COUNT_LE_LENGTH) THEN
      REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN REPEAT DISCH_TAC THEN
      MP_TAC(ISPEC ll HUFFMAN_COUNT_ALL_LE1) THEN
      ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_TAC THEN
      ASM_CASES_TAC (i `ALL (\n. n <= 1) ll0`) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_iff(concl th) &&
        is_eq(lhand(concl th)) && rand(lhand(concl th)) = n)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
       [SUBGOAL_THEN (i `huffman_ok ll0`) ASSUME_TAC THENL
         [nookf; ALL_TAC] THEN
        PUFF_STEPS_TAC ((c+4)--(c+8)) THEN fin;
        SUBGOAL_THEN (i `~huffman_ok ll0`) ASSUME_TAC THENL
         [nookf; ALL_TAC] THEN
        PUFF_STEPS_TAC ((c+4)--(c+8)) THEN ret ((c+9)--(c+24))]];
    SUBGOAL_THEN (i `~huffman_ok ll0`) ASSUME_TAC THENL
     [nookf; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = i `32768 < huffman_kraft ll0`)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    ABBREV_TAC (mk_eq(`x0v:int64`,x0)) THEN
    SUBGOAL_THEN `~(val(word_zx(x0v:int64):int32) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_EQ_0] THEN DISCH_TAC THEN
      UNDISCH_TAC `ival(word_zx(x0v:int64):int32) < &0` THEN
      ASM_REWRITE_TAC[IVAL_WORD_0] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    PUFF_STEPS_TAC ((c+1)--(c+2)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; INT_SUB_RZERO]) THEN
    PUFF_STEPS_TAC [c+3] THEN ret ((c+4)--(c+19))];;

(*** The final state at 0xe68 ***)

let DYN_LC_FIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN BETA_TAC THEN
  EXISTS_TAC `syms:int16 list` THEN ASM_REWRITE_TAC[] THEN
  FIXED_TABLES_KEEP_TAC;;

(*** At 0xe9c, with the tables of both codes ***)

let dyn_dc = mk_abs(`s:armstate`,
  list_mk_exists([`lsyms:int16 list`; `dsyms:int16 list`], list_mk_conj
   [`~(EL 256 lens = 0) /\ huffman_ok (list_of_seq (\i. EL i lens) nlen) /\
     LENGTH(lsyms:int16 list) = nlen /\
     huffman_table (list_of_seq (\i. EL i lens) nlen)
       (huffman_counts (list_of_seq (\i. EL i lens) nlen)) lsyms /\
     huffman_ok (list_of_seq (\i. EL (nlen + i) lens) ndist) /\
     LENGTH(dsyms:int16 list) = ndist /\
     huffman_table (list_of_seq (\i. EL (nlen + i) lens) ndist)
       (huffman_counts (list_of_seq (\i. EL (nlen + i) lens) ndist)) dsyms`;
    `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
    `read PC s = word(pc + 0xe9c)`;
    `read X20 s = word last`;
    dyn_headers;
    `read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 160),32)) s =
     num_of_wordlist(huffman_counts
                      (list_of_seq (\i. EL i (lens:num list)) nlen)) /\
     read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 656),2 * nlen)) s =
     num_of_wordlist(lsyms:int16 list) /\
     read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 192),32)) s =
     num_of_wordlist(huffman_counts
                (list_of_seq (\i. EL (nlen + i) (lens:num list)) ndist)) /\
     read (memory :> bytes(word_add (word_sub stackpointer (word 2448))
                                    (word 224),2 * ndist)) s =
     num_of_wordlist(dsyms:int16 list)`;
    subst [`q:num`,`pk:num`] puff_state]));;

let DYN_DC_FIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN BETA_TAC THEN
  MAP_EVERY EXISTS_TAC [`lsyms:int16 list`; `syms:int16 list`] THEN
  ASM_REWRITE_TAC[] THEN FIXED_TABLES_KEEP_TAC;;

(*** The literal/length code table, from 0xe30 ***)

let DYN_LL_TAC =
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `256 < LENGTH(lens:num list)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EL 256 lens <= 15` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x <= 15) (lens:num list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `MAP (word:num->int16) lens`; `nlen + ndist`; `256`; `s0:armstate`]
   READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) o
    REWRITE_RULE[WORD_ADD_ASSOC_NUM] o
    CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  PUFF_STEPS_TAC [1] THEN
  ASM_CASES_TAC `EL 256 lens = 0` THENL
   [PUFF_RETURN_TAC (REPEAT DISJ2_TAC) (2--18)
     (NO_DYN_LENS_TAC (ASM_REWRITE_TAC[]));
    ALL_TAC] THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (2--6) THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `lens:num list`; `0`; `nlen:num`; `s6:armstate`]
   READ_MEMORY_LENGTHS_SUB) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ALL (\x. x <= 15) (list_of_seq (\i. EL i (lens:num list)) nlen)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[EL_LIST_OF_SEQ] THEN
    UNDISCH_TAC `ALL (\x. x <= 15) (lens:num list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PUFF_CONSTRUCT_CALL_TAC [LENGTH_LIST_OF_SEQ]
   [`word_add (word_sub stackpointer (word 2448)) (word 128):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 160):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 656):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `list_of_seq (\i. EL i (lens:num list)) nlen`; `pc:num`;
    `word(pc + 3656):int64`; `word_sub stackpointer (word 2448):int64`] 7 THEN
  DYN_TABLE_CHECK_TAC `list_of_seq (\i. EL i (lens:num list)) nlen`
    `nlen:num` 7 160 DYN_LC_FIN_TAC;;

(*** The distance code table, from 0xe68 ***)

let DYN_DL_TAC =
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--5) THEN
  MP_TAC(ISPECL
   [`word_add (word_sub stackpointer (word 2448)) (word 1816):int64`;
    `lens:num list`; `nlen:num`; `ndist:num`; `s5:armstate`]
   READ_MEMORY_LENGTHS_SUB) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ALL (\x. x <= 15) (list_of_seq (\i. EL (nlen + i) (lens:num list)) ndist)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[EL_LIST_OF_SEQ] THEN
    UNDISCH_TAC `ALL (\x. x <= 15) (lens:num list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PUFF_CONSTRUCT_CALL_TAC [LENGTH_LIST_OF_SEQ]
   [`word_add (word_sub stackpointer (word 2448)) (word 144):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 192):int64`;
    `word_add (word_sub stackpointer (word 2448)) (word 224):int64`;
    `word_add (word_sub stackpointer (word 2448))
              (word (1816 + 2 * nlen)):int64`;
    `list_of_seq (\i. EL (nlen + i) (lens:num list)) ndist`; `pc:num`;
    `word(pc + 3708):int64`; `word_sub stackpointer (word 2448):int64`] 6 THEN
  DYN_TABLE_CHECK_TAC `list_of_seq (\i. EL (nlen + i) (lens:num list)) ndist`
    `ndist:num` 6 192 DYN_DC_FIN_TAC;;

(*** No decoding when there is none of the block data that fits ***)

let NO_DYN_CODES_TAC =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `2`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
    MAP_EVERY X_GEN_TAC [`out0:byte list`; `q0:num`] THEN
    MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `p3:num`;
                  `(out0,q0):byte list#num`; `nlen:num`; `ndist:num`;
                  `ncode:num`; `cl:num list`; `lens:num list`; `q:num`]
                 DEFLATE_DYNAMIC_LENS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM NOT_LE] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_neg(concl th) && is_exists(rand(concl th)))) THEN
    MESON_TAC[];
    SIMP_TAC[]];;

let NO_DYN_CODES_AT_ALL_TAC =
  MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`; `2`;
                `outlen:num`] DEFLATE_DECODE_NO_BLOCK_AT_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[deflate_block; ARITH_EQ] THEN
    MAP_EVERY X_GEN_TAC [`out0:byte list`; `q0:num`] THEN
    MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `p3:num`;
                  `(out0,q0):byte list#num`; `nlen:num`; `ndist:num`;
                  `ncode:num`; `cl:num list`; `lens:num list`; `q:num`]
                 DEFLATE_DYNAMIC_LENS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_neg(concl th) && is_exists(rand(concl th)))) THEN
    MESON_TAC[];
    SIMP_TAC[]];;

(*** From 0xe9c, the call of codes and the end of the block ***)

let DYN_CODES_TAC =
  let sp = `word_sub stackpointer (word 2448):int64` in
  let fr n = mk_comb(mk_comb(`word_add:int64->int64->int64`,sp),
                     mk_comb(`word:num->int64`,mk_small_numeral n)) in
  let ll = `list_of_seq (\i. EL i (lens:num list)) nlen`
  and dl = `list_of_seq (\i. EL (nlen + i) (lens:num list)) ndist` in
  let all15 t = mk_comb(`ALL (\x. x <= 15):num list->bool`,t) in
  ENSURES_EXISTS_PRE_TAC `ls:int16 list` THEN
  ENSURES_EXISTS_PRE_TAC `ds:int16 list` THEN GLOBALIZE_PRECONDITION_TAC THEN
  MAP_EVERY (fun t ->
    SUBGOAL_THEN (all15 t) ASSUME_TAC THENL
     [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
      SIMP_TAC[EL_LIST_OF_SEQ] THEN
      UNDISCH_TAC `ALL (\x. x <= 15) (lens:num list)` THEN
      REWRITE_TAC[GSYM ALL_EL] THEN DISCH_TAC THEN
      GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC]) [ll; dl] THEN
  MAP_EVERY (fun t ->
    FIRST_ASSUM(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) o
      CONJUNCT1 o REWRITE_RULE[huffman_ok] o
      check (fun th -> concl th = mk_comb(`huffman_ok`,t)))) [ll; dl] THEN
  MP_TAC(ISPECL [`l:byte list`; `cl:num list`; `nlen + ndist`;
                 `([]:num list,p3 + 14 + 3 * ncode)`; `(lens:num list,q:num)`]
                DEFLATE_LENGTHS_MONO) THEN
  ASM_REWRITE_TAC[SND] THEN DISCH_TAC THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun n -> PUFF_STEPS_TAC [n] THEN REG_PTR_NORM_TAC) (1--4) THEN
  PUFF_CALL_THS_TAC
   [ASSUME `LENGTH(ls:int16 list) = nlen`;
    ASSUME `LENGTH(ds:int16 list) = ndist`; LENGTH_LIST_OF_SEQ]
   PUFF_CODES_CORRECT
   [fr 288; fr 128; fr 160; fr 656; ll; mk_comb(`huffman_counts`,ll);
    `ls:int16 list`; fr 144; fr 192; fr 224; dl;
    mk_comb(`huffman_counts`,dl); `ds:int16 list`;
    `l:byte list`; `source:int64`; `q:num`; `dest:int64`; `outlen:num`;
    `outk:byte list`; `fl:int64`; `ea:int64`; `el:num`; `ev:num`;
    `enc:int64 list->num`; puff_sctx; `ctx0:int64 list`; `pc:num`;
    `word(pc + 3756):int64`; sp] 5
  THENL
   [ABBREV_TAC `x0v = read X0 s5` THEN
    ASM_CASES_TAC `word_zx(x0v:int64):int32 = word 0` THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `word_zx(x0v:int64):int32 = word 0`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `out:byte list` (X_CHOOSE_THEN `q2:num`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `val(word_zx(x0v:int64):int32) = 0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
      PUFF_STEPS_TAC (6--8) THEN
      SUBGOAL_THEN `deflate_block l 2 (outk,p3) (out,q2)` ASSUME_TAC THENL
       [REWRITE_TAC[deflate_block; ARITH_EQ] THEN
        MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `p3:num`;
                      `(out,q2):byte list#num`; `nlen:num`; `ndist:num`;
                      `ncode:num`; `cl:num list`; `lens:num list`; `q:num`]
                     DEFLATE_DYNAMIC_LENS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`l:byte list`; `outk:byte list`; `pk:num`;
                    `out:byte list`; `q2:num`; `last:num`; `2`]
                   DEFLATE_BLOCKS_AFTER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_ASSUM(fun th ->
        if can (term_match [] `deflate_codes l ll dl (outk,q) (out,q2)`)
               (concl th)
        then MP_TAC(MATCH_MP DEFLATE_CODES_LENGTH th) THEN
             MP_TAC(MATCH_MP DEFLATE_CODES_BOUND th)
        else failwith "") THEN REPEAT STRIP_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`out:byte list`; `q2:num`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY SIMPLE_ARITH_TAC THEN
      FIXED_TABLES_KEEP_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `~(word_zx(x0v:int64):int32 = word 0)`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(val(word_zx(x0v:int64):int32) = 0)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
      PUFF_STEPS_TAC (6--8) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0; INT_SUB_RZERO]) THEN
      ASM_CASES_TAC `ival(word_zx(x0v:int64):int32) < &0` THEN
      PUFF_STEPS_TAC [9] THENL
       [PUFF_RETURN_TAC (REPEAT DISJ2_TAC) (10--24) NO_DYN_CODES_TAC;
        PUFF_RETURN_TAC (REPEAT DISJ2_TAC) (10--17) NO_DYN_CODES_TAC]];
    PUFF_ESCAPE_TAC (REPEAT DISJ2_TAC) 5 NO_DYN_CODES_AT_ALL_TAC];;

(*** The code length code lengths: loop A reads them in the order of the   ***)
(*** RFC, then loop B zeros the others                                     ***)

let DYN_CLEN_TAC =
  MATCH_MP_TAC(ISPECL [`ncode:num`; dyn_a] ENSURES_LOOP_EXIT) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL
     [BETA_TAC THEN SIMP_TAC[]; SUBSUMED_ID_MAYCHANGE_TAC];
    DYN_A_ITER_TAC;
    BETA_TAC THEN REWRITE_TAC[LT_REFL] THEN
    MATCH_MP_TAC(ISPECL [`19 - ncode`; dyn_b] ENSURES_LOOP_EXIT) THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; DYN_B_ENTRY_TAC;
      DYN_B_ITER_TAC; DYN_B_EXIT_TAC]];;

(*** From the code lengths at 0xe30, the two tables and the call of codes ***)

let DYN_END_TAC =
  ENSURES_EXISTS_PRE_TAC `lens:num list` THEN
  ENSURES_EXISTS_PRE_TAC `q:num` THEN GLOBALIZE_PRECONDITION_TAC THEN
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC dyn_lc THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; DYN_LL_TAC;
    ENSURES_EXISTS_PRE_TAC `lsyms:int16 list` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC dyn_dc THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; DYN_DL_TAC;
      DYN_CODES_TAC]];;

(*** From the table of the code length code at 0xd84: loop C reads the     ***)
(*** code lengths, up to 0xe30                                             ***)

let DYN_LENGTHS_TAC =
  ENSURES_EXISTS_PRE_TAC `cl:num list` THEN
  ENSURES_EXISTS_PRE_TAC `csyms:int16 list` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  ASSUME_TAC(CONV_RULE(RAND_CONV NUM_REDUCE_CONV)
    (ASSUME `huffman_kraft cl <= 2 EXP 15`)) THEN
  SUBGOAL_THEN `ALL (\x. x <= 15) (cl:num list)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x <= 7) (cl:num list)` THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC dyn_lens THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    MATCH_MP_TAC(ISPEC dyn_c ENSURES_WHILE_MEASURE) THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; DYN_C_ENTRY_TAC;
      DYN_C_ITER_TAC];
    DYN_END_TAC];;

(*** A block with dynamic codes, through the points dyn_a0, dyn_cl and     ***)
(*** dyn_ctab, after the case of a header with too many lengths            ***)

let DYN_TAC =
  DYN_ABBREV_TAC THEN
  ASM_CASES_TAC `nlen <= 286 /\ ndist <= 30` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC dyn_a0 THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; DYN_HEAD_TAC;
      MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC dyn_cl THEN
      REPEAT CONJ_TAC THENL
       [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; DYN_CLEN_TAC;
        MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC dyn_ctab THEN
        REPEAT CONJ_TAC THENL
         [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; DYN_CL_TAC;
          DYN_LENGTHS_TAC]]];
    DYN_HEAD_NEG_TAC];;

(* ------------------------------------------------------------------------- *)
(* The loop over the blocks.                                                 *)
(* ------------------------------------------------------------------------- *)

(*** A block of type 3, which is an error ***)

let PUFF_TYPE3_TAC =
  SUBGOAL_THEN `btype = 3` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIXED_TABLES_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN
  PUFF_RETURN_TAC (REPEAT DISJ2_TAC) (1--23) NO_BLOCK_TAC;;

(*** An iteration of the loop over the blocks, from 0xb48: the header,     ***)
(*** up to 0xb68, the block, by its type, and its end at 0xd78             ***)

let PUFF_ITER_TAC =
  PUFF_ITER_INTRO_TAC THEN
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC puff_dispatch THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; PUFF_HEADER_TAC;
    ENSURES_EXISTS_PRE_TAC `last:num` THEN
    ENSURES_EXISTS_PRE_TAC `btype:num` THEN GLOBALIZE_PRECONDITION_TAC THEN
    MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC puff_blockend THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
      ASM_CASES_TAC `btype = 0` THENL
       [STORED_TAC;
        ASM_CASES_TAC `btype = 1` THENL
         [FIXED_TAC;
          ASM_CASES_TAC `btype = 2` THENL [DYN_TAC; PUFF_TYPE3_TAC]]];
      PUFF_BLOCKEND_TAC]];;

(* ------------------------------------------------------------------------- *)
(* The correctness of puff.                                                  *)
(* ------------------------------------------------------------------------- *)

let PUFF_CORRECT = prove
 (`!dest destlen source sourcelen outlen l fs fl ea el ev enc ctx0
    pc returnaddress stackpointer.
     setjmp_contract fs ea el ev enc /\ longjmp_contract fl ea el ev enc /\
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH l < 2 EXP 60 /\ ~(dest = word 0) /\ outlen < 2 EXP 60 /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 2560),2560); (dest,outlen)]
      [(word pc,0x20320); (source,LENGTH l); (destlen,8); (sourcelen,8);
       (ea,el)] /\
     nonoverlapping (word_sub stackpointer (word 2560),2560) (dest,outlen) /\
     ALLPAIRS nonoverlapping [(destlen,8); (sourcelen,8)]
      [(word pc,0x20320); (source,LENGTH l); (ea,el)] /\
     nonoverlapping (destlen,8) (sourcelen,8) /\
     ALLPAIRS nonoverlapping [(source,LENGTH l); (ea,el)]
      [(word pc,0x20320)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0xad0) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               jmp_context s = ctx0 /\
               C_ARGUMENTS [dest; destlen; source; sourcelen] s /\
               read (memory :> bytes64 destlen) s = word outlen /\
               read (memory :> bytes64 sourcelen) s = word(LENGTH l) /\
               read (memory :> bytes(source,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64(word(pc + 0x20000))) s = fs /\
               read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
               read (memory :> bytes(ea,el)) s = ev /\
               puff_fixed_tables pc s)
          (\s. read PC s = returnaddress /\ jmp_context s = ctx0 /\
               puff_fixed_tables pc s /\
               (word_zx(read X0 s):int32 = word 0
                ==> ?out n. deflate_decode l out n /\
                            read (memory :> bytes(dest,LENGTH out)) s =
                            num_of_bytelist out /\
                            read (memory :> bytes64 destlen) s =
                            word(LENGTH out) /\
                            read (memory :> bytes64 sourcelen) s = word n) /\
               (~(word_zx(read X0 s):int32 = word 0)
                ==> ~(?out n. deflate_decode l out n /\ LENGTH out <= outlen)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE_JMP_CONTEXT ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 2560),2560);
                      memory :> bytes(dest,outlen);
                      memory :> bytes(destlen,8); memory :> bytes(sourcelen,8);
                      memory :> bytes(word(pc + 0x20028),4);
                      memory :> bytes(word(pc + 0x20040),0x2dc)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALLPAIRS; ALL] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SPECL [`pc:num`; `0x20000`] WORD_ADD;
              SPECL [`pc:num`; `0x20028`] WORD_ADD;
              SPECL [`pc:num`; `0x20040`] WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC puff_frame THEN
  CONJ_TAC THENL [PUFF_FRAME_TAC; ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE_JMP_CONTEXT;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  JMP_CONTEXT_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC puff_inv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; PUFF_ENTRY_TAC;
    PUFF_ITER_TAC]);;

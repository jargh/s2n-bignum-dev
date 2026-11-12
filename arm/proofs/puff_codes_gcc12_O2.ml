(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function codes(s,lencode,distcode) of puff, at 0x900 in the image,    *)
(* which decodes the data of a block, with the literal/length code given by  *)
(* the table lencode and the distance code given by distcode, from the       *)
(* current position in the stream up to and including the end-of-block       *)
(* symbol, adding the literals and the copies that it gives to the output.   *)
(* It returns 0 at the end of the block, 1 if the output would not fit in    *)
(* the output buffer, -10 for a length symbol 286 or 287, -11 for a distance *)
(* back beyond the start of the output, or the negative value that decode    *)
(* returns if there is no symbol, and decode and bits call longjmp(s->env,1) *)
(* if the input runs out.                                                    *)
(*                                                                           *)
(* In the listing, in hex, 0x830 is decode and 0x7a0 is bits, and x21, x23,  *)
(* x25 and x24 point to the tables of the base lengths, the extra bits of    *)
(* the lengths, the base distances and the extra bits of the distances.      *)
(*                                                                           *)
(* 900: stp   x29, x30, [sp, #-96]!    9e8: bl    0x830 (decode)             *)
(* 904: mov   x29, sp                  9ec: mov   w19, w0                    *)
(* 908: stp   x21, x22, [sp, #32]      9f0: tbnz  w0, #31, 0x998             *)
(* 90c: adrp  x21, 0x1000              9f4: ldrsh w1, [x24, w0, sxtw #1]     *)
(* 910: add   x21, x21, #0xb0          9f8: mov   x0, x28                    *)
(* 914: mov   x22, x2                  9fc: ldrsh w27, [x25, w19, sxtw #1]   *)
(* 918: stp   x19, x20, [sp, #16]      a00: bl    0x7a0 (bits)               *)
(* 91c: mov   x20, x1                  a04: add   w4, w27, w0                *)
(* 920: stp   x23, x24, [sp, #48]      a08: ldr   x2, [x28, #16]             *)
(* 924: add   x23, x21, #0x40          a0c: cmp   x4, x2                     *)
(* 928: add   x24, x21, #0xc0          a10: b.hi  0xac4                      *)
(* 92c: stp   x25, x26, [sp, #64]      a14: ldr   x0, [x28]                  *)
(* 930: add   x25, x21, #0x80          a18: add   x1, x2, w26, sxtw          *)
(* 934: stp   x27, x28, [sp, #80]      a1c: cbnz  x0, 0xa50                  *)
(* 938: mov   x28, x0                  a20: str   x1, [x28, #16]             *)
(* 93c: nop                            a24: cmp   w19, #0x100                *)
(* 940: mov   x1, x20                  a28: b.ne  0x940                      *)
(* 944: mov   x0, x28                  a2c: mov   w19, #0x0                  *)
(* 948: bl    0x830 (decode)           a30: mov   w0, w19                    *)
(* 94c: mov   w19, w0                  a34: ldp   x19, x20, [sp, #16]        *)
(* 950: tbnz  w0, #31, 0x998           a38: ldp   x21, x22, [sp, #32]        *)
(* 954: cmp   w0, #0xff                a3c: ldp   x23, x24, [sp, #48]        *)
(* 958: b.gt  0x9b8                    a40: ldp   x25, x26, [sp, #64]        *)
(* 95c: ldr   x1, [x28]                a44: ldp   x27, x28, [sp, #80]        *)
(* 960: ldr   x0, [x28, #16]           a48: ldp   x29, x30, [sp], #96        *)
(* 964: cbz   x1, 0x97c                a4c: ret                              *)
(* 968: ldr   x2, [x28, #8]            a50: ldr   x3, [x28, #8]              *)
(* 96c: cmp   x2, x0                   a54: cmp   x3, x1                     *)
(* 970: b.eq  0xab4                    a58: b.cc  0xab4                      *)
(* 974: strb  w19, [x1, x0]            a5c: cbz   w26, 0xa24                 *)
(* 978: ldr   x0, [x28, #16]           a60: sub   x3, x2, x4                 *)
(* 97c: add   x0, x0, #0x1             a64: sub   w1, w26, #0x2              *)
(* 980: str   x0, [x28, #16]           a68: ldrb  w3, [x0, x3]               *)
(* 984: mov   x1, x20                  a6c: strb  w3, [x0, x2]               *)
(* 988: mov   x0, x28                  a70: ldr   x3, [x28, #16]             *)
(* 98c: bl    0x830 (decode)           a74: add   x3, x3, #0x1               *)
(* 990: mov   w19, w0                  a78: str   x3, [x28, #16]             *)
(* 994: tbz   w0, #31, 0x954           a7c: cmp   w26, #0x1                  *)
(* 998: ldp   x21, x22, [sp, #32]      a80: b.eq  0xa24                      *)
(* 99c: mov   w0, w19                  a84: nop                              *)
(* 9a0: ldp   x19, x20, [sp, #16]      a88: ldr   x2, [x28]                  *)
(* 9a4: ldp   x23, x24, [sp, #48]      a8c: sub   x0, x3, x4                 *)
(* 9a8: ldp   x25, x26, [sp, #64]      a90: sub   w1, w1, #0x1               *)
(* 9ac: ldp   x27, x28, [sp, #80]      a94: ldrb  w0, [x2, x0]               *)
(* 9b0: ldp   x29, x30, [sp], #96      a98: strb  w0, [x2, x3]               *)
(* 9b4: ret                            a9c: ldr   x3, [x28, #16]             *)
(* 9b8: cmp   w0, #0x100               aa0: add   x3, x3, #0x1               *)
(* 9bc: b.eq  0xa2c                    aa4: str   x3, [x28, #16]             *)
(* 9c0: sub   w19, w0, #0x101          aa8: cmn   w1, #0x1                   *)
(* 9c4: cmp   w19, #0x1c               aac: b.ne  0xa88                      *)
(* 9c8: b.gt  0xabc                    ab0: b     0xa24                      *)
(* 9cc: ldrsh w1, [x23, w19, sxtw #1]  ab4: mov   w19, #0x1                  *)
(* 9d0: mov   x0, x28                  ab8: b     0x998                      *)
(* 9d4: ldrsh w26, [x21, w19, sxtw #1] abc: mov   w19, #0xfffffff6           *)
(* 9d8: bl    0x7a0 (bits)             ac0: b     0x998                      *)
(* 9dc: add   w26, w26, w0             ac4: mov   w19, #0xfffffff5           *)
(* 9e0: mov   x1, x22                  ac8: b     0x998                      *)
(* 9e4: mov   x0, x28                                                        *)
(* ========================================================================= *)

needs "arm/proofs/puff_bits_gcc12_O2.ml";;
needs "arm/proofs/puff_decode_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* The proof is by a loop (ENSURES_WHILE_MEASURE) whose invariant codes_inv  *)
(* n holds at 0x954 with a symbol sym decoded from position pk to qk, and    *)
(* the output so far outk, such that the block data from p with the initial  *)
(* output out0 decodes to the same result as from pk with outk, and the      *)
(* measure n, the number of bits in the stream after qk, decreases with each *)
(* symbol. The end of block returns 0, and a literal is added to the output  *)
(* and the next symbol decoded. A length symbol is followed by its extra     *)
(* bits, the distance symbol and its extra bits, then the first byte of the  *)
(* copy, to reach codes_mid at 0xa88, where a loop with the invariant        *)
(* codes_copy copies the others before the next symbol is decoded. Each      *)
(* other return, and each call of longjmp, is at a point where the block     *)
(* data has no decoding, or none whose output fits in the output buffer.     *)
(* ------------------------------------------------------------------------- *)

(*** The invariant at 0x954, with the measure n ***)

let codes_inv = `\n s.
  ?outk pk sym qk.
   aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
   read PC s = word(pc + 0x954) /\
   read SP s = word_sub stackpointer (word 96) /\
   read X29 s = word_sub stackpointer (word 96) /\
   read X0 s = word sym /\ read X19 s = word sym /\
   read X20 s = lh /\ read X21 s = word_add (word pc) (word 4272) /\
   read X22 s = dh /\ read X23 s = word_add (word pc) (word 4336) /\
   read X24 s = word_add (word pc) (word 4464) /\
   read X25 s = word_add (word pc) (word 4400) /\ read X28 s = st /\
   read (Q8 :> bottomhalf) s = ctx_d8 /\ read (Q9 :> bottomhalf) s = ctx_d9 /\
   read (Q10 :> bottomhalf) s = ctx_d10 /\
   read (Q11 :> bottomhalf) s = ctx_d11 /\
   read (Q12 :> bottomhalf) s = ctx_d12 /\
   read (Q13 :> bottomhalf) s = ctx_d13 /\
   read (Q14 :> bottomhalf) s = ctx_d14 /\
   read (Q15 :> bottomhalf) s = ctx_d15 /\
   read (memory :> bytes64(word_sub stackpointer (word 96))) s = ctx_x29 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 8))) s = returnaddress /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 16))) s = ctx_x19 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 24))) s = ctx_x20 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 32))) s = ctx_x21 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 40))) s = ctx_x22 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 48))) s = ctx_x23 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 56))) s = ctx_x24 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 64))) s = ctx_x25 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 72))) s = ctx_x26 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 80))) s = ctx_x27 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 88))) s = ctx_x28 /\
   read (memory :> bytes64 st) s = outp /\
   read (memory :> bytes64(word_add st (word 8))) s = word outlen /\
   read (memory :> bytes64(word_add st (word 16))) s = word(LENGTH outk) /\
   read (memory :> bytes(outp,LENGTH outk)) s = num_of_bytelist outk /\
   read (memory :> bytes64(word_add st (word 24))) s = inp /\
   read (memory :> bytes64(word_add st (word 32))) s = word(LENGTH l) /\
   read (memory :> bytes64(word_add st (word 40))) s = word((qk + 7) DIV 8) /\
   read (memory :> bytes32(word_add st (word 48))) s =
   word(deflate_bits l qk (8 * ((qk + 7) DIV 8) - qk)) /\
   read (memory :> bytes32(word_add st (word 52))) s =
   word(8 * ((qk + 7) DIV 8) - qk) /\
   read (memory :> bytes(inp,LENGTH l)) s = num_of_bytelist l /\
   read (memory :> bytes64 lh) s = lcnt /\
   read (memory :> bytes64(word_add lh (word 8))) s = lsym /\
   read (memory :> bytes(lcnt,32)) s = num_of_wordlist(lcnts:int16 list) /\
   read (memory :> bytes(lsym,2 * LENGTH(lsyms:int16 list))) s =
   num_of_wordlist lsyms /\
   read (memory :> bytes64 dh) s = dcnt /\
   read (memory :> bytes64(word_add dh (word 8))) s = dsym /\
   read (memory :> bytes(dcnt,32)) s = num_of_wordlist(dcnts:int16 list) /\
   read (memory :> bytes(dsym,2 * LENGTH(dsyms:int16 list))) s =
   num_of_wordlist dsyms /\
   read (memory :> bytes(word_add st (word 56),312)) s =
   (enc:int64 list->num) ctx /\
   read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
   read (memory :> bytes(ea,el)) s = ev /\
   huffman_decode l ll pk sym qk /\ n = 8 * LENGTH l - qk /\
   LENGTH outk <= outlen /\
   (!r. deflate_codes l ll dl (out0,p) r <=>
        deflate_codes l ll dl (outk,pk) r)`;;

(*** The calls of decode with the two tables, and of bits, at position p   ***)
(*** and with the return address ret                                       ***)

let DECODE_LL_VARS p ret =
  [`st:int64`; `lh:int64`; `lcnt:int64`; `lsym:int64`; `ll:num list`;
   `lcnts:int16 list`; `lsyms:int16 list`; `l:byte list`; `inp:int64`;
   p; `fl:int64`; `ea:int64`; `el:num`; `ev:num`;
   `enc:int64 list->num`; `ctx:int64 list`; `ctx0:int64 list`; `pc:num`;
   ret; `word_sub stackpointer (word 96):int64`];;

let DECODE_DL_VARS p ret =
  [`st:int64`; `dh:int64`; `dcnt:int64`; `dsym:int64`; `dl:num list`;
   `dcnts:int16 list`; `dsyms:int16 list`; `l:byte list`; `inp:int64`;
   p; `fl:int64`; `ea:int64`; `el:num`; `ev:num`;
   `enc:int64 list->num`; `ctx:int64 list`; `ctx0:int64 list`; `pc:num`;
   ret; `word_sub stackpointer (word 96):int64`];;

let BITS_VARS need p ret =
  [`st:int64`; need; `l:byte list`; `inp:int64`; p; `fl:int64`; `ea:int64`;
   `el:num`; `ev:num`; `enc:int64 list->num`; `ctx:int64 list`;
   `ctx0:int64 list`; `pc:num`; ret; `word_sub stackpointer (word 96):int64`];;

(*** The returns other than at the end of a block, and the longjmps. With  ***)
(*** CODES_HEAD_ERROR_TAC and CODES_HEAD_ESCAPE_TAC, the postcondition has ***)
(*** codes_mid as an extra disjunct at the front.                          ***)

let CODES_SP_RESTORE = WORD_RULE
  `word_add (word_sub (x:int64) (word 96)) (word 96) = x`;;

let CODES_RETURN_TAC tac =
  ASM_REWRITE_TAC[jmp_context] THEN REWRITE_TAC[CODES_SP_RESTORE] THEN
  DISJ1_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN tac;;

let CODES_ERROR_TAC steps tac =
  PUFF_STEPS_TAC steps THEN ENSURES_FINAL_STATE_TAC THEN
  DISJ2_TAC THEN CODES_RETURN_TAC tac;;

let CODES_HEAD_ERROR_TAC steps tac =
  PUFF_STEPS_TAC steps THEN ENSURES_FINAL_STATE_TAC THEN
  DISJ2_TAC THEN DISJ2_TAC THEN CODES_RETURN_TAC tac;;

let CODES_ESCAPE_TAC tac =
  ENSURES_FINAL_STATE_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  ASM_REWRITE_TAC[jmp_context] THEN tac;;

let CODES_HEAD_ESCAPE_TAC tac =
  ENSURES_FINAL_STATE_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  ASM_REWRITE_TAC[jmp_context] THEN tac;;

(*** From the entry to 0x954 after the first symbol ***)

let CODES_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--18) THEN PUFF_ADRP_TAC THEN
  PUFF_STEPS_TAC [19] THEN
  PUFF_CALL_TAC PUFF_DECODE_CORRECT
    (DECODE_LL_VARS `p:num` `word(pc + 2380):int64`) 20 THENL
   [DECODE_FACTS_TAC `p:num` THEN
    PUFF_STEPS_TAC (21--22) THEN BIT31_DECIDE_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `8 * LENGTH(l:byte list) - q` THEN BETA_TAC THEN
    MAP_EVERY EXISTS_TAC [`out0:byte list`; `p:num`; `c:num`; `q:num`] THEN
    ASM_REWRITE_TAC[];
    ABBREV_TAC `x0v = read X0 s20` THEN
    CODES_ERROR_TAC (21--30)
     (MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                     `out0:byte list`; `p:num`] DEFLATE_CODES_NODECODE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]);
    CODES_ESCAPE_TAC
     (MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                     `out0:byte list`; `p:num`] DEFLATE_CODES_NODECODE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[])];;

(*** An iteration, from codes_inv n for the symbol sym from pk to qk ***)

let CODES_ITER_INTRO_TAC =
  X_GEN_TAC `n:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `outk:byte list` THEN
  ENSURES_EXISTS_PRE_TAC `pk:num` THEN
  ENSURES_EXISTS_PRE_TAC `sym:num` THEN
  ENSURES_EXISTS_PRE_TAC `qk:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN DECODE_FACTS_TAC `pk:num`;;

(*** The end of the block ***)

let CODES_END_TAC =
  PUFF_STEPS_TAC (1--13) THEN ENSURES_FINAL_STATE_TAC THEN
  DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[jmp_context] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[CODES_SP_RESTORE] THEN
  MAP_EVERY EXISTS_TAC [`outk:byte list`; `qk:num`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `outk:byte list`; `pk:num`; `qk:num`] DEFLATE_CODES_END) THEN
  UNDISCH_TAC `huffman_decode l ll pk sym qk` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[];;

(*** A literal, which does not fit in the output, or which is added to it  ***)
(*** before the next symbol is decoded                                     ***)

let LIT_NODECODE_TAC =
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`out:byte list`; `q:num`] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `outk:byte list`; `pk:num`; `sym:num`; `qk:num`;
                 `(out:byte list),(q:num)`] DEFLATE_CODES_LITERAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `APPEND outk [word sym:byte]`; `qk:num`]
                DEFLATE_CODES_NODECODE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[];;

let CODES_LITERAL_TAC =
  SUBGOAL_THEN `~(val(outp:int64) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
  PUFF_STEPS_TAC (1--7) THEN
  ASM_CASES_TAC `LENGTH(outk:byte list) = outlen` THEN
  PTR_DECIDE_FLAGS_TAC THENL
   [PUFF_STEPS_TAC [8] THEN
    CODES_ERROR_TAC (9--18)
     (REWRITE_TAC[NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`out:byte list`; `q:num`] THEN
      MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                     `outk:byte list`; `pk:num`; `sym:num`; `qk:num`;
                     `(out:byte list),(q:num)`] DEFLATE_CODES_LITERAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP DEFLATE_CODES_LENGTH) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN SIMPLE_ARITH_TAC);
    PUFF_STEPS_TAC (8--15) THEN
    MP_TAC(ISPECL [`outp:int64`; `outk:byte list`; `word sym:byte`;
                   `s15:armstate`] READ_MEMORY_BYTELIST_SNOC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    PUFF_CALL_TAC PUFF_DECODE_CORRECT
      (DECODE_LL_VARS `qk:num` `word(pc + 2448):int64`) 16 THENL
     [DECODE_FACTS_TAC `qk:num` THEN
      PUFF_STEPS_TAC (17--18) THEN BIT31_DECIDE_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `8 * LENGTH(l:byte list) - q` THEN BETA_TAC THEN
      CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC
       [`APPEND outk [word sym:byte]`; `qk:num`; `c:num`; `q:num`] THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
      REWRITE_TAC[ADD1] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SIMPLE_ARITH_TAC;
        GEN_TAC THEN MATCH_MP_TAC DEFLATE_CODES_LITERAL THEN
        ASM_REWRITE_TAC[]];
      ABBREV_TAC `x0v = read X0 s16` THEN
      CODES_ERROR_TAC (17--26) LIT_NODECODE_TAC;
      CODES_ESCAPE_TAC LIT_NODECODE_TAC]];;

(*** The state in the copy loop at 0xa88 when i + 1 bytes have been        ***)
(*** copied, for a copy of len bytes from dst back, with the distance      ***)
(*** symbol c, and with the stream read up to position q2                  ***)

let codes_copy_state = `
   read SP s = word_sub stackpointer (word 96) /\
   read X29 s = word_sub stackpointer (word 96) /\
   read X19 s = word c /\
   read X20 s = lh /\ read X21 s = word_add (word pc) (word 4272) /\
   read X22 s = dh /\ read X23 s = word_add (word pc) (word 4336) /\
   read X24 s = word_add (word pc) (word 4464) /\
   read X25 s = word_add (word pc) (word 4400) /\ read X28 s = st /\
   read X3 s = word(LENGTH outk + i + 1) /\ read X4 s = word dst /\
   (i < len - 1 ==> read X1 s = word(len - 2 - i)) /\
   read (Q8 :> bottomhalf) s = ctx_d8 /\ read (Q9 :> bottomhalf) s = ctx_d9 /\
   read (Q10 :> bottomhalf) s = ctx_d10 /\
   read (Q11 :> bottomhalf) s = ctx_d11 /\
   read (Q12 :> bottomhalf) s = ctx_d12 /\
   read (Q13 :> bottomhalf) s = ctx_d13 /\
   read (Q14 :> bottomhalf) s = ctx_d14 /\
   read (Q15 :> bottomhalf) s = ctx_d15 /\
   read (memory :> bytes64(word_sub stackpointer (word 96))) s = ctx_x29 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 8))) s = returnaddress /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 16))) s = ctx_x19 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 24))) s = ctx_x20 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 32))) s = ctx_x21 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 40))) s = ctx_x22 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 48))) s = ctx_x23 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 56))) s = ctx_x24 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 64))) s = ctx_x25 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 72))) s = ctx_x26 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 80))) s = ctx_x27 /\
   read (memory :> bytes64(word_add (word_sub stackpointer (word 96))
                                    (word 88))) s = ctx_x28 /\
   read (memory :> bytes64 st) s = outp /\
   read (memory :> bytes64(word_add st (word 8))) s = word outlen /\
   read (memory :> bytes64(word_add st (word 16))) s =
   word(LENGTH outk + i + 1) /\
   read (memory :> bytes(outp,LENGTH outk + i + 1)) s =
   num_of_bytelist(lz77_copy outk dst (i + 1)) /\
   read (memory :> bytes64(word_add st (word 24))) s = inp /\
   read (memory :> bytes64(word_add st (word 32))) s = word(LENGTH l) /\
   read (memory :> bytes64(word_add st (word 40))) s = word((q2 + 7) DIV 8) /\
   read (memory :> bytes32(word_add st (word 48))) s =
   word(deflate_bits l q2 (8 * ((q2 + 7) DIV 8) - q2)) /\
   read (memory :> bytes32(word_add st (word 52))) s =
   word(8 * ((q2 + 7) DIV 8) - q2) /\
   read (memory :> bytes(inp,LENGTH l)) s = num_of_bytelist l /\
   read (memory :> bytes64 lh) s = lcnt /\
   read (memory :> bytes64(word_add lh (word 8))) s = lsym /\
   read (memory :> bytes(lcnt,32)) s = num_of_wordlist(lcnts:int16 list) /\
   read (memory :> bytes(lsym,2 * LENGTH(lsyms:int16 list))) s =
   num_of_wordlist lsyms /\
   read (memory :> bytes64 dh) s = dcnt /\
   read (memory :> bytes64(word_add dh (word 8))) s = dsym /\
   read (memory :> bytes(dcnt,32)) s = num_of_wordlist(dcnts:int16 list) /\
   read (memory :> bytes(dsym,2 * LENGTH(dsyms:int16 list))) s =
   num_of_wordlist dsyms /\
   read (memory :> bytes(word_add st (word 56),312)) s =
   (enc:int64 list->num) ctx /\
   read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
   read (memory :> bytes(ea,el)) s = ev`;;

(*** The invariant of the copy loop, with the flag tested at 0xaac ***)

let codes_copy = mk_abs(`i:num`,mk_abs(`s:armstate`,
  mk_conj(codes_copy_state,`read ZF s <=> i = len - 1`)));;

(*** At 0xa88 after the first byte is copied, with facts about the copy ***)

let codes_mid = mk_abs(`s:armstate`,
  list_mk_exists([`len:num`; `c:num`; `dst:num`; `q2:num`],
   list_mk_conj
    [`3 <= len /\ len < 2 EXP 9 /\ c < 30 /\ 1 <= dst /\
      dst <= LENGTH(outk:byte list) /\ LENGTH outk + len <= outlen /\
      qk < q2 /\ q2 <= 8 * LENGTH(l:byte list) /\
      (!r. deflate_codes l ll dl (out0,p) r <=>
           deflate_codes l ll dl (lz77_copy outk dst len,q2) r)`;
     `aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc`;
     `read PC s = word(pc + 0xa88)`;
     rhs(concl(REWRITE_CONV[ADD_CLAUSES; SUB_0; ARITH_RULE `0 + 1 = 1`]
                (subst [`0`,`i:num`] codes_copy_state)))]));;

(*** No decoding: with no length/distance pair at pk, with no distance     ***)
(*** symbol, with the extra bits of the distance beyond the input, with    ***)
(*** the distance back beyond the start of the output, and with the copy   ***)
(*** too long for the output buffer                                        ***)

let LENDIST_NO_TAC =
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`out:byte list`; `q:num`] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `outk:byte list`; `pk:num`; `sym:num`; `qk:num`;
                 `(out:byte list),(q:num)`] DEFLATE_CODES_LENDIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`; `pk:num`;
                 `sym:num`; `qk:num`] DEFLATE_LENDIST_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP HUFFMAN_DECODE_POS o check
    (fun th -> can (term_match [] `huffman_decode l dl x d p2`)
                   (concl th)))) THEN
  SIMPLE_ARITH_TAC;;

let is_hdecode t =
  can (find_term (fun u -> is_const u && fst(dest_const u) = "huffman_decode"))
      t;;

let LENDIST_NODIST_TAC =
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`out:byte list`; `q:num`] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `outk:byte list`; `pk:num`; `sym:num`; `qk:num`;
                 `(out:byte list),(q:num)`] DEFLATE_CODES_LENDIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`; `pk:num`;
                 `sym:num`; `qk:num`] DEFLATE_LENDIST_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `huffman_decode l dl x d p2`) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_neg(concl th) && is_hdecode(concl th) &&
    free_in `dl:num list` (concl th))) THEN
  MESON_TAC[];;

let LENDIST_NO_UNIQ_TAC =
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`out:byte list`; `q':num`] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `outk:byte list`; `pk:num`; `sym:num`; `qk:num`;
                 `(out:byte list),(q':num)`] DEFLATE_CODES_LENDIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`; `pk:num`;
                 `sym:num`; `qk:num`] DEFLATE_LENDIST_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  STRIP_TAC THEN REPEAT HUFFMAN_UNIQUE_TAC THEN SIMPLE_ARITH_TAC;;

let COPY_FAR_TAC =
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`out:byte list`; `q':num`] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `outk:byte list`; `pk:num`; `sym:num`; `qk:num`; `c:num`;
                 `q:num`; `(out:byte list),(q':num)`] DEFLATE_CODES_COPY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[];;

let COPY_OVERFLOW_TAC =
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`out:byte list`; `q':num`] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `outk:byte list`; `pk:num`; `sym:num`; `qk:num`; `c:num`;
                 `q:num`; `(out:byte list),(q':num)`] DEFLATE_CODES_COPY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DEFLATE_CODES_LENGTH) THEN
  REWRITE_TAC[LENGTH_LZ77_COPY] THEN SIMPLE_ARITH_TAC;;

(*** For a length symbol, from 0x954 to codes_mid at 0xa88 ***)

let CODES_LENGTH_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--6) THEN
  ASM_CASES_TAC `sym - 257 <= 28` THEN W32_DECIDE_FLAGS_TAC THENL
   [ALL_TAC; CODES_HEAD_ERROR_TAC (7--17) LENDIST_NO_TAC] THEN
  SXTW_ABBREV_TAC `X19` `w19v:int64` `sym - 257` THEN PUFF_STEPS_TAC [7] THEN
  TABLE_ELEMENT_TAC 4336 29 `deflate_length_extra` `sym - 257` `s7:armstate`
  THEN
  TABLE_ELEMENT_TAC 4272 29 `deflate_length_base` `sym - 257` `s7:armstate`
  THEN
  MP_TAC(SPEC `sym - 257` (CONJUNCT1 DEFLATE_TABLE_BOUNDS)) THEN
  MP_TAC(SPEC `sym - 257` (CONJUNCT1(CONJUNCT2 DEFLATE_TABLE_BOUNDS))) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  PUFF_STEPS_TAC (8--11) THEN
  PUFF_CALL_TAC PUFF_BITS_CORRECT
    (BITS_VARS `EL (sym - 257) deflate_length_extra` `qk:num`
               `word(pc + 2524):int64`) 12 THENL
   [ALL_TAC; CODES_HEAD_ESCAPE_TAC LENDIST_NO_TAC] THEN
  SUBGOAL_THEN `deflate_bits l qk (EL (sym - 257) deflate_length_extra) < 32`
  ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (EL (sym - 257) deflate_length_extra)` THEN
    REWRITE_TAC[DEFLATE_BITS_BOUND; ARITH_RULE `32 = 2 EXP 5`; LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PUFF_STEPS_TAC (13--16) THEN
  PUFF_CALL_TAC PUFF_DECODE_CORRECT
    (DECODE_DL_VARS `qk + EL (sym - 257) deflate_length_extra`
                    `word(pc + 2540):int64`) 17 THENL
   [ALL_TAC;
    ABBREV_TAC `x0v = read X0 s17` THEN
    CODES_HEAD_ERROR_TAC (18--27) LENDIST_NODIST_TAC;
    CODES_HEAD_ESCAPE_TAC LENDIST_NODIST_TAC] THEN
  DECODE_FACTS_TAC `qk + EL (sym - 257) deflate_length_extra` THEN
  PUFF_STEPS_TAC [18] THEN PUFF_STEPS_TAC [19] THEN BIT31_DECIDE_TAC THEN
  MP_TAC(SPEC `c:num`
    (CONJUNCT1(CONJUNCT2(CONJUNCT2 DEFLATE_TABLE_BOUNDS)))) THEN
  MP_TAC(SPEC `c:num`
    (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 DEFLATE_TABLE_BOUNDS))))) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  TABLE_ELEMENT_TAC 4464 30 `deflate_dist_extra` `c:num` `s19:armstate` THEN
  TABLE_ELEMENT_TAC 4400 30 `deflate_dist_base` `c:num` `s19:armstate` THEN
  SXTW_ABBREV_TAC `X0` `w0d:int64` `c:num` THEN
  PUFF_STEPS_TAC (20--23) THEN
  PUFF_CALL_TAC PUFF_BITS_CORRECT
    (BITS_VARS `EL c deflate_dist_extra` `q:num` `word(pc + 2564):int64`) 24
  THENL [ALL_TAC; CODES_HEAD_ESCAPE_TAC LENDIST_NO_UNIQ_TAC] THEN
  SUBGOAL_THEN `deflate_bits l q (EL c deflate_dist_extra) < 8192`
  ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (EL c deflate_dist_extra)` THEN
    REWRITE_TAC[DEFLATE_BITS_BOUND; ARITH_RULE `8192 = 2 EXP 13`; LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(val(outp:int64) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
  PUFF_STEPS_TAC (25--27) THEN
  ABBREV_TAC `dst = EL c deflate_dist_base +
                    deflate_bits l q (EL c deflate_dist_extra)` THEN
  ABBREV_TAC `len = EL (sym - 257) deflate_length_base +
                    deflate_bits l qk
                     (EL (sym - 257) deflate_length_extra)` THEN
  SUBGOAL_THEN `LENGTH(outk:byte list) < 2 EXP 60` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dst <= 2 EXP 15 /\ 1 <= dst` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dst" THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `len < 2 EXP 9 /\ 3 <= len` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "len" THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `dst <= LENGTH(outk:byte list)` THEN
  PUFF_STEPS_TAC [28] THENL
   [ALL_TAC; CODES_HEAD_ERROR_TAC (29--38) COPY_FAR_TAC] THEN
  PUFF_STEPS_TAC (29--31) THEN
  ASM_CASES_TAC `LENGTH(outk:byte list) + len <= outlen` THEN
  PUFF_STEPS_TAC (32--34) THENL
   [ALL_TAC; CODES_HEAD_ERROR_TAC (35--44) COPY_OVERFLOW_TAC] THEN
  PUFF_STEPS_TAC (35--37) THEN
  MP_TAC(ISPECL [`outp:int64`; `outk:byte list`;
                 `LENGTH(outk:byte list) - dst`; `s37:armstate`]
                READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  PUFF_STEPS_TAC (38--39) THEN
  MP_TAC(ISPECL [`outp:int64`; `outk:byte list`;
                 `EL (LENGTH outk - dst) outk:byte`; `s39:armstate`]
                READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN
  MP_TAC(ISPECL [`0`; `outk:byte list`; `dst:num`] LZ77_COPY_SNOC) THEN
  REWRITE_TAC[ADD_CLAUSES; lz77_copy] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  PUFF_STEPS_TAC (40--45) THEN
  ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`len:num`; `c:num`; `dst:num`; `q + EL c deflate_dist_extra`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;
    SIMPLE_ARITH_TAC;
    GEN_TAC THEN
    MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                   `outk:byte list`; `pk:num`; `sym:num`; `qk:num`; `c:num`;
                   `q:num`; `r:byte list#num`] DEFLATE_CODES_COPY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[]];;

(*** From codes_mid, the copy loop, then the next symbol ***)

let COPY_NODECODE_TAC =
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MP_TAC(ISPECL [`l:byte list`; `ll:num list`; `dl:num list`;
                 `lz77_copy outk dst len:byte list`; `q2:num`]
                DEFLATE_CODES_NODECODE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[];;

let CODES_COPY_TAC =
  ENSURES_EXISTS_PRE_TAC `len:num` THEN ENSURES_EXISTS_PRE_TAC `c:num` THEN
  ENSURES_EXISTS_PRE_TAC `dst:num` THEN ENSURES_EXISTS_PRE_TAC `q2:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  UNDISCH_THEN
   `!r. deflate_codes l ll dl (out0,p) r <=> deflate_codes l ll dl (outk,pk) r`
   (K ALL_TAC) THEN
  SUBGOAL_THEN `~(len - 1 = 0)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `len - 1` `pc + 0xa88` `pc + 0xaac` codes_copy THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SIMP_TAC[];
      SUBSUMED_ID_MAYCHANGE_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(ASSUME_TAC o C MP (ASSUME `i < len - 1`)) THEN
    MP_TAC(ISPECL [`outp:int64`; `lz77_copy outk dst (i + 1):byte list`;
                   `(LENGTH(outk:byte list) + i + 1) - dst`; `s0:armstate`]
                  READ_MEMORY_BYTES8_BYTELIST) THEN
    REWRITE_TAC[LENGTH_LZ77_COPY] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    PUFF_STEPS_TAC (1--9) THEN
    MP_TAC(ISPECL [`outp:int64`; `lz77_copy outk dst (i + 1):byte list`;
                   `EL ((LENGTH(outk:byte list) + i + 1) - dst)
                       (lz77_copy outk dst (i + 1)):byte`; `s9:armstate`]
                  READ_MEMORY_BYTELIST_SNOC) THEN
    REWRITE_TAC[LENGTH_LZ77_COPY] THEN ASM_REWRITE_TAC[WORD_VAL] THEN
    MP_TAC(ISPECL [`i + 1`; `outk:byte list`; `dst:num`] LZ77_COPY_SNOC) THEN
    REWRITE_TAC[LENGTH_LZ77_COPY] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[ARITH_RULE
     `LENGTH(outk:byte list) + (i + 1) + 1 = (LENGTH outk + i + 1) + 1`] THEN
    ASM_REWRITE_TAC[WORD_ZX_ZX_32_64] THEN
    REWRITE_TAC[WORD_RULE `word_add (word_sub (x:int32) y) y = x`] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      SIMPLE_ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(ASSUME_TAC o C MP (ASSUME `i < len - 1`)) THEN
    PUFF_STEPS_TAC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(len - 1) + 1 = len` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--7) THEN
    PUFF_CALL_TAC PUFF_DECODE_CORRECT
      (DECODE_LL_VARS `q2:num` `word(pc + 2380):int64`) 8 THENL
     [DECODE_FACTS_TAC `q2:num` THEN
      PUFF_STEPS_TAC (9--10) THEN BIT31_DECIDE_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `8 * LENGTH(l:byte list) - q` THEN BETA_TAC THEN
      CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC
       [`lz77_copy outk dst len:byte list`; `q2:num`; `c':num`; `q:num`] THEN
      ASM_REWRITE_TAC[LENGTH_LZ77_COPY];
      ABBREV_TAC `x0v = read X0 s8` THEN
      CODES_ERROR_TAC (9--18) COPY_NODECODE_TAC;
      CODES_ESCAPE_TAC COPY_NODECODE_TAC]];;

(*** A length symbol, or 286 or 287 ***)

let CODES_LENGTH_TAC =
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC codes_mid THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    CODES_LENGTH_HEAD_TAC; CODES_COPY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Given the state at st, with the stream read up to position p and the      *)
(* output so far out0, and the tables at lh and dh for the codes with code   *)
(* lengths ll and dl, either codes returns 0, and the block data from p      *)
(* decodes with the output that it leaves, which fits in the output buffer,  *)
(* reading up to the end of the block, or there is no decoding, or none      *)
(* whose output fits in the output buffer, and codes returns another value,  *)
(* or calls longjmp with the context ctx saved in the jmp_buf of the state   *)
(* if there is no decoding.                                                  *)
(* ------------------------------------------------------------------------- *)

let PUFF_CODES_CORRECT = prove
 (`!st lh lcnt lsym ll lcnts lsyms dh dcnt dsym dl dcnts dsyms
    l inp p outp outlen out0 fl ea el ev enc ctx ctx0
    pc returnaddress stackpointer.
     longjmp_contract fl ea el ev enc /\
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     p <= 8 * LENGTH l /\ LENGTH l < 2 EXP 60 /\
     ~(outp = word 0) /\ LENGTH out0 <= outlen /\ outlen < 2 EXP 60 /\
     ALL (\n. n <= 15) ll /\ LENGTH ll <= 288 /\
     huffman_kraft ll <= 2 EXP 15 /\ huffman_table ll lcnts lsyms /\
     LENGTH lsyms <= 320 /\
     ALL (\n. n <= 15) dl /\ LENGTH dl <= 30 /\
     huffman_kraft dl <= 2 EXP 15 /\ huffman_table dl dcnts dsyms /\
     LENGTH dsyms <= 320 /\
     ALLPAIRS nonoverlapping
      [(word_sub stackpointer (word 112),112); (outp,outlen)]
      [(word pc,0x20320); (st,368); (inp,LENGTH l); (lh,16); (lcnt,32);
       (lsym,2 * LENGTH lsyms); (dh,16); (dcnt,32); (dsym,2 * LENGTH dsyms);
       (ea,el)] /\
     nonoverlapping (word_sub stackpointer (word 112),112) (outp,outlen) /\
     ALLPAIRS nonoverlapping [(st,368)]
      [(word pc,0x20320); (inp,LENGTH l); (lh,16); (lcnt,32);
       (lsym,2 * LENGTH lsyms); (dh,16); (dcnt,32); (dsym,2 * LENGTH dsyms)] /\
     nonoverlapping (ea,el) (word_add st (word 16),8) /\
     nonoverlapping (ea,el) (word_add st (word 40),16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0x900) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               jmp_context s = ctx0 /\
               C_ARGUMENTS [st; lh; dh] s /\
               puff_output st outp outlen out0 s /\
               puff_input st inp l p s /\
               puff_table lh lcnt lsym lcnts lsyms s /\
               puff_table dh dcnt dsym dcnts dsyms s /\
               read (memory :> bytes(word_add st (word 56),312)) s = enc ctx /\
               read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\ jmp_context s = ctx0 /\
               (word_zx(read X0 s):int32 = word 0
                ==> ?out q. deflate_codes l ll dl (out0,p) (out,q) /\
                            LENGTH out <= outlen /\
                            puff_input st inp l q s /\
                            puff_output st outp outlen out s) /\
               (~(word_zx(read X0 s):int32 = word 0)
                ==> ~(?out q. deflate_codes l ll dl (out0,p) (out,q) /\
                              LENGTH out <= outlen)) \/
               read PC s = EL 11 ctx /\ jmp_context s = ctx /\
               word_zx(read X0 s):int32 = word 1 /\
               ~(?out q. deflate_codes l ll dl (out0,p) (out,q)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE_JMP_CONTEXT ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 96),96);
                      memory :> bytes(word_sub stackpointer (word 112),16);
                      memory :> bytes(word_add st (word 16),8);
                      memory :> bytes(word_add st (word 40),16);
                      memory :> bytes(outp,outlen)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALLPAIRS; ALL] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; puff_input; puff_output; puff_table;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE_JMP_CONTEXT;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  JMP_CONTEXT_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC codes_inv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; CODES_ENTRY_TAC;
    CODES_ITER_INTRO_TAC THEN
    ASM_CASES_TAC `sym = 256` THENL
     [ENSURES_INIT_TAC "s0" THEN CODES_END_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `sym < 256` THENL
     [ENSURES_INIT_TAC "s0" THEN CODES_LITERAL_TAC; CODES_LENGTH_TAC]]);;

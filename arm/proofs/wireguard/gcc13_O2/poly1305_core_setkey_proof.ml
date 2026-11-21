(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of poly1305_core_setkey_spec.ml: with the key as the *)
(* 128-bit word of its two 64-bit halves, the limbs of r and their products  *)
(* with 20 are bit-level functions of the halves, as the code computes them. *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_setkey_spec.ml";;

let WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "poly1305_core_setkey"];;

(* ------------------------------------------------------------------------- *)
(* The 128-bit word of two words, and the limbs of a 128-bit value as        *)
(* bit-level functions of it.                                                *)
(* ------------------------------------------------------------------------- *)

let SK_JOIN = prove
 (`!(t0:int64) (t1:int64).
     word(val t0 + 2 EXP 64 * val t1):int128 = word_join t1 t0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_JOIN;
    DIMINDEX_64; DIMINDEX_128] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SK_LIMBS = prove
 (`!x:int128.
     word(val x MOD 17592186044416):int64 =
     word_zx(word_and x (word 17592186044415)) /\
     word((val x DIV 17592186044416) MOD 17592186044416):int64 =
     word_zx(word_and (word_ushr x 44) (word 17592186044415)) /\
     word(val x DIV 309485009821345068724781056):int64 =
     word_zx(word_ushr x 88) /\
     word(20 * (val x DIV 17592186044416) MOD 17592186044416):int64 =
     word_mul (word 20)
       (word_zx(word_and (word_ushr x 44) (word 17592186044415))) /\
     word(20 * val x DIV 309485009821345068724781056):int64 =
     word_mul (word 20) (word_zx(word_ushr x 88))`,
  GEN_TAC THEN REWRITE_TAC[word_zx; WORD_MUL] THEN
  REWRITE_TAC[ARITH_RULE `17592186044415 = 2 EXP 44 - 1`;
              VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`key:int64`; `raw:int64`; `kb:byte list`; `pc:num`;
                       `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES; poly1305_key_at] THEN
  STRIP_TAC THEN
  ABBREV_TAC `t0w:int64 = word(num_of_bytelist(SUB_LIST(0,8) kb))` THEN
  ABBREV_TAC `t1w:int64 = word(num_of_bytelist(SUB_LIST(8,8) kb))` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`raw:int64`; `kb:byte list`; `16`; `0`; `s0:armstate`]
         WG_READ_BYTES64_BYTELIST) THEN
  MP_TAC(ISPECL [`raw:int64`; `kb:byte list`; `16`; `8`; `s0:armstate`]
         WG_READ_BYTES64_BYTELIST) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN
  ARM_STEPS_TAC WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `poly1305_r kb =
    val(word_and (word_join (t1w:int64) (t0w:int64):int128)
                 (word 21267647620597763993911028882763415551))`
  SUBST1_TAC THENL
   [REWRITE_TAC[poly1305_r] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM SK_JOIN] THEN AP_TERM_TAC THEN
    REWRITE_TAC[WG_SUB_LIST_16; WG_NUM_OF_BYTELIST_APPEND] THEN
    SUBGOAL_THEN `LENGTH(SUB_LIST(0,8) (kb:byte list)) = 8 /\
                  LENGTH(SUB_LIST(0 + 8,8) (kb:byte list)) = 8`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[SYM(ASSUME
      `word(num_of_bytelist(SUB_LIST(0,8) kb)):int64 = t0w`);
                SYM(ASSUME
      `word(num_of_bytelist(SUB_LIST(8,8) kb)):int64 = t1w`)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    ASM_SIMP_TAC[WG_VAL_WORD_BYTES8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[SK_LIMBS] THEN
  REPEAT CONJ_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC);;

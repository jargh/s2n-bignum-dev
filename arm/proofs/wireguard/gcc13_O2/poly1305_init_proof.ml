(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of poly1305_init_spec.ml: the four 32-bit words of s *)
(* are copied, buflen and the accumulator zeroed, and poly1305_core_setkey   *)
(* is simulated with its theorem for the first 16 bytes of the key.          *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/poly1305_init_spec.ml";;

let WIREGUARD_POLY1305_INIT_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "poly1305_init"];;

let PI_SETKEY_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_POLY1305_INIT_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_POLY1305_INIT_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC [`desc:int64`; `key:int64`; `k:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of s, buflen and the accumulator ***)

  MAP_EVERY (fun i -> MP_TAC(ISPECL [`key:int64`; `k:byte list`; `32`;
               mk_small_numeral i; `s0:armstate`] WG_READ_BYTES32_BYTELIST))
   [16; 20; 24; 28] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  ARM_STEPS_TAC EXEC (1--16) THEN

  (*** poly1305_core_setkey for the first 16 bytes of the key ***)

  MP_TAC(ISPECL [`key:int64`; `k:byte list`; `32`; `0`; `16`; `s16:armstate`]
         WG_READ_BYTES_SUBLIST) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,16) (k:byte list)) = 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  PI_SETKEY_TAC [`read X0 s`; `read X1 s`; `SUB_LIST(0,16) (k:byte list)`;
                 `pc:num`; `read X30 s`] 17 THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o
    REWRITE_RULE[poly1305_key_at; POLY1305_R_SUB_LIST; GSYM WORD_ADD_ASSOC;
                 GSYM WORD_ADD]) THEN
  ARM_STEPS_TAC EXEC (18--19) THEN ENSURES_FINAL_STATE_TAC THEN

  (*** The state ***)

  REWRITE_TAC[poly1305_desc_at; poly1305_h_at; poly1305_key_at; LENGTH] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[poly1305_kacc] THEN
  ASM_REWRITE_TAC[VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WG_BYTES16_SPLIT32; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; SUB_LIST_CLAUSES;
                num_of_bytelist];
    REWRITE_TAC[WG_WORD_ZX_ZX] THEN
    SUBGOAL_THEN `!i. i + 4 <= 32 ==> LENGTH(SUB_LIST(i,4) (k:byte list)) = 4`
    ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[WG_VAL_WORD_BYTES4; ARITH] THEN
    MP_TAC(SPECL [`k:byte list`; `16`] WG_NUM_OF_BYTELIST_SUB16) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

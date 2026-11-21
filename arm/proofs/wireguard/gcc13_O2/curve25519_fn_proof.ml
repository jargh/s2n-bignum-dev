(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of curve25519_fn_spec.ml: the call of                *)
(* curve25519_generic through the PLT is simulated with its contract and     *)
(* that of __crypto_memneq with its theorem, the zero point being read from  *)
(* the image.                                                                *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/curve25519_fn_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/rodata.ml";;

let WIREGUARD_CURVE25519_FN_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "curve25519_fn"; layout_range "plt_curve25519_generic"];;

let CURVE25519_FN_MEMNEQ_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_CURVE25519_FN_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_CURVE25519_FN_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `scalar:int64`; `point:int64`; `sb:byte list`;
    `pb:byte list`; `cfn:int64`; `ea3:int64`; `el3:num`; `ev3:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1248 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "curve25519" o REWRITE_RULE[curve25519_generic_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_curve25519_generic:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 1216):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[WORD_ADD] o
              MATCH_MP WG_CURVE25519_NULL_POINT_LOADED) THEN

  (*** X25519 by curve25519_generic ***)

  ARM_STEPS_TAC EXEC (1--5) THEN
  WG_PLT_TAC EXEC 5 THEN
  WG_CALL_TAC "curve25519" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `sb:byte list`; `pb:byte list`;
    `read SP s`; `read X30 s`] 10 THEN

  (*** The comparison with the zero point ***)

  ARM_STEPS_TAC EXEC (11--13) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (14--15) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  CURVE25519_FN_MEMNEQ_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(wg_dh sb pb)`;
    `0`; `pc:num`; `read X30 s`] 16 THEN
  ABBREV_TAC `res = read X0 s16` THEN
  ARM_STEPS_TAC EXEC (17--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_EQ_0; LENGTH_WG_DH; wg_zero32] THEN
  COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

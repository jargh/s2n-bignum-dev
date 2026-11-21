(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of hchacha_block_spec.ml: the frame record, the call *)
(* of hchacha_block_generic (simulated with its theorem) and the return.     *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/hchacha_block_spec.ml";;

let WIREGUARD_HCHACHA_BLOCK_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "hchacha_block"];;

let HCHACHA_BLOCK_GENERIC_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_HCHACHA_BLOCK_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let WIREGUARD_HCHACHA_BLOCK_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_HCHACHA_BLOCK_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_HCHACHA_BLOCK_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `out:int64`; `xs:num->int32`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 112 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 96):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  ARM_STEPS_TAC EXEC (1--3) THEN
  SUBGOAL_THEN
   `!i. i < 16
        ==> read (memory :> bytes32(word_add st (word(4 * i)))) s3 = xs i`
  ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  HCHACHA_BLOCK_GENERIC_TAC
   [`read X0 s`; `read X1 s`; `xs:num->int32`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `pc:num`; `read SP s`; `read X30 s`] 4 THEN
  ARM_STEPS_TAC EXEC (5--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of message_ephemeral_spec.ml: in the two cases of    *)
(* the test of dst = src, the copy (inlined, 16 bytes at a time) and the     *)
(* calls of mix_hash and kdf (with one output) simulated with their          *)
(* theorems.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/message_ephemeral_spec.ml";;

let WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "message_ephemeral"];;

let MESSAGE_EPHEMERAL_MIX_HASH_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* kdf with the output d1 only.                                              *)

let MESSAGE_EPHEMERAL_KDF_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   KDF_SPECIALIZE_RULE WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT
    [`d1:int64`; `word 0:int64`; `word 0:int64`; `data:int64`;
     `word 0:int64`; `word 0:int64`; `datalen:int64`]);;

(* From the label join1 (at step n), where the copy has been done if needed: *)
(* mix_hash, kdf and the return.                                             *)

let MESSAGE_EPHEMERAL_TAIL_TAC n =
  let EXEC = WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_EXEC in
  ARM_STEPS_TAC EXEC (n--(n+2)) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `32 + 32 < 2 EXP 64`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 32 < 2 EXP 64`) THEN
  MESSAGE_EPHEMERAL_MIX_HASH_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `hb:byte list`; `eb:byte list`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`;
    `read SP s`; `read X30 s`] (n+3) THEN
  ARM_STEPS_TAC EXEC ((n+4)--(n+12)) THEN
  MESSAGE_EPHEMERAL_KDF_TAC
   [`read X0 s`; `read X3 s`; `read X6 s`; `read X7 s`; `eb:byte list`;
    `ckb:byte list`; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`;
    `read SP s`; `read X30 s`] (n+13) THEN
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME `~(ck:int64 = word 0)`] THEN
  ARM_STEPS_TAC EXEC ((n+14)--(n+16)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wg_ephemeral; wg_kdf1] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];;

let WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `ck:int64`; `hash:int64`; `eb:byte list`;
    `ckb:byte list`; `hb:byte list`; `mset:int64`; `ea1:int64`; `el1:num`;
    `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 832 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 800):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--9) THEN
  ASM_CASES_TAC `dst:int64 = src` THENL
   [WG_PC_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; ASSUME `dst:int64 = src`] THEN
    MESSAGE_EPHEMERAL_TAIL_TAC 10;
    ALL_TAC] THEN
  UNDISCH_TAC
   `dst:int64 = src \/
    nonoverlapping_modulo (2 EXP 64) (val dst,32) (val(src:int64),32)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  WG_PC_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; ASSUME `~(dst:int64 = src)`] THEN
  WG_BYTES32_WORDS_TAC `src:int64` `s9:armstate` THEN
  ARM_STEPS_TAC EXEC (10--13) THEN
  MESSAGE_EPHEMERAL_TAIL_TAC 14 THEN
  WG_BYTES32_OF_WORDS_TAC[]);;

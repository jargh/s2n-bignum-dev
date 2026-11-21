(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of blake2s_constprop_0_1_spec.ml: memset of the      *)
(* state on the stack and the stores of blake2s_init for an unkeyed 32-byte  *)
(* hash, then blake2s_update with handshake_name and blake2s_final into      *)
(* handshake_init_chaining_key, simulated with their theorems, and           *)
(* WG_HASH_STREAM.                                                           *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/blake2s_constprop_0_1_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/rodata.ml";;

let WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "blake2s_constprop_0_1"; layout_range "plt_memset"];;

let B1_EXEC = WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_EXEC;;

let B1_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,B1_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let B1_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,B1_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* The state (at stackpointer + 360) after the data, the construction.       *)

let b1_d = `APPEND [] wg_construction`;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `mcpy:int64`;
    `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 480 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "memset" (REWRITE_RULE[memset_contract] th))
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `data_handshake_init_chaining_key:num`]
                WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 336):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  GOT_ENTRY_TAC `got_memset:num` `s0:armstate` THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`] WG_HANDSHAKE_NAME_LOADED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD]) THEN

  (*** blake2s_init: the zeroing and the initial words ***)

  ARM_STEPS_TAC B1_EXEC (1--6) THEN WG_PLT_TAC B1_EXEC 6 THEN
  WG_CALL_TAC "memset" B1_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 11 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC `word_add stackpointer (word 360):int64` 120
    [32; 40] `s11:armstate` THEN
  ARM_STEPS_TAC B1_EXEC (12--31) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC B1_EXEC (32--36) THEN
  BLAKE2S_STATE_INIT_TAC `word_add stackpointer (word 360):int64`
    `s36:armstate` THEN

  (*** The update with the construction, and the final ***)

  ASSUME_TAC(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH)) THEN
  ASSUME_TAC LENGTH_WG_CONSTRUCTION THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 37:int64)`) THEN
  B1_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
    `[]:byte list`; `wg_construction`; `32`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  BLAKE2S_STATE_EXPAND_TAC `s37:armstate` THEN
  ARM_STEPS_TAC B1_EXEC [38] THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC B1_EXEC (39--41) THEN
  BLAKE2S_STATE_COLLECT_TAC
   (list_mk_comb(`blake2s_state_at`,
      [`word_add stackpointer (word 360):int64`; `blake2s_h0 0 32`; b1_d;
       `32`; `s41:armstate`])) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
    (mk_comb(`LENGTH:byte list->num`,b1_d)) `2 EXP 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  B1_FINAL_TAC
   [`read X0 s`; `read X1 s`; `blake2s_h0 0 32`; b1_d; `32`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC B1_EXEC (43--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[APPEND; wg_ck0] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WG_HASH_STREAM THEN
  REWRITE_TAC[LENGTH_WG_CONSTRUCTION] THEN CONV_TAC NUM_REDUCE_CONV);;

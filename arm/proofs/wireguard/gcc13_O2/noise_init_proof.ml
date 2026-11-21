(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_init_spec.ml: memset of the state on the    *)
(* stack, blake2s_constprop_0_1 for the chaining key, the stores of          *)
(* blake2s_init for an unkeyed 32-byte hash, then blake2s_update with the    *)
(* chaining key and identifier_name and blake2s_final into                   *)
(* handshake_init_hash, simulated with their theorems, and WG_HASH_STREAM.   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_init_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;
needs "arm/proofs/wireguard/gcc13_O2/rodata.ml";;

let WIREGUARD_NOISE_INIT_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_init"; layout_range "plt_memset"];;

let NI_EXEC = WIREGUARD_NOISE_INIT_GCC13_O2_EXEC;;

let NI_CK_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,NI_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let NI_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,NI_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let NI_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,NI_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* The state (at stackpointer + 520) after the data d in s.                  *)

let ni_state_at d s =
  list_mk_comb(`blake2s_state_at`,
    [`word_add stackpointer (word 520):int64`; `blake2s_h0 0 32`; d; `32`;
     s]);;

let ni_d1 = `APPEND [] wg_ck0`;;

let ni_d2 = `APPEND (APPEND [] wg_ck0) wg_identifier`;;

(* ------------------------------------------------------------------------- *)
(* The proof. The chaining key is in the form word(pc + k) of the theorem    *)
(* for blake2s_constprop_0_1, and also (for the update) in the form          *)
(* word_add (word pc) (word k) of the address that the code computes.        *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_NOISE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`mset:int64`; `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`]
  THEN
  WORD_FORALL_OFFSET_TAC 640 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC [`memset_contract mset ea el ev`,"memset"] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `data_handshake_init_hash:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 480):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  GOT_ENTRY_TAC `got_memset:num` `s0:armstate` THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`] WG_IDENTIFIER_NAME_LOADED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD]) THEN

  (*** The zeroing of the state and the chaining key ***)

  ARM_STEPS_TAC NI_EXEC (1--7) THEN WG_PLT_TAC NI_EXEC 7 THEN
  WG_CALL_TAC "memset" NI_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC NI_EXEC [13] THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC NI_EXEC [14] THEN
  NI_CK_TAC
   [`mset:int64`; `ea:int64`; `el:num`; `ev:num`; `mcpy:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 15 THEN
  ASSUME_TAC(REWRITE_RULE[WORD_ADD] (ASSUME
    `read (memory :> bytes(word(pc + data_handshake_init_chaining_key),32))
          s15 = num_of_bytelist wg_ck0`)) THEN

  (*** blake2s_init, the updates with the chaining key and the identifier, ***)
  (*** and the final                                                       ***)

  ARM_STEPS_TAC NI_EXEC (16--41) THEN
  BLAKE2S_STATE_INIT_TAC `word_add stackpointer (word 520):int64`
    `s41:armstate` THEN
  ASSUME_TAC(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH)) THEN
  ASSUME_TAC LENGTH_WG_CK0_H0 THEN ASSUME_TAC LENGTH_WG_IDENTIFIER THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 34:int64)`) THEN
  NI_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
    `[]:byte list`; `wg_ck0`; `32`; `mcpy:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 42 THEN
  BLAKE2S_STATE_EXPAND_TAC `s42:armstate` THEN
  ARM_STEPS_TAC NI_EXEC (43--44) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC NI_EXEC (45--48) THEN
  BLAKE2S_STATE_COLLECT_TAC (ni_state_at ni_d1 `s48:armstate`) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
    (mk_binop `(+):num->num->num` (mk_comb(`LENGTH:byte list->num`,ni_d1))
              `34`) `2 EXP 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  NI_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
    ni_d1; `wg_identifier`; `32`; `mcpy:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 49 THEN
  BLAKE2S_STATE_EXPAND_TAC `s49:armstate` THEN
  ARM_STEPS_TAC NI_EXEC (50--52) THEN
  BLAKE2S_STATE_COLLECT_TAC (ni_state_at ni_d2 `s52:armstate`) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
    (mk_comb(`LENGTH:byte list->num`,ni_d2)) `2 EXP 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  NI_FINAL_TAC
   [`read X0 s`; `read X1 s`; `blake2s_h0 0 32`; ni_d2; `32`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 53 THEN
  ARM_STEPS_TAC NI_EXEC (54--56) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[APPEND; wg_h0] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WG_HASH_STREAM THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN CONV_TAC NUM_REDUCE_CONV);;

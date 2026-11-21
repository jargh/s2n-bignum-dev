(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of precompute_key_spec.ml: memset of the state on    *)
(* the stack and the stores of blake2s_init for an unkeyed 32-byte hash,     *)
(* then blake2s_update with the label and the public key and blake2s_final,  *)
(* simulated with their theorems, and WG_HASH_STREAM.                        *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/precompute_key_spec.ml";;

let WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "precompute_key"; layout_range "plt_memset"];;

let PK_EXEC = WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_EXEC;;

let PK_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,PK_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let PK_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,PK_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* The state (at stackpointer + 392) after the data d in s.                  *)

let pk_state_at d s =
  list_mk_comb(`blake2s_state_at`,
    [`word_add stackpointer (word 392):int64`; `blake2s_h0 0 32`; d; `32`;
     s]);;

let pk_d1 = `APPEND [] (lb:byte list)`;;

let pk_d2 = `APPEND (APPEND [] (lb:byte list)) pb`;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`key:int64`; `pub:int64`; `label:int64`; `pb:byte list`; `lb:byte list`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `mcpy:int64`;
    `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 512 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "memset" (REWRITE_RULE[memset_contract] th))
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 336):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  GOT_ENTRY_TAC `got_memset:num` `s0:armstate` THEN

  (*** blake2s_init: the zeroing and the initial words ***)

  ARM_STEPS_TAC PK_EXEC (1--11) THEN WG_PLT_TAC PK_EXEC 11 THEN
  WG_CALL_TAC "memset" PK_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 16 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC `word_add stackpointer (word 392):int64` 120
    [32; 40] `s16:armstate` THEN
  ARM_STEPS_TAC PK_EXEC (17--40) THEN
  BLAKE2S_STATE_INIT_TAC `word_add stackpointer (word 392):int64`
    `s40:armstate` THEN

  (*** The updates with the label and the public key, and the final ***)

  ASSUME_TAC(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH)) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 8:int64)`) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  PK_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
    `[]:byte list`; `lb:byte list`; `32`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 41 THEN
  BLAKE2S_STATE_EXPAND_TAC `s41:armstate` THEN
  ARM_STEPS_TAC PK_EXEC (42--45) THEN
  BLAKE2S_STATE_COLLECT_TAC (pk_state_at pk_d1 `s45:armstate`) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
    (mk_binop `(+):num->num->num` (mk_comb(`LENGTH:byte list->num`,pk_d1))
              `32`) `2 EXP 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  PK_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
    pk_d1; `pb:byte list`; `32`; `mcpy:int64`; `ea2:int64`; `el2:num`;
    `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 46 THEN
  BLAKE2S_STATE_EXPAND_TAC `s46:armstate` THEN
  ARM_STEPS_TAC PK_EXEC (47--49) THEN
  BLAKE2S_STATE_COLLECT_TAC (pk_state_at pk_d2 `s49:armstate`) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
    (mk_comb(`LENGTH:byte list->num`,pk_d2)) `2 EXP 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  PK_FINAL_TAC
   [`read X0 s`; `read X1 s`; `blake2s_h0 0 32`; pk_d2; `32`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 50 THEN
  ARM_STEPS_TAC PK_EXEC (51--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[APPEND] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WG_HASH_STREAM THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN CONV_TAC NUM_REDUCE_CONV);;

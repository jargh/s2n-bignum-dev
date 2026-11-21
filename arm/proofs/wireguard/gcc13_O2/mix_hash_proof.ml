(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of mix_hash_spec.ml: the state is initialized for an *)
(* unkeyed hash of 32 bytes, and the calls of blake2s_update and             *)
(* blake2s_final are simulated with their theorems, the state being carried  *)
(* between them as facts about the memory.                                   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/mix_hash_spec.ml";;

let WIREGUARD_MIX_HASH_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "mix_hash"; layout_range "plt_memset"];;

let MIX_HASH_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_MIX_HASH_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let MIX_HASH_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_MIX_HASH_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_MIX_HASH_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`hash:int64`; `src:int64`; `srclen:int64`; `hb:byte list`; `sb:byte list`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 512 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(LABEL_TAC "memset" o REWRITE_RULE[memset_contract] o
    check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "memset_contract"
      with Failure _ -> false)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            (19--29) THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 336):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Zero the state, at stackpointer + 392 ***)

  ARM_STEPS_TAC EXEC (1--11) THEN
  WG_PLT_TAC EXEC 11 THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 16 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC `word_add stackpointer (word 392):int64` 120
    [32; 40] `s16:armstate` THEN

  (*** The initial chained state, buffer length and output length ***)

  ARM_STEPS_TAC EXEC (17--40) THEN
  BLAKE2S_STATE_INIT_TAC `word_add stackpointer (word 392):int64`
    `s40:armstate` THEN

  (*** blake2s_update of the hash ***)

  ASSUME_TAC(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH)) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s40:armstate` THEN
  MIX_HASH_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
    `[]:byte list`; `hb:byte list`; `32`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 41 THEN

  (*** blake2s_update of src ***)

  BLAKE2S_STATE_EXPAND_TAC `s41:armstate` THEN
  ARM_STEPS_TAC EXEC (42--45) THEN
  BLAKE2S_STATE_COLLECT_TAC
   `blake2s_state_at (word_add stackpointer (word 392)) (blake2s_h0 0 32)
      (APPEND [] hb) 32 s45` THEN
  SUBGOAL_THEN `LENGTH(APPEND [] (hb:byte list)) + val(srclen:int64) < 2 EXP 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s45:armstate` THEN
  MIX_HASH_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
    `APPEND [] hb:byte list`; `sb:byte list`; `32`; `mcpy:int64`;
    `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`; `read SP s`;
    `read X30 s`] 46 THEN

  (*** blake2s_final to the hash ***)

  BLAKE2S_STATE_EXPAND_TAC `s46:armstate` THEN
  ARM_STEPS_TAC EXEC (47--49) THEN
  BLAKE2S_STATE_COLLECT_TAC
   `blake2s_state_at (word_add stackpointer (word 392)) (blake2s_h0 0 32)
      (APPEND (APPEND [] hb) sb) 32 s49` THEN
  SUBGOAL_THEN `LENGTH(APPEND (APPEND [] hb) (sb:byte list)) < 2 EXP 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s49:armstate` THEN
  GOT_ENTRY_TAC `got_memset:num` `s49:armstate` THEN
  MIX_HASH_FINAL_TAC
   [`read X0 s`; `read X1 s`; `blake2s_h0 0 32`;
    `APPEND (APPEND [] hb) sb:byte list`; `32`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 50 THEN
  ARM_STEPS_TAC EXEC (51--54) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[wg_mix_hash; WG_HASH_STREAM; LENGTH_APPEND] THEN
  REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[]);;

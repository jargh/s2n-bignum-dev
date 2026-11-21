(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_handshake_clear_spec.ml: down_write, then   *)
(* wg_index_hashtable_remove and handshake_zero from their theorems, and     *)
(* up_write.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_clear_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_handshake_clear"; layout_range "plt_down_write";
    layout_range "plt_up_write"];;

let HC_EXEC = WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_EXEC;;

let HC_REMOVE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,HC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let HC_ZERO_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,HC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let hc_got = [`got_down_write:num`; `got_up_write:num`];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`hs:int64`; `peer:int64`; `dev:int64`; `table:int64`; `nx:int64`;
    `pp:int64`; `dwr:int64`; `uwr:int64`; `lk:int64`; `ulk:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4160 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) hc_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4128):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) hc_got THEN
  ARM_STEPS_TAC HC_EXEC (1--7) THEN WG_PLT_TAC HC_EXEC 7 THEN
  WG_CALL_TAC "down_write" HC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC HC_EXEC (13--17) THEN
  HC_REMOVE_TAC
   [`read X0 s`; `read X1 s`; `nx:int64`; `pp:int64`; `lk:int64`;
    `ulk:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 18 THEN
  ARM_STEPS_TAC HC_EXEC (19--20) THEN
  HC_ZERO_TAC [`read X0 s`; `pc:num`; `read X30 s`] 21 THEN
  ARM_STEPS_TAC HC_EXEC (22--23) THEN WG_PLT_TAC HC_EXEC 23 THEN
  WG_CALL_TAC "up_write" HC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC HC_EXEC (29--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

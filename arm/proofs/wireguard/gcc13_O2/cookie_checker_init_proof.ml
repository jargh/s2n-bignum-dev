(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of cookie_checker_init_spec.ml: __init_rwsem,        *)
(* ktime_get_coarse_with_offset, get_random_bytes and the stores.            *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/cookie_checker_init_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_cookie_checker_init"; layout_range "plt_init_rwsem";
    layout_range "plt_ktime_get_coarse_with_offset";
    layout_range "plt_get_random_bytes"];;

let KC_EXEC = WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_EXEC;;

let kc_got =
  [`got_init_rwsem:num`; `got_ktime_get_coarse_with_offset:num`;
   `got_get_random_bytes:num`];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`checker:int64`; `wg:int64`; `irw:int64`; `ktc:int64`; `grb:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4128 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`init_rwsem_contract irw ea el ev`,"init_rwsem";
    `ktime_get_coarse_with_offset_contract ktc ea el ev`,"ktime";
    `get_random_bytes_contract grb ea el ev`,"get_random_bytes"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) kc_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4096):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) kc_got THEN
  ARM_STEPS_TAC KC_EXEC (1--11) THEN WG_PLT_TAC KC_EXEC 11 THEN
  WG_CALL_TAC "init_rwsem" KC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read SP s`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC KC_EXEC (17--18) THEN WG_PLT_TAC KC_EXEC 18 THEN
  WG_CALL_TAC "ktime" KC_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 23 THEN
  ARM_STEPS_TAC KC_EXEC (24--27) THEN WG_PLT_TAC KC_EXEC 27 THEN
  WG_CALL_TAC "get_random_bytes" KC_EXEC
   [`read X0 s`; `read X1 s`; `read SP s`; `read X30 s`] 32 THEN
  ARM_STEPS_TAC KC_EXEC (33--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

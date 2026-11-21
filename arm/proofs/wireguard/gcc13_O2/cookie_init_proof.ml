(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of cookie_init_spec.ml: memset (with the zero fact   *)
(* for the fields before the lock, which the simulation keeps) and           *)
(* __init_rwsem.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/cookie_init_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_COOKIE_INIT_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_cookie_init"; layout_range "plt_memset";
    layout_range "plt_init_rwsem"];;

let KI_EXEC = WIREGUARD_COOKIE_INIT_GCC13_O2_EXEC;;

let ki_got = [`got_memset:num`; `got_init_rwsem:num`];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_COOKIE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`cookie:int64`; `mset:int64`; `irw:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4128 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`memset_contract mset ea el ev`,"memset";
    `init_rwsem_contract irw ea el ev`,"init_rwsem"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) ki_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4096):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) ki_got THEN
  ARM_STEPS_TAC KI_EXEC (1--7) THEN WG_PLT_TAC KI_EXEC 7 THEN
  WG_CALL_TAC "memset" KI_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 12 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MP_TAC(ISPECL [`cookie:int64`; `152`; `0`; `0`; `112`; `s12:armstate`]
    WG_READ_BYTES_OF_NUM) THEN
  ASM_REWRITE_TAC[DIV_0; MOD_0; WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC KI_EXEC (13--18) THEN WG_PLT_TAC KI_EXEC 18 THEN
  WG_CALL_TAC "init_rwsem" KI_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read SP s`; `read X30 s`] 23 THEN
  ARM_STEPS_TAC KI_EXEC (24--26) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

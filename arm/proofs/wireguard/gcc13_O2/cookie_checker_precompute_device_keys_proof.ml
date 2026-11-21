(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of cookie_checker_precompute_device_keys_spec.ml:    *)
(* the test of has_identity, then either the two calls of precompute_key     *)
(* (simulated with its theorem; the labels are in the .rodata of the image)  *)
(* or the zeroing of the two keys by 64-bit stores.                          *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/cookie_checker_precompute_device_keys_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_cookie_checker_precompute_device_keys"];;

let PD_EXEC = WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_EXEC;;

let PD_PK_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,PD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let pd_pk_args lb =
  [`read X0 s`; `read X1 s`; `read X2 s`; `spub:byte list`; lb;
   `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
   `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`checker:int64`; `wg:int64`; `spub:byte list`; `hid:bool`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `mcpy:int64`;
    `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 544 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 512):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun th ->
    MP_TAC(SPECL [`s0:armstate`; `pc:num`] th) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD]))
   [WG_COOKIE_KEY_LABEL_LOADED; WG_MAC1_KEY_LABEL_LOADED] THEN
  ARM_STEPS_TAC PD_EXEC (1--7) THEN
  ASM_CASES_TAC `hid:bool` THENL
   [WG_PC_REWRITE_TAC [ASSUME `hid:bool`] THEN
    WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
    ARM_STEPS_TAC PD_EXEC [8] THEN WG_ADRP_TAC THEN
    ARM_STEPS_TAC PD_EXEC (9--13) THEN
    ASSUME_TAC LENGTH_WG_LABEL_COOKIE THEN ASSUME_TAC LENGTH_WG_LABEL_MAC1 THEN
    PD_PK_TAC (pd_pk_args `wg_label_cookie`) 14 THEN
    ARM_STEPS_TAC PD_EXEC (15--19) THEN
    PD_PK_TAC (pd_pk_args `wg_label_mac1`) 20 THEN
    ARM_STEPS_TAC PD_EXEC (21--23) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[wg_cookie_key; wg_mac1_key];
    WG_PC_REWRITE_TAC [ASSUME `~hid`] THEN
    WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
    ARM_STEPS_TAC PD_EXEC (8--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN WG_ZERO_BYTES_TAC]);;

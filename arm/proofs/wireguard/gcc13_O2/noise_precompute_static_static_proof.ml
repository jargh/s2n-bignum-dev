(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_precompute_static_static_spec.ml: the lock  *)
(* taken, then if the identity has a key X25519 by curve25519 (curve25519_fn *)
(* in the layout) into the precomputed secret, zeroed if that has no key or  *)
(* the result is zero, and the lock released: three paths.                   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_precompute_static_static_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_precompute_static_static";
    layout_range "plt_down_write"; layout_range "plt_up_write"];;

let PS_EXEC = WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_EXEC;;

let PS_DH_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,PS_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let ps_got =
  [`got_curve25519_generic:num`; `got_down_write:num`; `got_up_write:num`];;

(* up_write (its PLT stub after the bl at step k) and the return.            *)

let PS_UP_WRITE_TAC k =
  WG_PLT_TAC PS_EXEC k THEN
  WG_CALL_TAC "up_write" PS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (k+5) THEN
  ARM_STEPS_TAC PS_EXEC ((k+6)--(k+9)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[wg_zero32; NUM_OF_BYTELIST_REPLICATE_0];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`peer:int64`; `si:int64`; `hid:bool`; `spriv:byte list`;
    `rpub:byte list`; `cfn:int64`; `dwr:int64`; `uwr:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4144 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) ps_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4096):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) ps_got THEN
  ARM_STEPS_TAC PS_EXEC (1--8) THEN WG_PLT_TAC PS_EXEC 8 THEN
  WG_CALL_TAC "down_write" PS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC PS_EXEC (14--17) THEN
  ASM_CASES_TAC `hid:bool` THENL
   [WG_PC_REWRITE_TAC [ASSUME `hid:bool`] THEN
    WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
    ARM_STEPS_TAC PS_EXEC (18--21) THEN
    PS_DH_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `spriv:byte list`;
      `rpub:byte list`; `cfn:int64`; `ea:int64`; `el:num`; `ev:num`;
      `pc:num`; `read SP s`; `read X30 s`] 22 THEN
    ASM_CASES_TAC `wg_dh spriv rpub = wg_zero32` THENL
     [WG_REG_REWRITE_TAC `X0` [ASSUME `wg_dh spriv rpub = wg_zero32`] THEN
      ARM_STEPS_TAC PS_EXEC (23--27) THEN PS_UP_WRITE_TAC 27 THEN
      WG_ZERO_BYTES_TAC;
      WG_REG_REWRITE_TAC `X0` [ASSUME `~(wg_dh spriv rpub = wg_zero32)`] THEN
      ARM_STEPS_TAC PS_EXEC (23--25) THEN PS_UP_WRITE_TAC 25];
    WG_PC_REWRITE_TAC [ASSUME `~hid`] THEN
    WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
    ARM_STEPS_TAC PS_EXEC (18--21) THEN PS_UP_WRITE_TAC 21 THEN
    WG_ZERO_BYTES_TAC]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of mix_dh_spec.ml: the calls of curve25519_fn and    *)
(* kdf (with a NULL third destination) are simulated with their theorems,    *)
(* in the two cases of the result of curve25519.                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/mix_dh_spec.ml";;

let WIREGUARD_MIX_DH_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "mix_dh"];;

let MIX_DH_CURVE25519_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_MIX_DH_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* kdf with the outputs d1 and d2 (of 32 bytes) only.                        *)

let MIX_DH_KDF_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_MIX_DH_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   KDF_SPECIALIZE_RULE WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT
    [`d1:int64`; `d2:int64`; `word 0:int64`; `data:int64`; `word 32:int64`;
     `word 0:int64`; `datalen:int64`]);;

(* The result of curve25519 in X0 at state s, simplified in a case.          *)

let MIX_DH_X0_TAC s ths =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("X0",_)),s')),_)
        when s' = s -> ASSUME_TAC(REWRITE_RULE ths th)
    | _ -> failwith "MIX_DH_X0_TAC");;

let WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_MIX_DH_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`ck:int64`; `key:int64`; `priv:int64`; `pub:int64`; `ckb:byte list`;
    `privb:byte list`; `pubb:byte list`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `cfn:int64`; `ea3:int64`; `el3:num`; `ev3:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1328 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 1248):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The DH by curve25519 into the buffer at stackpointer + 1296 ***)

  ARM_STEPS_TAC EXEC (1--13) THEN
  MIX_DH_CURVE25519_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `privb:byte list`;
    `pubb:byte list`; `cfn:int64`; `ea3:int64`; `el3:num`; `ev3:num`;
    `pc:num`; `read SP s`; `read X30 s`] 14 THEN
  ASM_CASES_TAC `wg_dh privb pubb = wg_zero32` THENL
   [MIX_DH_X0_TAC `s14:armstate` [ASSUME `wg_dh privb pubb = wg_zero32`] THEN
    ARM_STEPS_TAC EXEC (15--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    MIX_DH_X0_TAC `s14:armstate`
      [ASSUME `~(wg_dh privb pubb = wg_zero32)`]] THEN

  (*** The KDF into the chaining key and the key ***)

  ARM_STEPS_TAC EXEC (15--25) THEN
  ASSUME_TAC(ISPECL [`privb:byte list`; `pubb:byte list`] LENGTH_WG_DH) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 32 < 2 EXP 64`) THEN
  MIX_DH_KDF_TAC
   [`read X0 s`; `read X1 s`; `read X3 s`; `read X6 s`; `read X7 s`;
    `wg_dh privb pubb`; `ckb:byte list`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME `~(ck:int64 = word 0)`;
                           ASSUME `~(key:int64 = word 0)`] THEN

  (*** Zero the buffer and return ***)

  ARM_STEPS_TAC EXEC (27--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wg_kdf2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* With a NULL key: the same, with the theorem for kdf with no second output.*)
(* ------------------------------------------------------------------------- *)

let MIX_DH_KDF_D1_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_MIX_DH_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   KDF_SPECIALIZE_RULE WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT
    [`d1:int64`; `word 0:int64`; `data:int64`; `word 32:int64`;
     `word 0:int64`; `datalen:int64`]);;

let WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_MIX_DH_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`ck:int64`; `priv:int64`; `pub:int64`; `ckb:byte list`;
    `privb:byte list`; `pubb:byte list`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `cfn:int64`; `ea3:int64`; `el3:num`; `ev3:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1328 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 1248):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--13) THEN
  MIX_DH_CURVE25519_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `privb:byte list`;
    `pubb:byte list`; `cfn:int64`; `ea3:int64`; `el3:num`; `ev3:num`;
    `pc:num`; `read SP s`; `read X30 s`] 14 THEN
  ASM_CASES_TAC `wg_dh privb pubb = wg_zero32` THENL
   [MIX_DH_X0_TAC `s14:armstate` [ASSUME `wg_dh privb pubb = wg_zero32`] THEN
    ARM_STEPS_TAC EXEC (15--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    MIX_DH_X0_TAC `s14:armstate`
      [ASSUME `~(wg_dh privb pubb = wg_zero32)`]] THEN
  ARM_STEPS_TAC EXEC (15--25) THEN
  ASSUME_TAC(ISPECL [`privb:byte list`; `pubb:byte list`] LENGTH_WG_DH) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 32 < 2 EXP 64`) THEN
  MIX_DH_KDF_D1_TAC
   [`read X0 s`; `read X3 s`; `read X6 s`; `read X7 s`;
    `wg_dh privb pubb`; `ckb:byte list`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME `~(ck:int64 = word 0)`] THEN
  ARM_STEPS_TAC EXEC (27--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wg_kdf1] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

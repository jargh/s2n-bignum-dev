(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_expire_current_peer_keypairs_spec.ml: the   *)
(* handshake's part as in noise_handshake_clear_proof.ml, the time, then     *)
(* four paths as the next and current keypairs are NULL or not (and when     *)
(* neither is, they may be the same).                                        *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_expire_current_peer_keypairs_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_expire_current_peer_keypairs";
    layout_range "plt_down_write"; layout_range "plt_up_write";
    layout_range "plt_ktime_get_coarse_with_offset";
    layout_range "plt_raw_spin_lock_bh";
    layout_range "plt_raw_spin_unlock_bh"];;

let EX_EXEC = WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_EXEC;;

let EX_REMOVE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,EX_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let EX_ZERO_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,EX_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let ex_got =
  [`got_down_write:num`; `got_up_write:num`;
   `got_ktime_get_coarse_with_offset:num`; `got_raw_spin_lock_bh:num`;
   `got_raw_spin_unlock_bh:num`];;

(* The unlock (its PLT stub after the bl at step k) and the return; the test *)
(* of the current keypair at step m, after the next one if nkz (it is NULL)  *)
(* is false.                                                                 *)

let EX_UNLOCK_TAC k =
  WG_PLT_TAC EX_EXEC k THEN
  WG_CALL_TAC "spin_unlock" EX_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (k+5) THEN
  ARM_STEPS_TAC EX_EXEC ((k+6)--(k+9)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let EX_CK_TAC m nkz =
  ASM_CASES_TAC `ck:int64 = word 0` THENL
   [WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `ck:int64 = word 0`] THEN
    ARM_STEPS_TAC EX_EXEC ((m+1)--(m+2)) THEN EX_UNLOCK_TAC (m+2);
    WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `~(ck:int64 = word 0)`] THEN
    (if nkz then ALL_TAC else
     ASM_CASES_TAC `nk:int64 = ck` THENL
      [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
         concl th = `nk:int64 = ck`));
       ASSUME_TAC(MP (SPECL [`nk:int64`; `ck:int64`; `72`]
                       WG_NONOVERLAPPING_BYTE_OFFSET)
                     (ASSUME `~(nk:int64 = ck)`))]) THEN
    ARM_STEPS_TAC EX_EXEC ((m+1)--(m+3)) THEN EX_UNLOCK_TAC (m+3)];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`peer:int64`; `dev:int64`; `table:int64`; `nx:int64`; `pp:int64`;
    `nk:int64`; `ck:int64`; `dwr:int64`; `uwr:int64`; `ktc:int64`;
    `lk:int64`; `ulk:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4176 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write";
    `ktime_get_coarse_with_offset_contract ktc ea el ev`,"ktime";
    `spinlock_bh_contract lk ea el ev`,"spin_lock";
    `spinlock_bh_contract ulk ea el ev`,"spin_unlock"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) ex_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4128):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) ex_got THEN

  (*** The handshake ***)

  ARM_STEPS_TAC EX_EXEC (1--9) THEN WG_PLT_TAC EX_EXEC 9 THEN
  WG_CALL_TAC "down_write" EX_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 14 THEN
  ARM_STEPS_TAC EX_EXEC (15--19) THEN
  EX_REMOVE_TAC
   [`read X0 s`; `read X1 s`; `nx:int64`; `pp:int64`; `lk:int64`;
    `ulk:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC EX_EXEC (21--22) THEN
  EX_ZERO_TAC [`read X0 s`; `pc:num`; `read X30 s`] 23 THEN
  ARM_STEPS_TAC EX_EXEC (24--25) THEN WG_PLT_TAC EX_EXEC 25 THEN
  WG_CALL_TAC "up_write" EX_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 30 THEN

  (*** The time and the keypairs ***)

  ARM_STEPS_TAC EX_EXEC (31--32) THEN WG_PLT_TAC EX_EXEC 32 THEN
  WG_CALL_TAC "ktime" EX_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 37 THEN
  ARM_STEPS_TAC EX_EXEC (38--45) THEN WG_PLT_TAC EX_EXEC 45 THEN
  WG_CALL_TAC "spin_lock" EX_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 50 THEN
  ARM_STEPS_TAC EX_EXEC (51--52) THEN
  ASM_CASES_TAC `nk:int64 = word 0` THENL
   [WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `nk:int64 = word 0`] THEN
    ARM_STEPS_TAC EX_EXEC (53--54) THEN EX_CK_TAC 54 true;
    WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `~(nk:int64 = word 0)`] THEN
    ARM_STEPS_TAC EX_EXEC (53--55) THEN EX_CK_TAC 55 false]);;

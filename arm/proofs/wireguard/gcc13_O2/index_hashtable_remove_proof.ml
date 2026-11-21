(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of index_hashtable_remove_spec.ml: the lock, then    *)
(* three paths as pprev and next are NULL or not, and the unlock.            *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/index_hashtable_remove_spec.ml";;

let WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_index_hashtable_remove";
    layout_range "plt_raw_spin_lock_bh";
    layout_range "plt_raw_spin_unlock_bh"];;

let IR_EXEC = WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_EXEC;;

let ir_got = [`got_raw_spin_lock_bh:num`; `got_raw_spin_unlock_bh:num`];;

(* The unlock (its PLT stub after the bl at step k) and the return.          *)

let IR_UNLOCK_TAC k =
  WG_PLT_TAC IR_EXEC k THEN
  WG_CALL_TAC "spin_unlock" IR_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (k+5) THEN
  ARM_STEPS_TAC IR_EXEC ((k+6)--(k+8)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `ent:int64`; `nx:int64`; `pp:int64`; `lk:int64`;
    `ulk:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4128 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (c,l) ->
    FIRST_ASSUM(fun th ->
      if concl th = c
      then LABEL_TAC l (REWRITE_RULE[spinlock_bh_contract] th)
      else NO_TAC))
   [`spinlock_bh_contract lk ea el ev`,"spin_lock";
    `spinlock_bh_contract ulk ea el ev`,"spin_unlock"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) ir_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4096):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) ir_got THEN
  ARM_STEPS_TAC IR_EXEC (1--7) THEN WG_PLT_TAC IR_EXEC 7 THEN
  WG_CALL_TAC "spin_lock" IR_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC IR_EXEC (13--14) THEN
  ASM_CASES_TAC `pp:int64 = word 0` THENL
   [WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `pp:int64 = word 0`] THEN
    ARM_STEPS_TAC IR_EXEC (15--16) THEN IR_UNLOCK_TAC 16;
    WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `~(pp:int64 = word 0)`] THEN
    ARM_STEPS_TAC IR_EXEC (15--17) THEN
    ASM_CASES_TAC `nx:int64 = word 0` THENL
     [WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `nx:int64 = word 0`] THEN
      ARM_STEPS_TAC IR_EXEC (18--20) THEN IR_UNLOCK_TAC 20;
      WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `~(nx:int64 = word 0)`] THEN
      ARM_STEPS_TAC IR_EXEC (18--21) THEN IR_UNLOCK_TAC 21]]);;

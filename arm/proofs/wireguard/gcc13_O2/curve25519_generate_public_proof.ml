(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of curve25519_generate_public_spec.ml: the secret is *)
(* compared with the zero point by __crypto_memneq (with its theorem) and if *)
(* it is not zero the call of curve25519_generic through the PLT with the    *)
(* base point is simulated with its contract and the result compared with    *)
(* the zero point, both points being read from the image.                    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/curve25519_generate_public_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/rodata.ml";;

let WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "curve25519_generate_public";
    layout_range "plt_curve25519_generic"];;

let CURVE25519_GENERATE_PUBLIC_MEMNEQ_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`pub:int64`; `secret:int64`; `sb:byte list`; `cfn:int64`; `ea3:int64`;
    `el3:num`; `ev3:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1264 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "curve25519" o REWRITE_RULE[curve25519_generic_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_curve25519_generic:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 1216):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[WORD_ADD] o
              MATCH_MP WG_CURVE25519_NULL_POINT_LOADED) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[WORD_ADD] o
              MATCH_MP WG_CURVE25519_BASE_POINT_LOADED) THEN

  (*** The comparison of the secret with the zero point ***)

  ARM_STEPS_TAC EXEC (1--5) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (6--12) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  CURVE25519_GENERATE_PUBLIC_MEMNEQ_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist sb`;
    `0`; `pc:num`; `read X30 s`] 13 THEN
  ABBREV_TAC `r1 = read X0 s13` THEN
  ARM_STEPS_TAC EXEC [14] THEN
  SUBGOAL_THEN `(sb = wg_zero32 <=> val(r1:int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_EQ_0; wg_zero32] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WG_NUM_OF_BYTELIST_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `val(r1:int64) = 0` THENL

   [(*** A zero secret: the result 0 ***)

    WG_PC_REWRITE_TAC [ASSUME `val(r1:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (15--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** X25519 with the base point by curve25519_generic ***)

    WG_PC_REWRITE_TAC [ASSUME `~(val(r1:int64) = 0)`] THEN
    ARM_STEPS_TAC EXEC (15--18) THEN
    SUBGOAL_THEN `num_of_bytelist(bytelist_of_num 32 9) = 9 /\
                  LENGTH(bytelist_of_num 32 9) = 32`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM; LENGTH_BYTELIST_OF_NUM] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    WG_PLT_TAC EXEC 18 THEN
    WG_CALL_TAC "curve25519" EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`; `sb:byte list`;
      `bytelist_of_num 32 9`; `read SP s`; `read X30 s`] 23 THEN

    (*** The comparison of the public key with the zero point ***)

    ARM_STEPS_TAC EXEC (24--27) THEN
    CURVE25519_GENERATE_PUBLIC_MEMNEQ_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`;
      `num_of_bytelist(wg_dh sb (bytelist_of_num 32 9))`;
      `0`; `pc:num`; `read X30 s`] 28 THEN
    ABBREV_TAC `r2 = read X0 s28` THEN
    ARM_STEPS_TAC EXEC (29--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wg_dh_pubkey; WORD_SUB_0; VAL_EQ_0] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WG_NUM_OF_BYTELIST_EQ_0; LENGTH_WG_DH; wg_zero32] THEN
    COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV]);;

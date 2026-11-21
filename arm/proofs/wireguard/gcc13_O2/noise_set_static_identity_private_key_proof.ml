(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_set_static_identity_private_key_spec.ml:    *)
(* the copy of the key (as four 64-bit words), its bytes named (b0, the 30   *)
(* of rmid and b31) and the clamping of the first and last, and              *)
(* curve25519_generate_public from the key that was given.                   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_set_static_identity_private_key_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_set_static_identity_private_key"];;

let SI_EXEC = WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_EXEC;;

let SI_GENPUB_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,SI_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* The key as its named bytes.                                               *)

let si_r = `CONS (b0:byte) (APPEND (bytelist_of_num 30 rmid) [b31])`;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`si:int64`; `pk:int64`; `sk:byte list`; `cfn:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 1296 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 1264):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The copy, and the key as its named bytes ***)

  WG_BYTES32_WORDS_TAC `pk:int64` `s0:armstate` THEN
  ARM_STEPS_TAC SI_EXEC (1--8) THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add si (word 32),32)) s8 =
                num_of_bytelist sk` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `b0 = read (memory :> bytes8 (word_add si (word 32))) s8` THEN
  ABBREV_TAC
   `rmid = read (memory :> bytes (word_add si (word 33),30)) s8` THEN
  ABBREV_TAC `b31 = read (memory :> bytes8 (word_add si (word 63))) s8` THEN
  SUBGOAL_THEN (mk_eq(`sk:byte list`,si_r)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`sk:byte list`; si_r] WG_NUM_OF_BYTELIST_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(SPECL [`word_add si (word 32):int64`; `b0:byte`; `rmid:num`;
                  `b31:byte`; `s8:armstate`] WG_BYTES32_CONS) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN

  (*** The clamping and the public key ***)

  ARM_STEPS_TAC SI_EXEC (9--15) THEN
  WG_FACT_NORM_TAC `read (memory :> bytes8 (word_add si (word 32))) s15`
    `word_and (b0:byte) (word 248)` THEN
  WG_FACT_NORM_TAC `read (memory :> bytes8 (word_add si (word 63))) s15`
    `word_or (word_and (b31:byte) (word 127)) (word 64)` THEN
  MP_TAC(SPECL [`word_add si (word 32):int64`; `b0:byte`; `rmid:num`;
                `b31:byte`; `s15:armstate`] WG_CLAMP_BYTES) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(ASSUME (mk_eq(`sk:byte list`,si_r)))] THEN DISCH_TAC THEN
  ARM_STEPS_TAC SI_EXEC [16] THEN
  SI_GENPUB_TAC
   [`read X0 s`; `read X1 s`; `sk:byte list`; `cfn:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 17 THEN
  ARM_STEPS_TAC SI_EXEC (18--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

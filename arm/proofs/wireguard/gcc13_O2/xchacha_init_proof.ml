(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of xchacha_init_spec.ml: the key and the first 16    *)
(* bytes of the nonce are loaded into the state 32 bits at a time (and the   *)
(* key into the buffer of the subkey, chacha_load_key), hchacha_block is     *)
(* simulated with its theorem, and the final state is stored 64 bits at a    *)
(* time from the subkey and the buffer of the 16-byte nonce, both of which   *)
(* are then zeroed.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/xchacha_init_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_common.ml";;
needs "common/wireguard_kernel.ml";;

let WIREGUARD_XCHACHA_INIT_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "xchacha_init"];;

let XI_HCHACHA_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_XCHACHA_INIT_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_HCHACHA_BLOCK_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the words of the 12-byte nonce of XChaCha20, the state at the end *)
(* from its 64-bit words, and HChaCha20 unfolded.                            *)
(* ------------------------------------------------------------------------- *)

let XI_NONCE_WORDS = prove
 (`!nb:byte list.
     LENGTH nb = 24
     ==> chacha20_le32 (xchacha20_nonce nb) 0 = word 0 /\
         chacha20_le32 (xchacha20_nonce nb) 1 =
         word(num_of_bytelist(SUB_LIST(16,4) nb)) /\
         chacha20_le32 (xchacha20_nonce nb) 2 =
         word(num_of_bytelist(SUB_LIST(20,4) nb))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chacha20_le32; xchacha20_nonce] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`REPLICATE 4 (word 0:byte)`; `SUB_LIST(16,8) (nb:byte list)`;
                 `0`; `4`] WG_SUB_LIST_APPEND_RIGHT) THEN
  MP_TAC(ISPECL [`REPLICATE 4 (word 0:byte)`; `SUB_LIST(16,8) (nb:byte list)`;
                 `4`; `4`] WG_SUB_LIST_APPEND_RIGHT) THEN
  MP_TAC(ISPECL [`REPLICATE 4 (word 0:byte)`; `SUB_LIST(16,8) (nb:byte list)`;
                 `0`; `4`] WG_SUB_LIST_APPEND_LEFT) THEN
  REWRITE_TAC[LENGTH_REPLICATE; ADD_CLAUSES; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[MESON[LENGTH_REPLICATE; SUB_LIST_LENGTH]
    `SUB_LIST(0,4) (REPLICATE 4 (x:byte)) = REPLICATE 4 x`;
    NUM_OF_BYTELIST_REPLICATE_0] THEN
  SIMP_TAC[WG_SUB_LIST_SUB_LIST_GEN; ARITH] THEN CONV_TAC NUM_REDUCE_CONV);;

let XI_STATE = prove
 (`!st:int64 s (sk:byte list) (nb:byte list).
     LENGTH sk = 32 /\ LENGTH nb = 24 /\
     read (memory :> bytes64 st) s = word 3684054920433006693 /\
     read (memory :> bytes64 (word_add st (word 8))) s =
       word 7719281312240119090 /\
     read (memory :> bytes64 (word_add st (word 16))) s =
       word(num_of_bytelist(SUB_LIST(0,8) sk)) /\
     read (memory :> bytes64 (word_add st (word 24))) s =
       word(num_of_bytelist(SUB_LIST(8,8) sk)) /\
     read (memory :> bytes64 (word_add st (word 32))) s =
       word(num_of_bytelist(SUB_LIST(16,8) sk)) /\
     read (memory :> bytes64 (word_add st (word 40))) s =
       word(num_of_bytelist(SUB_LIST(24,8) sk)) /\
     read (memory :> bytes64 (word_add st (word 48))) s = word 0 /\
     read (memory :> bytes64 (word_add st (word 56))) s =
       word(num_of_bytelist(SUB_LIST(16,8) nb))
     ==> !i. i < 16
             ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s =
                 chacha20_state sk 0 (xchacha20_nonce nb) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WG_BYTES64_SPLIT o
         check (fun th ->
           can (term_match [] `read (memory :> bytes64 a) s = d`)
               (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[chacha20_state] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[XI_NONCE_WORDS] THEN
  REWRITE_TAC[chacha20_le32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun i -> MP_TAC(ISPECL [`sk:byte list`; mk_small_numeral i]
                                     CP_SUBWORD_BYTES8))
            [0; 8; 16; 24] THEN
  MP_TAC(ISPECL [`nb:byte list`; `16`] CP_SUBWORD_BYTES8) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let XI_HCHACHA20_UNFOLD =
  CONV_RULE(RAND_CONV(TOP_DEPTH_CONV let_CONV))
   (REWRITE_CONV[hchacha20] `hchacha20 kb (SUB_LIST(0,16) (nb:byte list))`);;

(* The state for HChaCha20: the key and the first 16 bytes of the nonce.     *)

let xi_hs = `chacha20_state kb (val(chacha20_le32 (SUB_LIST(0,16) nb) 0))
                            (SUB_LIST(4,12) (SUB_LIST(0,16) (nb:byte list)))`;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_XCHACHA_INIT_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `key:int64`; `nonce:int64`; `kb:byte list`; `nb:byte list`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 224 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 112):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of the key and nonce, and the state for hchacha_block ***)

  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`key:int64`; `kb:byte list`; `32`; mk_small_numeral k;
                  `s0:armstate`] WG_READ_BYTES32_BYTELIST) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC) [0; 4; 8; 12; 16; 20; 24; 28] THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`nonce:int64`; `nb:byte list`; `24`; mk_small_numeral k;
                  `s0:armstate`] WG_READ_BYTES32_BYTELIST) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC) [0; 4; 8; 12] THEN
  MP_TAC(SPECL [`nonce:int64`; `nb:byte list`; `24`; `16`;
                `s0:armstate`] WG_READ_BYTES64_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ARM_STEPS_TAC EXEC (1--45) THEN
  SUBGOAL_THEN
   (mk_forall(`i:num`,mk_imp(`i < 16`,
      mk_eq(`read (memory :> bytes32(word_add st (word(4 * i)))) s45`,
            mk_comb(xi_hs,`i:num`)))))
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`st:int64`; `s45:armstate`;
                  `word 3684054920433006693:int64`] WG_BYTES64_SPLIT) THEN
    MP_TAC(SPECL [`word_add st (word 8):int64`; `s45:armstate`;
                  `word 7719281312240119090:int64`] WG_BYTES64_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[WG_WORD_ZX_ZX] THEN
    REWRITE_TAC[chacha20_state] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[chacha20_le32; WORD_VAL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[WG_SUB_LIST_SUB_LIST_GEN; ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** hchacha_block into the subkey buffer at stackpointer + 192 ***)

  XI_HCHACHA_TAC
   [`read X0 s`; `read X1 s`; xi_hs; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `pc:num`; `read SP s`; `read X30 s`] 46 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM XI_HCHACHA20_UNFOLD]) THEN
  ABBREV_TAC `sk = hchacha20 kb (SUB_LIST(0,16) nb)` THEN
  SUBGOAL_THEN `LENGTH(sk:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "sk" THEN REWRITE_TAC[LENGTH_HCHACHA20]; ALL_TAC] THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 192):int64`
    `s46:armstate` THEN

  (*** The final state, the zeroing and the return ***)

  ARM_STEPS_TAC EXEC (47--65) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC XI_STATE THEN ASM_REWRITE_TAC[]);;

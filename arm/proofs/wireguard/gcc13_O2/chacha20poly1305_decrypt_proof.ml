(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of chacha20poly1305_decrypt_spec.ml: the ChaCha20    *)
(* state is built as for encryption (CP_STATE), __chacha20poly1305_decrypt   *)
(* is simulated with its theorem, and then memset zeroes the state; in the   *)
(* case of success the plaintext written to dst is kept through that.        *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_decrypt_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_common.ml";;

let WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "chacha20poly1305_decrypt"; layout_range "plt_memset"];;

let CDW_EXEC = WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_EXEC;;

let CDW_INNER_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CDW_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* The plaintext of a successful decryption is 16 bytes shorter.             *)

let CDW_LENGTH_SOME = prove
 (`!key nonce (ct:byte list) al p.
     aead_chacha20_poly1305_decrypt key nonce ct al = SOME p
     ==> 16 <= LENGTH ct /\ LENGTH p = LENGTH ct - 16`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aead_chacha20_poly1305_decrypt] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CP_LENGTH_ENC; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let CDW_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `len:int64`; `ad:int64`; `adlen:int64`;
    `nonce:int64`; `key:int64`; `kb:byte list`; `ct:byte list`;
    `al:byte list`; `kv:int64`; `ms:int64`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 800 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "memset" (REWRITE_RULE[memset_contract] th))
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  GOT_ENTRY_TAC `got_memset:num` `s0:armstate` THEN
  MAP_EVERY (fun i -> MP_TAC(ISPECL [`key:int64`; `kb:byte list`; `32`;
               mk_small_numeral i; `s0:armstate`] WG_READ_BYTES64_BYTELIST))
   [0; 8; 16; 24] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC;;

let CDW_END_TAC =
  ARM_STEPS_TAC CDW_EXEC (26--30) THEN WG_PLT_TAC CDW_EXEC 30 THEN
  WG_CALL_TAC "memset" CDW_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 35 THEN
  ARM_STEPS_TAC CDW_EXEC (36--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[wg_aead_decrypt];;

let CDW_SOME_TAC =
  MP_TAC(ISPEC
   `aead_chacha20_poly1305_decrypt kb (wg_aead_nonce (val(nonce:int64))) ct
                                   al`
   (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `p0:byte list`) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (fun t ->
             try fst(dest_const t) = "SOME" with Failure _ -> false))
           (concl th)
    then MP_TAC(SPEC `p0:byte list` th) else failwith "CDW_SOME_TAC") THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`kb:byte list`; `wg_aead_nonce (val(nonce:int64))`;
                 `ct:byte list`; `al:byte list`; `p0:byte list`]
                CDW_LENGTH_SOME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if concl th = `LENGTH(p0:byte list) = val(len:int64) - 16` then th
    else REWRITE_RULE
          [ASSUME `LENGTH(p0:byte list) = val(len:int64) - 16`] th) THEN
  SUBGOAL_THEN `val(len:int64) - 16 <= val len` ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  CDW_END_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option";
              FORALL_UNWIND_THM1] THEN
  CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CDW_SETUP_TAC THEN ARM_STEPS_TAC CDW_EXEC (1--24) THEN
  MP_TAC(ISPECL [`word_add stackpointer (word 736):int64`; `s24:armstate`;
                 `kb:byte list`; `nonce:int64`] CP_STATE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th))] THEN
  ASSUME_TAC(SPEC `val(nonce:int64)` CP_LENGTH_NONCE) THEN
  SUBGOAL_THEN
   `dst:int64 = src \/
    nonoverlapping (dst,val(len:int64) - 16) (src:int64,val len)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CDW_INNER_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `kb:byte list`; `wg_aead_nonce (val(nonce:int64))`;
    `ct:byte list`; `al:byte list`; `kv:int64`; `ms:int64`; `mset:int64`;
    `ea1:int64`; `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 25 THEN
  ASM_CASES_TAC
   `aead_chacha20_poly1305_decrypt kb (wg_aead_nonce (val(nonce:int64)))
                                   ct al = NONE` THENL
   [CDW_END_TAC THEN REWRITE_TAC[distinctness "option"] THEN
    CONV_TAC WORD_REDUCE_CONV;
    CDW_SOME_TAC]);;

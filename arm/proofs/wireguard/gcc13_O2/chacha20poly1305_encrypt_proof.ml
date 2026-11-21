(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of chacha20poly1305_encrypt_spec.ml: the 64-bit      *)
(* stores of the constants, the key and the nonce give the ChaCha20 state    *)
(* of RFC 8439 for the key and the WireGuard nonce with counter 0            *)
(* (CP_STATE), and __chacha20poly1305_encrypt is simulated with its theorem. *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_encrypt_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_common.ml";;

let WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "chacha20poly1305_encrypt"];;

let CW_EXEC = WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_EXEC;;

let CW_INNER_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CW_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA20POLY1305_ENCRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let CW_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `len:int64`; `ad:int64`; `adlen:int64`;
    `nonce:int64`; `key:int64`; `kb:byte list`; `pl:byte list`;
    `al:byte list`; `kv:int64`; `ms:int64`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 784 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun i -> MP_TAC(ISPECL [`key:int64`; `kb:byte list`; `32`;
               mk_small_numeral i; `s0:armstate`] WG_READ_BYTES64_BYTELIST))
   [0; 8; 16; 24] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC;;

let WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CW_SETUP_TAC THEN ARM_STEPS_TAC CW_EXEC (1--22) THEN
  MP_TAC(ISPECL [`word_add stackpointer (word 720):int64`; `s22:armstate`;
                 `kb:byte list`; `nonce:int64`] CP_STATE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th))] THEN
  ASSUME_TAC(SPEC `val(nonce:int64)` CP_LENGTH_NONCE) THEN
  SUBGOAL_THEN
   `dst:int64 = src \/
    nonoverlapping (dst,val(len:int64) + 16) (src:int64,val len)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CW_INNER_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `kb:byte list`; `wg_aead_nonce (val(nonce:int64))`;
    `pl:byte list`; `al:byte list`; `kv:int64`; `ms:int64`; `mset:int64`;
    `ea1:int64`; `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 23 THEN
  ARM_STEPS_TAC CW_EXEC (24--30) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[wg_aead]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of cookie_message_consume_spec.ml: the lookup of the *)
(* entry from its contract, then (if found) under down_read the test of      *)
(* have_sent_mac1 and the decryption by xchacha20poly1305_decrypt into the   *)
(* local cookie on the stack (at stackpointer + 4848), and (if that          *)
(* succeeds, with the plaintext named c) under down_write the stores of the  *)
(* cookie, the time and the flags; wg_peer_put at the end: four paths.       *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/cookie_message_consume_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_cookie_message_consume";
    layout_range "plt_down_read"; layout_range "plt_up_read";
    layout_range "plt_down_write"; layout_range "plt_up_write";
    layout_range "plt_ktime_get_coarse_with_offset";
    layout_range "plt_wg_peer_put"];;

let CO_EXEC = WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_EXEC;;

let CO_DEC_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CO_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_XCHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let co_got =
  [`got_memset:num`; `got_memcpy:num`; `got_down_write:num`;
   `got_up_write:num`; `got_down_read:num`; `got_up_read:num`;
   `got_ktime_get_coarse_with_offset:num`; `got_wg_peer_put:num`];;

let co_dec =
  `wg_xaead_decrypt dk (SUB_LIST(8,24) msg) (SUB_LIST(32,32) msg) lm`;;

let co_dec_fail = mk_eq(co_dec,`NONE:(byte list)option`);;

(* ------------------------------------------------------------------------- *)
(* The setup and the lookup (step 13), and the lock taken for reading if the *)
(* entry is found.                                                           *)
(* ------------------------------------------------------------------------- *)

let CO_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`src:int64`; `wg:int64`; `itbl:int64`; `msg:byte list`; `found:bool`;
    `ent:int64`; `peer:int64`; `sent:bool`; `dk:byte list`; `lm:byte list`;
    `cb:num`; `kv:int64`; `ms:int64`; `mset:int64`; `mcpy:int64`;
    `dwr:int64`; `uwr:int64`; `drd:int64`; `urd:int64`; `ktc:int64`;
    `wpp:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4864 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`peer:int64`; `1648`; `0`] WG_NONZERO_OFFSET) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; VAL_WORD_0; WORD_ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  WG_LABEL_CONTRACTS_TAC
   [`rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write";
    `rwsem_contract drd ea el ev`,"down_read";
    `rwsem_contract urd ea el ev`,"up_read";
    `ktime_get_coarse_with_offset_contract ktc ea el ev`,"ktime"] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `wg_peer_put_cookie_contract f a b c`) (concl th)
    then LABEL_TAC "wg_peer_put" (REWRITE_RULE[wg_peer_put_cookie_contract] th)
    else NO_TAC) THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) co_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4800):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) co_got THEN
  WG_WORD_FACT_TAC WG_READ_BYTES32_BYTELIST `src:int64` 64 `msg:byte list` 4
    `s0:armstate` THEN
  ARM_STEPS_TAC CO_EXEC (1--12) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `wg_index_lookup_entry_contract a b c d e f g`)
           (concl th)
    then WG_CONTRACT_SIM_TAC CO_EXEC
           (REWRITE_RULE[wg_index_lookup_entry_contract] th)
           [`read X3 s`; `read SP s`; `read X30 s`] 13
    else failwith "CO_SETUP_TAC") THEN
  ARM_STEPS_TAC CO_EXEC [14];;

let CO_FOUND_TAC =
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME `found:bool`] THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `found:bool`)) (concl th) &&
       can (find_term ((=) `s14:armstate`)) (concl th)
    then REWRITE_RULE[ASSUME `found:bool`] th else th) THEN
  WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `~(ent = word 0:int64)`] THEN
  ARM_STEPS_TAC CO_EXEC (15--17) THEN WG_PLT_TAC CO_EXEC 17 THEN
  WG_CALL_TAC "down_read" CO_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC CO_EXEC (23--25);;

(* ------------------------------------------------------------------------- *)
(* The decryption (step 34) if a mac1 was sent.                              *)
(* ------------------------------------------------------------------------- *)

let CO_DECRYPT_TAC =
  WG_PC_REWRITE_TAC [ASSUME `sent:bool`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  MAP_EVERY (fun (i,k) ->
    MP_TAC(SPECL [`src:int64`; `msg:byte list`; `64`; mk_small_numeral i;
                  mk_small_numeral k; `s25:armstate`]
                 WG_READ_BYTES_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN DISCH_TAC)
   [8,24; 32,32] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(8,24) (msg:byte list)) = 24 /\
                LENGTH(SUB_LIST(32,32) (msg:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 16:int64)`) THEN
  SUBGOAL_THEN
   `word_add stackpointer (word 4848):int64 = word_add src (word 32) \/
    nonoverlapping (word_add stackpointer (word 4848):int64,32 - 16)
                   (word_add src (word 32),32)` ASSUME_TAC THENL
   [DISJ2_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC CO_EXEC (26--33) THEN
  CO_DEC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `dk:byte list`; `SUB_LIST(8,24) (msg:byte list)`;
    `SUB_LIST(32,32) (msg:byte list)`; `lm:byte list`; `kv:int64`; `ms:int64`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 34;;

(* ------------------------------------------------------------------------- *)
(* The paths that keep the cookie: up_read (its PLT stub at step k, after    *)
(* the steps from m), then wg_peer_put and the return, as for an entry that  *)
(* is not found (with no lock).                                              *)
(* ------------------------------------------------------------------------- *)

let CO_UP_READ_PUT_TAC m k =
  ARM_STEPS_TAC CO_EXEC (m--k) THEN WG_PLT_TAC CO_EXEC k THEN
  WG_CALL_TAC "up_read" CO_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (k+5) THEN
  ARM_STEPS_TAC CO_EXEC ((k+6)--(k+8)) THEN WG_PLT_TAC CO_EXEC (k+8) THEN
  WG_CALL_TAC "wg_peer_put" CO_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (k+13) THEN
  ARM_STEPS_TAC CO_EXEC ((k+14)--(k+16)) THEN
  ENSURES_FINAL_STATE_TAC;;

let CO_NOTFOUND_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~found`; VAL_WORD_0] THEN
  ARM_STEPS_TAC CO_EXEC (15--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let CO_NOTSENT_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~sent`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  CO_UP_READ_PUT_TAC 26 27 THEN ASM_REWRITE_TAC[];;

let CO_DEC_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME co_dec_fail] THEN
  CO_UP_READ_PUT_TAC 35 38 THEN ASM_REWRITE_TAC[distinctness "option"];;

(* ------------------------------------------------------------------------- *)
(* The decryption that succeeds: the plaintext c (16 bytes, as two words),   *)
(* the stores under down_write, and the cookie at peer + 689 from them.      *)
(* ------------------------------------------------------------------------- *)

let CO_DEC_OK_TAC =
  MP_TAC(ISPEC co_dec (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c:byte list`) THEN
  SUBGOAL_THEN `LENGTH(c:byte list) = 16` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP WG_XAEAD_DECRYPT_LENGTH
      (ASSUME (mk_eq(co_dec,`SOME(c:byte list)`)))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) co_dec)) (concl th)
    then MP_TAC(SPEC `c:byte list` th) else failwith "CO_DEC_OK_TAC") THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  WG_REG_REWRITE_TAC `X0`
   [ASSUME (mk_eq(co_dec,`SOME(c:byte list)`)); distinctness "option"] THEN
  ARM_STEPS_TAC CO_EXEC (35--38) THEN WG_PLT_TAC CO_EXEC 38 THEN
  WG_CALL_TAC "up_read" CO_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 43 THEN
  ARM_STEPS_TAC CO_EXEC (44--47) THEN WG_PLT_TAC CO_EXEC 47 THEN
  WG_CALL_TAC "down_write" CO_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 52 THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`word_add stackpointer (word 4848):int64`; `c:byte list`;
                  `16`; mk_small_numeral k; `s52:armstate`]
                 WG_READ_BYTES64_BYTELIST) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV WG_ADDR_CONV) THEN DISCH_TAC)
   [0; 8] THEN
  ARM_STEPS_TAC CO_EXEC (53--58) THEN WG_PLT_TAC CO_EXEC 58 THEN
  WG_CALL_TAC "ktime" CO_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 63 THEN
  ARM_STEPS_TAC CO_EXEC (64--70) THEN WG_PLT_TAC CO_EXEC 70 THEN
  WG_CALL_TAC "up_write" CO_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 75 THEN
  ARM_STEPS_TAC CO_EXEC (76--78) THEN WG_PLT_TAC CO_EXEC 78 THEN
  WG_CALL_TAC "wg_peer_put" CO_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 83 THEN
  ARM_STEPS_TAC CO_EXEC (84--86) THEN
  MP_TAC(ISPECL [`word_add peer (word 689):int64`;
                 `SUB_LIST(0,8) (c:byte list)`; `SUB_LIST(8,8) (c:byte list)`;
                 `s86:armstate`] WG_READ_BYTES_16_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WG_ADDR_CONV)) THEN
  ASM_SIMP_TAC[WG_SUB_LIST_HALVES_16] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  MESON_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CO_SETUP_TAC THEN
  ASM_CASES_TAC `found:bool` THENL [ALL_TAC; CO_NOTFOUND_TAC] THEN
  CO_FOUND_TAC THEN
  ASM_CASES_TAC `sent:bool` THENL [ALL_TAC; CO_NOTSENT_TAC] THEN
  CO_DECRYPT_TAC THEN
  ASM_CASES_TAC co_dec_fail THENL [CO_DEC_FAIL_TAC; CO_DEC_OK_TAC]);;

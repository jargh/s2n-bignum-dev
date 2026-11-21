(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of cookie_message_create_spec.ml: the stores of the  *)
(* type and the index, wait_for_random_bytes and get_random_bytes for the    *)
(* nonce (named nonce), make_cookie into the local cookie on the stack (at   *)
(* stackpointer + 4352) and xchacha20poly1305_encrypt from it: one path.     *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/cookie_message_create_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_cookie_message_create";
    layout_range "plt_wait_for_random_bytes";
    layout_range "plt_get_random_bytes"];;

let CM_EXEC = WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_EXEC;;

let CM_COOKIE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CM_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CM_XAEAD_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CM_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_XCHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let cm_got =
  [`got_memset:num`; `got_memcpy:num`; `got_down_write:num`;
   `got_up_write:num`; `got_down_read:num`; `got_up_read:num`;
   `got_ktime_get_coarse_with_offset:num`; `got_get_random_bytes:num`;
   `got_wait_for_random_bytes:num`];;

let cm_pl = `wg_mac sec' (wg_cookie_data proto a4 a6 port)`;;

(* ------------------------------------------------------------------------- *)
(* The setup, the nonce and the cookie (step 35).                            *)
(* ------------------------------------------------------------------------- *)

let CM_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `skb:int64`; `ridx:int32`; `checker:int64`; `len:int32`;
    `data:int64`; `m1:byte list`; `ck:byte list`; `proto:int16`;
    `th:int16`; `nh:int16`; `head:int64`; `sec:byte list`; `bd:int64`;
    `a4:byte list`; `a6:byte list`; `port:byte list`; `kv:int64`;
    `ms:int64`; `mset:int64`; `mcpy:int64`; `dwr:int64`; `uwr:int64`;
    `drd:int64`; `urd:int64`; `ktc:int64`; `grb:int64`; `wfrb:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4368 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`get_random_bytes_contract grb ea el ev`,"get_random_bytes";
    `wait_for_random_bytes_contract wfrb ea el ev`,"wait_for_random_bytes"]
  THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) cm_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4288):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) cm_got;;

let CM_NONCE_TAC =
  ARM_STEPS_TAC CM_EXEC (1--17) THEN WG_PLT_TAC CM_EXEC 17 THEN
  WG_CALL_TAC "wait_for_random_bytes" CM_EXEC
   [`read SP s`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC CM_EXEC (23--25) THEN WG_PLT_TAC CM_EXEC 25 THEN
  WG_CALL_TAC "get_random_bytes" CM_EXEC
   [`read X0 s`; `read X1 s`; `read SP s`; `read X30 s`] 30 THEN
  WG_FACT_CONV_TAC `read (memory :> bytes32 (word_add dst (word 4))) s30`
    (REWRITE_CONV[WG_WORD_ZX_ZX]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WG_LEN32_SUB
    (ASSUME `32 <= val(len:int32)`)]) THEN
  WG_NAME_BYTES_TAC `word_add dst (word 8):int64` `24` `nonce:byte list`
    `s30:armstate`;;

let CM_MAKE_COOKIE_TAC =
  ARM_STEPS_TAC CM_EXEC (31--34) THEN
  CM_COOKIE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `proto:int16`; `th:int16`;
    `nh:int16`; `head:int64`; `sec:byte list`; `bd:int64`; `a4:byte list`;
    `a6:byte list`; `port:byte list`; `mset:int64`; `mcpy:int64`;
    `dwr:int64`; `uwr:int64`; `drd:int64`; `urd:int64`; `ktc:int64`;
    `grb:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 35;;

(* ------------------------------------------------------------------------- *)
(* The encryption (step 44) and the return.                                  *)
(* ------------------------------------------------------------------------- *)

let CM_ENCRYPT_TAC =
  ARM_STEPS_TAC CM_EXEC (36--43) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 16:int64)`) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,cm_pl),`16`))
  ASSUME_TAC THENL
   [REWRITE_TAC[wg_mac; LENGTH_BLAKE2S] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add dst (word 32):int64 = word_add stackpointer (word 4352) \/
    nonoverlapping (word_add dst (word 32):int64,16 + 16)
                   (word_add stackpointer (word 4352),16)` ASSUME_TAC THENL
   [DISJ2_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  CM_XAEAD_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `ck:byte list`; `nonce:byte list`; cm_pl;
    `m1:byte list`; `kv:int64`; `ms:int64`; `mset:int64`; `ea:int64`;
    `el:num`; `ev:num`; `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 44 THEN
  ARM_STEPS_TAC CM_EXEC (45--49) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`nonce:byte list`; `sec':byte list`] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `wg_xaead`)) (concl th)
    then CONV_RULE(DEPTH_CONV NUM_ADD_CONV THENC
                   DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
                   DEPTH_CONV NUM_ADD_CONV) th
    else th) THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CM_SETUP_TAC THEN CM_NONCE_TAC THEN CM_MAKE_COOKIE_TAC THEN CM_ENCRYPT_TAC);;

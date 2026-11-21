(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_handshake_consume_response_spec.ml, as for  *)
(* consume_initiation. The code gives up in six ways: with no static         *)
(* identity or no handshake for the index, from the tail (zeroing the stack  *)
(* copies, up_read of the identity's lock and the return), and if the state  *)
(* is not HANDSHAKE_CREATED_INITIATION, either Diffie-Hellman result (mix_dh *)
(* with a NULL key) is zero or the empty text does not decrypt, from join1,  *)
(* which drops the reference to the peer first. On success the state and the *)
(* ephemeral private key are checked again under the write lock; that check  *)
(* succeeds, since nothing else runs in this model. mix_psk and the two      *)
(* calls of mix_hash are inlined, and the empty text is decrypted with       *)
(* chacha20poly1305_decrypt to NULL.                                         *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_consume_response_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_handshake_consume_response";
    layout_range "plt_down_read"; layout_range "plt_memset";
    layout_range "plt_up_read"; layout_range "plt_down_write";
    layout_range "plt_up_write"; layout_range "plt_wg_peer_put"];;

let CS_EXEC = WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_EXEC;;

let cs_sim th = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CS_EXEC,0,wireguard_gcc13_O2_mc,th);;

let CS_EPH_TAC =
  cs_sim WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CS_MIX_DH_TAC =
  cs_sim WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CS_KDF_TAC = cs_sim WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CS_MEMNEQ_TAC =
  cs_sim WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

(* chacha20poly1305_decrypt of the 16 bytes of the empty text to NULL, with  *)
(* the conditions and frame regions for it that become trivial removed.      *)

let CS_DEC0_TH =
  let th1 = SPECL [`word 0:int64`; `src:int64`; `word 16:int64`]
    WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT in
  GEN `src:int64`
   (CONV_RULE (DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
               DEPTH_CONV NUM_SUB_CONV THENC
               REWRITE_CONV[ALL] THENC
               SIMP_CONV[NONOVERLAPPING_TRIVIAL] THENC
               ONCE_DEPTH_CONV WG_MAYCHANGE_DROP_EMPTY_CONV) th1);;

let CS_DEC0_TAC = cs_sim CS_DEC0_TH;;

let cs_mixdh_args ckb privb pubb =
  [`read X0 s`; `read X2 s`; `read X3 s`; ckb; privb; pubb;
   `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
   `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
   `cfn:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

(* The consumption gives up if either Diffie-Hellman result is zero.         *)

let WG_CONSUME_RESPONSE_DH_ZERO = prove
 (`!ck h epriv spriv psk (msg:byte list).
     wg_dh epriv (SUB_LIST(12,32) msg) = wg_zero32 \/
     wg_dh spriv (SUB_LIST(12,32) msg) = wg_zero32
     ==> wg_consume_response (ck,h) epriv spriv psk msg = NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[wg_consume_response; wg_ephemeral; wg_kdf3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The setup, as for consume_initiation; the stack pointer of the frame is   *)
(* stackpointer + 4128, with the lock of the handshake (its address) at      *)
(* + 4240, the copy of the state at + 4252, the addresses of the hash and    *)
(* chaining key of the handshake at + 4256 and + 4264, the peer from the     *)
(* lookup at + 4272, the key at + 4280, the hash at + 4312, the chaining key *)
(* at + 4344, the ephemeral key at + 4376, the ephemeral private key at      *)
(* + 4408, the preshared key at + 4472, tau at + 4504 and the BLAKE2s state  *)
(* at + 4536.                                                                *)
(* ------------------------------------------------------------------------- *)

let cs_got =
  [`got_memset:num`; `got_memcpy:num`; `got_curve25519_generic:num`;
   `got_down_read:num`; `got_up_read:num`; `got_down_write:num`;
   `got_up_write:num`; `got_wg_peer_put:num`];;

let cs_st = `word_add stackpointer (word 4536):int64`;;

let CS_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`src:int64`; `wg:int64`; `msg:byte list`; `spriv:byte list`; `hid:bool`;
    `itbl:int64`; `found:bool`; `peer:int64`; `st:int32`; `ckb:byte list`;
    `hb:byte list`; `epriv:byte list`; `psk:byte list`; `kv:int64`;
    `ms:int64`; `mset:int64`; `mcpy:int64`; `cfn:int64`; `drd:int64`;
    `urd:int64`; `dwr:int64`; `uwr:int64`; `wpp:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4656 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`memset_contract mset ea el ev`,"memset";
    `memcpy_contract mcpy ea el ev`,"memcpy";
    `rwsem_contract drd ea el ev`,"down_read";
    `rwsem_contract urd ea el ev`,"up_read";
    `rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write";
    `wg_peer_put_contract wpp ea el ev`,"wg_peer_put"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) cs_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4128):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add stackpointer (word 4344) = word 0:int64) /\
                ~(word_add stackpointer (word 4280) = word 0:int64) /\
                ~(word_add stackpointer (word 4504) = word 0:int64)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WG_NONZERO_OFFSET THEN
    EXISTS_TAC `4656` THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; VAL_WORD_0] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) cs_got;;

let CS_PART1_TAC =
  ARM_STEPS_TAC CS_EXEC (1--37) THEN WG_PLT_TAC CS_EXEC 37 THEN
  WG_CALL_TAC "down_read" CS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 42 THEN
  ARM_STEPS_TAC CS_EXEC (43--44);;

(* ------------------------------------------------------------------------- *)
(* The tails. From join3 (at step n): zeroing the stack copies, up_read of   *)
(* the identity's lock and the return. From join1 (at step n): wg_peer_put   *)
(* of the peer and then join3; the code gives up from there as               *)
(* wg_consume_response does, proved by none_tac.                             *)
(* ------------------------------------------------------------------------- *)

let CS_TAIL3_TAC n =
  ARM_STEPS_TAC CS_EXEC (n--(n+15)) THEN WG_PLT_TAC CS_EXEC (n+15) THEN
  WG_CALL_TAC "up_read" CS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+20) THEN
  ARM_STEPS_TAC CS_EXEC ((n+21)--(n+28)) THEN
  ENSURES_FINAL_STATE_TAC;;

let CS_JOIN1_TAC n =
  ARM_STEPS_TAC CS_EXEC [n; n+1] THEN WG_PLT_TAC CS_EXEC (n+1) THEN
  WG_CALL_TAC "wg_peer_put_2" CS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+6) THEN
  ARM_STEPS_TAC CS_EXEC ((n+7)--(n+8)) THEN CS_TAIL3_TAC (n+9);;

let CS_FAIL1_TAC none_tac n =
  CS_JOIN1_TAC n THEN
  SUBGOAL_THEN `wg_consume_response (ckb,hb) epriv spriv psk msg = NONE`
  ASSUME_TAC THENL [none_tac; ALL_TAC] THEN
  ASM_REWRITE_TAC[distinctness "option"] THEN CONV_TAC WORD_REDUCE_CONV;;

(* No static identity: the result NULL.                                      *)

let CS_NOID_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~hid`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  ARM_STEPS_TAC CS_EXEC [45] THEN CS_TAIL3_TAC 46 THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The lookup of the handshake for the receiver index, from the assumption   *)
(* about it; if found, the copies of its fields under its lock.              *)
(* ------------------------------------------------------------------------- *)

let CS_LOOKUP_TAC =
  WG_PC_REWRITE_TAC [ASSUME `hid:bool`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  MAP_EVERY (fun k ->
    MP_TAC(ISPECL [`peer:int64`; `1648`; mk_small_numeral k]
                  WG_NONZERO_OFFSET) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; VAL_WORD_0; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC) [0; 240] THEN
  WG_WORD_FACT_TAC WG_READ_BYTES32_BYTELIST `src:int64` 60 `msg:byte list` 8
    `s44:armstate` THEN
  ARM_STEPS_TAC CS_EXEC (45--50) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `wg_index_lookup_contract a b c d e`) (concl th)
    then WG_CONTRACT_SIM_TAC CS_EXEC
           (REWRITE_RULE[wg_index_lookup_contract] th)
           [`read X3 s`; `read SP s`; `read X30 s`] 51
    else failwith "CS_LOOKUP_TAC") THEN
  ARM_STEPS_TAC CS_EXEC (52--53);;

(* Not found: the result NULL.                                               *)

let CS_NOTFOUND_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~found`; VAL_WORD_0] THEN
  ARM_STEPS_TAC CS_EXEC (54--56) THEN CS_TAIL3_TAC 57 THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

let CS_COPY_TAC =
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME `found:bool`] THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `s53:armstate`)) (concl th) &&
       can (find_term ((=) `found:bool`)) (concl th)
    then REWRITE_RULE[ASSUME `found:bool`] th else th) THEN
  WG_PC_REWRITE_TAC
   [VAL_EQ_0; ASSUME `~(word_add peer (word 240) = word 0:int64)`] THEN
  ARM_STEPS_TAC CS_EXEC (54--56) THEN WG_PLT_TAC CS_EXEC 56 THEN
  WG_CALL_TAC "down_read" CS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 61 THEN
  MAP_EVERY (fun k -> WG_BYTES32_WORDS_TAC
     (mk_comb(mk_comb(`word_add:int64->int64->int64`,`peer:int64`),
              mk_comb(`word:num->int64`,mk_small_numeral k))) `s61:armstate`)
    [296; 456; 488; 424] THEN
  ARM_STEPS_TAC CS_EXEC (62--87) THEN
  MAP_EVERY (fun (k,l) ->
    let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,
                            `stackpointer:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral k)) in
    SUBGOAL_THEN
     (subst [a,`a:int64`; l,`l:byte list`]
        `read (memory :> bytes(a:int64,32)) s87 =
         num_of_bytelist(l:byte list)`)
    ASSUME_TAC THENL [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC])
   [4408,`epriv:byte list`; 4312,`hb:byte list`; 4344,`ckb:byte list`;
    4472,`psk:byte list`] THEN
  WG_FACT_CONV_TAC
    `read (memory :> bytes32 (word_add stackpointer (word 4252))) s87`
    (REWRITE_CONV[WG_ZX_ZX_32]) THEN
  WG_PLT_TAC CS_EXEC 87 THEN
  WG_CALL_TAC "up_read" CS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 92 THEN
  ARM_STEPS_TAC CS_EXEC (93--95);;

(* Not in the state 1: the result NULL, from join1.                          *)

let CS_BADST_TAC =
  WG_PC_REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0; WG_ZX_ZX_32;
                     ASSUME `~(st:int32 = word 1)`] THEN
  CS_JOIN1_TAC 96 THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The fields of the message, message_ephemeral (ee, ck1, h1), and mix_dh    *)
(* (with a NULL key) with the ephemeral and then the static private key      *)
(* (ck2, ck3).                                                               *)
(* ------------------------------------------------------------------------- *)

let CS_EPH_DH_TAC =
  WG_PC_REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0; WG_ZX_ZX_32;
                     ASSUME `st:int32 = word 1`] THEN
  MAP_EVERY (fun (i,k) ->
    MP_TAC(SPECL [`src:int64`; `msg:byte list`; `60`; mk_small_numeral i;
                  mk_small_numeral k; `s95:armstate`]
                 WG_READ_BYTES_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN DISCH_TAC)
   [12,32; 44,16] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(12,32) (msg:byte list)) = 32 /\
                LENGTH(SUB_LIST(44,16) (msg:byte list)) = 16`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ARM_STEPS_TAC CS_EXEC (96--101) THEN
  CS_EPH_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `SUB_LIST(12,32) (msg:byte list)`; `ckb:byte list`; `hb:byte list`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 102 THEN
  ABBREV_TAC `ee = SUB_LIST(12,32) (msg:byte list)` THEN
  ABBREV_TAC `ck1 = FST(wg_ephemeral (ckb,hb) ee)` THEN
  ABBREV_TAC `h1 = SND(wg_ephemeral (ckb,hb) ee)` THEN
  SUBGOAL_THEN `LENGTH(ck1:byte list) = 32 /\ LENGTH(h1:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck1"; "h1"] THEN REWRITE_TAC[LENGTH_WG_EPHEMERAL];
    ALL_TAC] THEN
  WG_ABBREV_NORM_TAC `ck1:byte list` [wg_ephemeral] THEN
  WG_ABBREV_NORM_TAC `h1:byte list` [wg_ephemeral] THEN
  ARM_STEPS_TAC CS_EXEC (103--107) THEN
  CS_MIX_DH_TAC
    (cs_mixdh_args `ck1:byte list` `epriv:byte list` `ee:byte list`) 108;;

let cs_dh1_fail = `wg_dh epriv ee = wg_zero32`;;

let cs_dh2_fail = `wg_dh spriv ee = wg_zero32`;;

let CS_DH_NONE_TAC =
  MATCH_MP_TAC WG_CONSUME_RESPONSE_DH_ZERO THEN ASM_REWRITE_TAC[];;

let CS_DH1_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cs_dh1_fail] THEN
  ARM_STEPS_TAC CS_EXEC [109] THEN CS_FAIL1_TAC CS_DH_NONE_TAC 110;;

let CS_DH1_OK_TAC =
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME (mk_neg cs_dh1_fail)] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME (mk_neg cs_dh1_fail)] THEN
  ARM_STEPS_TAC CS_EXEC [109] THEN
  ABBREV_TAC `ck2 = wg_kdf1 ck1 (wg_dh epriv ee)` THEN
  SUBGOAL_THEN `LENGTH(ck2:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "ck2" THEN REWRITE_TAC[LENGTH_WG_KDF]; ALL_TAC] THEN
  ARM_STEPS_TAC CS_EXEC (110--114) THEN
  CS_MIX_DH_TAC
    (cs_mixdh_args `ck2:byte list` `spriv:byte list` `ee:byte list`) 115;;

let CS_DH2_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cs_dh2_fail] THEN
  ARM_STEPS_TAC CS_EXEC [116] THEN CS_FAIL1_TAC CS_DH_NONE_TAC 117;;

(* ------------------------------------------------------------------------- *)
(* mix_psk: KDF with the preshared key (ck4, tau, key) and the hash of tau   *)
(* (h2), then the decryption of the empty text with the key and h2.          *)
(* ------------------------------------------------------------------------- *)

let CS_PSK_TAC =
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME (mk_neg cs_dh2_fail)] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME (mk_neg cs_dh2_fail)] THEN
  ARM_STEPS_TAC CS_EXEC [116] THEN
  ABBREV_TAC `ck3 = wg_kdf1 ck2 (wg_dh spriv ee)` THEN
  SUBGOAL_THEN `LENGTH(ck3:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "ck3" THEN REWRITE_TAC[LENGTH_WG_KDF]; ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 32 < 2 EXP 64`) THEN
  ARM_STEPS_TAC CS_EXEC (117--129) THEN
  CS_KDF_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `read X7 s`; `psk:byte list`; `ck3:byte list`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 130 THEN
  WG_IMP_ASSUM_REWRITE_TAC
   [ASSUME `~(word_add stackpointer (word 4344) = word 0:int64)`;
    ASSUME `~(word_add stackpointer (word 4280) = word 0:int64)`;
    ASSUME `~(word_add stackpointer (word 4504) = word 0:int64)`;
    ASSUME `val(word 32:int64) = 32`] THEN
  ABBREV_TAC `ck4 = wg_kdf_t (wg_hmac ck3 psk) 1` THEN
  ABBREV_TAC `tauv = wg_kdf_t (wg_hmac ck3 psk) 2` THEN
  ABBREV_TAC `kk = wg_kdf_t (wg_hmac ck3 psk) 3` THEN
  SUBGOAL_THEN `LENGTH(ck4:byte list) = 32 /\ LENGTH(tauv:byte list) = 32 /\
                LENGTH(kk:byte list) = 32` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck4"; "tauv"; "kk"] THEN
    REWRITE_TAC[WG_KDF_T_CLAUSES; LENGTH_WG_HMAC];
    ALL_TAC] THEN
  ARM_STEPS_TAC CS_EXEC (131--135) THEN
  WG_MIXH_TAC CS_EXEC cs_st 135 167 173 178 `h1:byte list` `tauv:byte list`
    `32` THEN
  ABBREV_TAC `h2 = wg_mix_hash h1 tauv` THEN
  SUBGOAL_THEN `LENGTH(h2:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "h2" THEN REWRITE_TAC[LENGTH_WG_MIX_HASH]; ALL_TAC] THEN
  ASSUME_TAC(ARITH_RULE `16 + 16 < 2 EXP 32`) THEN
  ASSUME_TAC(ARITH_RULE `32 + 16 < 2 EXP 32`) THEN
  ARM_STEPS_TAC CS_EXEC (180--191) THEN
  CS_DEC0_TAC
   [`read X1 s`; `read X3 s`; `read X4 s`; `read X5 s`; `read X6 s`;
    `kk:byte list`; `SUB_LIST(44,16) (msg:byte list)`; `h2:byte list`;
    `kv:int64`; `ms:int64`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 192 THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `wg_aead_decrypt`)) (concl th)
    then CONV_RULE(DEPTH_CONV WORD_RED_CONV) th else th);;

let cs_dec = `wg_aead_decrypt kk 0 (SUB_LIST(44,16) msg) h2`;;

let cs_dec_fail = mk_eq(cs_dec,`NONE:(byte list)option`);;

let CS_DEC_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cs_dec_fail] THEN
  ARM_STEPS_TAC CS_EXEC [193; 194] THEN
  CS_FAIL1_TAC
   (REWRITE_TAC[wg_consume_response; wg_ephemeral; wg_kdf3; wg_decrypt] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]) 195;;

(* ------------------------------------------------------------------------- *)
(* The hash of the empty text (h3), and under the write lock the check of    *)
(* the state and the ephemeral private key (crypto_memneq of the handshake's *)
(* and the copy) and the copies into the handshake, after which the result   *)
(* is the peer, from join3.                                                  *)
(* ------------------------------------------------------------------------- *)

let CS_DEC_OK_TAC =
  WG_DECRYPTED_TAC cs_dec `p:byte list` 0 THEN
  ARM_STEPS_TAC CS_EXEC (193--198) THEN
  WG_MIXH_TAC CS_EXEC cs_st 198 230 236 241 `h2:byte list`
    `SUB_LIST(44,16) (msg:byte list)` `16` THEN
  ABBREV_TAC `h3 = wg_mix_hash h2 (SUB_LIST(44,16) (msg:byte list))` THEN
  SUBGOAL_THEN `LENGTH(h3:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "h3" THEN REWRITE_TAC[LENGTH_WG_MIX_HASH]; ALL_TAC] THEN
  ARM_STEPS_TAC CS_EXEC (243--244) THEN WG_PLT_TAC CS_EXEC 244 THEN
  WG_CALL_TAC "down_write" CS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 249 THEN
  ARM_STEPS_TAC CS_EXEC (250--256) THEN
  CS_MEMNEQ_TAC [`read X0 s`; `read X1 s`; `read X2 s`;
                 `num_of_bytelist epriv`; `num_of_bytelist epriv`;
                 `pc:num`; `read X30 s`] 257 THEN
  ARM_STEPS_TAC CS_EXEC [258];;

let CS_FINAL_TAC =
  MAP_EVERY (fun k -> WG_BYTES32_WORDS_TAC
     (mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
              mk_comb(`word:num->int64`,mk_small_numeral k))) `s258:armstate`)
    [4312; 4344; 4376] THEN
  WG_WORD_FACT_TAC WG_READ_BYTES32_BYTELIST `src:int64` 60 `msg:byte list` 4
    `s258:armstate` THEN
  ARM_STEPS_TAC CS_EXEC (259--279) THEN
  MAP_EVERY (fun (k,l) ->
    let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,`peer:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral k)) in
    SUBGOAL_THEN
     (subst [a,`a:int64`; l,`l:byte list`]
        `read (memory :> bytes(a:int64,32)) s279 =
         num_of_bytelist(l:byte list)`)
    ASSUME_TAC THENL [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC])
   [360,`ee:byte list`; 456,`h3:byte list`; 488,`ck4:byte list`] THEN
  WG_FACT_CONV_TAC `read (memory :> bytes32 (word_add peer (word 532))) s279`
    (REWRITE_CONV[WG_ZX_ZX_32]) THEN
  WG_PLT_TAC CS_EXEC 279 THEN
  WG_CALL_TAC "up_write" CS_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 284 THEN
  ARM_STEPS_TAC CS_EXEC (285--287) THEN CS_TAIL3_TAC 288 THEN
  SUBGOAL_THEN
   `wg_consume_response (ckb,hb) epriv spriv psk msg = SOME(ee,ck4,h3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wg_consume_response; wg_ephemeral; wg_kdf3; wg_decrypt] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CS_SETUP_TAC THEN CS_PART1_TAC THEN
  ASM_CASES_TAC `hid:bool` THENL [ALL_TAC; CS_NOID_TAC] THEN
  CS_LOOKUP_TAC THEN
  ASM_CASES_TAC `found:bool` THENL [ALL_TAC; CS_NOTFOUND_TAC] THEN
  CS_COPY_TAC THEN
  ASM_CASES_TAC `st:int32 = word 1` THENL [ALL_TAC; CS_BADST_TAC] THEN
  CS_EPH_DH_TAC THEN
  ASM_CASES_TAC cs_dh1_fail THENL [CS_DH1_FAIL_TAC; ALL_TAC] THEN
  CS_DH1_OK_TAC THEN
  ASM_CASES_TAC cs_dh2_fail THENL [CS_DH2_FAIL_TAC; ALL_TAC] THEN
  CS_PSK_TAC THEN
  ASM_CASES_TAC cs_dec_fail THENL [CS_DEC_FAIL_TAC; ALL_TAC] THEN
  CS_DEC_OK_TAC THEN CS_FINAL_TAC);;

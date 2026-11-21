(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_handshake_consume_initiation_spec.ml. The   *)
(* code gives up in seven ways, which join two tails: before the lookup      *)
(* (no static identity, a zero Diffie-Hellman result, the static key not     *)
(* decrypting, no peer) the tail with no peer, and after it (a zero          *)
(* precomputed secret, the timestamp not decrypting, a replay or a flood)    *)
(* the tail that drops the reference to the peer. Both zero the key, hash    *)
(* and chaining key on the stack and release the lock of the static          *)
(* identity, as the success path does after updating the handshake. The      *)
(* three calls of mix_hash are inlined (blake2s_init by stores, then         *)
(* blake2s_update twice and blake2s_final), and the values of the Noise      *)
(* steps are named as they come, with the abbreviations in the expanded      *)
(* forms of the definitions, so that the results of                          *)
(* wg_consume_initiation_kernel can be found by rewriting with them.         *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_consume_initiation_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_handshake_consume_initiation";
    layout_range "plt_down_read"; layout_range "plt_memset";
    layout_range "plt_up_read"; layout_range "plt_memcmp";
    layout_range "plt_ktime_get_coarse_with_offset";
    layout_range "plt_down_write"; layout_range "plt_up_write";
    layout_range "plt_wg_peer_put"];;

let CC_EXEC = WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_EXEC;;

let cc_sim th = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CC_EXEC,0,wireguard_gcc13_O2_mc,th);;

let CC_EPH_TAC =
  cc_sim WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CC_MIX_DH_TAC =
  cc_sim WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CC_DEC_TAC =
  cc_sim WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CC_MEMNEQ_TAC =
  cc_sim WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

(* kdf with the outputs d1 and d2 only (mix_precomputed_dh).                 *)

let CC_KDF_TAC =
  cc_sim (KDF_SPECIALIZE_RULE WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT
           [`d1:int64`; `d2:int64`; `word 0:int64`; `data:int64`;
            `word 32:int64`; `word 0:int64`; `datalen:int64`]);;

let cc_dec_args kb ct al =
  [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
   `read X5 s`; `read X6 s`; kb; ct; al; `kv:int64`; `ms:int64`;
   `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
   `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

(* The kernel's consumption gives up if consume_initiation_static does.      *)

let WG_CONSUME_INITIATION_KERNEL_STATIC_NONE = prove
 (`!spriv spub msg peer ss lts lic now.
     wg_consume_initiation_static spriv spub msg = NONE
     ==> wg_consume_initiation_kernel spriv spub msg peer ss lts lic now =
         NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[wg_consume_initiation_kernel]);;

(* ------------------------------------------------------------------------- *)
(* The setup, as for create_initiation; the stack pointer of the frame is    *)
(* stackpointer + 4128, with the timestamp at + 4252, the key at + 4264, the *)
(* chaining key at + 4296, the hash at + 4328, the static key at + 4360, the *)
(* ephemeral key at + 4392 and the BLAKE2s state at + 4424.                  *)
(* ------------------------------------------------------------------------- *)

let cc_got =
  [`got_memset:num`; `got_memcpy:num`; `got_curve25519_generic:num`;
   `got_down_read:num`; `got_up_read:num`; `got_down_write:num`;
   `got_up_write:num`; `got_memcmp:num`;
   `got_ktime_get_coarse_with_offset:num`; `got_wg_peer_put:num`];;

let cc_data =
  [`data_handshake_init_chaining_key:num`; `data_handshake_init_hash:num`;
   `data_zero_point:num`];;

let CC_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`src:int64`; `wg:int64`; `msg:byte list`; `spub:byte list`;
    `spriv:byte list`; `hid:bool`; `tbl:int64`; `peer:int64`;
    `ss:byte list`; `lts:byte list`; `lic:int64`; `kv:int64`; `ms:int64`;
    `mset:int64`; `mcpy:int64`; `cfn:int64`; `drd:int64`; `urd:int64`;
    `dwr:int64`; `uwr:int64`; `mcmp:int64`; `ktc:int64`; `wpp:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4544 THEN
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
    `memcmp_contract mcmp ea el ev`,"memcmp";
    `ktime_get_coarse_with_offset_contract ktc ea el ev`,"ktime";
    `wg_peer_put_contract wpp ea el ev`,"wg_peer_put"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD)
                  (cc_got @ cc_data)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4128):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add stackpointer (word 4264) = word 0:int64) /\
                ~(word_add stackpointer (word 4296) = word 0:int64)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WG_NONZERO_OFFSET THEN
    EXISTS_TAC `4544` THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; VAL_WORD_0] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) cc_got;;

(* ------------------------------------------------------------------------- *)
(* The tails. From join3 (at step n): zeroing the stack copies, up_read of   *)
(* the identity's lock and the return, with wg_peer_put of the peer (put     *)
(* the label of its contract, for NULL or not) if the result is NULL. The    *)
(* code gives up from join1 (before the lookup) or join4 (after it, with the *)
(* reference dropped), at step n, as wg_consume_initiation_kernel does,      *)
(* proved by none_tac (for any time, with the theorems rths for the          *)
(* assumption, or for the time now1).                                        *)
(* ------------------------------------------------------------------------- *)

let CC_TAIL3_TAC n put =
  ARM_STEPS_TAC CC_EXEC (n--(n+7)) THEN WG_PLT_TAC CC_EXEC (n+7) THEN
  WG_CALL_TAC "up_read" CC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+12) THEN
  ARM_STEPS_TAC CC_EXEC [n+13] THEN
  (match put with
     Some lab ->
       ARM_STEPS_TAC CC_EXEC [n+14; n+15] THEN WG_PLT_TAC CC_EXEC (n+15) THEN
       (if lab = "wg_peer_put_1"
        then WG_CALL_TAC lab CC_EXEC [`read SP s`; `read X30 s`] (n+20)
        else WG_CALL_TAC lab CC_EXEC
               [`read X0 s`; `read SP s`; `read X30 s`] (n+20)) THEN
       ARM_STEPS_TAC CC_EXEC ((n+21)--(n+26))
   | None -> ARM_STEPS_TAC CC_EXEC ((n+14)--(n+19))) THEN
  ENSURES_FINAL_STATE_TAC;;

let CC_FAIL_TAC put none_tac rths n =
  ARM_STEPS_TAC CC_EXEC (n--(n+3)) THEN CC_TAIL3_TAC (n+4) (Some put) THEN
  SUBGOAL_THEN
   `!now. wg_consume_initiation_kernel spriv spub msg peer ss lts lic now =
          NONE`
   (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE rths th)) THENL
   [GEN_TAC THEN none_tac; ALL_TAC] THEN
  ASM_REWRITE_TAC[distinctness "option"] THEN CONV_TAC WORD_REDUCE_CONV;;

let CC_FAIL1_TAC = CC_FAIL_TAC "wg_peer_put_1";;

let CC_FAIL4_TAC = CC_FAIL_TAC "wg_peer_put_2";;

let CC_FAIL4N_TAC none_tac n =
  ARM_STEPS_TAC CC_EXEC (n--(n+3)) THEN
  CC_TAIL3_TAC (n+4) (Some "wg_peer_put_2") THEN
  SUBGOAL_THEN
   `wg_consume_initiation_kernel spriv spub msg peer ss lts lic now1 = NONE`
  ASSUME_TAC THENL [none_tac; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXISTS_TAC [`now1:int64`; `now1:int64`] THEN
  ASM_REWRITE_TAC[distinctness "option"];;

(* No static identity: the result 0.                                         *)

let CC_NOID_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~hid`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  ARM_STEPS_TAC CC_EXEC (35--36) THEN
  CC_TAIL3_TAC 37 (Some "wg_peer_put_1") THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The inlined calls of mix_hash (WG_MIXH_TAC of noise_common.ml), with the  *)
(* hash at stackpointer + 4328 and the BLAKE2s state at stackpointer + 4424. *)
(* ------------------------------------------------------------------------- *)

let cc_st = `word_add stackpointer (word 4424):int64`;;

let CC_MIXH_TAC = WG_MIXH_TAC CC_EXEC cc_st;;

(* ------------------------------------------------------------------------- *)
(* handshake_init: the chaining key and hash copied from the data, and the   *)
(* static public key mixed into the hash (the first inlined mix_hash).       *)
(* ------------------------------------------------------------------------- *)

let CC_DATA_WORDS_TAC s =
  ASSUME_TAC LENGTH_WG_CK0_H0 THEN
  WG_BYTES32_WORDS_TAC `word_add (word pc) (word 37136):int64` s THEN
  WG_BYTES32_WORDS_TAC `word_add (word pc) (word 37168):int64` s THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (find_term ((=) s)) (lhand c) &&
       (can (find_term ((=) `wg_ck0`)) (rand c) ||
        can (find_term ((=) `wg_h0`)) (rand c)) &&
       can (find_term ((=) `SUB_LIST:num#num->byte list->byte list`))
           (rand c)
    then REWRITE_RULE[WORD_ADD] th else th);;

let CC_INIT_TAC =
  WG_PC_REWRITE_TAC [ASSUME `hid:bool`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  ARM_STEPS_TAC CC_EXEC [35] THEN WG_ADRP_TAC THEN
  CC_DATA_WORDS_TAC `s35:armstate` THEN
  ARM_STEPS_TAC CC_EXEC (36--61) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 4328),32)) s61 =
    num_of_bytelist wg_h0` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 4296),32)) s61 =
    num_of_bytelist wg_ck0` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  CC_MIXH_TAC 61 79 84 88 `wg_h0` `spub:byte list` `32`;;

(* ------------------------------------------------------------------------- *)
(* The fields of the message, message_ephemeral, and mix_dh with the static  *)
(* private key, the values named (ee, ck1, h1, then ck2 and k1).             *)
(* ------------------------------------------------------------------------- *)

let CC_MSG_FACTS_TAC s =
  MAP_EVERY (fun (i,k) ->
    MP_TAC(SPECL [`src:int64`; `msg:byte list`; `116`; mk_small_numeral i;
                  mk_small_numeral k; s] WG_READ_BYTES_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN DISCH_TAC)
   [4,4; 8,32; 40,48; 88,28] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(8,32) (msg:byte list)) = 32 /\
                LENGTH(SUB_LIST(40,48) (msg:byte list)) = 48 /\
                LENGTH(SUB_LIST(88,28) (msg:byte list)) = 28`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let CC_EPH_DH_TAC =
  CC_MSG_FACTS_TAC `s89:armstate` THEN
  ASSUME_TAC(SPECL [`wg_h0`; `spub:byte list`] LENGTH_WG_MIX_HASH) THEN
  ARM_STEPS_TAC CC_EXEC (90--94) THEN
  CC_EPH_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `SUB_LIST(8,32) (msg:byte list)`; `wg_ck0`; `wg_mix_hash wg_h0 spub`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 95 THEN
  ABBREV_TAC `ee = SUB_LIST(8,32) (msg:byte list)` THEN
  ABBREV_TAC `ck1 = FST(wg_ephemeral (wg_ck0,wg_mix_hash wg_h0 spub) ee)` THEN
  ABBREV_TAC `h1 = SND(wg_ephemeral (wg_ck0,wg_mix_hash wg_h0 spub) ee)` THEN
  SUBGOAL_THEN `LENGTH(ck1:byte list) = 32 /\ LENGTH(h1:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck1"; "h1"] THEN REWRITE_TAC[LENGTH_WG_EPHEMERAL];
    ALL_TAC] THEN
  ARM_STEPS_TAC CC_EXEC (96--100) THEN
  CC_MIX_DH_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `ck1:byte list`; `spriv:byte list`; `ee:byte list`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `cfn:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 101;;

let cc_dh_fail = `wg_dh spriv ee = wg_zero32`;;

let CC_DH_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cc_dh_fail] THEN
  ARM_STEPS_TAC CC_EXEC [102] THEN
  CC_FAIL1_TAC
   (MATCH_MP_TAC WG_CONSUME_INITIATION_KERNEL_STATIC_NONE THEN
    MATCH_MP_TAC WG_CONSUME_INITIATION_STATIC_DH_ZERO THEN
    ASM_REWRITE_TAC[]) [] 103;;

let CC_DH_OK_TAC =
  WG_ABBREV_NORM_TAC `ck1:byte list` [wg_ephemeral] THEN
  WG_ABBREV_NORM_TAC `h1:byte list` [wg_ephemeral] THEN
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME (mk_neg cc_dh_fail)] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME (mk_neg cc_dh_fail)] THEN
  ARM_STEPS_TAC CC_EXEC [102] THEN
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && can (find_term ((=) `wg_kdf2`)) (concl th)
    then CONJUNCTS_THEN ASSUME_TAC th else failwith "CC_DH_OK_TAC") THEN
  ABBREV_TAC `ck2 = FST(wg_kdf2 ck1 (wg_dh spriv ee))` THEN
  ABBREV_TAC `k1 = SND(wg_kdf2 ck1 (wg_dh spriv ee))` THEN
  SUBGOAL_THEN `LENGTH(ck2:byte list) = 32 /\ LENGTH(k1:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck2"; "k1"] THEN REWRITE_TAC[LENGTH_WG_KDF];
    ALL_TAC] THEN
  WG_ABBREV_NORM_TAC `ck2:byte list` [wg_kdf2] THEN
  WG_ABBREV_NORM_TAC `k1:byte list` [wg_kdf2];;

(* ------------------------------------------------------------------------- *)
(* The static key: chacha20poly1305_decrypt (its result named sk), and the   *)
(* second inlined mix_hash (h2), after which consume_initiation_static gives *)
(* SOME.                                                                     *)
(* ------------------------------------------------------------------------- *)

let CC_STATIC_DEC_TAC =
  SUBGOAL_THEN
   `nonoverlapping (word_add stackpointer (word 4360):int64,48 - 16)
                   (word_add src (word 40),48)` ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
    NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 48:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `48 + 16 < 2 EXP 32`) THEN
  ASSUME_TAC(ARITH_RULE `32 + 16 < 2 EXP 32`) THEN
  ARM_STEPS_TAC CC_EXEC (103--111) THEN
  CC_DEC_TAC (cc_dec_args `k1:byte list` `SUB_LIST(40,48) (msg:byte list)`
                          `h1:byte list`) 112 THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `wg_aead_decrypt`)) (concl th)
    then CONV_RULE(DEPTH_CONV WORD_RED_CONV) th else th);;

let cc_sdec = `wg_aead_decrypt k1 0 (SUB_LIST(40,48) msg) h1`;;

let cc_sdec_fail = mk_eq(cc_sdec,`NONE:(byte list)option`);;

let CC_SDEC_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cc_sdec_fail] THEN
  ARM_STEPS_TAC CC_EXEC [113] THEN
  CC_FAIL1_TAC
   (MATCH_MP_TAC WG_CONSUME_INITIATION_KERNEL_STATIC_NONE THEN
    REWRITE_TAC[wg_consume_initiation_static; wg_handshake_init;
                wg_ephemeral; wg_kdf2; wg_decrypt] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]) [] 114;;

let CC_STATIC_OK_TAC =
  WG_DECRYPTED_TAC cc_sdec `sk:byte list` 32 THEN
  ARM_STEPS_TAC CC_EXEC (113--117) THEN
  CC_MIXH_TAC 117 134 139 143 `h1:byte list`
    `SUB_LIST(40,48) (msg:byte list)` `48` THEN
  ABBREV_TAC `h2 = wg_mix_hash h1 (SUB_LIST(40,48) (msg:byte list))` THEN
  SUBGOAL_THEN `LENGTH(h2:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "h2" THEN REWRITE_TAC[LENGTH_WG_MIX_HASH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wg_consume_initiation_static spriv spub msg = SOME(ee,sk,ck2,h2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wg_consume_initiation_static; wg_handshake_init;
                wg_ephemeral; wg_kdf2; wg_decrypt] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The lookup of the peer, from the assumption about it for the static key   *)
(* of the message, and the test for NULL.                                    *)
(* ------------------------------------------------------------------------- *)

let CC_LOOKUP_TAC =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (fun t ->
             try fst(dest_const t) = "wg_pubkey_lookup_contract"
             with Failure _ -> false)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[wg_pubkey_lookup_contract]
           (MP (SPECL [`ee:byte list`; `sk:byte list`; `ck2:byte list`;
                       `h2:byte list`] th)
               (ASSUME `wg_consume_initiation_static spriv spub msg =
                        SOME(ee,sk,ck2,h2)`)))
    else failwith "CC_LOOKUP_TAC") THEN
  ARM_STEPS_TAC CC_EXEC (145--147) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term ((=) `word(pc + wg_pubkey_hashtable_lookup):int64`))
           (concl th)
    then WG_CONTRACT_SIM_TAC CC_EXEC th
           [`read X1 s`; `read SP s`; `read X30 s`] 148
    else failwith "CC_LOOKUP_TAC") THEN
  ARM_STEPS_TAC CC_EXEC (149--150);;

let CC_NOPEER_TAC =
  WG_PC_REWRITE_TAC [ASSUME `val(peer:int64) = 0`] THEN
  CC_FAIL1_TAC (REWRITE_TAC[wg_consume_initiation_kernel] THEN
                ASM_REWRITE_TAC[GSYM VAL_EQ_0]) [] 151;;

(* ------------------------------------------------------------------------- *)
(* mix_precomputed_dh: the test of the peer's precomputed secret against the *)
(* zero point, then kdf with it (ck3, k2).                                   *)
(* ------------------------------------------------------------------------- *)

let CC_SS_TEST_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~(val(peer:int64) = 0)`] THEN
  SUBGOAL_THEN `~(peer:int64 = word 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
  ARM_STEPS_TAC CC_EXEC (151--153) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC CC_EXEC (154--158) THEN
  CC_MEMNEQ_TAC [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist ss`;
                 `0`; `pc:num`; `read X30 s`] 159 THEN
  ABBREV_TAC `r3 = read X0 s159` THEN ARM_STEPS_TAC CC_EXEC [160] THEN
  SUBGOAL_THEN `(ss = wg_zero32 <=> val(r3:int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_EQ_0; wg_zero32] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WG_NUM_OF_BYTELIST_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let CC_SS_FAIL_TAC =
  WG_PC_REWRITE_TAC
   [EQ_MP (ASSUME `(ss = wg_zero32 <=> val(r3:int64) = 0)`)
          (ASSUME `ss = wg_zero32`)] THEN
  CC_FAIL4_TAC
   (REWRITE_TAC[wg_consume_initiation_kernel] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[WG_CONSUME_INITIATION_TIMESTAMP_SS_ZERO])
   [ASSUME `ss = wg_zero32`] 161;;

let CC_KDF_SS_TAC =
  WG_PC_REWRITE_TAC
   [REWRITE_RULE[ASSUME `~(ss = wg_zero32)`]
      (ASSUME `(ss = wg_zero32 <=> val(r3:int64) = 0)`)] THEN
  SUBGOAL_THEN `~(val(r3:int64) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `ss = wg_zero32 <=> val(r3:int64) = 0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_STEPS_TAC CC_EXEC (161--170) THEN
  CC_KDF_TAC
   [`read X0 s`; `read X1 s`; `read X3 s`; `read X6 s`; `read X7 s`;
    `ss:byte list`; `ck2:byte list`; `mset:int64`; `ea:int64`;
    `el:num`; `ev:num`; `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 171 THEN
  WG_IMP_ASSUM_REWRITE_TAC
   [ASSUME `~(word_add stackpointer (word 4296) = word 0:int64)`;
    ASSUME `~(word_add stackpointer (word 4264) = word 0:int64)`] THEN
  ABBREV_TAC `ck3 = wg_kdf_t (wg_hmac ck2 ss) 1` THEN
  ABBREV_TAC `k2 = wg_kdf_t (wg_hmac ck2 ss) 2` THEN
  SUBGOAL_THEN `LENGTH(ck3:byte list) = 32 /\ LENGTH(k2:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck3"; "k2"] THEN
    REWRITE_TAC[WG_KDF_T_CLAUSES; LENGTH_WG_HMAC];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The timestamp: chacha20poly1305_decrypt (named tb), and the third inlined *)
(* mix_hash (h3).                                                            *)
(* ------------------------------------------------------------------------- *)

let CC_TS_DEC_TAC =
  SUBGOAL_THEN
   `nonoverlapping (word_add stackpointer (word 4252):int64,28 - 16)
                   (word_add src (word 88),28)` ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
    NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 28:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `28 + 16 < 2 EXP 32`) THEN
  ARM_STEPS_TAC CC_EXEC (172--179) THEN
  CC_DEC_TAC (cc_dec_args `k2:byte list` `SUB_LIST(88,28) (msg:byte list)`
                          `h2:byte list`) 180 THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `wg_aead_decrypt`)) (concl th)
    then CONV_RULE(DEPTH_CONV WORD_RED_CONV) th else th);;

let cc_tdec = `wg_aead_decrypt k2 0 (SUB_LIST(88,28) msg) h2`;;

let cc_tdec_fail = mk_eq(cc_tdec,`NONE:(byte list)option`);;

let CC_TS_NONE_TAC =
  REWRITE_TAC[wg_consume_initiation_kernel] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wg_consume_initiation_timestamp; wg_kdf2; wg_decrypt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[COND_ID];;

let CC_TDEC_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cc_tdec_fail] THEN
  ARM_STEPS_TAC CC_EXEC [181] THEN
  CC_FAIL4_TAC CC_TS_NONE_TAC [] 182;;

let CC_TS_OK_TAC =
  WG_DECRYPTED_TAC cc_tdec `tb:byte list` 12 THEN
  ARM_STEPS_TAC CC_EXEC (181--185) THEN
  CC_MIXH_TAC 185 204 209 213 `h2:byte list`
    `SUB_LIST(88,28) (msg:byte list)` `28` THEN
  ABBREV_TAC `h3 = wg_mix_hash h2 (SUB_LIST(88,28) (msg:byte list))` THEN
  SUBGOAL_THEN `LENGTH(h3:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "h3" THEN REWRITE_TAC[LENGTH_WG_MIX_HASH]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The replay and flood checks (under down_read of the handshake's lock):    *)
(* memcmp with the latest timestamp (its result mc1), the time now1, and the *)
(* branch on the flags, whose condition is cc_accept.                        *)
(* ------------------------------------------------------------------------- *)

let cc_accept =
 `wg_bytes_lt (lts:byte list) tb /\
  val(word_add (lic:int64) (word 20000000)) <= val(now1:int64)`;;

let CC_CHECKS_TAC =
  ARM_STEPS_TAC CC_EXEC (215--216) THEN WG_PLT_TAC CC_EXEC 216 THEN
  WG_CALL_TAC "down_read" CC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 221 THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 12:int64)`) THEN
  ARM_STEPS_TAC CC_EXEC (222--225) THEN WG_PLT_TAC CC_EXEC 225 THEN
  WG_CALL_TAC "memcmp" CC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `tb:byte list`; `lts:byte list`;
    `read X30 s`] 230 THEN
  ABBREV_TAC `mc1 = read X0 s230` THEN
  ARM_STEPS_TAC CC_EXEC (231--237) THEN WG_PLT_TAC CC_EXEC 237 THEN
  WG_CALL_TAC "ktime" CC_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 242 THEN
  ABBREV_TAC `now1 = read X0 s242` THEN
  ARM_STEPS_TAC CC_EXEC (243--247) THEN WG_PLT_TAC CC_EXEC 247 THEN
  WG_CALL_TAC "up_read" CC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 252 THEN
  ARM_STEPS_TAC CC_EXEC (253--255) THEN
  W(fun (asl,w) ->
    let s = rand w in
    let pcth = snd(find (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),v)
          -> s' = s
      | _ -> false) asl) in
    let c = rand(lhand(rator(rand(concl pcth)))) in
    SUBGOAL_THEN (mk_eq(c,cc_accept)) ASSUME_TAC THENL
     [REWRITE_TAC[WORD_SUB_0; INT_SUB_RZERO; WG_ZX3] THEN
      REWRITE_TAC[VAL_EQ_0; WG_CSET_HI_ZERO] THEN
      REWRITE_TAC[TAUT `(p <=> ~(x = x)) <=> ~p`] THEN
      REWRITE_TAC[WG_IVAL_POS; TAUT `(if p then q else F) <=> p /\ q`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]);;

let CC_PC_ACCEPT_TAC th2 =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = cc_accept
    then WG_PC_REWRITE_TAC [th; th2] else failwith "CC_PC_ACCEPT_TAC");;

let CC_REJECT_TAC =
  CC_PC_ACCEPT_TAC (ASSUME (mk_neg cc_accept)) THEN
  CC_FAIL4N_TAC
   (REWRITE_TAC[wg_consume_initiation_kernel] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wg_consume_initiation_timestamp; wg_kdf2; wg_decrypt] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]) 256;;

(* ------------------------------------------------------------------------- *)
(* Success: down_write, the copies of the ephemeral key, the timestamp (the  *)
(* second memcmp, under the write lock, gives the same result), the hash,    *)
(* the chaining key and the sender index into the handshake, and the time    *)
(* now2 for the last consumption.                                            *)
(* ------------------------------------------------------------------------- *)

let CC_COPIES_TAC =
  CC_PC_ACCEPT_TAC (ASSUME cc_accept) THEN
  ARM_STEPS_TAC CC_EXEC (256--257) THEN WG_PLT_TAC CC_EXEC 257 THEN
  WG_CALL_TAC "down_write" CC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 262 THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 4392):int64`
                       `s262:armstate` THEN
  ARM_STEPS_TAC CC_EXEC (263--273) THEN WG_PLT_TAC CC_EXEC 273 THEN
  WG_CALL_TAC "memcmp" CC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `tb:byte list`; `lts:byte list`;
    `read X30 s`] 278 THEN
  ABBREV_TAC `mc2 = read X0 s278` THEN ARM_STEPS_TAC CC_EXEC (279--280) THEN
  WG_PC_REWRITE_TAC [WORD_SUB_0; INT_SUB_RZERO; VAL_EQ_0;
    TAUT `(p <=> ~(x = x)) <=> ~p`; WG_IVAL_POS;
    ASSUME `&0 < ival(word_zx(mc2:int64):int32)`] THEN
  WG_WORD_FACT_TAC WG_READ_BYTES64_BYTELIST
    `word_add stackpointer (word 4252):int64` 12 `tb:byte list` 0
    `s280:armstate` THEN
  WG_WORD_FACT_TAC WG_READ_BYTES32_BYTELIST
    `word_add stackpointer (word 4252):int64` 12 `tb:byte list` 8
    `s280:armstate` THEN
  ARM_STEPS_TAC CC_EXEC (281--284) THEN
  WG_FACT_CONV_TAC `read (memory :> bytes32 (word_add peer (word 528))) s284`
    (REWRITE_CONV[WG_ZX_ZX_32]) THEN
  MP_TAC(SPECL [`word_add peer (word 520):int64`; `tb:byte list`;
                `s284:armstate`] WG_BYTES12_OF_WORDS) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add peer (word 360),32)) s284 =
                num_of_bytelist ee` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 4328):int64`
                       `s284:armstate` THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 4296):int64`
                       `s284:armstate` THEN
  WG_WORD_FACT_TAC WG_READ_BYTES32_BYTELIST `src:int64` 116 `msg:byte list`
    4 `s284:armstate` THEN
  ARM_STEPS_TAC CC_EXEC (285--299) THEN WG_PLT_TAC CC_EXEC 299 THEN
  WG_CALL_TAC "ktime" CC_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 304 THEN
  ABBREV_TAC `now2 = read X0 s304` THEN
  ARM_STEPS_TAC CC_EXEC (305--307) THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add peer (word 456),32)) s307 =
                num_of_bytelist h3` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add peer (word 488),32)) s307 =
                num_of_bytelist ck3` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  WG_FACT_CONV_TAC `read (memory :> bytes32 (word_add peer (word 532))) s307`
    (REWRITE_CONV[WG_ZX_ZX_32]);;

(* From step n: the state, up_write of the handshake's lock and the tail.    *)

let CC_UPW_TAIL_TAC n =
  ARM_STEPS_TAC CC_EXEC (n--(n+4)) THEN WG_PLT_TAC CC_EXEC (n+4) THEN
  WG_CALL_TAC "up_write" CC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+9) THEN
  ARM_STEPS_TAC CC_EXEC ((n+10)--(n+12)) THEN
  CC_TAIL3_TAC (n+13) None;;

(* The result of wg_consume_initiation_kernel, and the postcondition.        *)

let CC_SUCCESS_FINAL_TAC =
  SUBGOAL_THEN
   `wg_consume_initiation_kernel spriv spub msg peer ss lts lic now1 =
    SOME(ee,tb,ck3,h3)` ASSUME_TAC THENL
   [REWRITE_TAC[wg_consume_initiation_kernel] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wg_consume_initiation_timestamp; wg_kdf2; wg_decrypt] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXISTS_TAC [`now1:int64`; `now2:int64`] THEN
  ASM_REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CC_SETUP_TAC THEN
  ARM_STEPS_TAC CC_EXEC (1--27) THEN WG_PLT_TAC CC_EXEC 27 THEN
  WG_CALL_TAC "down_read" CC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 32 THEN
  ARM_STEPS_TAC CC_EXEC (33--34) THEN
  ASM_CASES_TAC `hid:bool` THENL [ALL_TAC; CC_NOID_TAC] THEN
  CC_INIT_TAC THEN CC_EPH_DH_TAC THEN
  ASM_CASES_TAC cc_dh_fail THENL [CC_DH_FAIL_TAC; ALL_TAC] THEN
  CC_DH_OK_TAC THEN CC_STATIC_DEC_TAC THEN
  ASM_CASES_TAC cc_sdec_fail THENL [CC_SDEC_FAIL_TAC; ALL_TAC] THEN
  CC_STATIC_OK_TAC THEN CC_LOOKUP_TAC THEN
  ASM_CASES_TAC `val(peer:int64) = 0` THENL [CC_NOPEER_TAC; ALL_TAC] THEN
  CC_SS_TEST_TAC THEN
  ASM_CASES_TAC `ss = wg_zero32` THENL [CC_SS_FAIL_TAC; ALL_TAC] THEN
  CC_KDF_SS_TAC THEN CC_TS_DEC_TAC THEN
  ASM_CASES_TAC cc_tdec_fail THENL [CC_TDEC_FAIL_TAC; ALL_TAC] THEN
  CC_TS_OK_TAC THEN CC_CHECKS_TAC THEN
  ASM_CASES_TAC cc_accept THENL [ALL_TAC; CC_REJECT_TAC] THEN
  CC_COPIES_TAC THEN
  ASM_CASES_TAC `ival(word_sub (lic:int64) now2) < &0` THENL
   [WG_PC_REWRITE_TAC [ASSUME `ival(word_sub (lic:int64) now2) < &0`] THEN
    ARM_STEPS_TAC CC_EXEC [308] THEN CC_UPW_TAIL_TAC 309 THEN
    CC_SUCCESS_FINAL_TAC;
    WG_PC_REWRITE_TAC [ASSUME `~(ival(word_sub (lic:int64) now2) < &0)`] THEN
    CC_UPW_TAIL_TAC 308 THEN CC_SUCCESS_FINAL_TAC]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_handshake_create_response_spec.ml, as for   *)
(* create_initiation: the code gives up if the handshake is not in the state *)
(* HANDSHAKE_CONSUMED_INITIATION, if curve25519_generate_public fails or if  *)
(* either Diffie-Hellman result (mix_dh with a NULL key) is zero, and all    *)
(* paths join the tail (up_write, up_read, zeroing the key and return). The  *)
(* empty plaintext is encrypted with chacha20poly1305_encrypt of NULL and 0. *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_create_response_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_handshake_create_response";
    layout_range "plt_wait_for_random_bytes"; layout_range "plt_down_read";
    layout_range "plt_down_write"; layout_range "plt_get_random_bytes";
    layout_range "plt_up_write"; layout_range "plt_up_read"];;

let CR_EXEC = WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_EXEC;;

let cr_sim th = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CR_EXEC,0,wireguard_gcc13_O2_mc,th);;

let CR_GENPUB_TAC =
  cr_sim WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CR_EPH_TAC =
  cr_sim WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CR_MIX_DH_TAC =
  cr_sim WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CR_KDF_TAC = cr_sim WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CR_MIX_HASH_TAC =
  cr_sim WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CR_INSERT_TAC =
  cr_sim WIREGUARD_INDEX_HASHTABLE_INSERT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

(* chacha20poly1305_encrypt of the empty plaintext from NULL, with the       *)
(* conditions and frame regions for it that become trivial removed.          *)

let CR_ENC0_TH =
  let th1 = SPECL [`dst:int64`; `word 0:int64`; `word 0:int64`]
    WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT in
  GEN `dst:int64`
   (CONV_RULE (DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
               REWRITE_CONV[ALL; ADD_CLAUSES; WG_READ_BYTES_0] THENC
               SIMP_CONV[NONOVERLAPPING_TRIVIAL] THENC
               ONCE_DEPTH_CONV WG_MAYCHANGE_DROP_EMPTY_CONV) th1);;

let CR_ENC0_TAC = cr_sim CR_ENC0_TH;;

let cr_mix_hash_args hb sb =
  [`read X0 s`; `read X1 s`; `read X2 s`; hb; sb;
   `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
   `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

let cr_mixdh_args ckb pubb =
  [`read X0 s`; `read X2 s`; `read X3 s`; ckb; `wg_clamp r`; pubb;
   `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
   `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
   `cfn:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* The setup (the frame is at stackpointer + 4144, with the key at + 4224    *)
(* and tau at + 4256), and to the test of the state.                         *)
(* ------------------------------------------------------------------------- *)

let cr_got =
  [`got_memset:num`; `got_memcpy:num`; `got_curve25519_generic:num`;
   `got_wait_for_random_bytes:num`; `got_get_random_bytes:num`;
   `got_down_read:num`; `got_up_read:num`; `got_down_write:num`;
   `got_up_write:num`];;

let CR_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `hs:int64`; `si:int64`; `stw:int32`; `ckb:byte list`;
    `hb:byte list`; `repub:byte list`; `rspub:byte list`; `psk:byte list`;
    `rindex:int32`; `peer:int64`; `dev:int64`; `table:int64`; `kv:int64`;
    `ms:int64`; `mset:int64`; `mcpy:int64`; `cfn:int64`; `wfrb:int64`;
    `grb:int64`; `drd:int64`; `urd:int64`; `dwr:int64`; `uwr:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`memset_contract mset ea el ev`,"memset";
    `memcpy_contract mcpy ea el ev`,"memcpy";
    `wait_for_random_bytes_contract wfrb ea el ev`,"wait_for_random_bytes";
    `get_random_bytes_contract grb ea el ev`,"get_random_bytes";
    `rwsem_contract drd ea el ev`,"down_read";
    `rwsem_contract urd ea el ev`,"up_read";
    `rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) cr_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 25; 26; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4144):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add hs (word 248) = word 0:int64) /\
                ~(word_add stackpointer (word 4224) = word 0:int64) /\
                ~(word_add stackpointer (word 4256) = word 0:int64)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WG_NONZERO_OFFSET THENL
     [EXISTS_TAC `336`; EXISTS_TAC `4288`; EXISTS_TAC `4288`] THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; VAL_WORD_0] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) cr_got;;

let CR_PART1_TAC =
  ARM_STEPS_TAC CR_EXEC (1--12) THEN WG_PLT_TAC CR_EXEC 12 THEN
  WG_CALL_TAC "wait_for_random_bytes" CR_EXEC
   [`read SP s`; `read X30 s`] 17 THEN
  ARM_STEPS_TAC CR_EXEC (18--20) THEN WG_PLT_TAC CR_EXEC 20 THEN
  WG_CALL_TAC "down_read" CR_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 25 THEN
  ARM_STEPS_TAC CR_EXEC (26--27) THEN WG_PLT_TAC CR_EXEC 27 THEN
  WG_CALL_TAC "down_write" CR_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 32 THEN
  ARM_STEPS_TAC CR_EXEC (33--35);;

(* From join2 (at step n): up_write, up_read, zeroing the key and return.    *)

let CR_TAIL2_TAC n =
  ARM_STEPS_TAC CR_EXEC [n; n+1] THEN WG_PLT_TAC CR_EXEC (n+1) THEN
  WG_CALL_TAC "up_write" CR_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+6) THEN
  ARM_STEPS_TAC CR_EXEC ((n+7)--(n+9)) THEN WG_PLT_TAC CR_EXEC (n+9) THEN
  WG_CALL_TAC "up_read" CR_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+14) THEN
  ARM_STEPS_TAC CR_EXEC ((n+15)--(n+22)) THEN
  ENSURES_FINAL_STATE_TAC;;

(* Not in the state 2: the result 0.                                         *)

let CR_NOST_TAC =
  WG_PC_REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0; WG_ZX_ZX_32;
                     ASSUME `~(stw:int32 = word 2)`] THEN
  ARM_STEPS_TAC CR_EXEC [36] THEN CR_TAIL2_TAC 37 THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  EXISTS_TAC `REPLICATE 32 (word 0):byte list` THEN
  REWRITE_TAC[LENGTH_REPLICATE];;

(* Giving up because cond holds, from join1 (at step n).                     *)

let CR_FAIL_TAC cond n =
  ARM_STEPS_TAC CR_EXEC [n] THEN CR_TAIL2_TAC (n+1) THEN
  SUBGOAL_THEN
   `!sender. wg_create_response (ckb,hb) repub rspub psk (wg_clamp r) sender
               rindex = NONE`
   (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[ASSUME cond] th))
  THENL
   [GEN_TAC THEN MATCH_MP_TAC WG_CREATE_RESPONSE_NONE THEN
    UNDISCH_TAC cond THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  EXISTS_TAC `r:byte list` THEN
  ASM_REWRITE_TAC[distinctness "option"] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The type and receiver index in the message, the ephemeral key from        *)
(* random bytes, clamped, and curve25519_generate_public into the message.   *)
(* ------------------------------------------------------------------------- *)

let CR_RANDOM_TAC =
  WG_PC_REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0; WG_ZX_ZX_32;
                     ASSUME `stw:int32 = word 2`] THEN
  ARM_STEPS_TAC CR_EXEC (36--41) THEN WG_PLT_TAC CR_EXEC 41 THEN
  WG_CALL_TAC "wait_for_random_bytes" CR_EXEC
   [`read SP s`; `read X30 s`] 46 THEN
  ARM_STEPS_TAC CR_EXEC (47--49) THEN WG_PLT_TAC CR_EXEC 49 THEN
  WG_CALL_TAC "get_random_bytes" CR_EXEC
   [`read X0 s`; `read X1 s`; `read SP s`; `read X30 s`] 54 THEN
  ABBREV_TAC `b0 = read (memory :> bytes8 (word_add hs (word 56))) s54` THEN
  ABBREV_TAC
   `rmid = read (memory :> bytes (word_add hs (word 57),30)) s54` THEN
  ABBREV_TAC `b31 = read (memory :> bytes8 (word_add hs (word 87))) s54` THEN
  ARM_STEPS_TAC CR_EXEC (55--64) THEN
  WG_FACT_NORM_TAC `read (memory :> bytes8 (word_add hs (word 56))) s64`
    `word_and (b0:byte) (word 248)` THEN
  WG_FACT_NORM_TAC `read (memory :> bytes8 (word_add hs (word 87))) s64`
    `word_or (word_and (b31:byte) (word 127)) (word 64)` THEN
  MP_TAC(SPECL [`word_add hs (word 56):int64`; `b0:byte`; `rmid:num`;
                `b31:byte`; `s64:armstate`] WG_CLAMP_BYTES) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `r = CONS (b0:byte) (APPEND (bytelist_of_num 30 rmid) [b31])` THEN
  SUBGOAL_THEN `LENGTH(r:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP LENGTH_WG_CLAMP (ASSUME `LENGTH(r:byte list) = 32`)) THEN
  CR_GENPUB_TAC
   [`read X0 s`; `read X1 s`; `wg_clamp r`; `cfn:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 65;;

let cr_gp_fail =
  `wg_clamp r = wg_zero32 \/ wg_dh_pubkey (wg_clamp r) = wg_zero32`;;

let CR_GP_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cr_gp_fail] THEN
  ARM_STEPS_TAC CR_EXEC [66] THEN CR_FAIL_TAC cr_gp_fail 67;;

(* ------------------------------------------------------------------------- *)
(* message_ephemeral (in place in the message), and mix_dh (with a NULL key) *)
(* with the remote ephemeral and then the remote static key.                 *)
(* ------------------------------------------------------------------------- *)

let CR_GP_OK_TAC =
  SUBGOAL_THEN `~(wg_clamp r = wg_zero32) /\
                ~(wg_dh_pubkey (wg_clamp r) = wg_zero32)` STRIP_ASSUME_TAC
  THENL [UNDISCH_TAC (mk_neg cr_gp_fail) THEN CONV_TAC TAUT; ALL_TAC] THEN
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME `~(wg_clamp r = wg_zero32)`] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME `~(wg_clamp r = wg_zero32)`;
     ASSUME `~(wg_dh_pubkey (wg_clamp r) = wg_zero32)`] THEN
  ARM_STEPS_TAC CR_EXEC [66] THEN
  ASSUME_TAC(SPEC `wg_clamp r` LENGTH_WG_DH_PUBKEY) THEN
  ARM_STEPS_TAC CR_EXEC (67--74) THEN
  CR_EPH_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `wg_dh_pubkey (wg_clamp r)`; `ckb:byte list`; `hb:byte list`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 75 THEN
  ABBREV_TAC
   `ck1 = FST(wg_ephemeral (ckb,hb) (wg_dh_pubkey (wg_clamp r)))` THEN
  ABBREV_TAC
   `h1 = SND(wg_ephemeral (ckb,hb) (wg_dh_pubkey (wg_clamp r)))` THEN
  SUBGOAL_THEN `LENGTH(ck1:byte list) = 32 /\ LENGTH(h1:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck1"; "h1"] THEN REWRITE_TAC[LENGTH_WG_EPHEMERAL];
    ALL_TAC] THEN
  WG_ABBREV_NORM_TAC `ck1:byte list` [wg_ephemeral] THEN
  WG_ABBREV_NORM_TAC `h1:byte list` [wg_ephemeral] THEN
  ARM_STEPS_TAC CR_EXEC (76--80) THEN
  CR_MIX_DH_TAC (cr_mixdh_args `ck1:byte list` `repub:byte list`) 81;;

let cr_dh1_fail = `wg_dh (wg_clamp r) repub = wg_zero32`;;

let CR_DH1_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cr_dh1_fail] THEN
  ARM_STEPS_TAC CR_EXEC (82--84) THEN CR_FAIL_TAC cr_dh1_fail 85;;

let CR_DH1_OK_TAC =
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME (mk_neg cr_dh1_fail)] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME (mk_neg cr_dh1_fail)] THEN
  ARM_STEPS_TAC CR_EXEC [82] THEN
  ABBREV_TAC `ck2 = wg_kdf1 ck1 (wg_dh (wg_clamp r) repub)` THEN
  SUBGOAL_THEN `LENGTH(ck2:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "ck2" THEN REWRITE_TAC[LENGTH_WG_KDF]; ALL_TAC] THEN
  ARM_STEPS_TAC CR_EXEC (83--87) THEN
  CR_MIX_DH_TAC (cr_mixdh_args `ck2:byte list` `rspub:byte list`) 88;;

let cr_dh2_fail = `wg_dh (wg_clamp r) rspub = wg_zero32`;;

let CR_DH2_FAIL_TAC =
  WG_REG_REWRITE_TAC `X0` [ASSUME cr_dh2_fail] THEN
  ARM_STEPS_TAC CR_EXEC (89--92) THEN CR_FAIL_TAC cr_dh2_fail 93;;

(* ------------------------------------------------------------------------- *)
(* KDF with the preshared key (ck4, tau, key), the hash of tau, the empty    *)
(* AEAD (es) and its hash, wg_index_hashtable_insert and the state.          *)
(* ------------------------------------------------------------------------- *)

let CR_KDF3_TAC =
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME (mk_neg cr_dh2_fail)] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME (mk_neg cr_dh2_fail)] THEN
  ARM_STEPS_TAC CR_EXEC (89--90) THEN
  ABBREV_TAC `ck3 = wg_kdf1 ck2 (wg_dh (wg_clamp r) rspub)` THEN
  SUBGOAL_THEN `LENGTH(ck3:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "ck3" THEN REWRITE_TAC[LENGTH_WG_KDF]; ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 32 < 2 EXP 64`) THEN
  ARM_STEPS_TAC CR_EXEC (91--102) THEN
  CR_KDF_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `read X6 s`; `read X7 s`; `psk:byte list`; `ck3:byte list`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 103 THEN
  WG_IMP_ASSUM_REWRITE_TAC
   [ASSUME `~(word_add hs (word 248) = word 0:int64)`;
    ASSUME `~(word_add stackpointer (word 4224) = word 0:int64)`;
    ASSUME `~(word_add stackpointer (word 4256) = word 0:int64)`;
    ASSUME `val(word 32:int64) = 32`];;

let CR_HASH_ENC_TAC =
  ABBREV_TAC `ck4 = wg_kdf_t (wg_hmac ck3 psk) 1` THEN
  ABBREV_TAC `tauv = wg_kdf_t (wg_hmac ck3 psk) 2` THEN
  ABBREV_TAC `kk = wg_kdf_t (wg_hmac ck3 psk) 3` THEN
  SUBGOAL_THEN `LENGTH(ck4:byte list) = 32 /\ LENGTH(tauv:byte list) = 32 /\
                LENGTH(kk:byte list) = 32` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck4"; "tauv"; "kk"] THEN
    REWRITE_TAC[WG_KDF_T_CLAUSES; LENGTH_WG_HMAC];
    ALL_TAC] THEN
  ASSUME_TAC(ARITH_RULE `32 + 32 < 2 EXP 64`) THEN
  ARM_STEPS_TAC CR_EXEC (104--107) THEN
  CR_MIX_HASH_TAC (cr_mix_hash_args `h1:byte list` `tauv:byte list`) 108 THEN
  ABBREV_TAC `h2 = wg_mix_hash h1 tauv` THEN
  SUBGOAL_THEN `LENGTH(h2:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "h2" THEN REWRITE_TAC[LENGTH_WG_MIX_HASH]; ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH)) THEN
  ASSUME_TAC(CONJUNCT1 num_of_bytelist) THEN
  ASSUME_TAC(ARITH_RULE `16 < 2 EXP 32`) THEN
  ASSUME_TAC(ARITH_RULE `32 + 16 < 2 EXP 32`) THEN
  ARM_STEPS_TAC CR_EXEC (109--119) THEN
  CR_ENC0_TAC
   [`read X0 s`; `read X3 s`; `read X4 s`; `read X5 s`; `read X6 s`;
    `kk:byte list`; `[]:byte list`; `h2:byte list`; `kv:int64`; `ms:int64`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 120 THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `wg_aead`)) (concl th)
    then CONV_RULE(DEPTH_CONV WORD_RED_CONV) th else th) THEN
  ABBREV_TAC `es = wg_aead kk 0 [] h2` THEN
  SUBGOAL_THEN `LENGTH(es:byte list) = 16` ASSUME_TAC THENL
   [EXPAND_TAC "es" THEN REWRITE_TAC[LENGTH_WG_AEAD; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 16:int64)`) THEN
  ARM_STEPS_TAC CR_EXEC (121--124) THEN
  CR_MIX_HASH_TAC (cr_mix_hash_args `h2:byte list` `es:byte list`) 125 THEN
  ABBREV_TAC `h3 = wg_mix_hash h2 es` THEN
  ARM_STEPS_TAC CR_EXEC (126--130) THEN
  CR_INSERT_TAC
   [`read X0 s`; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`] 131 THEN
  ABBREV_TAC
   `sender = read (memory :> bytes32 (word_add hs (word 28))) s131` THEN
  ARM_STEPS_TAC CR_EXEC (132--136);;

(* The result of wg_create_response, and the postcondition.                  *)

let CR_FINAL_TAC =
  WG_FACT_CONV_TAC `read (memory :> bytes32 (word_add dst (word 4))) s136`
    (REWRITE_CONV[WG_ZX_ZX_32]) THEN
  WG_FACT_CONV_TAC `read (memory :> bytes32 (word_add dst (word 8))) s136`
    (REWRITE_CONV[WG_ZX_ZX_32]) THEN
  CR_TAIL2_TAC 137 THEN
  SUBGOAL_THEN
   `wg_create_response (ckb,hb) repub rspub psk (wg_clamp r) sender rindex =
    SOME(wg_response_msg sender rindex (wg_dh_pubkey (wg_clamp r)) es,ck4,h3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wg_create_response; wg_ephemeral; wg_encrypt; wg_kdf3] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`dst:int64`; `sender:int32`; `rindex:int32`;
                `wg_dh_pubkey (wg_clamp r)`; `es:byte list`; `s159:armstate`]
               WG_RESPONSE_MSG_BYTES) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_WG_DH_PUBKEY] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  EXISTS_TAC `r:byte list` THEN
  ASM_REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CR_SETUP_TAC THEN CR_PART1_TAC THEN
  ASM_CASES_TAC `stw:int32 = word 2` THENL [ALL_TAC; CR_NOST_TAC] THEN
  CR_RANDOM_TAC THEN
  ASM_CASES_TAC cr_gp_fail THENL [CR_GP_FAIL_TAC; ALL_TAC] THEN
  CR_GP_OK_TAC THEN
  ASM_CASES_TAC cr_dh1_fail THENL [CR_DH1_FAIL_TAC; ALL_TAC] THEN
  CR_DH1_OK_TAC THEN
  ASM_CASES_TAC cr_dh2_fail THENL [CR_DH2_FAIL_TAC; ALL_TAC] THEN
  CR_KDF3_TAC THEN CR_HASH_ENC_TAC THEN CR_FINAL_TAC);;

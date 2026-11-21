(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_handshake_create_initiation_spec.ml. The    *)
(* code is straight-line apart from the four ways it gives up, which all     *)
(* join the tail (up_write, up_read, zeroing the key on the stack and        *)
(* return): no static identity, curve25519_generate_public failing (a zero   *)
(* key), mix_dh failing (a zero Diffie-Hellman result) and a zero            *)
(* precomputed secret. The kernel functions are simulated with their         *)
(* contracts and the functions of the image with their theorems; the random  *)
(* bytes, the time and the sender index are named as they come, and the      *)
(* bytes that the code writes are related to the values of                   *)
(* wg_create_initiation with the lemmas of noise_common.ml.                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_create_initiation_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_handshake_create_initiation";
    layout_range "plt_wait_for_random_bytes"; layout_range "plt_down_read";
    layout_range "plt_down_write"; layout_range "plt_get_random_bytes";
    layout_range "plt_ktime_get_real_ts64"; layout_range "plt_up_write";
    layout_range "plt_up_read"];;

let CI_EXEC = WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_EXEC;;

let ci_sim th = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CI_EXEC,0,wireguard_gcc13_O2_mc,th);;

let CI_MIX_HASH_TAC =
  ci_sim WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CI_GENPUB_TAC = ci_sim
  WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CI_EPH_TAC =
  ci_sim WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CI_MIX_DH_TAC =
  ci_sim WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CI_ENC_TAC =
  ci_sim WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CI_MEMNEQ_TAC =
  ci_sim WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let CI_INSERT_TAC =
  ci_sim WIREGUARD_INDEX_HASHTABLE_INSERT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

(* kdf with the outputs d1 and d2 only (mix_precomputed_dh).                 *)

let CI_KDF_TAC =
  ci_sim (KDF_SPECIALIZE_RULE WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT
           [`d1:int64`; `d2:int64`; `word 0:int64`; `data:int64`;
            `word 32:int64`; `word 0:int64`; `datalen:int64`]);;

let ci_mix_hash_args hb sb =
  [`read X0 s`; `read X1 s`; `read X2 s`; hb; sb;
   `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
   `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

let ci_enc_args kb pl al =
  [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
   `read X5 s`; `read X6 s`; kb; pl; al; `kv:int64`; `ms:int64`;
   `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
   `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* The setup. The GOT entries and the data that the code reads are given     *)
(* in the form word_add (word pc) (word n) that the simulation uses, and     *)
(* the GOT entries also in the form of the theorems for the callees.         *)
(* ------------------------------------------------------------------------- *)

let ci_got =
  [`got_memset:num`; `got_memcpy:num`; `got_curve25519_generic:num`;
   `got_wait_for_random_bytes:num`; `got_get_random_bytes:num`;
   `got_ktime_get_real_ts64:num`; `got_down_read:num`; `got_up_read:num`;
   `got_down_write:num`; `got_up_write:num`];;

let ci_data =
  [`data_handshake_init_chaining_key:num`; `data_handshake_init_hash:num`;
   `data_zero_point:num`];;

let CI_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `hs:int64`; `si:int64`; `spub:byte list`; `hid:bool`;
    `rpub:byte list`; `ss:byte list`; `peer:int64`; `dev:int64`;
    `table:int64`; `kv:int64`; `ms:int64`; `mset:int64`; `mcpy:int64`;
    `cfn:int64`; `wfrb:int64`; `grb:int64`; `ktm:int64`; `drd:int64`;
    `urd:int64`; `dwr:int64`; `uwr:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4304 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`memset_contract mset ea el ev`,"memset";
    `memcpy_contract mcpy ea el ev`,"memcpy";
    `curve25519_generic_contract cfn ea el ev`,"curve25519";
    `wait_for_random_bytes_contract wfrb ea el ev`,"wait_for_random_bytes";
    `get_random_bytes_contract grb ea el ev`,"get_random_bytes";
    `ktime_get_real_ts64_contract ktm ea el ev`,"ktime_get_real_ts64";
    `rwsem_contract drd ea el ev`,"down_read";
    `rwsem_contract urd ea el ev`,"up_read";
    `rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD)
                  (ci_got @ ci_data)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4144):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add hs (word 248) = word 0:int64) /\
                ~(word_add stackpointer (word 4272) = word 0:int64)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WG_NONZERO_OFFSET THENL
     [EXISTS_TAC `336`; EXISTS_TAC `4304`] THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; VAL_WORD_0] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) ci_got;;

(* ------------------------------------------------------------------------- *)
(* To the test of has_identity: wait_for_random_bytes, down_read of the      *)
(* identity's lock and down_write of the handshake's.                        *)
(* ------------------------------------------------------------------------- *)

let CI_PART1_TAC =
  ARM_STEPS_TAC CI_EXEC (1--15) THEN WG_PLT_TAC CI_EXEC 15 THEN
  WG_CALL_TAC "wait_for_random_bytes" CI_EXEC
   [`read SP s`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC CI_EXEC (21--23) THEN WG_PLT_TAC CI_EXEC 23 THEN
  WG_CALL_TAC "down_read" CI_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC CI_EXEC (29--30) THEN WG_PLT_TAC CI_EXEC 30 THEN
  WG_CALL_TAC "down_write" CI_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 35 THEN
  ARM_STEPS_TAC CI_EXEC (36--38);;

(* ------------------------------------------------------------------------- *)
(* From join3 (at step n): up_write, up_read, zeroing the key and return.    *)
(* ------------------------------------------------------------------------- *)

let CI_TAIL_TAC n =
  ARM_STEPS_TAC CI_EXEC [n; n+1] THEN WG_PLT_TAC CI_EXEC (n+1) THEN
  WG_CALL_TAC "up_write" CI_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+6) THEN
  ARM_STEPS_TAC CI_EXEC ((n+7)--(n+9)) THEN WG_PLT_TAC CI_EXEC (n+9) THEN
  WG_CALL_TAC "up_read" CI_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+14) THEN
  ARM_STEPS_TAC CI_EXEC ((n+15)--(n+23)) THEN
  ENSURES_FINAL_STATE_TAC;;

(* No static identity: the result 0.                                         *)

let CI_NOID_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~hid`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  ARM_STEPS_TAC CI_EXEC [39] THEN CI_TAIL_TAC 40 THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  EXISTS_TAC `REPLICATE 32 (word 0):byte list` THEN
  REWRITE_TAC[LENGTH_REPLICATE];;

(* Giving up because cond holds, from join1 (at step n): the result 0, as    *)
(* wg_create_initiation is NONE for the random bytes r and any timestamp     *)
(* and sender index.                                                         *)

let CI_FAIL_TAC cond n =
  ARM_STEPS_TAC CI_EXEC [n; n+1] THEN CI_TAIL_TAC (n+2) THEN
  SUBGOAL_THEN
   `!ts sender. wg_create_initiation spub rpub ss (wg_clamp r) ts sender =
                NONE`
   (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[ASSUME cond] th))
  THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC WG_CREATE_INITIATION_NONE THEN
    UNDISCH_TAC cond THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXISTS_TAC [`r:byte list`; `word 0:int64`; `word 0:int64`] THEN
  ASM_REWRITE_TAC[distinctness "option"] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* handshake_init: the chaining key and hash copied from the data and the    *)
(* remote static key mixed into the hash.                                    *)
(* ------------------------------------------------------------------------- *)

let CI_DATA_WORDS_TAC =
  ASSUME_TAC LENGTH_WG_CK0_H0 THEN
  WG_BYTES32_WORDS_TAC `word_add (word pc) (word 37136):int64`
                       `s41:armstate` THEN
  WG_BYTES32_WORDS_TAC `word_add (word pc) (word 37168):int64`
                       `s41:armstate` THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (find_term ((=) `s41:armstate`)) (lhand c) &&
       (can (find_term ((=) `wg_ck0`)) (rand c) ||
        can (find_term ((=) `wg_h0`)) (rand c)) &&
       can (find_term ((=) `SUB_LIST:num#num->byte list->byte list`))
           (rand c)
    then REWRITE_RULE[WORD_ADD] th else th);;

let CI_INIT_TAC =
  ARM_STEPS_TAC CI_EXEC (39--41) THEN WG_ADRP_TAC THEN CI_DATA_WORDS_TAC THEN
  ARM_STEPS_TAC CI_EXEC (42--59) THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add hs (word 216),32)) s59 =
                num_of_bytelist wg_h0` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add hs (word 248),32)) s59 =
                num_of_bytelist wg_ck0` ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `32 + 32 < 2 EXP 64`) THEN
  ARM_STEPS_TAC CI_EXEC [60] THEN
  CI_MIX_HASH_TAC (ci_mix_hash_args `wg_h0` `rpub:byte list`) 61;;

(* ------------------------------------------------------------------------- *)
(* The ephemeral key: wait_for_random_bytes, get_random_bytes into the       *)
(* handshake, the random bytes named (b0, the 30 of rmid and b31, the list   *)
(* r), the clamping, and curve25519_generate_public into the message.        *)
(* ------------------------------------------------------------------------- *)

let CI_RANDOM_TAC =
  ARM_STEPS_TAC CI_EXEC [62] THEN WG_PLT_TAC CI_EXEC 62 THEN
  WG_CALL_TAC "wait_for_random_bytes" CI_EXEC
   [`read SP s`; `read X30 s`] 67 THEN
  ARM_STEPS_TAC CI_EXEC (68--70) THEN WG_PLT_TAC CI_EXEC 70 THEN
  WG_CALL_TAC "get_random_bytes" CI_EXEC
   [`read X0 s`; `read X1 s`; `read SP s`; `read X30 s`] 75 THEN
  ABBREV_TAC `b0 = read (memory :> bytes8 (word_add hs (word 56))) s75` THEN
  ABBREV_TAC
   `rmid = read (memory :> bytes (word_add hs (word 57),30)) s75` THEN
  ABBREV_TAC `b31 = read (memory :> bytes8 (word_add hs (word 87))) s75` THEN
  ARM_STEPS_TAC CI_EXEC (76--85) THEN
  WG_FACT_NORM_TAC `read (memory :> bytes8 (word_add hs (word 56))) s85`
    `word_and (b0:byte) (word 248)` THEN
  WG_FACT_NORM_TAC `read (memory :> bytes8 (word_add hs (word 87))) s85`
    `word_or (word_and (b31:byte) (word 127)) (word 64)` THEN
  MP_TAC(SPECL [`word_add hs (word 56):int64`; `b0:byte`; `rmid:num`;
                `b31:byte`; `s85:armstate`] WG_CLAMP_BYTES) THEN
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
  CI_GENPUB_TAC
   [`read X0 s`; `read X1 s`; `wg_clamp r`; `cfn:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 86;;

let ci_gp_fail =
  `wg_clamp r = wg_zero32 \/ wg_dh_pubkey (wg_clamp r) = wg_zero32`;;

let CI_GP_OK_TAC =
  SUBGOAL_THEN `~(wg_clamp r = wg_zero32) /\
                ~(wg_dh_pubkey (wg_clamp r) = wg_zero32)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC (mk_neg ci_gp_fail) THEN CONV_TAC TAUT; ALL_TAC] THEN
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME `~(wg_clamp r = wg_zero32)`] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME `~(wg_clamp r = wg_zero32)`;
     ASSUME `~(wg_dh_pubkey (wg_clamp r) = wg_zero32)`] THEN
  ARM_STEPS_TAC CI_EXEC [87];;

(* ------------------------------------------------------------------------- *)
(* message_ephemeral (in place in the message), mix_dh with the remote       *)
(* static key, and the new chaining keys and hashes named.                   *)
(* ------------------------------------------------------------------------- *)

let CI_EPH_DH_TAC =
  ASSUME_TAC(SPEC `wg_clamp r` LENGTH_WG_DH_PUBKEY) THEN
  ASSUME_TAC(SPECL [`wg_h0`; `rpub:byte list`] LENGTH_WG_MIX_HASH) THEN
  ARM_STEPS_TAC CI_EXEC (88--92) THEN
  CI_EPH_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `wg_dh_pubkey (wg_clamp r)`; `wg_ck0`; `wg_mix_hash wg_h0 rpub`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 93 THEN
  ABBREV_TAC `ck1 = FST(wg_ephemeral (wg_ck0,wg_mix_hash wg_h0 rpub)
                            (wg_dh_pubkey (wg_clamp r)))` THEN
  ABBREV_TAC `h1 = SND(wg_ephemeral (wg_ck0,wg_mix_hash wg_h0 rpub)
                           (wg_dh_pubkey (wg_clamp r)))` THEN
  SUBGOAL_THEN `LENGTH(ck1:byte list) = 32 /\ LENGTH(h1:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck1"; "h1"] THEN REWRITE_TAC[LENGTH_WG_EPHEMERAL];
    ALL_TAC] THEN
  ARM_STEPS_TAC CI_EXEC (94--98) THEN
  CI_MIX_DH_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `ck1:byte list`; `wg_clamp r`; `rpub:byte list`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `cfn:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 99;;

let ci_dh_fail = `wg_dh (wg_clamp r) rpub = wg_zero32`;;

let CI_DH_OK_TAC =
  WG_IMP_ASSUM_REWRITE_TAC[ASSUME (mk_neg ci_dh_fail)] THEN
  WG_REG_REWRITE_TAC `X0` [ASSUME (mk_neg ci_dh_fail)] THEN
  ARM_STEPS_TAC CI_EXEC (100--101) THEN
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) && can (find_term ((=) `wg_kdf2`)) (concl th)
    then CONJUNCTS_THEN ASSUME_TAC th else failwith "CI_DH_OK_TAC") THEN
  ABBREV_TAC `ck2 = FST(wg_kdf2 ck1 (wg_dh (wg_clamp r) rpub))` THEN
  ABBREV_TAC `k1 = SND(wg_kdf2 ck1 (wg_dh (wg_clamp r) rpub))` THEN
  SUBGOAL_THEN `LENGTH(ck2:byte list) = 32 /\ LENGTH(k1:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck2"; "k1"] THEN REWRITE_TAC[LENGTH_WG_KDF];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* message_encrypt of the static public key: chacha20poly1305_encrypt to the *)
(* message and mix_hash of the result (es).                                  *)
(* ------------------------------------------------------------------------- *)

let CI_STATIC_TAC =
  SUBGOAL_THEN `nonoverlapping (word_add dst (word 40):int64,32 + 16) (si,32)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(ARITH_RULE `32 + 16 < 2 EXP 32`) THEN
  ARM_STEPS_TAC CI_EXEC (102--110) THEN
  CI_ENC_TAC (ci_enc_args `k1:byte list` `spub:byte list` `h1:byte list`)
    111 THEN
  WG_FACT_CONV_TAC
   `read (memory :> bytes (word_add dst (word 40),32 + 16)) s111`
   (NUM_REDUCE_CONV THENC DEPTH_CONV WORD_RED_CONV) THEN
  ABBREV_TAC `es = wg_aead k1 0 spub h1` THEN
  SUBGOAL_THEN `LENGTH(es:byte list) = 48` ASSUME_TAC THENL
   [EXPAND_TAC "es" THEN ASM_REWRITE_TAC[LENGTH_WG_AEAD] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 48:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `32 + 48 < 2 EXP 64`) THEN
  ARM_STEPS_TAC CI_EXEC (112--116) THEN
  CI_MIX_HASH_TAC (ci_mix_hash_args `h1:byte list` `es:byte list`) 117 THEN
  ABBREV_TAC `h2 = wg_mix_hash h1 es` THEN
  SUBGOAL_THEN `LENGTH(h2:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "h2" THEN REWRITE_TAC[LENGTH_WG_MIX_HASH]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* mix_precomputed_dh: the test of the precomputed secret against the zero   *)
(* point (__crypto_memneq), then kdf with it.                                *)
(* ------------------------------------------------------------------------- *)

let CI_SS_TEST_TAC =
  ARM_STEPS_TAC CI_EXEC [118] THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC CI_EXEC (119--122) THEN
  CI_MEMNEQ_TAC [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist ss`;
                 `0`; `pc:num`; `read X30 s`] 123 THEN
  ABBREV_TAC `r3 = read X0 s123` THEN ARM_STEPS_TAC CI_EXEC [124] THEN
  SUBGOAL_THEN `(ss = wg_zero32 <=> val(r3:int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_EQ_0; wg_zero32] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WG_NUM_OF_BYTELIST_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let ci_ss_fail = `ss = wg_zero32`;;

let CI_SS_FAIL_TAC =
  WG_PC_REWRITE_TAC
   [EQ_MP (ASSUME `(ss = wg_zero32 <=> val(r3:int64) = 0)`)
          (ASSUME ci_ss_fail)] THEN
  CI_FAIL_TAC ci_ss_fail 125;;

let CI_KDF_SS_TAC =
  WG_PC_REWRITE_TAC
   [REWRITE_RULE[ASSUME (mk_neg ci_ss_fail)]
     (ASSUME `(ss = wg_zero32 <=> val(r3:int64) = 0)`)] THEN
  ARM_STEPS_TAC CI_EXEC (125--133) THEN
  CI_KDF_TAC
   [`read X0 s`; `read X1 s`; `read X3 s`; `read X6 s`; `read X7 s`;
    `ss:byte list`; `ck2:byte list`; `mset:int64`; `ea:int64`;
    `el:num`; `ev:num`; `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 134 THEN
  WG_IMP_ASSUM_REWRITE_TAC
   [ASSUME `~(word_add hs (word 248) = word 0:int64)`;
    ASSUME `~(word_add stackpointer (word 4272) = word 0:int64)`] THEN
  ABBREV_TAC `ck3 = wg_kdf_t (wg_hmac ck2 ss) 1` THEN
  ABBREV_TAC `k2 = wg_kdf_t (wg_hmac ck2 ss) 2` THEN
  SUBGOAL_THEN `LENGTH(ck3:byte list) = 32 /\ LENGTH(k2:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ck3"; "k2"] THEN
    REWRITE_TAC[WG_KDF_T_CLAUSES; LENGTH_WG_HMAC];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* tai64n_now: ktime_get_real_ts64 into the struct timespec64 on the stack   *)
(* (its 16 bytes named tsn; the seconds sec and nanoseconds nsec, and the    *)
(* byte tb that the code loads), and the 12 bytes of the timestamp.          *)
(* ------------------------------------------------------------------------- *)

let CI_TIME_TAC =
  ARM_STEPS_TAC CI_EXEC (135--137) THEN WG_PLT_TAC CI_EXEC 137 THEN
  WG_CALL_TAC "ktime_get_real_ts64" CI_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 142 THEN
  ABBREV_TAC
   `tsn = read (memory :> bytes (word_add stackpointer (word 4256),16))
               s142` THEN
  MP_TAC(SPECL [`word_add stackpointer (word 4256):int64`; `16`; `tsn:num`;
                `0`; `s142:armstate`] WG_READ_BYTES64_OF_NUM) THEN
  MP_TAC(SPECL [`word_add stackpointer (word 4256):int64`; `16`; `tsn:num`;
                `11`; `s142:armstate`] WG_READ_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0; DIV_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `sec:int64 = word(tsn MOD 18446744073709551616)` THEN
  ABBREV_TAC
   `tb:byte = word((tsn DIV 309485009821345068724781056) MOD 256)` THEN
  ARM_STEPS_TAC CI_EXEC (143--158) THEN
  WG_FACT_NORM_TAC
   `read (memory :> bytes32 (word_add stackpointer (word 4252))) s158`
   `word_zx (tb:byte):int32` THEN
  ABBREV_TAC
   `nsec:int64 =
    word((tsn DIV 18446744073709551616) MOD 18446744073709551616)` THEN
  SUBGOAL_THEN `tb:byte = word_subword (nsec:int64) (24,8)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `word ((tsn DIV 309485009821345068724781056) MOD 256):byte = tb` THEN
    UNDISCH_TAC
     `word ((tsn DIV 18446744073709551616) MOD 18446744073709551616):int64 =
      nsec` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[WG_TAI64N_NSEC_BYTE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add stackpointer (word 4244):int64`; `sec:int64`;
                `nsec:int64`; `tb:byte`; `s158:armstate`] WG_TAI64N_BYTES) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* ------------------------------------------------------------------------- *)
(* message_encrypt of the timestamp (et), the sender index from              *)
(* wg_index_hashtable_insert, the state, and the tail.                       *)
(* ------------------------------------------------------------------------- *)

let CI_TIMESTAMP_TAC =
  SUBGOAL_THEN `nonoverlapping (word_add dst (word 88):int64,12 + 16)
                               (word_add stackpointer (word 4244),12)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(SPECL [`sec:int64`; `nsec:int64`] LENGTH_WG_TAI64N) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 12:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `12 + 16 < 2 EXP 32`) THEN
  ARM_STEPS_TAC CI_EXEC [159] THEN
  CI_ENC_TAC (ci_enc_args `k2:byte list` `wg_tai64n sec nsec`
                          `h2:byte list`) 160 THEN
  WG_FACT_CONV_TAC
   `read (memory :> bytes (word_add dst (word 88),12 + 16)) s160`
   (NUM_REDUCE_CONV THENC DEPTH_CONV WORD_RED_CONV) THEN
  ABBREV_TAC `et = wg_aead k2 0 (wg_tai64n sec nsec) h2` THEN
  SUBGOAL_THEN `LENGTH(et:byte list) = 28` ASSUME_TAC THENL
   [EXPAND_TAC "et" THEN REWRITE_TAC[LENGTH_WG_AEAD; LENGTH_WG_TAI64N] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 28:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `32 + 28 < 2 EXP 64`) THEN
  ARM_STEPS_TAC CI_EXEC (161--164) THEN
  CI_MIX_HASH_TAC (ci_mix_hash_args `h2:byte list` `et:byte list`) 165;;

let CI_INSERT_TAIL_TAC =
  ARM_STEPS_TAC CI_EXEC (166--170) THEN
  CI_INSERT_TAC
   [`read X0 s`; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`] 171 THEN
  ABBREV_TAC
   `sender = read (memory :> bytes32 (word_add hs (word 28))) s171` THEN
  ARM_STEPS_TAC CI_EXEC (172--175) THEN
  WG_FACT_NORM_TAC `read (memory :> bytes32 (word_add dst (word 4))) s175`
    `sender:int32` THEN
  CI_TAIL_TAC 176;;

(* The result of wg_create_initiation, and the postcondition.                *)

let CI_SOME_TAC =
  SUBGOAL_THEN `~(val(r3:int64) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `ss = wg_zero32 <=> val(r3:int64) = 0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wg_create_initiation spub rpub ss (wg_clamp r) (wg_tai64n sec nsec)
                         sender =
    SOME(wg_initiation_msg sender (wg_dh_pubkey (wg_clamp r)) es et, ck3,
         wg_mix_hash h2 et)` ASSUME_TAC THENL
   [REWRITE_TAC[wg_create_initiation; wg_handshake_init; wg_ephemeral;
                wg_encrypt; wg_kdf2] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC
     ["et"; "h2"; "es"; "k2"; "ck3"; "k1"; "ck2"; "h1"; "ck1"] THEN
    REWRITE_TAC[wg_ephemeral; wg_kdf2] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
    ALL_TAC];;

let CI_FINAL_TAC =
  MP_TAC(SPECL [`dst:int64`; `sender:int32`; `wg_dh_pubkey (wg_clamp r)`;
                `es:byte list`; `et:byte list`; `s199:armstate`]
               WG_INITIATION_MSG_BYTES) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_WG_DH_PUBKEY] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  MAP_EVERY EXISTS_TAC [`r:byte list`; `sec:int64`; `nsec:int64`] THEN
  ASM_REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CI_SETUP_TAC THEN CI_PART1_TAC THEN
  ASM_CASES_TAC `hid:bool` THENL [ALL_TAC; CI_NOID_TAC] THEN
  WG_PC_REWRITE_TAC [ASSUME `hid:bool`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  CI_INIT_TAC THEN CI_RANDOM_TAC THEN
  ASM_CASES_TAC ci_gp_fail THENL
   [WG_REG_REWRITE_TAC `X0` [ASSUME ci_gp_fail] THEN
    ARM_STEPS_TAC CI_EXEC [87] THEN CI_FAIL_TAC ci_gp_fail 88;
    ALL_TAC] THEN
  CI_GP_OK_TAC THEN CI_EPH_DH_TAC THEN
  ASM_CASES_TAC ci_dh_fail THENL
   [WG_REG_REWRITE_TAC `X0` [ASSUME ci_dh_fail] THEN
    ARM_STEPS_TAC CI_EXEC (100--101) THEN CI_FAIL_TAC ci_dh_fail 102;
    ALL_TAC] THEN
  CI_DH_OK_TAC THEN CI_STATIC_TAC THEN CI_SS_TEST_TAC THEN
  ASM_CASES_TAC ci_ss_fail THENL [CI_SS_FAIL_TAC; ALL_TAC] THEN
  CI_KDF_SS_TAC THEN CI_TIME_TAC THEN CI_TIMESTAMP_TAC THEN
  CI_INSERT_TAIL_TAC THEN CI_SOME_TAC THEN CI_FINAL_TAC);;

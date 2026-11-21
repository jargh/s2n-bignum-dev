(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of the handshake functions of     *)
(* noise.c (the wg_noise_handshake functions): the lengths of the values of  *)
(* the Noise steps in common/wireguard.ml, the bytes that the code writes    *)
(* for the clamped ephemeral key, the TAI64N timestamp and the messages,     *)
(* tactics for the facts about one register or memory word in the current    *)
(* state, and for an inlined mix_hash and the result of a decryption.        *)
(* ========================================================================= *)

needs "common/wireguard_kernel.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The lengths of the values of the handshake.                               *)
(* ------------------------------------------------------------------------- *)

let LENGTH_WG_MIX_HASH = prove
 (`!h (x:byte list). LENGTH(wg_mix_hash h x) = 32`,
  REWRITE_TAC[wg_mix_hash; LENGTH_WG_HASH]);;

let LENGTH_WG_KDF = prove
 (`!k (x:byte list).
     LENGTH(wg_kdf1 k x) = 32 /\
     LENGTH(FST(wg_kdf2 k x)) = 32 /\ LENGTH(SND(wg_kdf2 k x)) = 32`,
  REWRITE_TAC[wg_kdf1; wg_kdf2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WG_KDF_T_CLAUSES; LENGTH_WG_HMAC]);;

let LENGTH_WG_EPHEMERAL = prove
 (`!ck h (e:byte list).
     LENGTH(FST(wg_ephemeral (ck,h) e)) = 32 /\
     LENGTH(SND(wg_ephemeral (ck,h) e)) = 32`,
  REWRITE_TAC[wg_ephemeral; LENGTH_WG_KDF; LENGTH_WG_MIX_HASH]);;

let LENGTH_WG_AEAD = prove
 (`!k n (p:byte list) a. LENGTH(wg_aead k n p a) = LENGTH p + 16`,
  REWRITE_TAC[wg_aead; aead_chacha20_poly1305_encrypt;
              aead_chacha20_poly1305_tag; poly1305] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_APPEND; chacha20_encrypt; LENGTH_LIST_OF_SEQ;
              LENGTH_BYTELIST_OF_NUM]);;

let LENGTH_WG_TAI64N = prove
 (`!sec nsec. LENGTH(wg_tai64n sec nsec) = 12`,
  REWRITE_TAC[wg_tai64n; LENGTH_APPEND; LENGTH_REVERSE;
              LENGTH_BYTELIST_OF_NUM] THEN ARITH_TAC);;

let LENGTH_WG_CLAMP = prove
 (`!k:byte list. LENGTH k = 32 ==> LENGTH(wg_clamp k) = 32`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wg_clamp; LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_WG_DH_PUBKEY = prove
 (`!k. LENGTH(wg_dh_pubkey k) = 32`,
  REWRITE_TAC[wg_dh_pubkey; LENGTH_WG_DH]);;

let LENGTH_WG_CK0_H0 = prove
 (`LENGTH wg_ck0 = 32 /\ LENGTH wg_h0 = 32`,
  REWRITE_TAC[wg_ck0; wg_h0; LENGTH_WG_HASH]);;

(* ------------------------------------------------------------------------- *)
(* An initiation is not created if a key or Diffie-Hellman result is zero.   *)
(* ------------------------------------------------------------------------- *)

let WG_CREATE_INITIATION_NONE = prove
 (`!spub rpub ss epriv ts sender.
     epriv = wg_zero32 \/ wg_dh_pubkey epriv = wg_zero32 \/
     wg_dh epriv rpub = wg_zero32 \/ ss = wg_zero32
     ==> wg_create_initiation spub rpub ss epriv ts sender = NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[wg_create_initiation; wg_handshake_init; wg_ephemeral;
              wg_encrypt; wg_kdf2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The clamping of 32 random bytes b0, the 30 bytes of rmid and b31, as the  *)
(* code does it, in place, to the first and last bytes.                      *)
(* ------------------------------------------------------------------------- *)

let WG_CLAMP_CONS = prove
 (`!b0 (m:byte list) b31.
     LENGTH m = 30
     ==> wg_clamp (CONS b0 (APPEND m [b31])) =
         CONS (word_and b0 (word 248))
              (APPEND m [word_or (word_and b31 (word 127)) (word 64)])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wg_clamp; APPEND; CONS_11] THEN
  REWRITE_TAC[EL; HD] THEN
  SUBGOAL_THEN `SUB_LIST(1,30) (CONS b0 (APPEND m [b31])) = m:byte list`
  SUBST1_TAC THENL
   [REWRITE_TAC[ONE; SUB_LIST_CLAUSES] THEN
    ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT; LE_REFL] THEN
    MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[num_CONV `31`; EL; TL] THEN
  ASM_REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

let WG_CLAMP_BYTES = prove
 (`!a:int64 b0 rmid b31 s.
     read (memory :> bytes8 a) s = word_and b0 (word 248) /\
     read (memory :> bytes(word_add a (word 1),30)) s = rmid /\
     read (memory :> bytes8 (word_add a (word 31))) s =
       word_or (word_and b31 (word 127)) (word 64)
     ==> read (memory :> bytes(a,32)) s =
         num_of_bytelist
          (wg_clamp(CONS b0 (APPEND (bytelist_of_num 30 rmid) [b31])))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rmid < 256 EXP 30` ASSUME_TAC THENL
   [EXPAND_TAC "rmid" THEN
    MATCH_MP_TAC(ARITH_RULE `x < 2 EXP (8 * 30) ==> x < 256 EXP 30`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  SIMP_TAC[WG_CLAMP_CONS; LENGTH_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[num_of_bytelist; WG_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `32 = 1 + 30 + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Big-endian bytes, for the TAI64N timestamp. A byte list of a numeral      *)
(* length as the explicit list, and the bytes of a 64-bit word as subwords.  *)
(* ------------------------------------------------------------------------- *)

let rec WG_BYTELIST_OF_NUM_CONV tm =
  match tm with
    Comb(Comb(Const("bytelist_of_num",_),k),n) when is_numeral k ->
      if dest_small_numeral k = 0
      then REWR_CONV (CONJUNCT1 bytelist_of_num) tm
      else (LAND_CONV num_CONV THENC
            REWR_CONV (CONJUNCT2 bytelist_of_num) THENC
            RAND_CONV WG_BYTELIST_OF_NUM_CONV) tm
  | _ -> failwith "WG_BYTELIST_OF_NUM_CONV";;

let WG_VAL_BYTE_OF = prove
 (`!(w:int64) k. (val w DIV 2 EXP k) MOD 256 = val(word_subword w (k,8):byte)`,
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let WG_VAL_BYTES_OF =
  map (fun k -> CONV_RULE (NUM_REDUCE_CONV THENC REWRITE_CONV[DIV_1])
                  (SPEC (mk_small_numeral k) (SPEC `w:int64` WG_VAL_BYTE_OF)))
      [0; 8; 16; 24; 32; 40; 48; 56];;

let WG_VAL_BYTE_MOD = prove
 (`!b:byte. val b MOD 256 = val b`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  ARITH_TAC);;

let WG_EXPAND_BYTES_TAC =
  CONV_TAC(ONCE_DEPTH_CONV WG_BYTELIST_OF_NUM_CONV) THEN
  REWRITE_TAC[REVERSE; APPEND; num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[DIV_DIV; MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC WG_VAL_BYTES_OF THEN REWRITE_TAC[WG_VAL_BYTE_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV;;

let WG_NUM_OF_BYTELIST_REVERSE_8 = prove
 (`!y:int64. num_of_bytelist(REVERSE(bytelist_of_num 8 (val y))) =
             val(word_bytereverse y)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `word_bytereverse (y:int64) =
    word_join
     (word_join (word_join (word_subword y (0,8):byte)
                           (word_subword y (8,8):byte):int16)
                (word_join (word_subword y (16,8):byte)
                           (word_subword y (24,8):byte):int16):int32)
     (word_join (word_join (word_subword y (32,8):byte)
                           (word_subword y (40,8):byte):int16)
                (word_join (word_subword y (48,8):byte)
                           (word_subword y (56,8):byte):int16):int32)`
  SUBST1_TAC THENL [BITBLAST_TAC; ALL_TAC] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
           DIMINDEX_64; ARITH] THEN
  WG_EXPAND_BYTES_TAC THEN ARITH_TAC);;

let WG_TAI64N_NSEC = prove
 (`!nsec:int64.
     num_of_bytelist(REVERSE(bytelist_of_num 4
       (val(word_and nsec (word_not(word 0xffffff)))))) =
     val(word_subword nsec (24,8):byte)`,
  GEN_TAC THEN WG_EXPAND_BYTES_TAC THEN
  SUBGOAL_THEN
   `word_subword (word_and nsec (word_not(word 0xffffff)):int64) (0,8):byte =
    word 0 /\
    word_subword (word_and nsec (word_not(word 0xffffff)):int64) (8,8):byte =
    word 0 /\
    word_subword (word_and nsec (word_not(word 0xffffff)):int64) (16,8):byte =
    word 0 /\
    word_subword (word_and nsec (word_not(word 0xffffff)):int64) (24,8):byte =
    word_subword nsec (24,8)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN BITBLAST_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC);;

(* Memory words as numbers.                                                  *)

let WG_READ_BYTES_VAL = prove
 (`(!x:int64 s:armstate.
      read (memory :> bytes(x,8)) s = val(read (memory :> bytes64 x) s)) /\
   (!x:int64 s:armstate.
      read (memory :> bytes(x,4)) s = val(read (memory :> bytes32 x) s))`,
  REWRITE_TAC[WG_READ_WORDS_BYTES; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP (8 * 8) ==> x < 2 EXP 64`);
    MATCH_MP_TAC(ARITH_RULE `x < 2 EXP (8 * 4) ==> x < 2 EXP 32`)] THEN
  REWRITE_TAC[READ_BYTES_BOUND]);;

(* The 12 bytes that tai64n_now writes: the byte-reversed seconds plus the   *)
(* TAI64 label, and the top byte of the nanoseconds (the rest being zero     *)
(* after the rounding) as a 32-bit word. The byte from the 16 bytes of the   *)
(* struct timespec64 that the code loads is that byte of tv_nsec.            *)

let WG_TAI64N_BYTES = prove
 (`!a:int64 sec nsec (tb:byte) s.
     read (memory :> bytes64 a) s =
       word_bytereverse (word_add sec (word 0x400000000000000a)) /\
     read (memory :> bytes32 (word_add a (word 8))) s = word_zx tb /\
     tb = word_subword nsec (24,8)
     ==> read (memory :> bytes(a,12)) s = num_of_bytelist(wg_tai64n sec nsec)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wg_tai64n; WG_NUM_OF_BYTELIST_APPEND; LENGTH_REVERSE;
              LENGTH_BYTELIST_OF_NUM; WG_NUM_OF_BYTELIST_REVERSE_8;
              WG_TAI64N_NSEC] THEN
  SUBGOAL_THEN `12 = 8 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; WG_READ_BYTES_VAL] THEN
  ASM_REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  REWRITE_TAC[ISPECL [`word 4611686018427387914:int64`; `sec:int64`]
                     WORD_ADD_SYM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `word_subword (nsec:int64) (24,8):byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let WG_TAI64N_NSEC_BYTE = prove
 (`!tsn. word((tsn DIV 309485009821345068724781056) MOD 256):byte =
         word_subword
          (word((tsn DIV 18446744073709551616) MOD 18446744073709551616):int64)
          (24,8)`,
  GEN_TAC THEN
  REWRITE_TAC[word_subword; VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`;
              ARITH_RULE `309485009821345068724781056 = 2 EXP 64 * 2 EXP 24`;
              ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  SPEC_TAC(`tsn DIV 2 EXP 64`,`x:num`) THEN GEN_TAC THEN
  REWRITE_TAC[DIV_MOD; MOD_MOD_EXP_MIN; GSYM EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The first 116 bytes of an initiation message from its fields.             *)
(* ------------------------------------------------------------------------- *)

let WG_INITIATION_MSG_BYTES = prove
 (`!dst:int64 sender e es et s.
     LENGTH e = 32 /\ LENGTH es = 48 /\
     read (memory :> bytes32 dst) s = word 1 /\
     read (memory :> bytes32 (word_add dst (word 4))) s = sender /\
     read (memory :> bytes(word_add dst (word 8),32)) s = num_of_bytelist e /\
     read (memory :> bytes(word_add dst (word 40),48)) s =
     num_of_bytelist es /\
     read (memory :> bytes(word_add dst (word 88),28)) s = num_of_bytelist et
     ==> read (memory :> bytes(dst,116)) s =
         num_of_bytelist(wg_initiation_msg sender e es et)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wg_initiation_msg; wg_le32; WG_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `116 = 4 + 4 + 32 + 48 + 28` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; WG_READ_BYTES_VAL] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `sender:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32; VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Addresses in a region that does not contain the address 0.                *)
(* ------------------------------------------------------------------------- *)

let WG_NONZERO_OFFSET = prove
 (`!a:int64 n k. nonoverlapping (a,n) (word 0:int64,1) /\ k < n
                 ==> ~(word_add a (word k) = word 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_0; VAL_WORD;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `0`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 1`; CONG; ADD_CLAUSES; MOD_0] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the fact about the PC, a register or a memory word in the     *)
(* current state: a conversion on the value of the PC, rewriting the value   *)
(* of a register, a new value equal to the old one (proved by BITBLAST_TAC)  *)
(* and a conversion on a fact whose left side matches a pattern.             *)
(* ------------------------------------------------------------------------- *)

let WG_PC_CONV_TAC conv : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let pcfact th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),v)
        -> s' = s
    | _ -> false in
  FIRST_X_ASSUM(fun th -> if pcfact th
                          then ASSUME_TAC(CONV_RULE (RAND_CONV conv) th)
                          else failwith "WG_PC_CONV_TAC") gl;;

let WG_REG_REWRITE_TAC reg ths : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let isfact th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),r),s')),v)
        -> s' = s && r = reg
    | _ -> false in
  FIRST_X_ASSUM(fun th -> if isfact th
                          then ASSUME_TAC(REWRITE_RULE ths th)
                          else failwith "WG_REG_REWRITE_TAC") gl;;

let WG_FACT_NORM_TAC lhs_tm new_rhs : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = lhs_tm then
      ASSUME_TAC(TRANS th (prove(mk_eq(rand c,new_rhs),BITBLAST_TAC)))
    else failwith "WG_FACT_NORM_TAC");;

let WG_FACT_CONV_TAC lhs_pat conv : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] lhs_pat) (lhand c) then
      ASSUME_TAC(CONV_RULE conv th)
    else failwith "WG_FACT_CONV_TAC");;

(* The contracts among the hypotheses as assumptions, both as they are and   *)
(* unfolded with the label for WG_CALL_TAC (the pairs of the contract and    *)
(* its label). A contract that unfolds to a conjunction, as the one for      *)
(* wg_peer_put does, gets the labels l_1 and l_2 for its conjuncts.          *)

let WG_LABEL_CONTRACTS_TAC cls =
  MAP_EVERY (fun (c,l) ->
    FIRST_ASSUM(fun th ->
      if concl th = c then
        let th' = REWRITE_RULE[memset_contract; memcpy_contract;
          curve25519_generic_contract; wait_for_random_bytes_contract;
          get_random_bytes_contract; ktime_get_real_ts64_contract;
          rwsem_contract; memcmp_contract;
          ktime_get_coarse_with_offset_contract; wg_peer_put_contract;
          init_rwsem_contract; spinlock_bh_contract] th in
        if is_conj(concl th')
        then LABEL_TAC (l ^ "_1") (CONJUNCT1 th') THEN
             LABEL_TAC (l ^ "_2") (CONJUNCT2 th')
        else LABEL_TAC l th'
      else NO_TAC)) cls;;

(* ------------------------------------------------------------------------- *)
(* For consuming messages: the lengths of decrypted texts, the conditions    *)
(* that make the steps of consume_initiation give up, the flags of a signed  *)
(* test of the result of memcmp and of an unsigned comparison by cset hi,    *)
(* and 12 bytes from a 64-bit and a 32-bit word.                             *)
(* ------------------------------------------------------------------------- *)

let WG_AEAD_DECRYPT_LENGTH = prove
 (`!key n (ct:byte list) al p.
     wg_aead_decrypt key n ct al = SOME p ==> LENGTH p = LENGTH ct - 16`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wg_aead_decrypt; aead_chacha20_poly1305_decrypt] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[chacha20_encrypt; LENGTH_LIST_OF_SEQ; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let WG_XAEAD_DECRYPT_LENGTH = prove
 (`!key nonce (ct:byte list) al p.
     wg_xaead_decrypt key nonce ct al = SOME p ==> LENGTH p = LENGTH ct - 16`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wg_xaead_decrypt; xchacha20_poly1305_decrypt;
              aead_chacha20_poly1305_decrypt] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[chacha20_encrypt; LENGTH_LIST_OF_SEQ; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let WG_CONSUME_INITIATION_STATIC_DH_ZERO = prove
 (`!spriv spub (msg:byte list).
     wg_dh spriv (SUB_LIST(8,32) msg) = wg_zero32
     ==> wg_consume_initiation_static spriv spub msg = NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[wg_consume_initiation_static; wg_handshake_init; wg_ephemeral;
              wg_kdf2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

let WG_CONSUME_INITIATION_TIMESTAMP_SS_ZERO = prove
 (`!ss ck h (msg:byte list).
     ss = wg_zero32 ==> wg_consume_initiation_timestamp ss (ck,h) msg = NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[wg_consume_initiation_timestamp; wg_kdf2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

let WG_IVAL_POS = prove
 (`!w:int32. ~(w = word 0) /\ ~(ival w < &0) <=> &0 < ival w`,
  GEN_TAC THEN REWRITE_TAC[GSYM IVAL_EQ_0] THEN INT_ARITH_TAC);;

let WG_ZX3 = prove
 (`!w:int64. word_zx(word_zx(word_zx w:int32):int64):int32 = word_zx w`,
  GEN_TAC THEN BITBLAST_TAC);;

let WG_ZX_ZX_32 = prove
 (`!w:int32. word_zx(word_zx w:int64):int32 = w`,
  GEN_TAC THEN BITBLAST_TAC);;

let WG_CSET_HI_ZERO = prove
 (`!x y:int64.
     word_zx(word_zx(if ~(val y <= val x /\ ~(val(word_sub x y) = 0))
                     then word 0 else word 1:int32):int64):int32 = word 0 <=>
     val x <= val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN ARITH_TAC);;

let WG_BYTES12_OF_WORDS = prove
 (`!a:int64 (l:byte list) s:armstate.
     LENGTH l = 12 /\
     read (memory :> bytes64 a) s = word(num_of_bytelist(SUB_LIST(0,8) l)) /\
     read (memory :> bytes32 (word_add a (word 8))) s =
       word(num_of_bytelist(SUB_LIST(8,4) l))
     ==> read (memory :> bytes(a,12)) s = num_of_bytelist l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l:byte list = APPEND (SUB_LIST(0,8) l) (SUB_LIST(8,4) l)`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [MP_TAC(ISPECL [`l:byte list`; `8`; `4`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_APPEND; LENGTH_SUB_LIST] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `12 = 8 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; WG_READ_BYTES_VAL] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  SUBGOAL_THEN
   `num_of_bytelist(SUB_LIST(0,8) (l:byte list)) < 2 EXP 64 /\
    num_of_bytelist(SUB_LIST(8,4) (l:byte list)) < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    W(fun (asl,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
    ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC]);;

(* An abbreviation v = t (the assumption t = v) with t rewritten by ths and  *)
(* its lets reduced, so that it matches the terms of the expanded specs.     *)

let WG_ABBREV_NORM_TAC v ths =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && rand c = v then
      ASSUME_TAC(CONV_RULE(LAND_CONV(REWRITE_CONV ths THENC
                   TOP_DEPTH_CONV let_CONV THENC REWRITE_CONV[FST; SND])) th)
    else failwith "WG_ABBREV_NORM_TAC");;

(* The word at offset k of the n bytes of the list l at a in state s, from   *)
(* the fact read (memory :> bytes(a,n)) s = num_of_bytelist l, with lem      *)
(* WG_READ_BYTES64_BYTELIST or WG_READ_BYTES32_BYTELIST.                     *)

let WG_WORD_FACT_TAC lem a n l k s =
  FIRST_ASSUM(fun th ->
    if concl th = list_mk_comb(`(=):num->num->bool`,
         [list_mk_comb(`read:(armstate,num)component->armstate->num`,
            [mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->
                                   (int64->byte,num)component->
                                   (armstate,num)component`,`memory`),
                     mk_comb(`bytes:int64#num->(int64->byte,num)component`,
                             mk_pair(a,mk_small_numeral n))); s]);
          mk_comb(`num_of_bytelist`,l)])
    then MP_TAC(MATCH_MP lem (CONJ th (EQT_ELIM(NUM_REDUCE_CONV
           (mk_binop `(<=):num->num->bool`
             (mk_binop `(+):num->num->num` (mk_small_numeral k)
               (mk_small_numeral(if lem == WG_READ_BYTES64_BYTELIST
                                 then 8 else 4)))
             (mk_small_numeral n))))))
    else failwith "WG_WORD_FACT_TAC") THEN
  CONV_TAC(LAND_CONV(LAND_CONV WG_ADDR_CONV)) THEN DISCH_TAC;;

(* ------------------------------------------------------------------------- *)
(* For responses: a response is not created if a key or Diffie-Hellman       *)
(* result is zero, an empty read, and the first 60 bytes of a response       *)
(* message from its fields.                                                  *)
(* ------------------------------------------------------------------------- *)

let WG_CREATE_RESPONSE_NONE = prove
 (`!ck h repub rspub psk epriv sender receiver.
     epriv = wg_zero32 \/ wg_dh_pubkey epriv = wg_zero32 \/
     wg_dh epriv repub = wg_zero32 \/ wg_dh epriv rspub = wg_zero32
     ==> wg_create_response (ck,h) repub rspub psk epriv sender receiver =
         NONE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[wg_create_response; wg_ephemeral; wg_encrypt; wg_kdf3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

let WG_READ_BYTES_0 = prove
 (`!a:int64 s:armstate. read (memory :> bytes(a,0)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]);;

let WG_RESPONSE_MSG_BYTES = prove
 (`!dst:int64 sender receiver e es s.
     LENGTH e = 32 /\
     read (memory :> bytes32 dst) s = word 2 /\
     read (memory :> bytes32 (word_add dst (word 4))) s = sender /\
     read (memory :> bytes32 (word_add dst (word 8))) s = receiver /\
     read (memory :> bytes(word_add dst (word 12),32)) s = num_of_bytelist e /\
     read (memory :> bytes(word_add dst (word 44),16)) s = num_of_bytelist es
     ==> read (memory :> bytes(dst,60)) s =
         num_of_bytelist(wg_response_msg sender receiver e es)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wg_response_msg; wg_le32; WG_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `60 = 4 + 4 + 4 + 32 + 16` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; WG_READ_BYTES_VAL] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `sender:int32` VAL_BOUND) THEN
  MP_TAC(ISPEC `receiver:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the code of execth. An inlined mix_hash, with the BLAKE2s     *)
(* state at st: memset of the state (the call at step m), its initial words  *)
(* stored (to step n1, the first blake2s_update), and blake2s_update of the  *)
(* hash hb and of the k bytes sb (from step n2) and blake2s_final (from step *)
(* n3), after which the hash that the final writes is wg_mix_hash hb sb.     *)
(* ------------------------------------------------------------------------- *)

let WG_MIXH_REST_TAC execth st n1 n2 n3 hb sb k =
  let sim th = ARM_SUBROUTINE_SIM_TAC
    (wireguard_gcc13_O2_mc,execth,0,wireguard_gcc13_O2_mc,th) in
  let upd = sim WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT
  and fin = sim WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT in
  let sv i = mk_var("s"^string_of_int i,`:armstate`) in
  let app l1 l2 = mk_binop `APPEND:byte list->byte list->byte list` l1 l2 in
  let state_at d s =
    list_mk_comb(`blake2s_state_at`,[st; `blake2s_h0 0 32`; d; `32`; s]) in
  let len_lt t = mk_binop `(<):num->num->bool` t `2 EXP 64` in
  let app0 = app `[]:byte list` hb in
  let app1 = app app0 sb in
  let heq =
    mk_eq(mk_comb(`SUB_LIST(0,32):byte list->byte list`,
                  mk_comb(`blake2s_bytes`,
                          list_mk_comb(`blake2s_final_hash`,
                                       [`blake2s_h0 0 32`; app1]))),
          list_mk_comb(`wg_mix_hash`,[hb; sb])) in
  ASSUME_TAC(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH)) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(WORD_REDUCE_CONV
    (mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,k)))) THEN
  upd [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
       `[]:byte list`; hb; `32`; `mcpy:int64`; `ea:int64`;
       `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] (n1+1) THEN
  BLAKE2S_STATE_EXPAND_TAC (sv(n1+1)) THEN
  ARM_STEPS_TAC execth ((n1+2)--n2) THEN
  BLAKE2S_STATE_COLLECT_TAC (state_at app0 (sv n2)) THEN
  SUBGOAL_THEN (len_lt (mk_binop `(+):num->num->num`
                  (mk_comb(`LENGTH:byte list->num`,app0)) k))
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  upd [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`;
       app0; sb; `32`; `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
       `pc:num`; `read SP s`; `read X30 s`] (n2+1) THEN
  BLAKE2S_STATE_EXPAND_TAC (sv(n2+1)) THEN
  ARM_STEPS_TAC execth ((n2+2)--n3) THEN
  BLAKE2S_STATE_COLLECT_TAC (state_at app1 (sv n3)) THEN
  SUBGOAL_THEN (len_lt (mk_comb(`LENGTH:byte list->num`,app1)))
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  fin [`read X0 s`; `read X1 s`; `blake2s_h0 0 32`; app1; `32`;
       `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
       `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
       `pc:num`; `read SP s`; `read X30 s`] (n3+1) THEN
  SUBGOAL_THEN heq ASSUME_TAC THENL
   [REWRITE_TAC[APPEND; wg_mix_hash] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC WG_HASH_STREAM THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) &&
       can (find_term ((=) (sv(n3+1)))) (lhand(concl th)) &&
       can (find_term ((=) (lhand heq))) (rand(concl th))
    then REWRITE_RULE[ASSUME heq] th else th);;

let WG_MIXH_TAC execth st m n1 n2 n3 hb sb k =
  let sv i = mk_var("s"^string_of_int i,`:armstate`) in
  WG_PLT_TAC execth m THEN
  WG_CALL_TAC "memset" execth
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (m+5) THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC st 120 [32; 40] (sv(m+5)) THEN
  ARM_STEPS_TAC execth ((m+6)--n1) THEN
  BLAKE2S_STATE_INIT_TAC st (sv n1) THEN
  WG_MIXH_REST_TAC execth st n1 n2 n3 hb sb k;;

(* ------------------------------------------------------------------------- *)
(* From the fact that a decryption dec (by chacha20poly1305_decrypt) is not  *)
(* NONE: its plaintext, named name, of length n, the fact about it from the  *)
(* postcondition of the decryption, and the result in X0 as 1.               *)
(* ------------------------------------------------------------------------- *)

let WG_DECRYPTED_TAC dec name n =
  MP_TAC(ISPEC dec (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC name) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,name),
                      mk_small_numeral n)) ASSUME_TAC THENL
   [MP_TAC(MATCH_MP WG_AEAD_DECRYPT_LENGTH
      (ASSUME (mk_eq(dec,mk_comb(`SOME:byte list->(byte list)option`,
                                 name))))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) dec)) (concl th)
    then MP_TAC(SPEC name th) else failwith "WG_DECRYPTED_TAC") THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  WG_REG_REWRITE_TAC `X0`
   [ASSUME (mk_eq(dec,mk_comb(`SOME:byte list->(byte list)option`,name)));
    distinctness "option"];;

(* ------------------------------------------------------------------------- *)
(* 16 bytes from their two 64-bit words, and the flags of a signed           *)
(* comparison cmp x, y for b.gt (and their negation for b.le).               *)
(* ------------------------------------------------------------------------- *)

let WG_READ_BYTES_16_OF_CHUNKS = prove
 (`!a:int64 l0 l1 s:armstate.
     LENGTH l0 = 8 /\ LENGTH l1 = 8 /\
     read (memory :> bytes64 a) s = word(num_of_bytelist l0) /\
     read (memory :> bytes64 (word_add a (word 8))) s =
     word(num_of_bytelist l1)
     ==> read (memory :> bytes(a,16)) s = num_of_bytelist(APPEND l0 l1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `16 = 8 + 8`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[WG_READ_BYTES_8; GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_SIMP_TAC[WG_VAL_WORD_BYTES8; WG_NUM_OF_BYTELIST_APPEND;
               LENGTH_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WG_IVAL_GT_FLAGS = prove
 (`!x y:int64.
     (~(val(word_sub x y) = 0) /\
      (ival(word_sub x y) < &0 <=> ~(ival x - ival y = ival(word_sub x y)))) <=>
     ival y < ival x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM IVAL_EQ] THEN
  MP_TAC(ISPECL [`x:int64`; `y:int64`] ICONG_WORD_SUB) THEN
  MP_TAC(ISPEC `x:int64` IVAL_BOUND) THEN MP_TAC(ISPEC `y:int64` IVAL_BOUND) THEN
  MP_TAC(ISPEC `word_sub x y:int64` IVAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64; int_congruent] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`ival(word_sub x y:int64)`,`w:int`) THEN
  SPEC_TAC(`ival(x:int64)`,`a:int`) THEN SPEC_TAC(`ival(y:int64)`,`b:int`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `d:int`) THEN
  ASM_CASES_TAC `(d:int) < &0` THENL
   [FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[INT_LT_DISCRETE] o
                check (fun th -> concl th = `(d:int) < &0`)) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < (d:int)` THENL
   [FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[INT_LT_DISCRETE] o
                check (fun th -> concl th = `&0 < (d:int)`)) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d:int = &0` SUBST_ALL_TAC THENL
   [ASM_INT_ARITH_TAC; ASM_INT_ARITH_TAC]);;

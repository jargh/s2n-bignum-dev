(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of __chacha20poly1305_encrypt and *)
(* __chacha20poly1305_decrypt (chacha20poly1305_encrypt_inner_proof.ml and   *)
(* chacha20poly1305_decrypt_inner_proof.ml), which have the same stack frame *)
(* in this build: the poly1305_desc_ctx at stackpointer + 376 and the block  *)
(* buffer at stackpointer + 344, stackpointer being 656 below the entry SP;  *)
(* and the lemma for the ChaCha20 state that chacha20poly1305_encrypt and    *)
(* chacha20poly1305_decrypt build for them.                                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the one-time key and the encryption in terms of the RFC block     *)
(* function, the padding, the lengths, and the words of the code.            *)
(* ------------------------------------------------------------------------- *)

let CP_EL_REPLICATE = prove
 (`!n (x:A) i. i < n ==> EL i (REPLICATE n x) = x`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[REPLICATE; EL; HD; TL; LT_SUC] THEN
  ASM_SIMP_TAC[]);;

let CP_EL_SUB_LIST_0 = prove
 (`!(l:A list) n i.
     i < n /\ n <= LENGTH l ==> EL i (SUB_LIST(0,n) l) = EL i l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `n:num`; `LENGTH(l:A list) - n`; `0`]
         SUB_LIST_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= l ==> n + l - n = l`; SUB_LIST_LENGTH] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[EL_APPEND; LENGTH_SUB_LIST] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CP_LENGTH_CHACHA20_BLOCK = prove
 (`!key c nonce. LENGTH(chacha20_block key c nonce) = 64`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`key:byte list`; `c:num`; `nonce:byte list`; `0`]
         CHACHA20_KBLOCK_STATE) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LENGTH_CHACHA20_KBLOCK]);;

let CP_OTK = prove
 (`!key nonce.
     list_of_seq
      (\i. word_xor (EL i (REPLICATE 32 (word 0:byte)))
                    (EL (i MOD 64)
                        (chacha20_kblock (chacha20_state key 0 nonce)
                                         (i DIV 64))))
      32 =
     SUB_LIST(0,32) (chacha20_block key 0 nonce)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_SUB_LIST;
              CP_LENGTH_CHACHA20_BLOCK] THEN
  CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; CP_EL_REPLICATE; CP_EL_SUB_LIST_0;
               CP_LENGTH_CHACHA20_BLOCK; ARITH_RULE `32 <= 64`] THEN
  ASM_SIMP_TAC[MOD_LT; DIV_LT; ARITH_RULE `i < 32 ==> i < 64`] THEN
  REWRITE_TAC[CHACHA20_KBLOCK_STATE; ADD_CLAUSES; WORD_XOR_0]);;

let CP_ENC = prove
 (`!key nonce (pl:byte list) n.
     LENGTH pl = n
     ==> list_of_seq
          (\i. word_xor (EL i pl)
                        (EL (i MOD 64)
                            (chacha20_kblock (chacha20_state key 1 nonce)
                                             (i DIV 64))))
          n =
         chacha20_encrypt key 1 nonce pl`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[chacha20_encrypt; CHACHA20_KBLOCK_STATE]);;

let CP_PAD_Z = prove
 (`!n. n MOD 16 = 0 ==> poly1305_pad16 n = []`,
  SIMP_TAC[poly1305_pad16; SUB_0; MOD_REFL; ARITH_EQ; REPLICATE]);;

let CP_LENS = prove
 (`!a:int64 x y s.
     read (memory :> bytes64 a) s = x /\
     read (memory :> bytes64 (word_add a (word 8))) s = y
     ==> read (memory :> bytes(a,16)) s =
         num_of_bytelist(APPEND (bytelist_of_num 8 (val x))
                                (bytelist_of_num 8 (val y)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_APPEND; NUM_OF_BYTELIST_OF_NUM;
              LENGTH_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `16 = 8 + 8`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; WG_READ_BYTES_8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `y:int64` VAL_BOUND_64) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT]);;

let CP_AND15 = prove
 (`!x:int64. val(word_and x (word 15)) = val x MOD 16`,
  REWRITE_TAC[ARITH_RULE `15 = 2 EXP 4 - 1`; VAL_WORD_AND_MASK_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CP_PAD_LEN = prove
 (`!n. LENGTH(poly1305_pad16 n) = (16 - n MOD 16) MOD 16 /\
       n + LENGTH(poly1305_pad16 n) = 16 * ((n + 15) DIV 16)`,
  GEN_TAC THEN REWRITE_TAC[poly1305_pad16; LENGTH_REPLICATE] THEN
  MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `r = n MOD 16` THEN ABBREV_TAC `q = n DIV 16` THEN STRIP_TAC THEN
  ASM_CASES_TAC `r = 0` THENL
   [REWRITE_TAC[ASSUME `r = 0`; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `(n + 15) DIV 16 = q` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `15` THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    SUBGOAL_THEN `(16 - r) MOD 16 = 16 - r` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(n + 15) DIV 16 = q + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r - 1` THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

let CP_PADLEN_WORD = prove
 (`!x:int64.
     word_zx(word_sub (word 16) (word_zx(word_and x (word 15)):int32)):int64 =
     word(16 - val x MOD 16)`,
  GEN_TAC THEN
  SUBGOAL_THEN `word_zx(word_and x (word 15):int64):int32 = word(val x MOD 16)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; CP_AND15; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN
    SUBGOAL_THEN `val(x:int64) MOD 16 < 16` MP_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
    SPEC_TAC(`val(x:int64) MOD 16`,`r:num`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `r < 4294967296` (fun th -> SIMP_TAC[MOD_LT; th]) THEN
    UNDISCH_TAC `r < 16` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(x:int64) MOD 16 < 16` MP_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  SPEC_TAC(`val(x:int64) MOD 16`,`r:num`) THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`16`; `r:num`] (INST_TYPE [`:32`,`:N`] WG_WORD_SUB_LE)) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `r < 16` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `16 - r` WG_WORD_ZX_SMALL) THEN ANTS_TAC THENL
   [ARITH_TAC; SIMP_TAC[]]);;

let CP_ZP_SUB = prove
 (`!a:int64 n s. read (memory :> bytes(a,32)) s = 0 /\ n <= 32
                 ==> read (memory :> bytes(a,n)) s = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `32`; `n:num`; `read memory s`]
         READ_BYTES_MOD) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[MOD_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 32 ==> MIN 32 n = n`] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let CP_PAD_NUM = prove
 (`!n. num_of_bytelist(poly1305_pad16 n) = 0`,
  REWRITE_TAC[poly1305_pad16; NUM_OF_BYTELIST_REPLICATE_0]);;

let CP_ZX_ZX = prove
 (`!x:int64. val x < 2 EXP 32 ==> word_zx(word_zx x:int32):int64 = x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(x:int64) < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `val(x:int64) < 2 EXP 32` THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let CP_LENGTH_ENC = prove
 (`!key c nonce (m:byte list).
     LENGTH(chacha20_encrypt key c nonce m) = LENGTH m`,
  REWRITE_TAC[chacha20_encrypt; LENGTH_LIST_OF_SEQ]);;

let CP_LEN_APPEND16 = prove
 (`!(d:byte list) l q.
     LENGTH d MOD 16 = 0 /\ LENGTH d DIV 16 = q /\ LENGTH l = 16
     ==> LENGTH(APPEND d l) MOD 16 = 0 /\ LENGTH(APPEND d l) DIV 16 = q + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LENGTH_APPEND] THEN
  SUBGOAL_THEN `LENGTH(d:byte list) = 16 * q` SUBST1_TAC THENL
   [MP_TAC(SPECL [`LENGTH(d:byte list)`; `16`] DIVISION) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `16 * q + 16 = 16 * (q + 1)`] THEN
    SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* The poly1305_desc_ctx at stackpointer + 376: before the calls as          *)
(* poly1305_desc_at for the bytes d absorbed so far, and between them as the *)
(* facts it stands for (the simulation keeping only facts read c s = v),     *)
(* the length of d mod and div 16 being rewritten by the theorems lens. The  *)
(* one-time key is the start of block 0 of the keystream.                    *)
(* ------------------------------------------------------------------------- *)

let CP_ADDR_NORM_RULE =
  CONV_RULE(DEPTH_CONV NUM_ADD_CONV) o
  REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];;

let CP_DESC_EXPAND_TAC lens s =
  let is_read t =
    try fst(dest_const(repeat rator t)) = "read" with Failure _ -> false in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `poly1305_desc_at desc k d (s:armstate)`)
           (concl th) &&
       rand(concl th) = s
    then
      let eth = CP_ADDR_NORM_RULE(REWRITE_RULE lens
                  (MATCH_MP POLY1305_DESC_AT_EXPAND th)) in
      let body = snd(strip_exists(concl eth)) in
      let lhss = mapfilter (fun c ->
          if is_eq c && is_read(lhand c) then lhand c else failwith "")
        (conjuncts body) in
      REPEAT(FIRST_X_ASSUM(fun a ->
        if is_eq(concl a) && mem (lhand(concl a)) lhss then ALL_TAC
        else failwith "")) THEN
      STRIP_ASSUME_TAC eth
    else failwith "CP_DESC_EXPAND_TAC");;

let CP_DESC_FOLD_TAC lens d s =
  SUBGOAL_THEN
   (list_mk_comb(`poly1305_desc_at (word_add stackpointer (word 376))
                   (SUB_LIST(0,32) (chacha20_block key 0 nonce))`,[d; s]))
  ASSUME_TAC THENL
   [REWRITE_TAC[poly1305_desc_at; poly1305_h_at; poly1305_key_at] THEN
    REWRITE_TAC lens THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; SUB_LIST_CLAUSES;
                num_of_bytelist];
    ALL_TAC];;

let CP_DESC_EQ_TAC eqth s =
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `poly1305_desc_at desc k d (s:armstate)`)
           (concl th) &&
       rand(concl th) = s
    then ASSUME_TAC
          (EQ_MP (AP_THM (AP_TERM (rator(rator(concl th))) eqth) s) th)
    else failwith "CP_DESC_EQ_TAC");;

let cp_d2 = `APPEND al (poly1305_pad16 (val(adlen:int64)))`;;

let CP_D2_LENS_TAC =
  SUBGOAL_THEN
   `LENGTH(APPEND al (poly1305_pad16 (val(adlen:int64)))) MOD 16 = 0 /\
    LENGTH(APPEND al (poly1305_pad16 (val(adlen:int64)))) DIV 16 =
    (val(adlen:int64) + 15) DIV 16`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN
    REWRITE_TAC[ASSUME `LENGTH(al:byte list) = val(adlen:int64)`] THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL CP_PAD_LEN)] THEN
    SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ];
    ALL_TAC];;

let cp_d2_lens () =
  [ASSUME `LENGTH(APPEND al (poly1305_pad16 (val(adlen:int64)))) MOD 16 = 0`;
   ASSUME `LENGTH(APPEND al (poly1305_pad16 (val(adlen:int64)))) DIV 16 =
           (val(adlen:int64) + 15) DIV 16`];;

(* Facts for a padding of 16 - n MOD 16 (not 0) bytes from the zero page at  *)
(* zpa, and the zero page address computed by the code as zpa.               *)

let CP_PAD_FACTS_TAC n s =
  let sub = vsubst [n,`n:num`; s,`s:armstate`] in
  SUBGOAL_THEN
   (sub `read (memory :> bytes(zpa,val(word(16 - n MOD 16):int64))) s =
         num_of_bytelist(poly1305_pad16 n) /\
         read (memory :> bytes(zpa,16 - n MOD 16)) s =
         num_of_bytelist(poly1305_pad16 n) /\
         LENGTH(poly1305_pad16 n) = val(word(16 - n MOD 16):int64) /\
         val(word(16 - n MOD 16):int64) = 16 - n MOD 16 /\
         val(word(16 - n MOD 16):int64) + 16 < 2 EXP 32 /\
         16 - n MOD 16 <= 32 /\
         16 - n MOD 16 + 16 < 2 EXP 32`)
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN (sub `val(word(16 - n MOD 16):int64) = 16 - n MOD 16`)
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CP_PAD_NUM; CONJUNCT1(SPEC_ALL CP_PAD_LEN)] THEN
    SUBGOAL_THEN (sub `(16 - n MOD 16) MOD 16 = 16 - n MOD 16`)
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      MP_TAC(ASSUME(sub `~(n MOD 16 = 0)`)) THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CP_ZP_SUB THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC;
    ALL_TAC];;

let CP_ZPA_TAC =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `zpa:int64`
    then RULE_ASSUM_TAC
          (REWRITE_RULE[REWRITE_RULE[wg_zero_page_va; WORD_ADD] th])
    else failwith "CP_ZPA_TAC");;

(* ------------------------------------------------------------------------- *)
(* The ChaCha20 state that chacha20poly1305_encrypt and _decrypt build on    *)
(* the stack with 64-bit stores of the constants, the key and the nonce: the *)
(* RFC 8439 state for the key and the WireGuard nonce with counter 0.        *)
(* ------------------------------------------------------------------------- *)

let CP_SUBWORD_BYTES8 = prove
 (`!(l:byte list) i.
     i + 8 <= LENGTH l
     ==> word_subword (word(num_of_bytelist(SUB_LIST(i,8) l)):int64) (0,32) =
         (word(num_of_bytelist(SUB_LIST(i,4) l)):int32) /\
         word_subword (word(num_of_bytelist(SUB_LIST(i,8) l)):int64) (32,32) =
         (word(num_of_bytelist(SUB_LIST(i + 4,4) l)):int32)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `SUB_LIST(i,8) (l:byte list) =
                APPEND (SUB_LIST(i,4) l) (SUB_LIST(i + 4,4) l)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUB_LIST_SPLIT] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(i,4) (l:byte list)) = 4 /\
                LENGTH(SUB_LIST(i + 4,4) (l:byte list)) = 4`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[WG_NUM_OF_BYTELIST_APPEND] THEN
  MP_TAC(ISPEC `SUB_LIST(i,4) (l:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `SUB_LIST(i + 4,4) (l:byte list)` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`num_of_bytelist(SUB_LIST(i,4) (l:byte list))`,`a:num`) THEN
  SPEC_TAC(`num_of_bytelist(SUB_LIST(i + 4,4) (l:byte list))`,`b:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a + 4294967296 * b < 18446744073709551616` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT; DIV_1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a + 4294967296 * b = b * 4294967296 + a`] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; ADD_CLAUSES]);;

let CP_NONCE_WORDS = prove
 (`!nonce:int64.
     word_subword nonce (0,32):int32 =
     word(num_of_bytelist(SUB_LIST(4,4) (wg_aead_nonce (val nonce)))) /\
     word_subword nonce (32,32):int32 =
     word(num_of_bytelist(SUB_LIST(8,4) (wg_aead_nonce (val nonce)))) /\
     word(num_of_bytelist(SUB_LIST(0,4) (wg_aead_nonce (val nonce)))):int32 =
     word 0`,
  GEN_TAC THEN REWRITE_TAC[wg_aead_nonce] THEN
  MP_TAC(ISPECL [`REPLICATE 4 (word 0:byte)`;
                 `bytelist_of_num 8 (val(nonce:int64))`; `0`; `4`]
         WG_SUB_LIST_APPEND_RIGHT) THEN
  MP_TAC(ISPECL [`REPLICATE 4 (word 0:byte)`;
                 `bytelist_of_num 8 (val(nonce:int64))`; `4`; `4`]
         WG_SUB_LIST_APPEND_RIGHT) THEN
  MP_TAC(ISPECL [`REPLICATE 4 (word 0:byte)`;
                 `bytelist_of_num 8 (val(nonce:int64))`; `0`; `4`]
         WG_SUB_LIST_APPEND_LEFT) THEN
  REWRITE_TAC[LENGTH_REPLICATE; ADD_CLAUSES; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[MESON[LENGTH_REPLICATE; SUB_LIST_LENGTH]
    `SUB_LIST(0,4) (REPLICATE 4 (x:byte)) = REPLICATE 4 x`;
    NUM_OF_BYTELIST_REPLICATE_0] THEN
  MP_TAC(ISPECL [`bytelist_of_num 8 (val(nonce:int64))`; `0`]
         CP_SUBWORD_BYTES8) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; ADD_CLAUSES; LE_REFL] THEN
  SUBGOAL_THEN `SUB_LIST(0,8) (bytelist_of_num 8 (val(nonce:int64))) =
                bytelist_of_num 8 (val nonce)` SUBST1_TAC THENL
   [MESON_TAC[LENGTH_BYTELIST_OF_NUM; SUB_LIST_LENGTH]; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN
  SUBGOAL_THEN `val(nonce:int64) MOD 256 EXP 8 = val nonce` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[ARITH_RULE `256 EXP 8 = 2 EXP 64`] THEN
    REWRITE_TAC[VAL_BOUND_64];
    REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
    SIMP_TAC[]]);;

let CP_LENGTH_NONCE = prove
 (`!n. LENGTH(wg_aead_nonce n) = 12`,
  REWRITE_TAC[wg_aead_nonce; LENGTH_APPEND; LENGTH_REPLICATE;
              LENGTH_BYTELIST_OF_NUM] THEN CONV_TAC NUM_REDUCE_CONV);;

let CP_STATE = prove
 (`!st:int64 s (kb:byte list) (nonce:int64).
     LENGTH kb = 32 /\
     read (memory :> bytes64 st) s = word 3684054920433006693 /\
     read (memory :> bytes64 (word_add st (word 8))) s =
       word 7719281312240119090 /\
     read (memory :> bytes64 (word_add st (word 16))) s =
       word(num_of_bytelist(SUB_LIST(0,8) kb)) /\
     read (memory :> bytes64 (word_add st (word 24))) s =
       word(num_of_bytelist(SUB_LIST(8,8) kb)) /\
     read (memory :> bytes64 (word_add st (word 32))) s =
       word(num_of_bytelist(SUB_LIST(16,8) kb)) /\
     read (memory :> bytes64 (word_add st (word 40))) s =
       word(num_of_bytelist(SUB_LIST(24,8) kb)) /\
     read (memory :> bytes64 (word_add st (word 48))) s = word 0 /\
     read (memory :> bytes64 (word_add st (word 56))) s = nonce
     ==> !i. i < 16
             ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s =
                 chacha20_state kb 0 (wg_aead_nonce (val nonce)) i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WG_BYTES64_SPLIT o
         check (fun th ->
           can (term_match [] `read (memory :> bytes64 a) s = d`)
               (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[chacha20_state; chacha20_le32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun i -> MP_TAC(ISPECL [`kb:byte list`; mk_small_numeral i]
                                     CP_SUBWORD_BYTES8))
            [0; 8; 16; 24] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[CP_NONCE_WORDS]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The internal interfaces of the Linux kernel's WireGuard code and crypto   *)
(* library (lib/crypto) in terms of the specifications in common/rfc7693.ml, *)
(* common/rfc8439.ml and common/wireguard.ml, for the proofs about their     *)
(* machine code (arm/proofs/wireguard).                                      *)
(* ========================================================================= *)

needs "common/rfc7693.ml";;
needs "common/wireguard.ml";;
needs "common/wireguard_tables.ml";;

(* ------------------------------------------------------------------------- *)
(* blake2s_compress(state, block, nblocks, inc): nblocks compressions of     *)
(* consecutive 64-byte blocks, here the blocks of the byte list p, the       *)
(* 64-bit counter tt of the state being incremented by inc before each, all  *)
(* with the final flag f of the state.                                       *)
(* ------------------------------------------------------------------------- *)

let blake2s_compress_blocks = define
 `blake2s_compress_blocks (h:num->int32) (p:byte list) (tt:int64) inc f 0 =
    h /\
  blake2s_compress_blocks h p tt inc f (SUC k) =
    blake2s_compress (blake2s_compress_blocks h p tt inc f k)
                     (blake2s_block p k)
                     (val(word_add tt (word(inc * (k + 1)):int64))) f`;;

let BLAKE2S_COMPRESS_BLOCKS_STEP = prove
 (`!h p tt inc f i.
     blake2s_compress_blocks h p tt inc f (i + 1) =
     blake2s_compress (blake2s_compress_blocks h p tt inc f i)
                      (blake2s_block p i)
                      (val(word_add tt (word(inc * (i + 1))):int64)) f`,
  REWRITE_TAC[GSYM ADD1; blake2s_compress_blocks]);;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

let WG_SUB_LIST_SUB_LIST = prove
 (`!(l:A list) a b c.
        SUB_LIST(b,c) (SUB_LIST(a,LENGTH l - a) l) = SUB_LIST(a + b,c) l`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES]; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[LENGTH; SUB_0; ADD_CLAUSES] THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES; SUB_LIST_LENGTH];
    ASM_REWRITE_TAC[SUB_SUC; SUB_LIST_CLAUSES]]);;

let WG_SUB_LIST_SUB_LIST_GEN = prove
 (`!(l:A list) a n b c.
        b + c <= n ==> SUB_LIST(b,c) (SUB_LIST(a,n) l) = SUB_LIST(a + b,c) l`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[SUB_LIST_CLAUSES]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES]] THEN
  INDUCT_TAC THENL
   [SIMP_TAC[LE; ADD_EQ_0; SUB_LIST_CLAUSES]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN INDUCT_TAC THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; LE_SUC] THEN
    REWRITE_TAC[SUB_LIST_MIN; CONS_11] THEN
    SIMP_TAC[ARITH_RULE `c <= n ==> MIN c n = c`];
    REWRITE_TAC[ADD_CLAUSES; SUB_LIST_CLAUSES; LE_SUC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `n:num`; `b:num`; `c:num`]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let WG_SUB_LIST_SUB_LIST_0 = prove
 (`!(l:A list) n b c.
        b + c <= n ==> SUB_LIST(b,c) (SUB_LIST(0,n) l) = SUB_LIST(b,c) l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `0`; `n:num`; `b:num`; `c:num`]
         WG_SUB_LIST_SUB_LIST_GEN) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let WG_SUB_LIST_APPEND_LEFT = prove
 (`!(l1:A list) l2 m n.
        m + n <= LENGTH l1
        ==> SUB_LIST(m,n) (APPEND l1 l2) = SUB_LIST(m,n) l1`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LE; ADD_EQ_0] THEN SIMP_TAC[SUB_LIST_CLAUSES; APPEND];
    ALL_TAC] THEN
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[ADD_CLAUSES; SUB_LIST_APPEND_LEFT]; ALL_TAC] THEN
  ASM_SIMP_TAC[APPEND; SUB_LIST_CLAUSES; LENGTH; ADD_CLAUSES; LE_SUC]);;

let WG_SUB_LIST_APPEND_RIGHT = prove
 (`!(l1:A list) l2 m n.
        SUB_LIST(LENGTH l1 + m,n) (APPEND l1 l2) = SUB_LIST(m,n) l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES]);;

let WG_SUB_LIST_APPEND_STRADDLE = prove
 (`!(l1:A list) l2 a b c.
        a + b = LENGTH l1
        ==> SUB_LIST(a,b + c) (APPEND l1 l2) =
            APPEND (SUB_LIST(a,b) l1) (SUB_LIST(0,c) l2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_LIST_SPLIT] THEN BINOP_TAC THENL
   [MATCH_MP_TAC WG_SUB_LIST_APPEND_LEFT THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l1:A list`; `l2:A list`; `0`; `c:num`]
      WG_SUB_LIST_APPEND_RIGHT) THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

(* A list of 32 elements as the explicit list of them.                       *)

let WG_LENGTH_32_EXPLICIT = prove
 (`!l:A list.
     LENGTH l = 32
     ==> l = [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l; EL 5 l; EL 6 l; EL 7 l;
              EL 8 l; EL 9 l; EL 10 l; EL 11 l; EL 12 l; EL 13 l; EL 14 l;
              EL 15 l; EL 16 l; EL 17 l; EL 18 l; EL 19 l; EL 20 l; EL 21 l;
              EL 22 l; EL 23 l; EL 24 l; EL 25 l; EL 26 l; EL 27 l; EL 28 l;
              EL 29 l; EL 30 l; EL 31 l]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* REPLICATE n x for a numeral n as the explicit list.                       *)

let rec WG_REPLICATE_CONV tm =
  match tm with
    Comb(Comb(Const("REPLICATE",_),n),x) ->
      if dest_numeral n =/ num_0 then REWR_CONV (CONJUNCT1 REPLICATE) tm else
      (RATOR_CONV(RAND_CONV num_CONV) THENC
       REWR_CONV (CONJUNCT2 REPLICATE) THENC
       RAND_CONV WG_REPLICATE_CONV) tm
  | _ -> failwith "WG_REPLICATE_CONV";;

(* ------------------------------------------------------------------------- *)
(* The blocks of a byte list and their compressions.                         *)
(* ------------------------------------------------------------------------- *)

let BLAKE2S_BLOCK_SHIFT = prove
 (`!p j k. blake2s_block p (j + k) =
           blake2s_block (SUB_LIST(64 * j,LENGTH p - 64 * j) p) k`,
  REWRITE_TAC[blake2s_block; FUN_EQ_THM; WG_SUB_LIST_SUB_LIST] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC]);;

(* The words of a block depend only on its 64 bytes.                         *)

let BLAKE2S_BLOCK_AGREE_SUB_LIST = prove
 (`!p k p' k'.
        SUB_LIST(64 * k,64) p = SUB_LIST(64 * k',64) p'
        ==> wg_agree 16 (blake2s_block p k) (blake2s_block p' k')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wg_agree; blake2s_block] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`p:byte list`; `64 * k`; `64`; `4 * j`; `4`]
         WG_SUB_LIST_SUB_LIST_GEN) THEN
  MP_TAC(ISPECL [`p':byte list`; `64 * k'`; `64`; `4 * j`; `4`]
         WG_SUB_LIST_SUB_LIST_GEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_REWRITE_TAC[]);;

let BLAKE2S_BLOCK_APPEND_LEFT = prove
 (`!(l1:byte list) l2 k.
        64 * k + 64 <= LENGTH l1
        ==> wg_agree 16 (blake2s_block (APPEND l1 l2) k) (blake2s_block l1 k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wg_agree; blake2s_block] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC WG_SUB_LIST_APPEND_LEFT THEN ASM_ARITH_TAC);;

let BLAKE2S_COMPRESS_BLOCKS_AGREE = prove
 (`!h h' p p' tt inc f n.
     wg_agree 8 h h' /\
     (!k. k < n ==> wg_agree 16 (blake2s_block p k) (blake2s_block p' k))
     ==> wg_agree 8 (blake2s_compress_blocks h p tt inc f n)
                    (blake2s_compress_blocks h' p' tt inc f n)`,
  REPLICATE_TAC 7 GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[blake2s_compress_blocks] THEN
  STRIP_TAC THEN MATCH_MP_TAC BLAKE2S_COMPRESS_AGREE THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `k < n ==> k < SUC n`];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let BLAKE2S_COMPRESS_BLOCKS_ADD = prove
 (`!h p tt inc f a b.
     blake2s_compress_blocks h p tt inc f (a + b) =
     blake2s_compress_blocks (blake2s_compress_blocks h p tt inc f a)
       (SUB_LIST(64 * a,LENGTH p - 64 * a) p) (word_add tt (word(inc * a)))
       inc f b`,
  REPLICATE_TAC 6 GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; blake2s_compress_blocks] THEN
  REWRITE_TAC[GSYM BLAKE2S_BLOCK_SHIFT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The state of an incremental BLAKE2s computation (struct blake2s_state)    *)
(* after the bytes d (the key block, if any, and the input so far) from the  *)
(* chained state h0: all the complete blocks of d but the last are           *)
(* compressed, and the remaining 1 to 64 bytes are in the buffer (none if d  *)
(* is empty), as blake2s_update(state, in, inlen) leaves them, so that       *)
(* blake2s_final can compress the last block with the finalization flag.     *)
(* ------------------------------------------------------------------------- *)

let blake2s_nblocks = new_definition
 `blake2s_nblocks (d:byte list) = (LENGTH d - 1) DIV 64`;;

let blake2s_buflen = new_definition
 `blake2s_buflen (d:byte list) = LENGTH d - 64 * blake2s_nblocks d`;;

let blake2s_chain = new_definition
 `blake2s_chain (h0:num->int32) (d:byte list) =
    blake2s_compress_blocks h0 d (word 0) 64 F (blake2s_nblocks d)`;;

let BLAKE2S_BUFLEN = prove
 (`!d:byte list.
        LENGTH d = 64 * blake2s_nblocks d + blake2s_buflen d /\
        blake2s_buflen d <= 64 /\
        (blake2s_buflen d = 0 <=> d = [])`,
  GEN_TAC THEN
  REWRITE_TAC[blake2s_buflen; blake2s_nblocks; GSYM LENGTH_EQ_NIL] THEN
  MP_TAC(SPECL [`LENGTH(d:byte list) - 1`; `64`] DIVISION) THEN
  ARITH_TAC);;

let BLAKE2S_NBLOCKS_UNIQUE = prove
 (`!(d:byte list) n b.
        LENGTH d = 64 * n + b /\ 1 <= b /\ b <= 64
        ==> blake2s_nblocks d = n /\ blake2s_buflen d = b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[blake2s_nblocks] THEN MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `b - 1` THEN ASM_ARITH_TAC;
    SIMP_TAC[blake2s_buflen] THEN ASM_ARITH_TAC]);;

(* Adding at most the rest of the last block to the bytes of a state.        *)

let BLAKE2S_UPDATE_SMALL = prove
 (`!h0 (d:byte list) m.
     ~(m = []) /\ blake2s_buflen d + LENGTH m <= 64
     ==> blake2s_nblocks (APPEND d m) = blake2s_nblocks d /\
         blake2s_buflen (APPEND d m) = blake2s_buflen d + LENGTH m /\
         wg_agree 8 (blake2s_chain h0 (APPEND d m)) (blake2s_chain h0 d) /\
         SUB_LIST(64 * blake2s_nblocks d,blake2s_buflen d + LENGTH m)
                 (APPEND d m) =
         APPEND (SUB_LIST(64 * blake2s_nblocks d,blake2s_buflen d) d) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `d:byte list` BLAKE2S_BUFLEN) THEN
  ABBREV_TAC `n = blake2s_nblocks d` THEN ABBREV_TAC `b = blake2s_buflen d` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`APPEND d m:byte list`; `n:num`; `b + LENGTH(m:byte list)`]
         BLAKE2S_NBLOCKS_UNIQUE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN
    UNDISCH_TAC `~(m:byte list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    ASM_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[blake2s_chain] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BLAKE2S_COMPRESS_BLOCKS_AGREE THEN
    REWRITE_TAC[WG_AGREE_REFL] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC BLAKE2S_BLOCK_APPEND_LEFT THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUB_LIST_SPLIT] THEN BINOP_TAC THENL
     [MATCH_MP_TAC WG_SUB_LIST_APPEND_LEFT THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `64 * n + b = LENGTH(d:byte list) + 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[WG_SUB_LIST_APPEND_RIGHT]] THEN
      MATCH_MP_TAC SUB_LIST_REFL THEN REWRITE_TAC[LE_REFL]]]);;

(* Adding more: the buffer is completed and compressed, then the next k      *)
(* complete blocks of m are compressed, leaving 1 to 64 bytes of m.          *)

let BLAKE2S_UPDATE_LARGE = prove
 (`!h0 (d:byte list) m k.
     64 - blake2s_buflen d < LENGTH m /\
     64 * k < LENGTH m - (64 - blake2s_buflen d) /\
     LENGTH m - (64 - blake2s_buflen d) <= 64 * k + 64
     ==> blake2s_nblocks (APPEND d m) = blake2s_nblocks d + 1 + k /\
         blake2s_buflen (APPEND d m) =
           LENGTH m - (64 - blake2s_buflen d) - 64 * k /\
         wg_agree 8 (blake2s_chain h0 (APPEND d m))
          (blake2s_compress_blocks
            (blake2s_compress_blocks (blake2s_chain h0 d)
               (APPEND (SUB_LIST(64 * blake2s_nblocks d,blake2s_buflen d) d)
                       (SUB_LIST(0,64 - blake2s_buflen d) m))
               (word(64 * blake2s_nblocks d)) 64 F 1)
            (SUB_LIST(64 - blake2s_buflen d,64 * k) m)
            (word(64 * (blake2s_nblocks d + 1))) 64 F k) /\
         SUB_LIST(64 * (blake2s_nblocks d + 1 + k),
                  LENGTH m - (64 - blake2s_buflen d) - 64 * k) (APPEND d m) =
         SUB_LIST(64 - blake2s_buflen d + 64 * k,
                  LENGTH m - (64 - blake2s_buflen d) - 64 * k) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `d:byte list` BLAKE2S_BUFLEN) THEN
  ABBREV_TAC `n = blake2s_nblocks d` THEN ABBREV_TAC `b = blake2s_buflen d` THEN
  STRIP_TAC THEN
  ABBREV_TAC `r = LENGTH(m:byte list) - (64 - b) - 64 * k` THEN
  MP_TAC(ISPECL [`APPEND d m:byte list`; `n + 1 + k`; `r:num`]
         BLAKE2S_NBLOCKS_UNIQUE) THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[blake2s_chain] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `64 * (n + 1 + k) = LENGTH(d:byte list) + (64 - b + 64 * k)`
    SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[WG_SUB_LIST_APPEND_RIGHT]]] THEN
  REWRITE_TAC[ARITH_RULE `n + 1 + k = n + (1 + k)`;
              BLAKE2S_COMPRESS_BLOCKS_ADD] THEN
  REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `64 * n + 64 * 1 = 64 * (n + 1)`] THEN
  MATCH_MP_TAC BLAKE2S_COMPRESS_BLOCKS_AGREE THEN CONJ_TAC THENL
   [MATCH_MP_TAC BLAKE2S_COMPRESS_BLOCKS_AGREE THEN CONJ_TAC THENL
     [MATCH_MP_TAC BLAKE2S_COMPRESS_BLOCKS_AGREE THEN
      REWRITE_TAC[WG_AGREE_REFL] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC BLAKE2S_BLOCK_APPEND_LEFT THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `j < 1 <=> j = 0`] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC BLAKE2S_BLOCK_AGREE_SUB_LIST THEN
      REWRITE_TAC[MULT_CLAUSES; WG_SUB_LIST_SUB_LIST; ADD_CLAUSES] THEN
      MP_TAC(ISPECL [`d:byte list`; `m:byte list`; `64 * n`; `b:num`;
                     `64 - b`] WG_SUB_LIST_APPEND_STRADDLE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `b <= 64 ==> b + (64 - b) = 64`] THEN
      DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SUB_LIST_REFL THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC BLAKE2S_BLOCK_AGREE_SUB_LIST THEN
    REWRITE_TAC[WG_SUB_LIST_SUB_LIST] THEN
    SUBGOAL_THEN
     `64 * n + 64 * 1 + 64 * j = LENGTH(d:byte list) + (64 - b + 64 * j)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[WG_SUB_LIST_APPEND_RIGHT]] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WG_SUB_LIST_SUB_LIST_GEN THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* blake2s_final(state, out) compresses the bytes left in the buffer, padded *)
(* with zeros, as the last block with the total length as the counter, and   *)
(* outputs the first outlen bytes of the result: for the state of            *)
(* __blake2s_init(state, outlen, key, keylen) followed by updates with the   *)
(* bytes of msg, the hash of RFC 7693.                                       *)
(* ------------------------------------------------------------------------- *)

let blake2s_input = new_definition
 `blake2s_input (key:byte list) (msg:byte list) =
    APPEND (if LENGTH key = 0 then []
            else APPEND key (REPLICATE (64 - LENGTH key) (word 0))) msg`;;

let blake2s_h0 = new_definition
 `blake2s_h0 kk nn =
    \i. if i = 0
        then word_xor (EL 0 blake2s_iv)
              (word_xor (word 0x01010000)
                (word_xor (word_shl (word kk) 8) (word nn)))
        else EL i blake2s_iv`;;

let blake2s_final_hash = new_definition
 `blake2s_final_hash h0 (d:byte list) =
    blake2s_compress (blake2s_chain h0 d)
      (blake2s_block
        (APPEND (SUB_LIST(64 * blake2s_nblocks d,blake2s_buflen d) d)
                (REPLICATE (64 - blake2s_buflen d) (word 0))) 0)
      (LENGTH d) T`;;

let BLAKE2S_BLOCKS_CHAIN = prove
 (`!h0 p (d:byte list) n.
     (!k. k < n ==> SUB_LIST(64 * k,64) p = SUB_LIST(64 * k,64) d) /\
     64 * n < 2 EXP 64
     ==> wg_agree 8 (blake2s_blocks (blake2s_block p) h0 n)
                    (blake2s_compress_blocks h0 d (word 0) 64 F n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[blake2s_blocks; blake2s_compress_blocks; WG_AGREE_REFL] THEN
  STRIP_TAC THEN REWRITE_TAC[WORD_ADD_0; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(64 * (n + 1)) MOD 2 EXP 64 = 64 * (n + 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC BLAKE2S_COMPRESS_AGREE THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `k < n ==> k < SUC n`] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BLAKE2S_BLOCK_AGREE_SUB_LIST THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let BLAKE2S_STREAM = prove
 (`!key nn msg.
     LENGTH key <= 64 /\ LENGTH(blake2s_input key msg) < 2 EXP 64
     ==> blake2s key nn msg =
         SUB_LIST(0,nn) (blake2s_bytes
           (blake2s_final_hash (blake2s_h0 (LENGTH key) nn)
                               (blake2s_input key msg)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[blake2s; blake2s_data] THEN
  REWRITE_TAC[GSYM blake2s_input] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `blake2s_input key msg` BLAKE2S_BUFLEN) THEN
  ABBREV_TAC `D = blake2s_input key msg` THEN
  ABBREV_TAC `n = blake2s_nblocks D` THEN ABBREV_TAC `b = blake2s_buflen D` THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAX 1 ((LENGTH(D:byte list) + 63) DIV 64) = n + 1`
  SUBST1_TAC THENL
   [REWRITE_TAC[MAX] THEN ASM_CASES_TAC `b = 0` THENL
     [SUBGOAL_THEN `LENGTH(D:byte list) = 0 /\ n = 0` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
      SUBGOAL_THEN `(LENGTH(D:byte list) + 63) DIV 64 = n + 1` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `b - 1` THEN ASM_ARITH_TAC;
        ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(if LENGTH(key:byte list) = 0 then LENGTH(msg:byte list)
                 else LENGTH msg + 64) = LENGTH(D:byte list)` SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[blake2s_input] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_REPLICATE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `64 * (n + 1) - LENGTH(D:byte list) = 64 - b` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[ADD_SUB]] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC BLAKE2S_BYTES_AGREE THEN
  ASM_REWRITE_TAC[blake2s_final_hash; blake2s_h0; blake2s_chain] THEN
  MATCH_MP_TAC BLAKE2S_COMPRESS_AGREE THEN CONJ_TAC THENL
   [MATCH_MP_TAC BLAKE2S_BLOCKS_CHAIN THEN CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC WG_SUB_LIST_APPEND_LEFT THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    MATCH_MP_TAC BLAKE2S_BLOCK_AGREE_SUB_LIST THEN
    MP_TAC(ISPECL [`D:byte list`; `REPLICATE (64 - b) (word 0):byte list`;
                   `64 * n`; `b:num`; `64 - b`]
                  WG_SUB_LIST_APPEND_STRADDLE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `b <= 64 ==> b + (64 - b) = 64`] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[SUB_LIST_REFL; LENGTH_REPLICATE; LE_REFL; MULT_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_LIST_REFL THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; LENGTH_REPLICATE] THEN
    ASM_ARITH_TAC]);;

(* The hash of WireGuard (unkeyed BLAKE2s with 32-byte output).              *)

let WG_HASH_STREAM = prove
 (`!x:byte list.
     LENGTH x < 2 EXP 64
     ==> wg_hash x =
         SUB_LIST(0,32) (blake2s_bytes
           (blake2s_final_hash (blake2s_h0 0 32) x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wg_hash] THEN
  MP_TAC(ISPECL [`[]:byte list`; `32`; `x:byte list`] BLAKE2S_STREAM) THEN
  REWRITE_TAC[blake2s_input; LENGTH; APPEND; LE_0] THEN ASM_REWRITE_TAC[]);;

(* HMAC with a key of 32 bytes (all the uses in noise.c) as the two hashes   *)
(* of the kernel's hmac.                                                     *)

let WG_HMAC_STREAM = prove
 (`!kb m:byte list.
     LENGTH kb = 32 /\ LENGTH m + 64 < 2 EXP 64
     ==> wg_hmac kb m =
         SUB_LIST(0,32) (blake2s_bytes (blake2s_final_hash (blake2s_h0 0 32)
           (APPEND (MAP (word_xor (word 0x5c))
                        (APPEND kb (REPLICATE 32 (word 0))))
             (SUB_LIST(0,32) (blake2s_bytes
                (blake2s_final_hash (blake2s_h0 0 32)
                  (APPEND (MAP (word_xor (word 0x36))
                               (APPEND kb (REPLICATE 32 (word 0))))
                          m)))))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wg_hmac] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(32 > 64)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (MAP (word_xor (word 54)) (APPEND kb (REPLICATE 32 (word 0))))
                  (m:byte list)) < 2 EXP 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE] THEN
    UNDISCH_TAC `LENGTH(m:byte list) + 64 < 2 EXP 64` THEN ARITH_TAC;
    ASM_SIMP_TAC[WG_HASH_STREAM]] THEN
  MATCH_MP_TAC WG_HASH_STREAM THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE; LENGTH_SUB_LIST;
                  blake2s_bytes; LENGTH_BYTELIST_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The lengths of the hashes, and the outputs of the HKDF of wg_kdf1/2/3.    *)

let LENGTH_BLAKE2S = prove
 (`!key nn msg. LENGTH(blake2s key nn msg) = MIN nn 32`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blake2s] THEN REPEAT LET_TAC THEN
  REWRITE_TAC[LENGTH_SUB_LIST; blake2s_bytes; LENGTH_BYTELIST_OF_NUM; SUB_0]);;

let LENGTH_WG_HASH = prove
 (`!x. LENGTH(wg_hash x) = 32`,
  REWRITE_TAC[wg_hash; LENGTH_BLAKE2S] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_WG_HMAC = prove
 (`!k x. LENGTH(wg_hmac k x) = 32`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wg_hmac] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH_WG_HASH]);;

let WG_KDF_T_CLAUSES = prove
 (`!t0. wg_kdf_t t0 1 = wg_hmac t0 [word 1] /\
        wg_kdf_t t0 2 = wg_hmac t0 (APPEND (wg_kdf_t t0 1) [word 2]) /\
        wg_kdf_t t0 3 = wg_hmac t0 (APPEND (wg_kdf_t t0 2) [word 3])`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; wg_kdf_t; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_WG_DH = prove
 (`!sb pb. LENGTH(wg_dh sb pb) = 32`,
  REWRITE_TAC[wg_dh; LENGTH_BYTELIST_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* ChaCha20: the 64 bytes of a block as the number of its 16 words.          *)
(* ------------------------------------------------------------------------- *)

let CHACHA20_WORDS_NUM =
  let wl = mk_list(map (fun i -> mk_comb(`x:num->int32`,mk_small_numeral i))
                       (0--15),`:int32`) in
  prove
   (mk_forall(`x:num->int32`,
     mk_eq(`num_of_bytelist(chacha20_words 16 x)`,
           mk_comb(`num_of_wordlist:int32 list->num`,wl))),
    GEN_TAC THEN REWRITE_TAC[chacha20_words; NUM_OF_BYTELIST_OF_NUM] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    W(fun (asl,w) -> SUBGOAL_THEN (mk_eq(lhand(lhand w),rand w))
                     SUBST1_TAC) THENL
     [CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN
      REWRITE_TAC[num_of_wordlist; DIMINDEX_32] THEN ARITH_TAC;
      MATCH_MP_TAC MOD_LT THEN
      MP_TAC(ISPEC wl NUM_OF_WORDLIST_BOUND) THEN
      REWRITE_TAC[LENGTH; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* The state of chacha_crypt after j blocks (the counter, word 12, advanced  *)
(* by j), and its keystream block, which for the state of RFC 8439 is the    *)
(* ChaCha20 block of the counter advanced by j.                              *)

let chacha20_ctr = new_definition
 `chacha20_ctr (xs:num->int32) j =
    \i. if i = 12 then word_add (xs 12) (word j) else xs i`;;

let chacha20_kblock = new_definition
 `chacha20_kblock (xs:num->int32) j =
    chacha20_words 16
      (\i. word_add (chacha20_rounds 10 (chacha20_ctr xs j) i)
                    (chacha20_ctr xs j i))`;;

let CHACHA20_CTR_STATE = prove
 (`!key c nonce j.
     chacha20_ctr (chacha20_state key c nonce) j =
     chacha20_state key (c + j) nonce`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; chacha20_ctr] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 12` THEN
  ASM_REWRITE_TAC[chacha20_state] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD]);;

let CHACHA20_KBLOCK_STATE = prove
 (`!key c nonce j.
     chacha20_kblock (chacha20_state key c nonce) j =
     chacha20_block key (c + j) nonce`,
  REWRITE_TAC[chacha20_kblock; CHACHA20_CTR_STATE; chacha20_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let CHACHA20_CTR_ADD = prove
 (`!xs j k. chacha20_ctr (chacha20_ctr xs j) k = chacha20_ctr xs (j + k)`,
  REWRITE_TAC[FUN_EQ_THM; chacha20_ctr] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let CHACHA20_CTR_1 = prove
 (`!xs:num->int32 i.
     chacha20_ctr xs 1 i = if i = 12 then word_add (xs 12) (word 1) else xs i`,
  REWRITE_TAC[chacha20_ctr]);;

let LENGTH_CHACHA20_KBLOCK = prove
 (`!xs j. LENGTH(chacha20_kblock xs j) = 64`,
  REWRITE_TAC[chacha20_kblock; chacha20_words; LENGTH_BYTELIST_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* XChaCha20: the lengths of the HChaCha20 subkey and of the 12-byte nonce.  *)

let LENGTH_HCHACHA20 = prove
 (`!key nonce. LENGTH(hchacha20 key nonce) = 32`,
  REWRITE_TAC[hchacha20; LET_DEF; LET_END_DEF; LENGTH_APPEND; chacha20_words;
              LENGTH_BYTELIST_OF_NUM] THEN ARITH_TAC);;

let LENGTH_XCHACHA20_NONCE = prove
 (`!nb:byte list. LENGTH nb = 24 ==> LENGTH(xchacha20_nonce nb) = 12`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[xchacha20_nonce; LENGTH_APPEND; LENGTH_REPLICATE;
                  LENGTH_SUB_LIST] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Poly1305 as the kernel computes it (lib/crypto/poly1305.c and             *)
(* poly1305-donna64.c): the accumulator after the first j blocks of 16 bytes *)
(* of m from the accumulator a, each block with 2^128 * hb added (hb = 1 for *)
(* the full blocks of the message, 0 for a last block padded by the caller). *)
(* ------------------------------------------------------------------------- *)

let poly1305_kacc = define
 `poly1305_kacc r a (m:byte list) hb 0 = a /\
  poly1305_kacc r a m hb (SUC j) =
    ((poly1305_kacc r a m hb j + num_of_bytelist(SUB_LIST(16 * j,16) m) +
      2 EXP 128 * hb) * r) MOD (2 EXP 130 - 5)`;;

let POLY1305_R_SUB_LIST = prove
 (`!k:byte list. poly1305_r(SUB_LIST(0,16) k) = poly1305_r k`,
  GEN_TAC THEN REWRITE_TAC[poly1305_r] THEN
  SIMP_TAC[WG_SUB_LIST_SUB_LIST_GEN; LE_REFL; ADD_CLAUSES]);;

let POLY1305_R_BOUND = prove
 (`!k. poly1305_r k < 2 EXP 124`,
  GEN_TAC THEN REWRITE_TAC[poly1305_r] THEN
  W(MP_TAC o PART_MATCH lhand (CONJUNCT2 VAL_WORD_AND_LE) o lhand o snd) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

(* The accumulator after i + j blocks is that after j more blocks from the   *)
(* one after i; it only depends on the blocks used; so the accumulator of    *)
(* the blocks of a list l1 of whole blocks followed by l2 is that of the     *)
(* blocks of l2 from the one of l1.                                          *)

let POLY1305_KACC_DROP = prove
 (`!r a (l:byte list) hb i j.
     poly1305_kacc r a l hb (i + j) =
     poly1305_kacc r (poly1305_kacc r a l hb i)
                   (SUB_LIST(16 * i,LENGTH l - 16 * i) l) hb j`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[poly1305_kacc; ADD_CLAUSES] THEN
  REWRITE_TAC[WG_SUB_LIST_SUB_LIST; LEFT_ADD_DISTRIB]);;

let POLY1305_KACC_PREFIX = prove
 (`!r a (l:byte list) l' hb j.
     (!i. i < j ==> SUB_LIST(16 * i,16) l = SUB_LIST(16 * i,16) l')
     ==> poly1305_kacc r a l hb j = poly1305_kacc r a l' hb j`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[poly1305_kacc] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let POLY1305_KACC_SPLIT = prove
 (`!r a (l1:byte list) l2 hb q j.
     LENGTH l1 = 16 * q
     ==> poly1305_kacc r a (APPEND l1 l2) hb (q + j) =
         poly1305_kacc r (poly1305_kacc r a l1 hb q) l2 hb j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[POLY1305_KACC_DROP] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN BINOP_TAC THENL
   [MATCH_MP_TAC POLY1305_KACC_PREFIX THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WG_SUB_LIST_APPEND_LEFT THEN
    ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM(ASSUME `LENGTH(l1:byte list) = 16 * q`)] THEN
    REWRITE_TAC[LENGTH_APPEND; ADD_SUB2] THEN
    MP_TAC(ISPECL [`l1:byte list`; `l2:byte list`; `0`; `LENGTH(l2:byte list)`]
           WG_SUB_LIST_APPEND_RIGHT) THEN
    REWRITE_TAC[ADD_CLAUSES; SUB_LIST_LENGTH]]);;

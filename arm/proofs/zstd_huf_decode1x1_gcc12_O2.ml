(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* HUF_decompress1X1_usingDTable_internal(dst,dstSize,cSrc,cSrcSize,DTable)  *)
(* of zstd, at 0x2850 in the image (as a copy specialized for its constant   *)
(* argument flags), which decodes the dstSize bytes of the single            *)
(* Huffman-coded stream at cSrc with the decoding table DTable built by      *)
(* HUF_readDTableX1_wksp, returning dstSize, or an error code if the stream  *)
(* does not consist exactly of the codes of dstSize bytes.                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/zstd_huf.ml";;

(* ------------------------------------------------------------------------- *)
(* The decoding table: 2^tl entries of 2 bytes, of which the entry for the   *)
(* state x has the number of bits and the symbol of the state, for the code  *)
(* of the weights ws with codes of at most ml <= tl bits.                    *)
(* ------------------------------------------------------------------------- *)

let huf_dtable = new_definition
 `huf_dtable ws ml tl =
    list_of_seq
     (\i. let y = (i DIV 2) DIV 2 EXP (tl - ml) in
          if EVEN i then word((ml + 1) - EL (huf_symbol ws y) ws):byte
          else word(huf_symbol ws y))
     (2 * 2 EXP tl)`;;

let LENGTH_HUF_DTABLE = prove
 (`!ws ml tl. LENGTH(huf_dtable ws ml tl) = 2 * 2 EXP tl`,
  REWRITE_TAC[huf_dtable; LENGTH_LIST_OF_SEQ]);;

let HUF_DTABLE_ENTRY = prove
 (`!ws ml tl x.
        x < 2 EXP tl
        ==> EL (2 * x) (huf_dtable ws ml tl) =
            word((ml + 1) - EL (huf_symbol ws (x DIV 2 EXP (tl - ml))) ws) /\
            EL (2 * x + 1) (huf_dtable ws ml tl) =
            word(huf_symbol ws (x DIV 2 EXP (tl - ml)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_dtable] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `x < n ==> 2 * x < 2 * n`;
               ARITH_RULE `x < n ==> 2 * x + 1 < 2 * n`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[EVEN_DOUBLE; EVEN_ADD; ARITH_EVEN] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x) DIV 2 = x /\ (2 * x + 1) DIV 2 = x`]);;

let HUF_DTABLE_READ = prove
 (`!ws ml tl (tbl:int64) x s.
        x < 2 EXP tl /\
        read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
        num_of_bytelist (huf_dtable ws ml tl)
        ==> read (memory :> bytes8 (word_add tbl (word (2 * x)))) s =
            word((ml + 1) - EL (huf_symbol ws (x DIV 2 EXP (tl - ml))) ws) /\
            read (memory :> bytes8 (word_add tbl (word (2 * x + 1)))) s =
            word(huf_symbol ws (x DIV 2 EXP (tl - ml)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`tbl:int64`; `huf_dtable ws ml tl`; `2 * x`;
                   `s:armstate`] READ_MEMORY_BYTES8_BYTELIST);
    MP_TAC(ISPECL [`tbl:int64`; `huf_dtable ws ml tl`; `2 * x + 1`;
                   `s:armstate`] READ_MEMORY_BYTES8_BYTELIST)] THEN
  ASM_REWRITE_TAC[LENGTH_HUF_DTABLE] THEN
  ASM_SIMP_TAC[HUF_DTABLE_ENTRY; ARITH_RULE `x < n ==> 2 * x < 2 * n`;
               ARITH_RULE `x < n ==> 2 * x + 1 < 2 * n`]);;

(* The entries of the table: the number of bits is from 1 to ml, and the     *)
(* symbol is a byte.                                                         *)

let HUF_NBITS_BOUND = prove
 (`!ws ml y. huf_complete ws ml /\ y < 2 EXP ml
             ==> 1 <= (ml + 1) - EL (huf_symbol ws y) ws /\
                 (ml + 1) - EL (huf_symbol ws y) ws <= ml`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_complete] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `y:num`] HUF_SYMBOL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `huf_symbol ws y`) THEN
  UNDISCH_TAC `huf_symbol ws y IN huf_present ws` THEN
  REWRITE_TAC[huf_present; IN_ELIM_THM] THEN ARITH_TAC);;

let HUF_SYMBOL_BOUND = prove
 (`!ws ml y. huf_complete ws ml /\ LENGTH ws <= 256 /\ y < 2 EXP ml
             ==> huf_symbol ws y < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_complete] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `y:num`] HUF_SYMBOL) THEN
  ASM_REWRITE_TAC[huf_present; IN_ELIM_THM] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lookup of the table with the top tl bits of the bit container c of 64 *)
(* bits, of which bc have been used: the container holds the 8 bytes of the  *)
(* stream from ofs, so the state is that of the specification at position    *)
(* 8 * ofs + 64 - bc, provided that the container still holds tl bits, or    *)
(* holds the start of the stream, below which there are only 0 bits.         *)
(* ------------------------------------------------------------------------- *)

let DIV_MULT2_ALT = prove
 (`!a b c. ~(a = 0) ==> (a * b) DIV (a * c) = b DIV c`,
  SIMP_TAC[DIV_MULT2]);;

let HUF_WINDOW_ARITH = prove
 (`!x k bc tl. bc < 64 /\ tl <= 64 /\ (tl + bc <= 64 \/ k = 0)
             ==> ((((x DIV 2 EXP k) MOD 2 EXP 64) * 2 EXP bc) MOD 2 EXP 64)
                 DIV 2 EXP (64 - tl) =
                 (2 EXP tl * (x MOD 2 EXP (k + 64 - bc))) DIV
                 2 EXP (k + 64 - bc)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(((x DIV 2 EXP k) MOD 2 EXP 64) * 2 EXP bc) MOD 2 EXP 64 =
    2 EXP bc * (x DIV 2 EXP k) MOD 2 EXP (64 - bc)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `2 EXP 64 = 2 EXP bc * 2 EXP (64 - bc)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM] THEN
    REWRITE_TAC[MOD_MULT2; MOD_MOD_EXP_MIN] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `2 EXP (64 - tl) = 2 EXP bc * 2 EXP (64 - bc - tl)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[DIV_MULT2_ALT; EXP_EQ_0; ARITH_EQ]] THEN
    SUBGOAL_THEN `2 EXP (k + 64 - bc) = 2 EXP tl * 2 EXP (k + 64 - bc - tl)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[DIV_MULT2_ALT; EXP_EQ_0; ARITH_EQ]] THEN
    SUBGOAL_THEN `2 EXP (64 - bc) = 2 EXP (64 - bc - tl) * 2 EXP tl /\
                  2 EXP (k + 64 - bc) = 2 EXP (k + 64 - bc - tl) * 2 EXP tl`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[GSYM DIV_MOD; DIV_DIV; GSYM EXP_ADD]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EXP; DIV_1; ADD_CLAUSES] THEN
    ABBREV_TAC `y = x MOD 2 EXP (64 - bc)` THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `(2 EXP tl * 2 EXP bc * y) DIV (2 EXP tl * 2 EXP (64 - tl))` THEN
    CONJ_TAC THENL [SIMP_TAC[DIV_MULT2_ALT; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `(2 EXP bc * 2 EXP tl * y) DIV (2 EXP bc * 2 EXP (64 - bc))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `2 EXP tl * 2 EXP (64 - tl) = 2 EXP 64 /\
                    2 EXP bc * 2 EXP (64 - bc) = 2 EXP 64`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[MULT_AC]];
      SIMP_TAC[DIV_MULT2_ALT; EXP_EQ_0; ARITH_EQ]]]);;

let HUF_WINDOW = prove
 (`!(st:byte list) ofs bc tl.
        bc < 64 /\ tl <= 64 /\ (tl + bc <= 64 \/ ofs = 0)
        ==> ((((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) *
              2 EXP bc) MOD 2 EXP 64) DIV 2 EXP (64 - tl) =
            zstd_back st (8 * ofs + 64 - bc) tl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zstd_back; ZSTD_BITS_NUM; EXP; DIV_1] THEN
  MATCH_MP_TAC HUF_WINDOW_ARITH THEN ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ]);;

(* The index computed, as an offset in the table.                            *)

let HUF_INDEX_WORD = prove
 (`!c bc tl.
        bc < 64 /\ 1 <= tl /\ tl <= 12
        ==> word_shl (word_jushr (word (2 EXP bc * c):int64)
                                 (word (64 - tl))) 1 =
            word (2 * (((c * 2 EXP bc) MOD 2 EXP 64) DIV 2 EXP (64 - tl)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jushr; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(64 - tl) MOD 2 EXP 64 MOD 64 = 64 - tl` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 64`;
                 ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 2 EXP 64`];
    ALL_TAC] THEN
  REWRITE_TAC[word_shl; word_ushr] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; EXP_1] THEN
  SUBGOAL_THEN
   `((2 EXP bc * c) MOD 2 EXP 64 DIV 2 EXP (64 - tl)) MOD 2 EXP 64 =
    (2 EXP bc * c) MOD 2 EXP 64 DIV 2 EXP (64 - tl)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `(2 EXP bc * c) MOD 2 EXP 64` THEN
    REWRITE_TAC[DIV_LE; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    REWRITE_TAC[MULT_SYM]]);;


(* The entry of the table for the state, through the index computed, as      *)
(* addresses in the form of those of the simulation, for the table at tbl.   *)

let HUF_LOOKUP_LEMMA = prove
 (`!(st:byte list) ofs bc tl c ws ml (tbl:int64) s.
        c = (num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64 /\
        bc < 64 /\ 1 <= tl /\ tl <= 12 /\ ml <= tl /\
        (tl + bc <= 64 \/ ofs = 0) /\
        read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
        num_of_bytelist (huf_dtable ws ml tl)
        ==> word_shl (word_jushr (word (2 EXP bc * c):int64)
                                 (word (64 - tl))) 1 =
            word (2 * zstd_back st (8 * ofs + 64 - bc) tl) /\
            read (memory :> bytes8
                   (word_add tbl
                     (word (2 * zstd_back st (8 * ofs + 64 - bc) tl)))) s =
            word((ml + 1) -
                 EL (huf_symbol ws (zstd_back st (8 * ofs + 64 - bc) ml))
                    ws) /\
            read (memory :> bytes8
                   (word_add tbl
                     (word (2 * zstd_back st (8 * ofs + 64 - bc) tl + 1)))) s =
            word(huf_symbol ws (zstd_back st (8 * ofs + 64 - bc) ml))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[HUF_INDEX_WORD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC HUF_WINDOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `zstd_back st (8 * ofs + 64 - bc) ml =
                zstd_back st (8 * ofs + 64 - bc) tl DIV 2 EXP (tl - ml)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ZSTD_BACK_DIV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HUF_DTABLE_READ THEN ASM_REWRITE_TAC[ZSTD_BACK_BOUND]]);;

(* The index computed from any bits, when the bits used are past the start   *)
(* of the stream.                                                            *)

let HUF_INDEX_ANY = prove
 (`!(y:int64) tl.
        1 <= tl /\ tl <= 12
        ==> word_shl (word_jushr y (word (64 - tl))) 1 =
            word (2 * val(word_jushr y (word (64 - tl)))) /\
            val(word_jushr y (word (64 - tl))) < 2 EXP tl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_jushr y (word (64 - tl)) = word_ushr (y:int64) (64 - tl)`
  SUBST1_TAC THENL
   [REWRITE_TAC[word_jushr; VAL_WORD; DIMINDEX_64] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 64`;
                 ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 2 EXP 64`];
    ALL_TAC] THEN
  REWRITE_TAC[word_shl; VAL_WORD_USHR; EXP_1] THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
  SUBGOAL_THEN `64 - tl + tl = 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]);;

let DIV_EXP_LT = prove
 (`!x k m. x < 2 EXP k /\ m <= k ==> x DIV 2 EXP (k - m) < 2 EXP m`,
  REPEAT STRIP_TAC THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  SUBGOAL_THEN `k - m + m = k` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* The shift 64 - tl computed from tl.                                       *)

let HUF_SHIFT_WORD = prove
 (`!tl. 1 <= tl /\ tl <= 12
        ==> word_zx (word_and (word_sub (word 0) (word tl):int32)
                              (word 63)):int64 = word (64 - tl)`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE
   `1 <= tl /\ tl <= 12 <=>
    tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/
    tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The decoding of one more symbol, and its byte stored after the others.    *)
(* ------------------------------------------------------------------------- *)

let HUF_DECODE_SUC = prove
 (`!ws ml (st:byte list) q k.
     FST(huf_decode ws ml st q (k + 1)) =
     APPEND (FST(huf_decode ws ml st q k))
      [word(huf_symbol ws (zstd_back st (FST(SND(huf_decode ws ml st q k)))
                                     ml))] /\
     FST(SND(huf_decode ws ml st q (k + 1))) =
     FST(SND(huf_decode ws ml st q k)) -
     ((ml + 1) -
      EL (huf_symbol ws (zstd_back st (FST(SND(huf_decode ws ml st q k))) ml))
         ws) /\
     (SND(SND(huf_decode ws ml st q (k + 1))) <=>
      SND(SND(huf_decode ws ml st q k)) /\
      (ml + 1) -
      EL (huf_symbol ws (zstd_back st (FST(SND(huf_decode ws ml st q k))) ml))
         ws <= FST(SND(huf_decode ws ml st q k)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ADD1; huf_decode] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let HUF_MEM_STEP = prove
 (`!dst ws ml (st:byte list) r j j' sym s.
        j + 1 = j' /\
        read (memory :> bytes(dst,j)) s =
        num_of_bytelist(FST(huf_decode ws ml st r j)) /\
        read (memory :> bytes8(word_add dst (word j))) s = word sym /\
        FST(huf_decode ws ml st r j') =
        APPEND (FST(huf_decode ws ml st r j)) [word sym]
        ==> read (memory :> bytes(dst,j')) s =
            num_of_bytelist(FST(huf_decode ws ml st r j'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `j':num`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`dst:int64`; `FST(huf_decode ws ml (st:byte list) r j)`;
                 `word sym:byte`; `s:armstate`] READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[HUF_DECODE_LENGTH]);;

(* ------------------------------------------------------------------------- *)
(* The state of the decoding. The stream st, of LENGTH st bytes at src, is   *)
(* read backwards, from its last bit r (zstd_end st r) down to bit 0, and    *)
(* huf_decode ws ml st r j gives the first j bytes decoded, the position     *)
(* after them and whether no code needed more bits than were left. The bit   *)
(* container in x4 holds the 8 bytes from ofs, src + ofs being the pointer   *)
(* in x7, with ofs = 0 or ofs + 8 <= LENGTH st (if the stream is shorter     *)
(* than 8 bytes, it holds them all, with ofs = 0), and bc in w3 of its bits  *)
(* have been used, so that the position is 8 * ofs + 64 - bc. The bytes      *)
(* decoded so far are at dst, which x5 points after, and the table, of which *)
(* the entry for a state of tl bits has its number of bits and symbol, is at *)
(* tbl in x6. Since the container is reloaded before each group of 4 bytes,  *)
(* when bc <= 7, the table is looked up with at least tl bits left in it,    *)
(* or the start of the stream in it. When the stream runs out, the code goes *)
(* on with bc > 64, and the bytes decoded are garbage, but decoding the n    *)
(* bytes then fails in the specification too, and the code returns an error. *)
(*                                                                           *)
(* The assertions below are at:                                              *)
(*                                                                           *)
(*   0x2990  huf_rinv, before the reload of the container for bytes 4k ...   *)
(*   0x2904  huf_body, before decoding bytes 4k to 4k + 3                    *)
(*   0x2a38  huf_tail, after the main loop, with j bytes decoded             *)
(*   0x2a40  huf_tloop, before the loop for the last bytes                   *)
(*   0x2a48  huf_tinv, in that loop, with bc > 64 once the stream has run    *)
(*           out                                                             *)
(*   0x2a70  huf_endchk, the check that the stream has been used exactly     *)
(*                                                                           *)
(* and each has a theorem that it leads to the return with the result as in  *)
(* huf_post, proved from those of the later ones. Each has the conjunct      *)
(* puff_memsafe e rr wr s, for the trace e at the entry, the loads being     *)
(* from the stream, the table and the byte DTable[2] (read at the entry) and *)
(* the stores to the n bytes at dst.                                         *)
(* ------------------------------------------------------------------------- *)

let huf_rr =
 `[src,LENGTH(st:byte list); word_add dtable (word 2),1;
   tbl,2 * 2 EXP tl]:(int64#num)list`
and huf_wr = `[dst,n]:(int64#num)list`;;

let huf_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
  huf_complete ws ml /\ LENGTH ws <= 256 /\
  ml <= tl /\ 1 <= tl /\ tl <= 12 /\ n < 2 EXP 28 /\
  8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64 /\
  val(dst:int64) + n < 2 EXP 64 /\
  nonoverlapping (dst,n) (src,LENGTH st) /\
  nonoverlapping (dst,n) (tbl,2 * 2 EXP tl) /\
  nonoverlapping (dst,n) (word pc,32000)`;;

let huf_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [memory :> bytes(dst,n)]`;;

let huf_vars =
 [`pc:num`; `returnaddress:int64`; `dst:int64`; `n:num`; `src:int64`;
  `st:byte list`; `dtable:int64`; `tbl:int64`; `ws:num list`; `ml:num`;
  `tl:num`; `r:num`; `e:uarch_event list`];;

(*** The goal for a piece from pre to post, with the variables huf_vars ***)
(*** and extra quantified in this order                                ***)

let mk_huf_goal extra pre post =
  let tm = mk_imp(huf_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; huf_frame]) in
  let vs = huf_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_huf_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** At the return: dstSize if the n bytes decoded use all of the stream, ***)
(*** and -20 (ERROR(corruption_detected)) otherwise                       ***)

let huf_post = with_memsafe huf_rr huf_wr `\s.
  read PC s = returnaddress /\
  read X0 s =
  (if SND(SND(huf_decode ws ml st r n)) /\
      FST(SND(huf_decode ws ml st r n)) = 0
   then word n else word 18446744073709551596) /\
  (SND(SND(huf_decode ws ml st r n)) /\
   FST(SND(huf_decode ws ml st r n)) = 0
   ==> read (memory :> bytes(dst,n)) s =
       num_of_bytelist(FST(huf_decode ws ml (st:byte list) r n)))`;;

(*** At 0x2a70, after the n bytes ***)

let huf_endchk = with_memsafe huf_rr huf_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x2a70) /\ read X30 s = returnaddress /\
  read X1 s = word n /\ read X2 s = src /\
  read X7 s = word_add src (word ofs) /\ read X3 s = word bc /\
  (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
  (SND(SND(huf_decode ws ml st r n)) /\
   FST(SND(huf_decode ws ml st r n)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   read (memory :> bytes(dst,n)) s =
   num_of_bytelist(FST(huf_decode ws ml st r n)) \/
   ~SND(SND(huf_decode ws ml st r n)) /\ ofs = 0 /\ 64 < bc /\
   bc <= 64 + 12 * n)`;;

(*** At 0x2a40, before the loop for the last j < n bytes ***)

let huf_tloop = with_memsafe huf_rr huf_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x2a40) /\ read X30 s = returnaddress /\
  read X1 s = word n /\ read X2 s = src /\ read X6 s = tbl /\
  read X10 s = word_add dst (word n) /\ read X11 s = word tl /\
  read X5 s = word_add dst (word j) /\
  read X7 s = word_add src (word ofs) /\
  read X4 s = word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read X3 s = word bc /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl) /\
  (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ j < n /\
  SND(SND(huf_decode ws ml st r j)) /\
  FST(SND(huf_decode ws ml st r j)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
  (ofs = 0 \/ bc + 12 * (n - j) <= 52) /\
  read (memory :> bytes(dst,j)) s =
  num_of_bytelist(FST(huf_decode ws ml st r j))`;;

(*** At 0x2a48, in that loop, for the measure m = n - j ***)

let huf_tinv = with_memsafe huf_rr huf_wr `\m s. ?j bc.
  m = n - j /\ j < n /\
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x2a48) /\ read X30 s = returnaddress /\
  read X1 s = word n /\ read X2 s = src /\ read X6 s = tbl /\
  read X10 s = word_add dst (word n) /\ read X11 s = word(64 - tl) /\
  read X5 s = word_add dst (word j) /\
  read X7 s = word_add src (word ofs) /\
  read X4 s = word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read X3 s = word bc /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl) /\
  (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
  (SND(SND(huf_decode ws ml st r j)) /\
   FST(SND(huf_decode ws ml st r j)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   (ofs = 0 \/ bc + 12 * (n - j) <= 52) /\
   read (memory :> bytes(dst,j)) s =
   num_of_bytelist(FST(huf_decode ws ml st r j)) \/
   ~SND(SND(huf_decode ws ml st r j)) /\ ofs = 0 /\ 64 < bc /\
   bc <= 64 + 12 * j)`;;

(*** At 0x2a38, after the main loop, with j <= n bytes ***)

let huf_tail = with_memsafe huf_rr huf_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x2a38) /\ read X30 s = returnaddress /\
  read X1 s = word n /\ read X2 s = src /\ read X6 s = tbl /\
  read X10 s = word_add dst (word n) /\ read X11 s = word tl /\
  read X5 s = word_add dst (word j) /\
  read X7 s = word_add src (word ofs) /\
  read X4 s = word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read X3 s = word bc /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl) /\
  (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ j <= n /\
  SND(SND(huf_decode ws ml st r j)) /\
  FST(SND(huf_decode ws ml st r j)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
  (ofs = 0 \/ bc + 12 * (n - j) <= 52) /\
  read (memory :> bytes(dst,j)) s =
  num_of_bytelist(FST(huf_decode ws ml st r j))`;;

(*** At 0x2990, the main loop, for the measure m = n - 4 * k ***)

let huf_rinv = with_memsafe huf_rr huf_wr `\m s. ?k ofs bc.
  m = n - 4 * k /\ 4 * k <= n /\ 4 <= n /\
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x2990) /\ read X30 s = returnaddress /\
  read X1 s = word n /\ read X2 s = src /\ read X6 s = tbl /\
  read X9 s = word(64 - tl) /\ read X10 s = word_add dst (word n) /\
  read X11 s = word tl /\ read X12 s = word_add src (word 8) /\
  read X13 s = word_add dst (word(n - 3)) /\
  read X5 s = word_add dst (word(4 * k)) /\
  read X7 s = word_add src (word ofs) /\
  read X4 s = word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read X3 s = word bc /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl) /\
  (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
  SND(SND(huf_decode ws ml st r (4 * k))) /\
  FST(SND(huf_decode ws ml st r (4 * k))) = 8 * ofs + 64 - bc /\ bc <= 64 /\
  read (memory :> bytes(dst,4 * k)) s =
  num_of_bytelist(FST(huf_decode ws ml st r (4 * k)))`;;

(*** At 0x2904, before bytes 4k to 4k + 3, with the container reloaded ***)

let huf_body = with_memsafe huf_rr huf_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x2904) /\ read X30 s = returnaddress /\
  read X1 s = word n /\ read X2 s = src /\ read X6 s = tbl /\
  read X9 s = word(64 - tl) /\ read X10 s = word_add dst (word n) /\
  read X11 s = word tl /\ read X12 s = word_add src (word 8) /\
  read X13 s = word_add dst (word(n - 3)) /\
  read X5 s = word_add dst (word(4 * k)) /\
  read X7 s = word_add src (word ofs) /\
  read X4 s = word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read X3 s = word bc /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl) /\
  (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
  4 * k + 4 <= n /\ bc <= 7 /\
  SND(SND(huf_decode ws ml st r (4 * k))) /\
  FST(SND(huf_decode ws ml st r (4 * k))) = 8 * ofs + 64 - bc /\
  read (memory :> bytes(dst,4 * k)) s =
  num_of_bytelist(FST(huf_decode ws ml st r (4 * k)))`;;

(* ------------------------------------------------------------------------- *)
(* The check at the end: the result is dstSize if and only if ptr is at the  *)
(* start of the stream and bc = 64, that is if the position is 0, and the    *)
(* decoding did not fail.                                                    *)
(* ------------------------------------------------------------------------- *)

let HUF_ENDCHK = prove
 (mk_huf_goal [`ofs:num`; `bc:num`] huf_endchk huf_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
    check (free_in `bc:num` o concl)) THENL
   [ASM_CASES_TAC `ofs = 0` THENL [ASM_CASES_TAC `bc = 64`; ALL_TAC];
    ALL_TAC] THEN
  ZSTD_RUN_TAC THEN ZSTD_FINAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop for the last bytes, one at a time without reloading. Each        *)
(* iteration either looks up the table with the bits of the specification   *)
(* (bc < 64), or with garbage once the stream has run out, when the number   *)
(* of bits in the table entry is still at least 1.                           *)
(* ------------------------------------------------------------------------- *)

let HUF_TAIL_LOOKUP_TAC =
  ZSTD_STEPS_TAC (1--3) THEN
  MP_TAC(ISPECL [`st:byte list`; `ofs:num`; `bc:num`; `tl:num`; `c:num`;
                 `ws:num list`; `ml:num`; `tbl:int64`; `s3:armstate`]
    HUF_LOOKUP_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`st:byte list`; `8 * ofs + 64 - bc`; `tl:num`]
    ZSTD_BACK_BOUND) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back st (8 * ofs + 64 - bc) ml`] HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back st (8 * ofs + 64 - bc) ml`] HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `x = zstd_back st (8 * ofs + 64 - bc) tl` THEN
  ABBREV_TAC `y = zstd_back st (8 * ofs + 64 - bc) ml` THEN
  ABBREV_TAC `sym = huf_symbol ws y` THEN
  ABBREV_TAC `nb = (ml + 1) - EL sym ws`;;

let HUF_TAIL_ANY_TAC =
  ZSTD_STEPS_TAC (1--3) THEN
  MP_TAC(ISPECL [`word_jshl (word c) (word bc):int64`; `tl:num`]
    HUF_INDEX_ANY) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x = val(word_jushr (word_jshl (word c) (word bc):int64)
                                 (word (64 - tl)))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; `x:num`;
                 `s3:armstate`] HUF_DTABLE_READ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `tl:num`; `ml:num`] DIV_EXP_LT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (tl - ml)`]
    HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (tl - ml)`]
    HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `sym = huf_symbol ws (x DIV 2 EXP (tl - ml))` THEN
  ABBREV_TAC `nb = (ml + 1) - EL sym ws`;;

let HUF_TAIL_STEP_TAC =
  ZSTD_STEPS_TAC (4--8) THEN STATE_PTR_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL]) THEN
  ASM_CASES_TAC `j + 1 = n` THEN ZSTD_STEPS_TAC (9--10);;

let HUF_TAIL_SUBST_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `j + 1 = n`));;

let HUF_MEM_SNOC_TAC s =
  MP_TAC(ISPECL [`dst:int64`; `FST(huf_decode ws ml (st:byte list) r j)`;
                 `word sym:byte`; s] READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[HUF_DECODE_LENGTH];;

let HUF_GOOD_END_TAC,HUF_GOOD_LOOP_TAC =
  let fin =
    ASM_CASES_TAC `nb <= 8 * ofs + 64 - bc` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [HUF_MEM_SNOC_TAC `s10:armstate` THEN NO_TAC; ZSTD_ARITH_TAC] in
  (ZSTD_CONTINUE_TAC HUF_ENDCHK [`bc + nb:num`,`bc:num`] THEN
   HUF_TAIL_SUBST_TAC THEN MEMSAFE_ELIM_TAC THEN
   ASM_REWRITE_TAC[HUF_DECODE_SUC] THEN fin),
  (PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `n - (j + 1)` THEN
   CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`j + 1`; `bc + nb:num`] THEN
   ASM_REWRITE_TAC[HUF_DECODE_SUC] THEN
   CONJ_TAC THENL [SIMPLE_ARITH_TAC; fin]);;

let HUF_BAD_FACT_TAC =
  SUBGOAL_THEN `~SND(SND(huf_decode ws ml (st:byte list) r (j + 1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[HUF_DECODE_SUC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                   `zstd_back (st:byte list) (8 * ofs + 64 - bc) ml`]
      HUF_NBITS_BOUND) THEN
    ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN ZSTD_ARITH_TAC;
    ALL_TAC];;

let HUF_BAD_END_TAC,HUF_BAD_LOOP_TAC =
  (HUF_BAD_FACT_TAC THEN
   ZSTD_CONTINUE_TAC HUF_ENDCHK [`bc + nb:num`,`bc:num`] THEN
   HUF_TAIL_SUBST_TAC THEN MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC),
  (HUF_BAD_FACT_TAC THEN
   PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `n - (j + 1)` THEN
   CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`j + 1`; `bc + nb:num`] THEN
   ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC);;

let HUF_TLOOP = prove
 (mk_huf_goal [`ofs:num`; `j:num`; `bc:num`] huf_tloop huf_post,
  ZSTD_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC huf_tinv ENSURES_WHILE_MEASURE) THEN REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--2) THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `n - j:num` THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `bc:num`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[HUF_SHIFT_WORD]; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `j:num` THEN ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  PUFF_INIT_TAC "s0" THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (free_in `bc:num` o concl)) THENL
   [ASM_CASES_TAC `bc < 64` THENL
     [HUF_TAIL_LOOKUP_TAC THEN HUF_TAIL_STEP_TAC THENL
       [HUF_GOOD_END_TAC; HUF_GOOD_LOOP_TAC];
      ALL_TAC];
    ALL_TAC] THEN
  (HUF_TAIL_ANY_TAC THEN HUF_TAIL_STEP_TAC THENL
    [HUF_BAD_END_TAC; HUF_BAD_LOOP_TAC]));;

(* ------------------------------------------------------------------------- *)
(* After the main loop: the end check if all n bytes are done.               *)
(* ------------------------------------------------------------------------- *)

let HUF_TAIL = prove
 (mk_huf_goal [`ofs:num`; `j:num`; `bc:num`] huf_tail huf_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j:num = n` THENL
   [ZSTD_STEPS_TAC (1--2) THEN ZSTD_CONTINUE_TAC HUF_ENDCHK [] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `j:num = n`)) THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];
    ZSTD_STEPS_TAC (1--2) THEN ZSTD_CONTINUE_TAC HUF_TLOOP [] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The body of the main loop, decoding bytes 4k to 4k + 3 with 4 lookups.    *)
(* HUF_BODY_SYM_TAC sn j bc does lookup j at state sn with bc bits used,     *)
(* with the state of the specification after it.                             *)
(* ------------------------------------------------------------------------- *)

let HUF_BODY_SYM_TAC sn j bcv =
  let s = mk_var("s"^string_of_int sn,`:armstate`) in
  let jn = string_of_int j in
  let jt = if j = 0 then `4 * k` else mk_binop `(+):num->num->num` `4 * k`
                                       (mk_small_numeral j)
  and jt' = mk_binop `(+):num->num->num` `4 * k` (mk_small_numeral(j + 1)) in
  let pos = mk_binop `(+):num->num->num` `8 * ofs`
              (mk_binop `(-):num->num->num` `64` bcv) in
  let xv = mk_var("x"^jn,`:num`) and yv = mk_var("y"^jn,`:num`)
  and symv = mk_var("sym"^jn,`:num`) and nbv = mk_var("nb"^jn,`:num`) in
  let back k = list_mk_icomb "zstd_back" [`st:byte list`; pos; k] in
  let dec t = list_mk_icomb "huf_decode"
                [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; t] in
  let fsts t = mk_icomb(`FST:num#bool->num`,
                        mk_icomb(`SND:byte list#num#bool->num#bool`,dec t))
  and snds t = mk_icomb(`SND:num#bool->bool`,
                        mk_icomb(`SND:byte list#num#bool->num#bool`,dec t))
  and fst t = mk_icomb(`FST:byte list#num#bool->byte list`,dec t) in
  let goal = list_mk_conj
   [mk_eq(fsts jt',mk_binop `(+):num->num->num` `8 * ofs`
      (mk_binop `(-):num->num->num` `64`
         (mk_binop `(+):num->num->num` nbv bcv)));
    snds jt';
    mk_eq(fst jt',list_mk_icomb "APPEND"
      [fst jt; mk_list([mk_comb(`word:num->byte`,symv)],`:byte`)])] in
  let split = if j = 0 then ALL_TAC else
    REWRITE_TAC[ARITH_RULE(mk_eq(jt',mk_binop `(+):num->num->num` jt `1`))] in
  MP_TAC(ISPECL [`st:byte list`; `ofs:num`; bcv; `tl:num`; `c:num`;
                 `ws:num list`; `ml:num`; `tbl:int64`; s]
    HUF_LOOKUP_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`st:byte list`; pos; `tl:num`] ZSTD_BACK_BOUND) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC (mk_eq(xv,back `tl:num`)) THEN
  ABBREV_TAC (mk_eq(yv,back `ml:num`)) THEN
  ABBREV_TAC (mk_eq(symv,list_mk_icomb "huf_symbol" [`ws:num list`; yv])) THEN
  ABBREV_TAC (mk_eq(nbv,mk_binop `(-):num->num->num` `ml + 1`
                    (list_mk_icomb "EL" [symv; `ws:num list`]))) THEN
  SUBGOAL_THEN goal STRIP_ASSUME_TAC THENL
   [split THEN ONCE_REWRITE_TAC[HUF_DECODE_SUC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;
    ALL_TAC];;

(*** The facts with subtractions, which slow down the arithmetic in the    ***)
(*** simulation of the stores, put together as one assumption             ***)

let HUF_HIDE_SUB_TAC : tactic =
  let numty = `:num` in
  let is_sub_fact tm =
    exists (fun op -> is_binary op tm && type_of(lhand tm) = numty)
           ["="; "<"; "<="] &&
    can (find_term (fun t -> is_binary "-" t && type_of t = numty)) tm &&
    not(exists (fun v -> type_of v = `:armstate`) (frees tm)) in
  fun (asl,w) ->
    let ths,others = partition (fun (_,th) -> is_sub_fact(concl th)) asl in
    if ths = [] then ALL_TAC (asl,w) else
    ASSUME_TAC (end_itlist CONJ (map snd ths)) (others,w);;

(*** The entries of the table read are no longer needed, and are dropped ***)
(*** to save time in the simulation of the stores                       ***)

let HUF_DROP_TABLE_TAC =
  let pat = `read (memory :> bytes8 (word_add tbl a)) s = x` in
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> can (term_match [`tbl:int64`] pat) (concl th));;

let HUF_BODY_MEM_TAC s =
  let jtm j = if j = 0 then `4 * k` else
    mk_binop `(+):num->num->num` `4 * k` (mk_small_numeral j) in
  let step j =
    MP_TAC(ISPECL [`dst:int64`; `ws:num list`; `ml:num`; `st:byte list`;
                   `r:num`; jtm j; jtm(j + 1);
                   mk_var("sym"^string_of_int j,`:num`); s] HUF_MEM_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] in
  step 0 THEN step 1 THEN step 2 THEN step 3;;

let HUF_BODY = prove
 (mk_huf_goal [`k:num`; `ofs:num`; `bc:num`] huf_body
   (mk_abs(`s:armstate`,
           mk_comb(mk_comb(huf_rinv,`n - 4 * (k + 1)`),`s:armstate`))),
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--4) THEN
  HUF_BODY_SYM_TAC 4 0 `bc:num` THEN HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (5--7) THEN HUF_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (8--12) THEN
  HUF_BODY_SYM_TAC 12 1 `nb0 + bc:num` THEN HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (13--15) THEN HUF_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (16--20) THEN
  HUF_BODY_SYM_TAC 20 2 `nb1 + nb0 + bc:num` THEN HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (21--23) THEN HUF_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (24--28) THEN
  HUF_BODY_SYM_TAC 28 3 `nb2 + nb1 + nb0 + bc:num` THEN HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (29--31) THEN HUF_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (32--35) THEN
  PUFF_FINAL_TAC THEN HUF_BODY_MEM_TAC `s35:armstate` THEN
  MAP_EVERY EXISTS_TAC
   [`k + 1`; `ofs:num`; `nb3 + nb2 + nb1 + nb0 + bc:num`] THEN
  REWRITE_TAC[ARITH_RULE `4 * (k + 1) = 4 * k + 4`] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main loop: BIT_reloadDStream, then the body if the stream is not at   *)
(* its start and 4 more bytes are to be decoded. The reload is of whole      *)
(* bytes, so leaves the position as it is, except that it does not go below  *)
(* the start of the stream (where bc can then be more than 7).               *)
(* ------------------------------------------------------------------------- *)

let HUF_RELOAD_WEAKEN_TAC =
  GEN_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `n - 4 * (k + 1)` THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[]];;

let HUF_RELOAD_BODY_TAC ofs' bc' =
  ZSTD_CONTINUE_WITH_TAC HUF_RELOAD_WEAKEN_TAC
   HUF_BODY [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let HUF_RELOAD_TAIL_TAC ofs' bc' =
  ZSTD_CONTINUE_TAC HUF_TAIL
   [ofs',`ofs:num`; `4 * k`,`j:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0; SUB_REFL] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let HUF_RELOAD_SLICE_TAC ofs' s =
  MP_TAC(SPECL [`src:int64`; `LENGTH(st:byte list)`;
                `num_of_bytelist(st:byte list)`; ofs'; s]
     READ_MEMORY_BYTES64_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC;;

let HUF_LOOP = prove
 (mk_huf_goal []
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      mk_comb(mk_comb(huf_rinv,`m:num`),`s:armstate`))))
   huf_post,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `k:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  PUFF_INIT_TAC "s0" THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [(*** ptr >= limitPtr: reload ***)
    SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--5) THEN
    HUF_RELOAD_SLICE_TAC `ofs - bc DIV 8` `s5:armstate` THEN
    ZSTD_STEPS_TAC (6--7) THEN ASM_CASES_TAC `4 * k + 4 <= n` THENL
     [ZSTD_STEPS_TAC [8] THEN
      HUF_RELOAD_BODY_TAC `ofs - bc DIV 8` `bc MOD 8`;
      ZSTD_STEPS_TAC (8--9) THEN
      HUF_RELOAD_TAIL_TAC `ofs - bc DIV 8` `bc MOD 8`];
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [(*** ptr = start: the end of the main loop ***)
    ZSTD_STEPS_TAC (1--6) THEN ASM_CASES_TAC `4 * k < n` THENL
     [ZSTD_STEPS_TAC (7--8) THEN
      ZSTD_CONTINUE_TAC HUF_TLOOP [`4 * k`,`j:num`] THEN
      MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
      REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;
      SUBGOAL_THEN `n = 4 * k` SUBST_ALL_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `bc = 64` THEN ZSTD_RUN_TAC THEN
      PUFF_FINAL_TAC THEN DISJ2_TAC THEN ZSTD_DECIDE_GOAL_TAC];
    ALL_TAC] THEN
  (*** start < ptr < limitPtr: the cautious reload ***)
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [ZSTD_STEPS_TAC (1--11) THEN
    HUF_RELOAD_SLICE_TAC `ofs - bc DIV 8` `s11:armstate` THEN
    ZSTD_STEPS_TAC (12--13) THEN ASM_CASES_TAC `4 * k + 4 <= n` THENL
     [ZSTD_STEPS_TAC [14] THEN
      HUF_RELOAD_BODY_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
      ZSTD_STEPS_TAC [14] THEN
      HUF_RELOAD_TAIL_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`];
    ZSTD_STEPS_TAC (1--13) THEN
    HUF_RELOAD_SLICE_TAC `0` `s13:armstate` THEN
    ZSTD_STEPS_TAC (14--15) THEN HUF_RELOAD_TAIL_TAC `0` `bc - 8 * ofs`]);;

(* ------------------------------------------------------------------------- *)
(* For n <= 3, the single reload before the tail (at 0x2a00, with the        *)
(* pointer in x0), and the start of the decoding, at position r.             *)
(* ------------------------------------------------------------------------- *)

let huf_single = with_memsafe huf_rr huf_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x2a00) /\ read X30 s = returnaddress /\
  read X1 s = word n /\ read X2 s = src /\ read X6 s = tbl /\
  read X10 s = word_add dst (word n) /\ read X11 s = word tl /\
  read X12 s = word_add src (word 8) /\ read X5 s = dst /\
  read X0 s = word_add src (word ofs) /\
  read X4 s = word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read X3 s = word bc /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl) /\
  (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ n <= 3 /\ bc <= 64 /\
  8 * ofs + 64 - bc = r`;;

let HUF_DECODE_0 = prove
 (`!ws ml (st:byte list) q. huf_decode ws ml st q 0 = ([],q,T)`,
  REWRITE_TAC[huf_decode]);;

let READ_MEMORY_BYTES_0 = prove
 (`!(a:int64) s. read (memory :> bytes(a,0)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]);;

let HUF_START_TAC =
  REWRITE_TAC[HUF_DECODE_0; READ_MEMORY_BYTES_0; num_of_bytelist;
              WORD_ADD_0];;

(*** The result for n = 0 ***)

let HUF_N0_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n = 0`)) THEN
  PUFF_FINAL_TAC THEN
  REWRITE_TAC[HUF_DECODE_0; READ_MEMORY_BYTES_0; num_of_bytelist] THEN
  ZSTD_DECIDE_GOAL_TAC;;

let HUF_SINGLE_GOON_TAC th insts =
  ZSTD_CONTINUE_TAC th insts THEN
  MEMSAFE_ELIM_TAC THEN HUF_START_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let HUF_SINGLE = prove
 (mk_huf_goal [`ofs:num`; `bc:num`] huf_single huf_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [(*** ptr >= limitPtr: reload ***)
    SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--5) THEN
    HUF_RELOAD_SLICE_TAC `ofs - bc DIV 8` `s5:armstate` THEN
    ZSTD_STEPS_TAC (6--7) THEN ASM_CASES_TAC `n = 0` THENL
     [ZSTD_RUN_TAC THEN HUF_N0_TAC;
      ZSTD_STEPS_TAC [8] THEN HUF_SINGLE_GOON_TAC HUF_TLOOP
       [`ofs - bc DIV 8`,`ofs:num`; `0`,`j:num`; `bc MOD 8`,`bc:num`]];
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [(*** ptr = start ***)
    ZSTD_STEPS_TAC (1--5) THEN ASM_CASES_TAC `n = 0` THENL
     [ASM_CASES_TAC `bc = 64` THEN ZSTD_RUN_TAC THEN HUF_N0_TAC;
      ZSTD_STEPS_TAC (6--7) THEN HUF_SINGLE_GOON_TAC HUF_TLOOP [`0`,`j:num`]];
    ALL_TAC] THEN
  (*** start < ptr < limitPtr: the cautious reload ***)
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [ZSTD_STEPS_TAC (1--9) THEN
    HUF_RELOAD_SLICE_TAC `ofs - bc DIV 8` `s9:armstate` THEN
    ZSTD_STEPS_TAC (10--11) THEN HUF_SINGLE_GOON_TAC HUF_TAIL
     [`ofs - bc DIV 8`,`ofs:num`; `0`,`j:num`; `bc - 8 * bc DIV 8`,`bc:num`];
    ZSTD_STEPS_TAC (1--12) THEN
    HUF_RELOAD_SLICE_TAC `0` `s12:armstate` THEN
    ZSTD_STEPS_TAC (13--14) THEN HUF_SINGLE_GOON_TAC HUF_TAIL
     [`0`,`ofs:num`; `0`,`j:num`; `bc - 8 * ofs`,`bc:num`]]);;

(* ------------------------------------------------------------------------- *)
(* The result: from huf_decode at the end of the stream to huf_stream.       *)
(* ------------------------------------------------------------------------- *)

let HUF_STREAM_DECODE = prove
 (`!ws ml (st:byte list) r out.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ zstd_end st r
        ==> (huf_stream ws ml st out <=>
             huf_decode ws ml st r (LENGTH out) = (out,0,T))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HUF_STREAM_PARSE] THEN
  ASM_SIMP_TAC[GSYM HUF_DECODE_PARSE] THEN
  ASM_MESON_TAC[ZSTD_END_UNIQUE]);;

let HUF_STREAM_END = prove
 (`!ws ml (st:byte list) out. huf_stream ws ml st out ==> ?r. zstd_end st r`,
  REWRITE_TAC[huf_stream] THEN MESON_TAC[]);;

let HUF_RESULT = prove
 (`!ws ml (st:byte list) r n (x0:int64) mem.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ zstd_end st r /\
        n < 2 EXP 28 /\
        x0 = (if SND(SND(huf_decode ws ml st r n)) /\
                 FST(SND(huf_decode ws ml st r n)) = 0
              then word n else word 18446744073709551596) /\
        (SND(SND(huf_decode ws ml st r n)) /\
         FST(SND(huf_decode ws ml st r n)) = 0
         ==> mem = num_of_bytelist(FST(huf_decode ws ml st r n)))
        ==> (!out. LENGTH out = n /\ huf_stream ws ml st out
                   ==> x0 = word n /\ mem = num_of_bytelist out) /\
            ((!out. LENGTH out = n ==> ~huf_stream ws ml st out)
             ==> zstd_is_error x0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!out. huf_stream ws ml st out <=>
          huf_decode ws ml st r (LENGTH out) = (out,0,T)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC HUF_STREAM_DECODE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `out:byte list` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `LENGTH(out:byte list) = n`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o
      SPEC `FST(huf_decode ws ml (st:byte list) r n)`) THEN
    REWRITE_TAC[HUF_DECODE_LENGTH] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC(`huf_decode ws ml (st:byte list) r n`,`d:byte list#num#bool`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[];
    REWRITE_TAC[zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The start: BIT_initDStream, then the main loop (n > 3) or the single      *)
(* reload (n <= 3). A stream of 8 bytes or more starts with the container    *)
(* holding its last 8 bytes, and a shorter one with it holding its bytes     *)
(* (put together in a switch on the length), with bc counting the missing    *)
(* ones as used; in both cases at the position below the top bit of the last *)
(* byte, which is the end of the stream in the specification. An empty       *)
(* stream, and one whose last byte is 0, are errors.                         *)
(* ------------------------------------------------------------------------- *)

let WORD_PRED_LEMMA = prove
 (`!k. 1 <= k ==> word(k + 18446744073709551615):int64 = word(k - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k + 18446744073709551615 = (k - 1) + 2 EXP 64`
  SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD] THEN
  SUBGOAL_THEN `word(2 EXP 64):int64 = word 0` SUBST1_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC WORD_REDUCE_CONV;
    REWRITE_TAC[WORD_ADD_0]]);;

let HUF_LAST_ADDR = prove
 (`!(a:int64) k.
        1 <= k
        ==> word_add (word_add a (word k)) (word 18446744073709551615) =
            word_add a (word(k - 1))`,
  SIMP_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_PRED_LEMMA]);;

let WORD_CONTAINER_0 = prove
 (`!x. word((x DIV 2 EXP (8 * 0)) MOD 2 EXP 64):int64 = word x`,
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE]);;

(*** The end pointer oend, computed with a conditional select ***)

let HUF_OEND_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `read X10 s5` then
      SUBGOAL_THEN `read X10 s5 = word_add dst (word n)` ASSUME_TAC THENL
       [REWRITE_TAC[th; SUB_0; INT_SUB_RZERO] THEN
        SUBGOAL_THEN `ival(word n:int64) = &n` SUBST1_TAC THENL
         [MATCH_MP_TAC(INST_TYPE [`:64`,`:N`] IVAL_WORD_SMALL) THEN
          REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMPLE_ARITH_TAC;
          ALL_TAC] THEN
        ASM_CASES_TAC `n = 0` THEN
        ASM_REWRITE_TAC[INT_OF_NUM_LT; LT; WORD_ADD_0];
        ALL_TAC]
    else NO_TAC);;

(*** The last byte b of the stream, with vb = val b ***)

let HUF_INIT_TAC =
  ZSTD_STEPS_TAC (6--9) THEN
  SUBGOAL_THEN `1 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`src:int64`; `st:byte list`; `LENGTH(st:byte list) - 1`;
                 `s9:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_PRED_LEMMA] THEN DISCH_TAC THEN
  ABBREV_TAC `b = EL (LENGTH(st:byte list) - 1) st` THEN
  ZSTD_STEPS_TAC [10] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HUF_LAST_ADDR
    (ASSUME `1 <= LENGTH(st:byte list)`)]) THEN
  ABBREV_TAC `vb = val(b:byte)` THEN
  SUBGOAL_THEN `vb < 256` ASSUME_TAC THENL
   [EXPAND_TAC "vb" THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC];;

let HUF_VB_FACTS_TAC =
  SUBGOAL_THEN `1 <= bitsize vb /\ bitsize vb <= 8` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                BITSIZE_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The errors, when there is no end of the stream ***)

let HUF_NO_STREAM_TAC tac =
  SUBGOAL_THEN `!out. ~huf_stream ws ml (st:byte list) out` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HUF_STREAM_END) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN GEN_TAC THEN tac;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV;;

let HUF_LAST0_TAC =
  MP_TAC(SPECL [`st:byte list`; `r:num`] ZSTD_END_LAST) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SIMPLE_ARITH_TAC;
    ASM_REWRITE_TAC[]];;

(*** Going on with HUF_SINGLE or HUF_LOOP, at the end of the stream ***)

let HUF_LENGTH_FACTS_TAC (tac:thm list -> tactic) : tactic =
  W(fun (asl,w) ->
    let ths = filter (fun th ->
      match concl th with
        Comb(Comb(Const("=",_),l),r) ->
          l = `LENGTH(st:byte list)` && is_numeral r
      | _ -> false) (map snd asl) in
    tac ths);;

let HUF_TOP_WEAKEN_TAC =
  X_GEN_TAC `s':armstate` THEN REWRITE_TAC[puff_memsafe] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ m ==> a /\ b /\ m`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_ASSUM ACCEPT_TAC ORELSE
    HUF_LENGTH_FACTS_TAC (fun ths ->
      FIRST_ASSUM(MP_TAC o check (is_exists o concl)) THEN
      REWRITE_TAC ths)] THEN
  MATCH_MP_TAC HUF_RESULT THEN
  EXISTS_TAC `8 * (LENGTH(st:byte list) - 1) + bitsize vb - 1` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MP_TAC(SPECL [`st:byte list`;
                `8 * (LENGTH(st:byte list) - 1) + bitsize vb - 1`]
     ZSTD_END_LAST) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SIMPLE_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ASSUME `EL (LENGTH(st:byte list) - 1) st = b`;
                ASSUME `val(b:byte) = vb`; ASSUME `~(vb = 0)`]];;

let HUF_TOP_GOON_TAC pre th insts =
  ZSTD_CONTINUE_WITH_TAC HUF_TOP_WEAKEN_TAC th
   ([`word_add dtable (word 4):int64`,`tbl:int64`;
     `8 * (LENGTH(st:byte list) - 1) + bitsize vb - 1`,`r:num`] @ insts) THEN
  pre THEN MEMSAFE_ELIM_TAC THEN
  ASM_REWRITE_TAC[WORD_ADD_0; WORD_CONTAINER_0; HUF_DECODE_0; MULT_CLAUSES;
                  READ_MEMORY_BYTES_0; num_of_bytelist] THEN
  REPEAT CONJ_TAC THEN
  (ZSTD_ARITH_TAC ORELSE (AP_TERM_TAC THEN ZSTD_ARITH_TAC));;

let HUF_SHIFT_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HUF_SHIFT_WORD
    (CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`))]);;

let HUF_TOP_SINGLE_TAC ofs bc =
  HUF_TOP_GOON_TAC ALL_TAC HUF_SINGLE [ofs,`ofs:num`; bc,`bc:num`];;

let HUF_TOP_LOOP_TAC ofs bc =
  HUF_SHIFT_TAC THEN
  HUF_TOP_GOON_TAC
   (EXISTS_TAC `n - 4 * 0` THEN MAP_EVERY EXISTS_TAC [`0`; ofs; bc])
   HUF_LOOP [];;

(*** A stream of 8 bytes or more whose last byte is not 0 ***)

let HUF_BIG_TAC =
  HUF_VB_FACTS_TAC THEN ZSTD_STEPS_TAC (11--21) THEN
  HUF_RELOAD_SLICE_TAC `LENGTH(st:byte list) - 8` `s21:armstate` THEN
  ZSTD_STEPS_TAC (22--23) THEN ASM_CASES_TAC `n <= 3` THEN
  ZSTD_STEPS_TAC [24] THENL
   [ZSTD_STEPS_TAC [25] THEN
    HUF_TOP_SINGLE_TAC `LENGTH(st:byte list) - 8` `32 - bitsize vb - 23`;
    ZSTD_STEPS_TAC (25--28) THEN
    HUF_TOP_LOOP_TAC `LENGTH(st:byte list) - 8` `32 - bitsize vb - 23`];;

(*** A stream of k bytes, 1 <= k <= 7 ***)

let HUF_SMALL_TAC k =
  let numt = mk_small_numeral in
  let els = map (fun i -> list_mk_icomb "EL" [numt i; `st:byte list`])
                (0--(k-1)) in
  let sum = itlist (fun e acc ->
              mk_binop `(+):num->num->num` (mk_icomb(`val:byte->num`,e))
                (mk_binop `( * ):num->num->num` `256` acc)) els `0` in
  let lst = mk_list(els,`:byte`) in
  let bc = mk_binop `(-):num->num->num`
             (mk_binop `(+):num->num->num` `32 - bitsize vb`
                (numt(8 * (8 - k)))) `23` in
  let memfact i =
    MP_TAC(ISPECL [`src:int64`; `st:byte list`; numt i; `s10:armstate`]
      READ_MEMORY_BYTES8_BYTELIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] in
  let range = ARITH_RULE(mk_eq(mk_binop `(<):num->num->bool` `i:num` (numt k),
                list_mk_disj(map (fun j -> mk_eq(`i:num`,numt j))
                                 (0--(k-1))))) in
  MAP_EVERY memfact (0--(k-1)) THEN
  SUBGOAL_THEN (mk_eq(`num_of_bytelist(st:byte list)`,sum)) ASSUME_TAC THENL
   [SUBGOAL_THEN (mk_eq(`st:byte list`,lst))
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] THEN
                 REWRITE_TAC[num_of_bytelist]) THEN
    REWRITE_TAC[LIST_EQ; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[range] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `vb = 0` THENL
   [ZSTD_RUN_TAC THEN PUFF_FINAL_TAC THEN HUF_NO_STREAM_TAC HUF_LAST0_TAC;
    HUF_VB_FACTS_TAC THEN ASM_CASES_TAC `n <= 3` THENL
     [ZSTD_SIM_UNTIL_TAC [0x2a00] THEN HUF_TOP_SINGLE_TAC `0` bc;
      ZSTD_SIM_UNTIL_TAC [0x2990] THEN HUF_TOP_LOOP_TAC `0` bc]];;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For the stream st of the n bytes at src, and the        *)
(* decoding table (built by HUF_readDTableX1_wksp) for the weights ws, with  *)
(* codes of at most ml bits and a table of tl bits, at DTable + 4, its       *)
(* header holding tl at DTable + 2: if st is the Huffman-coded stream of     *)
(* the n bytes out, the result is n, with out at dst, and if there is no     *)
(* such out, it is an error code. The loads are from the stream and the      *)
(* table, and the stores to the n bytes at dst.                              *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS1X1_USINGDTABLE_CORRECT = prove
 (`!pc returnaddress dst n src (st:byte list) dtable ws ml tl e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     huf_complete ws ml /\ LENGTH ws <= 256 /\
     ml <= tl /\ 1 <= tl /\ tl <= 12 /\ n < 2 EXP 28 /\
     8 <= val src /\ val src + LENGTH st + 8 < 2 EXP 64 /\
     LENGTH st < 2 EXP 60 /\ val dst + n < 2 EXP 64 /\
     nonoverlapping (dst,n) (src,LENGTH st) /\
     nonoverlapping (dst,n) (word_add dtable (word 4),2 * 2 EXP tl) /\
     nonoverlapping (dst,n) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x2850) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; word n; src; word(LENGTH st); dtable] s /\
               read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
               read (memory :> bytes8(word_add dtable (word 2))) s = word tl /\
               read (memory :> bytes(word_add dtable (word 4),2 * 2 EXP tl))
                    s =
               num_of_bytelist(huf_dtable ws ml tl) /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!out. LENGTH out = n /\ huf_stream ws ml st out
                      ==> read X0 s = word n /\
                          read (memory :> bytes(dst,n)) s =
                          num_of_bytelist out) /\
               ((!out. LENGTH out = n ==> ~huf_stream ws ml st out)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH st; word_add dtable (word 2),1;
                       word_add dtable (word 4),2 * 2 EXP tl]
                      [dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(dst,n)])`,
  ZSTD_INTRO_TAC THEN REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `LENGTH(st:byte list) = 0` THENL
   [ZSTD_RUN_TAC THEN PUFF_FINAL_TAC THEN
    HUF_NO_STREAM_TAC(REWRITE_TAC[zstd_end] THEN ASM_MESON_TAC[LENGTH_EQ_NIL]);
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--5) THEN HUF_OEND_TAC THEN HUF_INIT_TAC THEN
  ASM_CASES_TAC `8 <= LENGTH(st:byte list)` THENL
   [ASM_CASES_TAC `vb = 0` THENL
     [ZSTD_RUN_TAC THEN PUFF_FINAL_TAC THEN HUF_NO_STREAM_TAC HUF_LAST0_TAC;
      HUF_BIG_TAC];
    SUBGOAL_THEN
     `LENGTH(st:byte list) = 1 \/ LENGTH st = 2 \/ LENGTH st = 3 \/
      LENGTH st = 4 \/ LENGTH st = 5 \/ LENGTH st = 6 \/ LENGTH st = 7`
    (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [SIMPLE_ARITH_TAC; HUF_SMALL_TAC 1; HUF_SMALL_TAC 2; HUF_SMALL_TAC 3;
      HUF_SMALL_TAC 4; HUF_SMALL_TAC 5; HUF_SMALL_TAC 6; HUF_SMALL_TAC 7]]);;

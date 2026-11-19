(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The fast decoding of Huffman-coded literals in four streams with          *)
(* double-symbol tables in zstd, compiled by gcc 12 at -O2 for AArch64:      *)
(* HUF_decompress4X2_usingDTable_internal_fast_c_loop, which does 5 lookups  *)
(* of each stream per iteration, of one or two symbols each.                 *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode4x1_fast_gcc12_O2.ml";;
needs "arm/proofs/zstd_huf_read_dtable_x2_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress4X2_usingDTable_internal_fast_c_loop at 0x1f60 takes its    *)
(* arguments at args as the single-symbol loop does: for each of the four    *)
(* streams k of the block blk at ilowest a pointer ip[k] = ilowest + u_k, an *)
(* output pointer op[k] and a bit container bits[k] (the 8 bytes from ip[k]  *)
(* with bit 0 set, shifted left by the s_k bits used, so that the stream is  *)
(* at position p_k = 8 * u_k + 64 - s_k in blk), then the table dt of 2^11   *)
(* entries of 4 bytes for the code of the weights ws (huf_dtable2 ws ml 11), *)
(* ilowest and oend. The output of stream k is the sz_k bytes from op_k, up  *)
(* to op_(k + 1), and oend for the last. A lookup takes the entry            *)
(* (huf_dentry2) of the top 11 bits of the container, of one or two symbols, *)
(* stores its two symbol bytes with one 16-bit store and moves the output on *)
(* by its number of symbols. Each iteration does 5 lookups of each stream    *)
(* and then reloads each container, in rounds: a round has at most m         *)
(* iterations, m the smallest of the number of 7-byte steps of the first     *)
(* stream back to ilowest and of the 10-byte steps of the room left in each  *)
(* output, and goes on while the output of the last stream is below olimit,  *)
(* its position after 5 * m bytes. Between rounds the code does again some   *)
(* stores of the last two streams in the last iteration (at the same         *)
(* addresses, with the same values), and a round starts only if m is not 0   *)
(* and the pointers are in order (ip[0] <= ip[1] <= ip[2] <= ip[3]). The     *)
(* arguments are copied to the frame at the entry and back at the return,    *)
(* and w18 tells the exit whether the registers must be copied to the frame  *)
(* first, after a round. The function returns the arguments after j_k        *)
(* symbols of each stream k, for some j_k <= sz_k, with the first j_k bytes  *)
(* of each output what huf_decode ws ml blk p_k decodes                      *)
(* (HUF_DECOMPRESS4X2_FAST_C_LOOP_CORRECT).                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The double-symbol decoding: the bits below a position split, the entry of *)
(* the table for the bits below the position of a stream, and a lookup as    *)
(* one or two steps of huf_decode (HUF_DECODE_X2_STEP).                      *)
(* ------------------------------------------------------------------------- *)

(*** The k bits below position p, as the k - n below p - n and the n ***)
(*** bits above them                                                 ***)

let DIV_SPLIT_LEMMA = prove
 (`!a b c x y. ~(x = 0) /\ ~(c = 0)
               ==> ((c * a) * (b + x * y)) DIV (x * c) =
                   (a * b) DIV x + a * y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c * a) * (b + x * y) = c * ((a * y) * x + a * b)` SUBST1_TAC
  THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT2; DIV_MULT_ADD] THEN ARITH_TAC);;

let ZSTD_BACK_SPLIT = prove
 (`!st p k n.
        n <= k /\ n <= p
        ==> zstd_back st p k =
            zstd_back st (p - n) (k - n) +
            2 EXP (k - n) * zstd_bits st (p - n) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zstd_back] THEN
  SUBGOAL_THEN `p = (p - n) + n` (fun th -> GEN_REWRITE_TAC
    (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ZSTD_BITS_ADD; ADD_CLAUSES] THEN
  SUBGOAL_THEN `2 EXP k = 2 EXP n * 2 EXP (k - n)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD] THEN
  MATCH_MP_TAC DIV_SPLIT_LEMMA THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]);;

let ZSTD_BACK_MOD = prove
 (`!st p k n.
        n <= k
        ==> zstd_back st p k MOD 2 EXP (k - n) = zstd_back st (p - n) (k - n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n <= p` THENL
   [ASM_SIMP_TAC[ZSTD_BACK_SPLIT] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[ZSTD_BACK_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN `p - n = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[zstd_back; zstd_bits; MULT_CLAUSES; EXP; DIV_0] THEN
  SUBGOAL_THEN `2 EXP k = 2 EXP p * 2 EXP (k - n) * 2 EXP (n - p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[MOD_MULT]);;
let HUF_SYMBOL_TOPBITS = prove
 (`!ws ml y z r.
        huf_complete ws ml /\ y < 2 EXP ml /\ z < 2 EXP ml /\ r <= ml /\
        y DIV 2 EXP (ml - r) = z DIV 2 EXP (ml - r) /\
        (ml + 1) - EL (huf_symbol ws y) ws <= r
        ==> huf_symbol ws z = huf_symbol ws y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HUF_SYMBOL_PREFIX THEN
  EXISTS_TAC `ml:num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ws:num list`; `y:num`] HUF_SYMBOL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[huf_complete]; ALL_TAC] THEN
  REWRITE_TAC[huf_present; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EL (huf_symbol ws y) ws <= ml` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[huf_complete; huf_present; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EL (huf_symbol ws y) ws - 1 =
    (ml - r) + (r - ((ml + 1) - EL (huf_symbol ws y) ws))`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EXP_ADD; GSYM DIV_DIV]);;

(*** The entry of the double-symbol table at the tl bits below position ***)
(*** p: the symbol decoded there, and the next one if its code fits     ***)

let HUF_DENTRY2_BACK = prove
 (`!ws ml tl st p.
     huf_complete ws ml /\ ml <= tl
     ==> huf_dentry2 ws ml tl (zstd_back st p tl) =
         let s1 = huf_symbol ws (zstd_back st p ml) in
         let nb1 = (ml + 1) - EL s1 ws in
         let s2 = huf_symbol ws (zstd_back st (p - nb1) ml) in
         let nb2 = (ml + 1) - EL s2 ws in
         if nb2 <= tl - nb1 then [s1; s2; nb1 + nb2; 2] else [s1; 0; nb1; 1]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_dentry2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC[ZSTD_BACK_DIV] THEN
  ABBREV_TAC `s1 = huf_symbol ws (zstd_back st p ml)` THEN
  ABBREV_TAC `nb1 = (ml + 1) - EL s1 ws` THEN
  SUBGOAL_THEN `1 <= nb1 /\ nb1 <= ml` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `zstd_back st p ml`] HUF_SYMBOL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[huf_complete; ZSTD_BACK_BOUND]; ALL_TAC] THEN
    ASM_REWRITE_TAC[huf_present; IN_ELIM_THM] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[huf_complete; huf_present; IN_ELIM_THM]) THEN
    SUBGOAL_THEN `EL s1 ws <= ml` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(ml + 1) - EL s1 ws = nb1`; `~(EL s1 ws = 0)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `zstd_back st p tl MOD 2 EXP (tl - nb1) =
    zstd_back st (p - nb1) (tl - nb1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ZSTD_BACK_MOD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = tl - nb1` THEN
  ABBREV_TAC `a = zstd_back st (p - nb1) r` THEN
  ABBREV_TAC `z = zstd_back st (p - nb1) ml` THEN
  ASM_CASES_TAC `ml <= r` THENL
   [SUBGOAL_THEN `(a * 2 EXP ml) DIV 2 EXP r = z`
     (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `2 EXP r = 2 EXP ml * 2 EXP (r - ml)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY EXPAND_TAC ["a"; "z"] THEN ASM_SIMP_TAC[ZSTD_BACK_DIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a * 2 EXP ml) DIV 2 EXP r = a * 2 EXP (ml - r)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `2 EXP ml = 2 EXP r * 2 EXP (ml - r)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MULT_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [MULT_SYM] THEN
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < 2 EXP r /\ z < 2 EXP ml /\ r <= ml /\
                z DIV 2 EXP (ml - r) = a`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "z"] THEN REWRITE_TAC[ZSTD_BACK_BOUND] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC ZSTD_BACK_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a * 2 EXP (ml - r) < 2 EXP ml` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP ml = 2 EXP r * 2 EXP (ml - r)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a * 2 EXP (ml - r)) DIV 2 EXP (ml - r) = a` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `y = a * 2 EXP (ml - r)` THEN
  ASM_CASES_TAC `(ml + 1) - EL (huf_symbol ws y) ws <= r` THENL
   [MP_TAC(SPECL [`ws:num list`; `ml:num`; `y:num`; `z:num`; `r:num`]
      HUF_SYMBOL_TOPBITS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `z:num`; `y:num`; `r:num`]
    HUF_SYMBOL_TOPBITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((ml + 1) - EL (huf_symbol ws y) ws <= r)` THEN
  ASM_REWRITE_TAC[]);;

(*** A lookup in the double-symbol table after k symbols decoded: one ***)
(*** or two more symbols, and the bits of their codes used            ***)

let HUF_DECODE_X2_STEP = prove
 (`!ws ml tl st q k.
     huf_complete ws ml /\ ml <= tl
     ==> let p = FST(SND(huf_decode ws ml st q k)) in
         let e = huf_dentry2 ws ml tl (zstd_back st p tl) in
         (EL 3 e = 1 \/ EL 3 e = 2) /\
         FST(huf_decode ws ml st q (k + EL 3 e)) =
         APPEND (FST(huf_decode ws ml st q k))
                (if EL 3 e = 2 then [word(EL 0 e); word(EL 1 e)]
                 else [word(EL 0 e)]) /\
         FST(SND(huf_decode ws ml st q (k + EL 3 e))) = p - EL 2 e /\
         (SND(SND(huf_decode ws ml st q (k + EL 3 e))) <=>
          SND(SND(huf_decode ws ml st q k)) /\ EL 2 e <= p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[HUF_DENTRY2_BACK] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `p = FST(SND(huf_decode ws ml st q k))` THEN
  COND_CASES_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THENL
   [ABBREV_TAC `s1 = huf_symbol ws (zstd_back st p ml)` THEN
    ABBREV_TAC `nb1 = (ml + 1) - EL s1 ws` THEN
    ABBREV_TAC `s2 = huf_symbol ws (zstd_back st (p - nb1) ml)` THEN
    ABBREV_TAC `nb2 = (ml + 1) - EL s2 ws` THEN
    REWRITE_TAC[ARITH_RULE `k + 2 = (k + 1) + 1`] THEN
    REWRITE_TAC[HUF_DECODE_SUC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN AP_TERM_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[HUF_DECODE_SUC]]);;

(* ------------------------------------------------------------------------- *)
(* The entries of the table and their bytes in memory, a lookup of the fast  *)
(* loop as steps of huf_decode (HUF_DECODE_FAST2_STEP) and the 16-bit store  *)
(* of its symbols after the bytes decoded before (READ_MEMORY_X2_STORE).     *)
(* ------------------------------------------------------------------------- *)

(*** The entries of the double-symbol table: the two symbols are bytes,  ***)
(*** the number of bits from 1 to tl and the number of symbols 1 or 2    ***)

let HUF_DENTRY2_BOUNDS = prove
 (`!ws ml tl x.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\ x < 2 EXP tl
        ==> EL 0 (huf_dentry2 ws ml tl x) < 256 /\
            EL 1 (huf_dentry2 ws ml tl x) < 256 /\
            1 <= EL 2 (huf_dentry2 ws ml tl x) /\
            EL 2 (huf_dentry2 ws ml tl x) <= tl /\
            (EL 3 (huf_dentry2 ws ml tl x) = 1 \/
             EL 3 (huf_dentry2 ws ml tl x) = 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[huf_dentry2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `y1 = x DIV 2 EXP (tl - ml)` THEN
  SUBGOAL_THEN `y1 < 2 EXP ml` ASSUME_TAC THENL
   [EXPAND_TAC "y1" THEN MATCH_MP_TAC DIV_EXP_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `y1:num`] HUF_SYMBOL_BOUND) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `y1:num`] HUF_NBITS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `nb1 = (ml + 1) - EL (huf_symbol ws y1) ws` THEN
  ABBREV_TAC `r = tl - nb1` THEN
  ABBREV_TAC `y2 = ((x MOD 2 EXP r) * 2 EXP ml) DIV 2 EXP r` THEN
  SUBGOAL_THEN `y2 < 2 EXP ml` ASSUME_TAC THENL
   [EXPAND_TAC "y2" THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[LT_MULT_LCANCEL] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ; MOD_LT_EQ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `y2:num`] HUF_SYMBOL_BOUND) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `y2:num`] HUF_NBITS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC [`tl - nb1 = r`; `ml <= tl`; `nb1 <= ml`] THEN
  ASM_ARITH_TAC);;

(*** The bytes of the entry x in memory, and its first two bytes as one ***)
(*** 16-bit word                                                         ***)

let HUF_DTABLE2_READ = prove
 (`!ws ml tl (tbl:int64) x s.
        x < 2 EXP tl /\
        read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
        num_of_bytelist (huf_dtable2 ws ml tl)
        ==> read (memory :> bytes8 (word_add tbl (word (4 * x)))) s =
            word(EL 0 (huf_dentry2 ws ml tl x)) /\
            read (memory :> bytes8 (word_add tbl (word (4 * x + 1)))) s =
            word(EL 1 (huf_dentry2 ws ml tl x)) /\
            read (memory :> bytes8 (word_add tbl (word (4 * x + 2)))) s =
            word(EL 2 (huf_dentry2 ws ml tl x)) /\
            read (memory :> bytes8 (word_add tbl (word (4 * x + 3)))) s =
            word(EL 3 (huf_dentry2 ws ml tl x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. k < 4
        ==> read (memory :> bytes8 (word_add tbl (word (4 * x + k)))) s =
            word(EL k (huf_dentry2 ws ml tl x))`
  (fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
             MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th) THEN
             CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
             SIMP_TAC[]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tbl:int64`; `huf_dtable2 ws ml tl`; `4 * x + k`;
                 `s:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_HUF_DTABLE2] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[HUF_DTABLE2_EL]);;

let HUF_DTABLE2_READ16 = prove
 (`!ws ml tl (tbl:int64) x s.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\
        x < 2 EXP tl /\
        read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
        num_of_bytelist (huf_dtable2 ws ml tl)
        ==> read (memory :> bytes16 (word_add tbl (word (4 * x)))) s =
            word(EL 0 (huf_dentry2 ws ml tl x) +
                 256 * EL 1 (huf_dentry2 ws ml tl x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; `x:num`;
                `s:armstate`] HUF_DTABLE2_READ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `x:num`]
    HUF_DENTRY2_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC WORD_JOIN_BYTES THEN ASM_REWRITE_TAC[]);;

(*** One or two more symbols decoded by a lookup of the double-symbol ***)
(*** table at the position 8 * u + 64 - x                             ***)

let HUF_DECODE_FAST2_STEP = prove
 (`!ws ml (blk:byte list) p0 j u x.
     huf_complete ws ml /\ ml <= 11 /\
     FST(SND(huf_decode ws ml blk p0 j)) = 8 * u + 64 - x /\
     SND(SND(huf_decode ws ml blk p0 j)) /\
     x + EL 2 (huf_dentry2 ws ml 11 (zstd_back blk (8 * u + 64 - x) 11))
     <= 64
     ==> let e = huf_dentry2 ws ml 11 (zstd_back blk (8 * u + 64 - x) 11) in
         FST(huf_decode ws ml blk p0 (j + EL 3 e)) =
         APPEND (FST(huf_decode ws ml blk p0 j))
                (if EL 3 e = 2 then [word(EL 0 e); word(EL 1 e)]
                 else [word(EL 0 e)]) /\
         FST(SND(huf_decode ws ml blk p0 (j + EL 3 e))) =
         8 * u + 64 - (x + EL 2 e) /\
         SND(SND(huf_decode ws ml blk p0 (j + EL 3 e)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; `blk:byte list`; `p0:num`;
                `j:num`] HUF_DECODE_X2_STEP) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC
   `e = huf_dentry2 ws ml 11 (zstd_back blk (8 * u + 64 - x) 11)` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(*** A 16-bit store of the two symbols of an entry after the bytes l ***)
(*** stored from a, of which the first len are kept                   ***)

let READ_MEMORY_X2_STORE = prove
 (`!a:int64 (l:byte list) b1 b2 len s:armstate.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        read (memory :> bytes16 (word_add a (word(LENGTH l)))) s =
        word(b1 + 256 * b2) /\
        b1 < 256 /\ b2 < 256 /\ (len = 1 \/ len = 2)
        ==> read (memory :> bytes(a,LENGTH l + len)) s =
            num_of_bytelist(APPEND l (if len = 2 then [word b1; word b2]
                                      else [word b1]))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `read (bytes(word_add a (word(LENGTH(l:byte list))),2)) (read memory s) =
    b1 + 256 * b2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_READ_MEMORY_BYTES16; VAL_WORD; DIMINDEX_16] THEN
    MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`word_add a (word(LENGTH(l:byte list))):int64`; `2`; `1`;
                   `read memory s`] READ_BYTES_MOD) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8;
                    ADD_CLAUSES; MULT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `b2:num` THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8;
                    ADD_CLAUSES; MULT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* The simulation, the regions, the hypotheses and the states of the pieces: *)
(* the head of the body at 0x20a8, in a round with m iterations left and     *)
(* olimit = op3 + L, and the head of a round at 0x2008 and the exit at       *)
(* 0x2440.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*** HUF_decompress4X2_usingDTable_internal_fast_c_loop at 0x1f60 ***)

let FL2_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc [0x1f60,0x24a4];;

(*** Simulation, as ZSTD_STEP_TAC, but normalizing small words only in ***)
(*** the values that the step has changed                               ***)

let FL2_STEP_TAC n =
  let flags = [`NF`; `ZF`; `CF`; `VF`; `PC`; `events`] in
  let reads s asl = mapfilter (fun (_,th) ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
        when s' = s -> (c,v)
    | _ -> fail()) asl in
  let evc = `events` in
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),(Const(_,_) as c)),
                                    s')),t)
          when s' = s && not(c = evc) -> can (find_term is_cond) t
      | _ -> false) asl in
  fun (asl0,w0 as gl) ->
    let old = reads (rand w0) asl0 in
    (ARM_STEPS_TAC FL2_EXEC [n] THEN
     (fun (asl,w as gl) ->
        let s = rand w in
        let conv = ZSTD_SMALL_WORD_CONV asl in
        let rule th =
          match concl th with
            Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
              when s' = s && not(mem c flags) && not(mem (c,v) old) ->
                CONV_RULE (RAND_CONV
                  (REWRITE_CONV[WORD_ADD_ASSOC_NUM] THENC conv)) th
          | _ -> th in
        RULE_ASSUM_TAC rule gl) THEN
     (fun gl -> if conditional gl then
                  (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                   TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                     WORD_CMP_64_SFLAGS) THEN
                   TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                   PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                   TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
                else ALL_TAC gl)) gl;;

let FL2_STEPS_TAC ns = MAP_EVERY FL2_STEP_TAC ns;;

(*** The regions: the input, the table of 2^11 entries of 4 bytes, the  ***)
(*** arguments, the frame of 320 bytes and the outputs of the streams,  ***)
(*** stream k having szk bytes from op_k, which follow each other up to ***)
(*** oend                                                               ***)

let fl2_rr =
 `[ilowest,LENGTH(blk:byte list); dt,8192; args,120;
   word_sub stackpointer (word 320),320]:(int64#num)list`
and fl2_wr =
 `[op0,sz0; op1,sz1; op2,sz2; op3,sz3; args,96;
   word_sub stackpointer (word 320),320]:(int64#num)list`;;

let fl2_regions =
 [`ilowest:int64`,`LENGTH(blk:byte list)`; `dt:int64`,`8192`;
  `args:int64`,`152`; `word_sub stackpointer (word 320):int64`,`320`;
  `word pc:int64`,`32000`];;

let fl2_nonover =
  let ops = map (fun k -> mk_var("op"^string_of_int k,`:int64`),
                          mk_var("sz"^string_of_int k,`:num`)) [0;1;2;3] in
  let mk (a,n) (b,m) =
    list_mk_icomb "nonoverlapping" [mk_pair(a,n); mk_pair(b,m)] in
  let rec pairs l = match l with
      [] -> [] | x::t -> map (fun y -> (x,y)) t @ pairs t in
  map (fun (x,y) -> mk x y) (pairs (ops @ fl2_regions));;

let fl2_hyps = list_mk_conj
 ([`aligned 4096 (word pc:int64)`; `pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml`; `LENGTH(ws:num list) <= 256`; `1 <= ml`;
   `ml <= 11`; `val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`;
   `word_add op0 (word sz0) = op1:int64`;
   `word_add op1 (word sz1) = op2:int64`;
   `word_add op2 (word sz2) = op3:int64`;
   `word_add op3 (word sz3) = oend:int64`;
   `val(op0:int64) + sz0 + sz1 + sz2 + sz3 < 2 EXP 64`] @
  fl2_nonover);;

let fl2_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `args:int64`;
  `blk:byte list`; `ilowest:int64`; `dt:int64`; `oend:int64`;
  `op0:int64`; `op1:int64`; `op2:int64`; `op3:int64`;
  `sz0:num`; `sz1:num`; `sz2:num`; `sz3:num`;
  `p0:num`; `p1:num`; `p2:num`; `p3:num`; `ws:num list`; `ml:num`;
  `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`; `x23:int64`;
  `x24:int64`; `x25:int64`; `x26:int64`; `x27:int64`; `x28:int64`;
  `x29:int64`; `e:uarch_event list`];;

(*** The state of stream k with jk symbols decoded and m iterations left ***)
(*** in the current round: its pointer, output pointer and container in  ***)
(*** the registers given, the bytes decoded and the position             ***)

let fl2_jv k = mk_var("j"^string_of_int k,`:num`);;

let fl2_dec k =
  list_mk_icomb "huf_decode"
   [`ws:num list`; `ml:num`; `blk:byte list`;
    mk_var("p"^string_of_int k,`:num`); fl2_jv k];;

let fl2_stream_core k =
  let n = string_of_int k in
  let u = mk_var("u"^n,`:num`) and sk = mk_var("s"^n,`:num`)
  and op = mk_var("op"^n,`:int64`) in
  subst [u,`u:num`; sk,`sk:num`; op,`op:int64`; fl2_jv k,`j:num`;
         fl2_dec k,`dec:byte list#num#bool`]
   `read (memory :> bytes(op,j)) s = num_of_bytelist(FST dec) /\
    FST(SND dec) = 8 * u + 64 - sk /\ SND(SND dec) /\
    sk <= 8 /\ u + 8 <= LENGTH(blk:byte list)`;;

let fl2_stream k (ipr,opr,cr) =
  let n = string_of_int k in
  let u = mk_var("u"^n,`:num`) and sk = mk_var("s"^n,`:num`)
  and op = mk_var("op"^n,`:int64`) and d = mk_var("sz"^n,`:num`) in
  let t = subst [u,`u:num`; op,`op:int64`; fl2_jv k,`j:num`; d,`d:num`;
                 fl_cont u sk,`c:int64`; fl2_stream_core k,`core:bool`]
   `read IPR (s:armstate) = word_add (ilowest:int64) (word u) /\
    read OPR s = word_add (op:int64) (word j) /\
    read CR s = (c:int64) /\ core /\
    7 * m <= u /\ j + 10 * m <= d` in
  subst [ipr,`IPR:(armstate,int64)component`;
         opr,`OPR:(armstate,int64)component`;
         cr,`CR:(armstate,int64)component`] t;;

let fl2_streams =
  [`X25`,`X8`,`X1`; `X23`,`X7`,`X3`; `X24`,`X6`,`X2`; `X28`,`X5`,`X26`];;

(*** The frame of 320 bytes below the stack pointer ***)

let fl2_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
             SP] ,,
  MAYCHANGE [memory :> bytes(op0,sz0); memory :> bytes(op1,sz1);
             memory :> bytes(op2,sz2); memory :> bytes(op3,sz3);
             memory :> bytes(args,96);
             memory :> bytes(word_sub stackpointer (word 320),320)]`;;

let mk_fl2_goal_hyps hyps extra pre post =
  let tm = mk_imp(list_mk_conj(fl2_hyps :: hyps),
                  list_mk_icomb "ensures" [`arm`; pre; post; fl2_frame]) in
  let vs = fl2_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fl2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let mk_fl2_goal = mk_fl2_goal_hyps [];;

(*** The frame: the registers saved, the pointers kept and the ends of the ***)
(*** outputs of the streams (the first output pointers of the next ones); ***)
(*** in the body also the pointers to the copies of the output pointers   ***)
(*** and to the ends, which the head of a round stores at [120] and [128] ***)

let fl2_spk k =
  let sp = `word_sub stackpointer (word 320):int64` in
  if k = 0 then sp
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,sp),
               mk_comb(`word:num->int64`,mk_small_numeral k));;

let fl2_saved =
  [0,`x29:int64`; 8,`returnaddress:int64`; 16,`x19:int64`; 24,`x20:int64`;
   32,`x21:int64`; 40,`x22:int64`; 48,`x23:int64`; 56,`x24:int64`;
   64,`x25:int64`; 72,`x26:int64`; 80,`x27:int64`; 88,`x28:int64`];;

let fl2_kept =
  [136,`ilowest:int64`;
   144,`word_add args (word 64):int64`; 152,`word_add args (word 32):int64`;
   160,`args:int64`; 168,fl2_spk 288; 176,fl2_spk 256; 184,fl2_spk 192;
   224,`op1:int64`; 232,`op2:int64`; 240,`op3:int64`; 248,`oend:int64`]
and fl2_body_kept = [120,fl2_spk 192; 128,fl2_spk 224];;

let fl2_stack_fact (k,v) =
  subst [fl2_spk k,`a:int64`; v,`v:int64`]
    `read (memory :> bytes64 a) s = (v:int64)`;;

let fl2_frame_facts = list_mk_conj
 (`read SP s = word_sub stackpointer (word 320)` ::
  mk_eq(`read X29 s`,fl2_spk 0) ::
  map fl2_stack_fact (fl2_saved @ fl2_kept));;

let fl2_common = list_mk_conj
 [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
   read X0 s = dt /\
   read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
   num_of_bytelist blk /\
   read (memory :> bytes(dt,8192)) s = num_of_bytelist(huf_dtable2 ws ml 11)`;
  fl2_frame_facts];;

let fl2_uvars =
  [`u0:num`; `u1:num`; `u2:num`; `u3:num`;
   `s0:num`; `s1:num`; `s2:num`; `s3:num`];;

(*** The head of the loop at 0x20a8, round m and olimit = op3 + L, ***)
(*** which the loop goes on as long as the output of stream 3 is   ***)
(*** below (some iteration being left when it is)                  ***)

let fl2_jvars = [`j0:num`; `j1:num`; `j2:num`; `j3:num`];;

let mk_fl2_state pcoff extra =
  let pct = subst [mk_small_numeral pcoff,`k:num`]
                  `read PC s = word(pc + k)` in
  let body = list_mk_conj
    (pct :: fl2_common :: extra @ map2 fl2_stream [0;1;2;3] fl2_streams) in
  let ex = list_mk_exists(fl2_uvars,body) in
  with_memsafe fl2_rr fl2_wr
    (list_mk_abs(fl2_jvars @ [`m:num`; `L:num`; `s:armstate`],ex));;

let fl2_olimit =
 [subst [fl2_spk 96,`a:int64`]
   `read (memory :> bytes64 a) s = word_add op3 (word L):int64`;
  `L <= j3 + 5 * m`];;

let fl2_body_pre = mk_fl2_state 0x20a8
  (`j3 < L` :: fl2_olimit @ map fl2_stack_fact fl2_body_kept);;

(*** The head of a round at 0x2008 (and the exit at 0x2440): the output ***)
(*** pointers in their copies (and op0, op3 in x8, x5), w18 = w (1 after ***)
(*** the first round), the streams with their pointers and containers in ***)
(*** registers, and the extra facts given                                ***)

let fl2_round_stream k (ipr,cr) =
  let n = string_of_int k in
  let u = mk_var("u"^n,`:num`) and sk = mk_var("s"^n,`:num`)
  and d = mk_var("sz"^n,`:num`) in
  let t = subst [u,`u:num`; fl2_jv k,`j:num`; d,`d:num`;
                 fl_cont u sk,`c:int64`; fl2_stream_core k,`core:bool`]
   `read IPR (s:armstate) = word_add (ilowest:int64) (word u) /\
    read CR s = (c:int64) /\ core /\ j <= d` in
  subst [ipr,`IPR:(armstate,int64)component`;
         cr,`CR:(armstate,int64)component`] t;;

let fl2_round_streams =
  [`X25`,`X1`; `X23`,`X3`; `X24`,`X2`; `X28`,`X26`];;

let fl2_round_facts w = list_mk_conj
 ([mk_eq(`read X4 s`,fl2_spk 192); mk_eq(`read X30 s`,fl2_spk 224);
   `read X8 s = word_add op0 (word j0)`;
   `read X5 s = word_add op3 (word j3)`; mk_eq(`read X18 s`,w)] @
  map (fun k ->
    let opk = mk_var("op"^string_of_int k,`:int64`) in
    fl2_stack_fact (192 + 8 * k,
      mk_comb(mk_comb(`word_add:int64->int64->int64`,opk),
              mk_comb(`word:num->int64`,fl2_jv k)))) [0;1;2;3]);;

let mk_fl2_round pcoff w extra =
  let pct = subst [mk_small_numeral pcoff,`k:num`]
                  `read PC s = word(pc + k)` in
  let body = list_mk_conj
    (pct :: fl2_common :: fl2_round_facts w :: extra @
     map2 fl2_round_stream [0;1;2;3] fl2_round_streams) in
  let ex = list_mk_exists(fl2_uvars,body) in
  with_memsafe fl2_rr fl2_wr (list_mk_abs(fl2_jvars @ [`s:armstate`],ex));;

let fl2_round = mk_fl2_round 0x2008 `word 1:int64` [];;

(*** The body from 0x20a8: 5 lookups of each stream and the reloads, and ***)
(*** then the next iteration, or the end of the round through 0x2400     ***)

let fl2_jvars' = [`j0':num`; `j1':num`; `j2':num`; `j3':num`];;

let fl2_body_goal =
  mk_fl2_goal_hyps [`1 <= m`] (fl2_jvars @ [`m:num`; `L:num`])
  (mk_abs(`s:armstate`,
      list_mk_comb(fl2_body_pre,fl2_jvars @ [`m:num`; `L:num`; `s:armstate`])))
  (mk_abs(`s:armstate`,
      list_mk_exists(fl2_jvars',
        list_mk_conj
         [`j0 + 5 <= j0' /\ j0' <= j0 + 10 /\ j1 + 5 <= j1' /\
           j1' <= j1 + 10 /\ j2 + 5 <= j2' /\ j2' <= j2 + 10 /\
           j3 + 5 <= j3' /\ j3' <= j3 + 10`;
          mk_disj
           (mk_conj(`j3' < L`,
              list_mk_comb(fl2_body_pre,
                fl2_jvars' @ [`m - 1`; `L:num`; `s:armstate`])),
            mk_conj(`L <= j3'`,
              list_mk_comb(fl2_round,fl2_jvars' @ [`s:armstate`])))])));;

(* ------------------------------------------------------------------------- *)
(* The normalization of the state after each step of the body: the index of  *)
(* a lookup and its entry of the table, the shifts, the stores merged into   *)
(* the bytes decoded, the reloads, and the numeric facts hidden that the     *)
(* stores do not need.                                                       *)
(* ------------------------------------------------------------------------- *)

(*** The lookups numbered as the simulation goes, for the names of the ***)
(*** variables of each                                                  ***)

let fl2_counter = ref 0;;

(*** The number of symbols of an entry, 1 or 2, as the length of its ***)
(*** symbols                                                         ***)

let LENGTH_X2_SYMS = prove
 (`!len (a:byte) b c.
        len = 1 \/ len = 2
        ==> LENGTH(if len = 2 then [a; b] else [c]) = len`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** The facts of a lookup: the shift of the index by 2, the zero ***)
(*** extensions of the bytes loaded and the shift of a container  ***)

let FAST2_SHL2 = prove
 (`!x. word_shl (word x:int64) 2 = word(4 * x)`,
  REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV);;

let FAST2_JSHL = prove
 (`!(c:int64) nb. nb < 64 ==> word_jshl c (word nb) = word_shl c nb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jshl] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `nb < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `64` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[MOD_LT]]);;

(*** The number of symbols of a lookup as the 32-bit offset of a store ***)

let FAST2_UXTW = prove
 (`!n. n < 2 EXP 32
       ==> word_zx (word_zx (word n:int64):int32):int64 = word n /\
           word_zx (word_zx (word_zx (word n:int64):int32):int32):int64 =
           word n`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 32` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[WORD_ZX_WORD; DIMINDEX_32; DIMINDEX_64; MOD_LT]]);;

let FAST2_UXTW256 = prove
 (`!n. n < 256
       ==> word_zx (word_zx (word n:int64):int32):int64 = word n /\
           word_zx (word_zx (word_zx (word n:int64):int32):int32):int64 =
           word n`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FAST2_UXTW THEN
  UNDISCH_TAC `n < 256` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** The antecedents of the lemmas about a lookup ***)

let FL2_ANT_TAC =
  REPEAT CONJ_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; FL_ARITH_TAC];;

(*** The index read from the container of a stream as bits of blk, with ***)
(*** the entry of the table for it: its two symbols a and b, its number ***)
(*** of bits nb and number of symbols len                               ***)

let FL2_INDEX_ONE_TAC (th:thm) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let _,tmi,_ = term_match [] fl_index_pat (rhs(concl th)) in
    let inst v = try rev_assoc v tmi with Failure _ -> v in
    let blk = inst `blk:byte list` and u = inst `u:num` and x = inst `x:num` in
    incr fl2_counter;
    let k = string_of_int !fl2_counter in
    let idx = mk_var("idx"^k,`:num`) and ev = mk_var("e"^k,`:num list`)
    and av = mk_var("a"^k,`:num`) and bv = mk_var("b"^k,`:num`)
    and nb = mk_var("nb"^k,`:num`) and len = mk_var("len"^k,`:num`) in
    let pos = subst [u,`u:num`; x,`x:num`] `8 * u + 64 - x` in
    let back = list_mk_icomb "zstd_back" [blk; pos; `11`] in
    let lt a b = mk_binop `(<):num->num->bool` a b
    and le a b = mk_binop `(<=):num->num->bool` a b in
    let xle = le x `52` in
    let et =
      list_mk_icomb "huf_dentry2" [`ws:num list`; `ml:num`; `11`; idx] in
    let el n = mk_icomb(mk_icomb(`EL:num->num list->num`,mk_small_numeral n),
                        ev) in
    (SUBGOAL_THEN xle (fun xth ->
       RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [blk; u; x] FAST_INDEX') xth]))
     THENL [FL_LE_TAC; ALL_TAC] THEN
     SUBGOAL_THEN (lt back `2048`) ASSUME_TAC THENL
      [MP_TAC(SPECL [blk; pos; `11`] ZSTD_BACK_BOUND) THEN
       CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
       ALL_TAC] THEN
     ABBREV_TAC (mk_eq(idx,back)) THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; idx] HUF_DENTRY2_BOUNDS) THEN
     ANTS_TAC THENL [FL2_ANT_TAC; DISCH_TAC] THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; idx; s]
       HUF_DTABLE2_READ16) THEN
     ANTS_TAC THENL [FL2_ANT_TAC; DISCH_TAC] THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; idx; s]
       HUF_DTABLE2_READ) THEN
     ANTS_TAC THENL
      [FL2_ANT_TAC;
       DISCH_THEN(fun rth -> let [_;_;r2;r3] = CONJUNCTS rth in
         ASSUME_TAC r2 THEN ASSUME_TAC r3)] THEN
     ABBREV_TAC (mk_eq(ev,et)) THEN
     ABBREV_TAC (mk_eq(av,el 0)) THEN ABBREV_TAC (mk_eq(bv,el 1)) THEN
     ABBREV_TAC (mk_eq(nb,el 2)) THEN ABBREV_TAC (mk_eq(len,el 3)) THEN
     FIRST_X_ASSUM(fun bth ->
       if is_conj(concl bth) && free_in len (concl bth) &&
          free_in nb (concl bth)
       then MAP_EVERY ASSUME_TAC (CONJUNCTS bth)
       else NO_TAC) THEN
     SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                                 mk_comb(`word:num->int64`,idx)),idx))
     ASSUME_TAC THENL
      [MATCH_MP_TAC VAL_WORD_LT64 THEN UNDISCH_TAC (lt idx `2048`) THEN
       ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN (list_mk_conj [le `1` len; le len `2`])
       STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC (mk_disj(mk_eq(len,`1`),mk_eq(len,`2`))) THEN ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN (list_mk_conj [lt nb `64`; lt len `256`;
                                 lt (mk_binop `(+):num->num->num` av
                                      (mk_binop `( * ):num->num->num`
                                        `256` bv)) `65536`])
       STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THENL
        [FL_ARITH_TAC;
         UNDISCH_TAC (mk_disj(mk_eq(len,`1`),mk_eq(len,`2`))) THEN ARITH_TAC;
         FL_ARITH_TAC];
       ALL_TAC] THEN
     ASSUME_TAC(GEN `c:int64` (MP (SPECL [`c:int64`; nb] FAST2_JSHL)
                  (ASSUME(lt nb `64`))))
    ) gl;;

(*** The table entries already loaded into registers, out of the way of ***)
(*** the simulation of the stores                                       ***)

let FL2_DROP_TAC : tactic =
  let dtv = `dt:int64` in
  fun (asl,w as gl) ->
    let s = rand w in
    let regvals = mapfilter (fun (_,th) ->
      let t = concl th in
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(_,_)),s')),
             Comb(Const("word",_),v))
          when s' = s -> v
      | _ -> fail()) asl in
    let is_entry th =
      let t = concl th in
      is_eq t &&
      (match lhs t with
         Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
              Comb(Const(("bytes16" | "bytes8"),_),a))),_) ->
           (match a with
              Comb(Comb(Const("word_add",_),b),_) -> b = dtv
            | _ -> false) &&
           (match rhs t with
              Comb(Const("word",_),v) -> mem v regvals
            | _ -> false)
       | _ -> false) in
    DISCARD_ASSUMPTIONS_TAC is_entry gl;;

let FL2_INDEX_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let ths = mapfilter (fun (_,th) ->
      let t = concl th in
      if is_eq t && is_comb(lhs t) && rand(lhs t) = s &&
         can (term_match [] fl_index_pat) (rhs t) then th else fail()) asl in
    MAP_EVERY FL2_INDEX_ONE_TAC ths gl;;

(*** The index shifted by 2 and the containers shifted ***)

let fl2_jshl_pat = `!c. word_jshl c (word nb:int64) = word_shl c nb`;;

let FL2_SHIFT_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let ths = mapfilter (fun (_,th) ->
      if can (term_match [] fl2_jshl_pat) (concl th) then th else fail())
      asl in
    let rule = REWRITE_RULE(FAST2_SHL2 :: WORD_SHL_COMPOSE :: ths) in
    RULE_ASSUM_TAC(fun th ->
      if free_in s (concl th) then rule th else th) gl;;


(*** A 16-bit store of the two symbols of a lookup after the bytes l   ***)
(*** stored from a, merged into one fact for the bytes from a up to the ***)
(*** symbols of the lookup; the facts for the bytes before the stores   ***)
(*** that the code does again after the loop are kept                   ***)

let READ_MEMORY_X2_STORE_N = prove
 (`!a:int64 (l:byte list) n b1 b2 len s:armstate.
        read (memory :> bytes(a,n)) s = num_of_bytelist l /\
        LENGTH l = n /\
        read (memory :> bytes16 (word_add a (word n))) s =
        word(b1 + 256 * b2) /\
        b1 < 256 /\ b2 < 256 /\ (len = 1 \/ len = 2)
        ==> read (memory :> bytes(a,n + len)) s =
            num_of_bytelist(APPEND l (if len = 2 then [word b1; word b2]
                                      else [word b1]))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MP_TAC th THEN
    SUBST1_TAC(SYM(CONJUNCT1(CONJUNCT2 th)))) THEN
  REWRITE_TAC[READ_MEMORY_X2_STORE]);;

let fl2_keep_bases = ref [`op1:int64`; `op2:int64`; `op3:int64`];;

let FL2_MERGE_TAC : tactic =
  let pat16 = `read (memory :> bytes16 a) (s:armstate) = word(x + 256 * y)`
  and patl = `read (memory :> bytes(a,n)) (s:armstate) = num_of_bytelist l` in
  fun (asl,w as gl) ->
    let s = rand w in
    let b16s = mapfilter (fun (_,th) ->
      let _ = term_match [] (subst [s,`s:armstate`] pat16) (concl th) in
      th) asl
    and lists = mapfilter (fun (_,th) ->
      let _ = term_match [] (subst [s,`s:armstate`] patl) (concl th) in
      th) asl in
    let base_len th = dest_pair(rand(rand(lhand(lhs(concl th))))) in
    let addr th16 = rand(rand(lhand(lhs(concl th16)))) in
    let ends_at thl a =
      let base,n = base_len thl in
      if n = `0` then a = base else
      (match a with
         Comb(Comb(Const("word_add",_),b),Comb(Const("word",_),k)) ->
           b = base && fl_num_norm k = fl_num_norm n
       | _ -> false) in
    let pairs = mapfilter (fun th16 ->
       let a = addr th16 in
       let thl = find (fun thl -> ends_at thl a) lists in (th16,thl)) b16s in
    match pairs with
      [] -> failwith "FL2_MERGE_TAC"
    | (th16,thl)::_ ->
        let base,n = base_len thl in
        let l = rand(rhs(concl thl)) in
        let v = rand(rhs(concl th16)) in
        let b1 = lhand v and b2 = rand(rand v) in
        let k = String.sub (fst(dest_var b1)) 1
                  (String.length(fst(dest_var b1)) - 1) in
        let len = mk_var("len"^k,`:num`) in
        let lgoal = mk_eq(mk_comb(`LENGTH:byte list->num`,l),n) in
        let lenth = TAC_PROOF((asl,lgoal),
          REWRITE_TAC[LENGTH_APPEND; HUF_DECODE_LENGTH] THEN
          MAP_EVERY (fun th -> if is_disj(concl th) then ASSUME_TAC th
                               else ALL_TAC) (fl_all_facts asl) THEN
          ASM_SIMP_TAC[LENGTH_X2_SYMS] THEN ARITH_TAC) in
        let th16' = if n = `0` then
            CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
              (fun t -> if t = base then SYM(SPEC base WORD_ADD_0)
                        else failwith ""))) th16
          else
            let k = rand(rand(addr th16)) in
            if k = n then th16 else
            let eq = EQT_ELIM(REWRITE_CONV[ADD_AC] (mk_eq(k,n))) in
            CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
              (fun t -> if t = k then eq else failwith ""))) th16 in
        let lemma = ISPECL [base; l; n; b1; b2; len; s]
                      READ_MEMORY_X2_STORE_N in
        let ants = conjuncts(lhand(concl lemma)) in
        let facts = fl_all_facts asl in
        let prove_ant t =
          if t = concl thl then thl
          else if t = concl lenth then lenth
          else if t = concl th16' then th16'
          else find (fun th -> concl th = t) facts in
        let th0 = MP lemma (end_itlist CONJ (map prove_ant ants)) in
        let th = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                   (fun t -> if is_pair t then
                               (RAND_CONV(REWRITE_CONV[GSYM ADD_ASSOC])) t
                             else failwith ""))) th0 in
        let n' = snd(dest_pair(rand(rand(lhand(lhs(concl th)))))) in
        let atoms = striplist (dest_binop `(+):num->num->num`) n' in
        let j = hd atoms and lens = tl atoms in
        let bnd = mk_binop `(<=):num->num->bool` n'
                    (mk_binop `(+):num->num->num` j
                       (mk_small_numeral(2 * length lens))) in
        let lenbs = filter (fun th -> let t = concl th in
          is_binary "<=" t && mem (lhand t) lens && rand t = `2`) facts in
        let bth = TAC_PROOF(([],bnd),
          MAP_EVERY (MP_TAC o ASSUME o concl) lenbs THEN ARITH_TAC) in
        let bth' = itlist PROVE_HYP lenbs bth in
        let keep = mem base !fl2_keep_bases in
        let is_old_bound t =
          is_binary "<=" t &&
          (match rand t with
             Comb(Comb(Const("+",_),j'),k) -> j' = j && is_numeral k
           | _ -> false) &&
          (match striplist (dest_binop `(+):num->num->num`) (lhand t) with
             j'::_::_ -> j' = j | _ -> false) in
        (DISCARD_ASSUMPTIONS_TAC (fun t -> concl t = concl th16 ||
                                           (not keep && concl t = concl thl) ||
                                           is_old_bound(concl t))
         THEN ASSUME_TAC th THEN ASSUME_TAC bth') gl;;

(*** The numeric facts not about the state put together as one         ***)
(*** conjunction, except those that the simulation of the stores and    ***)
(*** loads needs: the bounds x < n of the values in registers, for the  ***)
(*** sizes of words, val(word idx) = idx, the room for the outputs of   ***)
(*** the streams j + 10 <= sz, the bounds of the outputs decoded j +    ***)
(*** len + ... <= j + c and the bounds of the regions below 2^64        ***)

let fl2_is_lookup_var v =
  is_var v &&
  (let n = fst(dest_var v) in
   exists (fun p ->
     let lp = String.length p and ln = String.length n in
     ln > lp && String.sub n 0 lp = p &&
     (let rest = String.sub n lp (ln - lp) in
      String.length rest > 0 &&
      List.for_all (fun c -> '0' <= c && c <= '9')
        (List.init (String.length rest) (String.get rest))))
     ["idx"; "a"; "b"; "nb"; "len"; "e"]);;

let FL2_HIDE_TAC : tactic =
  let numty = `:num` and numlty = `:num list` and statety = `:armstate`
  and valc = `val:int64->num` and two64 = `2 EXP 64` and dtv = `dt:int64` in
  let is_rel tm =
    exists (fun op -> is_binary op tm) ["="; "<"; "<="] &&
    (type_of(lhand tm) = numty || type_of(lhand tm) = numlty) in
  let is_jv v = is_var v &&
    (let n = fst(dest_var v) in String.length n = 2 && n.[0] = 'j') in
  fun (asl,w) ->
    let s = rand w in
    let live = itlist (fun (_,th) acc ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
          when s' = s &&
               (is_const c ||
                (match c with
                   Comb(Comb(Const(":>",_),_),Comb(_,a)) ->
                     (match a with
                        Comb(Comb(Const("word_add",_),b),_) -> b = dtv
                      | _ -> false)
                 | _ -> false)) ->
            union (filter fl2_is_lookup_var (frees v)) acc
      | _ -> acc) asl [] in
    let keep tm =
      (is_eq tm && is_comb(lhs tm) &&
       fst(strip_comb(lhs tm)) = valc &&
       subset (filter fl2_is_lookup_var (frees tm)) live) ||
      (is_binary "<" tm && is_numeral(rand tm) &&
       subset (filter fl2_is_lookup_var (frees tm)) live) ||
      (is_binary "<=" tm &&
       (match lhand tm with
          Comb(Comb(Const("+",_),j),_) -> is_jv j
        | _ -> false)) ||
      can (find_term ((=) two64)) tm in
    let is_hidden tm =
      (is_rel tm || is_disj tm) &&
      not(exists (fun v -> type_of v = statety) (frees tm)) &&
      not(keep tm) in
    let ths,others = partition (fun (_,th) -> is_hidden(concl th)) asl in
    if ths = [] then ALL_TAC (asl,w) else
    ASSUME_TAC (end_itlist CONJ (map snd ths)) (others,w);;

(*** The zero extensions of the numbers of symbols as 32-bit offsets of ***)
(*** stores, again after the small-word normalization has changed them   ***)

let FL2_UXTW_TAC : tactic =
  let is_len t = is_var t &&
    String.length(fst(dest_var t)) > 3 &&
    String.sub (fst(dest_var t)) 0 3 = "len" in
  fun (asl,w as gl) ->
    let s = rand w in
    let lens = setify(mapfilter (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(_,_)),s')),
             Comb(Const("word",_),v))
          when s' = s && is_len v -> v
      | _ -> fail()) asl) in
    let is_uxtw th =
      let t = concl th in
      is_eq t &&
      (match rhs t with Comb(Const("word",_),v) -> is_len v | _ -> false) &&
      (match lhs t with Comb(Const("word_zx",_),_) -> true | _ -> false) in
    let add len =
      let lt = mk_binop `(<):num->num->bool` len `256` in
      let lth = snd(find (fun (_,th) -> concl th = lt) asl) in
      MAP_EVERY ASSUME_TAC (CONJUNCTS(MP (SPEC len FAST2_UXTW256) lth)) in
    (DISCARD_ASSUMPTIONS_TAC is_uxtw THEN MAP_EVERY add lens) gl;;

let FL2_NORM_TAC = FL2_INDEX_TAC THEN FL2_SHIFT_TAC THEN FL2_DROP_TAC THEN
                   REPEAT FL2_MERGE_TAC THEN FL_RELOAD_TAC THEN
                   REPEAT FL_WINDOW_TAC THEN FL2_HIDE_TAC THEN
                   HUF_HIDE_SUB_TAC THEN FL2_UXTW_TAC;;

let FL2_NSTEPS_TAC ns =
  MAP_EVERY (fun n -> FL2_STEP_TAC n THEN FL2_NORM_TAC) ns;;

(* ------------------------------------------------------------------------- *)
(* The end of the body: the symbols of the lookups of each stream as steps   *)
(* of huf_decode, the test of olimit, the counts and the streams of the      *)
(* post, the memory safety in a small context and the stores done again      *)
(* after a round.                                                            *)
(* ------------------------------------------------------------------------- *)

(*** After the body: the symbols decoded by the lookups of each stream, as ***)
(*** steps of huf_decode, from the facts of the lookups, and the bytes     ***)
(*** stored as those decoded                                               ***)

let fl2_num_norm = fl_num_norm;;

let FL2_DECODE5_TAC (u:term) (p:term) (j:term) : tactic =
  fun (asl,w as gl) ->
    let facts = fl_all_facts asl in
    let idxpat = `zstd_back (blk:byte list) (8 * u + 64 - x) 11 = idx` in
    let looks = mapfilter (fun th ->
      let _,tmi,_ = term_match [] idxpat (concl th) in
      let inst v = try rev_assoc v tmi with Failure _ -> v in
      if inst `u:num` = u then (inst `x:num`,inst `idx:num`,th)
      else fail()) facts in
    let size x = length(striplist (dest_binop `(+):num->num->num`) x) in
    let looks = sort (fun (x,_,_) (y,_,_) -> size x < size y) looks in
    let lfact l = find (fun th -> let t = concl th in is_eq t && lhs t = l)
                       facts in
    let elfact n ev = lfact (mk_icomb(mk_icomb(`EL:num->num list->num`,
                                               mk_small_numeral n),ev)) in
    let dec jt = list_mk_icomb "huf_decode"
                   [`ws:num list`; `ml:num`; `blk:byte list`; p; jt] in
    let fst_snd jt = mk_icomb(`FST:num#bool->num`,
                       mk_icomb(`SND:byte list#num#bool->num#bool`,dec jt))
    and snd_snd jt = mk_icomb(`SND:num#bool->bool`,
                       mk_icomb(`SND:byte list#num#bool->num#bool`,dec jt)) in
    let addac a b =
      if a = b then REFL a else EQT_ELIM(REWRITE_CONV[ADD_AC] (mk_eq(a,b))) in
    let step (jt,posth,okth,ths) (x,idx,ith) =
      let eth = lfact (list_mk_icomb "huf_dentry2"
                         [`ws:num list`; `ml:num`; `11`; idx]) in
      let ev = rhs(concl eth) in
      let ths5 = [ith; eth; elfact 0 ev; elfact 1 ev; elfact 2 ev;
                  elfact 3 ev] in
      let lemma = SPECL [`ws:num list`; `ml:num`; `blk:byte list`; p; jt; u; x]
                    HUF_DECODE_FAST2_STEP in
      let lemma' =
        REWRITE_RULE ths5 (CONV_RULE(TOP_DEPTH_CONV let_CONV) lemma) in
      let ant = lhand(concl lemma') in
      let cs = conjuncts ant in
      let c3 = el 2 cs and c5 = el 4 cs in
      let p3 =
        if concl posth = c3 then posth else
        let r = rhs(concl posth) in
        let x' = rand(rand r) and x3 = rand(rand(rhs c3)) in
        TRANS posth
          (AP_TERM (rator r) (AP_TERM (rator(rand r)) (addac x' x3))) in
      let p5 = TAC_PROOF((asl,c5),FL_ARITH_TAC) in
      let prove_ant t =
        if t = c3 then p3 else if t = c5 then p5
        else if t = concl okth then okth
        else find (fun th -> concl th = t) facts in
      let th = MP lemma' (end_itlist CONJ (map prove_ant cs)) in
      let [f1;f2;f3] = CONJUNCTS th in
      let lenv = rhs(concl(elfact 3 ev)) in
      let jt' = mk_binop `(+):num->num->num` jt lenv in
      let jn = fl2_num_norm jt' in
      let norm th = if jn = jt' then th else
        CONV_RULE(ONCE_DEPTH_CONV(fun t -> if t = jt' then addac jt' jn
                                           else failwith "")) th in
      (jn,norm f2,norm f3,norm f1 :: ths) in
    let posth0 = lfact (fst_snd j) in
    let okth0 = find (fun th -> concl th = snd_snd j) facts in
    let jn,posth,okth,ths =
      itlist (fun l acc -> step acc l) (rev looks) (j,posth0,okth0,[]) in
    let memth = snd(find (fun (_,th) -> let t = concl th in
      is_eq t &&
      (match lhs t with
         Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
              Comb(Const("bytes",_),ar))),_) ->
           let b,n = dest_pair ar in
           (match b with Var(_,_) -> true | _ -> false) &&
           n = jn &&
           (match rhs t with
              Comb(Const("num_of_bytelist",_),_) -> true | _ -> false) &&
           can (find_term ((=) (dec j))) (rhs t)
       | _ -> false)) asl) in
    let memth' = REWRITE_RULE (map SYM ths) memth in
    (MAP_EVERY ASSUME_TAC [posth; okth; memth']) gl;;

(*** The values of the output pointers, from the outputs following each ***)
(*** other below 2^64                                                    ***)

let FL2_VAL_OPS = prove
 (`!op0 op1 op2 op3:int64 sz0 sz1 sz2 sz3.
        word_add op0 (word sz0) = op1 /\ word_add op1 (word sz1) = op2 /\
        word_add op2 (word sz2) = op3 /\
        val op0 + sz0 + sz1 + sz2 + sz3 < 2 EXP 64
        ==> val op1 = val op0 + sz0 /\ val op2 = val op0 + sz0 + sz1 /\
            val op3 = val op0 + sz0 + sz1 + sz2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:int64 n. val x + n < 2 EXP 64 ==> val(word_add x (word n)) = val x + n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(op1:int64) = val(op0:int64) + sz0` ASSUME_TAC THENL
   [EXPAND_TAC "op1" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(op2:int64) = val(op0:int64) + sz0 + sz1` ASSUME_TAC THENL
   [EXPAND_TAC "op2" THEN FIRST_X_ASSUM(fun th ->
      W(fun (asl,w) -> MP_TAC(SPECL [`op1:int64`; `sz1:num`] th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "op3" THEN FIRST_X_ASSUM(fun th ->
    W(fun (asl,w) -> MP_TAC(SPECL [`op2:int64`; `sz2:num`] th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC);;

let VAL_WORD_ADD_LT = prove
 (`!x:int64 n. val x + n < 2 EXP 64 ==> val(word_add x (word n)) = val x + n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(*** Arithmetic from the facts given (also among those hidden) ***)

let FL2_USE_ARITH_TAC tms : tactic =
  fun (asl,w as gl) ->
    let facts = fl_all_facts asl in
    let ths = map (fun t -> find (fun th -> concl th = t) facts) tms in
    (MAP_EVERY MP_TAC ths THEN ARITH_TAC) gl;;

(*** The test of the loop at 0x23fc, olimit = op3 + L against op3 + j, ***)
(*** split into the cases j < L (the loop goes on) and not             ***)

let FL2_TEST_TAC (j3t:term) =
  let jflag = mk_binop `(<):num->num->bool` j3t `L:num` in
  MP_TAC(SPECL [`op0:int64`; `op1:int64`; `op2:int64`; `op3:int64`;
                `sz0:num`; `sz1:num`; `sz2:num`; `sz3:num`] FL2_VAL_OPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RULE_ASSUM_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_)
        when mem c [`NF`;`ZF`;`CF`;`VF`] ->
          REWRITE_RULE[WORD_ADD_ASSOC_NUM] th
    | _ -> th) THEN
  W(fun (asl,w) ->
    let s = rand w in
    let cf = snd(find (fun (_,th) -> let t = concl th in
               is_iff t && lhand t = list_mk_icomb "read" [`CF`; s]) asl) in
    let vs = find_terms (fun t -> match t with
               Comb(Const("val",_),Comb(Comb(Const("word_add",_),b),_)) ->
                 b = `op3:int64`
             | _ -> false) (rand(concl cf)) in
    let eqs = map (fun v -> let a = rand v in
      mk_eq(v,mk_binop `(+):num->num->num` `val(op3:int64)`
                       (rand(rand a)))) vs in
    MAP_EVERY (fun e -> SUBGOAL_THEN e ASSUME_TAC THENL
      [MATCH_MP_TAC VAL_WORD_ADD_LT THEN
       FL2_USE_ARITH_TAC
        [`val(op3:int64) = val(op0:int64) + sz0 + sz1 + sz2`;
         `val(op0:int64) + sz0 + sz1 + sz2 + sz3 < 2 EXP 64`;
         `L <= j3 + 5 * m`; `j3 + 10 * m <= sz3`; `j3 + 10 <= sz3`;
         mk_binop `(<=):num->num->bool` j3t `j3 + 10`];
       ALL_TAC]) eqs) THEN
  SUBGOAL_THEN `val(word L:int64) = L` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN
    FL2_USE_ARITH_TAC [`val(op0:int64) + sz0 + sz1 + sz2 + sz3 < 2 EXP 64`;
      `L <= j3 + 5 * m`; `j3 + 10 * m <= sz3`];
    ALL_TAC] THEN
  ASM_CASES_TAC jflag;;

(*** The post of the body: the counts of symbols decoded and the new u ***)
(*** and s of each stream from its pointer register                   ***)

let fl2_ipregs = [`X25`; `X23`; `X24`; `X28`];;

let FL2_STREAM_WITNESS_TAC (s:term) : tactic =
  fun (asl,w as gl) ->
    let ipval r = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
        is_eq t && lhs t = list_mk_icomb "read" [r; s]) asl))) in
    let offs = map (fun r -> rand(rand(ipval r))) fl2_ipregs in
    let ts = map (fun o' -> lhand(rand o')) offs in
    (MAP_EVERY EXISTS_TAC offs THEN
     MAP_EVERY (fun t -> EXISTS_TAC (mk_binop `(MOD):num->num->num` t `8`))
       ts) gl;;

(*** The new counts of symbols of the streams, from the facts bytes(op, j) ***)

let fl2_new_counts asl s =
  map (fun k ->
    let op = mk_var("op"^string_of_int k,`:int64`) in
    let j = fl2_jv k in
    let cands = mapfilter (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),_),Comb(Const("bytes",_),ar))),s')),
             Comb(Const("num_of_bytelist",_),l))
          when s' = s && fst(dest_pair ar) = op &&
               (match l with
                  Comb(Const("FST",_),d) ->
                    can (term_match [] `huf_decode a b c d e`) d
                | _ -> false) -> snd(dest_pair ar)
      | _ -> fail()) asl in
    let n x = length(striplist (dest_binop `(+):num->num->num`) x) in
    let best = itlist (fun c b -> if n c > n b then c else b) cands j in
    best) [0;1;2;3];;

(*** The hidden facts that the memory safety of the accesses needs: the ***)
(*** indices into the table, the numbers of symbols and the pointers,   ***)
(*** and the bounds of the symbols stored again after the loop          ***)

let FL2_MEMSAFE_FACTS_TAC : tactic =
  fun (asl,w as gl) ->
    let facts = fl_all_facts asl in
    let have t = exists (fun (_,th) -> concl th = t) asl in
    let is_pref p v = is_var v &&
      (let n = fst(dest_var v) in
       String.length n > String.length p &&
       String.sub n 0 (String.length p) = p) in
    let ok t =
      (is_binary "<" t && is_pref "idx" (lhand t) && rand t = `2048`) ||
      (is_binary "<=" t && is_pref "len" (lhand t) && rand t = `2`) ||
      (is_binary "<" t && rand t = `65536`) ||
      (is_binary "<=" t && rand t = `LENGTH(blk:byte list)`) in
    let ths = filter (fun th -> ok(concl th) && not(have(concl th))) facts in
    MAP_EVERY ASSUME_TAC ths gl;;

(*** MEMSAFE_ELIM_TAC with the memory safety proved in a small context: ***)
(*** the events, the accesses before and the linear facts about the     ***)
(*** numbers in the addresses                                           ***)

let FL2_MEMSAFE_ELIM_TAC : tactic =
  let l1 = TAUT `p ==> (p /\ q <=> q)` and l2 = TAUT `q ==> (p /\ q <=> p)` in
  let numty = `:num` and statety = `:armstate` and evc = `events` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="] in
  let bad = ["EL"; "huf_decode"; "zstd_back"; "huf_dentry2"; "FST"; "SND";
             "num_of_bytelist"; "word"; "MOD"; "DIV"] in
  let linear t =
    not(can (find_term (fun u -> is_const u && mem (fst(dest_const u)) bad))
          t) in
  let keep t =
    (match strip_comb t with
       Const("memaccess_inbounds",_),_ -> true
     | _ -> false) ||
    (is_eq t && is_comb(lhs t) &&
     (try rand(rator(lhs t)) = evc with Failure _ -> false)) ||
    (is_num_relop t && linear t &&
     not(exists (fun v -> type_of v = statety) (frees t))) in
  let has_events asl s =
    exists (fun (_,th) -> let t = concl th in
              is_eq t && is_read_events(lhs t) && rand(lhs t) = s) asl in
  let expand c = if is_exists c then REFL c else REWR_CONV puff_memsafe c in
  fun (asl,w as gl) ->
    let ok t = is_memsafe_clause t &&
               (let _,_,_,s = memsafe_clause_args t in has_events asl s) in
    let redex t = is_comb t && is_abs(fst(strip_comb t)) &&
                  can (find_term is_memsafe_clause) t in
    ((if can (find_term redex) w then BETA_TAC else ALL_TAC) THEN
     W(fun (asl,w) ->
       let cls = setify(find_terms ok w) in
       if cls = [] then ALL_TAC else
       let sasl = map (fun th -> ("",th))
                   (filter (fun th -> keep(concl th)) (fl_all_facts asl)) in
       let eqs = map expand cls in
       let exps = setify(map (rhs o concl) eqs) in
       let pths = map (fun c -> TAC_PROOF((sasl,c),MEMSAFE_TAC)) exps in
       let prove_cl c =
         let eq = expand c in
         EQ_MP (SYM eq) (find (fun th -> concl th = rhs(concl eq)) pths) in
       let ths = map prove_cl cls in
       let rec conv tm =
         if is_conj tm then
           let p,q = dest_conj tm in
           try let th = find (fun th -> aconv (concl th) p) ths in
               (REWR_CONV(MP (INST [p,`p:bool`; q,`q:bool`] l1) th) THENC
                conv) tm
           with Failure _ ->
           try let th = find (fun th -> aconv (concl th) q) ths in
               REWR_CONV(MP (INST [p,`p:bool`; q,`q:bool`] l2) th) tm
           with Failure _ -> BINOP_CONV conv tm
         else SUB_CONV conv tm in
       CONV_TAC conv)) gl;;

let FL2_FINAL_TAC = ENSURES_FINAL_STATE_TAC THEN FL2_MEMSAFE_ELIM_TAC;;

(*** The halfword of the first two bytes of a 32-bit word in memory ***)

let READ_MEMORY_BYTES16_OF_32 = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes32 a) s = word n /\ n < 65536
        ==> read (memory :> bytes16 a) s = word n`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[GSYM VAL_READ_MEMORY_BYTES16] THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `2`; `read memory s`] READ_BYTES_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[VAL_READ_MEMORY_BYTES32] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_16; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n < 4294967296` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(*** The 16-bit loads of the halfwords kept in the frame after the loop ***)

let FL2_HALF_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let facts = fl_all_facts asl in
    let b32s = mapfilter (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),_),Comb(Const("bytes32",_),a))),s')),
             Comb(Const("word",_),n)) when s' = s -> (a,n,th)
      | _ -> fail()) asl in
    let tac (a,n,th) =
      let lt = mk_binop `(<):num->num->bool` n `65536` in
      let lth = find (fun th -> concl th = lt) facts in
      ASSUME_TAC(MP (ISPECL [a; n; s] READ_MEMORY_BYTES16_OF_32)
                    (CONJ th lth)) in
    MAP_EVERY tac b32s gl;;

let FL2_NORM_NOHIDE_TAC =
  FL2_INDEX_TAC THEN FL2_SHIFT_TAC THEN FL2_DROP_TAC THEN
  REPEAT FL2_MERGE_TAC THEN FL_RELOAD_TAC THEN REPEAT FL_WINDOW_TAC THEN
  FL2_UXTW_TAC;;

(*** For the stores done again after the loop: the bounds of the outputs ***)
(*** decoded and of the symbols stored, from the hidden facts            ***)

let FL2_AFTER_FACTS_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let facts = fl_all_facts asl in
    let have t = exists (fun (_,th) -> concl th = t) asl in
    let lens_of n =
      match striplist (dest_binop `(+):num->num->num`) n with
        j::(_::_ as ls) -> Some(j,ls)
      | _ -> None in
    let outs = mapfilter (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),_),Comb(Const("bytes",_),ar))),s')),_)
          when s' = s ->
            (match lens_of(snd(dest_pair ar)) with
               Some(j,ls) -> (snd(dest_pair ar),j,ls)
             | None -> fail())
      | _ -> fail()) asl in
    let bound (n,j,ls) =
      let bnd = mk_binop `(<=):num->num->bool` n
                  (mk_binop `(+):num->num->num` j
                     (mk_small_numeral(2 * length ls))) in
      if have bnd then ALL_TAC else
      let lenbs = filter (fun th -> let t = concl th in
        is_binary "<=" t && mem (lhand t) ls && rand t = `2`) facts in
      let bth = TAC_PROOF(([],bnd),
        MAP_EVERY (MP_TAC o ASSUME o concl) lenbs THEN ARITH_TAC) in
      ASSUME_TAC(itlist PROVE_HYP lenbs bth) in
    let vals = setify(itlist (fun (_,th) acc ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),v)
          when s' = s ->
            find_terms (fun t -> match t with
              Comb(Const("word",_),Comb(Comb(Const("+",_),_),
                   Comb(Comb(Const("*",_),k),_))) -> k = `256`
            | _ -> false) v @ acc
      | _ -> acc) asl []) in
    let small v =
      let lt = mk_binop `(<):num->num->bool` (rand v) `65536` in
      if have lt then ALL_TAC else
      try ASSUME_TAC(find (fun th -> concl th = lt) facts)
      with Failure _ -> ALL_TAC in
    (MAP_EVERY bound outs THEN MAP_EVERY small vals) gl;;

(* ------------------------------------------------------------------------- *)
(* The body from 0x20a8 to its next iteration or, through the stores done    *)
(* again at 0x2400, the head of the next round (FL2_BODY).                   *)
(* ------------------------------------------------------------------------- *)

(*** The conjuncts of the post of the body, by their form ***)

let fl2_is_numrel t =
  exists (fun op -> is_binary op t) ["<";"<=";"="] &&
  type_of(lhand t) = `:num` &&
  not(can (find_term (fun u -> is_const u && fst(dest_const u) = "FST")) t);;

let fl2_is_ptr t =
  is_eq t &&
  (match lhs t with
     Comb(Comb(Const("read",_),c),_) ->
       (match rhs t with
          Comb(Comb(Const("word_add",_),Var(n,_)),_) ->
            String.length n = 3 && String.sub n 0 2 = "op"
        | _ -> false)
   | _ -> false);;

let fl2_is_cont t =
  is_eq t &&
  (match rhs t with
     Comb(Comb(Const("word_shl",_),_),_) -> true
   | _ -> false);;

let fl2_is_pos t =
  is_eq t && (match lhs t with Comb(Const("FST",_),_) -> true | _ -> false);;

let FL2_CONJ_TAC : tactic =
  fun (asl,w as gl) ->
    (FIRST [FIRST_ASSUM ACCEPT_TAC;
            ASM_REWRITE_TAC[] THEN NO_TAC;
            (if fl2_is_numrel w then FL_ARITH_TAC else NO_TAC);
            (if fl2_is_ptr w then
               ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN AP_TERM_TAC THEN
               AP_TERM_TAC THEN ARITH_TAC
             else NO_TAC);
            (if fl2_is_cont w then
               CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
               FIRST_ASSUM ACCEPT_TAC
             else NO_TAC);
            (if fl2_is_pos w then ASM_REWRITE_TAC[] THEN FL_ARITH_TAC
             else NO_TAC)]) gl;;

(*** The end of the body: the steps of the decoding, the final state, the ***)
(*** counts decoded, the case of the loop and the streams                 ***)

let FL2_POST_TAC (s:term) (loop:bool) : tactic =
  FL2_DECODE5_TAC `u0:num` `p0:num` `j0:num` THEN
  FL2_DECODE5_TAC `u1:num` `p1:num` `j1:num` THEN
  FL2_DECODE5_TAC `u2:num` `p2:num` `j2:num` THEN
  FL2_DECODE5_TAC `u3:num` `p3:num` `j3:num` THEN
  FL_EXPAND_POST_TAC THEN FL2_FINAL_TAC THEN
  (fun (asl,w as gl) ->
     if is_conj w then
       (CONJ_TAC THENL
         [ALL_TAC; FL2_MEMSAFE_FACTS_TAC THEN MONOTONE_MAYCHANGE_TAC]) gl
     else ALL_TAC gl) THEN
  W(fun (asl,w) -> MAP_EVERY EXISTS_TAC (fl2_new_counts asl s)) THEN
  CONJ_TAC THENL [REPEAT CONJ_TAC THEN FL_ARITH_TAC; ALL_TAC] THEN
  (if loop then
     DISJ1_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]
   else
     DISJ2_TAC THEN CONJ_TAC THENL
      [REWRITE_TAC[GSYM NOT_LT] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  FL2_STREAM_WITNESS_TAC s THEN
  REPEAT CONJ_TAC THEN FL2_CONJ_TAC;;

(*** The test at 0x23fc with the count of stream 3 after the body ***)

let FL2_TEST_CASES_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let cands = mapfilter (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),_),Comb(Const("bytes",_),ar))),s')),_)
          when s' = s && fst(dest_pair ar) = `op3:int64` -> snd(dest_pair ar)
      | _ -> fail()) asl in
    let n x = length(striplist (dest_binop `(+):num->num->num`) x) in
    let j3' = itlist (fun c b -> if n c > n b then c else b) cands `j3:num` in
    FL2_TEST_TAC j3' gl;;

let FL2_BODY_SIM_TAC =
  ZSTD_INTRO_TAC THEN
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v) fl2_uvars THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `7 <= u0 /\ 7 <= u1 /\ 7 <= u2 /\ 7 <= u3 /\
                j0 + 10 <= sz0 /\ j1 + 10 <= sz1 /\ j2 + 10 <= sz2 /\
                j3 + 10 <= sz3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`7 * m <= u0`; `7 * m <= u1`; `7 * m <= u2`;
                           `7 * m <= u3`; `1 <= m`; `j0 + 10 * m <= sz0`;
                           `j1 + 10 * m <= sz1`; `j2 + 10 * m <= sz2`;
                           `j3 + 10 * m <= sz3`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (fun gl -> fl2_counter := 0; ALL_TAC gl) THEN
  FL2_NSTEPS_TAC (1--213);;

let FL2_BODY_TAC =
  FL2_BODY_SIM_TAC THEN FL2_TEST_CASES_TAC THENL
   [FL2_STEP_TAC 214 THEN FL2_POST_TAC `s214:armstate` true;
    FL2_STEP_TAC 214 THEN FL2_HALF_TAC THEN FL2_AFTER_FACTS_TAC THEN
    MAP_EVERY (fun k -> FL2_STEP_TAC k THEN FL2_NORM_NOHIDE_TAC)
      (215--230) THEN
    FL2_POST_TAC `s230:armstate` false];;

let FL2_BODY = prove(fl2_body_goal,FL2_BODY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The return: the copies of the arguments in the frame stored back at       *)
(* 0x246c (FL2_EXIT0), after the registers are copied to them at the exit at *)
(* 0x2440 after a round (FL2_EXIT).                                          *)
(* ------------------------------------------------------------------------- *)

(*** The return: the registers restored, and for each stream its pointer, ***)
(*** output pointer and container in the arguments, after jk symbols     ***)

let fl2_field n =
  if n = 0 then `args:int64`
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,`args:int64`),
               mk_comb(`word:num->int64`,mk_small_numeral n));;

let fl2_copy_stream (ipa,opa,ca) k =
  let n = string_of_int k in
  let u = mk_var("u"^n,`:num`) and sk = mk_var("s"^n,`:num`)
  and op = mk_var("op"^n,`:int64`) and d = mk_var("sz"^n,`:num`) in
  subst [ipa,`aip:int64`; opa,`aop:int64`; ca,`abits:int64`;
         u,`u:num`; op,`op:int64`; fl2_jv k,`j:num`; d,`d:num`;
         fl_cont u sk,`c:int64`; fl2_stream_core k,`core:bool`]
   `read (memory :> bytes64 aip) (s:armstate) =
    word_add (ilowest:int64) (word u) /\
    read (memory :> bytes64 aop) s = word_add (op:int64) (word j) /\
    read (memory :> bytes64 abits) s = (c:int64) /\ core /\ j <= d`;;

let fl2_out_stream k =
  fl2_copy_stream (fl2_field(8 * k),fl2_field(32 + 8 * k),
                   fl2_field(64 + 8 * k)) k;;

let fl2_top_post =
  let ex = list_mk_exists(fl2_jvars @ fl2_uvars,
             list_mk_conj(map fl2_out_stream [0;1;2;3])) in
  with_memsafe fl2_rr fl2_wr (mk_abs(`s:armstate`,list_mk_conj
   [`read PC s = returnaddress /\ read SP s = stackpointer /\
     read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
     read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
     read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
     read X28 s = x28 /\ read X29 s = x29 /\ read X30 s = returnaddress`;
    ex]));;

(*** The exit at 0x246c, with the streams in their copies in the frame ***)

let fl2_local_stream k =
  fl2_copy_stream (fl2_spk(288 + 8 * k),fl2_spk(192 + 8 * k),
                   fl2_spk(256 + 8 * k)) k;;

let fl2_exit0_pre =
  let body = list_mk_conj
   ([`read PC s = word(pc + 0x246c)`; fl2_common;
     `read X10 s = word_add args (word 64) /\
      read X12 s = word_add args (word 32) /\ read X7 s = args`;
     mk_eq(`read X13 s`,fl2_spk 288); mk_eq(`read X11 s`,fl2_spk 256)] @
    map fl2_local_stream [0;1;2;3]) in
  with_memsafe fl2_rr fl2_wr
    (list_mk_abs(fl2_jvars @ [`s:armstate`],list_mk_exists(fl2_uvars,body)));;

let fl2_exit0_goal = mk_fl2_goal fl2_jvars
  (mk_abs(`s:armstate`,list_mk_comb(fl2_exit0_pre,fl2_jvars @ [`s:armstate`])))
  fl2_top_post;;

(*** The exit at 0x2440 after a round (w18 = 1), with the streams in ***)
(*** registers, as at the head of a round                            ***)

let fl2_exit_pre = mk_fl2_round 0x2440 `word 1:int64` [];;

let fl2_exit_goal = mk_fl2_goal fl2_jvars
  (mk_abs(`s:armstate`,list_mk_comb(fl2_exit_pre,fl2_jvars @ [`s:armstate`])))
  fl2_top_post;;

(*** The exits ***)

let FL2_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 320)) (word 320):int64 =
  stackpointer`;;

let FL2_POST_EXIT_TAC =
  ASM_REWRITE_TAC[FL2_SP_RESTORE] THEN
  MAP_EVERY EXISTS_TAC (fl2_jvars @ fl2_uvars) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN REWRITE_TAC[];;

(*** 0x246c: the copies in the frame to the arguments, the registers ***)
(*** restored, the return                                            ***)

let FL2_EXIT0 = prove
 (fl2_exit0_goal,
  ZSTD_INTRO_TAC THEN
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v) fl2_uvars THEN
  PUFF_INIT_TAC "s0" THEN
  FL_JOIN128_TAC (map fl2_spk [256; 272; 288; 304; 192; 208]) THEN
  FL2_STEPS_TAC (1--7) THEN FL_SPLIT128_TAC THEN
  FL2_STEPS_TAC (8--14) THEN PUFF_FINAL_TAC THEN FL2_POST_EXIT_TAC);;

(*** 0x2440 after a round: the streams copied from the registers to the ***)
(*** frame, and on to 0x246c                                            ***)

let FL2_PRE_TAC =
  MAP_EVERY EXISTS_TAC fl2_uvars THEN MEMSAFE_ELIM_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[];;

let FL2_EXIT = prove
 (fl2_exit_goal,
  ZSTD_INTRO_TAC THEN
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v) fl2_uvars THEN
  PUFF_INIT_TAC "s0" THEN FL2_STEPS_TAC (1--11) THEN
  ZSTD_CONTINUE_TAC FL2_EXIT0 [] THEN FL2_PRE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The head of a round at 0x2008: the number of iterations, by               *)
(* multiplications for the divisions by 7 and 10, the checks and the exit,   *)
(* for any w18 and copies of the stream pointers and containers in the frame *)
(* (FL2_NEXT_G), and after the first round (FL2_NEXT).                       *)
(* ------------------------------------------------------------------------- *)

(*** The division by 10 of the fast loop, by multiplication ***)

let DIV10_MAGIC = prove
 (`!b. b < 2 EXP 64
       ==> ((b * 14757395258967641293) DIV 2 EXP 64) DIV 8 = b DIV 10`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = (b * 14757395258967641293) DIV 2 EXP 64` THEN
  MP_TAC(SPECL [`b * 14757395258967641293`; `2 EXP 64`] DIVISION) THEN
  ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:num`; `10`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `q = b DIV 10` THEN ABBREV_TAC `r = b MOD 10` THEN STRIP_TAC THEN
  UNDISCH_TAC `b < 2 EXP 64` THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** The head of a round at 0x2008: the number of iterations m, the ***)
(*** smallest of u0 / 7 and (szk - jk) / 10, and if it is not 0 and ***)
(*** the pointers are in order the loop goes on, otherwise it ends  ***)
(*** at 0x2440. For the first round too: any w18, and the copies of ***)
(*** the stream pointers and containers in the frame (at [288] and  ***)
(*** [256], which the head does not change) as variables            ***)

let fl2_beta t = rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let fl2_copy_vars =
  map (fun k -> mk_var("ci"^string_of_int k,`:int64`)) [0;1;2;3] @
  map (fun k -> mk_var("cb"^string_of_int k,`:int64`)) [0;1;2;3];;

let fl2_copies = list_mk_conj
  (map2 (fun k v -> fl2_stack_fact(k,v))
        [288; 296; 304; 312; 256; 264; 272; 280] fl2_copy_vars);;

let fl2_round_g = mk_fl2_round 0x2008 `w18:int64` [fl2_copies]
and fl2_exit_g = mk_fl2_round 0x2440 `w18:int64` [fl2_copies];;

let fl2_next_post exitp =
  mk_abs(`s:armstate`,
     mk_disj(list_mk_exists([`m:num`; `L:num`],
               mk_conj(`1 <= m`,
                 list_mk_comb(fl2_body_pre,
                   fl2_jvars @ [`m:num`; `L:num`; `s:armstate`]))),
             exitp));;

let fl2_next_g_goal = fl2_beta(mk_fl2_goal
  (fl2_jvars @ `w18:int64` :: fl2_copy_vars)
  (mk_abs(`s:armstate`,list_mk_comb(fl2_round_g,fl2_jvars @ [`s:armstate`])))
  (fl2_next_post(list_mk_comb(fl2_exit_g,fl2_jvars @ [`s:armstate`]))));;

(*** The divisions by 10 in the normal form of the steps ***)

let FL2_DIV10_NUM = prove
 (`!d. d < 2 EXP 64
       ==> ((d * 14757395258967641293) DIV 18446744073709551616) DIV 8 =
           d DIV 10`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:num` DIV10_MAGIC) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let FL2_DIV10_FACTS_TAC =
  MAP_EVERY (fun (sz,j) ->
    let d = mk_binop `(-):num->num->num` sz j in
    let lt = mk_binop `(<):num->num->bool` d `2 EXP 64` in
    SUBGOAL_THEN lt (fun th -> ASSUME_TAC th THEN
                               ASSUME_TAC(MP (SPEC d FL2_DIV10_NUM) th)) THENL
     [FL2_USE_ARITH_TAC [`val(op0:int64) + sz0 + sz1 + sz2 + sz3 < 2 EXP 64`];
      ALL_TAC])
   [`sz0:num`,`j0:num`; `sz1:num`,`j1:num`; `sz2:num`,`j2:num`;
    `sz3:num`,`j3:num`];;

let FL2_NEXT_NORM_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let c = `14757395258967641293` in
    let ths = mapfilter (fun (_,th) -> let t = concl th in
      if is_eq t &&
         (match lhs t with Comb(Comb(Const("DIV",_),_),_) -> true
                         | _ -> false) &&
         can (find_term ((=) c)) (lhs t)
      then th else fail()) asl in
    let rule = REWRITE_RULE ths in
    RULE_ASSUM_TAC(fun th -> if free_in s (concl th) then rule th else th) gl;;

(*** The csel of the minimum (steps 24, 39, 54 and 69) simulated alone, ***)
(*** and its value as the MIN, with the bounds of the numbers compared ***)

let FL2_MIN_LT64 = prove
 (`!x y. x < 2 EXP 64 ==> MIN x y < 2 EXP 64`,
  REWRITE_TAC[MIN] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_ARITH_TAC);;

let FL2_DIV_LT64 = prove
 (`!x k. x < 2 EXP 64 ==> x DIV k < 2 EXP 64`,
  MESON_TAC[DIV_LE; LET_TRANS]);;

let FL2_CSEL_STEP_TAC n =
  ARM_STEPS_TAC FL2_EXEC [n] THEN
  W(fun (asl,w) ->
    let s = rand w in
    let rd = list_mk_icomb "read" [`X7`; s] in
    let v = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
              is_eq t && lhs t = rd) asl))) in
    let _,(wa,wb) = dest_cond v in
    let a = rand wa and b = rand wb in
    let lt t = mk_binop `(<):num->num->bool` t `2 EXP 64` in
    let bnd = REPEAT(MATCH_MP_TAC FL2_MIN_LT64 ORELSE
                     MATCH_MP_TAC FL2_DIV_LT64) THEN
              FIRST_ASSUM ACCEPT_TAC in
    SUBGOAL_THEN (mk_conj(lt a,lt b))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [a; b] FL_CSEL_MIN) th]))
    THENL [CONJ_TAC THEN bnd; ALL_TAC]);;

let FL2_NSTEPS_NEXT_TAC ns =
  MAP_EVERY (fun n -> if mem n [24; 39; 54; 69] then FL2_CSEL_STEP_TAC n
                      else FL2_STEP_TAC n THEN FL2_NEXT_NORM_TAC) ns;;

(*** The room of the output of each stream as the difference of its end ***)
(*** and its output pointer                                             ***)

let FL2_ROOM_TAC (opa,opb,sz,j) =
  let t = subst [opa,`a:int64`; opb,`b:int64`; sz,`d:num`; j,`j:num`]
    `word_sub b (word_add a (word j)) = word(d - j):int64` in
  let h = subst [opa,`a:int64`; opb,`b:int64`; sz,`d:num`]
    `word_add a (word d) = b:int64` in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME h)) THEN MATCH_MP_TAC FL_SUB_OP THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC];;

(*** The values of the stream pointers, for their checks ***)

let FL2_IPVAL_TAC =
  MAP_EVERY (fun u ->
    let t = subst [u,`u:num`]
      `val(word_add ilowest (word u):int64) = val(ilowest:int64) + u` in
    SUBGOAL_THEN t ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_ADD_LT THEN
      FL2_USE_ARITH_TAC [subst [u,`u:num`] `u + 8 <= LENGTH(blk:byte list)`;
        `val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`];
      ALL_TAC])
  [`u0:num`; `u1:num`; `u2:num`; `u3:num`];;

(*** The exit of a round at 0x2440, and the checks of the order of the ***)
(*** stream pointers from step k                                       ***)

let FL2_NEXT_EXIT_TAC =
  FL_EXPAND_POST_TAC THEN FL2_FINAL_TAC THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC fl2_uvars THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[];;

let FL2_CHECKS_TAC k pass_tac fail_tac =
  ASM_CASES_TAC `u0 <= u1` THENL
   [ASM_CASES_TAC `u1 <= u2` THENL
     [ASM_CASES_TAC `u2 <= u3` THENL
       [FL2_STEPS_TAC (k--(k+8)) THEN pass_tac;
        FL2_STEPS_TAC (k--(k+5)) THEN fail_tac];
      FL2_STEPS_TAC (k--(k+3)) THEN fail_tac];
    FL2_STEPS_TAC (k--(k+1)) THEN fail_tac];;

let FL2_NEXT_PASS_TAC =
  FL_EXPAND_POST_TAC THEN FL2_FINAL_TAC THEN
  DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`m:num`; `j3 + m + 4 * m`] THEN
  CONJ_TAC THENL [UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC fl2_uvars THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(m = 0)`; `7 * m <= u0`; `u0 <= u1`; `u1 <= u2`; `u2 <= u3`] THEN
  ARITH_TAC;;

(*** The number of iterations m and its bounds ***)

let FL2_ITERS_TAC =
  ABBREV_TAC `m = MIN (MIN (MIN (MIN (u0 DIV 7) ((sz0 - j0) DIV 10))
                        ((sz1 - j1) DIV 10)) ((sz2 - j2) DIV 10))
                   ((sz3 - j3) DIV 10)` THEN
  SUBGOAL_THEN `7 * m <= u0 /\ j0 + 10 * m <= sz0 /\ j1 + 10 * m <= sz1 /\
                j2 + 10 * m <= sz2 /\ j3 + 10 * m <= sz3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    MP_TAC(SPECL [`u0:num`; `7`] DIV_MUL_LE) THEN
    MP_TAC(SPECL [`sz0 - j0:num`; `10`] DIV_MUL_LE) THEN
    MP_TAC(SPECL [`sz1 - j1:num`; `10`] DIV_MUL_LE) THEN
    MP_TAC(SPECL [`sz2 - j2:num`; `10`] DIV_MUL_LE) THEN
    MP_TAC(SPECL [`sz3 - j3:num`; `10`] DIV_MUL_LE) THEN
    FL2_USE_ARITH_TAC [`j0 <= sz0`; `j1 <= sz1`; `j2 <= sz2`; `j3 <= sz3`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `m:num`
                          then ALL_TAC else NO_TAC) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th -> let t = concl th in
    can (find_term ((=) `14757395258967641293`)) t ||
    (is_eq t && (match lhs t with
                   Comb(Comb(Const("word_sub",_),_),_) -> true
                 | _ -> false))) THEN
  HUF_HIDE_SUB_TAC;;

let FL2_NEXT_TAC =
  ZSTD_INTRO_TAC THEN
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v) fl2_uvars THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  FL2_STEPS_TAC (1--11) THEN
  SUBGOAL_THEN `u0 < 2 EXP 64` ASSUME_TAC THENL
   [FL2_USE_ARITH_TAC [`u0 + 8 <= LENGTH(blk:byte list)`;
      `val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `u0:num` FL_DIV7)
                                 (ASSUME `u0 < 2 EXP 64`)]) THEN
  MAP_EVERY FL2_ROOM_TAC [`op0:int64`,`op1:int64`,`sz0:num`,`j0:num`;
                          `op1:int64`,`op2:int64`,`sz1:num`,`j1:num`;
                          `op2:int64`,`op3:int64`,`sz2:num`,`j2:num`;
                          `op3:int64`,`oend:int64`,`sz3:num`,`j3:num`] THEN
  FL2_DIV10_FACTS_TAC THEN FL2_NSTEPS_NEXT_TAC (12--71) THEN
  FL2_ITERS_TAC THEN FL2_STEPS_TAC (72--74) THEN
  ASM_CASES_TAC `m = 0` THENL
   [FL_SUBST_ZERO_TAC `m:num` THEN FL2_STEPS_TAC (75--76) THEN
    FL2_NEXT_EXIT_TAC;
    SUBGOAL_THEN
     `val(word_add op3 (word (j3 + m + 4 * m)):int64) =
      val(op3:int64) + j3 + m + 4 * m /\
      val(word_add op3 (word j3):int64) = val(op3:int64) + j3`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`op0:int64`; `op1:int64`; `op2:int64`; `op3:int64`;
                    `sz0:num`; `sz1:num`; `sz2:num`; `sz3:num`]
                   FL2_VAL_OPS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_ADD_LT THEN
      FL2_USE_ARITH_TAC [`val(op3:int64) = val(op0:int64) + sz0 + sz1 + sz2`;
        `val(op0:int64) + sz0 + sz1 + sz2 + sz3 < 2 EXP 64`;
        `j3 + 10 * m <= sz3`];
      ALL_TAC] THEN
    FL2_STEPS_TAC (75--76) THEN FL2_IPVAL_TAC THEN
    FL2_CHECKS_TAC 77 FL2_NEXT_PASS_TAC FL2_NEXT_EXIT_TAC];;

let FL2_NEXT_G = prove(fl2_next_g_goal,FL2_NEXT_TAC);;

(*** After the first round: w18 = 1 and the copies whatever they are, and ***)
(*** the exit through 0x2440 to the return                                ***)

let fl2_next_goal = fl2_beta(mk_fl2_goal fl2_jvars
  (mk_abs(`s:armstate`,list_mk_comb(fl2_round,fl2_jvars @ [`s:armstate`])))
  (fl2_next_post(mk_comb(fl2_top_post,`s:armstate`))));;

let ENSURES_PRE_DISJ = prove
 (`!(P1:A->bool) P2 Q C.
        ensures step P1 Q C /\ ensures step P2 Q C
        ==> ensures step (\s. P1 s \/ P2 s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let ENSURES_PRE_EXISTS = prove
 (`!(P:B->A->bool) Q C.
        (!x. ensures step (P x) Q C) ==> ensures step (\s. ?x. P x s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

(*** The precondition beta-reduced, and an existential of it as a ***)
(*** variable                                                     ***)

let FL2_PRE_BETA_TAC =
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV(TOP_DEPTH_CONV BETA_CONV))));;

let FL2_PRE_EXISTS_TAC v =
  MATCH_MP_TAC ENSURES_PRE_EXISTS THEN X_GEN_TAC v THEN FL2_PRE_BETA_TAC;;

let FL2_NEXT = prove
 (fl2_next_goal,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:armstate`,list_mk_exists(fl2_copy_vars,
    fl2_beta(list_mk_comb(subst [`word 1:int64`,`w18:int64`] fl2_round_g,
                          fl2_jvars @ [`s:armstate`]))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    MAP_EVERY (fun k -> EXISTS_TAC (subst [fl2_spk k,`a:int64`]
                 `read (memory :> bytes64 a) (s:armstate)`))
     [288; 296; 304; 312; 256; 264; 272; 280] THEN
    MAP_EVERY EXISTS_TAC fl2_uvars THEN ASM_REWRITE_TAC[];
    MAP_EVERY FL2_PRE_EXISTS_TAC fl2_copy_vars] THEN
  W(fun (asl,w) ->
    let th = INST [`word 1:int64`,`w18:int64`] (SPEC_ALL FL2_NEXT_G) in
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC (rand(rator(rand(concl th)))) THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; FL_ACCEPT_TAC th; ALL_TAC]) THEN
  MATCH_MP_TAC ENSURES_PRE_DISJ THEN CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      SUBSUMED_ID_MAYCHANGE_TAC];
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC fl2_top_post THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (mk_abs(`s:armstate`,fl2_beta(list_mk_comb(fl2_exit_pre,
                    fl2_jvars @ [`s:armstate`])))) THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC fl2_uvars THEN ASM_REWRITE_TAC[];
        FL_ACCEPT_TAC(SPEC_ALL FL2_EXIT)]]]);;

(* ------------------------------------------------------------------------- *)
(* The loop from 0x20a8 to the return, by induction on the room left in the  *)
(* output of the last stream (FL2_LOOP).                                     *)
(* ------------------------------------------------------------------------- *)

(*** The loop from 0x20a8 to the return, by induction on sz3 - j3 ***)

let fl2_loop_goal = fl2_beta(mk_fl2_goal_hyps [`1 <= m`]
  (fl2_jvars @ [`m:num`; `L:num`])
  (mk_abs(`s:armstate`,
     list_mk_comb(fl2_body_pre,fl2_jvars @ [`m:num`; `L:num`; `s:armstate`])))
  fl2_top_post);;

(*** The induction hypothesis for the counts jt, iterations mt and ***)
(*** limit lt, from the measure and the bounds of the counts       ***)

let FL2_LOOP_ARITH_TAC : tactic =
  fun (asl,w as gl) ->
    let cands = [`sz3 - j3 = n`; `j3 + 5 <= j3'`; `j3' <= j3 + 10`;
                 `j3 + 10 * m <= sz3`; `1 <= m`; `j3' < L`;
                 `L <= j3 + 5 * m`; `1 <= m'`] in
    let ths = mapfilter (fun t -> snd(find (fun (_,th) -> concl th = t) asl))
                cands in
    (MAP_EVERY MP_TAC ths THEN ARITH_TAC) gl;;

let FL2_LOOP_IH_TAC (jt:term list) (mt:term) (lt:term) =
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_binop `(-):num->num->num` `sz3:num`
                                 (el 3 jt))) THEN
  ANTS_TAC THENL [FL2_LOOP_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL (jt @ [mt; lt])) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [REFL_TAC; FL2_LOOP_ARITH_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  GEN_TAC THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;;

let FL2_LOOP = prove
 (fl2_loop_goal,
  ZSTD_INTRO_TAC THEN
  W(fun (asl,w) ->
    let gen = list_mk_forall(`n:num` :: fl2_jvars @ [`m:num`; `L:num`],
                mk_imp(`sz3 - j3 = n /\ 1 <= m`,w)) in
    SUBGOAL_THEN gen (fun th -> MATCH_MP_TAC th THEN
                                EXISTS_TAC `sz3 - j3:num` THEN
                                ASM_REWRITE_TAC[])) THEN
  UNDISCH_TAC `1 <= m` THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC (fl2_jvars @ [`m:num`; `L:num`]) THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRE_FACT THEN
  EXISTS_TAC `j3 + 10 * m <= sz3 /\ L <= j3 + 5 * m` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (rand(rator(rand(snd(strip_forall(concl FL2_BODY)))))) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; FL_ACCEPT_TAC(SPEC_ALL FL2_BODY); ALL_TAC] THEN
  MAP_EVERY FL2_PRE_EXISTS_TAC fl2_jvars' THEN
  MATCH_MP_TAC ENSURES_PRE_PURE THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRE_DISJ THEN CONJ_TAC THEN
  MATCH_MP_TAC ENSURES_PRE_PURE THEN DISCH_TAC THEN FL2_PRE_BETA_TAC THENL
   [FL2_LOOP_IH_TAC fl2_jvars' `m - 1` `L:num`;
    W(fun (asl,w) ->
      let th = INST (zip fl2_jvars' fl2_jvars) (SPEC_ALL FL2_NEXT) in
      let q = rand(rator(rand(concl th))) in
      MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q THEN
      REPEAT CONJ_TAC THENL
       [MAYCHANGE_IDEMPOT_TAC; FL_ACCEPT_TAC th; ALL_TAC]) THEN
    MATCH_MP_TAC ENSURES_DISJ_DONE THEN
    CONJ_TAC THENL [SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
    X_GEN_TAC `m':num` THEN FL2_PRE_BETA_TAC THEN
    FL2_PRE_EXISTS_TAC `L':num` THEN
    MATCH_MP_TAC ENSURES_PRE_PURE THEN DISCH_TAC THEN
    FL2_LOOP_IH_TAC fl2_jvars' `m':num` `L':num`]);;

(* ------------------------------------------------------------------------- *)
(* The entry at 0x1f60: the frame, the copies of the arguments, the first    *)
(* round with w18 = 0 and its exit (FL2_EXIT_FIRST), and the whole function  *)
(* (FL2_TOP and HUF_DECOMPRESS4X2_FAST_C_LOOP_CORRECT).                      *)
(* ------------------------------------------------------------------------- *)

(*** The entry at 0x1f60: the arguments, the streams with their pointers ***)
(*** and containers in the arguments, the registers to be saved           ***)

let fl2_args_in =
 `read (memory :> bytes64 (word_add args (word 32))) s = op0 /\
  read (memory :> bytes64 (word_add args (word 40))) s = op1 /\
  read (memory :> bytes64 (word_add args (word 48))) s = op2 /\
  read (memory :> bytes64 (word_add args (word 56))) s = op3 /\
  read (memory :> bytes64 (word_add args (word 96))) s = dt /\
  read (memory :> bytes64 (word_add args (word 104))) s = ilowest /\
  read (memory :> bytes64 (word_add args (word 112))) s = oend`;;

let fl2_args_streams =
  let one k =
    let n = string_of_int k in
    let u = mk_var("u"^n,`:num`) and x = mk_var("s"^n,`:num`)
    and p = mk_var("p"^n,`:num`) in
    subst [fl2_field(8 * k),`a8:int64`; fl2_field(64 + 8 * k),`a64:int64`;
           u,`u:num`; x,`x:num`; fl_cont u x,`c:int64`; p,`p:num`]
     `read (memory :> bytes64 a8) s = word_add (ilowest:int64) (word u) /\
      read (memory :> bytes64 a64) s = (c:int64) /\
      p = 8 * u + 64 - x /\ x <= 8 /\ u + 8 <= LENGTH(blk:byte list)` in
  list_mk_conj(map one [0;1;2;3]);;

let fl2_top_pre =
  let body = list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x1f60) /\ read SP s = stackpointer /\
     read X30 s = returnaddress /\ read X0 s = args /\
     read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
     read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
     read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
     read X28 s = x28 /\ read X29 s = x29 /\
     read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
     num_of_bytelist blk /\
     read (memory :> bytes(dt,8192)) s =
     num_of_bytelist(huf_dtable2 ws ml 11)`;
    fl2_args_in;
    list_mk_exists(fl2_uvars,fl2_args_streams);
    `read events s = e`] in
  mk_abs(`s:armstate`,body);;

let fl2_top_goal = mk_fl2_goal [] fl2_top_pre fl2_top_post;;

(*** The first round: w18 = 0, no symbols decoded, and the copies of the ***)
(*** stream pointers and containers those at the entry, of the streams   ***)
(*** at ui, si                                                           ***)

let fl2_ivars =
  map (fun k -> mk_var("ui"^string_of_int k,`:num`)) [0;1;2;3] @
  map (fun k -> mk_var("si"^string_of_int k,`:num`)) [0;1;2;3];;

let fl2_init_insts =
  let ui k = mk_var("ui"^string_of_int k,`:num`)
  and si k = mk_var("si"^string_of_int k,`:num`) in
  (`word 0:int64`,`w18:int64`) :: map (fun k -> `0`,fl2_jv k) [0;1;2;3] @
  map2 (fun k v -> mk_comb(`word_add (ilowest:int64)`,
                           mk_comb(`word:num->int64`,ui k)),v)
       [0;1;2;3] (fst(chop_list 4 fl2_copy_vars)) @
  map2 (fun k v -> fl_cont (ui k) (si k),v)
       [0;1;2;3] (snd(chop_list 4 fl2_copy_vars));;

let fl2_init_facts = list_mk_conj(map (fun k ->
  let n = string_of_int k in
  subst [mk_var("ui"^n,`:num`),`u:num`; mk_var("si"^n,`:num`),`x:num`;
         mk_var("p"^n,`:num`),`p:num`]
   `p = 8 * u + 64 - x /\ x <= 8 /\ u + 8 <= LENGTH(blk:byte list)`)
  [0;1;2;3]);;

(*** The exit at 0x2440 after the first round (w18 = 0): the copies of ***)
(*** the entry to the arguments, and the return                        ***)

let fl2_exit_first_goal = mk_fl2_goal_hyps [fl2_init_facts] fl2_ivars
  (mk_abs(`s:armstate`,fl2_beta(vsubst fl2_init_insts
     (list_mk_comb(fl2_exit_g,fl2_jvars @ [`s:armstate`])))))
  fl2_top_post;;

let FL2_PRE0_TAC =
  MAP_EVERY EXISTS_TAC fl2_ivars THEN MEMSAFE_ELIM_TAC THEN
  REWRITE_TAC[huf_decode; FST; SND; WORD_ADD_0; ADD_CLAUSES; MULT_CLAUSES;
              READ_MEMORY_BYTES_0; num_of_bytelist; LE_0] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
  ASM_REWRITE_TAC[];;

let fl2_pinsts = map (fun k ->
  let n = string_of_int k in
  subst [mk_var("ui"^n,`:num`),`u:num`; mk_var("si"^n,`:num`),`x:num`]
    `8 * u + 64 - x`,mk_var("p"^n,`:num`)) [0;1;2;3];;

let FL2_EXIT_FIRST = prove
 (fl2_exit_first_goal,
  ZSTD_INTRO_TAC THEN
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v) fl2_uvars THEN
  PUFF_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  FL2_STEPS_TAC (1--5) THEN
  ZSTD_CONTINUE_TAC FL2_EXIT0
    (map (fun v -> `0`,v) fl2_jvars @ fl2_pinsts) THEN
  FL2_PRE0_TAC);;

(*** 0x1f60: the frame, the copies of the arguments, the streams in ***)
(*** registers, and the first round from 0x2008                     ***)

let FL2_TOP = prove
 (fl2_top_goal,
  ZSTD_INTRO_TAC THEN
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v) fl2_ivars THEN
  MATCH_MP_TAC ENSURES_PRE_FACT THEN EXISTS_TAC fl2_init_facts THEN
  CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  W(fun (asl,w) ->
    let th = INST fl2_init_insts (SPEC_ALL FL2_NEXT_G) in
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC (rand(rator(rand(concl th)))) THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC) THENL
   [PUFF_INIT_TAC "s0" THEN
    FL_JOIN128_TAC (map fl2_field [0; 16; 32; 48; 64; 80]) THEN
    FL2_STEPS_TAC (1--21) THEN FL_SPLIT128_TAC THEN
    FL_JOIN128_TAC [fl2_spk 200] THEN
    FL2_STEPS_TAC (22--25) THEN FL_SPLIT128_TAC THEN
    FL2_STEPS_TAC (26--42) THEN
    ZSTD_CONTINUE_WITH_TAC
     (GEN_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[])
     FL2_NEXT_G (fl2_init_insts @ fl2_pinsts) THEN
    FL2_PRE0_TAC;
    MATCH_MP_TAC ENSURES_PRE_DISJ THEN CONJ_TAC THENL
     [FL2_PRE_EXISTS_TAC `m:num` THEN FL2_PRE_EXISTS_TAC `L:num` THEN
      MATCH_MP_TAC ENSURES_PRE_PURE THEN DISCH_TAC THEN
      FL_ACCEPT_TAC(INST (map (fun v -> `0`,v) fl2_jvars)
                         (SPEC_ALL FL2_LOOP));
      FL_ACCEPT_TAC(SPEC_ALL FL2_EXIT_FIRST)]]);;

(*** The fast loop as a subroutine ***)

let fl2_std_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [memory :> bytes(op0,sz0); memory :> bytes(op1,sz1);
             memory :> bytes(op2,sz2); memory :> bytes(op3,sz3);
             memory :> bytes(args,96);
             memory :> bytes(word_sub stackpointer (word 320),320)]`;;

let fl2_std_pre =
  let body = list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x1f60) /\ read SP s = stackpointer /\
     read X30 s = returnaddress /\ read X0 s = args /\
     read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
     num_of_bytelist blk /\
     read (memory :> bytes(dt,8192)) s =
     num_of_bytelist(huf_dtable2 ws ml 11)`;
    fl2_args_in;
    list_mk_exists(fl2_uvars,fl2_args_streams);
    `read events s = e`] in
  mk_abs(`s:armstate`,body);;

let fl2_std_post =
  let ex = list_mk_exists(fl2_jvars @ fl2_uvars,
             list_mk_conj(map fl2_out_stream [0;1;2;3])) in
  let ms = subst [fl2_rr,`rr:(int64#num)list`; fl2_wr,`wr:(int64#num)list`]
   `?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 rr wr` in
  mk_abs(`s:armstate`,
         list_mk_conj [`read PC s = returnaddress`; ex; ms]);;

let fl2_goal =
  let tm = mk_imp(fl2_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; fl2_std_pre; fl2_std_post; fl2_std_frame]) in
  let fvs = frees tm in
  list_mk_forall(filter (fun v -> mem v fvs) fl2_vars,tm);;

let HUF_DECOMPRESS4X2_FAST_C_LOOP_CORRECT = prove
 (fl2_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS] THEN
  ENSURES_PRESERVED_TAC "x19" `X19` THEN
  ENSURES_PRESERVED_TAC "x20" `X20` THEN
  ENSURES_PRESERVED_TAC "x21" `X21` THEN
  ENSURES_PRESERVED_TAC "x22" `X22` THEN
  ENSURES_PRESERVED_TAC "x23" `X23` THEN
  ENSURES_PRESERVED_TAC "x24" `X24` THEN
  ENSURES_PRESERVED_TAC "x25" `X25` THEN
  ENSURES_PRESERVED_TAC "x26" `X26` THEN
  ENSURES_PRESERVED_TAC "x27" `X27` THEN
  ENSURES_PRESERVED_TAC "x28" `X28` THEN
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  W(fun (asl,w) ->
    let th0 = FL_FRAME_RULE(SPEC_ALL FL2_TOP) in
    let hth = TAC_PROOF((asl,lhand(concl th0)),
                REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
    let th = MP th0 hth in
    let [_;p0;q0;c0] = snd(strip_comb(concl th)) in
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c0 THEN
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p0 THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q0 THEN
      CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]]) THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC fl2_uvars;
    MAP_EVERY EXISTS_TAC (fl2_jvars @ fl2_uvars)] THEN
  ASM_REWRITE_TAC[]);;

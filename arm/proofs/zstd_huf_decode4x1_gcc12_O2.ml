(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* zstd's HUF_decompress4X1_usingDTable_internal, the decoding of            *)
(* Huffman-coded literals in four streams with single-symbol tables,         *)
(* compiled by gcc 12 at -O2 for AArch64                                     *)
(* (HUF_DECOMPRESS4X1_USINGDTABLE_CORRECT). For a valid block the result is  *)
(* the size n of the output, with the output at dst; the result is always n  *)
(* or an error code; and when bit 5 of the flags (HUF_flags_disableFast) is  *)
(* set, so that only the slow path runs, it is an error code for a block     *)
(* that is not valid. The fast path sets up its arguments with               *)
(* HUF_DecompressFastArgs_init, decodes with                                 *)
(* HUF_decompress4X1_usingDTable_internal_fast_c_loop and finishes each      *)
(* stream at 0x537c; it does not check that a stream ends exactly at its     *)
(* start, hence the weaker result for invalid blocks.                        *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode4x1_slow_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* A stream within a block decodes from 8 * a + r in the block as on its own *)
(* from r, and a valid stream from the position of the fast path reaches its *)
(* start.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** The decoding of a stream within the block (the fast path decodes on ***)
(*** the whole block from absolute positions): a stream at byte a of the ***)
(*** block decodes the same from 8 * a + r as on its own from r, as long ***)
(*** as no code needs more bits than are left                            ***)

let ZSTD_BIT_SUBLIST = prove
 (`!(blk:byte list) a l i.
        a + l <= LENGTH blk /\ i < 8 * l
        ==> (zstd_bit (zstd_sublist blk a l) i <=> zstd_bit blk (8 * a + i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zstd_bit; LENGTH_ZSTD_SUBLIST] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `8 * a + i < 8 * LENGTH(blk:byte list) /\ i DIV 8 < l /\
                (8 * a + i) MOD 8 = i MOD 8 /\
                (8 * a + i) DIV 8 = a + i DIV 8`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD];
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC];
    ASM_SIMP_TAC[ZSTD_SUBLIST_EL]]);;

let ZSTD_BITS_SUBLIST = prove
 (`!(blk:byte list) a l n p.
        a + l <= LENGTH blk /\ p + n <= 8 * l
        ==> zstd_bits (zstd_sublist blk a l) p n =
            zstd_bits blk (8 * a + p) n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[zstd_bits] THEN REPEAT STRIP_TAC THEN
  BINOP_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC ZSTD_BIT_SUBLIST THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let DIV_LOW_HIGH = prove
 (`!x y n. y < n ==> (y + n * x) DIV n = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `y:num` THEN
  ASM_ARITH_TAC);;

let ZSTD_BACK_SUBLIST = prove
 (`!(blk:byte list) a l q k n.
        a + l <= LENGTH blk /\ q <= 8 * l /\ n <= q /\ n <= k
        ==> zstd_back blk (8 * a + q) k DIV 2 EXP (k - n) =
            zstd_back (zstd_sublist blk a l) q k DIV 2 EXP (k - n)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ZSTD_BACK_TOP; ARITH_RULE `n <= q ==> n <= 8 * a + q`] THEN
  ASM_SIMP_TAC[ZSTD_BITS_SUBLIST; ADD_CLAUSES] THEN
  REWRITE_TAC[ZSTD_BITS_ADD; ADD_CLAUSES] THEN
  SUBGOAL_THEN `(8 * a + q) - n = 8 * a + (q - n)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD; GSYM DIV_DIV]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC DIV_LOW_HIGH THEN
  REWRITE_TAC[ZSTD_BITS_BOUND]);;

(*** The symbol of a state depends only on the bits of its code ***)

let HUF_SYMBOL_PREFIX = prove
 (`!ws ml x y.
        huf_complete ws ml /\ x < 2 EXP ml /\ y < 2 EXP ml /\
        x DIV 2 EXP (EL (huf_symbol ws x) ws - 1) =
        y DIV 2 EXP (EL (huf_symbol ws x) ws - 1)
        ==> huf_symbol ws y = huf_symbol ws x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = huf_symbol ws x` THEN
  SUBGOAL_THEN `s IN huf_present ws` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    MP_TAC(SPECL [`ws:num list`; `x:num`] HUF_SYMBOL) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[huf_complete]) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `s:num`; `y:num`]
    HUF_SYMBOL_CODE) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `s:num`; `x:num`]
    HUF_SYMBOL_CODE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(*** Decoding: positions only go down, and a stream decodes the same in ***)
(*** the block, as long as no code needs more bits than are left         ***)

let HUF_DECODE_POS_LE = prove
 (`!ws ml (st:byte list) q k. FST(SND(huf_decode ws ml st q k)) <= q`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[huf_decode; LE_REFL] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let HUF_DECODE_SUBLIST = prove
 (`!ws ml (blk:byte list) a l r k.
        huf_complete ws ml /\ a + l <= LENGTH blk /\ r <= 8 * l /\
        SND(SND(huf_decode ws ml (zstd_sublist blk a l) r k))
        ==> huf_decode ws ml blk (8 * a + r) k =
            (FST(huf_decode ws ml (zstd_sublist blk a l) r k),
             8 * a + FST(SND(huf_decode ws ml (zstd_sublist blk a l) r k)),
             T)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ABBREV_TAC `st = zstd_sublist (blk:byte list) a l` THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[huf_decode]; ALL_TAC] THEN
  REWRITE_TAC[huf_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; `k:num`]
    HUF_DECODE_POS_LE) THEN
  ABBREV_TAC `p = FST(SND(huf_decode ws ml (st:byte list) r k))` THEN
  DISCH_TAC THEN
  let hc = REWRITE_RULE[huf_complete] (ASSUME `huf_complete ws ml`) in
  ABBREV_TAC `s = huf_symbol ws (zstd_back (st:byte list) p ml)` THEN
  SUBGOAL_THEN `s IN huf_present ws` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    MP_TAC(SPECL [`ws:num list`; `zstd_back (st:byte list) p ml`]
      HUF_SYMBOL) THEN
    REWRITE_TAC[CONJUNCT1 hc; ZSTD_BACK_BOUND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= EL s ws /\ EL s ws <= ml` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `s IN huf_present ws` THEN
      REWRITE_TAC[huf_present; IN_ELIM_THM] THEN ARITH_TAC;
      MATCH_MP_TAC(CONJUNCT2 hc) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `huf_symbol ws (zstd_back blk (8 * a + p) ml) = s`
  SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC HUF_SYMBOL_PREFIX THEN
    EXISTS_TAC `ml:num` THEN ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
    MP_TAC(SPECL [`blk:byte list`; `a:num`; `l:num`; `p:num`; `ml:num`;
                  `(ml + 1) - EL s ws`] ZSTD_BACK_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ml - ((ml + 1) - EL s ws) = EL s ws - 1` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`1 <= EL s ws`; `EL s ws <= ml`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`p <= r`; `r <= 8 * l`; `1 <= EL s ws`] THEN
      ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN UNDISCH_TAC `(ml + 1) - EL s ws <= p` THEN
  ARITH_TAC);;

let HUF_LASTSHIFT_NONZERO_LE = prove
 (`!b:byte. ~(b = word 0) ==> huf_lastshift b <= 8`,
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[huf_lastshift] THEN
  REWRITE_TAC[WORD_CLZ_BITSIZE; DIMINDEX_8] THEN
  SUBGOAL_THEN `~(bitsize(val(b:byte)) = 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[BITSIZE_EQ_0; VAL_EQ_0]; ARITH_TAC]);;

(*** The start of a valid stream is 8 times its length minus the shift ***)
(*** of its last byte                                                   ***)

let HUF_LASTSHIFT_END = prove
 (`!(st:byte list) r.
        zstd_end st r
        ==> ~(LENGTH st = 0) /\ ~(EL (LENGTH st - 1) st = word 0) /\
            r = 8 * LENGTH st - huf_lastshift(EL (LENGTH st - 1) st)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `st:byte list = []` THENL
   [ASM_REWRITE_TAC[zstd_end]; ALL_TAC] THEN
  ASM_SIMP_TAC[ZSTD_END_LAST] THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
  ABBREV_TAC `b = EL (LENGTH(st:byte list) - 1) st` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(b:byte = word 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `1 <= bitsize(val(b:byte)) /\ bitsize(val b) <= 8`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE; ARITH_RULE `1 <= b <=> ~(b = 0)`;
                BITSIZE_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[huf_lastshift; WORD_CLZ_BITSIZE; DIMINDEX_8] THEN
  SUBGOAL_THEN `~(LENGTH(st:byte list) = 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`1 <= bitsize(val(b:byte))`; `bitsize(val(b:byte)) <= 8`] THEN
  ARITH_TAC);;

(*** A valid stream decodes in the block from 8 times its end minus the ***)
(*** shift of its last byte, ending at 8 times its start                ***)

let HUF_STREAM_BLOCK = prove
 (`!ws ml (blk:byte list) a l out.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ a + l <= LENGTH blk /\
        huf_stream ws ml (zstd_sublist blk a l) out
        ==> ~(l = 0) /\ ~(EL (a + l - 1) blk = word 0) /\
            huf_decode ws ml blk
              (8 * (a + l) - huf_lastshift(EL (a + l - 1) blk)) (LENGTH out) =
            (out,8 * a,T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:num` o MATCH_MP HUF_STREAM_END) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HUF_LASTSHIFT_END) THEN
  REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EL (l - 1) (zstd_sublist (blk:byte list) a l) =
                EL (a + l - 1) blk` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ZSTD_SUBLIST_EL; ARITH_RULE `~(l = 0) ==> l - 1 < l`]
    THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `EL (l - 1) (zstd_sublist (blk:byte list) a l) = EL (a + l - 1) blk`])
  THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `zstd_sublist (blk:byte list) a l`;
                `r:num`; `out:byte list`] HUF_STREAM_DECODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `blk:byte list`; `a:num`; `l:num`;
                `r:num`; `LENGTH(out:byte list)`] HUF_DECODE_SUBLIST) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `x - y <= x`] THEN
  SUBGOAL_THEN `8 * (a + l) - huf_lastshift (EL (a + l - 1) blk) =
                8 * a + 8 * l - huf_lastshift (EL (a + l - 1) blk)`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `EL (a + l - 1) (blk:byte list)`
      HUF_LASTSHIFT_NONZERO_LE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(l = 0)` THEN ARITH_TAC;
    REWRITE_TAC[]]);;

(*** The theory for the whole of HUF_decompress4X1_usingDTable_internal: ***)
(*** the fast path decodes each stream of a valid block from the end of  ***)
(*** the stream in the block, and reaches its start                      ***)

let HUF_LASTSHIFT_LE8 = prove
 (`!b:byte. huf_lastshift b <= 8`,
  GEN_TAC THEN ASM_CASES_TAC `b:byte = word 0` THENL
   [ASM_REWRITE_TAC[huf_lastshift; LE_0];
    ASM_SIMP_TAC[HUF_LASTSHIFT_NONZERO_LE]]);;

(*** The positions of the decoding only go down ***)

let HUF_DECODE_POS_MONO = prove
 (`!ws ml (st:byte list) q j k.
        j <= k
        ==> FST(SND(huf_decode ws ml st q k)) <=
            FST(SND(huf_decode ws ml st q j))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
   [SIMP_TAC[LE; LE_REFL];
    REWRITE_TAC[LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[huf_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[] THEN ARITH_TAC]);;

(*** A decoding that ends at 8 * a never went below 8 * a ***)

let HUF_DECODE_START_LE = prove
 (`!ws ml (st:byte list) p j L out a u x.
        huf_decode ws ml st p L = (out,8 * a,T) /\ j <= L /\
        FST(SND(huf_decode ws ml st p j)) = 8 * u + 64 - x
        ==> a <= u + 8`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `p:num`; `j:num`;
                `L:num`] HUF_DECODE_POS_MONO) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(*** A valid stream from a to e in the block, of at least 8 bytes, from  ***)
(*** the position the fast path starts at                                ***)

let HUF_STREAM_FAST = prove
 (`!ws ml (blk:byte list) a l e out.
        huf_complete ws ml /\ LENGTH ws <= 256 /\
        a + l = e /\ 8 <= e /\ e <= LENGTH blk /\
        huf_stream ws ml (zstd_sublist blk a l) out
        ==> huf_decode ws ml blk
              (8 * (e - 8) + 64 - huf_lastshift(EL (e - 1) blk)) (LENGTH out) =
            (out,8 * a,T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `blk:byte list`; `a:num`; `l:num`;
                `out:byte list`] HUF_STREAM_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a + l - 1 = e - 1` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(l = 0)`; `a + l = e`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `8 * (e - 8) + 64 - huf_lastshift(EL (e - 1) (blk:byte list)) =
    8 * e - huf_lastshift(EL (e - 1) blk)`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `EL (e - 1) (blk:byte list)` HUF_LASTSHIFT_LE8) THEN
    UNDISCH_TAC `8 <= e` THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(*** The four streams of a valid block, when the fast path applies ***)

let top_e k = el k fa_ends and top_a k = el k fa_starts;;

let top_p k =
  subst [top_e k,`e:num`]
   `8 * (e - 8) + 64 - huf_lastshift(EL (e - 1) (blk:byte list))`;;

let top_L k = if k = 3 then `n - 3 * q` else `q:num`;;

let top_o k =
  el k [`0`; `q:num`; `2 * q`; `3 * q`];;

let top_fa_ok =
  [`8 <= huf_jump blk 0`; `8 <= huf_jump blk 1`; `8 <= huf_jump blk 2`;
   subst [fa_a3,`a3:num`] `a3 + 8 <= LENGTH(blk:byte list)`];;

let top_hyps =
  [`huf_complete ws ml /\ LENGTH(ws:num list) <= 256`;
   `(n + 3) DIV 4 = q`] @ top_fa_ok;;

let top_dec k =
  list_mk_icomb "huf_decode"
   [`ws:num list`; `ml:num`; `blk:byte list`; top_p k; top_L k];;

let huf_streams4_fast =
  list_mk_forall
   ([`ws:num list`; `ml:num`; `blk:byte list`; `out:byte list`; `n:num`;
     `q:num`],
    mk_imp(list_mk_conj
            (top_hyps @ [`huf_streams4 T ws ml blk out`;
                         `LENGTH(out:byte list) = n`]),
           list_mk_conj (map (fun k ->
             mk_eq(top_dec k,
                   mk_pair(list_mk_icomb "zstd_sublist"
                             [`out:byte list`; top_o k; top_L k],
                           mk_pair(mk_binop `( * ):num->num->num` `8`
                                     (top_a k),`T`))))
             [0;1;2;3])));;

let HUF_STREAMS4_FAST = prove
 (huf_streams4_fast,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_streams4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `LENGTH(out:byte list) = n`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `(n + 3) DIV 4 = q`)) THEN
  let l k = if k = 3 then subst [fa_a3,`a3:num`] `LENGTH(blk:byte list) - a3`
            else mk_comb(`huf_jump blk`,mk_small_numeral k) in
  MAP_EVERY (fun k ->
    MP_TAC(ISPECL [`ws:num list`; `ml:num`; `blk:byte list`; top_a k; l k;
                   top_e k;
                   list_mk_icomb "zstd_sublist"
                    [`out:byte list`; top_o k; top_L k]]
             HUF_STREAM_FAST) THEN
    ASM_REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC; DISCH_TAC])
   [0;1;2;3] THEN
  ASM_REWRITE_TAC[]);;

(*** The bytes of the four segments, when each is what its stream decodes ***)
(*** to if it uses no bits beyond the stream                              ***)

let huf_streams4_fast_result =
  let mk k = mk_var("m"^string_of_int k,`:num`) in
  let imp k =
    let d = top_dec k in
    mk_imp(mk_comb(`SND:num#bool->bool`,
                   mk_comb(`SND:byte list#num#bool->num#bool`,d)),
           mk_eq(mk k,
                 mk_comb(`num_of_bytelist`,
                   mk_comb(`FST:byte list#num#bool->byte list`,d)))) in
  list_mk_forall
   ([`ws:num list`; `ml:num`; `blk:byte list`; `n:num`; `q:num`] @
    map mk [0;1;2;3],
    mk_imp(list_mk_conj(top_hyps @ [`3 * q <= n`] @ map imp [0;1;2;3]),
     `!out. LENGTH out = n /\ huf_streams4 T ws ml blk out
            ==> m0 + 2 EXP (8 * q) * (m1 + 2 EXP (8 * q) *
                                      (m2 + 2 EXP (8 * q) * m3)) =
                num_of_bytelist out`));;

let HUF_STREAMS4_FAST_RESULT = prove
 (huf_streams4_fast_result,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `out:byte list` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `blk:byte list`; `out:byte list`;
                `n:num`; `q:num`] HUF_STREAMS4_FAST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [MP (SPECL [`out:byte list`; `q:num`; `n:num`] ZSTD_SUBLIST_SPLIT4)
       (CONJ (ASSUME `LENGTH(out:byte list) = n`) (ASSUME `3 * q <= n`))] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_ZSTD_SUBLIST]);;

(*** The byte 2 of the header of the table, as a byte of its 32-bit word ***)

let READ_BYTES32_BYTE2 = prove
 (`!(a:int64) s.
     word_subword (read (memory :> bytes32 a) s) (16,8):byte =
     read (memory :> bytes8 (word_add a (word 2))) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  W(fun (asl,w) ->
    let bs = setify(find_terms (fun t ->
               try fst(dest_const(fst(strip_comb t))) = "read" &&
                   type_of t = `:byte`
               with Failure _ -> false) w) in
    MAP_EVERY (fun b -> SPEC_TAC(b,genvar `:byte`)) bs) THEN
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The finish of a stream after the fast loop, at 0x537c.                    *)
(* ------------------------------------------------------------------------- *)

(*** The lookups of the finish of a stream ***)

let FIN_INDEX_ANY = prove
 (`!(y:int64). word_shl (word_ushr y 53) 1 = word (2 * val(word_ushr y 53)) /\
               val(word_ushr y 53) < 2048`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD_USHR; EXP_1] THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  MP_TAC(ISPEC `y:int64` VAL_BOUND_64) THEN ARITH_TAC);;

let FIN_INDEX2 = prove
 (`!(blk:byte list) ofs bc.
     bc < 64 /\ (11 + bc <= 64 \/ ofs = 0)
     ==> word_shl (word_ushr
           (word (2 EXP bc * (num_of_bytelist blk DIV 2 EXP (8 * ofs)) MOD
                  18446744073709551616):int64) 53) 1 =
         word (2 * zstd_back blk (8 * ofs + 64 - bc) 11)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[CONJUNCT1(SPEC_ALL FIN_INDEX_ANY)] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`blk:byte list`; `ofs:num`; `bc:num`; `11`] ZSTD_WINDOW) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC MULT_SYM);;

(*** The finish of a stream after the fast loop, at 0x537c: the segment  ***)
(*** of L bytes at op, of which j were decoded by the fast loop, decoded ***)
(*** to its end by BIT_DStream from the start ilowest of the block, with ***)
(*** the stream from position p in blk (positions from ilowest)          ***)

let fin_rr =
 `[ilowest,LENGTH(blk:byte list); dt,4096; argk,128;
   word_add (word_sub stackpointer (word 496)) (word 448),8]:(int64#num)list`
and fin_wr =
 `[op,L; word_add argk (word 32),8]:(int64#num)list`;;

let fin_hyps = list_mk_conj
 [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
  `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\ 1 <= ml /\ ml <= 11`;
  `8 <= val(ilowest:int64) /\
   val ilowest + LENGTH(blk:byte list) < 2 EXP 64`;
  `MIN q rest = L /\ q < 2 EXP 28 /\ val(op:int64) + rest < 2 EXP 64`;
  `nonoverlapping (op:int64,L) (ilowest,LENGTH(blk:byte list)) /\
   nonoverlapping (op,L) (dt:int64,4096) /\
   nonoverlapping (op,L) (argk:int64,128) /\
   nonoverlapping (op,L)
     (word_add (word_sub stackpointer (word 496)) (word 448),8) /\
   nonoverlapping (op,L) (word pc,32000) /\
   nonoverlapping (word_add argk (word 32),8)
     (word_add (word_sub stackpointer (word 496)) (word 448),8) /\
   nonoverlapping (word_add argk (word 32),8)
     (ilowest,LENGTH(blk:byte list)) /\
   nonoverlapping (word_add argk (word 32),8) (dt,4096) /\
   nonoverlapping (word_add argk (word 32),8) (word pc,32000)`];;

let fin_frame =
 `MAYCHANGE [PC; X1; X2; X3; X4; X6; X7; X8; X11; X12; X13; X14; X15;
             X19] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op,L);
             memory :> bytes(word_add argk (word 32),8)]`;;

let fin_vars =
 [`pc:num`; `stackpointer:int64`; `argk:int64`; `op:int64`; `rest:num`;
  `q:num`; `L:num`; `blk:byte list`; `ilowest:int64`; `dt:int64`;
  `ws:num list`; `ml:num`; `p:num`; `j0:num`; `e:uarch_event list`];;

let mk_fin_goal extra pre post =
  let tm = mk_imp(fin_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; fin_frame]) in
  let vs = fin_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fin_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** The facts that hold all through ***)

let fin_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read X0 s = argk /\ read X5 s = dt /\ read X8 s = word_add op (word L) /\
  read X11 s = word (L - j0) /\
  read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
  num_of_bytelist blk /\
  read (memory :> bytes(dt,4096)) s = num_of_bytelist(huf_dtable ws ml 11) /\
  read (memory :> bytes64 (word_add argk (word 32))) s =
  word_add op (word j0) /\ j0 <= L`;;

(*** At 0x542c, after the segment: the bytes decoded if no code needed ***)
(*** more bits than were left                                          ***)

let fin_post = with_memsafe fin_rr fin_wr `\s.
  read PC s = word(pc + 0x542c) /\ read X19 s = word_add op (word L) /\
  read (memory :> bytes64 (word_add argk (word 32))) s =
  word_add op (word L) /\
  (SND(SND(huf_decode ws ml blk p L))
   ==> read (memory :> bytes(op,L)) s =
       num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p L)))`;;

(*** At 0x5418, the segment done ***)

let fin_done = with_memsafe fin_rr fin_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x5418)`; fin_common;
  `SND(SND(huf_decode ws ml blk p L))
   ==> read (memory :> bytes(op,L)) s =
       num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p L))`]));;

(*** The bytes decoded, when no code needed more bits than were left ***)

let fin_ok = `SND(SND(huf_decode ws ml (blk:byte list) p L))`;;

let FIN_OKCASES_TAC =
  ASM_CASES_TAC fin_ok THENL
   [FIRST_X_ASSUM(fun th ->
      if is_imp(concl th) && lhand(concl th) = fin_ok
      then ASSUME_TAC(MP th (ASSUME fin_ok)) else NO_TAC);
    FIRST_X_ASSUM(fun th ->
      if is_imp(concl th) && lhand(concl th) = fin_ok
      then ALL_TAC else NO_TAC)];;

let FIN_FINAL_TAC =
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

(*** 0x5418: op[k] in the arguments moved to the end of the segment ***)

let FIN_DONE = prove
 (mk_fin_goal [] fin_done fin_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FIN_OKCASES_TAC THEN
  ZSTD_STEPS_TAC (1--2) THEN
  FA_STATE_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
    MP (ARITH_RULE `j0 <= L ==> j0 + (L - j0) = L`) (ASSUME `j0 <= L`)] THEN
  ZSTD_STEPS_TAC (3--5) THEN FIN_FINAL_TAC);;

(*** 0x5a00, the loop for the last bytes of the segment, without reloads, ***)
(*** for the measure m = L - jj, with the container at ofs fixed          ***)

let fin_win = `word((num_of_bytelist (blk:byte list) DIV 2 EXP (8 * ofs)) MOD
                    2 EXP 64):int64`;;

let fin_tinv = with_memsafe fin_rr fin_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `bc:num`],list_mk_conj
   [`m = L - jj /\ jj < L`;
    `read PC s = word(pc + 0x5a00)`; fin_common;
    `read X3 s = word_add op (word jj)`;
    mk_eq(`read X4 s`,fin_win);
    `read X1 s = word bc /\ ofs + 8 <= LENGTH(blk:byte list)`;
    `SND(SND(huf_decode ws ml blk p jj)) /\
     FST(SND(huf_decode ws ml blk p jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
     (ofs = 0 \/ bc + 11 * (L - jj) <= 53) /\
     read (memory :> bytes(op,jj)) s =
     num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p jj)) \/
     ~SND(SND(huf_decode ws ml blk p jj)) /\ ofs = 0 /\ 64 < bc /\
     bc <= 64 + 11 * jj`])));;

(*** The goal of the loop: from the invariant for some m to fin_done ***)

let fin_tloop_goal = mk_fin_goal [`ofs:num`]
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(fin_tinv,[`m:num`; `s:armstate`]))))
  fin_done;;

(*** A lookup at position 8 * ofs + 64 - bc: x, y, sym and nb, at state s ***)

let FIN_LOOKUP_FACTS_TAC (s:term) (bc:term) =
  let pos = subst [bc,`bc:num`] `8 * ofs + 64 - bc` in
  let back k = list_mk_icomb "zstd_back" [`blk:byte list`; pos; k] in
  MP_TAC(SPECL [`blk:byte list`; `ofs:num`; bc] FIN_INDEX2) THEN
  ANTS_TAC THENL
   [FA_ARITHV_TAC [`ofs:num`; `L:num`; `jj:num`];
    DISCH_THEN(fun th -> FA_STATE_REWRITE_TAC[th])] THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; back `11`; s]
    HUF_DTABLE_READ) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`blk:byte list`; pos; `11`] ZSTD_BACK_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MP (SPECL [`blk:byte list`; pos; `11`; `ml:num`] ZSTD_BACK_DIV)
               (ASSUME `ml <= 11`)] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`blk:byte list`; pos; `11`] ZSTD_BACK_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC (mk_eq(`x:num`,back `11`)) THEN
  ABBREV_TAC (mk_eq(`y:num`,back `ml:num`)) THEN
  ABBREV_TAC `sym = huf_symbol ws y` THEN
  ABBREV_TAC `nb = (ml + 1) - EL sym ws`;;

(*** A lookup with any bits, once the stream has run out ***)

let FIN_LOOKUP_ANY_TAC (s:term) =
  FIRST_ASSUM(fun th ->
    let t = concl th in
    match t with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),r)
        when s' = s && c = `X2` ->
        let y' = lhand(lhand r) in
        let y = lhand r in
        (MP_TAC(ISPEC y' FIN_INDEX_ANY) THEN
         ABBREV_TAC (mk_eq(`x:num`,mk_comb(`val:int64->num`,y))) THEN
         DISCH_THEN(CONJUNCTS_THEN2 (fun th -> FA_STATE_REWRITE_TAC[th])
                                    ASSUME_TAC))
    | _ -> NO_TAC) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; `x:num`; s]
    HUF_DTABLE_READ) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `11`; `ml:num`] DIV_EXP_LT) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (11 - ml)`]
    HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (11 - ml)`]
    HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `sym = huf_symbol ws (x DIV 2 EXP (11 - ml))` THEN
  ABBREV_TAC `nb = (ml + 1) - EL sym ws`;;

(*** The loop for the last bytes, at 0x5a00 ***)

let FIN_MEM_SNOC_TAC s =
  MP_TAC(ISPECL [`op:int64`; `FST(huf_decode ws ml (blk:byte list) p jj)`;
                 `word sym:byte`; s] READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[HUF_DECODE_LENGTH];;

let FIN_TAIL_SUBST_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `jj + 1 = L`));;

let FIN_ARITH_TAC = FA_ARITHV_TAC [`ofs:num`; `bc:num`; `nb:num`; `jj:num`;
                                   `L:num`; `m:num`; `ml:num`];;

let FIN_GOOD_END_TAC =
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN FIN_TAIL_SUBST_TAC THEN
  ASM_REWRITE_TAC[HUF_DECODE_SUC] THEN
  DISCH_TAC THEN FIN_MEM_SNOC_TAC `s11:armstate`;;

let FIN_GOOD_LOOP_TAC =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `L - (jj + 1)` THEN
  CONJ_TAC THENL [FIN_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`jj + 1`; `bc + nb:num`] THEN
  ASM_REWRITE_TAC[HUF_DECODE_SUC] THEN
  ASM_CASES_TAC `nb <= 8 * ofs + 64 - bc` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIN_MEM_SNOC_TAC `s10:armstate` THEN NO_TAC; FIN_ARITH_TAC];;

let FIN_BAD_FACT_TAC =
  SUBGOAL_THEN `~SND(SND(huf_decode ws ml (blk:byte list) p (jj + 1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[HUF_DECODE_SUC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                   `zstd_back (blk:byte list) (8 * ofs + 64 - bc) ml`]
      HUF_NBITS_BOUND) THEN
    ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN FIN_ARITH_TAC;
    ALL_TAC];;

let FIN_BAD_END_TAC =
  FIN_BAD_FACT_TAC THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
  FIN_TAIL_SUBST_TAC THEN ASM_REWRITE_TAC[];;

let FIN_BAD_LOOP_TAC =
  FIN_BAD_FACT_TAC THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `L - (jj + 1)` THEN
  CONJ_TAC THENL [FIN_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`jj + 1`; `bc + nb:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIN_ARITH_TAC;;

let FIN_TLOOP = prove
 (fin_tloop_goal,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  PUFF_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (free_in `bc:num` o concl)) THENL
   [ASM_CASES_TAC `bc < 64` THENL
     [ZSTD_STEPS_TAC (1--3) THEN
      FIN_LOOKUP_FACTS_TAC `s3:armstate` `bc:num` THEN
      ZSTD_STEPS_TAC (4--8) THEN STATE_PTR_NORM_TAC THEN
      ASM_CASES_TAC `jj + 1 = L` THENL
       [ZSTD_STEPS_TAC (9--11) THEN FIN_GOOD_END_TAC;
        ZSTD_STEPS_TAC (9--10) THEN FIN_GOOD_LOOP_TAC];
      ALL_TAC];
    ALL_TAC] THEN
  (ZSTD_STEPS_TAC (1--3) THEN FIN_LOOKUP_ANY_TAC `s3:armstate` THEN
   ZSTD_STEPS_TAC (4--8) THEN STATE_PTR_NORM_TAC THEN
   ASM_CASES_TAC `jj + 1 = L` THENL
    [ZSTD_STEPS_TAC (9--11) THEN FIN_BAD_END_TAC;
     ZSTD_STEPS_TAC (9--10) THEN FIN_BAD_LOOP_TAC]));;

(*** The tail loop on to 0x542c ***)

let fin_tloop2_goal = mk_fin_goal [`ofs:num`]
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(fin_tinv,[`m:num`; `s:armstate`]))))
  fin_post;;

let FIN_TLOOP2 = prove
 (fin_tloop2_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC fin_done THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC(SPEC_ALL FIN_TLOOP) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SPEC_ALL FIN_DONE) THEN ASM_REWRITE_TAC[]]);;

(*** Going on with a piece of the same postcondition ***)

let FIN_CONTINUE_TAC = ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN REWRITE_TAC[]);;

(*** 0x59f4: the check of the end of the segment before the tail loop ***)

let fin_tail = with_memsafe fin_rr fin_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x59f4)`; fin_common;
  `read X3 s = word_add op (word jj)`;
  mk_eq(`read X4 s`,fin_win);
  `read X1 s = word bc /\ ofs + 8 <= LENGTH(blk:byte list) /\ jj <= L`;
  `SND(SND(huf_decode ws ml blk p jj)) /\
   FST(SND(huf_decode ws ml blk p jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   (ofs = 0 \/ bc + 11 * (L - jj) <= 53) /\
   read (memory :> bytes(op,jj)) s =
   num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p jj))`]));;

let FIN_TAIL = prove
 (mk_fin_goal [`ofs:num`; `jj:num`; `bc:num`] fin_tail fin_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ASM_CASES_TAC `jj:num = L` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `jj:num = L`)) THEN
    ZSTD_STEPS_TAC (1--2) THEN FIN_CONTINUE_TAC FIN_DONE [] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];
    ZSTD_STEPS_TAC (1--3) THEN FIN_CONTINUE_TAC FIN_TLOOP2 [] THEN
    EXISTS_TAC `L - jj:num` THEN MAP_EVERY EXISTS_TAC [`jj:num`; `bc:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN FIN_ARITH_TAC]);;

(*** The main loop: 0x59c0 (reload) and 0x5930 (4 bytes) ***)

let fin_ptrs =
 `read X12 s = ilowest /\ read X13 s = word_add ilowest (word 8) /\
  read X14 s = word_add op (word (L - 3)) /\ 3 <= L`;;

let fin_rinv = with_memsafe fin_rr fin_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj /\ jj <= L`;
    `read PC s = word(pc + 0x59c0)`; fin_common; fin_ptrs;
    `read X3 s = word_add op (word jj) /\
     read X6 s = word_add ilowest (word ofs)`;
    mk_eq(`read X4 s`,fin_win);
    `read X1 s = word bc /\ ofs + 8 <= LENGTH(blk:byte list)`;
    `SND(SND(huf_decode ws ml blk p jj)) /\
     FST(SND(huf_decode ws ml blk p jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
     read (memory :> bytes(op,jj)) s =
     num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p jj))`])));;

let fin_body = with_memsafe fin_rr fin_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x5930)`; fin_common; fin_ptrs;
  `read X3 s = word_add op (word jj) /\
   read X6 s = word_add ilowest (word ofs) /\ read X7 s = word 1`;
  mk_eq(`read X4 s`,fin_win);
  `read X1 s = word bc /\ ofs + 8 <= LENGTH(blk:byte list) /\
   jj + 4 <= L /\ bc <= 7`;
  `SND(SND(huf_decode ws ml blk p jj)) /\
   FST(SND(huf_decode ws ml blk p jj)) = 8 * ofs + 64 - bc /\
   read (memory :> bytes(op,jj)) s =
   num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p jj))`]));;

(*** Lookup jn of the body at state sn, with bcv bits used, and the state ***)
(*** of the specification after it                                       ***)

let FIN_SYM_TAC sn jn bcv =
  let s = mk_var("s"^string_of_int sn,`:armstate`) in
  let n = string_of_int jn in
  let jt = if jn = 0 then `jj:num` else
           mk_binop `(+):num->num->num` `jj:num` (mk_small_numeral jn)
  and jt' = mk_binop `(+):num->num->num` `jj:num` (mk_small_numeral(jn+1)) in
  let pos = subst [bcv,`bc:num`] `8 * ofs + 64 - bc` in
  let back k = list_mk_icomb "zstd_back" [`blk:byte list`; pos; k] in
  let xv = mk_var("x"^n,`:num`) and yv = mk_var("y"^n,`:num`)
  and symv = mk_var("sym"^n,`:num`) and nbv = mk_var("nb"^n,`:num`) in
  let dec t = list_mk_icomb "huf_decode"
                [`ws:num list`; `ml:num`; `blk:byte list`; `p:num`; t] in
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
  let split = if jn = 0 then ALL_TAC else
    REWRITE_TAC[ARITH_RULE(mk_eq(jt',mk_binop `(+):num->num->num` jt `1`))] in
  MP_TAC(SPECL [`blk:byte list`; `ofs:num`; bcv] FIN_INDEX2) THEN
  ANTS_TAC THENL
   [FA_ARITHV_TAC [`ofs:num`; `bc:num`; `nb0:num`; `nb1:num`; `nb2:num`;
                   `ml:num`];
    DISCH_THEN(fun th -> FA_STATE_REWRITE_TAC[th])] THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; back `11`; s]
    HUF_DTABLE_READ) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`blk:byte list`; pos; `11`] ZSTD_BACK_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MP (SPECL [`blk:byte list`; pos; `11`; `ml:num`] ZSTD_BACK_DIV)
               (ASSUME `ml <= 11`)] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`blk:byte list`; pos; `11`] ZSTD_BACK_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC (mk_eq(xv,back `11`)) THEN
  ABBREV_TAC (mk_eq(yv,back `ml:num`)) THEN
  ABBREV_TAC (mk_eq(symv,list_mk_icomb "huf_symbol" [`ws:num list`; yv])) THEN
  ABBREV_TAC (mk_eq(nbv,mk_binop `(-):num->num->num` `ml + 1`
                    (list_mk_icomb "EL" [symv; `ws:num list`]))) THEN
  SUBGOAL_THEN goal STRIP_ASSUME_TAC THENL
   [split THEN ONCE_REWRITE_TAC[HUF_DECODE_SUC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FA_ARITHV_TAC [`ofs:num`; `bc:num`; `nb0:num`; `nb1:num`; `nb2:num`;
                   `nb3:num`; `ml:num`];
    ALL_TAC];;

let FIN_BODY_MEM_TAC s =
  let jtm j = if j = 0 then `jj:num` else
    mk_binop `(+):num->num->num` `jj:num` (mk_small_numeral j) in
  let step j =
    MP_TAC(ISPECL [`op:int64`; `ws:num list`; `ml:num`; `blk:byte list`;
                   `p:num`; jtm j; jtm(j + 1);
                   mk_var("sym"^string_of_int j,`:num`); s] HUF_MEM_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] in
  step 0 THEN step 1 THEN step 2 THEN step 3;;

(*** 0x5930: the body, 4 bytes ***)

let FIN_DROP_TABLE_TAC =
  let pat = `read (memory :> bytes8 (word_add dt a)) s = x` in
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> can (term_match [`dt:int64`] pat) (concl th));;

let fin_body_goal = mk_fin_goal [`jj:num`; `ofs:num`; `bc:num`] fin_body
  (mk_abs(`s:armstate`,
          list_mk_comb(fin_rinv,[`L - (jj + 4)`; `s:armstate`])));;

let FIN_BODY = prove
 (fin_body_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ZSTD_STEPS_TAC (1--5) THEN FIN_SYM_TAC 5 0 `bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (6--8) THEN FIN_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (9--13) THEN FIN_SYM_TAC 13 1 `nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (14--16) THEN FIN_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (17--21) THEN FIN_SYM_TAC 21 2 `nb1 + nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (22--24) THEN FIN_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (25--29) THEN FIN_SYM_TAC 29 3 `nb2 + nb1 + nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (30--32) THEN FIN_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (33--36) THEN
  PUFF_FINAL_TAC THEN FIN_BODY_MEM_TAC `s36:armstate` THEN
  MAP_EVERY EXISTS_TAC
   [`jj + 4`; `ofs:num`; `nb3 + nb2 + nb1 + nb0 + bc:num`] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  FA_ARITHV_TAC [`ofs:num`; `bc:num`; `nb0:num`; `nb1:num`; `nb2:num`;
                 `nb3:num`; `ml:num`]);;

(*** 0x59c0: the main loop, the reload and then the body or the tail ***)

let FIN_OPVAL_TAC =
  MAP_EVERY (fun k ->
    let th = SPECL [`op:int64`; k] VAL_WORD_ADD_NOWRAP in
    MP_TAC th THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(op:int64) + rest < 2 EXP 64`; `MIN q rest = L`] THEN
      REWRITE_TAC[MIN] THEN
      FA_ARITHV_TAC [`jj:num`; `L:num`; `rest:num`; `q:num`; `op:int64`];
      DISCH_TAC])
  [`jj:num`; `L - 3`];;

let FIN_SLICE_TAC ofs' s =
  MP_TAC(SPECL [`ilowest:int64`; `LENGTH(blk:byte list)`;
                `num_of_bytelist(blk:byte list)`; ofs'; s]
     READ_MEMORY_BYTES64_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FA_ARITHV_TAC [`ofs:num`; `bc:num`; `blk:byte list`];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC;;

let FIN_RELOAD_WEAKEN_TAC =
  GEN_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `L - (jj + 4)` THEN
  CONJ_TAC THENL
   [FA_ARITHV_TAC [`m:num`; `jj:num`; `L:num`];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[]];;

let FIN_RELOAD_BODY_TAC ofs' bc' =
  ZSTD_CONTINUE_WITH_TAC FIN_RELOAD_WEAKEN_TAC
   FIN_BODY [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FA_ARITHV_TAC [`ofs:num`; `bc:num`; `jj:num`; `L:num`; `blk:byte list`];;

let FIN_TO_TAIL_TAC ofs' bc' =
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC)
   FIN_TAIL [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FA_ARITHV_TAC [`ofs:num`; `bc:num`; `jj:num`; `L:num`; `blk:byte list`];;

let fin_loop_goal = mk_fin_goal []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(fin_rinv,[`m:num`; `s:armstate`]))))
  fin_post;;

let FIN_LOOP = prove
 (fin_loop_goal,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  FIN_OPVAL_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [FIN_SLICE_TAC `ofs - bc DIV 8` `s0:armstate` THEN
    ASM_CASES_TAC `jj + 4 <= L` THENL
     [ZSTD_STEPS_TAC (1--9) THEN
      FIN_RELOAD_BODY_TAC `ofs - bc DIV 8` `bc MOD 8`;
      ZSTD_STEPS_TAC (1--11) THEN
      FIN_TO_TAIL_TAC `ofs - bc DIV 8` `bc MOD 8`];
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (1--6) THEN FIN_TO_TAIL_TAC `ofs:num` `bc:num`;
    ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [FIN_SLICE_TAC `ofs - bc DIV 8` `s0:armstate` THEN
    ASM_CASES_TAC `jj + 4 <= L` THENL
     [ZSTD_STEPS_TAC (1--14) THEN
      FIN_RELOAD_BODY_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
      ZSTD_STEPS_TAC (1--16) THEN
      FIN_TO_TAIL_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`];
    FIN_SLICE_TAC `0` `s0:armstate` THEN ZSTD_STEPS_TAC (1--13) THEN
    FIN_TO_TAIL_TAC `0` `bc - 8 * ofs`]);;

(*** 0x537c, the start of the finish of a stream ***)

let fin_head = with_memsafe fin_rr fin_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x537c)`;
  `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
   read X0 s = argk /\ read X5 s = dt /\ read X9 s = word q /\
   read X19 s = op /\ read X21 s = word_add op (word rest) /\
   read SP s = word_sub stackpointer (word 496) /\
   aligned 16 (stackpointer:int64) /\
   read (memory :> bytes64
          (word_add (word_sub stackpointer (word 496)) (word 448))) s =
   ilowest /\
   read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
   num_of_bytelist blk /\
   read (memory :> bytes(dt,4096)) s = num_of_bytelist(huf_dtable ws ml 11)`;
  subst [fl_cont `u:num` `sh:num`,`c:int64`]
  `read (memory :> bytes64 argk) s = word_add ilowest (word u) /\
   read (memory :> bytes64 (word_add argk (word 32))) s =
   word_add op (word j0) /\
   read (memory :> bytes64 (word_add argk (word 64))) s = (c:int64) /\
   read (memory :> bytes64 (word_add argk (word 120))) s =
   word_add ilowest (word a)`;
  `read (memory :> bytes(op,j0)) s =
   num_of_bytelist(FST(huf_decode ws ml blk p j0)) /\
   FST(SND(huf_decode ws ml blk p j0)) = 8 * u + 64 - sh /\
   SND(SND(huf_decode ws ml (blk:byte list) p j0)) /\
   sh <= 8 /\ u + 8 <= LENGTH(blk:byte list) /\ j0 <= L /\
   a <= LENGTH(blk:byte list)`]));;

let fin_hpost = with_memsafe fin_rr fin_wr `\s.
  read PC s = word(pc + 0x542c) /\ read X19 s = word_add op (word L) /\
  read (memory :> bytes64 (word_add argk (word 32))) s =
  word_add op (word L) /\
  (SND(SND(huf_decode ws ml blk p L))
   ==> read (memory :> bytes(op,L)) s =
       num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p L))) \/
  read PC s = word(pc + 0x5440) /\ u + 8 < a`;;

let fin_head_goal =
  mk_fin_goal [`u:num`; `sh:num`; `a:num`] fin_head fin_hpost;;

(*** 0x537c: the head of the finish of a stream ***)

let FIN_CSEL = prove
 (`!(op:int64) q rest.
     q < 2 EXP 64 /\ rest < 2 EXP 64
     ==> (if ~(val (word rest:int64) <= q /\
               ~(val (word_sub (word q) (word rest):int64) = 0))
          then word_add op (word q) else word_add op (word rest)) =
         word_add op (word (MIN q rest))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_LT64; VAL_EQ_0; WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `(word q:int64 = word rest) <=> q = rest` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD_LT64]; ALL_TAC] THEN
  REWRITE_TAC[MIN] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC);;

let FIN_SUBK = prove
 (`!(p:int64) a k. k <= a ==> word_sub (word_add p (word a)) (word k) =
                              word_add p (word (a - k))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let FIN_ZX_SMALL = prove
 (`!n. n < 2 EXP 32 ==> word_zx (word_zx (word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
    DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN
  ASM_SIMP_TAC[MOD_MOD_EXP_MIN; MOD_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let FIN_HEAD_VAL_TAC =
  MAP_EVERY (fun k ->
    let th = SPECL [`op:int64`; k] VAL_WORD_ADD_NOWRAP in
    MP_TAC th THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(op:int64) + rest < 2 EXP 64`; `MIN q rest = L`; `j0 <= L`] THEN
      REWRITE_TAC[MIN] THEN ARITH_TAC;
      DISCH_TAC])
  [`j0:num`; `L:num`] THEN
  MP_TAC(SPECL [`ilowest:int64`; `u:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`;
      `u + 8 <= LENGTH(blk:byte list)`] THEN ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`ilowest:int64`; `a:num`; `8`] VAL_WORD_SUB_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`;
      `a <= LENGTH(blk:byte list)`; `8 <= val(ilowest:int64)`] THEN ARITH_TAC;
    DISCH_TAC];;

let FIN_SETUP_TAC =
  SUBGOAL_THEN `sh < 64 /\ sh < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sh <= 8` THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let ctz = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
      (MP (SPECL [`word((num_of_bytelist (blk:byte list) DIV 2 EXP (8 * u)) MOD
                        2 EXP 64):int64`; `sh:num`] FAST_RELOAD_CTZ)
          (ASSUME `sh < 64`)) in
    FA_STATE_REWRITE_TAC[ctz]) THEN
  FA_STATE_REWRITE_TAC[MP (SPEC `sh:num` FIN_ZX_SMALL)
                         (ASSUME `sh < 2 EXP 32`)] THEN
  FA_STATE_REWRITE_TAC[MP (SPECL [`op:int64`; `L:num`; `j0:num`] FL_SUB_OP)
                         (ASSUME `j0 <= L`)];;

let FIN_HEAD_WTAC =
  let one = FIRST_ASSUM ACCEPT_TAC ORELSE
            (FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  (one ORELSE (DISJ1_TAC THEN REPEAT CONJ_TAC THEN one));;

let FIN_HEAD_ARITH_TAC =
  FA_ARITHV_TAC [`u:num`; `sh:num`; `j0:num`; `L:num`; `blk:byte list`];;

let FIN_HEAD_CONJ_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN REWRITE_TAC[] THEN
    NO_TAC) ORELSE
   FIN_HEAD_ARITH_TAC);;

let FIN_HEAD_TAIL_TAC ofs' bc' =
  ZSTD_CONTINUE_WITH_TAC FIN_HEAD_WTAC FIN_TAIL
    [ofs',`ofs:num`; `j0:num`,`jj:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN FIN_HEAD_CONJ_TAC;;

let FIN_HEAD = prove
 (fin_head_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--5) THEN
  SUBGOAL_THEN `q < 2 EXP 64 /\ rest < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`q < 2 EXP 28`; `val(op:int64) + rest < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FA_STATE_REWRITE_TAC[MP (SPECL [`op:int64`; `q:num`; `rest:num`] FIN_CSEL)
    (CONJ (ASSUME `q < 2 EXP 64`) (ASSUME `rest < 2 EXP 64`))] THEN
  FA_STATE_REWRITE_TAC[ASSUME `MIN q rest = L`] THEN
  FIN_HEAD_VAL_TAC THEN ZSTD_STEPS_TAC (6--7) THEN
  ASM_CASES_TAC `u + 8 < a` THENL
   [ZSTD_STEPS_TAC (8--12) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIN_SLICE_TAC `u:num` `s7:armstate` THEN ZSTD_STEPS_TAC (8--21) THEN
  FIN_SETUP_TAC THEN
  MP_TAC(SPECL [`sh:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `3 < L - j0` THENL
   [FA_STATE_REWRITE_TAC[MP (SPECL [`op:int64`; `L:num`; `3`] FIN_SUBK)
      (MP (ARITH_RULE `3 < L - j0 ==> 3 <= L`) (ASSUME `3 < L - j0`))] THEN
    ZSTD_STEPS_TAC (22--23) THEN
    ZSTD_CONTINUE_WITH_TAC FIN_HEAD_WTAC FIN_LOOP [] THEN
    EXISTS_TAC `L - j0` THEN
    MAP_EVERY EXISTS_TAC [`j0:num`; `u:num`; `sh:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN FIN_HEAD_CONJ_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (22--23) THEN
  ASM_CASES_TAC `8 <= u` THENL
   [FIN_SLICE_TAC `u - sh DIV 8` `s23:armstate` THEN
    ZSTD_STEPS_TAC (24--29) THEN FIN_HEAD_TAIL_TAC `u - sh DIV 8` `sh MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `u = 0` THENL
   [ZSTD_STEPS_TAC (24--27) THEN FIN_HEAD_TAIL_TAC `u:num` `sh:num`;
    ALL_TAC] THEN
  FIN_SLICE_TAC `u - sh DIV 8` `s23:armstate` THEN
  ZSTD_STEPS_TAC (24--34) THEN
  ASM_CASES_TAC `j0:num = L` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `j0:num = L`)) THEN
    ZSTD_STEPS_TAC (35--36) THEN
    ZSTD_CONTINUE_WITH_TAC FIN_HEAD_WTAC FIN_DONE [`L:num`,`j0:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[SUB_REFL];
    ZSTD_STEPS_TAC [35] THEN
    ZSTD_CONTINUE_WITH_TAC FIN_HEAD_WTAC FIN_TLOOP2
     [`u - sh DIV 8`,`ofs:num`] THEN
    EXISTS_TAC `L - j0:num` THEN
    MAP_EVERY EXISTS_TAC [`j0:num`; `sh - 8 * sh DIV 8`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN FIN_HEAD_CONJ_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

(*** The whole of HUF_decompress4X1_usingDTable_internal at 0x5300 ***)

(*** The start: the registers saved and restored, the arguments, and the  ***)
(*** header of the table as a 32-bit word dh                              ***)

let TOP_START_TAC =
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
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  ABBREV_TAC `dh = read (memory :> bytes32 dtable) s0` THEN
  SUBGOAL_THEN `val(word_subword (dh:int32) (16,8):byte) = tl` ASSUME_TAC
  THENL
   [EXPAND_TAC "dh" THEN REWRITE_TAC[READ_BYTES32_BYTE2] THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `tl <= 12` THEN ARITH_TAC;
    ALL_TAC];;

(*** The derived facts about the regions ***)

let TOP_REGIONS_TAC =
  SUBGOAL_THEN
   `nonoverlapping (dst:int64,n) (word_add dtable (word 4),2 * 2 EXP tl) /\
    nonoverlapping (word_sub stackpointer (word 688),688)
                   (word_add dtable (word 4),2 * 2 EXP tl) /\
    nonoverlapping (word_sub stackpointer (word 688),688) (dtable,4) /\
    nonoverlapping (word_add dtable (word 4),2 * 2 EXP tl) (word pc,32000) /\
    nonoverlapping (src:int64,LENGTH(blk:byte list))
                   (word_add dtable (word 4),2 * 2 EXP tl) /\
    nonoverlapping (dst:int64,n) (word_sub stackpointer (word 496),496) /\
    nonoverlapping (word_sub stackpointer (word 496),496)
                   (src,LENGTH(blk:byte list)) /\
    nonoverlapping (word_sub stackpointer (word 496),496)
                   (word_add dtable (word 4),2 * 2 EXP tl) /\
    nonoverlapping (word_sub stackpointer (word 496),496) (dtable,4) /\
    nonoverlapping (word_sub stackpointer (word 496),496) (word pc,32000)`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `tt = 2 EXP tl` THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(src:int64) + LENGTH(blk:byte list) < 2 EXP 64 /\
    val(dst:int64) + n < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`;
      `val(dst:int64) + n + 3 < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC];;

(*** Helpers: the state number, steps from the current state, and the  ***)
(*** addresses of the memory reads in a theorem in the normal form of    ***)
(*** the simulator                                                       ***)

let top_state_num (asl,w) =
  let w' = if is_imp w then rand w else w in
  let n = fst(dest_var(rand w')) in
  int_of_string(String.sub n 1 (String.length n - 1));;

let TOP_STEPS_TAC k : tactic =
  W(fun gl -> let n = top_state_num gl in ZSTD_STEPS_TAC ((n+1)--(n+k)));;

let TOP_ADDR_CONV =
  let is_bytes t =
    match t with
      Comb(Const(c,_),_) ->
        mem c ["bytes8";"bytes16";"bytes32";"bytes64";"bytes128";"bytes"]
    | _ -> false in
  ONCE_DEPTH_CONV (fun t ->
    if is_bytes t
    then RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) t
    else failwith "TOP_ADDR_CONV");;

let TOP_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 496)) (word 496):int64 =
  stackpointer`;;

let TOP_BIT5 = prove
 (`!x:int64. bit 5 (word_zx x:int32) <=> bit 5 x`,
  SIMP_TAC[BIT_WORD_ZX; DIMINDEX_32; ARITH]);;

(*** The final state: the postcondition, with the frame proved from the  ***)
(*** few facts that its subsumption needs, its stack addresses rebased    ***)
(*** on the region of 688 bytes                                           ***)

let TOP_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 496):int64 =
  word_add (word_sub stackpointer (word 688)) (word 192)`;;

let top_frame_facts =
  [`3 * q <= n`; `2 * q <= n`; `q <= n`; `n - 3 * q <= q`;
   `val(dst:int64) + n + 3 < 2 EXP 64`; `n < 2 EXP 28`];;

let TOP_FRAME_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE[TOP_STACK_REBASE; WORD_ADD_ASSOC_NUM] th)
    else th) THEN
  W(fun (asl,w) ->
    let sasl = filter (fun (_,th) -> let t = concl th in
                 maychange_term t || mem t top_frame_facts) asl in
    ACCEPT_TAC(TAC_PROOF((sasl,w),
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC)));;

let TOP_FINAL_TAC : tactic =
  GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
  GEN_REWRITE_TAC TRY_CONV [BETA_THM] THEN
  W(fun (asl,w) ->
    let mcs,ocs = partition maychange_term (conjuncts w) in
    let w' = mk_conj(list_mk_conj ocs,list_mk_conj mcs) in
    GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))]) THEN
  CONJ_TAC THENL [MEMSAFE_ELIM_TAC; TOP_FRAME_TAC];;

(*** The result of the slow path at 0x5444 ***)

let top_sp_alist =
  [("dt",`dtable:int64`); ("v25",`x25:int64`); ("v26",`x26:int64`);
   ("v27",`x27:int64`); ("v28",`x28:int64`)];;

let TOP_RESULT_ABBREV_TAC : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let x0 = list_mk_icomb "read" [`X0`; s]
    and m = subst [s,`s:armstate`]
              `read (memory :> bytes(dst:int64,n)) s` in
    ABBREV_TAC (mk_eq(`x0r:int64`,x0)) THEN
    ABBREV_TAC (mk_eq(`mr:num`,m)));;

let TOP_RESULT_TAC : tactic =
  W(fun (asl,w) ->
    let ths = map snd (filter (fun (_,th) ->
      can (find_term (fun t -> is_const t &&
                               fst(dest_const t) = "huf_streams4"))
          (concl th)) asl) in
    MESON_TAC ths);;

let TOP_SLOW_TAC : tactic =
  BK_BIGSTEP_TAC SP_CORRECT top_sp_alist THEN
  TOP_RESULT_ABBREV_TAC THEN ZSTD_RUN_TAC THEN TOP_FINAL_TAC THEN
  ASM_REWRITE_TAC[TOP_SP_RESTORE] THEN TOP_RESULT_TAC;;

(*** The prologue, to the test of bit 5 of the flags at 0x5328 ***)

let TOP_PROLOGUE_TAC : tactic =
  TOP_REGIONS_TAC THEN ZSTD_STEPS_TAC (1--11) THEN
  ASM_CASES_TAC `bit 5 (flags':int64)` THEN
  W(fun (asl,w) ->
    let c = snd(hd asl) and s = rand w in
    RULE_ASSUM_TAC(fun th ->
      if free_in s (concl th) then REWRITE_RULE[TOP_BIT5; c] th else th));;

(*** The call of HUF_DecompressFastArgs_init at 0x5354 with the arguments ***)
(*** at sp + 344 in the frame of 496 bytes                                ***)

let top_args = `word_add (word_sub stackpointer (word 496)) (word 344):int64`;;

let TOP_CALL_TAC th : tactic =
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  W(fun gl -> ARM_BIGSTEP_TAC ZSTD_EXEC
                ("s"^string_of_int(top_state_num gl + 1))) THEN
  EVENTS_UNABBREV_TAC;;

let TOP_FA_CALL_TAC : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(CONV_RULE TOP_ADDR_CONV (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x5358):int64`; top_args;
    `dst:int64`; `n:num`; `src:int64`; `blk:byte list`; `dtable:int64`;
    `dh:int32`; `tl:num`] HUF_DECOMPRESSFASTARGS_INIT_CORRECT)))) THEN
  TOP_CALL_TAC HUF_DECOMPRESSFASTARGS_INIT_CORRECT;;

let TOP_FA_TAC : tactic = TOP_STEPS_TAC 11 THEN TOP_FA_CALL_TAC;;

(*** The error -20 of HUF_DecompressFastArgs_init: no valid block ***)

let TOP_NOVALID_TAC tac : tactic =
  SUBGOAL_THEN `!out. ~(LENGTH out = n /\ huf_streams4 T ws ml blk out)`
  ASSUME_TAC THENL
   [X_GEN_TAC `out:byte list` THEN STRIP_TAC THEN tac; ALL_TAC];;

let TOP_ERROR_END_TAC : tactic =
  ZSTD_RUN_TAC THEN TOP_FINAL_TAC THEN
  ASM_REWRITE_TAC[TOP_SP_RESTORE; zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (asl,w) ->
    let th = snd(find (fun (_,th) -> concl th =
      `!out. ~(LENGTH out = n /\ huf_streams4 T ws ml blk out)`) asl) in
    MESON_TAC[th]);;

let TOP_FA20_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_eq(lhand(concl th)) &&
    rand(lhand(concl th)) = `word 18446744073709551596:int64`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TOP_NOVALID_TAC
   (FIRST_ASSUM(MP_TAC o MATCH_MP HUF_STREAMS4_NECESSARY) THEN
    UNDISCH_TAC `LENGTH(blk:byte list) < 10 \/
                 LENGTH blk <
                 6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2` THEN
    ARITH_TAC) THEN
  TOP_ERROR_END_TAC;;

(*** The fast path: HUF_DecompressFastArgs_init returned 1 ***)

let top_op k =
  if k = 0 then `dst:int64`
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,`dst:int64`),
               mk_comb(`word:num->int64`,top_o k));;

let top_rest k = if k = 0 then `n:num`
                 else mk_binop `(-):num->num->num` `n:num` (top_o k);;

let top_argk k =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,
                  `word_sub stackpointer (word 496):int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(344 + 8 * k)));;

let top_u k = mk_binop `(-):num->num->num` (top_e k) `8`;;

let top_sh k =
  subst [top_e k,`e:num`] `huf_lastshift(EL (e - 1) (blk:byte list))`;;

(*** The end of the output in X21, once the length is known not 0 ***)

let TOP_X21_LEMMA = prove
 (`!(dst:int64) n.
     ~(n = 0) /\ n < 2 EXP 28
     ==> (if ~(n - 0 = 0) /\ ~(ival (word (n - 0):int64) < &0)
          then word_add dst (word n) else dst) = word_add dst (word n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_0] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ival(word n:int64) = &n` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
    UNDISCH_TAC `n < 2 EXP 28` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
    CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INT_OF_NUM_LT; LT]]);;

let TOP_FA1_SETUP_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_eq(lhand(concl th)) &&
    rand(lhand(concl th)) = `word 1:int64`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_imp(concl th) && is_eq(lhand(concl th)) &&
    rand(lhand(concl th)) = `word 18446744073709551596:int64`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `tl = 11`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `2 * 2 EXP 11 = 4096`]) THEN
  ABBREV_TAC `q = (n + 3) DIV 4` THEN
  SUBGOAL_THEN
   `3 * q <= n /\ n <= 4 * q /\ n - 3 * q <= q /\ q < 2 EXP 28 /\
    2 * q <= n /\ q <= n /\ ~(n - 3 * q = 0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(n + 3) DIV 4 = q`; `3 * q < n`; `n < 2 EXP 28`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`dst:int64`; top_o k] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(dst:int64) + n + 3 < 2 EXP 64`; `3 * q <= n`] THEN ARITH_TAC;
      DISCH_TAC])
   [1;2;3] THEN
  SUBGOAL_THEN `val(word_add dst (word (3 * q)):int64) + n - 3 * q < 2 EXP 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(dst:int64) + n + 3 < 2 EXP 64`; `3 * q <= n`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add dst (word n):int64 =
    word_add (word_add dst (word (3 * q))) (word (n - 3 * q))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `3 * q <= n` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FA_STATE_REWRITE_TAC[MP (SPECL [`dst:int64`; `n:num`] TOP_X21_LEMMA)
    (CONJ (ASSUME `~(n = 0)`) (ASSUME `n < 2 EXP 28`))];;

(*** The call of the fast loop at 0x5368 ***)

let top_fl_alist =
  [("returnaddress",`word(pc + 0x536c):int64`);
   ("stackpointer",`word_sub stackpointer (word 496):int64`);
   ("args",top_args); ("ilowest",`src:int64`);
   ("dt",`word_add dtable (word 4):int64`);
   ("oend",`word_add dst (word n):int64`); ("D",`n - 3 * q`)] @
  map (fun k -> ("op"^string_of_int k,top_op k)) [0;1;2;3] @
  map (fun k -> ("p"^string_of_int k,top_p k)) [0;1;2;3];;

let TOP_FL_PRE_TAC : tactic =
  MAP_EVERY EXISTS_TAC (map top_u [0;1;2;3] @ map top_sh [0;1;2;3]) THEN
  ASM_REWRITE_TAC[HUF_LASTSHIFT_LE8] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY UNDISCH_TAC top_fa_ok THEN ARITH_TAC;;

let TOP_FL_CALL_TAC : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun gl ->
    let th = ml_inst_thm HUF_DECOMPRESS4X1_FAST_C_LOOP_CORRECT
               (("e",current_events gl)::top_fl_alist) in
    MP_TAC(CONV_RULE(TOP_ADDR_CONV THENC ONCE_DEPTH_CONV NUM_ADD_CONV)
             (REWRITE_RULE[WORD_SUB_SUB_NUM] th))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  W(fun gl -> ARM_BIGSTEP_TAC ZSTD_EXEC
                ("s"^string_of_int(top_state_num gl + 1))) THEN
  W(fun (_,w) ->
    if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                     with Failure _ -> false)
    then EVENTS_UNABBREV_TAC else TOP_FL_PRE_TAC);;

let TOP_FL_TAC : tactic = TOP_STEPS_TAC 5 THEN TOP_FL_CALL_TAC;;

(*** A big step with a theorem th instantiated by names, its addresses ***)
(*** normalized, its hypotheses from the assumptions                    ***)

let TOP_BIGSTEP_TAC th alist : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun gl ->
    let th' = CONV_RULE TOP_ADDR_CONV
                (ml_inst_thm th (("e",current_events gl)::alist)) in
    let n = top_state_num gl in
    MP_TAC th' THEN ANTS_TAC THENL [ML_HYP_TAC; ALL_TAC] THEN
    ARM_BIGSTEP_TAC ZSTD_EXEC ("s"^string_of_int(n + 1)) THEN
    W(fun (_,w) ->
      if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                       with Failure _ -> false)
      then EVENTS_UNABBREV_TAC THEN MEMSAFE_STRIP_TAC
      else REPEAT CONJ_TAC THEN
           FIRST [ML_PRE_MEMSAFE_TAC; ML_FACT_TAC; T4_CONJ_TAC]));;

(*** The equation of the value of a register in the current state ***)

let TOP_REG_TAC (r:term) (v:term) (tac:tactic) : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let rd = list_mk_icomb "read" [r; s] in
    let _,fth = find (fun (_,th) -> let t = concl th in
                       is_eq t && lhs t = rd) asl in
    let eq = mk_eq(rhs(concl fth),v) in
    let eth = TAC_PROOF((asl,eq),tac) in
    FIRST_X_ASSUM(fun th -> if concl th = concl fth
                            then ASSUME_TAC(TRANS th eth) else NO_TAC));;

let TOP_WORD_EQ_TAC : tactic =
  CONV_TAC(BINOP_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  TRY(AP_TERM_TAC THEN AP_TERM_TAC) THEN
  MAP_EVERY UNDISCH_TAC [`3 * q <= n`] THEN ARITH_TAC;;

(*** The finish of stream k at 0x537c ***)

let top_addr k =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,
                  `word_sub stackpointer (word 496):int64`),
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(*** The pointer offset u and shift sh of stream k after the fast loop, ***)
(*** as named in the goal, from its arguments in the frame               ***)

let top_fin_vars k (asl,w) =
  let s = rand w in
  let rd a = subst [a,`a:int64`; s,`s:armstate`]
               `read (memory :> bytes64 a) s` in
  let ths = itlist (fun (_,th) acc -> CONJUNCTS th @ acc) asl [] in
  let value a = rhs(concl(find (fun th -> let t = concl th in
                  is_eq t && lhs t = rd a) ths)) in
  let u = rand(rand(value(top_addr(344 + 8 * k))))
  and sh = rand(value(top_addr(408 + 8 * k))) in
  u,sh;;

let top_fin_alist k gl =
  let u,sh = top_fin_vars k gl in
  [("argk",top_argk k); ("op",top_op k); ("rest",top_rest k);
   ("L",top_L k); ("ilowest",`src:int64`);
   ("dt",`word_add dtable (word 4):int64`); ("p",top_p k); ("j0",`j:num`);
   ("u",u); ("sh",sh); ("a",top_a k)];;

let TOP_FIN_PREP_TAC k : tactic =
  TOP_REG_TAC `X0` (top_argk k) TOP_WORD_EQ_TAC THEN
  TOP_REG_TAC `X19` (top_op k) TOP_WORD_EQ_TAC THEN
  TOP_REG_TAC `X21`
   (mk_comb(mk_comb(`word_add:int64->int64->int64`,top_op k),
            mk_comb(`word:num->int64`,top_rest k)))
   TOP_WORD_EQ_TAC;;

let TOP_FIN_TAC k : tactic =
  TOP_FIN_PREP_TAC k THEN
  W(fun gl -> TOP_BIGSTEP_TAC FIN_HEAD (top_fin_alist k gl));;

(*** The error of the finish of stream k: its pointer below its start, ***)
(*** which no valid block can give                                    ***)

let TOP_FINERR_TAC k : tactic =
  W(fun gl ->
  let u,sh = top_fin_vars k gl in
  TOP_NOVALID_TAC
   (MP_TAC(SPECL [`ws:num list`; `ml:num`; `blk:byte list`; `out:byte list`;
                  `n:num`; `q:num`] HUF_STREAMS4_FAST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ws:num list`; `ml:num`; `blk:byte list`; top_p k; `j:num`;
                   top_L k; list_mk_icomb "zstd_sublist"
                     [`out:byte list`; top_o k; top_L k];
                   top_a k; u; sh] HUF_DECODE_START_LE) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`j <= n - 3 * q`; `n - 3 * q <= q`;
      mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` u `8`)
               (top_a k)] THEN
    ARITH_TAC) THEN
  TOP_ERROR_END_TAC);;

(*** After the finish of stream k, at 0x542c: the bytes of its segment ***)
(*** as mk, then on to the next stream                                 ***)

let TOP_NEXT_TAC k : tactic =
  let m = mk_var("m"^string_of_int k,`:num`) in
  W(fun (asl,w) ->
    let s = rand w in
    ABBREV_TAC (mk_eq(m,subst [top_op k,`a:int64`; top_L k,`l:num`;
                               s,`s:armstate`]
                          `read (memory :> bytes(a,l)) s`))) THEN
  TOP_STEPS_TAC 3;;

(*** The end of the fast path: n, and the bytes of the four segments ***)

let TOP_FAST_END_TAC : tactic =
  ZSTD_RUN_TAC THEN TOP_FINAL_TAC THEN
  ASM_REWRITE_TAC[TOP_SP_RESTORE] THEN
  REWRITE_TAC[MATCH_MP SP_BYTES4 (ASSUME `3 * q <= n`)] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HUF_STREAMS4_FAST_RESULT THEN
  REPEAT CONJ_TAC THEN ML_FACT_TAC;;

(*** The four streams, from 0x537c ***)

let rec TOP_PASSES_TAC k : tactic =
  TOP_FIN_TAC k THENL
   [TOP_NEXT_TAC k THEN
    (if k = 3 then TOP_FAST_END_TAC else TOP_PASSES_TAC (k + 1));
    TOP_FINERR_TAC k];;

(*** The numeric facts of the streams after the fast loop, as one       ***)
(*** conjunction: as separate facts they make the linear arithmetic of  ***)
(*** the simulation (SIMPLE_ARITH_TAC over all the facts) take minutes  ***)

let TOP_HIDE_TAC : tactic =
  let has_dec t =
    can (find_term (fun u -> is_const u &&
                             fst(dest_const u) = "huf_decode")) t in
  let is_var_named c t = is_var t && (fst(dest_var t)).[0] = c in
  let hide t =
    (is_eq t && type_of(lhs t) = `:num` && has_dec(lhs t)) ||
    (is_binary "<=" t && is_var_named 's' (lhand t) && rand t = `8`) ||
    (is_binary "<=" t && is_binary "+" (lhand t) &&
     is_var_named 'u' (lhand(lhand t)) &&
     rand t = `LENGTH(blk:byte list)`) in
  fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> hide(concl th)) asl in
    if hs = [] then ALL_TAC (asl,w) else
    let th = end_itlist CONJ (map snd hs) in
    ASSUME_TAC th (ks,w);;

(*** The arithmetic facts that the preconditions of the finishes need ***)

let TOP_FIN_FACTS_TAC : tactic =
  let one t =
    SUBGOAL_THEN t ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       ([`j <= n - 3 * q`; `n - 3 * q <= q`] @ top_fa_ok) THEN ARITH_TAC;
      ALL_TAC] in
  MAP_EVERY one
   (`j <= q` ::
    map (fun k -> mk_binop `(<=):num->num->bool` (top_a k)
                    `LENGTH(blk:byte list)`) [0;1;2;3]);;

(*** The paths after HUF_DecompressFastArgs_init: 0, the slow path; 1, the ***)
(*** fast loop and the finishes of the four streams                       ***)

let TOP_FA0_TAC = TOP_STEPS_TAC 3 THEN TOP_SLOW_TAC;;

let TOP_FAST_SETUP_TAC : tactic =
  TOP_FA1_SETUP_TAC THEN TOP_FL_TAC THEN TOP_HIDE_TAC THEN
  TOP_STEPS_TAC 4 THEN FA_STATE_REWRITE_TAC[ASSUME `(n + 3) DIV 4 = q`] THEN
  TOP_FIN_FACTS_TAC;;

let TOP_FA1_TAC : tactic =
  TOP_FAST_SETUP_TAC THEN TOP_PASSES_TAC 0;;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For the block blk of four streams at src, the decoding  *)
(* table (built by HUF_readDTableX1_wksp) for the weights ws, with codes of  *)
(* at most ml bits and a table of tl bits, at DTable + 4, its header holding *)
(* tl at DTable + 2, and the n bytes at dst: if blk is the four streams of   *)
(* the n bytes out (huf_streams4 T), the result is n, with out at dst; the   *)
(* result is always n or an error code; and with bit 5 of the flags set      *)
(* (HUF_flags_disableFast), the result is an error code when there is no     *)
(* such out. The loads are from the block, the table and its header and the  *)
(* stack, the stores to the n bytes at dst and the stack, whose region of    *)
(* 688 bytes is the frame of 496 bytes and the 192 bytes of the fast loop    *)
(* below it.                                                                 *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS4X1_USINGDTABLE_CORRECT = prove
 (`!pc returnaddress stackpointer dst n src (blk:byte list) dtable flags
    ws ml tl e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\
     huf_complete ws ml /\ LENGTH ws <= 256 /\
     1 <= ml /\ ml <= tl /\ tl <= 12 /\
     n < 2 EXP 28 /\ val(dst:int64) + n + 3 < 2 EXP 64 /\
     8 <= val(src:int64) /\ val src + LENGTH blk + 8 < 2 EXP 64 /\
     LENGTH blk < 2 EXP 32 /\
     nonoverlapping (dst,n) (src,LENGTH blk) /\
     nonoverlapping (dst,n) (dtable,4 + 2 * 2 EXP tl) /\
     nonoverlapping (dst,n) (word_sub stackpointer (word 688),688) /\
     nonoverlapping (dst,n) (word pc,32000) /\
     nonoverlapping (word_sub stackpointer (word 688),688) (src,LENGTH blk) /\
     nonoverlapping (word_sub stackpointer (word 688),688)
                    (dtable,4 + 2 * 2 EXP tl) /\
     nonoverlapping (word_sub stackpointer (word 688),688) (word pc,32000) /\
     nonoverlapping (src,LENGTH blk) (dtable,4 + 2 * 2 EXP tl) /\
     nonoverlapping (src,LENGTH blk) (word pc,32000) /\
     nonoverlapping (dtable,4 + 2 * 2 EXP tl) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x5300) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; word n; src; word(LENGTH blk); dtable;
                            flags] s /\
               read (memory :> bytes(src,LENGTH blk)) s =
               num_of_bytelist blk /\
               read (memory :> bytes8(word_add dtable (word 2))) s = word tl /\
               read (memory :> bytes(word_add dtable (word 4),2 * 2 EXP tl))
                    s =
               num_of_bytelist(huf_dtable ws ml tl) /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!out. LENGTH out = n /\ huf_streams4 T ws ml blk out
                      ==> read X0 s = word n /\
                          read (memory :> bytes(dst,n)) s =
                          num_of_bytelist out) /\
               (read X0 s = word n \/ zstd_is_error(read X0 s)) /\
               (bit 5 flags /\
                (!out. LENGTH out = n ==> ~huf_streams4 T ws ml blk out)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH blk; dtable,4 + 2 * 2 EXP tl;
                       word_sub stackpointer (word 688),688]
                      [dst,n; word_sub stackpointer (word 688),688]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,n);
                      memory :> bytes(word_sub stackpointer (word 688),688)])`,
  TOP_START_TAC THEN TOP_PROLOGUE_TAC THENL
   [TOP_SLOW_TAC;
    TOP_FA_TAC THENL [TOP_FA0_TAC; TOP_FA1_TAC; TOP_FA20_TAC]]);;

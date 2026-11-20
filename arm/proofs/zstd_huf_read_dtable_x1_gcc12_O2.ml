(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decoding table for the single-symbol decoding of Huffman-coded        *)
(* streams: zstd's HUF_readDTableX1_wksp, compiled by gcc 12 at -O2 for      *)
(* AArch64.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode1x1_gcc12_O2.ml";;
needs "arm/proofs/zstd_huf_read_stats_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_readDTableX1_wksp at 0x66d4 reads the description of a Huffman tree   *)
(* at src with HUF_readStats_wksp, called at 0x672c, and fills the decoding  *)
(* table at dtable + 4, 2 bytes an entry, with a workspace wk of at least    *)
(* 1492 bytes: rankVal at wk and rankStart at wk + 52 (13 words each), the   *)
(* workspace of HUF_readStats_wksp at wk + 104, the symbols at wk + 980 and  *)
(* the weights at wk + 1236. The table log tl is the larger of the           *)
(* Max_Number_of_Bits ml of the description and MIN (mtl + 1) 11, mtl being  *)
(* the byte 0 of the header at dtable. When ml is smaller, the weights are   *)
(* raised by the difference k in place (the loop at 0x6798), rankVal moved   *)
(* up by k (the loop at 0x67d0) and the words below zeroed by memset; a      *)
(* table log above mtl + 1 is an error. The header byte 2 gets tl (0x67fc),  *)
(* rankStart the start of each weight among the sorted symbols (the loop at  *)
(* 0x6828), and a counting sort stores the symbols in the order of their     *)
(* weights, four at a time (0x6850) and then one at a time (0x68b4). The     *)
(* loop at 0x6908 over the weights fills the table, with loops for 1, 2, 4   *)
(* and 8 entries a symbol and one for more, 16 entries at a time. The table  *)
(* is huf_dtable ws tl tl for the weights ws raised, which is huf_dtable ws0 *)
(* ml tl for those of the description (HUF_DTABLE_RESCALE). The pieces are   *)
(* proved from the end: the loops for the symbols of one weight (RD_L1,      *)
(* RD_L2, RD_L4, RD_L8, RD_LGI and RD_LGO), the loop over the weights        *)
(* (RD_FILL), the sort (RD_SORTR and RD_SORT4), rankStart (RD_RANKSTART),    *)
(* the header (RD_HEADER) and the raising (RD_RESCALE_R and RD_RESCALE_W),   *)
(* each going on with the later pieces to the return, then the whole         *)
(* function. Each has the conjunct puff_memsafe e rr wr s, for the trace e   *)
(* at the entry of the function.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The table for the weights raised by k, as that for the weights as they    *)
(* are with more states, and the entries of the states of one symbol as zstd *)
(* stores them, huf_dblock, a block of the table, with the values of its     *)
(* 64-bit and 128-bit stores of them.                                        *)
(* ------------------------------------------------------------------------- *)

(*** The table for the weights raised by k ***)

let HUF_DTABLE_RESCALE = prove
 (`!ws ml k.
        huf_total ws = 2 EXP ml
        ==> huf_dtable (huf_rescale k ws) (ml + k) (ml + k) =
            huf_dtable ws ml (ml + k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_dtable] THEN
  REWRITE_TAC[SUB_REFL; EXP; DIV_1; ARITH_RULE `(m + k) - m = k`] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `i DIV 2 < 2 EXP k * huf_total ws` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM EXP_ADD] THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[HUF_SYMBOL_RESCALE] THEN
  MP_TAC(SPECL [`ws:num list`; `(i DIV 2) DIV 2 EXP k`] HUF_SYMBOL) THEN
  ANTS_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC `i < 2 * 2 EXP (ml + k)` THEN
    ASM_REWRITE_TAC[EXP_ADD] THEN REWRITE_TAC[MULT_AC];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  SPEC_TAC(`huf_symbol ws ((i DIV 2) DIV 2 EXP k)`,`s:num`) THEN
  REWRITE_TAC[huf_present; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_HUF_RESCALE] THEN
  REWRITE_TAC[ARITH_RULE `((m + k) + 1) - (e + k) = (m + 1) - e`]);;

(*** The entries of the table for the states of one symbol ***)

let huf_dblock = new_definition
 `huf_dblock n nb sym =
    list_of_seq (\i. if EVEN i then word nb else word sym:byte) (2 * n)`;;

let LENGTH_HUF_DBLOCK = prove
 (`!n nb sym. LENGTH(huf_dblock n nb sym) = 2 * n`,
  REWRITE_TAC[huf_dblock; LENGTH_LIST_OF_SEQ]);;

let HUF_DTABLE_BLOCK = prove
 (`!ws tl w j.
        huf_total ws = 2 EXP tl /\ ~(w = 0) /\ j < huf_rank ws w
        ==> SUB_LIST(2 * (huf_ustart ws w + j * 2 EXP (w - 1)),
                     2 * 2 EXP (w - 1)) (huf_dtable ws tl tl) =
            huf_dblock (2 EXP (w - 1)) ((tl + 1) - w)
                       (huf_sorted ws (huf_bstart ws w + j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_BLOCK_END) THEN
  ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `u = huf_ustart ws w + j * 2 EXP (w - 1)` THEN
  ABBREV_TAC `L = 2 EXP (w - 1)` THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH_HUF_DTABLE;
              LENGTH_HUF_DBLOCK] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 2 * L` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_HUF_DTABLE;
    ARITH_RULE `u + L <= t ==> 2 * u + 2 * L <= 2 * t`] THEN
  ASM_SIMP_TAC[huf_dblock; EL_LIST_OF_SEQ] THEN
  MP_TAC(REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS] (SPEC `i:num` EVEN_OR_ODD)) THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `q:num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[EVEN_DOUBLE; EVEN_ADD; ARITH_EVEN; EVEN_MULT; EVEN;
              ARITH_RULE `2 * u + 2 * q = 2 * (u + q)`;
              ARITH_RULE `2 * u + SUC(2 * q) = 2 * (u + q) + 1`] THEN
  MP_TAC(SPECL [`ws:num list`; `tl:num`; `tl:num`; `u + q`]
    HUF_DTABLE_ENTRY) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[SUB_REFL; EXP; DIV_1] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`; `u + q`]
    HUF_SYMBOL_BLOCK) THEN
  ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_SIMP_TAC[]);;

(*** The bytes of the entries of one symbol, as the code stores them ***)

let HUF_DBLOCK_ADD = prove
 (`!m n nb sym. huf_dblock (m + n) nb sym =
                APPEND (huf_dblock m nb sym) (huf_dblock n nb sym)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_APPEND; LENGTH_HUF_DBLOCK] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 2 * (m + n)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EL_APPEND; LENGTH_HUF_DBLOCK] THEN
  ASM_CASES_TAC `i < 2 * m` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[huf_dblock; EL_LIST_OF_SEQ;
    ARITH_RULE `~(i < 2 * m) /\ i < 2 * (m + n) ==> i - 2 * m < 2 * n`] THEN
  REWRITE_TAC[EVEN_SUB; EVEN_DOUBLE] THEN
  ASM_CASES_TAC `i = 2 * m` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[EVEN_DOUBLE; LE_REFL];
    ASM_SIMP_TAC[ARITH_RULE
     `~(i < 2 * m) /\ ~(i = 2 * m) ==> ~(i <= 2 * m)`]]);;

let HUF_DBLOCK_1 = prove
 (`!nb sym. huf_dblock 1 nb sym = [word nb; word sym]`,
  REWRITE_TAC[huf_dblock] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN REWRITE_TAC[ARITH]);;

let NUM_OF_HUF_DBLOCK = prove
 (`!n nb sym.
        nb < 256 /\ sym < 256
        ==> num_of_bytelist(huf_dblock n nb sym) =
            (nb + 256 * sym) * nsum {i | i < n} (\i. 65536 EXP i)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[huf_dblock; MULT_CLAUSES; list_of_seq; num_of_bytelist;
                NSUM_CLAUSES_NUMSEG_LT];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1; HUF_DBLOCK_ADD; NUM_OF_BYTELIST_APPEND; HUF_DBLOCK_1] THEN
  ASM_REWRITE_TAC[LENGTH_HUF_DBLOCK; GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `2 EXP (8 * 2 * n) = 65536 EXP n` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`; GSYM EXP_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_RING]);;

(* ------------------------------------------------------------------------- *)
(* The array of the symbols at wk + 980 as the counting sort fills it,       *)
(* rd_symlist ws k l0, the positions of the first k symbols holding them and *)
(* the others the bytes l0 there before.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The sorted symbols as they are stored one at a time, the others       ***)
(*** being the bytes l0 there before                                       ***)

let rd_symlist = new_definition
 `rd_symlist ws k (l0:byte list) =
    list_of_seq (\p. if ?i. i < k /\ huf_pos ws i = p
                     then word(huf_sorted ws p) else EL p l0) 256`;;

let LENGTH_RD_SYMLIST = prove
 (`!ws k l0. LENGTH(rd_symlist ws k l0) = 256`,
  REWRITE_TAC[rd_symlist; LENGTH_LIST_OF_SEQ]);;

let RD_SYMLIST_0 = prove
 (`!ws l0. LENGTH l0 = 256 ==> rd_symlist ws 0 l0 = l0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rd_symlist; CONJUNCT1 LT; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let EL_RD_SYMLIST_STEP = prove
 (`!ws k l0 p.
        k < LENGTH ws /\ p < 256
        ==> EL p (rd_symlist ws (k + 1) l0) =
            if p = huf_pos ws k then word k else EL p (rd_symlist ws k l0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[rd_symlist; EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[ARITH_RULE `i < k + 1 <=> i < k \/ i = k`] THEN
  ASM_CASES_TAC `p = huf_pos ws k` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[HUF_SORTED_POS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?i. (i < k \/ i = k) /\ huf_pos ws i = p) <=>
                (?i. i < k /\ huf_pos ws i = p)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

let RD_SYMLIST_FULL = prove
 (`!ws l0 p.
        LENGTH ws <= 256 /\ p < LENGTH ws
        ==> EL p (rd_symlist ws (LENGTH ws) l0) = word(huf_sorted ws p)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[rd_symlist; EL_LIST_OF_SEQ; ARITH_RULE
    `p < n /\ n <= 256 ==> p < 256`] THEN
  MP_TAC(SPECL [`ws:num list`; `p:num`] HUF_POS_SURJ) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The setting of the pieces: their regions, hypotheses and frame, their     *)
(* goals (mk_rd_goal), the postcondition at the return (rd_fpost), the facts *)
(* in the frame of 112 bytes (rd_common), those about the weights and the    *)
(* workspace while the table is filled (rd_tables) and the invariant of the  *)
(* loop over the weights at 0x6908 (rd_finv).                                *)
(* ------------------------------------------------------------------------- *)

(*** The regions, the hypotheses and the frame ***)

let rd_rr =
 `[src,LENGTH(l:byte list); dtable,4 + 2 * 2 EXP (mtl + 1); wk,1492;
   word_sub stackpointer (word 432),432;
   word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
   word_add (word pc) (word 31600),128]:(int64#num)list`
and rd_wr =
 `[dtable,4 + 2 * 2 EXP (mtl + 1); wk,1492;
   word_sub stackpointer (word 432),432]:(int64#num)list`;;

let rd_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\ mtl <= 12 /\
  nonoverlapping (dtable:int64,4 + 2 * 2 EXP (mtl + 1)) (wk:int64,1492) /\
  nonoverlapping (dtable,4 + 2 * 2 EXP (mtl + 1))
                 (word_sub stackpointer (word 432),432) /\
  nonoverlapping (dtable,4 + 2 * 2 EXP (mtl + 1)) (word pc,0x20018) /\
  nonoverlapping (wk,1492) (word_sub stackpointer (word 432),432) /\
  nonoverlapping (wk,1492) (word pc,0x20018) /\
  nonoverlapping (word_sub stackpointer (word 432),432) (word pc,0x20018)`;;

let rd_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X29; X30; SP] ,,
  MAYCHANGE [memory :> bytes(dtable,4 + 2 * 2 EXP (mtl + 1));
             memory :> bytes(wk,1492);
             memory :> bytes(word_sub stackpointer (word 432),432)]`;;

let rd_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `dtable:int64`;
  `src:int64`; `l:byte list`; `wk:int64`; `ea:int64`; `el:num`;
  `mtl:num`; `ws:num list`; `tl:num`; `h:num`; `l0:byte list`;
  `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`; `x23:int64`;
  `x24:int64`; `x25:int64`; `x26:int64`; `x29:int64`;
  `e:uarch_event list`];;

let mk_rd_goal extra hyps pre post =
  let tm = mk_imp(hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; rd_frame]) in
  let vs = rd_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_rd_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** At the return after the table is filled, for the weights ws and the   ***)
(*** table log tl                                                          ***)

let rd_fpost = with_memsafe rd_rr rd_wr `\s.
  read PC s = returnaddress /\ read SP s = stackpointer /\
  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
  read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
  read X25 s = x25 /\ read X26 s = x26 /\ read X29 s = x29 /\
  read X30 s = returnaddress /\
  read X0 s = word h /\
  read (memory :> bytes8 (word_add dtable (word 2))) s = word tl /\
  read (memory :> bytes(word_add dtable (word 4),2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws tl tl)`;;

(*** The facts that hold all through, in the frame of 112 bytes ***)

let rd_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read SP s = word_sub stackpointer (word 112) /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 16))) s = x29 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 24))) s =
  returnaddress /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 32))) s = x19 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 40))) s = x20 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 48))) s = x21 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 56))) s = x22 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 64))) s = x23 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 72))) s = x24 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 80))) s = x25 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 112)) (word 88))) s = x26 /\
  read X19 s = wk /\ read X20 s = dtable /\ read X21 s = word h`;;

(*** The facts about the weights and the tables of the workspace for the   ***)
(*** filling of the table: the numbers of the weights, the symbols         ***)
(*** sorted by their weights, tl and the header byte of the table          ***)

let rd_tables =
 `ALL (\x. x <= tl) ws /\ LENGTH ws <= 256 /\ huf_total ws = 2 EXP tl /\
  1 <= tl /\ tl <= mtl + 1 /\ tl <= 12 /\
  read (memory :> bytes(wk,4 * (tl + 1))) s =
  num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) (tl + 1)) /\
  read (memory :> bytes(word_add wk (word 980),256)) s =
  num_of_bytelist(rd_symlist ws (LENGTH ws) l0) /\
  read (memory :> bytes8 (word_add dtable (word 2))) s = word tl`;;

(*** At 0x6908, the loop over the weights w from 1 to tl, for the measure  ***)
(*** m = tl + 1 - w                                                        ***)

let rd_finv = with_memsafe rd_rr rd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`w:num`,list_mk_conj
    [`m = (tl + 1) - w /\ 1 <= w /\ w <= tl /\
      read PC s = word(pc + 0x6908) /\
      read X0 s = word w /\ read X13 s = word 1 /\ read X15 s = word 4 /\
      read X14 s = word_add wk (word 1) /\
      read X11 s = word_add dtable (word 4) /\
      read X10 s = word_add dtable (word 36) /\
      read X16 s = word_add dtable (word 6) /\
      read X12 s = word(tl + 1) /\ read X7 s = word(tl + 1) /\
      read X9 s = word(huf_ustart ws w) /\
      read X8 s = word(huf_bstart ws w) /\
      read (memory :> bytes(word_add dtable (word 4),
                            2 * huf_ustart ws w)) s =
      num_of_bytelist(SUB_LIST(0,2 * huf_ustart ws w) (huf_dtable ws tl tl))`;
     rd_tables;
     rd_common])));;

(* ------------------------------------------------------------------------- *)
(* The loops over the symbols of one weight w from 1 to 4 (a numeral, 2^(w - *)
(* 1) entries for each symbol): the loop for the weight 2 at 0x6960 (RD_L2), *)
(* for the weight 1 at 0x6ad8 (RD_L1), for the weight 3 at 0x6b30 (RD_L4)    *)
(* and for the weight 4 at 0x69e0 (RD_L8). Each goes on to the loop over the *)
(* weights at 0x6908 or the return, its postcondition being mk_rd_wpost w.   *)
(* ------------------------------------------------------------------------- *)

(*** The loops over the symbols of one weight w, the first j of them       ***)
(*** done, for the measure huf_rank ws w - j                               ***)

let rd_fixed =
 `read X0 s = word w /\ read X13 s = word 1 /\ read X15 s = word 4 /\
  read X14 s = word_add wk (word 1) /\
  read X11 s = word_add dtable (word 4) /\
  read X10 s = word_add dtable (word 36) /\
  read X16 s = word_add dtable (word 6) /\
  read X12 s = word(tl + 1) /\ read X7 s = word(tl + 1) /\
  read X9 s = word(huf_ustart ws w) /\
  read X8 s = word(huf_bstart ws w) /\
  read X6 s = word(huf_rank ws w) /\
  read X5 s = word(2 EXP (w - 1)) /\
  read X3 s = word((tl + 1) - w)`;;

let rd_prefix =
 `read (memory :> bytes(word_add dtable (word 4),
                        2 * (huf_ustart ws w + j * 2 EXP (w - 1)))) s =
  num_of_bytelist(SUB_LIST(0,2 * (huf_ustart ws w + j * 2 EXP (w - 1)))
                          (huf_dtable ws tl tl))`;;

let rd_numeral_conv t =
  rhs(concl((DEPTH_CONV NUM_RED_CONV THENC REWRITE_CONV[MULT_CLAUSES]) t));;

let mk_rd_inner pcoff wv regs =
  let tm = with_memsafe rd_rr rd_wr
   (list_mk_abs([`m:num`; `s:armstate`],
     mk_exists(`j:num`,list_mk_conj
      [mk_conj(`m = huf_rank ws w - j /\ j < huf_rank ws w /\
                1 <= w /\ w <= tl`,
               mk_eq(`read PC s`,
                     mk_comb(`word:num->int64`,
                             mk_binop `(+):num->num->num` `pc:num`
                                      (mk_small_numeral pcoff))));
       regs; rd_fixed; rd_prefix; rd_tables; rd_common]))) in
  rd_numeral_conv(subst [wv,`w:num`] tm);;

(*** After the symbols of the weight w: the loop over the weights goes on ***)

let mk_rd_wpost wv =
  let s = `s:armstate` in
  rd_numeral_conv(subst [wv,`w:num`]
   (mk_abs(s,mk_disj(mk_exists(`m':num`,
                       mk_conj(`m' < (tl + 1) - w`,
                               list_mk_comb(rd_finv,[`m':num`; s]))),
                     mk_comb(rd_fpost,s)))));;

(*** The loop for the weight 2, two entries for each symbol, at 0x6960 ***)

let rd_l2inv = mk_rd_inner 0x6960 `2`
 `read X2 s = word_add wk (word(huf_bstart ws w + j)) /\
  read X17 s = word_add wk (word(huf_bstart ws w + huf_rank ws w)) /\
  read X1 s = word_add dtable
                (word(4 + 2 * (huf_ustart ws w + j * 2 EXP (w - 1))))`;;

(*** The branch in the current state on the equality of two pointers with  ***)
(*** the same base, decided by the arithmetic of their offsets             ***)

let RD_PTR_BRANCH_TAC =
  let norm = REWRITE_CONV[WORD_ADD_ASSOC_NUM] in
  let conv asl tm =
    let th0 = BINOP_CONV (RAND_CONV norm) tm in
    let ith = PART_MATCH (lhs o rand) PTR_EQ_OFFSETS
                (rand(concl th0)) in
    let ant = lhand(concl ith) in
    TRANS th0 (MP ith (TAC_PROOF((asl,ant),
      CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THEN SIMPLE_ARITH_TAC))) in
  W(fun (asl,w) ->
    let s = rand w in
    let pc = mk_comb(`read PC`,s) in
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && lhs c = pc then
        CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV(conv asl))) th
      else th) THEN
    ZSTD_DECIDE_BRANCH_TAC THEN PC_COND_NORM_TAC THEN TRY DECIDE_IFS_TAC);;

(*** The value of a 64-bit store of four entries for nb and sym ***)

let NSUM_65536_4 = prove
 (`nsum {i | i < 4} (\i. 65536 EXP i) = 281479271743489`,
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`;
              NSUM_CLAUSES_NUMSEG_LT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_WORD_HUF_DBLOCK4 = prove
 (`!nb sym.
        nb < 256 /\ sym < 256
        ==> val(word((65536 * (nb + 256 * sym) + nb + 256 * sym) +
                     4294967296 *
                     (65536 * (nb + 256 * sym) + nb + 256 * sym)):int64) =
            num_of_bytelist(huf_dblock 4 nb sym)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NUM_OF_HUF_DBLOCK; NSUM_65536_4] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC(MESON[MOD_LT] `x = y /\ y < n ==> x MOD n = y`) THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`nb < 256`; `sym < 256`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let NSUM_65536_8 = prove
 (`nsum {i | i < 8} (\i. 65536 EXP i) =
   281479271743489 * 18446744073709551617`,
  REWRITE_TAC[ARITH_RULE `8 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))`;
              NSUM_CLAUSES_NUMSEG_LT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_WORD_JOIN_HUF_DBLOCK8 = prove
 (`!nb sym.
        nb < 256 /\ sym < 256
        ==> val(word_join
                 (word((65536 * (nb + 256 * sym) + nb + 256 * sym) +
                       4294967296 *
                       (65536 * (nb + 256 * sym) + nb + 256 * sym)):int64)
                 (word((65536 * (nb + 256 * sym) + nb + 256 * sym) +
                       4294967296 *
                       (65536 * (nb + 256 * sym) + nb + 256 * sym)):int64)
                :int128) =
            num_of_bytelist(huf_dblock 8 nb sym)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  ASM_SIMP_TAC[VAL_WORD_HUF_DBLOCK4; NUM_OF_HUF_DBLOCK; NSUM_65536_4;
               NSUM_65536_8] THEN
  ARITH_TAC);;

(*** A block of the entries of a symbol extended by a chunk of 16 entries  ***)
(*** in two 128-bit stores                                                 ***)

let READ_MEMORY_HUF_DBLOCK_CHUNK = prove
 (`!a:int64 k nb sym v s:armstate.
        read (memory :> bytes(a,32 * k)) s =
        num_of_bytelist(huf_dblock (16 * k) nb sym) /\
        read (memory :> bytes128(word_add a (word(32 * k)))) s = v /\
        read (memory :> bytes128(word_add a (word(32 * k + 16)))) s = v /\
        val v = num_of_bytelist(huf_dblock 8 nb sym)
        ==> read (memory :> bytes(a,32 * (k + 1))) s =
            num_of_bytelist(huf_dblock (16 * (k + 1)) nb sym)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `32 * (k + 1) = 32 * k + 16 + 16`;
              ARITH_RULE `16 * (k + 1) = 16 * k + 8 + 8`; HUF_DBLOCK_ADD] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_HUF_DBLOCK] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[VAL_READ_MEMORY_BYTES128; WORD_ADD_ASSOC_NUM] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The start of the proof of a loop for the invariant at the measure     ***)
(*** m, with the variable v of the invariant                               ***)

let RD_START_VAR_TAC v =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC v THEN PUFF_INIT_TAC "s0";;

(*** The facts for the symbol at the position bstart + j of the sorted     ***)
(*** symbols, for the weight w (a numeral), with j < huf_rank ws w among   ***)
(*** the assumptions: the symbol and its load from the state s0, its       ***)
(*** entries in the table and their end, as a linear fact about            ***)
(*** dsz = 2^(mtl + 1) (abbreviated with tt = 2^tl at the end, since       ***)
(*** NONOVERLAPPING_TAC does not use facts with EXP of variables)          ***)

let RD_SYMBOL_TAC w =
  let bj = mk_binop `(+):num->num->num`
             (mk_comb(`huf_bstart ws`,w)) `j:num` in
  MP_TAC(SPECL [`ws:num list`; w; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN NUM_REDUCE_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; bj] HUF_SORTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   (list_mk_conj
     [mk_binop `(<):num->num->bool`
        (mk_binop `(-):num->num->num` `tl + 1` w) `256`;
      mk_binop `(<):num->num->bool` (mk_comb(`huf_sorted ws`,bj)) `256`])
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; mk_binop `(+):num->num->num` w `1`]
    HUF_BSTART_LE) THEN
  REWRITE_TAC[HUF_BSTART_SUC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`word_add wk (word 980):int64`;
                 `rd_symlist ws (LENGTH ws) l0`; bj; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_RD_SYMLIST] THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [mk_binop `(<):num->num->bool` bj `LENGTH(ws:num list)`;
      `LENGTH(ws:num list) <= 256`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RD_SYMLIST_FULL] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add wk (word 980)) (word n):int64 =
                         word_add wk (word(n + 980))`] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `tl:num`; w; `j:num`] HUF_DTABLE_BLOCK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  NUM_REDUCE_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ws:num list`; w; `j:num`] HUF_BLOCK_END) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN NUM_REDUCE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP tl <= 2 EXP (mtl + 1) /\ 2 EXP (mtl + 1) <= 8192`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    SUBST1_TAC(ARITH_RULE `8192 = 2 EXP 13`) THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`tl <= mtl + 1`; `mtl <= 12`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `dsz = 2 EXP (mtl + 1)` THEN
  ABBREV_TAC `tt = 2 EXP tl`;;

(*** The table prefix in the state s extended by the entries of the symbol ***)
(*** bstart + j for the weight w, of 2^(w - 1) = L entries (numerals),     ***)
(*** with blocktac proving that they are in memory as huf_dblock           ***)

let RD_EXTEND_TAC w L s blocktac =
  let inst t =
    rd_numeral_conv(subst [w,`w:num`; L,`L:num`; s,`s:armstate`] t) in
  let blk = inst
    `huf_dblock L ((tl + 1) - w) (huf_sorted ws (huf_bstart ws w + j))` in
  let p = inst `2 * (huf_ustart ws w + j * L)` in
  let n = inst `2 * L` in
  SUBGOAL_THEN
   (inst `read (memory :> bytes(word_add (word_add dtable (word 4))
                                         (word(2 * (huf_ustart ws w + j * L))),
                                LENGTH(huf_dblock L ((tl + 1) - w)
                                  (huf_sorted ws (huf_bstart ws w + j))))) s =
          num_of_bytelist(huf_dblock L ((tl + 1) - w)
                                     (huf_sorted ws (huf_bstart ws w + j)))`)
  MP_TAC THENL [blocktac; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_HUF_DBLOCK] THEN NUM_REDUCE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = blk
                        then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`word_add dtable (word 4):int64`; `huf_dtable ws tl tl`;
                 p; n; s] READ_MEMORY_BYTELIST_EXTEND) THEN
  ASM_REWRITE_TAC[LENGTH_HUF_DTABLE] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_binop `(+):num->num->num` p n,
                      inst `2 * (huf_ustart ws w + (j + 1) * L)`))
   SUBST1_TAC THENL [ARITH_TAC; DISCH_TAC];;

(*** Entries stored one byte at a time ***)

let RD_BYTES8_BLOCK_TAC =
  MATCH_MP_TAC READ_MEMORY_BYTELIST_BYTES8 THEN
  REWRITE_TAC[LENGTH_HUF_DBLOCK; huf_dblock] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[ARITH; WORD_ADD_ASSOC_NUM; WORD_ADD_0; ADD_ASSOC;
              ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[];;

(*** Entries stored 64 bits at a time ***)

let RD_BYTES64_BLOCK_TAC =
  REWRITE_TAC[LENGTH_HUF_DBLOCK] THEN NUM_REDUCE_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_8; WORD_ADD_ASSOC_NUM] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[VAL_WORD_HUF_DBLOCK4];;

(*** The end of an iteration of a loop over the symbols of one weight:     ***)
(*** the next symbol j + 1 of that weight, the pointers in the registers   ***)
(*** moved on                                                              ***)

let RD_NEXT_SYMBOL_TAC w =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC (subst [w,`w:num`] `huf_rank ws w - (j + 1)`) THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `j + 1`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
  ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  REPEAT CONJ_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(*** The end of the symbols of the weight w, j + 1 = huf_rank ws w, with   ***)
(*** the branch back to 0x6908 as the step n: the next weight w + 1, or    ***)
(*** the return in k more steps for w = tl, with the whole table           ***)

let RD_NEXT_WEIGHT_TAC w n k =
  let w1 = rd_numeral_conv(mk_binop `(+):num->num->num` w `1`) in
  let L = rd_numeral_conv(subst [w,`w:num`] `2 EXP (w - 1)`) in
  let norm = CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[MULT_CLAUSES]) in
  let usuc = norm(SPECL [`ws:num list`; w] HUF_USTART_SUC)
  and bsuc = norm(SPECL [`ws:num list`; w] HUF_BSTART_SUC) in
  let jr = subst [w,`w:num`] `j + 1 = huf_rank ws w` in
  ASM_CASES_TAC (mk_binop `(<=):num->num->bool` w1 `tl:num`) THENL
   [ZSTD_STEPS_TAC [n] THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC (subst [w1,`w:num`] `(tl + 1) - w`) THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC w1] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = jr)) THEN
    REWRITE_TAC[usuc; bsuc] THEN ASM_REWRITE_TAC[] THEN NUM_REDUCE_TAC;
    SUBGOAL_THEN (mk_eq(`tl:num`,w)) SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (n--(n+k)) THEN
    PUFF_FINAL_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN (rd_numeral_conv(subst [w,`w:num`; L,`L:num`]
                   `huf_ustart ws w + (j + 1) * L = tt`)) SUBST_ALL_TAC THENL
     [MP_TAC(SPECL [`ws:num list`; w] HUF_USTART_ALL) THEN
      ASM_REWRITE_TAC[] THEN NUM_REDUCE_TAC THEN REWRITE_TAC[usuc] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (subst [w,`w:num`]
      `SUB_LIST(0,2 * tt) (huf_dtable ws w w) = huf_dtable ws w w`)
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC SUB_LIST_REFL THEN
      REWRITE_TAC[LENGTH_HUF_DTABLE] THEN ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE];;

(*** The loop for the weight 2 ***)

let rd_l2goal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_l2inv,[`m:num`; `s:armstate`]))))
  (mk_rd_wpost `2`);;

let RD_L2 = prove
 (rd_l2goal,
  RD_START_VAR_TAC `j:num` THEN RD_SYMBOL_TAC `2` THEN
  ZSTD_STEPS_TAC (1--8) THEN
  RD_EXTEND_TAC `2` `2` `s8:armstate` RD_BYTES8_BLOCK_TAC THEN
  ASM_CASES_TAC `j + 1 < huf_rank ws 2` THENL
   [ZSTD_STEPS_TAC [9] THEN RD_PTR_BRANCH_TAC THEN RD_NEXT_SYMBOL_TAC `2`;
    SUBGOAL_THEN `j + 1 = huf_rank ws 2` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC [9] THEN RD_PTR_BRANCH_TAC THEN
    ZSTD_STEPS_TAC (10--13) THEN RD_NEXT_WEIGHT_TAC `2` 14 8]);;

(*** The loop for the weight 1, one entry for each symbol, at 0x6ad8 ***)

let rd_l1inv = mk_rd_inner 0x6ad8 `1`
 `read X2 s = word_add wk (word(huf_bstart ws w + j)) /\
  read X17 s =
  word_add dtable
   (word(4 + 2 * (huf_ustart ws w + huf_rank ws w * 2 EXP (w - 1)))) /\
  read X1 s = word_add dtable
                (word(4 + 2 * (huf_ustart ws w + j * 2 EXP (w - 1))))`;;

let rd_l1goal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_l1inv,[`m:num`; `s:armstate`]))))
  (mk_rd_wpost `1`);;

let RD_L1 = prove
 (rd_l1goal,
  RD_START_VAR_TAC `j:num` THEN RD_SYMBOL_TAC `1` THEN
  ZSTD_STEPS_TAC (1--5) THEN
  RD_EXTEND_TAC `1` `1` `s5:armstate` RD_BYTES8_BLOCK_TAC THEN
  ASM_CASES_TAC `j + 1 < huf_rank ws 1` THENL
   [ZSTD_STEPS_TAC (6--7) THEN RD_PTR_BRANCH_TAC THEN RD_NEXT_SYMBOL_TAC `1`;
    SUBGOAL_THEN `j + 1 = huf_rank ws 1` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (6--7) THEN RD_PTR_BRANCH_TAC THEN
    ZSTD_STEPS_TAC (8--11) THEN RD_NEXT_WEIGHT_TAC `1` 12 9]);;

(*** The loop for the weight 3, four entries for each symbol, at 0x6b30 ***)

let rd_l4inv = mk_rd_inner 0x6b30 `3`
 `read X2 s = word j /\
  read X4 s = word_add wk (word(huf_bstart ws w + 980)) /\
  read X18 s = word_add dtable (word(4 + 2 * huf_ustart ws w))`;;

let rd_l4goal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_l4inv,[`m:num`; `s:armstate`]))))
  (mk_rd_wpost `3`);;

(*** The symbol in the form of the address of its load at 0x6b30 and       ***)
(*** 0x69e0, and the index register of that load                           ***)

let RD_SYMBOL_INDEXED_TAC w =
  RD_SYMBOL_TAC w THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in
    is_eq c && can (find_term ((=) `980`)) c &&
    can (find_term ((=) `s0:armstate`)) c &&
    not(can (find_term ((=) `256`)) c))) THEN
  REWRITE_TAC[ARITH_RULE `(b + j) + 980 = (b + 980) + j`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN SIMPLE_ARITH_TAC; ALL_TAC];;

let RD_L4 = prove
 (rd_l4goal,
  RD_START_VAR_TAC `j:num` THEN RD_SYMBOL_INDEXED_TAC `3` THEN
  ZSTD_STEPS_TAC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
    `(4 + 2 * u) + 8 * j = 4 + 2 * (u + j * 4)`]) THEN
  RD_EXTEND_TAC `3` `4` `s6:armstate` RD_BYTES64_BLOCK_TAC THEN
  ASM_CASES_TAC `j + 1 < huf_rank ws 3` THENL
   [ZSTD_STEPS_TAC (7--9) THEN RD_NEXT_SYMBOL_TAC `3`;
    SUBGOAL_THEN `j + 1 = huf_rank ws 3` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (7--13) THEN RD_NEXT_WEIGHT_TAC `3` 14 9]);;

(*** The loop for the weight 4, eight entries for each symbol, at 0x69e0 ***)

let rd_l8inv = mk_rd_inner 0x69e0 `4`
 `read X2 s = word j /\
  read X4 s = word_add wk (word(huf_bstart ws w + 980)) /\
  read X22 s = word_add dtable (word(4 + 2 * huf_ustart ws w))`;;

let rd_l8goal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_l8inv,[`m:num`; `s:armstate`]))))
  (mk_rd_wpost `4`);;

(*** Entries stored 128 bits at a time ***)

let RD_BYTES128_BLOCK_TAC =
  REWRITE_TAC[LENGTH_HUF_DBLOCK] THEN NUM_REDUCE_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_16; WORD_ADD_ASSOC_NUM] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[VAL_WORD_JOIN_HUF_DBLOCK8];;

let RD_L8 = prove
 (rd_l8goal,
  RD_START_VAR_TAC `j:num` THEN RD_SYMBOL_INDEXED_TAC `4` THEN
  ZSTD_STEPS_TAC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
    `(4 + 2 * u) + 16 * j = 4 + 2 * (u + j * 8)`]) THEN
  RD_EXTEND_TAC `4` `8` `s9:armstate` RD_BYTES128_BLOCK_TAC THEN
  ASM_CASES_TAC `j + 1 < huf_rank ws 4` THENL
   [ZSTD_STEPS_TAC (10--11) THEN RD_NEXT_SYMBOL_TAC `4`;
    SUBGOAL_THEN `j + 1 = huf_rank ws 4` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (10--15) THEN RD_NEXT_WEIGHT_TAC `4` 16 9]);;

(* ------------------------------------------------------------------------- *)
(* The loops for the weights w >= 5 (a variable): the loop over the chunks   *)
(* of 16 entries of the symbol j at 0x6a78 (RD_LGI), then the loop over the  *)
(* symbols at 0x6a50 (RD_LGO).                                               *)
(* ------------------------------------------------------------------------- *)

(*** The loops for the weights w >= 5, 2^(w - 1) entries for each symbol,  ***)
(*** in chunks of 16 entries stored 256 bits at a time                     ***)

let rd_pattern =
  `(65536 * (nb + 256 * sym) + nb + 256 * sym) +
   4294967296 * (65536 * (nb + 256 * sym) + nb + 256 * sym)`;;

let rd_q0 =
  let pat = subst [`(tl + 1) - w`,`nb:num`;
                   `huf_sorted ws (huf_bstart ws w + j)`,`sym:num`]
                  rd_pattern in
  let wp = mk_comb(`word:num->int64`,pat) in
  mk_eq(`read Q0 s`,list_mk_comb(`word_join:int64->int64->int128`,[wp; wp]));;

let rd_lg_regs =
 `5 <= w /\
  read X17 s = word_add wk (word(huf_bstart ws w + j)) /\
  read X30 s = word_add wk (word(huf_bstart ws w + huf_rank ws w)) /\
  read X22 s = word(2 EXP (w - 1) - 16) /\
  read X23 s = word(2 EXP (w - 1)) /\
  read X18 s = word(huf_ustart ws w + j * 2 EXP (w - 1))`;;

(*** At 0x6a50, for the symbol j ***)

let rd_lgoinv = mk_rd_inner 0x6a50 `w:num` rd_lg_regs;;

(*** At 0x6a78, for the symbol j, k chunks of its entries stored ***)

let rd_lgiinv = with_memsafe rd_rr rd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`k:num`,list_mk_conj
    [`m = 2 EXP (w - 1) - 16 * k /\ 16 * k < 2 EXP (w - 1) /\
      j < huf_rank ws w /\ 1 <= w /\ w <= tl /\
      read PC s = word(pc + 0x6a78) /\
      read X1 s =
      word_add dtable
       (word((4 + 2 * (huf_ustart ws w + j * 2 EXP (w - 1))) + 32 * k)) /\
      read X4 s =
      word_add dtable
       (word(4 + 2 * ((huf_ustart ws w + j * 2 EXP (w - 1)) +
                      2 EXP (w - 1))))`;
     rd_q0; rd_lg_regs; rd_fixed; rd_prefix;
     `read (memory :> bytes(word_add dtable
                    (word(4 + 2 * (huf_ustart ws w + j * 2 EXP (w - 1)))),
                            32 * k)) s =
      num_of_bytelist(huf_dblock (16 * k) ((tl + 1) - w)
                       (huf_sorted ws (huf_bstart ws w + j)))`;
     rd_tables; rd_common])));;

let rd_lgigoal = mk_rd_goal [`w:num`; `j:num`] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_lgiinv,[`m:num`; `s:armstate`]))))
  (mk_abs(`s:armstate`,
     mk_disj(mk_exists(`m':num`,
               mk_conj(`m' < huf_rank ws w - j`,
                       list_mk_comb(rd_lgoinv,[`m':num`; `s:armstate`]))),
             mk_comb(mk_rd_wpost `w:num`,`s:armstate`))));;


(*** 2^(w - 1) for w >= 5, as a multiple of 16 ***)

let RD_EXP_16 = prove
 (`!w. 5 <= w ==> 2 EXP (w - 1) = 16 * 2 EXP (w - 5)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w - 1 = 4 + (w - 5)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV]);;

(*** The facts for the symbol j of the weight w >= 5, with the             ***)
(*** abbreviations L = 2^(w - 1), uj = huf_ustart ws w + j * L for the     ***)
(*** start of its entries, dsz = 2^(mtl + 1) and tt = 2^tl                 ***)

let RD_LG_FACTS_TAC =
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `huf_bstart ws w + j`] HUF_SORTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(tl + 1) - w < 256 /\ huf_sorted ws (huf_bstart ws w + j) < 256`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `w + 1`] HUF_BSTART_LE) THEN
  REWRITE_TAC[HUF_BSTART_SUC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `tl:num`; `w:num`; `j:num`]
    HUF_DTABLE_BLOCK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_BLOCK_END) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o
    REWRITE_RULE[RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC]) THEN
  SUBGOAL_THEN `2 EXP tl <= 2 EXP (mtl + 1) /\ 2 EXP (mtl + 1) <= 8192`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    SUBST1_TAC(ARITH_RULE `8192 = 2 EXP 13`) THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`tl <= mtl + 1`; `mtl <= 12`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `w:num` RD_EXP_16) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `1 <= 2 EXP (w - 5)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `dsz = 2 EXP (mtl + 1)` THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  ABBREV_TAC `L = 2 EXP (w - 1)` THEN
  ABBREV_TAC `uj = huf_ustart ws w + j * L`;;

(*** The block of entries of the symbol j extended by the chunk k in the   ***)
(*** state s, from the value of Q0                                         ***)

let RD_CHUNK_TAC s =
  W(fun (asl,w) ->
    let q0 = mk_comb(`read Q0`,s) in
    let v = rhs(concl(snd(find (fun (_,th) ->
              is_eq(concl th) && lhs(concl th) = q0) asl))) in
    MP_TAC(ISPECL [`word_add dtable (word(4 + 2 * uj)):int64`; `k:num`;
                   `(tl + 1) - w`; `huf_sorted ws (huf_bstart ws w + j)`;
                   v; s] READ_MEMORY_HUF_DBLOCK_CHUNK) THEN
    ASM_SIMP_TAC[VAL_WORD_JOIN_HUF_DBLOCK8] THEN
    REWRITE_TAC[WORD_ADD_ASSOC_NUM;
                ARITH_RULE `a + 32 * k + 16 = (a + 32 * k) + 16`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC);;

(*** The remaining equations of pointers and arithmetic ***)

let RD_WORD_ARITH_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [AP_TERM_TAC THEN AP_TERM_TAC THEN
         (ARITH_TAC ORELSE SIMPLE_ARITH_TAC);
         AP_TERM_TAC THEN (ARITH_TAC ORELSE SIMPLE_ARITH_TAC);
         SIMPLE_ARITH_TAC];;

(*** 16 * (k + 1) <= L from 16 * k < L for L a multiple of 16 ***)

let RD_CHUNK_BOUND_TAC =
  SUBGOAL_THEN `16 * (k + 1) <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `16 * k < L`)) THEN
    FIRST_ASSUM(fun th -> if concl th = `16 * 2 EXP (w - 5) = L`
                          then REWRITE_TAC[SYM th] else NO_TAC) THEN
    REWRITE_TAC[LT_MULT_LCANCEL; LE_MULT_LCANCEL; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `16 <= L` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC];;

(*** The loop over the chunks of the symbol j, then the next symbol or     ***)
(*** the next weight                                                       ***)

let RD_LGI = prove
 (rd_lgigoal,
  RD_START_VAR_TAC `k:num` THEN RD_LG_FACTS_TAC THEN RD_CHUNK_BOUND_TAC THEN
  ZSTD_STEPS_TAC (1--2) THEN RD_CHUNK_TAC `s2:armstate` THEN
  ASM_CASES_TAC `16 * (k + 1) < L` THENL
   [ZSTD_STEPS_TAC (3--4) THEN RD_PTR_BRANCH_TAC THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `L - 16 * (k + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `k + 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
    ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN RD_WORD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `16 * (k + 1) = L` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (3--4) THEN RD_PTR_BRANCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_eq(concl th) &&
    can (term_match [] `read (memory :> bytes(a,32 * (k + 1))) s = x`)
        (concl th))) THEN
  ASM_REWRITE_TAC[ARITH_RULE `32 * (k + 1) = 2 * 16 * (k + 1)`] THEN
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_comb(lhs c) &&
       fst(strip_comb(lhs c)) = `SUB_LIST:num#num->byte list->byte list`
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM] (ISPECL
   [`word_add dtable (word 4):int64`; `huf_dtable ws tl tl`; `2 * uj`;
    `2 * L`; `s4:armstate`] READ_MEMORY_BYTELIST_EXTEND)) THEN
  ASM_REWRITE_TAC[LENGTH_HUF_DTABLE] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * uj + 2 * L = 2 * (uj + L)`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `j + 1 < huf_rank ws w` THENL
   [ZSTD_STEPS_TAC (5--8) THEN RD_PTR_BRANCH_TAC THEN
    PUFF_FINAL_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `huf_rank ws w - (j + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `j + 1`] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j + 1 = huf_rank ws w` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (5--8) THEN RD_PTR_BRANCH_TAC THEN
  ZSTD_STEPS_TAC (9--12) THEN
  SUBGOAL_THEN `huf_ustart ws w + huf_rank ws w * L = uj + L` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `j + 1 = huf_rank ws w`
                          then REWRITE_TAC[SYM th] else NO_TAC) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; ADD_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if lhs(concl th) = `read X9 s12`
    then ASSUME_TAC(REWRITE_RULE[ASSUME
           `huf_ustart ws w + huf_rank ws w * L = uj + L`] th)
    else NO_TAC) THEN
  ZSTD_SMALL_WORD_TAC THEN
  ASM_CASES_TAC `w + 1 <= tl` THENL
   [ZSTD_STEPS_TAC [13] THEN
    PUFF_FINAL_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(tl + 1) - (w + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `w + 1`] THEN
    REWRITE_TAC[HUF_USTART_SUC; HUF_BSTART_SUC; HUF_EXP_DIV2] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `~(w = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `tl:num = w` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(w + 1 <= tl)`; `w <= tl`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (13--22) THEN
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
  SUBGOAL_THEN `uj + L = tt` SUBST_ALL_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `w:num`] HUF_USTART_ALL) THEN
    ASM_REWRITE_TAC[HUF_USTART_SUC; HUF_EXP_DIV2] THEN
    SUBGOAL_THEN `~(w = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUB_LIST(0,2 * tt) (huf_dtable ws w w) = huf_dtable ws w w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC SUB_LIST_REFL THEN
    REWRITE_TAC[LENGTH_HUF_DTABLE] THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

(*** The loop over the symbols of the weight w >= 5 ***)

let rd_lgogoal = mk_rd_goal [`w:num`] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_lgoinv,[`m:num`; `s:armstate`]))))
  (mk_rd_wpost `w:num`);;

(*** The load of the symbol bstart + j in the state s0 ***)

let RD_SYMLOAD_TAC =
  MP_TAC(ISPECL [`word_add wk (word 980):int64`;
                 `rd_symlist ws (LENGTH ws) l0`; `huf_bstart ws w + j`;
                 `s0:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_RD_SYMLIST] THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`huf_bstart ws w + j < LENGTH(ws:num list)`;
      `LENGTH(ws:num list) <= 256`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RD_SYMLIST_FULL] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add wk (word 980)) (word n):int64 =
                         word_add wk (word(n + 980))`] THEN
  DISCH_TAC;;

(*** Setting the value of a register in a chosen form ***)

let RD_SET_REG_TAC tm tac =
  SUBGOAL_THEN tm (fun th ->
    let l = lhs(concl th) in
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
      (fun th' -> is_eq(concl th') && lhs(concl th') = l))) THEN
    ASSUME_TAC th) THENL [tac; ALL_TAC];;

(*** Undoing the abbreviations of RD_LG_FACTS_TAC ***)

let RD_UNABBREV_TAC =
  let unabbrev tm =
    FIRST_X_ASSUM(fun th ->
      if concl th = tm then SUBST_ALL_TAC(SYM th) else NO_TAC) in
  unabbrev `huf_ustart ws w + j * L = uj` THEN
  unabbrev `2 EXP (w - 1) = L` THEN
  unabbrev `2 EXP tl = tt` THEN unabbrev `2 EXP (mtl + 1) = dsz`;;

(*** The loop over the symbols, going on with RD_LGI for each ***)

let RD_LGO = prove
 (rd_lgogoal,
  RD_START_VAR_TAC `j:num` THEN RD_LG_FACTS_TAC THEN RD_SYMLOAD_TAC THEN
  ZSTD_STEPS_TAC (1--10) THEN
  SUBGOAL_THEN `16 <= L` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`16 * 2 EXP (w - 5) = L`; `1 <= 2 EXP (w - 5)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  RD_SET_REG_TAC
   `read X1 s10 = word_add dtable (word((4 + 2 * uj) + 32 * 0))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN RD_WORD_ARITH_TAC) THEN
  RD_SET_REG_TAC `read X4 s10 = word_add dtable (word(4 + 2 * (uj + L)))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN RD_WORD_ARITH_TAC) THEN
  RD_UNABBREV_TAC THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) RD_LGI [] THEN
  EXISTS_TAC `2 EXP (w - 1) - 16 * 0` THEN EXISTS_TAC `0` THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_0; huf_dblock; list_of_seq;
              num_of_bytelist] THEN
  REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The loop over the weights w at 0x6908 (RD_FILL), from 1 to tl, branching  *)
(* on 2^(w - 1) to the loops for the symbols of the weight w, the weights    *)
(* from 5 on with w a variable.                                              *)
(* ------------------------------------------------------------------------- *)

let rd_fillgoal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_finv,[`m:num`; `s:armstate`]))))
  rd_fpost;;

(*** The facts for the weight w in the state s0: the number of its         ***)
(*** symbols, from rankVal, and bounds on the starts of its symbols and    ***)
(*** of their entries                                                      ***)

let RD_FILL_FACTS_TAC =
  MP_TAC(ISPECL [`wk:int64`;
                 `list_of_seq (\j. word(huf_rank ws j):int32) (tl + 1)`;
                 `tl + 1`; `w:num`; `s0:armstate`]
    READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `w <= tl ==> w < tl + 1`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(word w:int64) = w` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `w + 1`] HUF_BSTART_LE) THEN
  REWRITE_TAC[HUF_BSTART_SUC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `w + 1`; `tl + 1`] HUF_USTART_MONO) THEN
  ASM_SIMP_TAC[HUF_USTART_ALL; ARITH_RULE `w <= tl ==> w + 1 <= tl + 1`] THEN
  REWRITE_TAC[HUF_USTART_SUC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP tl <= 4096` ASSUME_TAC THENL
   [SUBST1_TAC(ARITH_RULE `4096 = 2 EXP 12`) THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    UNDISCH_TAC `tl <= 12` THEN ARITH_TAC;
    ALL_TAC];;

(*** No symbols of the weight w (a numeral), the branch back to 0x6908     ***)
(*** being the step n: the next weight w + 1, or the return in k more      ***)
(*** steps for w = tl                                                      ***)

let RD_ZERO_TAC w n k =
  let w1 = rd_numeral_conv(mk_binop `(+):num->num->num` w `1`) in
  let norm = CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[MULT_CLAUSES]) in
  let usuc = norm(SPECL [`ws:num list`; w] HUF_USTART_SUC)
  and bsuc = norm(SPECL [`ws:num list`; w] HUF_BSTART_SUC) in
  ASM_CASES_TAC (mk_binop `(<=):num->num->bool` w1 `tl:num`) THENL
   [ZSTD_STEPS_TAC [n] THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC (subst [w1,`w:num`] `(tl + 1) - w`) THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC w1] THEN
    REWRITE_TAC[usuc; bsuc] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN NUM_REDUCE_TAC;
    SUBGOAL_THEN (mk_eq(`tl:num`,w)) SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (n--(n+k)) THEN
    PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN (subst [w,`w:num`] `huf_ustart ws w = 2 EXP w`)
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MP_TAC(CONV_RULE NUM_REDUCE_CONV
        (SPECL [`ws:num list`; w] HUF_USTART_ALL)) THEN
      ASM_REWRITE_TAC[usuc; MULT_CLAUSES; ADD_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN (subst [w,`w:num`]
      `SUB_LIST(0,2 * 2 EXP w) (huf_dtable ws w w) = huf_dtable ws w w`)
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC SUB_LIST_REFL THEN REWRITE_TAC[LENGTH_HUF_DTABLE; LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE];;

(*** Going on with the loop th over the symbols of the weight w from the   ***)
(*** first one                                                             ***)

let RD_ENTER_TAC th w =
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) th [] THEN
  EXISTS_TAC (subst [w,`w:num`] `huf_rank ws w - 0`) THEN EXISTS_TAC `0` THEN
  MEMSAFE_ELIM_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (subst [w,`w:num`] `~(huf_rank ws w = 0)`) THEN ARITH_TAC;;

let RD_WORD_ADD_1 = WORD_RULE
  `word_add (word a) (word_add x (word 1)):int64 = word_add x (word(a + 1))`;;

(*** The weight 2 ***)

let RD_FILL2_TAC =
  ZSTD_STEPS_TAC (1--12) THEN
  ASM_CASES_TAC `huf_rank ws 2 = 0` THENL
   [ZSTD_STEPS_TAC (13--18) THEN RD_ZERO_TAC `2` 19 8; ALL_TAC] THEN
  ZSTD_STEPS_TAC (13--22) THEN
  RD_SET_REG_TAC
   `read X1 s22 = word_add dtable (word(4 + 2 * huf_ustart ws 2))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN RD_WORD_ARITH_TAC) THEN
  RD_SET_REG_TAC
   `read X17 s22 = word_add wk (word(huf_bstart ws 2 + huf_rank ws 2))`
   (ASM_REWRITE_TAC[RD_WORD_ADD_1] THEN RD_WORD_ARITH_TAC) THEN
  RD_ENTER_TAC RD_L2 `2`;;

(*** The weight 1 ***)

let RD_FILL1_TAC =
  ZSTD_STEPS_TAC (1--10) THEN
  ASM_CASES_TAC `huf_rank ws 1 = 0` THENL
   [ZSTD_STEPS_TAC (11--16) THEN RD_ZERO_TAC `1` 17 8; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= huf_rank ws 1` ASSUME_TAC THENL
   [UNDISCH_TAC `~(huf_rank ws 1 = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (11--20) THEN
  RD_SET_REG_TAC
   `read X1 s20 = word_add dtable (word(4 + 2 * huf_ustart ws 1))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN RD_WORD_ARITH_TAC) THEN
  RD_SET_REG_TAC
   `read X17 s20 =
    word_add dtable (word(4 + 2 * (huf_ustart ws 1 + huf_rank ws 1)))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN RD_WORD_ARITH_TAC) THEN
  RD_ENTER_TAC RD_L1 `1`;;

(*** The weights 3 and 4 ***)

let RD_FILL3_TAC =
  ZSTD_STEPS_TAC (1--7) THEN
  ASM_CASES_TAC `huf_rank ws 3 = 0` THENL
   [ZSTD_STEPS_TAC (8--13) THEN RD_ZERO_TAC `3` 14 8; ALL_TAC] THEN
  ZSTD_STEPS_TAC (8--16) THEN RD_ENTER_TAC RD_L4 `3`;;

let RD_FILL4_TAC =
  ZSTD_STEPS_TAC (1--10) THEN
  ASM_CASES_TAC `huf_rank ws 4 = 0` THENL
   [ZSTD_STEPS_TAC (11--16) THEN RD_ZERO_TAC `4` 17 8; ALL_TAC] THEN
  ZSTD_STEPS_TAC (11--18) THEN RD_ENTER_TAC RD_L8 `4`;;

(*** The weights w >= 5 ***)

let RD_ISHR_EXP = prove
 (`!w. 1 <= w /\ w <= 12
       ==> word_zx(word_ishr (word(2 EXP w):int32) 1):int64 =
           word(2 EXP (w - 1))`,
  SUBGOAL_THEN
   `!w. w < 13 ==> 1 <= w
        ==> word_zx(word_ishr (word(2 EXP w):int32) 1):int64 =
            word(2 EXP (w - 1))`
   (fun th -> MESON_TAC[th; ARITH_RULE `w <= 12 <=> w < 13`]) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let RD_AND_EXP = prove
 (`!w. 5 <= w /\ w <= 12
       ==> word_and (word(2 EXP (w - 1) - 1)) (word 4294967280):int64 =
           word(2 EXP (w - 1) - 16)`,
  SUBGOAL_THEN
   `!w. w < 13 ==> 5 <= w
        ==> word_and (word(2 EXP (w - 1) - 1)) (word 4294967280):int64 =
            word(2 EXP (w - 1) - 16)`
   (fun th -> MESON_TAC[th; ARITH_RULE `w <= 12 <=> w < 13`]) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(*** No symbols of the weight w >= 5, the branch back to 0x6908 being the  ***)
(*** step 17                                                               ***)

let RD_ZERO_SYM_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       rator(lhs(concl th)) = `read X9`
    then ASSUME_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES] th)
    else NO_TAC) THEN
  ASM_CASES_TAC `w + 1 <= tl` THENL
   [ZSTD_STEPS_TAC [17] THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(tl + 1) - (w + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `w + 1`] THEN
    REWRITE_TAC[HUF_USTART_SUC; HUF_BSTART_SUC] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `tl:num = w` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(w + 1 <= tl)`; `w <= tl`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (17--25) THEN
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN
  SUBGOAL_THEN `huf_ustart ws w = 2 EXP w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MP_TAC(SPECL [`ws:num list`; `w:num`] HUF_USTART_ALL) THEN
    ASM_REWRITE_TAC[HUF_USTART_SUC; MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `SUB_LIST(0,2 * 2 EXP w) (huf_dtable ws w w) = huf_dtable ws w w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC SUB_LIST_REFL THEN REWRITE_TAC[LENGTH_HUF_DTABLE; LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;;

let RD_FILL_GE5_TAC =
  SUBGOAL_THEN `5 <= w /\ w <= 12` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(w = 1)`; `~(w = 2)`; `~(w = 3)`; `~(w = 4)`;
      `1 <= w`; `w <= tl`; `tl <= 12`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--3) THEN
  RD_SET_REG_TAC `read X5 s3 = word(2 EXP (w - 1))`
   (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RD_ISHR_EXP THEN SIMPLE_ARITH_TAC) THEN
  SUBGOAL_THEN `16 <= 2 EXP (w - 1) /\ 2 EXP (w - 1) <= 2048`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(ARITH_RULE `16 = 2 EXP 4`) THEN
    SUBST1_TAC(ARITH_RULE `2048 = 2 EXP 11`) THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`5 <= w`; `w <= 12`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `w:num` RD_AND_EXP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `L = 2 EXP (w - 1)` THEN
  ZSTD_STEPS_TAC (4--10) THEN
  ASM_CASES_TAC `huf_rank ws w = 0` THENL
   [ZSTD_STEPS_TAC (11--16) THEN RD_ZERO_SYM_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (11--21) THEN
  SUBGOAL_THEN `1 <= huf_rank ws w` ASSUME_TAC THENL
   [UNDISCH_TAC `~(huf_rank ws w = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  RD_SET_REG_TAC
   `read X30 s21 = word_add wk (word(huf_bstart ws w + huf_rank ws w))`
   (ASM_REWRITE_TAC[RD_WORD_ADD_1] THEN RD_WORD_ARITH_TAC) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `2 EXP (w - 1) = L`
                          then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  RD_ENTER_TAC RD_LGO `w:num`;;

let RD_FILL_CASE_TAC v tac =
  ASM_CASES_TAC (mk_eq(`w:num`,v)) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN tac;
    ALL_TAC];;

let RD_FILL = prove
 (rd_fillgoal,
  RD_START_VAR_TAC `w:num` THEN RD_FILL_FACTS_TAC THEN
  RD_FILL_CASE_TAC `1` RD_FILL1_TAC THEN
  RD_FILL_CASE_TAC `2` RD_FILL2_TAC THEN
  RD_FILL_CASE_TAC `3` RD_FILL3_TAC THEN
  RD_FILL_CASE_TAC `4` RD_FILL4_TAC THEN
  RD_FILL_GE5_TAC);;

(* ------------------------------------------------------------------------- *)
(* The counting sort of the symbols at 0x6850, four at a time (RD_SORT4),    *)
(* and at 0x68b4, one at a time (RD_SORTR), with rankStart the next position *)
(* for each weight; before it the loop at 0x6828 setting rankStart           *)
(* (RD_RANKSTART).                                                           *)
(* ------------------------------------------------------------------------- *)

(*** The counting sort of the symbols by their weights, the first k of     ***)
(*** them placed                                                           ***)

let rd_sortfacts =
 `ALL (\x. x <= tl) ws /\ LENGTH ws <= 256 /\ huf_total ws = 2 EXP tl /\
  1 <= tl /\ tl <= mtl + 1 /\ tl <= 12 /\
  LENGTH(l0:byte list) = 256 /\ k <= LENGTH ws /\
  read X7 s = word tl /\ read X9 s = word tl /\
  read X22 s = word_add wk (word 1236) /\ read X23 s = word(LENGTH ws) /\
  read (memory :> bytes(wk,4 * (tl + 1))) s =
  num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) (tl + 1)) /\
  read (memory :> bytes(word_add wk (word 52),4 * (tl + 1))) s =
  num_of_wordlist(list_of_seq
   (\v. word(huf_bstart ws v + CARD {t | t < k /\ EL t ws = v}):int32)
   (tl + 1)) /\
  read (memory :> bytes(word_add wk (word 980),256)) s =
  num_of_bytelist(rd_symlist ws k l0) /\
  read (memory :> bytes(word_add wk (word 1236),LENGTH ws)) s =
  num_of_bytelist(MAP (word:num->byte) ws) /\
  read (memory :> bytes8 (word_add dtable (word 2))) s = word tl`;;

(*** The loop at 0x68b4 placing one symbol at a time ***)

let rd_sortrinv = with_memsafe rd_rr rd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`k:num`,list_mk_conj
    [`m = LENGTH(ws:num list) - k /\ k < LENGTH ws /\
      read PC s = word(pc + 0x68b4) /\
      read X0 s = word k /\ read X3 s = word_add wk (word(1236 + k)) /\
      read X8 s = word(huf_rank ws 0)`;
     rd_sortfacts; rd_common])));;

let rd_sortrgoal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_sortrinv,[`m:num`; `s:armstate`]))))
  rd_fpost;;

(*** The facts for placing the symbol kt in the state s: its weight and    ***)
(*** its load (the address normalized by addrconv), the split of           ***)
(*** rankStart at its weight and that of the symbols at its position,      ***)
(*** abbreviated as the variable pv                                        ***)

let RD_PLACE_FACTS_TAC kt s addrconv pv =
  let inst t = subst [kt,`k:num`; s,`s:armstate`; pv,`p:num`] t in
  SUBGOAL_THEN (inst `k < LENGTH(ws:num list)`) ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add wk (word 1236):int64`; `MAP (word:num->byte) ws`;
                 kt; s] READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE addrconv) THEN
  SUBGOAL_THEN (inst `EL k ws <= tl`) ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `ALL (\x. x <= tl) ws`)) THEN
    DISCH_THEN(MP_TAC o SPEC kt o REWRITE_RULE[GSYM ALL_EL]) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; kt] HUF_POS_WEIGHTS) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; kt] HUF_POS_LT) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`word_add wk (word 52):int64`;
    inst `list_of_seq (\v. word(huf_bstart ws v +
                          CARD {t | t < k /\ EL t ws = v}):int32) (tl + 1)`;
    inst `EL k (ws:num list)`; s] READ_MEMORY_WORDLIST32_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read (memory :> bytes32 a) s = EL j l`)
        (concl th))) THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `w <= tl ==> w < tl + 1`] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM;
                            ARITH_RULE `52 + 4 * j = 4 * j + 52`] th)) THEN
  MP_TAC(ISPECL [`word_add wk (word 980):int64`; inst `rd_symlist ws k l0`;
    inst `huf_bstart ws (EL k ws) + CARD {t | t < k /\ EL t ws = EL k ws}`;
    `1`; s] READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_RD_SYMLIST] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC (inst
   `p = huf_bstart ws (EL k ws) + CARD {t | t < k /\ EL t ws = EL k ws}`);;

(*** After the stores of rankStart[w] = p + 1 and the symbol kt at p in    ***)
(*** the state s: both arrays for kt + 1                                   ***)

let RD_PLACED_TAC kt s pv =
  let inst t = subst [kt,`k:num`; s,`s:armstate`; pv,`p:num`] t in
  MP_TAC(ISPECL [`word_add wk (word 52):int64`;
    inst `list_of_seq (\v. word(huf_bstart ws v +
                          CARD {t | t < k /\ EL t ws = v}):int32) (tl + 1)`;
    inst `list_of_seq (\v. word(huf_bstart ws v +
                          CARD {t | t < k + 1 /\ EL t ws = v}):int32)
                (tl + 1)`;
    inst `EL k (ws:num list)`; s] READ_MEMORY_WORDLIST32_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `w <= tl ==> w < tl + 1`] THEN
    REWRITE_TAC[GEN `P:num->bool`
                 (SPECL [`P:num->bool`; kt] CARD_RESTRICT_LT_ADD1);
                WORD_ADD_ASSOC_NUM; ARITH_RULE `52 + 4 * j = 4 * j + 52`] THEN
    ASM_REWRITE_TAC[ADD_ASSOC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (inst `~(EL k (ws:num list) = i)`)
     (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN (inst `p < 256`) ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add wk (word 980):int64`; inst `rd_symlist ws k l0`;
    inst `rd_symlist ws (k + 1) l0`; pv;
    inst `word_add wk (word(p + 980)):int64`; inst `word k:byte`; s]
    READ_MEMORY_BYTELIST_UPDATE1) THEN
  ASM_REWRITE_TAC[LENGTH_RD_SYMLIST] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_RD_SYMLIST_STEP; ARITH_RULE `k < n ==> k < n`] THEN
    CONV_TAC WORD_RULE;
    DISCH_TAC];;

(*** The end of the sort at 0x68dc: the setup of the loop over the         ***)
(*** weights, from the step n, then RD_FILL                                ***)

let RD_DSZ_ABBREV_TAC =
  SUBGOAL_THEN `2 EXP (mtl + 1) <= 8192` ASSUME_TAC THENL
   [SUBST1_TAC(ARITH_RULE `8192 = 2 EXP 13`) THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
    UNDISCH_TAC `mtl <= 12` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `dsz = 2 EXP (mtl + 1)`;;

(*** A later piece th whose hypotheses and frame are in terms of dsz ***)

let RD_DSZ_RULE th =
  REWRITE_RULE[ASSUME `2 EXP (mtl + 1) = dsz`] (SPEC_ALL th);;

let RD_DSZ_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th -> if concl th = `2 EXP (mtl + 1) = dsz`
                          then SUBST_ALL_TAC(SYM th) else NO_TAC);;

let RD_SORTED_TAC n =
  ZSTD_STEPS_TAC (n--(n+10)) THEN RD_DSZ_UNABBREV_TAC THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[])
   RD_FILL [] THEN
  EXISTS_TAC `(tl + 1) - 1` THEN EXISTS_TAC `1` THEN
  MEMSAFE_ELIM_TAC THEN
  REWRITE_TAC[HUF_START_1; MULT_CLAUSES; SUB_LIST_CLAUSES;
              num_of_bytelist; READ_MEMORY_BYTES_0] THEN
  ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC;;

let RD_SORTR = prove
 (rd_sortrgoal,
  RD_START_VAR_TAC `k:num` THEN RD_DSZ_ABBREV_TAC THEN
  RD_PLACE_FACTS_TAC `k:num` `s0:armstate`
   (LAND_CONV(REWRITE_CONV[WORD_ADD_ASSOC_NUM])) `p:num` THEN
  ZSTD_STEPS_TAC (1--7) THEN
  RD_PLACED_TAC `k:num` `s7:armstate` `p:num` THEN
  ASM_CASES_TAC `k + 1 < LENGTH(ws:num list)` THENL
   [ZSTD_STEPS_TAC (8--10) THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `LENGTH(ws:num list) - (k + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `k + 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
    ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k + 1 = LENGTH(ws:num list)` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (8--10) THEN RD_SORTED_TAC 11);;

(*** The loop at 0x6850 placing four symbols at a time ***)

let rd_sort4inv = with_memsafe rd_rr rd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`q:num`,list_mk_conj
    [`m = LENGTH(ws:num list) - 4 * q /\ 4 * q + 3 < LENGTH ws /\
      read PC s = word(pc + 0x6850) /\
      read X5 s = word(4 * q) /\
      read X6 s = word_add wk (word(1236 + 4 * q)) /\
      read X8 s = word(LENGTH ws - 3)`;
     subst [`4 * q`,`k:num`] rd_sortfacts; rd_common])));;

let rd_sort4goal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_sort4inv,[`m:num`; `s:armstate`]))))
  rd_fpost;;

let RD_GROUP_END = prove
 (`!n q. 4 * q + 4 <= n /\ n <= 4 * q + 7 /\ n <= 256
         ==> word_zx(word_add (word_and (word(n - 4)) (word 4294967292))
                              (word 4):int32):int64 = word(4 * (q + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word 4294967292:int32 = word_not(word(2 EXP 2 - 1))`
  SUBST1_TAC THENL
   [CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV); ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `val(word(n - 4):int32) = n - 4` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `n <= 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(n - 4) DIV 2 EXP 2 = q` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `n - 4 - 4 * q` THEN
    MAP_EVERY UNDISCH_TAC [`4 * q + 4 <= n`; `n <= 4 * q + 7`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  MP_TAC(SPEC `2 EXP 2 * q + 4` RS_WORD_ZX32) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`4 * q + 4 <= n`; `n <= 256`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC]);;

(*** rankVal[0] as a 32-bit load from wk in the state s ***)

let RD_RANK0_TAC s =
  MP_TAC(ISPECL [`wk:int64`;
                 `list_of_seq (\j. word(huf_rank ws j):int32) (tl + 1)`;
                 `tl + 1`; `0`; s] READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; ARITH_RULE `0 < n + 1`] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `0 < n + 1`] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `1`] HUF_BSTART_LE) THEN
  REWRITE_TAC[HUF_START_1] THEN DISCH_TAC;;

(*** The placement of the symbol 4q + u (u a small number), from the       ***)
(*** state number n, the arrays being for 4q + u at the start              ***)

let RD_PLACE4_TAC u n =
  let kt = if u = 0 then `4 * q`
           else mk_binop `(+):num->num->num` `4 * q` (mk_small_numeral u) in
  let k1 = mk_binop `(+):num->num->num` `4 * q`
             (mk_small_numeral(u + 1)) in
  let pv = mk_var("p" ^ string_of_int u,`:num`) in
  let st i = mk_var("s" ^ string_of_int i,`:armstate`) in
  let conv = if u = 0 then LAND_CONV(REWRITE_CONV[WORD_ADD_ASSOC_NUM])
             else LAND_CONV(REWRITE_CONV[WORD_ADD_ASSOC_NUM; ADD_ASSOC]) in
  RD_PLACE_FACTS_TAC kt (st n) conv pv THEN
  ZSTD_STEPS_TAC ((n+1)--(n+11)) THEN
  RD_PLACED_TAC kt (st(n+11)) pv THEN
  (if u = 3 then
     RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(4 * q + 3) + 1 = 4 * (q + 1)`])
   else
     RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
       (mk_eq(mk_binop `(+):num->num->num` kt `1`,k1))]));;

let RD_SORT4 = prove
 (rd_sort4goal,
  RD_START_VAR_TAC `q:num` THEN RD_DSZ_ABBREV_TAC THEN
  ZSTD_STEPS_TAC [1] THEN
  RD_PLACE4_TAC 0 1 THEN RD_PLACE4_TAC 1 12 THEN
  RD_PLACE4_TAC 2 23 THEN RD_PLACE4_TAC 3 34 THEN
  ZSTD_STEPS_TAC (46--48) THEN
  ASM_CASES_TAC `4 * (q + 1) + 3 < LENGTH(ws:num list)` THENL
   [ZSTD_STEPS_TAC [49] THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `LENGTH(ws:num list) - 4 * (q + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `q + 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
    ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (49--52) THEN
  RD_SET_REG_TAC `read X0 s52 = word(4 * (q + 1))`
   (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RD_GROUP_END THEN
    REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC) THEN
  RD_RANK0_TAC `s52:armstate` THEN
  ASM_CASES_TAC `LENGTH(ws:num list) = 4 * (q + 1)` THENL
   [ZSTD_STEPS_TAC (53--55) THEN RD_SORTED_TAC 56; ALL_TAC] THEN
  ZSTD_STEPS_TAC (53--58) THEN
  RD_SET_REG_TAC `read X3 s58 = word_add wk (word(1236 + 4 * (q + 1)))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN RD_WORD_ARITH_TAC) THEN
  RD_DSZ_UNABBREV_TAC THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[])
   RD_SORTR [] THEN
  EXISTS_TAC `LENGTH(ws:num list) - 4 * (q + 1)` THEN
  EXISTS_TAC `4 * (q + 1)` THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC);;

(*** The loop at 0x6828 setting rankStart[v] = huf_bstart ws v for         ***)
(*** v <= tl, the first n of them set, for the measure (tl + 1) - n,       ***)
(*** then the sort                                                         ***)

let rd_rsfacts =
 `ALL (\x. x <= tl) ws /\ 2 <= LENGTH ws /\ LENGTH ws <= 256 /\
  huf_total ws = 2 EXP tl /\ 1 <= tl /\ tl <= mtl + 1 /\ tl <= 12 /\
  LENGTH(l0:byte list) = 256 /\
  read X7 s = word tl /\ read X9 s = word tl /\
  read X22 s = word_add wk (word 1236) /\ read X23 s = word(LENGTH ws) /\
  read X8 s = word_zx(word_sub (word(LENGTH ws)) (word 3):int32) /\
  read (memory :> bytes(wk,4 * (tl + 1))) s =
  num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) (tl + 1)) /\
  read (memory :> bytes(word_add wk (word 980),256)) s = num_of_bytelist l0 /\
  read (memory :> bytes(word_add wk (word 1236),LENGTH ws)) s =
  num_of_bytelist(MAP (word:num->byte) ws) /\
  read (memory :> bytes8 (word_add dtable (word 2))) s = word tl`;;

let rd_rsinv = with_memsafe rd_rr rd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`n:num`,list_mk_conj
    [`m = (tl + 1) - n /\ n <= tl /\
      read PC s = word(pc + 0x6828) /\
      read X0 s = word n /\ read X1 s = word(huf_bstart ws n) /\
      read X4 s = word_add wk (word 52) /\
      read (memory :> bytes(word_add wk (word 52),4 * n)) s =
      num_of_wordlist(list_of_seq (\v. word(huf_bstart ws v):int32) n)`;
     rd_rsfacts; rd_common])));;

let rd_rsgoal = mk_rd_goal [] rd_hyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_rsinv,[`m:num`; `s:armstate`]))))
  rd_fpost;;

let RD_WORD_SUB3 = prove
 (`!n. 3 <= n /\ n < 2 EXP 32
       ==> word_zx(word_sub (word n) (word 3):int32):int64 = word(n - 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word n) (word 3):int32 = word(n - 3)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
  MATCH_MP_TAC RS_WORD_ZX32 THEN UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC);;

let RD_BSTART_LIST_SNOC = prove
 (`!ws n. list_of_seq (\v. word(huf_bstart ws v):int32) (n + 1) =
          APPEND (list_of_seq (\v. word(huf_bstart ws v)) n)
                 [word(huf_bstart ws n)]`,
  REWRITE_TAC[GSYM ADD1; list_of_seq]);;

(*** The symbols placed so far and their counts, for none of them ***)

let RD_SORT_START_TAC =
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES;
              ADD_CLAUSES] THEN
  ASM_SIMP_TAC[RD_SYMLIST_0];;

let RD_RANKSTART = prove
 (rd_rsgoal,
  RD_START_VAR_TAC `n:num` THEN RD_DSZ_ABBREV_TAC THEN
  MP_TAC(ISPECL [`wk:int64`;
                 `list_of_seq (\j. word(huf_rank ws j):int32) (tl + 1)`;
                 `tl + 1`; `n:num`; `s0:armstate`]
    READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `n <= tl ==> n < tl + 1`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `n + 1`] HUF_BSTART_LE) THEN
  REWRITE_TAC[HUF_BSTART_SUC] THEN DISCH_TAC THEN
  ZSTD_STEPS_TAC (1--5) THEN
  MP_TAC(ISPECL [`word_add wk (word 52):int64`;
                 `list_of_seq (\v. word(huf_bstart ws v):int32) n`;
                 `word(huf_bstart ws n):int32`; `s5:armstate`]
    READ_MEMORY_WORDLIST32_APPEND1) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; WORD_ADD_ASSOC_NUM] THEN
  REWRITE_TAC[GSYM RD_BSTART_LIST_SNOC] THEN DISCH_TAC THEN
  ASM_CASES_TAC `n + 1 <= tl` THENL
   [ZSTD_STEPS_TAC [6] THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(tl + 1) - (n + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `n + 1`] THEN
    ASM_REWRITE_TAC[HUF_BSTART_SUC];
    ALL_TAC] THEN
  SUBGOAL_THEN `n:num = tl` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(n + 1 <= tl)`; `n <= tl`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `4 <= LENGTH(ws:num list)` THENL
   [RD_SET_REG_TAC `read X8 s5 = word(LENGTH(ws:num list) - 3)`
     (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RD_WORD_SUB3 THEN
      CONJ_TAC THEN SIMPLE_ARITH_TAC) THEN
    ZSTD_STEPS_TAC (6--10) THEN RD_DSZ_UNABBREV_TAC THEN
    ZSTD_CONTINUE_WITH_TAC
     (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
      ASM_REWRITE_TAC[])
     RD_SORT4 [] THEN
    EXISTS_TAC `LENGTH(ws:num list) - 4 * 0` THEN EXISTS_TAC `0` THEN
    MEMSAFE_ELIM_TAC THEN RD_SORT_START_TAC THEN
    ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(ws:num list) = 2 \/ LENGTH(ws:num list) = 3`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(4 <= LENGTH(ws:num list))`; `2 <= LENGTH(ws:num list)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (fun eq ->
    RULE_ASSUM_TAC(fun th' ->
      if is_eq(concl th') && lhs(concl th') = `read X8 s5`
      then CONV_RULE(RAND_CONV(REWRITE_CONV[eq] THENC
                               WORD_REDUCE_CONV)) th'
      else th') THEN ASSUME_TAC eq)) THEN
  RD_RANK0_TAC `s5:armstate` THEN
  ZSTD_STEPS_TAC (6--16) THEN RD_DSZ_UNABBREV_TAC THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[])
   RD_SORTR [] THEN
  EXISTS_TAC `LENGTH(ws:num list) - 0` THEN EXISTS_TAC `0` THEN
  MEMSAFE_ELIM_TAC THEN RD_SORT_START_TAC THEN
  ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The table log tl stored with the header (RD_HEADER), and before it the    *)
(* raising of the weights by k = MIN (mtl + 1) 11 - ml when ml is less than  *)
(* that: the weights in place at 0x6798 (RD_RESCALE_W), then rankVal moved   *)
(* up by k at 0x67d0 and the words below zeroed with memset (RD_RESCALE_R).  *)
(* ------------------------------------------------------------------------- *)

(*** At 0x67fc with tableLog tl in X7: its store, the check against the    ***)
(*** maximum mtl + 1 (assumed to pass), the header, then RD_RANKSTART      ***)

let rd_hdfacts =
 `ALL (\x. x <= tl) ws /\ 2 <= LENGTH ws /\ LENGTH ws <= 256 /\
  huf_total ws = 2 EXP tl /\ 1 <= tl /\ tl <= mtl + 1 /\ tl <= 12 /\
  LENGTH(l0:byte list) = 256 /\
  read X7 s = word tl /\ read X24 s = word(mtl + 1) /\
  read X25 s = word_zx(dh:int32) /\
  read X22 s = word_add wk (word 1236) /\ read X23 s = word(LENGTH ws) /\
  read (memory :> bytes(wk,4 * (tl + 1))) s =
  num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) (tl + 1)) /\
  read (memory :> bytes(word_add wk (word 980),256)) s = num_of_bytelist l0 /\
  read (memory :> bytes(word_add wk (word 1236),LENGTH ws)) s =
  num_of_bytelist(MAP (word:num->byte) ws)`;;

let rd_hdpre = with_memsafe rd_rr rd_wr
 (mk_abs(`s:armstate`,list_mk_conj
   [`read PC s = word(pc + 0x67fc)`; rd_hdfacts; rd_common]));;

let rd_hdgoal = mk_rd_goal [`dh:int32`] rd_hyps rd_hdpre rd_fpost;;

let WORD_SUBWORD_INSERT_16_8 = prove
 (`!(x:int32) (y:int32).
        word_subword (word_insert x (16,8) y:int32) (16,8):byte =
        word_subword y (0,8)`,
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_0_8_WORD = prove
 (`!n. word_subword (word n:int32) (0,8):byte = word n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  REWRITE_TAC[EXP; DIV_1; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** The stack addresses in the MAYCHANGE assumption as offsets from the   ***)
(*** base of the stack region, for MONOTONE_MAYCHANGE_TAC                  ***)

let RD_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 112):int64 =
  word_add (word_sub stackpointer (word 432)) (word 320)`;;

let RD_FRAME_REBASE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE[RD_STACK_REBASE; WORD_ADD_ASSOC_NUM] th)
    else th);;

let RD_HEADER = prove
 (rd_hdgoal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD_DSZ_ABBREV_TAC THEN
  ZSTD_STEPS_TAC (1--11) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES8_2_OF_32 o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `read (memory :> bytes32 dtable) s11`))
  THEN REWRITE_TAC[WORD_SUBWORD_INSERT_16_8; WORD_SUBWORD_0_8_WORD] THEN
  DISCH_TAC THEN RD_FRAME_REBASE_TAC THEN
  ZSTD_CONTINUE_TAC (RD_DSZ_RULE RD_RANKSTART) [] THEN
  EXISTS_TAC `(tl + 1) - 0` THEN EXISTS_TAC `0` THEN
  MEMSAFE_ELIM_TAC THEN
  REWRITE_TAC[HUF_BSTART_0; MULT_CLAUSES; READ_MEMORY_BYTES_0; list_of_seq;
              num_of_wordlist] THEN
  ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC);;

(*** The rescaling of the weights by k = target - ml when tableLog ml is   ***)
(*** below the target: the loop at 0x67d0 moving rankVal[r] to             ***)
(*** rankVal[r + k] for r from ml down to 1, the memset of rankVal[1..k]   ***)
(*** then RD_HEADER for the weights rescaled and the table log ml + k      ***)

let rd_rpost = subst [`huf_rescale k ws0`,`ws:num list`; `ml + k`,`tl:num`]
  rd_fpost;;

let rd_rescfacts =
 `ALL (\x. x <= ml) ws0 /\ 2 <= LENGTH ws0 /\ LENGTH ws0 <= 256 /\
  huf_total ws0 = 2 EXP ml /\ 1 <= ml /\ 1 <= k /\ ml + k <= 11 /\
  ml + k <= mtl + 1 /\ LENGTH(l0:byte list) = 256 /\
  read X3 s = word k /\ read X26 s = word(ml + k) /\
  read X24 s = word(mtl + 1) /\ read X25 s = word_zx(dh:int32) /\
  read X22 s = word_add wk (word 1236) /\ read X23 s = word(LENGTH ws0) /\
  read (memory :> bytes(word_add wk (word 980),256)) s = num_of_bytelist l0 /\
  read (memory :> bytes64 (word_add (word pc) (word 0x20010))) s = fset /\
  read (memory :> bytes(ea,el)) s = ev`;;

let rd_rhyps = mk_conj(rd_hyps,
 `memset_memsafe_contract fset ea el ev /\
  nonoverlapping (wk:int64,1492) (ea:int64,el)`);;

let rd_rminv = with_memsafe rd_rr rd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`r:num`,list_mk_conj
    [`m = r /\ 1 <= r /\ r <= ml /\
      read PC s = word(pc + 0x67d0) /\
      read X7 s = word r /\ read X0 s = word_add wk (word(4 * (r + k))) /\
      read (memory :> bytes(wk,52)) s =
      num_of_wordlist(list_of_seq
       (\j. word(if r + k < j /\ j <= ml + k then huf_rank ws0 (j - k)
                 else huf_rank ws0 j):int32) 13) /\
      read (memory :> bytes(word_add wk (word 1236),LENGTH ws0)) s =
      num_of_bytelist(MAP (word:num->byte) (huf_rescale k ws0))`;
     rd_rescfacts; rd_common])));;

let rd_rmgoal = mk_rd_goal
  [`ws0:num list`; `ml:num`; `k:num`; `dh:int32`; `fset:int64`; `ev:num`]
  rd_rhyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_rminv,[`m:num`; `s:armstate`]))))
  rd_rpost;;

let RD_WORD_DEC4 = prove
 (`!(x:int64) n.
        1 <= n
        ==> word_add (word_add x (word(4 * n))) (word 18446744073709551612) =
            word_add x (word(4 * (n - 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 * n = 4 * (n - 1) + 4` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[WORD_ADD_0]);;

(*** The facts for the move of rankVal[r] in the state s0 ***)

let RD_MOVE_FACTS_TAC =
  SUBGOAL_THEN `word_zx(word_zx(word r:int64):int32):int64 = word r`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ZX_ZX] THEN
    SUBGOAL_THEN `word_zx(word r:int64):int32 = word r` SUBST1_TAC THENL
     [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
      REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC RS_WORD_ZX32 THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word r:int64) = r` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`wk:int64`;
    `list_of_seq (\j. word(if r + k < j /\ j <= ml + k
                           then huf_rank ws0 (j - k)
                           else huf_rank ws0 j):int32) 13`;
    `13`; `r:num`; `s0:armstate`] READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `r <= ml /\ ml + k <= 11 ==> r < 13`;
               ARITH_RULE `~(r + k < r:num)`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`wk:int64`;
    `list_of_seq (\j. word(if r + k < j /\ j <= ml + k
                           then huf_rank ws0 (j - k)
                           else huf_rank ws0 j):int32) 13`;
    `r + k`; `s0:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

(*** The list after the move of rankVal[r] in the state s ***)

let RD_MOVED_TAC s =
  MP_TAC(ISPECL [`wk:int64`;
    `list_of_seq (\j. word(if r + k < j /\ j <= ml + k
                           then huf_rank ws0 (j - k)
                           else huf_rank ws0 j):int32) 13`;
    `list_of_seq (\j. word(if (r - 1) + k < j /\ j <= ml + k
                           then huf_rank ws0 (j - k)
                           else huf_rank ws0 j):int32) 13`;
    `r + k`; s] READ_MEMORY_WORDLIST32_UPDATE) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ;
                 ARITH_RULE `r <= ml /\ ml + k <= 11 ==> r + k < 13`] THEN
    REWRITE_TAC[ADD_SUB] THEN
    SUBGOAL_THEN `(r - 1) + k < r + k /\ r + k <= ml + k`
     (fun th -> REWRITE_TAC[th]) THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r - 1) + k < i <=> r + k < i`
     (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC [`~(i = r + k)`; `1 <= r`] THEN ARITH_TAC;
    DISCH_TAC];;

(*** The numbers of the rescaled weights, from those moved and zeroed ***)

let RD_RESCALED_RANKS = prove
 (`!ws0 ml k j.
        ALL (\x. x <= ml) ws0 /\ j < 13 /\ ~(1 <= j /\ j < 1 + k)
        ==> word(huf_rank (huf_rescale k ws0) j):int32 =
            word(if k < j /\ j <= ml + k then huf_rank ws0 (j - k)
                 else huf_rank ws0 j)`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[HUF_RANK_RESCALE] THEN
  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ARITH_RULE `~(k < 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `k < j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `a = 0 /\ b = 0 ==> a = b`) THEN
  CONJ_TAC THEN MATCH_MP_TAC HUF_RANK_ABOVE THEN EXISTS_TAC `ml:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RD_RESCALED_ZERO = prove
 (`!ws0 k. k <= 12
           ==> SUB_LIST(1,k)
                (list_of_seq (\j. word(huf_rank (huf_rescale k ws0) j):int32)
                             13) =
               list_of_seq (\j. word 0) k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH_LIST_OF_SEQ] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < k /\ 1 + k <= 13` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
               ARITH_RULE `i < k /\ k <= 12 ==> 1 + i < 13`] THEN
  REWRITE_TAC[HUF_RANK_RESCALE] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < k ==> ~(1 + i = 0) /\ 1 + i <= k`]);;

(*** After the memset in the state s15: the rescaled rankVal, then the     ***)
(*** step to 0x67fc and RD_HEADER for the rescaled weights                 ***)

let RD_RESCALE_EXIT_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `word_zx(word 0:int64):byte`)) (concl th))) THEN
  REWRITE_TAC[WORD_ZX_0] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP READ_MEMORY_BYTES_ZERO) THEN
  MP_TAC(ISPECL [`wk:int64`;
    `list_of_seq (\j. word(if k < j /\ j <= ml + k
                           then huf_rank ws0 (j - k)
                           else huf_rank ws0 j):int32) 13`;
    `list_of_seq (\j. word(huf_rank (huf_rescale k ws0) j):int32) 13`;
    `1`; `k:num`; `s15:armstate`] READ_MEMORY_WORDLIST32_RANGE_UPDATE) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[RD_RESCALED_ZERO; ASSUME `ml + k <= 11`;
           ARITH_RULE `ml + k <= 11 ==> k <= 12`;
           NUM_OF_WORDLIST_LIST_OF_SEQ_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; RD_RESCALED_RANKS];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`wk:int64`;
    `\j. word(huf_rank (huf_rescale k ws0) j):int32`;
    `(ml + k) + 1`; `13`; `s15:armstate`] READ_MEMORY_WORDLIST32_TRUNC) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  ZSTD_STEPS_TAC [16] THEN RD_FRAME_REBASE_TAC THEN
  ZSTD_CONTINUE_TAC (RD_DSZ_RULE RD_HEADER)
   [`huf_rescale k ws0`,`ws:num list`; `ml + k`,`tl:num`] THEN
  MEMSAFE_ELIM_TAC THEN
  ASM_SIMP_TAC[LENGTH_HUF_RESCALE; HUF_TOTAL_RESCALE; HUF_RESCALE_BOUND] THEN
  REWRITE_TAC[EXP_ADD; MULT_SYM] THEN RD_WORD_ARITH_TAC;;

let RD_RESCALE_R = prove
 (rd_rmgoal,
  RD_START_VAR_TAC `r:num` THEN RD_DSZ_ABBREV_TAC THEN RD_MOVE_FACTS_TAC THEN
  ZSTD_STEPS_TAC (1--3) THEN RD_MOVED_TAC `s3:armstate` THEN
  ASM_CASES_TAC `r = 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `r = 1`));
    SUBGOAL_THEN `2 <= r` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(r = 1)`; `1 <= r`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ZSTD_STEPS_TAC [4] THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `r - 1` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `r - 1`] THEN
    ASM_SIMP_TAC[RD_WORD_DEC4; ARITH_RULE `1 <= r ==> 1 <= r + k`] THEN
    ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_SUB_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  ZSTD_STEPS_TAC (4--9) THEN
  RD_SET_REG_TAC `read X0 s9 = word_add wk (word 4)`
   (ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC) THEN
  MP_TAC(ISPECL [`wk:int64`;
    `list_of_seq (\j. word(if k < j /\ j <= ml + k
                           then huf_rank ws0 (j - k)
                           else huf_rank ws0 j):int32) 13`;
    `1`; `k:num`; `s9:armstate`] READ_MEMORY_WORDLIST32_RANGE_SPLIT) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `val(word(4 * k):int64) = 4 * k` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (10--11) THEN PUFF_ADRP_TAC THEN ZSTD_STEPS_TAC (12--14) THEN
  ZSTD_MEMSET_TAC [ASSUME `val(word(4 * k):int64) = 4 * k`]
    `word_add wk (word 4):int64` `word 0:int64` `word(4 * k):int64`
    `word(pc + 26616):int64` 15 THEN
  RD_RESCALE_EXIT_TAC);;

(*** The loop at 0x6798 raising the nonzero weights by k in place, the     ***)
(*** first i of them done, for the measure LENGTH ws0 - i, then            ***)
(*** RD_RESCALE_R                                                          ***)

let rd_rwlist =
 `list_of_seq (\j. word(if j < i /\ ~(EL j ws0 = 0) then EL j ws0 + k
                        else EL j ws0):byte) (LENGTH(ws0:num list))`;;

let rd_rwinv = with_memsafe rd_rr rd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`i:num`,list_mk_conj
    [`m = LENGTH(ws0:num list) - i /\ i < LENGTH ws0 /\
      read PC s = word(pc + 0x6798) /\
      read X1 s = word_add wk (word i) /\
      read X4 s = word_add wk (word(LENGTH ws0)) /\
      read X7 s = word ml /\
      read (memory :> bytes(wk,52)) s =
      num_of_wordlist(list_of_seq (\j. word(huf_rank ws0 j):int32) 13)`;
     mk_eq(`read (memory :> bytes(word_add wk (word 1236),
                                  LENGTH(ws0:num list))) s`,
           mk_comb(`num_of_bytelist`,rd_rwlist));
     rd_rescfacts; rd_common])));;

let rd_rwgoal = mk_rd_goal
  [`ws0:num list`; `ml:num`; `k:num`; `dh:int32`; `fset:int64`; `ev:num`]
  rd_rhyps
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(rd_rwinv,[`m:num`; `s:armstate`]))))
  rd_rpost;;

(*** The facts for the weight i in the state s0: its load and the split    ***)
(*** of the weights around it                                              ***)

let RD_RW_FACTS_TAC =
  MP_TAC(ISPECL [`word_add wk (word 1236):int64`; rd_rwlist; `i:num`;
                 `s0:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; LT_REFL] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM; ARITH_RULE `1236 + i = i + 1236`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`word_add wk (word 1236):int64`; rd_rwlist; `i:num`; `1`;
                 `s0:armstate`] READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `EL i (ws0:num list) <= 12` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[GSYM ALL_EL] o
      check (fun th -> concl th = `ALL (\x. x <= ml) ws0`)) THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The weights for i + 1 after the store b of the weight i in state s ***)

let RD_RW_STORED_TAC s =
  MP_TAC(ISPECL [`word_add wk (word 1236):int64`; rd_rwlist;
    subst [`i + 1`,`i:num`] rd_rwlist; `i:num`;
    `word_add wk (word(i + 1236)):int64`;
    `word(if ~(EL i ws0 = 0) then EL i ws0 + k else EL i ws0):byte`; s]
    READ_MEMORY_BYTELIST_UPDATE1) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `i < i + 1`] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    SUBGOAL_THEN `j < i + 1 <=> j < i` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `~(j:num = i)` THEN ARITH_TAC;
    DISCH_TAC];;

let RD_RWLIST_FULL = prove
 (`!ws0 k. list_of_seq (\j. word(if j < LENGTH ws0 /\ ~(EL j ws0 = 0)
                                 then EL j ws0 + k else EL j ws0):byte)
                       (LENGTH ws0) =
           MAP word (huf_rescale k ws0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP; LENGTH_HUF_RESCALE] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP; LENGTH_HUF_RESCALE; EL_HUF_RESCALE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let RD_RESCALE_W = prove
 (rd_rwgoal,
  RD_START_VAR_TAC `i:num` THEN RD_DSZ_ABBREV_TAC THEN RD_RW_FACTS_TAC THEN
  ZSTD_STEPS_TAC (1--7) THEN RD_RW_STORED_TAC `s7:armstate` THEN
  ASM_CASES_TAC `i + 1 < LENGTH(ws0:num list)` THENL
   [ZSTD_STEPS_TAC (8--9) THEN RD_PTR_BRANCH_TAC THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `LENGTH(ws0:num list) - (i + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `i + 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
    ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i + 1 = LENGTH(ws0:num list)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (8--9) THEN RD_PTR_BRANCH_TAC THEN
  ZSTD_STEPS_TAC (10--14) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `i + 1 = LENGTH(ws0:num list)`
                          then RULE_ASSUM_TAC(REWRITE_RULE[th; RD_RWLIST_FULL])
                          else NO_TAC) THEN
  ZSTD_CONTINUE_TAC (RD_DSZ_RULE RD_RESCALE_R) [] THEN
  EXISTS_TAC `ml:num` THEN EXISTS_TAC `ml:num` THEN
  MEMSAFE_ELIM_TAC THEN
  REWRITE_TAC[ARITH_RULE `((a:num) < j /\ j <= a) <=> F`] THEN
  ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole function: the size of the workspace checked, HUF_readStats_wksp *)
(* called (RD_CALL_TAC) and its error returned, the target table log MIN     *)
(* (mtl + 1) 11 compared with ml, and the later pieces for the weights       *)
(* raised or as they are, or the error for a table log above mtl + 1.        *)
(* ------------------------------------------------------------------------- *)

(*** HUF_readDTableX1_wksp from 0x66d4 ***)

let rd_goal =
 `!pc returnaddress stackpointer dtable src (l:byte list) wk wsz flags mtl
    fcpy fset ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 272) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     mtl <= 12 /\ LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 1492 <= 2 EXP 64 /\
     nonoverlapping (dtable:int64,4 + 2 * 2 EXP (mtl + 1)) (wk,1492) /\
     nonoverlapping (dtable,4 + 2 * 2 EXP (mtl + 1))
                    (word_sub stackpointer (word 432),432) /\
     nonoverlapping (dtable,4 + 2 * 2 EXP (mtl + 1)) (word pc,0x20018) /\
     nonoverlapping (dtable,4 + 2 * 2 EXP (mtl + 1)) (src,LENGTH l) /\
     nonoverlapping (wk,1492) (word_sub stackpointer (word 432),432) /\
     nonoverlapping (wk,1492) (word pc,0x20018) /\
     nonoverlapping (wk,1492) (src,LENGTH l) /\
     nonoverlapping (wk,1492) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 432),432)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 432),432) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 432),432) (ea,el)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x66d4) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dtable; src; word(LENGTH l); wk; wsz; flags] s /\
               read (memory :> bytes8 dtable) s = word mtl /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (1492 <= val(wsz:int64)
                ==> !ws ml h.
                      huf_weights T l ws ml h /\ ml <= mtl + 1
                      ==> read X0 s = word h /\
                          read (memory :> bytes8(word_add dtable (word 2))) s =
                          word(MAX ml (MIN (mtl + 1) 11)) /\
                          read (memory :> bytes(word_add dtable (word 4),
                                        2 * 2 EXP (MAX ml (MIN (mtl + 1) 11))))
                               s =
                          num_of_bytelist
                           (huf_dtable ws ml (MAX ml (MIN (mtl + 1) 11)))) /\
               (~(1492 <= val wsz /\
                  ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl + 1)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; dtable,4 + 2 * 2 EXP (mtl + 1); wk,1492;
                       word_sub stackpointer (word 432),432;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [dtable,4 + 2 * 2 EXP (mtl + 1); wk,1492;
                       word_sub stackpointer (word 432),432]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dtable,4 + 2 * 2 EXP (mtl + 1));
             memory :> bytes(wk,1492);
             memory :> bytes(word_sub stackpointer (word 432),432)])`;;

let RD_TOP_START_TAC =
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
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0";;

let RD_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 112)) (word 112):int64 =
  stackpointer`;;

let RD_TOP_FRAME_TAC = RD_FRAME_REBASE_TAC THEN MONOTONE_MAYCHANGE_TAC;;

(*** An error return, the reason proving that it is not a success ***)

let RD_TOP_FAIL_TAC =
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[RD_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN TRY RD_TOP_FRAME_TAC;;

(*** The call of HUF_readStats_wksp at 0x672c ***)

let RD_CALL_TAC =
  SUBGOAL_THEN `~(word_sub stackpointer (word 112):int64 = word 160)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 112) = word 160 <=>
                           x = word 272`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add wk (word 1236):int64) + 255 < 2 EXP 64`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`wk:int64`; `1236`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `val(wk:int64) + 1492 <= 2 EXP 64` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `val(wk:int64) + 1492 <= 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--23) THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x6730):int64`;
    `word_sub stackpointer (word 112):int64`;
    `word_add wk (word 1236):int64`; `wk:int64`;
    `word_add (word_sub stackpointer (word 112)) (word 108):int64`;
    `word_add (word_sub stackpointer (word 112)) (word 104):int64`;
    `src:int64`; `l:byte list`; `word_add wk (word 104):int64`;
    `fcpy:int64`; `fset:int64`; `ea:int64`; `el:num`; `ev:num`]
   HUF_READSTATS_WKSP_CORRECT))) THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM] THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC
                      NUM_LE_CONV)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC ZSTD_EXEC "s24" THEN EVENTS_UNABBREV_TAC;;

let WORD_AND_255_SUBWORD = prove
 (`!x:int32. word_and x (word 255) = word_zx(word_subword x (0,8):byte)`,
  CONV_TAC WORD_BLAST);;

let RD_HEADER_MTL = prove
 (`!dh:int32 mtl.
        word mtl:byte = word_subword dh (0,8) /\ mtl <= 12
        ==> word_and dh (word 255) = word mtl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_AND_255_SUBWORD] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

(*** The postcondition of the whole function from that of a later piece,   ***)
(*** for the weights ws, ml with header of h bytes, the table being        ***)
(*** that for tl = MAX ml (MIN (mtl + 1) 11), given by the equations ths   ***)

let RD_TOP_POST_TAC ths =
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`ws':num list`; `ml':num`; `h':num`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                  `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC ths THEN
    ASM_REWRITE_TAC[ARITH_RULE `MAX (a:num) a = a`];
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC];;

(*** Going on with a piece th, instantiated by insts, weakening its frame ***)

let RD_GOON_TAC wtac th insts =
  let frame_rule =
    REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
                 MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
                 SOME_FLAGS] in
  W(fun (asl,w) ->
    let th1 = INST insts (SPEC_ALL th) in
    let hyp = lhand(concl th1) in
    let hth = TAC_PROOF((asl,hyp),
                REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
    let eth0 = frame_rule(MP th1 hth) in
    let _,bod = dest_abs(rand(rator w)) in
    let c = rator(rator(rand bod)) in
    let c0 = rand(concl eth0) in
    let sth = TAC_PROOF(([],list_mk_icomb "subsumed" [c0;c]),
                        SUBSUMED_MAYCHANGE_TAC) in
    let eth = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ sth eth0) in
    MATCH_MP_TAC(MATCH_MP EVENTUALLY_ENSURES eth) THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [BETA_TAC;
      CONJ_TAC THENL [RD_TOP_FRAME_TAC; BETA_TAC THEN wtac]]);;

let RD_MAP_LIST_OF_SEQ = prove
 (`!(f:A->B) l. list_of_seq (\j. f(EL j l)) (LENGTH l) = MAP f l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP]);;

(*** The symbols region as the bytes l0 there in the state s ***)

let RD_SYMBYTES_TAC s =
  MP_TAC(ISPECL [`word_add wk (word 980):int64`;
    mk_comb(`read (memory :> bytelist(word_add wk (word 980),256))`,s);
    `256`; s] READ_BYTELIST_EQ_BYTES) THEN
  REWRITE_TAC[] THEN STRIP_TAC;;

(*** Going on with RD_HEADER for the weights ws as they are, tl = ml,      ***)
(*** from the state s at 0x67fc                                            ***)

let RD_TOP_HEADER_TAC s =
  MP_TAC(ISPECL [`wk:int64`; `\j. word(huf_rank ws j):int32`;
                 `ml + 1`; `13`; s] READ_MEMORY_WORDLIST32_TRUNC) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  RD_SYMBYTES_TAC s THEN
  RD_GOON_TAC
   (RD_TOP_POST_TAC [ASSUME `MAX ml tg = ml`])
   (RD_DSZ_RULE RD_HEADER)
   [`ml:num`,`tl:num`;
    mk_comb(`read (memory :> bytelist(word_add wk (word 980),256))`,s),
    `l0:byte list`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST [ARITH_TAC; RD_WORD_ARITH_TAC];;

(*** No weights: the error code of HUF_readStats_wksp returned ***)

let RD_NOWEIGHTS_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s24 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s24 = x0r`] THEN
  ZSTD_STEPS_TAC (25--26) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  ZSTD_STEPS_TAC (27--33) THEN RD_TOP_FAIL_TAC;;

(*** The table log ml too large for the table: the error at 0x6b6c ***)

let RD_TOP_TABLELOG_ERROR_TAC =
  ZSTD_STEPS_TAC (37--51) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[RD_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [RD_TOP_FRAME_TAC;
    MAP_EVERY X_GEN_TAC [`ws':num list`; `ml':num`; `h':num`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                  `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`ml':num <= mtl + 1`; `ml':num = ml`;
                           `~(ml <= mtl + 1)`] THEN ARITH_TAC];;

(*** From the state s36 with the target table log in X26: the rescale,     ***)
(*** the header for the table log ml as it is, or the error                ***)

let RD_TARGET_TAC =
  ZSTD_STEPS_TAC (25--36) THEN
  RD_SET_REG_TAC `read X26 s36 = word(MIN (mtl + 1) 11)`
   (ASM_REWRITE_TAC[MIN]) THEN
  SUBGOAL_THEN `1 <= MIN (mtl + 1) 11 /\ MIN (mtl + 1) 11 <= 11 /\
                MIN (mtl + 1) 11 <= mtl + 1`
  STRIP_ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `tg = MIN (mtl + 1) 11` THEN
  ASM_CASES_TAC `ml < tg` THENL
   [SUBGOAL_THEN `MAX ml tg = ml + (tg - ml)` ASSUME_TAC THENL
     [UNDISCH_TAC `ml < tg` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tg - ml`]
      HUF_DTABLE_RESCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ZSTD_STEPS_TAC (37--44) THEN
    RD_SET_REG_TAC `read X1 s44 = word_add wk (word 0)`
     (ASM_REWRITE_TAC[WORD_ADD_0]) THEN
    RD_SYMBYTES_TAC `s44:armstate` THEN
    RD_GOON_TAC
     (RD_TOP_POST_TAC [ASSUME `MAX ml tg = ml + (tg - ml)`])
     (RD_DSZ_RULE RD_RESCALE_W)
     [`ws:num list`,`ws0:num list`; `tg - ml`,`k:num`;
      `read (memory :> bytelist(word_add wk (word 980),256)) s44`,
      `l0:byte list`] THEN
    EXISTS_TAC `LENGTH(ws:num list) - 0` THEN EXISTS_TAC `0` THEN
    MEMSAFE_ELIM_TAC THEN
    REWRITE_TAC[CONJUNCT1 LT; RD_MAP_LIST_OF_SEQ; GSYM WORD_ADD] THEN
    ASM_REWRITE_TAC[] THEN RD_WORD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MAX ml tg = ml` ASSUME_TAC THENL
   [UNDISCH_TAC `~(ml < tg)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `ml:num = tg` THENL
   [ZSTD_STEPS_TAC (37--40) THEN
    RD_SET_REG_TAC `read X7 s40 = word ml` (ASM_REWRITE_TAC[]) THEN
    SUBGOAL_THEN `ml <= mtl + 1` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`ml:num = tg`; `tg <= mtl + 1`] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `ml:num = tg`)) THEN
    RD_TOP_HEADER_TAC `s40:armstate`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ml <= mtl + 1` THENL
   [FIRST
     [MAP_EVERY UNDISCH_TAC
       [`MIN (mtl + 1) 11 = tg`; `~(ml < tg)`; `~(ml:num = tg)`;
        `ml <= mtl + 1`; `mtl + 1 <= 11`] THEN ARITH_TAC;
      ZSTD_STEPS_TAC (37--38) THEN RD_TOP_HEADER_TAC `s38:armstate`];
    FIRST
     [MAP_EVERY UNDISCH_TAC
       [`~(ml <= mtl + 1)`; `ml <= 12`; `~(mtl + 1 <= 11)`] THEN
      ARITH_TAC;
      RD_TOP_TABLELOG_ERROR_TAC]];;

(*** The weights ws, ml with header of h bytes from HUF_readStats_wksp ***)

let RD_WEIGHTS_TAC =
  FIRST_X_ASSUM(X_CHOOSE_THEN `ws:num list` (X_CHOOSE_THEN `ml:num`
     (X_CHOOSE_TAC `h:num`)) o check (is_exists o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ws:num list`; `ml:num`; `h:num`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `huf_weights`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUF_WEIGHTS_FACTS) THEN
  X_CHOOSE_TAC `dh:int32`
   (MESON[] `?d:int32. read (memory :> bytes32 dtable) s24 = d`) THEN
  SUBGOAL_THEN `word_and (dh:int32) (word 255) = word mtl` ASSUME_TAC THENL
   [MATCH_MP_TAC RD_HEADER_MTL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES8_0_OF_32 o
      check (fun th ->
        concl th = `read (memory :> bytes32 dtable) s24 = dh`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  ASM_CASES_TAC `mtl + 1 <= 11` THEN RD_TARGET_TAC;;

let HUF_READDTABLEX1_WKSP_CORRECT = prove
 (rd_goal,
  RD_TOP_START_TAC THEN RD_DSZ_ABBREV_TAC THEN
  ASM_CASES_TAC `1492 <= val(wsz:int64)` THENL
   [ALL_TAC; ZSTD_STEPS_TAC (1--14) THEN RD_TOP_FAIL_TAC] THEN
  RD_CALL_TAC THEN
  ASM_CASES_TAC `?ws ml h. huf_weights T (l:byte list) ws ml h` THENL
   [RD_WEIGHTS_TAC; RD_NOWEIGHTS_TAC]);;

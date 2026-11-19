(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decoding table for the double-symbol decoding of Huffman-coded        *)
(* streams: zstd's HUF_readDTableX2_wksp, compiled by gcc 12 at -O2 for      *)
(* AArch64.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_read_stats_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_readDTableX2_wksp at 0x6b90 reads the description of a Huffman tree   *)
(* at src with HUF_readStats_wksp, called at 0x6c24, and fills the           *)
(* double-symbol decoding table at dtable + 4, 4 bytes an entry, with a      *)
(* workspace wk of at least 2124 bytes: rankVal at wk, rows of 13 words      *)
(* indexed by the length of a code, rankStats (the counts of the weights     *)
(* from HUF_readStats_wksp) at wk + 624, rankStart at wk + 680 (after a word *)
(* at wk + 676), the sorted symbols at wk + 736, the weights at wk + 992 and *)
(* the workspace of HUF_readStats_wksp at wk + 1248. The table log tl is     *)
(* mtl, the byte 0 of the header at dtable, except that it is 11 when mtl is *)
(* 12 and the Max_Number_of_Bits ml of the description is not                *)
(* (huf_tablelog2); a description with ml above mtl is an error. The setup   *)
(* finds the largest weight mw with symbols (the loop at 0x6c60), rankStart, *)
(* the start of each weight among the sorted symbols, weight 0 last          *)
(* (0x6c9c), sorts the symbols by weight (0x6ce8) and fills rankVal: row 0   *)
(* with the start of each weight among the entries of the table (0x6d24) and *)
(* the rows c from ml + 1 - mw with those shifted right by c (0x6d5c). The   *)
(* loop at 0x6e44 over the weights w fills the table. When the code of w, of *)
(* nb1 = ml + 1 - w bits, leaves fewer bits r = tl - nb1 than the shortest   *)
(* code, HUF_fillDTableX2ForWeight (0x1c50) fills 2^r entries of one symbol  *)
(* for each symbol of w (level 1). Otherwise, for each symbol of w (the loop *)
(* at 0x6ee0), the entries whose second symbol does not fit get the entry of *)
(* one symbol first (the prefill), and then for each weight w2 whose code    *)
(* fits in the r bits, from the smallest, minW, to mw (the loop at 0x6f60),  *)
(* HUF_fillDTableX2ForWeight fills the entries whose second symbol has the   *)
(* weight w2, 2^(r - nb2) of them for each such symbol, nb2 = ml + 1 - w2    *)
(* (level 2). The table is huf_dtable2 ws ml tl, which is shown block by     *)
(* block (HUF_DTABLE2_LEVEL1, HUF_DTABLE2_PREFILL and HUF_DTABLE2_LEVEL2).   *)
(* The pieces are ensures theorems between points of the code with the frame *)
(* of the whole function, chained by ENSURES_TRANS_SIMPLE, with the loops    *)
(* over the weights, the symbols of a weight and the weights of the second   *)
(* symbol by ENSURES_LOOP_EXIT; the inner loops (the prefill, the rows of    *)
(* rankVal, its row 0, the sort, rankStart and the search for mw) are lemmas *)
(* with frames of their own, used as big steps. Each piece has the conjunct  *)
(* of memory safety for the trace e at the entry of the function.            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The double-symbol decoding table: entry x for the weights ws with codes   *)
(* of at most ml bits and the table log tl.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The double-symbol decoding table of zstd for the weights ws with ***)
(*** codes of at most ml bits and a table log tl >= ml: entry x is the  ***)
(*** symbol s1 of the top ml bits of x, the symbol s2 of the bits after ***)
(*** the code of s1 if its code fits in the tl bits (or 0), the number  ***)
(*** of bits of the codes used and the number of symbols, 1 or 2        ***)

let huf_dentry2 = new_definition
 `huf_dentry2 ws ml tl x =
    let s1 = huf_symbol ws (x DIV 2 EXP (tl - ml)) in
    let nb1 = (ml + 1) - EL s1 ws in
    let r = tl - nb1 in
    let s2 = huf_symbol ws ((x MOD 2 EXP r * 2 EXP ml) DIV 2 EXP r) in
    let nb2 = (ml + 1) - EL s2 ws in
    if nb2 <= r then [s1; s2; nb1 + nb2; 2] else [s1; 0; nb1; 1]`;;

let huf_dtable2 = new_definition
 `huf_dtable2 ws ml tl =
    list_of_seq (\i. word(EL (i MOD 4) (huf_dentry2 ws ml tl (i DIV 4))):byte)
                (4 * 2 EXP tl)`;;

let LENGTH_HUF_DTABLE2 = prove
 (`!ws ml tl. LENGTH(huf_dtable2 ws ml tl) = 4 * 2 EXP tl`,
  REWRITE_TAC[huf_dtable2; LENGTH_LIST_OF_SEQ]);;

let HUF_DTABLE2_EL = prove
 (`!ws ml tl x k.
        x < 2 EXP tl /\ k < 4
        ==> EL (4 * x + k) (huf_dtable2 ws ml tl) =
            word(EL k (huf_dentry2 ws ml tl x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_dtable2] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL
    [lhand(rand(lhand w)); `4 * x + k`; `4 * 2 EXP tl`] EL_LIST_OF_SEQ)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  BETA_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(4 * x + k) MOD 4 = k /\ (4 * x + k) DIV 4 = x`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT];
    ONCE_REWRITE_TAC[ADD_SYM] THEN SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* The entries of the symbols of one weight as HUF_fillDTableX2ForWeight     *)
(* stores them (fw_block, 2^(tlg - nb) copies of the entry of each symbol),  *)
(* and their bytes in memory from its stores.                                *)
(* ------------------------------------------------------------------------- *)

(*** The entries of the fill function for the symbols of one weight ***)

(*** The entries, and the bytes of L copies of the entry of each symbol ***)

let fw_entry = new_definition
 `fw_entry lv nb b (s:byte) =
    lv * 2 EXP 24 + nb * 2 EXP 16 +
    (if lv = 1 then val s else b + 256 * val s)`;;

let fw_block = new_definition
 `fw_block L lv nb b (syms:byte list) =
    list_of_seq
     (\i. word((fw_entry lv nb b (EL (i DIV (4 * L)) syms) DIV
                2 EXP (8 * (i MOD 4))) MOD 2 EXP 8):byte)
     (4 * L * LENGTH syms)`;;

let fw_rep = new_definition
 `fw_rep k e = e * nsum {i | i < k} (\i. 2 EXP (32 * i))`;;

let LENGTH_FW_BLOCK = prove
 (`!L lv nb b syms. LENGTH(fw_block L lv nb b syms) = 4 * L * LENGTH syms`,
  REWRITE_TAC[fw_block; LENGTH_LIST_OF_SEQ]);;

let FW_ENTRY_BOUND = prove
 (`!lv nb b s. lv < 256 /\ nb < 256 /\ b < 256
               ==> fw_entry lv nb b s < 2 EXP 32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fw_entry] THEN
  MP_TAC(ISPEC `s:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let FW_BLOCK_APPEND = prove
 (`!L lv nb b l1 l2.
        fw_block L lv nb b (APPEND l1 l2) =
        APPEND (fw_block L lv nb b l1) (fw_block L lv nb b l2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_APPEND; LENGTH_FW_BLOCK] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ABBREV_TAC `n1 = LENGTH(l1:byte list)` THEN
  ABBREV_TAC `n2 = LENGTH(l2:byte list)` THEN
  ASM_CASES_TAC `L = 0` THENL
   [UNDISCH_TAC `i < 4 * L * n1 + 4 * L * n2` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];
    ALL_TAC] THEN
  REWRITE_TAC[EL_APPEND; LENGTH_FW_BLOCK] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[fw_block] THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `i < 4 * L * (n1 + n2) /\ i DIV (4 * L) < n1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_ARITH_TAC;
        ASM_SIMP_TAC[RDIV_LT_EQ; MULT_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC];
      ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_APPEND]];
    ALL_TAC] THEN
  SUBGOAL_THEN `i < 4 * L * (n1 + n2) /\ i - 4 * L * n1 < 4 * L * n2`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `?j. i = (4 * L) * n1 + j`
   (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)
  THENL [EXISTS_TAC `i - 4 * L * n1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `((4 * L) * n1 + j) - 4 * L * n1 = j`] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MULT_EQ_0; ARITH_EQ; EL_APPEND;
               ARITH_RULE `~(n1 + x < n1)`; ADD_SUB2] THEN
  REWRITE_TAC[ARITH_RULE `(4 * L) * n1 + j = 4 * (L * n1) + j`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let FW_REP_SUC = prove
 (`!n e. fw_rep (SUC n) e = fw_rep n e + 2 EXP (32 * n) * e`,
  REWRITE_TAC[fw_rep; NSUM_CLAUSES_NUMSEG_LT] THEN CONV_TAC NUM_RING);;

let FW_REP_ADD = prove
 (`!j k e. fw_rep (j + k) e = fw_rep j e + 2 EXP (32 * j) * fw_rep k e`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; fw_rep; NSUM_CLAUSES_NUMSEG_LT; MULT_CLAUSES];
    ASM_REWRITE_TAC[ADD_CLAUSES; FW_REP_SUC] THEN
    REWRITE_TAC[ARITH_RULE `32 * (j + k) = 32 * j + 32 * k`; EXP_ADD] THEN
    CONV_TAC NUM_RING]);;

let FW_REP_CLAUSES = prove
 (`(!e. fw_rep 0 e = 0) /\ (!e. fw_rep 1 e = e) /\
   (!e. fw_rep 2 e = e + 4294967296 * e)`,
  REWRITE_TAC[fw_rep; ARITH_RULE `2 = SUC 1 /\ 1 = SUC 0`;
              NSUM_CLAUSES_NUMSEG_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let NUM_OF_FW_BLOCK1 = prove
 (`!L lv nb b s.
        fw_entry lv nb b s < 2 EXP 32
        ==> num_of_bytelist(fw_block L lv nb b [s]) =
            fw_rep L (fw_entry lv nb b s)`,
  REPEAT GEN_TAC THEN ABBREV_TAC `e = fw_entry lv nb b s` THEN DISCH_TAC THEN
  REWRITE_TAC[fw_block; LENGTH; MULT_CLAUSES; ARITH_RULE `SUC 0 = 1`] THEN
  SUBGOAL_THEN
   `!i. i < 4 * L ==> EL (i DIV (4 * L)) [s:byte] = s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i DIV (4 * L) = 0` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(4 * L = 0)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[DIV_EQ_0]];
      REWRITE_TAC[EL; HD]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `list_of_seq (\i. word((fw_entry lv nb b (EL (i DIV (4 * L)) [s]) DIV
                           2 EXP (8 * i MOD 4)) MOD 2 EXP 8):byte) (4 * L) =
    list_of_seq (\i. word((e DIV 2 EXP (8 * i MOD 4)) MOD 2 EXP 8)) (4 * L)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    ALL_TAC] THEN
  SPEC_TAC(`L:num`,`L:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; num_of_bytelist; FW_REP_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 * SUC L = 4 * L + 4`; LIST_OF_SEQ_ADD_APPEND] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[ADD1; FW_REP_ADD; FW_REP_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * 4 * L = 32 * L`] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL; DIV_1] THEN
  UNDISCH_TAC `e < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(SPECL [`e:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`e DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`e DIV 256 DIV 256`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `e DIV 16777216 < 256` MP_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(*** The bytes of the entries in memory, from the stores ***)

let READ_MEMORY_FW_REP_COMBINE = prove
 (`!a:int64 m n e s:armstate.
        read (memory :> bytes(a,4 * m)) s = fw_rep m e /\
        read (memory :> bytes(word_add a (word(4 * m)),4 * n)) s = fw_rep n e
        ==> read (memory :> bytes(a,4 * (m + n))) s = fw_rep (m + n) e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; READ_BYTES_COMBINE; FW_REP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * 4 * m = 32 * m`]);;

let READ_MEMORY_FW_REP_STORE32 = prove
 (`!a:int64 e s:armstate.
        read (memory :> bytes32 a) s = word e /\ e < 2 EXP 32
        ==> read (memory :> bytes(a,4)) s = fw_rep 1 e`,
  REPEAT GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_MEMORY_BYTES32] THEN
  REWRITE_TAC[FW_REP_CLAUSES; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let READ_MEMORY_FW_REP_STORE64 = prove
 (`!a:int64 v:int64 e s:armstate.
        read (memory :> bytes64 a) s = v /\ val v = fw_rep 2 e
        ==> read (memory :> bytes(a,8)) s = fw_rep 2 e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_MEMORY_BYTES64]);;

let FW_ENTRY_ALT = prove
 (`!lv nb b s.
     (if ~(lv = 1) then b + 256 * val s else val s) + 16777216 * lv +
     65536 * nb = fw_entry lv nb b s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fw_entry] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let READ_MEMORY_FW_EXTEND = prove
 (`!dst:int64 L lv nb b syms i s:armstate.
        i < LENGTH syms /\ fw_entry lv nb b (EL i syms) < 2 EXP 32 /\
        read (memory :> bytes(dst,4 * L * i)) s =
        num_of_bytelist(fw_block L lv nb b (SUB_LIST(0,i) syms)) /\
        read (memory :> bytes(word_add dst (word(4 * L * i)),4 * L)) s =
        fw_rep L (fw_entry lv nb b (EL i syms))
        ==> read (memory :> bytes(dst,4 * L * (i + 1))) s =
            num_of_bytelist(fw_block L lv nb b (SUB_LIST(0,i + 1) syms))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_SNOC; FW_BLOCK_APPEND; NUM_OF_BYTELIST_APPEND;
               NUM_OF_FW_BLOCK1] THEN
  REWRITE_TAC[ARITH_RULE `4 * L * (i + 1) = 4 * L * i + 4 * L`;
              READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[LENGTH_FW_BLOCK; LENGTH_SUB_LIST] THEN
  SUBGOAL_THEN `MIN i (LENGTH(syms:byte list) - 0) = i` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]);;

let FW_ENTRY_ALT2 = prove
 (`!lv nb b s.
     (16777216 * lv + 65536 * nb) +
     (if ~(lv = 1) then b + 256 * val s else val s) = fw_entry lv nb b s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fw_entry] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let FW_VAL_REP2 = prove
 (`!e. e < 2 EXP 32 ==> val(word(e + 4294967296 * e):int64) = fw_rep 2 e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FW_REP_CLAUSES] THEN
  MATCH_MP_TAC VAL_WORD_LT64 THEN UNDISCH_TAC `e < 2 EXP 32` THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The table in blocks: the states of the weights in the table (huf_rv, as   *)
(* the code computes rankVal), the entries of the states of one symbol, and  *)
(* the blocks that HUF_fillDTableX2ForWeight fills at the levels 1 and 2 and *)
(* those of the prefill.                                                     *)
(* ------------------------------------------------------------------------- *)

(*** For a complete code, the states of the weights w and above start at  ***)
(*** a multiple of 2^(w - 1)                                              ***)

let HUF_USTART_ALIGNED = prove
 (`!ws ml w.
        huf_total ws = 2 EXP ml /\ ALL (\x. x <= ml) ws /\
        1 <= w /\ w <= ml + 1
        ==> ?q. huf_ustart ws w = 2 EXP (w - 1) * q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. ?q. huf_ustart ws (w + k) = huf_ustart ws w + 2 EXP (w - 1) * q`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES];
      FIRST_X_ASSUM(X_CHOOSE_TAC `q:num`) THEN
      EXISTS_TAC `q + huf_rank ws (w + k) * 2 EXP k` THEN
      ASM_REWRITE_TAC[ADD1; ADD_ASSOC; HUF_USTART_SUC; HUF_EXP_DIV2] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= w ==> ~(w + k = 0)`] THEN
      SUBGOAL_THEN `(w + k) - 1 = (w - 1) + k` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_RING]];
    DISCH_THEN(MP_TAC o SPEC `(ml + 1) - w`) THEN
    ASM_SIMP_TAC[ARITH_RULE `w <= ml + 1 ==> w + (ml + 1) - w = ml + 1`;
                 HUF_USTART_ALL] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
    EXISTS_TAC `2 EXP ((ml + 1) - w) - q` THEN
    SUBGOAL_THEN `2 EXP ml = 2 EXP (w - 1) * 2 EXP ((ml + 1) - w)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB] THEN ASM_ARITH_TAC]);;

(*** The start of the states of the weight w in a table of r bits ***)

let huf_rv = new_definition
 `huf_rv ws ml r w = (huf_ustart ws w * 2 EXP r) DIV 2 EXP ml`;;

(*** As the code computes it, rankVal[nb][w] = rankVal[0][w] >> nb ***)

let HUF_RV_CODE = prove
 (`!ws ml tl nb w.
        ml <= tl /\ nb <= tl
        ==> (huf_ustart ws w * 2 EXP (tl - ml)) DIV 2 EXP nb =
            huf_rv ws ml (tl - nb) w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_rv] THEN
  ABBREV_TAC `u = huf_ustart ws w` THEN
  ASM_CASES_TAC `nb <= tl - ml` THENL
   [SUBGOAL_THEN `2 EXP (tl - ml) = 2 EXP nb * 2 EXP ((tl - ml) - nb) /\
                  2 EXP (tl - nb) = 2 EXP ml * 2 EXP ((tl - ml) - nb)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `u * a * b = a * (u * b)`] THEN
    SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP nb = 2 EXP (tl - ml) * 2 EXP (nb - (tl - ml)) /\
                2 EXP ml = 2 EXP (tl - nb) * 2 EXP (nb - (tl - ml))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [MULT_SYM] THEN
  SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]);;

let HUF_RV_STEP = prove
 (`!ws ml r w.
        huf_total ws = 2 EXP ml /\ ALL (\x. x <= ml) ws /\
        1 <= w /\ w <= ml /\ (ml + 1) - w <= r
        ==> huf_rv ws ml r (w + 1) =
            huf_rv ws ml r w + huf_rank ws w * 2 EXP (r - ((ml + 1) - w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `w:num`] HUF_USTART_ALIGNED) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `q:num`)] THEN
  REWRITE_TAC[huf_rv; HUF_USTART_SUC; HUF_EXP_DIV2] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= w ==> ~(w = 0)`] THEN
  SUBGOAL_THEN `2 EXP (w - 1) * 2 EXP r =
                2 EXP ml * 2 EXP (r - ((ml + 1) - w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `(a * q + c * a) * b = (q + c) * (a * b) /\ (a * q) * b = q * (a * b)`] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `x * a * b = a * (x * b)`] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC);;

let HUF_RV_ALL = prove
 (`!ws ml r m.
        huf_total ws = 2 EXP ml /\ ALL (\x. x <= m) ws
        ==> huf_rv ws ml r (m + 1) = 2 EXP r`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[huf_rv; HUF_USTART_ALL] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

let HUF_RV_MONO = prove
 (`!ws ml r v w. v <= w ==> huf_rv ws ml r v <= huf_rv ws ml r w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_rv] THEN MATCH_MP_TAC DIV_MONO THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_SIMP_TAC[HUF_USTART_MONO]);;

(*** The entries of the table for the states of the symbol j of the      ***)
(*** weight w, 2^r of them for r = tl - nb1: the symbol, and the second    ***)
(*** from the bits after its code if that fits                            ***)

let HUF_DENTRY2_IN_BLOCK = prove
 (`!ws ml tl w j z.
        huf_complete ws ml /\ ml <= tl /\ 1 <= w /\ j < huf_rank ws w /\
        z < 2 EXP (tl - ((ml + 1) - w))
        ==> huf_dentry2 ws ml tl
             (huf_ustart ws w * 2 EXP (tl - ml) +
              j * 2 EXP (tl - ((ml + 1) - w)) + z) =
            let s1 = huf_sorted ws (huf_bstart ws w + j) in
            let nb1 = (ml + 1) - w in
            let r = tl - nb1 in
            let s2 = huf_symbol ws ((z * 2 EXP ml) DIV 2 EXP r) in
            let nb2 = (ml + 1) - EL s2 ws in
            if nb2 <= r then [s1; s2; nb1 + nb2; 2] else [s1; 0; nb1; 1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HUF_COMPLETE_ALL_LE) THEN
  SUBGOAL_THEN `w <= ml` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `w:num`] HUF_RANK_ABOVE) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `w:num`] HUF_USTART_ALIGNED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[huf_complete]; ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_TAC `q:num`)] THEN
  REWRITE_TAC[huf_dentry2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `r = tl - ((ml + 1) - w)` THEN
  SUBGOAL_THEN `2 EXP r = 2 EXP (w - 1) * 2 EXP (tl - ml)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = huf_ustart ws w * 2 EXP (tl - ml) + j * 2 EXP r + z` THEN
  SUBGOAL_THEN
   `x DIV 2 EXP (tl - ml) =
    (huf_ustart ws w + j * 2 EXP (w - 1)) + z DIV 2 EXP (tl - ml)`
  ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[ASSUME `2 EXP r = 2 EXP (w - 1) * 2 EXP (tl - ml)`] THEN
    REWRITE_TAC[ARITH_RULE
     `u * t + j * (a * t) + z = (u + j * a) * t + z`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `z DIV 2 EXP (tl - ml) < 2 EXP (w - 1)` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x MOD 2 EXP r = z` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[ASSUME `huf_ustart ws w = 2 EXP (w - 1) * q`] THEN
    REWRITE_TAC[ARITH_RULE
     `(a * q) * t + j * r + z = (q * (a * t) + j * r) + z`] THEN
    REWRITE_TAC[GSYM(ASSUME `2 EXP r = 2 EXP (w - 1) * 2 EXP (tl - ml)`)] THEN
    REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `huf_symbol ws (x DIV 2 EXP (tl - ml)) =
                huf_sorted ws (huf_bstart ws w + j)` SUBST1_TAC THENL
   [MATCH_MP_TAC HUF_SYMBOL_BLOCK THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME `EL (huf_sorted ws (huf_bstart ws w + j)) ws = w`] THEN
  REWRITE_TAC[ASSUME `tl - ((ml + 1) - w) = r`] THEN
  REWRITE_TAC[ASSUME `x MOD 2 EXP r = z`] THEN
  REWRITE_TAC[GSYM(ASSUME `2 EXP r = 2 EXP (w - 1) * 2 EXP (tl - ml)`)]);;

(*** The bytes of an entry ***)

let FW_BYTE_LEMMA = prove
 (`!e d q v r. e = (256 * q + v) * d + r /\ r < d /\ v < 256
               ==> (e DIV d) MOD 256 = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e DIV d = 256 * q + v` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let FW_ENTRY_BYTE = prove
 (`!lv nb b s k.
        lv < 256 /\ nb < 256 /\ b < 256 /\ k < 4
        ==> (fw_entry lv nb b s DIV 2 EXP (8 * k)) MOD 2 EXP 8 =
            EL k (if lv = 1 then [val s; 0; nb; 1] else [b; val s; nb; lv])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `k < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`] THEN
  STRIP_TAC THEN MP_TAC(ISPEC `s:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[fw_entry] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  FIRST(map (fun (q,r) ->
     MATCH_MP_TAC FW_BYTE_LEMMA THEN MAP_EVERY EXISTS_TAC [q; r] THEN
     ASM_ARITH_TAC)
   [`65536 * lv + 256 * nb`,`0`;
    `65536 * lv + 256 * nb + val(s:byte)`,`0`;
    `256 * lv + nb`,`val(s:byte)`; `256 * lv + nb`,`b:num`;
    `lv:num`,`val(s:byte)`; `lv:num`,`b + 256 * val(s:byte)`;
    `0`,`65536 * nb + val(s:byte)`;
    `0`,`65536 * nb + b + 256 * val(s:byte)`]));;

(*** A block of the table as the code fills it, from its entries ***)

let HUF_DTABLE2_FW_BLOCK = prove
 (`!ws ml tl P L lv nb b (syms:byte list).
        P + L * LENGTH syms <= 2 EXP tl /\ lv < 256 /\ nb < 256 /\ b < 256 /\
        (!i. i < L * LENGTH syms
             ==> huf_dentry2 ws ml tl (P + i) =
                 if lv = 1 then [val(EL (i DIV L) syms); 0; nb; 1]
                 else [b; val(EL (i DIV L) syms); nb; lv])
        ==> SUB_LIST(4 * P,4 * L * LENGTH syms) (huf_dtable2 ws ml tl) =
            fw_block L lv nb b syms`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH_HUF_DTABLE2;
              LENGTH_FW_BLOCK] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `m < 4 * L * LENGTH(syms:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_HUF_DTABLE2;
    ARITH_RULE `P + L * n <= t ==> 4 * P + 4 * L * n <= 4 * t`] THEN
  REWRITE_TAC[fw_block] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC(SPECL [`m:num`; `4`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `i = m DIV 4` THEN ABBREV_TAC `k = m MOD 4` THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < L * LENGTH(syms:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4 * P + m = 4 * (P + i) + k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[HUF_DTABLE2_EL; ARITH_RULE
   `P + L * n <= t /\ i < L * n ==> P + i < t`] THEN
  SUBGOAL_THEN `(i * 4 + k) DIV (4 * L) = i DIV L` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FW_ENTRY_BYTE THEN
  ASM_REWRITE_TAC[]);;

(*** The symbols of the weight w in order, as bytes ***)

let huf_wsyms = new_definition
 `huf_wsyms ws w =
    list_of_seq (\j. word(huf_sorted ws (huf_bstart ws w + j)):byte)
                (huf_rank ws w)`;;

let LENGTH_HUF_WSYMS = prove
 (`!ws w. LENGTH(huf_wsyms ws w) = huf_rank ws w`,
  REWRITE_TAC[huf_wsyms; LENGTH_LIST_OF_SEQ]);;

let VAL_EL_HUF_WSYMS = prove
 (`!ws w j. LENGTH ws <= 256 /\ j < huf_rank ws w
            ==> val(EL j (huf_wsyms ws w)) =
                huf_sorted ws (huf_bstart ws w + j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[huf_wsyms; EL_LIST_OF_SEQ] THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `huf_bstart ws w + j`] HUF_SORTED) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(*** The entries of the state of the symbol j of the weight w: past the    ***)
(*** start of the weight w2 among r bits, the second symbol of weight w2   ***)

let HUF_RV_EXACT = prove
 (`!ws ml r w2.
        huf_total ws = 2 EXP ml /\ ALL (\x. x <= ml) ws /\
        1 <= w2 /\ w2 <= ml + 1 /\ (ml + 1) - w2 <= r
        ==> huf_rv ws ml r w2 * 2 EXP ml = huf_ustart ws w2 * 2 EXP r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_rv] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `w2:num`] HUF_USTART_ALIGNED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
  SUBGOAL_THEN `2 EXP (w2 - 1) * 2 EXP r =
                2 EXP ml * 2 EXP ((w2 - 1 + r) - ml)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(a * q) * b = q * (a * b)`] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `q * a * b = a * (q * b)`] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC);;

(*** The starts of the weights in the table of tl bits ***)

let HUF_U_STEP = prove
 (`!ws ml tl w.
        1 <= w /\ ml <= tl /\ w <= ml
        ==> huf_ustart ws (w + 1) * 2 EXP (tl - ml) =
            huf_ustart ws w * 2 EXP (tl - ml) +
            huf_rank ws w * 2 EXP (tl - ((ml + 1) - w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HUF_USTART_SUC; HUF_EXP_DIV2] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= w ==> ~(w = 0)`] THEN
  SUBGOAL_THEN `2 EXP (tl - ((ml + 1) - w)) = 2 EXP (w - 1) * 2 EXP (tl - ml)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    CONV_TAC NUM_RING]);;

let HUF_U_ALL = prove
 (`!ws ml tl m.
        huf_total ws = 2 EXP ml /\ ALL (\x. x <= m) ws /\ ml <= tl
        ==> huf_ustart ws (m + 1) * 2 EXP (tl - ml) = 2 EXP tl`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HUF_USTART_ALL; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** The entries of the symbol j of the weight w whose second symbol has  ***)
(*** the weight w2 (with a code of nb2 bits that fits in the r left), as   ***)
(*** the code fills them for the symbols of w2 (HUF_fillDTableX2ForWeight  ***)
(*** at the level 2)                                                       ***)

let HUF_DTABLE2_LEVEL2 = prove
 (`!ws ml tl w j w2 nb1 r nb2.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\ tl <= 12 /\
        1 <= w /\ w <= ml /\ j < huf_rank ws w /\ 1 <= w2 /\ w2 <= ml /\
        nb1 = (ml + 1) - w /\ r = tl - nb1 /\ nb2 = (ml + 1) - w2 /\
        nb2 <= r
        ==> SUB_LIST(4 * (huf_ustart ws w * 2 EXP (tl - ml) + j * 2 EXP r +
                          huf_rv ws ml r w2),
                     4 * 2 EXP (r - nb2) * huf_rank ws w2)
                    (huf_dtable2 ws ml tl) =
            fw_block (2 EXP (r - nb2)) 2 (nb1 + nb2)
                     (huf_sorted ws (huf_bstart ws w + j)) (huf_wsyms ws w2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> is_eq(concl th) && lhs(concl th) = v)))
   [`nb1:num`; `r:num`; `nb2:num`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HUF_COMPLETE_ALL_LE) THEN
  SUBGOAL_THEN `huf_total ws = 2 EXP ml` ASSUME_TAC THENL
   [ASM_MESON_TAC[huf_complete]; ALL_TAC] THEN
  ABBREV_TAC `U = huf_ustart ws w * 2 EXP (tl - ml)` THEN
  ABBREV_TAC `L = 2 EXP (r - nb2)` THEN
  ABBREV_TAC `s1 = huf_sorted ws (huf_bstart ws w + j)` THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `huf_bstart ws w + j`] HUF_SORTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`;
    `U + j * 2 EXP r + huf_rv ws ml r w2`; `L:num`; `2`; `nb1 + nb2`;
    `s1:num`; `huf_wsyms ws w2`] HUF_DTABLE2_FW_BLOCK) THEN
  REWRITE_TAC[LENGTH_HUF_WSYMS] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `w2:num`]
      HUF_RV_STEP) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `w2 + 1`; `ml + 1`]
      HUF_RV_MONO) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `ml:num`]
      HUF_RV_ALL) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`] HUF_U_STEP) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `ml:num`] HUF_U_ALL) THEN
    MP_TAC(SPECL [`ws:num list`; `w + 1`; `ml + 1`] HUF_USTART_MONO) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    SUBGOAL_THEN `j * 2 EXP r + 2 EXP r <= huf_rank ws w * 2 EXP r /\
                  huf_ustart ws (w + 1) * 2 EXP (tl - ml) <=
                  huf_ustart ws (ml + 1) * 2 EXP (tl - ml)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `j * a + a = (j + 1) * a`; LE_MULT_RCANCEL] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `huf_rv ws ml r w2 + i < 2 EXP r` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `w2:num`]
      HUF_RV_STEP) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `w2 + 1`; `ml + 1`]
      HUF_RV_MONO) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `ml:num`]
      HUF_RV_ALL) THEN
    ASM_REWRITE_TAC[ARITH_RULE `w2 + 1 <= ml + 1 <=> w2 <= ml`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`; `j:num`;
                `huf_rv ws ml r w2 + i`] HUF_DENTRY2_IN_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ADD_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `w2:num`] HUF_RV_EXACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `L * 2 EXP ml = 2 EXP (w2 - 1) * 2 EXP r` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`i:num`; `L:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `j2 = i DIV L` THEN ABBREV_TAC `z2 = i MOD L` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `j2 < huf_rank ws w2` ASSUME_TAC THENL
   [SUBGOAL_THEN `j2 * L < huf_rank ws w2 * L` MP_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[LT_MULT_RCANCEL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((huf_rv ws ml r w2 + j2 * L + z2) * 2 EXP ml) DIV 2 EXP r =
    (huf_ustart ws w2 + j2 * 2 EXP (w2 - 1)) + (z2 * 2 EXP ml) DIV 2 EXP r`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(huf_rv ws ml r w2 + j2 * L + z2) * 2 EXP ml =
      (huf_ustart ws w2 + j2 * 2 EXP (w2 - 1)) * 2 EXP r + z2 * 2 EXP ml`
    SUBST1_TAC THENL
     [REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z2 * 2 EXP ml) DIV 2 EXP r < 2 EXP (w2 - 1)` ASSUME_TAC
  THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `2 EXP r * 2 EXP (w2 - 1) = L * 2 EXP ml` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `huf_symbol ws ((huf_ustart ws w2 + j2 * 2 EXP (w2 - 1)) +
                   (z2 * 2 EXP ml) DIV 2 EXP r) =
    huf_sorted ws (huf_bstart ws w2 + j2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HUF_SYMBOL_BLOCK THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(w2 = 0) <=> 1 <= w2`] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `w2:num`; `j2:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_EL_HUF_WSYMS]);;

(*** The symbol of a state, its weight and the start of that weight ***)

let HUF_SYMBOL_WEIGHT = prove
 (`!ws ml y.
        huf_complete ws ml /\ y < 2 EXP ml
        ==> huf_symbol ws y < LENGTH ws /\ 1 <= EL (huf_symbol ws y) ws /\
            EL (huf_symbol ws y) ws <= ml /\
            ~(huf_rank ws (EL (huf_symbol ws y) ws) = 0) /\
            huf_ustart ws (EL (huf_symbol ws y) ws) <= y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `y:num`] HUF_SYMBOL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[huf_complete]; ALL_TAC] THEN
  ABBREV_TAC `s = huf_symbol ws y` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `s:num`] HUF_PRESENT_WEIGHT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[huf_present; IN_ELIM_THM] o
    check (fun th -> concl th = `s IN huf_present ws`)) THEN
  ASM_REWRITE_TAC[HUF_RANK_MEM] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_MESON_TAC[MEM_EL];
    MP_TAC(SPECL [`ws:num list`; `s:num`] HUF_START_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(*** The entries of all the symbols of the weight w when no second symbol ***)
(*** fits in the r bits left (HUF_fillDTableX2ForWeight at the level 1)   ***)

let HUF_DTABLE2_LEVEL1 = prove
 (`!ws ml tl w nb1 r.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\ tl <= 12 /\
        1 <= w /\ w <= ml /\ nb1 = (ml + 1) - w /\ r = tl - nb1 /\
        (!v. 1 <= v /\ ~(huf_rank ws v = 0) ==> r < (ml + 1) - v)
        ==> SUB_LIST(4 * (huf_ustart ws w * 2 EXP (tl - ml)),
                     4 * 2 EXP r * huf_rank ws w)
                    (huf_dtable2 ws ml tl) =
            fw_block (2 EXP r) 1 nb1 0 (huf_wsyms ws w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> is_eq(concl th) && lhs(concl th) = v)))
   [`nb1:num`; `r:num`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HUF_COMPLETE_ALL_LE) THEN
  SUBGOAL_THEN `huf_total ws = 2 EXP ml` ASSUME_TAC THENL
   [ASM_MESON_TAC[huf_complete]; ALL_TAC] THEN
  ABBREV_TAC `U = huf_ustart ws w * 2 EXP (tl - ml)` THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `U:num`; `2 EXP r`;
    `1`; `nb1:num`; `0`; `huf_wsyms ws w`] HUF_DTABLE2_FW_BLOCK) THEN
  REWRITE_TAC[LENGTH_HUF_WSYMS] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`] HUF_U_STEP) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `ml:num`] HUF_U_ALL) THEN
    MP_TAC(SPECL [`ws:num list`; `w + 1`; `ml + 1`] HUF_USTART_MONO) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    SUBGOAL_THEN `huf_ustart ws (w + 1) * 2 EXP (tl - ml) <=
                  huf_ustart ws (ml + 1) * 2 EXP (tl - ml)`
    MP_TAC THENL [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`i:num`; `2 EXP r`] DIVISION) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ABBREV_TAC `j = i DIV 2 EXP r` THEN ABBREV_TAC `z = i MOD 2 EXP r` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `j < huf_rank ws w` ASSUME_TAC THENL
   [SUBGOAL_THEN `j * 2 EXP r < huf_rank ws w * 2 EXP r` MP_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`; `j:num`;
                `z:num`] HUF_DENTRY2_IN_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ADD_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `(z * 2 EXP ml) DIV 2 EXP r`]
    HUF_SYMBOL_WEIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL; LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ];
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL (huf_symbol ws ((z * 2 EXP ml) DIV 2 EXP r))
                                  ws` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN ASM_SIMP_TAC[VAL_EL_HUF_WSYMS]);;

(*** The first entries of the symbol j of the weight w, those whose second ***)
(*** symbol has a weight below w2, none of which fits in the r bits left   ***)

let HUF_DTABLE2_PREFILL = prove
 (`!ws ml tl w j w2 nb1 r.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\ tl <= 12 /\
        1 <= w /\ w <= ml /\ j < huf_rank ws w /\ w2 <= ml + 1 /\
        nb1 = (ml + 1) - w /\ r = tl - nb1 /\
        (!v. 1 <= v /\ v < w2 /\ ~(huf_rank ws v = 0) ==> r < (ml + 1) - v)
        ==> SUB_LIST(4 * (huf_ustart ws w * 2 EXP (tl - ml) + j * 2 EXP r),
                     4 * huf_rv ws ml r w2 * 1)
                    (huf_dtable2 ws ml tl) =
            fw_block (huf_rv ws ml r w2) 1 nb1 0
                     [word(huf_sorted ws (huf_bstart ws w + j))]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> is_eq(concl th) && lhs(concl th) = v)))
   [`nb1:num`; `r:num`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HUF_COMPLETE_ALL_LE) THEN
  SUBGOAL_THEN `huf_total ws = 2 EXP ml` ASSUME_TAC THENL
   [ASM_MESON_TAC[huf_complete]; ALL_TAC] THEN
  ABBREV_TAC `U = huf_ustart ws w * 2 EXP (tl - ml)` THEN
  ABBREV_TAC `L = huf_rv ws ml r w2` THEN
  ABBREV_TAC `s1 = huf_sorted ws (huf_bstart ws w + j)` THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `huf_bstart ws w + j`] HUF_SORTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `L <= 2 EXP r` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `w2:num`; `ml + 1`]
      HUF_RV_MONO) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `r:num`; `ml:num`]
      HUF_RV_ALL) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `U + j * 2 EXP r`;
    `L:num`; `1`; `nb1:num`; `0`; `[word s1:byte]`] HUF_DTABLE2_FW_BLOCK) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`] HUF_U_STEP) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `ml:num`] HUF_U_ALL) THEN
    MP_TAC(SPECL [`ws:num list`; `w + 1`; `ml + 1`] HUF_USTART_MONO) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    SUBGOAL_THEN `j * 2 EXP r + 2 EXP r <= huf_rank ws w * 2 EXP r /\
                  huf_ustart ws (w + 1) * 2 EXP (tl - ml) <=
                  huf_ustart ws (ml + 1) * 2 EXP (tl - ml)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `j * a + a = (j + 1) * a`; LE_MULT_RCANCEL] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`; `j:num`;
                `i:num`] HUF_DENTRY2_IN_BLOCK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ADD_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(i * 2 EXP ml) DIV 2 EXP r < huf_ustart ws w2` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC `i < L` THEN EXPAND_TAC "L" THEN REWRITE_TAC[huf_rv] THEN
    REWRITE_TAC[ARITH_RULE `i < n <=> i + 1 <= n`] THEN
    SIMP_TAC[LE_RDIV_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    MP_TAC(SPECL [`2`; `ml:num`] EXP_EQ_0) THEN REWRITE_TAC[ARITH_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `(i * 2 EXP ml) DIV 2 EXP r`]
    HUF_SYMBOL_WEIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`ws:num list`; `w2:num`; `ml + 1`] HUF_USTART_MONO) THEN
    ASM_SIMP_TAC[HUF_USTART_ALL] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `EL (huf_symbol ws ((i * 2 EXP ml) DIV 2 EXP r)) ws < w2`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`ws:num list`; `w2:num`;
      `EL (huf_symbol ws ((i * 2 EXP ml) DIV 2 EXP r)) ws`]
      HUF_USTART_MONO) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL (huf_symbol ws ((i * 2 EXP ml) DIV 2 EXP r))
                                  ws` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SUBGOAL_THEN `i DIV L = 0` SUBST1_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[EL; HD; CONS_11] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* HUF_fillDTableX2ForWeight at 0x1c50, with loops for 1, 2, 4 and 8 entries *)
(* a symbol and one for more, 8 entries at a time                            *)
(* (HUF_FILLDTABLEX2FORWEIGHT_CORRECT).                                      *)
(* ------------------------------------------------------------------------- *)

(*** HUF_fillDTableX2ForWeight at 0x1c50: for the symbols at begin..end, ***)
(*** each 2^(tlg - nb) copies of its 32-bit entry at dst, the entry of  ***)
(*** a symbol s being lv << 24 + nb << 16 + s for the level lv = 1 and  ***)
(*** lv << 24 + nb << 16 + b + (s << 8) otherwise                       ***)

let FW_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc [0x1c50,0x1de0];;

(*** The fill function from its entry to its return, for the symbols ***)
(*** syms at bg, the bytes of fw_block at dst                          ***)

let fw_goal =
 `!pc returnaddress (dst:int64) (bg:int64) (syms:byte list) nb tlg b lv e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     nb <= tlg /\ tlg <= 12 /\ b < 256 /\ lv < 256 /\ LENGTH syms <= 256 /\
     nonoverlapping (dst,4 * 2 EXP (tlg - nb) * LENGTH syms)
                    (word pc,32000) /\
     nonoverlapping (dst,4 * 2 EXP (tlg - nb) * LENGTH syms)
                    (bg,LENGTH syms)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x1c50) /\ read X30 s = returnaddress /\
               read X0 s = dst /\ read X1 s = bg /\
               read X2 s = word_add bg (word(LENGTH syms)) /\
               read X3 s = word nb /\ read X4 s = word tlg /\
               read X5 s = word b /\ read X6 s = word lv /\
               read (memory :> bytes(bg,LENGTH syms)) s =
               num_of_bytelist syms /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(dst,4 * 2 EXP (tlg - nb) * LENGTH syms))
                    s =
               num_of_bytelist(fw_block (2 EXP (tlg - nb)) lv nb b syms) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [bg,LENGTH syms; dst,4 * 2 EXP (tlg - nb) * LENGTH syms]
                      [dst,4 * 2 EXP (tlg - nb) * LENGTH syms]))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(dst,4 * 2 EXP (tlg - nb) *
                                          LENGTH syms)])`;;

(*** Simulation, with the pointers normalized ***)

let FW_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC FW_EXEC [n] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
  ZSTD_SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                  WORD_CMP_64_SFLAGS) THEN
                TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let FW_STEPS_TAC ns = MAP_EVERY FW_STEP_TAC ns;;

let FW_NUM_CONV = DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV);;

(*** The first steps, computing tlg - nb = d in W4 ***)

let WORD_AND_31_SMALL = prove
 (`!d. d < 32 ==> word_and (word d) (word 31):int32 = word d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `5`]
    (INST_TYPE [`:32`,`:N`] WORD_AND_MASK_SMALL)) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
  ASM_SIMP_TAC[MOD_LT]);;

let FW_START_TAC =
  PUFF_INIT_TAC "s0" THEN FW_STEPS_TAC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN FW_STEPS_TAC (2--3) THEN
  TRY(FIRST_ASSUM(fun th ->
        if concl th = `d < 32`
        then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WORD_AND_31_SMALL th])
        else NO_TAC));;

(*** No symbols ***)

let FW_EMPTY_TAC =
  PUFF_FINAL_TAC THEN
  ASM_REWRITE_TAC[fw_block; MULT_CLAUSES; list_of_seq; num_of_bytelist;
                  READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];;

(*** The memory of the entries of a symbol from k 64-bit stores at a ***)

let FW_COMBINE_RULE a m n th1 th2 =
  let e = rand(rand(concl th1)) and s = rand(lhand(concl th1)) in
  let ith = ISPECL [a; mk_small_numeral m; mk_small_numeral n; e; s]
              READ_MEMORY_FW_REP_COMBINE in
  let ith' = CONV_RULE (FW_NUM_CONV THENC REWRITE_CONV[WORD_ADD_ASSOC_NUM])
               ith in
  MP ith' (CONJ th1 th2);;

let fw_bound_th asl =
  let ok th = can (term_match [] `!s. fw_entry lv nb b s < n`) (concl th) in
  let th = snd(find (ok o snd) asl) in
  SPEC `EL i syms:byte`
   (CONV_RULE(ONCE_DEPTH_CONV(fun t ->
      if t = `4294967296` then SYM(NUM_REDUCE_CONV `2 EXP 32`)
      else failwith "")) th);;

let fw_addr a j =
  if j = 0 then a else
  rhs(concl(REWRITE_CONV[WORD_ADD_ASSOC_NUM]
    (mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
             mk_comb(`word:num->int64`,mk_small_numeral j)))));;

let FW_STORES64_TAC a k =
  W(fun (asl,w) ->
    let s = rand w in
    let e = `fw_entry lv nb b (EL i syms)` in
    let vth = MP (SPEC e FW_VAL_REP2) (fw_bound_th asl) in
    let store j =
      let tm = subst [fw_addr a (8 * j),`x:int64`; s,`s:armstate`]
                 `read (memory :> bytes64 x) s` in
      let sth = snd(find (fun (_,th) -> let c = concl th in
                            is_eq c && lhs c = tm) asl) in
      MATCH_MP READ_MEMORY_FW_REP_STORE64 (CONJ sth vth) in
    let rec go j th =
      if j = k then th
      else go (j + 1) (FW_COMBINE_RULE a (2 * j) 2 th (store j)) in
    ASSUME_TAC(go 1 (store 0)));;

let FW_STORES32_TAC a k =
  W(fun (asl,w) ->
    let s = rand w in
    let bth = fw_bound_th asl in
    let store j =
      let tm = subst [fw_addr a (4 * j),`x:int64`; s,`s:armstate`]
                 `read (memory :> bytes32 x) s` in
      let sth = snd(find (fun (_,th) -> let c = concl th in
                            is_eq c && lhs c = tm) asl) in
      MATCH_MP READ_MEMORY_FW_REP_STORE32 (CONJ sth bth) in
    let rec go j th =
      if j = k then th
      else go (j + 1) (FW_COMBINE_RULE a j 1 th (store j)) in
    ASSUME_TAC(go 1 (store 0)));;

(*** The prefix of the table extended by the entries of symbol i, with ***)
(*** L entries a symbol, and the rest of the invariant                ***)

let FW_EXTEND_TAC L =
  W(fun (asl,w) ->
    let s = rand w in
    MP_TAC(ISPECL [`dst:int64`; L; `lv:num`; `nb:num`; `b:num`;
                   `syms:byte list`; `i:num`; s] READ_MEMORY_FW_EXTEND)) THEN
  REWRITE_TAC[MULT_ASSOC] THEN CONV_TAC FW_NUM_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN DISCH_TAC THEN
  PUFF_FINAL_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC;;

(*** The loops for d = 0, 1, 2, 3 ***)

let fw_rr k =
  subst [k,`k:num`]
   `[bg,LENGTH(syms:byte list); dst,k * LENGTH syms]:(int64#num)list`
and fw_wr k =
  subst [k,`k:num`] `[dst,k * LENGTH(syms:byte list)]:(int64#num)list`;;

let fw_inv0 = with_memsafe_loop (fw_rr `4`) (fw_wr `4`)
 `\i s.
  (read X30 s = returnaddress /\ read X0 s = dst /\ read X1 s = bg /\
   read X2 s = word(LENGTH syms) /\
   read X3 s = word(16777216 * lv + 65536 * nb) /\ read X5 s = word b /\
   read X6 s = word lv /\ read X7 s = word i /\
   read (memory :> bytes(bg,LENGTH syms)) s = num_of_bytelist syms /\
   read (memory :> bytes(dst,4 * i)) s =
   num_of_bytelist(fw_block 1 lv nb b (SUB_LIST(0,i) syms))) /\
  (read ZF s <=> i = LENGTH syms)`;;

let fw_inv k L r = with_memsafe_loop (fw_rr k) (fw_wr k)
 (subst [k,`k:num`; L,`L:num`; r,`r:(armstate,int64)component`]
 `\i s.
  (read X30 s = returnaddress /\ read X0 s = word_add dst (word(k * i)) /\
   read X1 s = word_add bg (word i) /\
   read X2 s = word_add bg (word(LENGTH syms)) /\
   read (r:(armstate,int64)component) s =
   word(16777216 * lv + 65536 * nb) /\ read X5 s = word b /\
   read X6 s = word lv /\
   read (memory :> bytes(bg,LENGTH syms)) s = num_of_bytelist syms /\
   read (memory :> bytes(dst,k * i)) s =
   num_of_bytelist(fw_block L lv nb b (SUB_LIST(0,i) syms))) /\
  (read ZF s <=> i = LENGTH syms)`);;

let FW_BOUND_TAC =
  SUBGOAL_THEN `!s. fw_entry lv nb b s < 2 EXP 32` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FW_ENTRY_BOUND THEN ASM_ARITH_TAC; ALL_TAC];;

let FW_CASE_TAC d =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  REWRITE_TAC[MULT_ASSOC] THEN RULE_ASSUM_TAC(REWRITE_RULE[MULT_ASSOC]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  FW_BOUND_TAC THEN ASM_CASES_TAC `LENGTH(syms:byte list) = 0`;;

let FW_LOOP_START_TAC n =
  FW_START_TAC THEN FW_STEPS_TAC (4--n) THEN PUFF_FINAL_TAC THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; fw_block; LENGTH; MULT_CLAUSES;
                  list_of_seq; num_of_bytelist; WORD_ADD_0;
                  READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];;

let FW_BODY_START_TAC n =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`bg:int64`; `syms:byte list`; `i:num`; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FW_STEPS_TAC (1--n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FW_ENTRY_ALT; FW_ENTRY_ALT2]);;

let FW_BACK_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
  FW_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let FW_EXIT_TAC n =
  PUFF_INIT_TAC "s0" THEN FW_STEPS_TAC (1--n) THEN PUFF_FINAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUB_LIST_LENGTH]) THEN ASM_REWRITE_TAC[];;

let FW_D0_TAC =
  FW_CASE_TAC `0` THENL
   [FW_START_TAC THEN FW_STEPS_TAC (4--13) THEN FW_EMPTY_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `LENGTH(syms:byte list)` `pc + 0x1db0` `pc + 0x1dd0`
    fw_inv0 THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FW_LOOP_START_TAC 17;
    FW_BODY_START_TAC 8 THEN
    SUBGOAL_THEN `val(word i:int64) = i`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [MATCH_MP_TAC VAL_WORD_LT64 THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FW_STORES32_TAC `word_add dst (word(4 * i)):int64` 1 THEN
    FW_EXTEND_TAC `1`;
    FW_BACK_TAC;
    FW_EXIT_TAC 2];;

let FW_DSMALL_TAC d k L r n0 n1 pc1 pc2 nb stores ne =
  FW_CASE_TAC d THENL
   [FW_START_TAC THEN FW_STEPS_TAC (4--n0) THEN FW_EMPTY_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `LENGTH(syms:byte list)` pc1 pc2 (fw_inv k L r) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FW_LOOP_START_TAC n1;
    FW_BODY_START_TAC nb THEN
    stores (subst [k,`k:num`] `word_add dst (word(k * i)):int64`) THEN
    FW_EXTEND_TAC L;
    FW_BACK_TAC;
    FW_EXIT_TAC ne];;

let fw_cases_tac =
  REWRITE_TAC[GSYM puff_memsafe; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `?d. tlg = nb + d` (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `tlg - nb` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB2] THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
  ASM_CASES_TAC `d = 0` THENL [FW_D0_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `d = 1` THENL
   [FW_DSMALL_TAC `1` `8` `2` `X3` 17 16 `pc + 0x1c90` `pc + 0x1cb0` 8
      (fun a -> FW_STORES32_TAC a 2) 2;
    ALL_TAC] THEN
  ASM_CASES_TAC `d = 2` THENL
   [FW_DSMALL_TAC `2` `16` `4` `X4` 12 11 `pc + 0x1d10` `pc + 0x1d34` 9
      (fun a -> FW_STORES64_TAC a 2) 3;
    ALL_TAC] THEN
  ASM_CASES_TAC `d = 3` THENL
   [FW_DSMALL_TAC `3` `32` `8` `X4` 16 15 `pc + 0x1cd0` `pc + 0x1cf8` 10
      (fun a -> FW_STORES64_TAC a 4) 3;
    ALL_TAC];;

(*** The loops for d >= 4, with 2^d = 8 * m entries a symbol ***)

let fw_invg = with_memsafe_loop (fw_rr `32 * m`) (fw_wr `32 * m`)
 `\i s.
  (read X30 s = returnaddress /\
   read X0 s = word_add dst (word((32 * m) * i)) /\
   read X1 s = word_add bg (word i) /\
   read X2 s = word_add bg (word(LENGTH syms)) /\
   read X5 s = word b /\ read X6 s = word lv /\
   read X7 s = word(16777216 * lv + 65536 * nb) /\
   read X8 s = word(32 * m) /\
   read (memory :> bytes(bg,LENGTH syms)) s = num_of_bytelist syms /\
   read (memory :> bytes(dst,(32 * m) * i)) s =
   num_of_bytelist(fw_block (8 * m) lv nb b (SUB_LIST(0,i) syms))) /\
  (read ZF s <=> i = LENGTH syms)`;;

let fw_inng = with_memsafe_loop (fw_rr `32 * m`) (fw_wr `32 * m`)
 `\j s.
  (read X30 s = returnaddress /\
   read X0 s = word_add dst (word((32 * m) * i + 32 * j)) /\
   read X1 s = word_add bg (word i) /\
   read X2 s = word_add bg (word(LENGTH syms)) /\
   read X3 s = word(fw_entry lv nb b (EL i syms) +
                    4294967296 * fw_entry lv nb b (EL i syms)) /\
   read X4 s = word_add dst (word((32 * m) * i + 32 * m)) /\
   read X5 s = word b /\ read X6 s = word lv /\
   read X7 s = word(16777216 * lv + 65536 * nb) /\
   read X8 s = word(32 * m) /\
   read (memory :> bytes(bg,LENGTH syms)) s = num_of_bytelist syms /\
   read (memory :> bytes(dst,(32 * m) * i)) s =
   num_of_bytelist(fw_block (8 * m) lv nb b (SUB_LIST(0,i) syms)) /\
   read (memory :> bytes(word_add dst (word((32 * m) * i)),32 * j)) s =
   fw_rep (8 * j) (fw_entry lv nb b (EL i syms))) /\
  (read ZF s <=> j = m)`;;

let FW_MNORM_TAC =
  RULE_ASSUM_TAC(CONV_RULE FW_NUM_CONV o REWRITE_RULE[MULT_ASSOC]);;

let FW_INNER_BODY_TAC =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
  FW_STEPS_TAC (1--4) THEN PTR_DECIDE_FLAGS_TAC THEN
  FW_STORES64_TAC `word_add dst (word((32 * m) * i + 32 * j)):int64` 4 THEN
  W(fun (asl,w) ->
    let s = rand w in
    MP_TAC(ISPECL [`word_add dst (word((32 * m) * i)):int64`; `8 * j`; `8`;
                   `fw_entry lv nb b (EL i syms)`; s]
                  READ_MEMORY_FW_REP_COMBINE)) THEN
  REWRITE_TAC[MULT_ASSOC; WORD_ADD_ASSOC_NUM] THEN CONV_TAC FW_NUM_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; MULT_ASSOC] THEN
  CONV_TAC FW_NUM_CONV THEN DISCH_TAC THEN
  PUFF_FINAL_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; MULT_ASSOC] THEN
  CONV_TAC FW_NUM_CONV THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ARITH_TAC];;

let FW_DGEN_TAC =
  SUBGOAL_THEN `4 <= d /\ d <= 12 /\ d < 32` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP d = 8 * 2 EXP (d - 3) /\ 2 EXP 1 <= 2 EXP (d - 3) /\
                2 EXP (d - 3) <= 2 EXP 9`
  MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 = 2 EXP 3`; GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN
    CONJ_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
    CONV_TAC(LAND_CONV(DEPTH_CONV NUM_EXP_CONV)) THEN STRIP_TAC] THEN
  ABBREV_TAC `m = 2 EXP (d - 3)` THEN
  REWRITE_TAC[ASSUME `2 EXP d = 8 * m`; MULT_ASSOC] THEN
  CONV_TAC FW_NUM_CONV THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) then th else
    CONV_RULE FW_NUM_CONV
     (REWRITE_RULE[ASSUME `2 EXP d = 8 * m`; MULT_ASSOC] th)) THEN
  SUBGOAL_THEN `(32 * m) * LENGTH(syms:byte list) <= 4194304` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `(32 * 512) * 256` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  FW_BOUND_TAC THEN
  ASM_CASES_TAC `LENGTH(syms:byte list) = 0` THENL
   [FW_START_TAC THEN FW_STEPS_TAC (4--14) THEN FW_EMPTY_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `LENGTH(syms:byte list)` `pc + 0x1d50` `pc + 0x1d8c`
    fw_invg THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FW_START_TAC THEN FW_STEPS_TAC (4--16) THEN FW_MNORM_TAC THEN
    PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[SUB_LIST_CLAUSES; fw_block; LENGTH; MULT_CLAUSES;
                    list_of_seq; num_of_bytelist; WORD_ADD_0;
                    READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(32 * m) * i + 32 * m <= (32 * m) * LENGTH(syms:byte list)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(32 * m) * i + 32 * m = (32 * m) * (i + 1)`;
                  LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_WHILE_PUP_TAC `m:num` `pc + 0x1d70` `pc + 0x1d80` fw_inng THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      PUFF_INIT_TAC "s0" THEN
      MP_TAC(ISPECL [`bg:int64`; `syms:byte list`; `i:num`; `s0:armstate`]
        READ_MEMORY_BYTES8_BYTELIST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FW_STEPS_TAC (1--8) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FW_ENTRY_ALT; FW_ENTRY_ALT2]) THEN
      PUFF_FINAL_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; FW_REP_CLAUSES;
                      READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
      FW_INNER_BODY_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
      FW_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
      PUFF_INIT_TAC "s0" THEN FW_STEPS_TAC (1--3) THEN
      PTR_DECIDE_FLAGS_TAC THEN FW_EXTEND_TAC `8 * m`];
    FW_BACK_TAC;
    FW_EXIT_TAC 2];;

(*** The fill function ***)

let HUF_FILLDTABLEX2FORWEIGHT_CORRECT = prove
 (fw_goal,
  fw_cases_tac THEN FW_DGEN_TAC);;

(* ------------------------------------------------------------------------- *)
(* The setting of the pieces of HUF_readDTableX2_wksp: the regions, the      *)
(* frame, the invariants and the hypotheses; and the pieces of the loop over *)
(* the weights at 0x6e44: a weight without second symbols (RD2_WITER1), the  *)
(* end (RD2_FEND), the prefill of the entries of a symbol (RD2_PREFILL), the *)
(* ends of a symbol and of a weight (RD2_SYMTAIL and RD2_WTAIL2), the start  *)
(* of a weight with second symbols (RD2_W2START and RD2_W2EMPTY) and the     *)
(* start of the loop (RD2_FSTART).                                           *)
(* ------------------------------------------------------------------------- *)

(*** HUF_readDTableX2_wksp at 0x6b90 ***)

let RD2_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc [0x6b90,0x70c4];;

(*** Simulation, as FW_STEP_TAC ***)

let RD2_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC RD2_EXEC [n] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_NUM]) THEN
  ZSTD_SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                  WORD_CMP_64_SFLAGS) THEN
                TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let RD2_STEPS_TAC ns = MAP_EVERY RD2_STEP_TAC ns;;

(*** Reading parts of memory given as numbers and byte lists ***)

let NUM_OF_BYTELIST_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTELIST_SLICE = prove
 (`!a:int64 (l:byte list) i k s:armstate.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        i + k <= LENGTH l
        ==> read (memory :> bytes(word_add a (word i),k)) s =
            num_of_bytelist(SUB_LIST(i,k) l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_BYTELIST_WORDLIST; NUM_OF_WORDLIST_SUB_LIST] THEN
  REWRITE_TAC[GSYM NUM_OF_BYTELIST_WORDLIST; DIMINDEX_8] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES32_OF_NUM = prove
 (`!a:int64 m n off k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ off = 4 * k /\ 4 * k + 4 <= m
        ==> read (memory :> bytes32(word_add a (word off))) s =
            word((n DIV 2 EXP (32 * k)) MOD 2 EXP 32)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `32 * k = 8 * (4 * k)`;
              ARITH_RULE `2 EXP 32 = 2 EXP (8 * 4)`] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** The setting: regions, frame and the facts throughout ***)

let rd2_rr =
 `[src,LENGTH(l:byte list); dtable,4 + 4 * 2 EXP mtl; wk,2124;
   word_sub stackpointer (word 528),528;
   word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
   word_add (word pc) (word 31600),128]:(int64#num)list`
and rd2_wr =
 `[dtable,4 + 4 * 2 EXP mtl; wk,2124;
   word_sub stackpointer (word 528),528]:(int64#num)list`;;

let rd2_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
             SP] ,,
  MAYCHANGE [memory :> bytes(dtable,4 + 4 * 2 EXP mtl);
             memory :> bytes(wk,2124);
             memory :> bytes(word_sub stackpointer (word 528),528)]`;;

(*** The frame of 208 bytes: the saved registers ***)

let rd2_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read SP s = word_sub stackpointer (word 208) /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 16))) s = x29 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 24))) s =
  returnaddress /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 32))) s = x19 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 40))) s = x20 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 48))) s = x21 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 56))) s = x22 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 64))) s = x23 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 72))) s = x24 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 80))) s = x25 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 88))) s = x26 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 96))) s = x27 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 104))) s = x28`;;

(*** The locals of the fill on the stack ***)

let rd2_locals =
 `read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 128))) s =
  word(mw + 1) /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 136))) s =
  word((ml + 1) - mw) /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 168))) s =
  word tl /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 172))) s = dtd /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 176))) s =
  word h /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 184))) s =
  dtable`;;

(*** The workspace while the table is filled: rankVal, rankStats and   ***)
(*** rankStart as the number wkv, the sorted symbols as the bytes sl  ***)

let rd2_wkmem =
 `read (memory :> bytes(wk,736)) s = wkv /\
  read (memory :> bytes(word_add wk (word 736),256)) s = num_of_bytelist sl`;;

(*** The facts about the weights, tl and the workspace (no state) ***)

let rd2_facts =
 `huf_complete ws ml /\ ALL (\x. x <= mw) ws /\ LENGTH ws <= 256 /\
  huf_total ws = 2 EXP ml /\ 1 <= ml /\ ml <= tl /\ tl <= mtl /\
  mtl <= 12 /\ 1 <= mw /\ mw <= ml /\ ~(huf_rank ws mw = 0) /\
  (!w. 1 <= w /\ w <= mw
       ==> (wkv DIV 2 EXP (32 * w)) MOD 2 EXP 32 =
           huf_ustart ws w * 2 EXP (tl - ml)) /\
  (!c w. (ml + 1) - mw <= c /\ c + (ml + 1) - mw <= tl /\
         1 <= w /\ w <= mw
         ==> (wkv DIV 2 EXP (32 * (13 * c + w))) MOD 2 EXP 32 =
             huf_rv ws ml (tl - c) w) /\
  (!k. k <= mw
       ==> (wkv DIV 2 EXP (32 * (170 + k))) MOD 2 EXP 32 =
           huf_bstart ws (k + 1) - huf_rank ws 0) /\
  LENGTH sl = 256 /\
  (!w. 1 <= w /\ w <= mw
       ==> SUB_LIST(huf_bstart ws w - huf_rank ws 0,huf_rank ws w) sl =
           huf_wsyms ws w)`;;

(*** Abbreviations in the templates: for the weight w, nb1 its code      ***)
(*** length, r the bits left in the table, U the start of its entries,   ***)
(*** for its symbol k, st the start of the entries and s1 the symbol,     ***)
(*** minW the smallest weight whose code fits in the r bits, and pre the ***)
(*** prefix of the table filled                                          ***)

let rd2_abbrevs =
  [`nb1:num`,`(ml + 1) - w`;
   `r:num`,`(tl + w) - (ml + 1)`;
   `U:num`,`huf_ustart ws w * 2 EXP (tl - ml)`;
   `st:num`,`huf_ustart ws w * 2 EXP (tl - ml) +
             k * 2 EXP ((tl + w) - (ml + 1))`;
   `s1:num`,`huf_sorted ws (huf_bstart ws w + k)`;
   `minW:num`,`MAX 1 ((2 * ml + 2) - (w + tl))`;
   `bgn:num`,`huf_bstart ws w - huf_rank ws 0`;
   `enw:num`,`huf_bstart ws (w + 1) - huf_rank ws 0`];;

let rd2_expand tm =
  let rec go tm =
    let tm' = subst (map (fun (v,t) -> (t,v)) rd2_abbrevs) tm in
    if tm' = tm then tm else go tm' in
  go tm;;

(*** The table prefix of p entries ***)

let rd2_prefix p =
  subst [p,`p:num`]
   `read (memory :> bytes(word_add dtable (word 4),4 * p)) s =
    num_of_bytelist(SUB_LIST(0,4 * p) (huf_dtable2 ws ml tl))`;;

(*** In the loops over the symbols of a weight w and the weights w2 of a ***)
(*** second symbol: the registers that do not change and the locals      ***)

let rd2_symregs =
 `read X10 s = word r /\ read X13 s = word_add wk (word 736) /\
  read X14 s = word((2 * ml + 1) - (mw + w)) /\ read X15 s = word minW /\
  read X19 s = word tl /\
  read X21 s = word_zx(word_sub (word(2 * ml + 2)) (word(w + tl)):int32) /\
  read X22 s = word((2 * ml + 2) - w) /\
  read X24 s = word_add dtable (word 4) /\
  read X26 s = word_add wk (word(52 * nb1 + 4 * minW)) /\
  read X28 s = word_add wk (word(680 + 4 * minW)) /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 116))) s =
  word(2 EXP r) /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 120))) s =
  word_add wk (word enw) /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 132))) s =
  word(16777216 + 65536 * nb1) /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 140))) s =
  word(2 * (ml - mw)) /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 144))) s =
  word nb1 /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 148))) s =
  word r /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 152))) s =
  word_add wk (word(4 * w)) /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 208)) (word 160))) s = wk`;;

(*** The loop over the weights w2 of the second symbol at 0x6f60, for    ***)
(*** the symbol k of the weight w, the first w2 - minW of them done      ***)

let rd2_w2regs =
 `read X11 s = word_add wk (word(52 * nb1 + 4 * w2)) /\
  read X12 s = word s1 /\
  read X18 s = word st /\
  read X20 s = word_add wk (word(bgn + k)) /\
  read X23 s = word_add dtable (word(4 + 4 * st)) /\
  read X25 s = word_add wk (word(680 + 4 * w2)) /\
  read X27 s = word((2 * ml + 2) - (w + w2))`;;

(*** The loop over the weights w at 0x6e44, the weights below w done ***)

let rd2_wregs =
 `read X12 s = word r /\ read X13 s = word_add wk (word 736) /\
  read X14 s = word((2 * ml + 1) - (mw + w)) /\
  read X15 s = word(2 * (ml - mw)) /\
  read X18 s = word_add wk (word(4 * w)) /\ read X19 s = word tl /\
  read X20 s = wk /\
  read X21 s = word_zx(word_sub (word(2 * ml + 2)) (word(w + tl)):int32) /\
  read X22 s = word((2 * ml + 2) - w) /\ read X23 s = word nb1 /\
  read X24 s = word_add dtable (word 4)`;;

let rd2_winv =
  with_memsafe rd2_rr rd2_wr
   (rd2_expand(mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6e44)`; rd2_wregs; rd2_locals; rd2_wkmem;
      rd2_prefix `U:num`; rd2_common])));;

(*** At 0x6fdc, after the loop over the weights, the table filled ***)

let rd2_fdone =
  with_memsafe rd2_rr rd2_wr
   (mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6fdc)`; rd2_locals; rd2_wkmem;
      rd2_prefix `2 EXP tl`; rd2_common]));;

(*** The hypotheses, the variables and the goals of the pieces ***)

let rd2_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\
  nonoverlapping (dtable:int64,4 + 4 * 2 EXP mtl) (wk:int64,2124) /\
  nonoverlapping (dtable,4 + 4 * 2 EXP mtl)
                 (word_sub stackpointer (word 528),528) /\
  nonoverlapping (dtable,4 + 4 * 2 EXP mtl) (word pc,0x20018) /\
  nonoverlapping (wk,2124) (word_sub stackpointer (word 528),528) /\
  nonoverlapping (wk,2124) (word pc,0x20018) /\
  nonoverlapping (word_sub stackpointer (word 528),528) (word pc,0x20018)`;;

let rd2_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `dtable:int64`;
  `src:int64`; `l:byte list`; `wk:int64`; `ea:int64`; `el:num`;
  `mtl:num`; `ws:num list`; `ml:num`; `h:num`; `tl:num`; `mw:num`;
  `dtd:int32`; `wkv:num`; `sl:byte list`;
  `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`; `x23:int64`;
  `x24:int64`; `x25:int64`; `x26:int64`; `x27:int64`; `x28:int64`;
  `x29:int64`; `e:uarch_event list`];;

let mk_rd2_goal extra hyps pre post =
  let tm = mk_imp(hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; rd2_frame]) in
  let vs = rd2_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_rd2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** One iteration of the loop over the weights, for the weight w with   ***)
(*** no second symbol fitting (r < minBits): one level-1 fill            ***)

let rd2_wnext =
  let inv1 = rhs(concl(BETA_CONV(mk_comb(subst [`w + 1`,`w:num`] rd2_winv,
                                         `s:armstate`)))) in
  mk_abs(`s:armstate`,
    mk_disj(mk_conj(`w + 1 <= mw`,inv1),
            mk_conj(`(w:num) = mw`,rhs(concl(BETA_CONV(mk_comb(rd2_fdone,
                                                    `s:armstate`)))))));;

let rd2_witer1_goal = mk_rd2_goal [`w:num`]
  (list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ tl + w + mw < 2 * ml + 2`])
  rd2_winv rd2_wnext;;

(*** The word at wk + off (off = 4 * k) of the workspace number wkv in   ***)
(*** the state s, with its value from fact (an instance of a fact about ***)
(*** wkv, specialized and with its hypotheses proved by arithmetic)     ***)

let RD2_WK32_TAC off k s =
  W(fun (asl,w) ->
    let th = ISPECL [`wk:int64`; `736`; `wkv:num`; off; k; s]
               READ_MEMORY_BYTES32_OF_NUM in
    MP_TAC th) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE SIMPLE_ARITH_TAC);
    DISCH_TAC];;

(*** Rewriting a value (wkv DIV 2 EXP (32 * k)) MOD 2 EXP 32 in the      ***)
(*** assumptions with the facts about wkv                                ***)

let RD2_WKV_TAC =
  let pats = [`(wkv DIV 2 EXP (32 * w)) MOD 2 EXP 32`;
              `(wkv DIV 2 EXP (32 * (13 * c + w))) MOD 2 EXP 32`;
              `(wkv DIV 2 EXP (32 * (170 + k))) MOD 2 EXP 32`] in
  W(fun (asl,w) ->
    let facts = filter (fun th ->
      let c = concl th in
      is_forall c &&
      can (find_term (fun t -> exists (fun p -> can (term_match [] p) t)
                                      pats)) c) (map snd asl) in
    let rule th = CONV_RULE(ONCE_DEPTH_CONV(fun t ->
      if not(exists (fun p -> can (term_match [] p) t) pats)
      then failwith "" else
      tryfind (fun f ->
        let ith = PART_MATCH (lhs o rand) f t in
        MP ith (TAC_PROOF((asl,lhand(concl ith)),
                          REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC)))
       facts)) th in
    RULE_ASSUM_TAC(fun th ->
      if is_forall(concl th) then th else try rule th with Failure _ -> th));;

(*** Setting the value of a register in a chosen form ***)

let RD2_SET_REG_TAC tm tac =
  SUBGOAL_THEN tm (fun th ->
    let l = lhs(concl th) in
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
      (fun th' -> is_eq(concl th') && lhs(concl th') = l))) THEN
    ASSUME_TAC th) THENL [tac; ALL_TAC];;


(*** Pruning the assumptions to the simple linear facts about numbers   ***)
(*** (sums of variables and numerals, no subtraction), for arithmetic   ***)
(*** at the end of a piece that would otherwise split cases on every    ***)
(*** subtraction among the facts                                         ***)

let rd2_simple_fact tm =
  let rec simple_num t =
    is_var t || is_numeral t ||
    (match t with
       Comb(Comb(Const("+",_),a),b) -> simple_num a && simple_num b
     | Comb(Comb(Const("*",_),a),b) -> is_numeral a && simple_num b
     | _ -> false) in
  let rel t =
    match t with
      Comb(Comb(Const(("<=" | "<" | "="),_),a),b) ->
        type_of a = `:num` && simple_num a && simple_num b
    | _ -> false in
  rel tm || (is_neg tm && rel(rand tm));;

let RD2_SIMPLE_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    not(rd2_simple_fact(concl th)))));;

(*** Abbreviations whose equations, having subtractions, are hidden from ***)
(*** the arithmetic as rd2_hide(t = v) (SIMPLE_ARITH_TAC uses every      ***)
(*** relation among the assumptions, and splits cases on each            ***)
(*** subtraction), and rewriting with them in the other assumptions      ***)

let rd2_hide = new_definition `rd2_hide (p:bool) <=> p`;;

let is_rd2_hidden th =
  match concl th with
    Comb(Const("rd2_hide",_),_) -> true
  | _ -> false;;

let RD2_HIDE_TAC tm =
  FIRST_X_ASSUM(fun th ->
    if concl th = tm then ASSUME_TAC(EQ_MP (SYM(SPEC tm rd2_hide)) th)
    else NO_TAC);;

let RD2_ABBREV_TAC tm =
  let v,t = dest_eq tm in
  ABBREV_TAC tm THEN RD2_HIDE_TAC (mk_eq(t,v));;

let rd2_hidden asl tm =
  EQ_MP (SPEC tm rd2_hide)
   (snd(find (fun (_,th) -> concl th = mk_comb(`rd2_hide`,tm)) asl));;

let RD2_UNHIDE_TAC tm =
  W(fun (asl,w) -> ASSUME_TAC(rd2_hidden asl tm));;

let RD2_FOLD_TAC tms =
  W(fun (asl,w) ->
    let ths = map (rd2_hidden asl) tms in
    RULE_ASSUM_TAC(fun th -> if is_rd2_hidden th then th
                             else REWRITE_RULE ths th));;

(*** Facts about the weight w, the abbreviations sc = 2^(tl - ml), L =   ***)
(*** 2^r, tt = 2^tl and dsz = 2^mtl, and the entries U..U + nl of the    ***)
(*** weight in the table and its symbols bw..ew of the sorted symbols    ***)

let RD2_WEIGHT_FACTS_TAC =
  SUBGOAL_THEN `w <= ml /\ ml + 1 <= tl + w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`] HUF_U_STEP) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `mw:num`] HUF_U_ALL) THEN
  MP_TAC(SPECL [`ws:num list`; `w + 1`; `mw + 1`] HUF_USTART_MONO) THEN
  ASM_REWRITE_TAC[LE_ADD_RCANCEL] THEN
  SUBGOAL_THEN `tl - ((ml + 1) - w) = (tl + w) - (ml + 1)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP tl <= 4096 /\ 2 EXP tl <= 2 EXP mtl /\
                2 EXP mtl <= 4096` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[LE_EXP; ARITH_RULE `4096 = 2 EXP 12`] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `huf_ustart ws (w + 1) * 2 EXP (tl - ml) <=
                huf_ustart ws (mw + 1) * 2 EXP (tl - ml)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`] HUF_BSTART_SUC) THEN
  MP_TAC(SPECL [`ws:num list`; `1`; `w:num`] HUF_BSTART_MONO) THEN
  MP_TAC(SPECL [`ws:num list`; `w + 1`] HUF_BSTART_LE) THEN
  REWRITE_TAC[HUF_START_1] THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP ((tl + w) - (ml + 1)) <= 2 EXP tl` ASSUME_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RD2_ABBREV_TAC `sc = 2 EXP (tl - ml)` THEN
  RD2_ABBREV_TAC `L = 2 EXP ((tl + w) - (ml + 1))` THEN
  RD2_ABBREV_TAC `tt = 2 EXP tl` THEN
  RD2_ABBREV_TAC `dsz = 2 EXP mtl` THEN
  RD2_ABBREV_TAC `uu = huf_ustart ws w * sc` THEN
  SUBGOAL_THEN `uu + L * huf_rank ws w <= tt /\ tt <= dsz /\ uu <= tt`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC];;

(*** The workspace words of the weight w and its sorted symbols, in s0 ***)

let RD2_WEIGHT_READS_TAC =
  RD2_WK32_TAC `4 * w` `w:num` `s0:armstate` THEN
  RD2_WK32_TAC `4 * w + 676` `170 + (w - 1)` `s0:armstate` THEN
  RD2_WK32_TAC `4 * w + 680` `170 + w` `s0:armstate` THEN
  RD2_WKV_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`w:num`; `1`] SUB_ADD)
                                (ASSUME `1 <= w`)]) THEN
  RD2_FOLD_TAC [`2 EXP (tl - ml) = sc`; `huf_ustart ws w * sc = uu`];;

(*** The level-1 fill call at step 15, for the weight w ***)

let RD2_L1_CALL_TAC =
  RD2_SET_REG_TAC
   `read X2 s14 =
    word_add (word_add wk (word (736 + huf_bstart ws w - huf_rank ws 0)))
             (word(huf_rank ws w))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMPLE_ARITH_TAC) THEN
  MP_TAC(ISPECL [`word_add wk (word 736):int64`; `sl:byte list`;
    `huf_bstart ws w - huf_rank ws 0`; `huf_rank ws w`; `s14:armstate`]
    READ_MEMORY_BYTELIST_SLICE) THEN
  ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `w:num` th)
    (CONJ (ASSUME `1 <= w`) (ASSUME `w <= mw`))]) o
    check (fun th -> is_forall(concl th) &&
           can (find_term ((=) `huf_wsyms`)) (concl th))) THEN
  DISCH_TAC THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 28196):int64`;
    `word_add dtable (word (4 + 4 * uu)):int64`;
    `word_add wk (word (736 + huf_bstart ws w - huf_rank ws 0)):int64`;
    `huf_wsyms ws w`; `(ml + 1) - w`; `tl:num`; `0`; `1`]
    HUF_FILLDTABLEX2FORWEIGHT_CORRECT))) THEN
  REWRITE_TAC[LENGTH_HUF_WSYMS] THEN
  SUBGOAL_THEN `tl - ((ml + 1) - w) = (tl + w) - (ml + 1)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> REWRITE_TAC
     (map (rd2_hidden asl) [`2 EXP ((tl + w) - (ml + 1)) = L`])) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s15" THEN
  EVENTS_UNABBREV_TAC;;

(*** The level-1 block in the table and the prefix extended by it ***)

let RD2_L1_EXTEND_TAC =
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`; `(ml + 1) - w`;
                `(tl + w) - (ml + 1)`] HUF_DTABLE2_LEVEL1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [X_GEN_TAC `v:num` THEN REWRITE_TAC[HUF_RANK_MEM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `v <= mw` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `v:num` o REWRITE_RULE[GSYM ALL_MEM] o
          check (fun th -> concl th = `ALL (\x. x <= mw) ws`)) THEN
        ASM_REWRITE_TAC[];
        SIMPLE_ARITH_TAC];
      SIMPLE_ARITH_TAC];
    DISCH_TAC] THEN
  RD2_FOLD_TAC [`2 EXP (tl - ml) = sc`; `huf_ustart ws w * sc = uu`;
                `2 EXP ((tl + w) - (ml + 1)) = L`] THEN
  W(fun (asl,w) ->
    let s = rand w in
    MP_TAC(ISPECL [`word_add dtable (word 4):int64`; `huf_dtable2 ws ml tl`;
                   `4 * uu`; `4 * L * huf_rank ws w`; s]
      READ_MEMORY_BYTELIST_EXTEND)) THEN
  REWRITE_TAC[LENGTH_HUF_DTABLE2; WORD_ADD_ASSOC_NUM] THEN
  W(fun (asl,w) -> REWRITE_TAC
     (map (rd2_hidden asl) [`2 EXP tl = tt`])) THEN
  FIRST_ASSUM(SUBST1_TAC o
    check (fun th -> is_eq(concl th) &&
                     can (term_match [] `SUB_LIST(4 * uu,n) l:byte list`)
                         (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** The end of an iteration: the registers of the next weight ***)

let RD2_REGS_TAC =
  RD2_SIMPLE_TAC THEN
  W(fun (asl,w) -> CONV_TAC(ZSTD_SMALL_WORD_CONV asl)) THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_ARITH_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC;
         AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
         AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC];;

let RD2_WITER1 = prove
 (rd2_witer1_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD2_WEIGHT_FACTS_TAC THEN
  RD2_WEIGHT_READS_TAC THEN RD2_STEPS_TAC (1--14) THEN
  RD2_L1_CALL_TAC THEN RD2_L1_EXTEND_TAC THEN
  ASM_CASES_TAC `w:num = mw` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `w:num = mw`)) THEN
    RD2_STEPS_TAC (16--23) THEN
    SUBGOAL_THEN `4 * uu + 4 * L * huf_rank ws mw = 4 * tt` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `4 * uu + 4 * L * huf_rank ws mw = 4 * tt`]) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    RD2_STEPS_TAC (16--23) THEN
    SUBGOAL_THEN `4 * uu + 4 * L * huf_rank ws w =
                  4 * (uu + huf_rank ws w * L)` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `4 * uu + 4 * L * huf_rank ws w =
              4 * (uu + huf_rank ws w * L)`]) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN RD2_REGS_TAC]);;

(*** At the return, after the table is filled, for the weights ws with  ***)
(*** codes of at most ml bits and the table log tl                      ***)

let rd2_fpost = with_memsafe rd2_rr rd2_wr `\s.
  read PC s = returnaddress /\ read SP s = stackpointer /\
  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
  read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
  read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
  read X28 s = x28 /\ read X29 s = x29 /\ read X30 s = returnaddress /\
  read X0 s = word h /\
  read (memory :> bytes8 dtable) s = word_subword (dtd:int32) (0,8) /\
  read (memory :> bytes8 (word_add dtable (word 1))) s = word 1 /\
  read (memory :> bytes8 (word_add dtable (word 2))) s = word tl /\
  read (memory :> bytes(word_add dtable (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable2 ws ml tl)`;;

let rd2_fend_goal = mk_rd2_goal []
  (list_mk_conj [rd2_hyps; `tl <= 12`]) rd2_fdone rd2_fpost;;

let READ_MEMORY_BYTES8_1_OF_32 = prove
 (`!x:int64 v s:armstate.
        read (memory :> bytes32 x) s = v
        ==> read (memory :> bytes8(word_add x (word 1))) s =
            word_subword v (8,8)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; GSYM VAL_READ_MEMORY_BYTES8] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_READ_MEMORY_BYTES32; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  SUBST1_TAC(ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`) THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** The bytes of the header as the code writes it ***)

let RD2_HEADER_BYTES = prove
 (`!dtd:int32 tl.
        tl < 256
        ==> word_subword
             (word_insert (word_insert dtd (16,8) (word tl:int32):int32)
                          (8,8) (word 1:int32):int32) (0,8) =
            word_subword dtd (0,8):byte /\
            word_subword
             (word_insert (word_insert dtd (16,8) (word tl:int32):int32)
                          (8,8) (word 1:int32):int32) (8,8) =
            word 1:byte /\
            word_subword
             (word_insert (word_insert dtd (16,8) (word tl:int32):int32)
                          (8,8) (word 1:int32):int32) (16,8) =
            word tl:byte`,
  REPEAT STRIP_TAC THENL
   [CONV_TAC WORD_BLAST; CONV_TAC WORD_BLAST; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `word_subword (word tl:int32) (0,8):byte` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`word tl:int32`,`y:int32`) THEN CONV_TAC WORD_BLAST;
    MATCH_MP_TAC WORD_SUBWORD_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC]);;

(*** The end at 0x6fdc: the header with table log tl, the return ***)

let RD2_FEND = prove
 (rd2_fend_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `2 EXP tl <= 4096` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; LE_EXP] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  RD2_ABBREV_TAC `dsz = 2 EXP mtl` THEN RD2_ABBREV_TAC `tt = 2 EXP tl` THEN
  RD2_STEPS_TAC (1--15) THEN
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhs c = `read (memory :> bytes32 dtable) s15` then
      MAP_EVERY (fun lem -> ASSUME_TAC(MATCH_MP lem th))
       [READ_MEMORY_BYTES8_0_OF_32; READ_MEMORY_BYTES8_1_OF_32;
        READ_MEMORY_BYTES8_2_OF_32]
    else NO_TAC) THEN
  MP_TAC(SPECL [`dtd:int32`; `tl:num`] RD2_HEADER_BYTES) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    AP_TERM_TAC THEN MATCH_MP_TAC SUB_LIST_REFL THEN
    REWRITE_TAC[LENGTH_HUF_DTABLE2] THEN
    W(fun (asl,w) -> REWRITE_TAC[rd2_hidden asl `2 EXP tl = tt`]) THEN
    ARITH_TAC]);;

(*** The loop over the symbols k of a weight w at 0x6ee0 (level 2) ***)

let rd2_syminv =
  with_memsafe rd2_rr rd2_wr
   (rd2_expand(mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6ee0)`; rd2_symregs;
      `read X18 s = word st /\ read X20 s = word_add wk (word(bgn + k))`;
      rd2_locals; rd2_wkmem; rd2_prefix `st:num`; rd2_common])));;

(*** The loop over the weights w2 of the second symbol at 0x6f60 ***)

let rd2_w2inv =
  with_memsafe rd2_rr rd2_wr
   (rd2_expand(mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6f60)`; rd2_symregs; rd2_w2regs;
      rd2_locals; rd2_wkmem; rd2_prefix `st + huf_rv ws ml r w2`;
      rd2_common])));;

(*** After the loop over w2 at 0x6f98, the entries of the symbol k done ***)

let rd2_w2exit =
  with_memsafe rd2_rr rd2_wr
   (rd2_expand(mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6f98)`; rd2_symregs;
      `read X18 s = word st /\ read X20 s = word_add wk (word(bgn + k))`;
      rd2_locals; rd2_wkmem; rd2_prefix `st + 2 EXP r`; rd2_common])));;

(*** The prefill of the entries of the symbol k whose second symbol does ***)
(*** not fit, from 0x6ee0 to 0x6f60                                     ***)

let rd2_prefill_goal = mk_rd2_goal [`w:num`; `k:num`]
  (list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ 2 * ml + 2 <= tl + w + mw /\ k < huf_rank ws w`])
  rd2_syminv
  (rd2_expand(subst [`MAX 1 ((2 * ml + 2) - (w + tl))`,`w2:num`] rd2_w2inv));;

(*** Facts about the symbol k of the weight w: its entries st..st + L,  ***)
(*** the symbol s1 and its byte among the sorted symbols                ***)

let RD2_SYMBOL_FACTS_TAC =
  SUBGOAL_THEN `k * L + L <= huf_rank ws w * L` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k * L + L = (k + 1) * L`; LE_MULT_RCANCEL] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `k:num`] HUF_SORTED_BUCKET) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `huf_bstart ws w + k`] HUF_SORTED) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `EL (huf_bstart ws w - huf_rank ws 0 + k) sl =
    word(huf_sorted ws (huf_bstart ws w + k)):byte`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `EL k:byte list->byte` o
      (fun th -> MP (SPEC `w:num` th)
                    (CONJ (ASSUME `1 <= w`) (ASSUME `w <= mw`))) o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `huf_wsyms`)) (concl th))) THEN
    REWRITE_TAC[huf_wsyms] THEN
    W(fun (asl,w) -> MP_TAC(ISPECL [`sl:byte list`;
       `huf_bstart ws w - huf_rank ws 0`; `huf_rank ws w`; `k:num`]
       EL_SUB_LIST)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `uu + k * L + L <= tt` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `st = uu + k * L` THEN
  SUBGOAL_THEN `st + L <= dsz` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC];;

(*** The entries of a prefill: L copies, and the first n of them ***)

let FW_REP_BOUND = prove
 (`!n e. e < 2 EXP 32 ==> fw_rep n e < 2 EXP (32 * n)`,
  INDUCT_TAC THEN REWRITE_TAC[FW_REP_CLAUSES; FW_REP_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `32 * SUC n = 32 * n + 32`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[EXP_ADD] THEN
  SUBGOAL_THEN `2 EXP (32 * n) * e <= 2 EXP (32 * n) * (2 EXP 32 - 1)`
  MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
  MP_TAC(SPECL [`2`; `32 * n`] EXP_EQ_0) THEN REWRITE_TAC[ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let FW_REP_TRUNC = prove
 (`!m n e. n <= m /\ e < 2 EXP 32
           ==> fw_rep m e MOD 2 EXP (32 * n) = fw_rep n e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m = n + (m - n)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[FW_REP_ADD]] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `fw_rep (m - n) e` THEN
  ASM_SIMP_TAC[FW_REP_BOUND] THEN ARITH_TAC);;

let READ_MEMORY_FW_REP_PREFIX = prove
 (`!a:int64 m n e s:armstate.
        read (memory :> bytes(a,4 * m)) s = fw_rep m e /\ n <= m /\
        e < 2 EXP 32
        ==> read (memory :> bytes(a,4 * n)) s = fw_rep n e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `4 * m`; `4 * n`; `read memory s`]
    READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * n = 32 * n`] THEN
  SUBGOAL_THEN `MIN (4 * m) (4 * n) = 4 * n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC FW_REP_TRUNC THEN ASM_REWRITE_TAC[]);;

let READ_MEMORY_FW_REP_STORE128 = prove
 (`!a:int64 v:int128 e s:armstate.
        read (memory :> bytes128 a) s = v /\ val v = fw_rep 4 e
        ==> read (memory :> bytes(a,4 * 4)) s = fw_rep 4 e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_MEMORY_BYTES128]);;

let FW_E1_LEMMA = prove
 (`!s1 nb. s1 < 256
           ==> s1 + 16777216 + 65536 * nb = fw_entry 1 nb 0 (word s1:byte)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fw_entry; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let FW_Q0_VAL = prove
 (`!e. e < 2 EXP 32
       ==> val(word_join (word(e + 4294967296 * e):int64)
                         (word(e + 4294967296 * e):int64):int128) =
           fw_rep 4 e`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  ASM_SIMP_TAC[FW_VAL_REP2] THEN
  REWRITE_TAC[ARITH_RULE `4 = 2 + 2`; FW_REP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** The prefix of the table extended by the first n of m copies of the ***)
(*** one-symbol entry e stored after it                                  ***)

let READ_MEMORY_PREFILL_EXTEND = prove
 (`!a:int64 l st m n e lv nb b x s:armstate.
        4 * (st + n) <= LENGTH l /\ n <= m /\ e < 2 EXP 32 /\
        fw_entry lv nb b x = e /\
        SUB_LIST(4 * st,4 * n * 1) l = fw_block n lv nb b [x] /\
        read (memory :> bytes(a,4 * st)) s =
        num_of_bytelist(SUB_LIST(0,4 * st) l) /\
        read (memory :> bytes(word_add a (word(4 * st)),4 * m)) s =
        fw_rep m e
        ==> read (memory :> bytes(a,4 * (st + n))) s =
            num_of_bytelist(SUB_LIST(0,4 * (st + n)) l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC READ_MEMORY_BYTELIST_EXTEND THEN
  ASM_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:num`; `lv:num`; `nb:num`; `b:num`; `x:byte`]
    NUM_OF_FW_BLOCK1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC READ_MEMORY_FW_REP_PREFIX THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]);;

(*** The entries of a 32-byte store of q0 after 8 * i of them ***)

let READ_MEMORY_FW_REP_STP128 = prove
 (`!a:int64 i e s:armstate.
        e < 2 EXP 32 /\
        read (memory :> bytes(a,32 * i)) s = fw_rep (8 * i) e /\
        read (memory :> bytes128(word_add a (word(32 * i)))) s =
        word_join (word(e + 4294967296 * e):int64)
                  (word(e + 4294967296 * e):int64) /\
        read (memory :> bytes128(word_add a (word(32 * i + 16)))) s =
        word_join (word(e + 4294967296 * e):int64)
                  (word(e + 4294967296 * e):int64)
        ==> read (memory :> bytes(a,32 * (i + 1))) s =
            fw_rep (8 * (i + 1)) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `e:num` FW_Q0_VAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`word_add a (word(32 * i)):int64`;
                 `word_join (word(e + 4294967296 * e):int64)
                            (word(e + 4294967296 * e):int64):int128`;
                 `e:num`; `s:armstate`] READ_MEMORY_FW_REP_STORE128) THEN
  MP_TAC(ISPECL [`word_add a (word(32 * i + 16)):int64`;
                 `word_join (word(e + 4294967296 * e):int64)
                            (word(e + 4294967296 * e):int64):int128`;
                 `e:num`; `s:armstate`] READ_MEMORY_FW_REP_STORE128) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 16 + 16`;
              ARITH_RULE `8 * (i + 1) = 8 * i + 4 + 4`;
              READ_BYTES_COMBINE; FW_REP_ADD; WORD_ADD_ASSOC_NUM] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * 32 * i = 32 * 8 * i`]);;

(*** The prefill loop at 0x6f38 of n 32-byte stores of q0 at a ***)

let rd2_pfinv = with_memsafe_loop `[a:int64,32 * n]` `[a:int64,32 * n]`
 `\i s.
  (read X0 s = word_add a (word(32 * i)) /\
   read X1 s = word_add a (word(32 * n)) /\
   read Q0 s = word_join (word(e1 + 4294967296 * e1):int64)
                         (word(e1 + 4294967296 * e1):int64) /\
   read (memory :> bytes(a,32 * i)) s = fw_rep (8 * i) e1) /\
  (read ZF s <=> i = n)`;;

let rd2_pfloop_goal =
 `!pc (a:int64) n e1 e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     0 < n /\ n <= 512 /\ e1 < 2 EXP 32 /\
     nonoverlapping (a,32 * n) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6f38) /\
               read X0 s = a /\ read X1 s = word_add a (word(32 * n)) /\
               read Q0 s = word_join (word(e1 + 4294967296 * e1):int64)
                                     (word(e1 + 4294967296 * e1):int64) /\
               read events s = e)
          (\s. read PC s = word(pc + 0x6f48) /\
               read (memory :> bytes(a,4 * (8 * n))) s = fw_rep (8 * n) e1 /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [a,32 * n] [a,32 * n]))
          (MAYCHANGE [PC; X0] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,32 * n)])`;;

let RD2_PFLOOP = prove
 (rd2_pfloop_goal,
  REWRITE_TAC[GSYM puff_memsafe; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_PUP_TAC `n:num` `pc + 0x6f38` `pc + 0x6f44` rd2_pfinv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    PUFF_INIT_TAC "s0" THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; FW_REP_CLAUSES;
                    READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    RD2_STEPS_TAC (1--3) THEN PTR_DECIDE_FLAGS_TAC THEN
    MP_TAC(ISPECL [`a:int64`; `i:num`; `e1:num`; `s3:armstate`]
      READ_MEMORY_FW_REP_STP128) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `4 * 8 * n = 32 * n`]]);;

(*** The number of 32-byte stores for skip entries, ceil(skip / 8) ***)

let PREFILL_COUNT_LEMMA = prove
 (`!skip L8. 0 < skip /\ skip <= 8 * L8
             ==> skip <= 8 * ((skip - 1) DIV 8 + 1) /\
                 8 * ((skip - 1) DIV 8 + 1) <= 8 * L8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`skip - 1`; `8`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = (skip - 1) DIV 8` THEN
  ABBREV_TAC `rr = (skip - 1) MOD 8` THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < L8` MP_TAC THENL
   [SUBGOAL_THEN `8 * q < 8 * L8` MP_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC];
    ASM_ARITH_TAC]);;

(*** After the m entries e1 are stored at st (skip <= m), the prefix of ***)
(*** the table to st + skip, in the state s                              ***)

let RD2_PREFILL_EXTEND_TAC m s =
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`; `k:num`;
                `(2 * ml + 2) - (w + tl)`; `(ml + 1) - w`;
                `(tl + w) - (ml + 1)`] HUF_DTABLE2_PREFILL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `v:num` THEN STRIP_TAC) THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> W(fun (asl,_) ->
    ASSUME_TAC(REWRITE_RULE (ASSUME `uu + k * L = st` ::
      map (rd2_hidden asl)
       [`2 EXP (tl - ml) = sc`; `huf_ustart ws w * sc = uu`;
        `2 EXP ((tl + w) - (ml + 1)) = L`;
        `huf_rv ws ml ((tl + w) - (ml + 1)) ((2 * ml + 2) - (w + tl)) =
         skip`]) th))) THEN
  MP_TAC(ISPECL [`word_add dtable (word 4):int64`; `huf_dtable2 ws ml tl`;
                 `st:num`; m; `skip:num`; `e1:num`; `1`; `(ml + 1) - w`;
                 `0`; `word(huf_sorted ws (huf_bstart ws w + k)):byte`;
                 s] READ_MEMORY_PREFILL_EXTEND) THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM; LENGTH_HUF_DTABLE2] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  W(fun (asl,w) -> REWRITE_TAC (map (rd2_hidden asl)
    [`2 EXP tl = tt`;
     `fw_entry 1 ((ml + 1) - w) 0
       (word (huf_sorted ws (huf_bstart ws w + k))) = e1`])) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** The prefill case: minW = 2ml + 2 - (w + tl) > 1, the start of minW ***)
(*** skip and the entry e1, up to the branch on r = 1 at step 12        ***)

let RD2_PREFILL_START_TAC =
  SUBGOAL_THEN `MAX 1 ((2 * ml + 2) - (w + tl)) = (2 * ml + 2) - (w + tl)`
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[MAX] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RD2_WK32_TAC `52 * ((ml + 1) - w) + 4 * ((2 * ml + 2) - (w + tl))`
    `13 * ((ml + 1) - w) + ((2 * ml + 2) - (w + tl))` `s0:armstate` THEN
  RD2_WKV_TAC THEN RD2_STEPS_TAC (1--5) THEN
  SUBGOAL_THEN `tl - ((ml + 1) - w) = (tl + w) - (ml + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `(tl + w) - (ml + 1)`;
                `(2 * ml + 2) - (w + tl)`; `ml + 1`] HUF_RV_MONO) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `(tl + w) - (ml + 1)`; `ml:num`]
    HUF_RV_ALL) THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) -> REWRITE_TAC
    [rd2_hidden asl `2 EXP ((tl + w) - (ml + 1)) = L`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[huf_complete; HUF_COMPLETE_ALL_LE]; ALL_TAC] THEN
  DISCH_TAC THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  RD2_ABBREV_TAC
   `skip = huf_rv ws ml ((tl + w) - (ml + 1)) ((2 * ml + 2) - (w + tl))` THEN
  SUBGOAL_THEN `skip <= L` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RD2_STEPS_TAC (6--12) THEN
  MP_TAC(SPECL [`huf_sorted ws (huf_bstart ws w + k)`; `(ml + 1) - w`]
    FW_E1_LEMMA) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN
   `fw_entry 1 ((ml + 1) - w) 0
     (word (huf_sorted ws (huf_bstart ws w + k))) < 2 EXP 32`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FW_ENTRY_BOUND THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RD2_ABBREV_TAC
   `e1 = fw_entry 1 ((ml + 1) - w) 0
          (word (huf_sorted ws (huf_bstart ws w + k)))`;;

let RD2_L_EQ_TAC n =
  SUBGOAL_THEN (mk_eq(`L:num`,mk_small_numeral n)) ASSUME_TAC THENL
   [W(fun (asl,w) -> REWRITE_TAC
      [SYM(rd2_hidden asl `2 EXP ((tl + w) - (ml + 1)) = L`)]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(*** r = 1: one 8-byte store of two entries ***)

let RD2_PREFILL_R1_TAC =
  RD2_L_EQ_TAC 2 THEN
  ZSTD_DECIDE_BRANCH_TAC THEN RD2_STEPS_TAC (13--14) THEN
  MP_TAC(ISPECL [`word_add dtable (word (4 + 4 * st)):int64`;
                 `word (e1 + 4294967296 * e1):int64`; `e1:num`;
                 `s14:armstate`] READ_MEMORY_FW_REP_STORE64) THEN
  ASM_SIMP_TAC[FW_VAL_REP2] THEN DISCH_TAC THEN
  RD2_PREFILL_EXTEND_TAC `2` `s14:armstate` THEN
  RD2_STEPS_TAC (15--20) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  RD2_REGS_TAC;;

(*** r = 2: one 16-byte store of four entries ***)

let RD2_PREFILL_R2_TAC =
  RD2_L_EQ_TAC 4 THEN
  TRY ZSTD_DECIDE_BRANCH_TAC THEN RD2_STEPS_TAC (13--16) THEN
  MP_TAC(ISPECL [`word_add dtable (word (4 + 4 * st)):int64`;
                 `word_join (word (e1 + 4294967296 * e1):int64)
                    (word (e1 + 4294967296 * e1):int64):int128`; `e1:num`;
                 `s16:armstate`] READ_MEMORY_FW_REP_STORE128) THEN
  ASM_SIMP_TAC[FW_Q0_VAL] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  RD2_PREFILL_EXTEND_TAC `4` `s16:armstate` THEN
  RD2_STEPS_TAC (17--22) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  RD2_REGS_TAC;;

(*** r >= 3: none if skip = 0, else the loop of ceil(skip / 8) 32-byte ***)
(*** stores (L = 2^r is a multiple of 8)                               ***)

let RD2_PREFILL_R3_TAC =
  SUBGOAL_THEN `3 <= (tl + w) - (ml + 1)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?L8. L = 8 * L8` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `2 EXP ((tl + w) - (ml + 1) - 3)` THEN
    W(fun (asl,w) -> REWRITE_TAC[SYM(rd2_hidden asl
      `2 EXP ((tl + w) - (ml + 1)) = L`)]) THEN
    REWRITE_TAC[ARITH_RULE `8 = 2 EXP 3`; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `skip = 0` THENL
   [ZSTD_DECIDE_BRANCH_TAC THEN RD2_STEPS_TAC (13--22) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN RD2_REGS_TAC;
    ALL_TAC] THEN
  ZSTD_DECIDE_BRANCH_TAC THEN RD2_STEPS_TAC (13--22) THEN
  MP_TAC(SPECL [`skip:num`; `L8:num`] PREFILL_COUNT_LEMMA) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `n8 = (skip - 1) DIV 8 + 1` THEN
  RD2_SET_REG_TAC
   `read X1 s22 = word_add dtable (word ((4 + 4 * st) + 32 * n8))`
   (ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE) THEN
  SUBGOAL_THEN `st + 8 * n8 <= dsz /\ 0 < n8 /\ n8 <= 512`
  STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word_add dtable (word (4 + 4 * st)):int64`; `n8:num`;
    `e1:num`] RD2_PFLOOP))) THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s23" THEN
  EVENTS_UNABBREV_TAC THEN
  RD2_PREFILL_EXTEND_TAC `8 * n8` `s23:armstate` THEN
  RD2_STEPS_TAC (24--29) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  RD2_REGS_TAC;;

(*** No prefill: minW = 1 and the start of weight 1 is 0 ***)

let RD2_NOPREFILL_TAC =
  SUBGOAL_THEN `MAX 1 ((2 * ml + 2) - (w + tl)) = 1`
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[MAX] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RD2_STEPS_TAC (1--5) THEN
  MP_TAC(SPECL [`2 * ml + 2`; `w + tl`; `1`] WORD_CMP_32_SUB_SFLAGS) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ZSTD_DECIDE_BRANCH_TAC THEN RD2_STEPS_TAC (6--11) THEN
  PUFF_FINAL_TAC THEN
  ASM_REWRITE_TAC[huf_rv; HUF_START_1; MULT_CLAUSES; DIV_0; ADD_CLAUSES] THEN
  RD2_REGS_TAC;;

let RD2_PREFILL = prove
 (rd2_prefill_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD2_WEIGHT_FACTS_TAC THEN
  RD2_SYMBOL_FACTS_TAC THEN
  MP_TAC(ISPECL [`word_add wk (word 736):int64`; `sl:byte list`;
                 `huf_bstart ws w - huf_rank ws 0 + k`; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `736 + huf_bstart ws w - huf_rank ws 0 + k =
                (huf_bstart ws w - huf_rank ws 0 + k) + 736`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `w + tl + 1 < 2 * ml + 2` THENL
   [ALL_TAC; RD2_NOPREFILL_TAC] THEN
  RD2_PREFILL_START_TAC THEN
  ASM_CASES_TAC `(tl + w) - (ml + 1) = 1` THENL
   [RD2_PREFILL_R1_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(tl + w) - (ml + 1) = 2` THENL
   [RD2_PREFILL_R2_TAC; RD2_PREFILL_R3_TAC]);;

(*** At 0x6fb0, after the loop over the symbols of the weight w (level 2) ***)

let rd2_symdone =
  with_memsafe rd2_rr rd2_wr
   (rd2_expand(mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6fb0)`; rd2_symregs; rd2_locals; rd2_wkmem;
      rd2_prefix `U + huf_rank ws w * 2 EXP r`; rd2_common])));;

(*** After the symbol k: the next symbol or the end of the loop ***)

let rd2_symnext =
  let inv1 = rhs(concl(BETA_CONV(mk_comb(subst [`k + 1`,`k:num`] rd2_syminv,
                                         `s:armstate`)))) in
  mk_abs(`s:armstate`,
    mk_disj(mk_conj(`k + 1 < huf_rank ws w`,inv1),
            mk_conj(`k + 1 = huf_rank ws w`,
                    rhs(concl(BETA_CONV(mk_comb(rd2_symdone,
                                                `s:armstate`)))))));;

let rd2_sym_hyps =
  list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ 2 * ml + 2 <= tl + w + mw /\ k < huf_rank ws w`];;

(*** The end of the entries of the symbol k, 0x6f98 to 0x6fac ***)

let rd2_symtail_goal = mk_rd2_goal [`w:num`; `k:num`]
  rd2_sym_hyps rd2_w2exit rd2_symnext;;

let RD2_SYMTAIL = prove
 (rd2_symtail_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD2_WEIGHT_FACTS_TAC THEN
  RD2_SYMBOL_FACTS_TAC THEN
  SUBGOAL_THEN `uu + (k + 1) * L = st + L` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k + 1 < huf_rank ws w` THENL
   [RD2_STEPS_TAC (1--6) THEN
    SUBGOAL_THEN `~(k + 1 = huf_rank ws w)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN RD2_REGS_TAC;
    SUBGOAL_THEN `huf_rank ws w = k + 1` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    RD2_STEPS_TAC (1--6) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[LT_REFL] THEN RD2_REGS_TAC]);;

(*** The end of a weight w (level 2), 0x6fb0 to the next weight or 6fdc ***)

let rd2_wtail2_goal = mk_rd2_goal [`w:num`]
  (list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ 2 * ml + 2 <= tl + w + mw`])
  rd2_symdone rd2_wnext;;

let RD2_WTAIL2 = prove
 (rd2_wtail2_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD2_WEIGHT_FACTS_TAC THEN
  ASM_CASES_TAC `w:num = mw` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `w:num = mw`)) THEN
    RD2_STEPS_TAC (1--11) THEN
    SUBGOAL_THEN `uu + huf_rank ws mw * L = tt`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    RD2_STEPS_TAC (1--11) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    RD2_REGS_TAC]);;

(*** The start of a weight w (level 2), 0x6e44 to the symbol loop at k = 0 ***)
(*** if it has symbols, and to the next weight (or 6fdc) otherwise        ***)

let rd2_syminv0 = subst [`0`,`k:num`] rd2_syminv;;

let rd2_w2start_goal = mk_rd2_goal [`w:num`]
  (list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ 2 * ml + 2 <= tl + w + mw /\
     ~(huf_rank ws w = 0)`])
  rd2_winv rd2_syminv0;;

let rd2_w2empty_goal = mk_rd2_goal [`w:num`]
  (list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ 2 * ml + 2 <= tl + w + mw /\
     huf_rank ws w = 0`])
  rd2_winv rd2_wnext;;

(*** The shift 1 << (r & 31) and r & 31 for r < 31 ***)

let RD2_WORD_SHIFT1 = prove
 (`!r. r < 31
       ==> word_and (word r) (word 31):int32 = word r /\
           word_zx (word_jshl (word 1) (word_and (word r) (word 31)):int32):
             int64 = word(2 EXP r) /\
           word_zx(word_and (word r) (word 31):int32):int64 = word r`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_and (word r) (word 31):int32 = word r` ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_AND_31_SMALL THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[word_jshl; VAL_WORD; DIMINDEX_32] THEN
    SUBGOAL_THEN `(r MOD 2 EXP 32) MOD 32 = r` SUBST1_TAC THENL
     [SIMP_TAC[MOD_LT; ARITH_RULE `r < 31 ==> r < 2 EXP 32`;
               ASSUME `r < 31`] THEN
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[WORD_SHL_WORD; MULT_CLAUSES] THEN
    MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONJ_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 31` THEN
    REWRITE_TAC[LT_EXP; LE_EXP] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC]);;

(*** The stores to the frame as stores to the region of 528 bytes below ***)
(*** the stack pointer, for the frame subsumption                         ***)

let RD2_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 208):int64 =
  word_add (word_sub stackpointer (word 528)) (word 320)`;;

let RD2_FRAME_REBASE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE[RD2_STACK_REBASE; WORD_ADD_ASSOC_NUM] th)
    else th);;

(*** From the test of the empty weight at step 14 to the symbol loop, with ***)
(*** maxth the value of minW                                              ***)

let RD2_W2START_TAIL_TAC maxth =
  RD2_STEPS_TAC (12--14) THEN
  MP_TAC(SPEC `(tl + w) - (ml + 1)` RD2_WORD_SHIFT1) THEN
  ANTS_TAC THENL
   [SIMPLE_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  RD2_FOLD_TAC [`2 EXP ((tl + w) - (ml + 1)) = L`] THEN
  RD2_STEPS_TAC (15--39) THEN
  RD2_SET_REG_TAC
   `read (memory :> bytes64 (word_add (word_sub stackpointer (word 208))
                                      (word 120))) s39 =
    word_add wk (word (huf_bstart ws (w + 1) - huf_rank ws 0))`
   (ASM_REWRITE_TAC[] THEN
    W(fun (asl,g) ->
      let a = rand(lhand(lhs g)) in
      TRANS_TAC EQ_TRANS
       (subst[a,`a:num`] `word_add wk (word (a + 1)):int64`) THEN
      CONJ_TAC THENL
       [SPEC_TAC(a,`a:num`) THEN CONV_TAC WORD_RULE;
        AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC])) THEN
  SUBGOAL_THEN maxth (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[MAX] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RD2_FRAME_REBASE_TAC THEN
  PUFF_FINAL_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN RD2_REGS_TAC;;

let RD2_W2START = prove
 (rd2_w2start_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD2_WEIGHT_FACTS_TAC THEN
  RD2_WEIGHT_READS_TAC THEN ASM_CASES_TAC `w + tl < 2 * ml + 2` THEN
  RD2_STEPS_TAC (1--11) THENL
   [RD2_SET_REG_TAC `read X11 s11 = word ((2 * ml + 2) - (w + tl))`
     (ASM_REWRITE_TAC[SUB_0] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `ival(word((2 * ml + 2) - (w + tl)):int32) =
                    &((2 * ml + 2) - (w + tl))` SUBST1_TAC THENL
       [MATCH_MP_TAC IVAL_WORD_SMALL THEN REWRITE_TAC[DIMINDEX_32] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[INT_OF_NUM_LT; LT] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC) THEN
    RD2_W2START_TAIL_TAC
     `MAX 1 ((2 * ml + 2) - (w + tl)) = (2 * ml + 2) - (w + tl)`;
    RD2_SET_REG_TAC `read X11 s11 = word 1`
     (ASM_REWRITE_TAC[WORD_SUB_0; INT_SUB_RZERO; ADD_CLAUSES] THEN
      COND_CASES_TAC THENL
       [POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
        SIMPLE_ARITH_TAC;
        CONV_TAC WORD_REDUCE_CONV]) THEN
    RD2_W2START_TAIL_TAC `MAX 1 ((2 * ml + 2) - (w + tl)) = 1`]);;

let RD2_W2EMPTY = prove
 (rd2_w2empty_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  RD2_HIDE_TAC `huf_rank ws w = 0` THEN RD2_WEIGHT_FACTS_TAC THEN
  RD2_UNHIDE_TAC `huf_rank ws w = 0` THEN RD2_WEIGHT_READS_TAC THEN
  ASM_CASES_TAC `w:num = mw` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `w:num = mw`)) THEN
    UNDISCH_TAC `huf_rank ws mw = 0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RD2_STEPS_TAC (1--22) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  RD2_REGS_TAC);;

(*** At 0x6da8, after the rows of rankVal: the start of the fill ***)

let rd2_rowsdone =
  with_memsafe rd2_rr rd2_wr
   (mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6da8)`;
      `read X5 s = word(ml + 1) /\ read X12 s = word ml /\
       read X14 s = word mw /\ read X15 s = word tl /\
       read X19 s = word tl /\ read X20 s = wk /\ read X23 s = dtable /\
       read X25 s = word_zx(dtd:int32) /\ read X27 s = word((ml + 1) - mw) /\
       read X28 s = word h`;
      rd2_wkmem; rd2_common]));;

let rd2_winv1 = subst [`1`,`w:num`] rd2_winv;;

let rd2_fstart_goal = mk_rd2_goal []
  (list_mk_conj [rd2_hyps; rd2_facts]) rd2_rowsdone rd2_winv1;;

let RD2_FSTART = prove
 (rd2_fstart_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--23) THEN
  RD2_FRAME_REBASE_TAC THEN PUFF_FINAL_TAC THEN
  REWRITE_TAC[HUF_START_1; MULT_CLAUSES; SUB_LIST_CLAUSES; num_of_bytelist;
              READ_MEMORY_BYTES_0] THEN
  ASM_REWRITE_TAC[] THEN RD2_REGS_TAC);;

(* ------------------------------------------------------------------------- *)
(* rankVal: the rows from its row 0 (RD2_ROWS_LOOP at 0x6d5c and             *)
(* RD2_ROWS_PIECE), row 0 (RD2_RV0_LOOP at 0x6d24 and RD2_RV0_PIECE), and    *)
(* the workspace as one number for the fill (rd2_wkv).                       *)
(* ------------------------------------------------------------------------- *)

(*** The rankVal array of 156 words (rows of 13) while the rows mb.. are ***)
(*** filled: the rows below c and the words below w of row c done, word  ***)
(*** j of row i (1 <= j <= mw) being word j of row 0 shifted right by i  ***)

let rd2_rows = new_definition
 `rd2_rows (rv:int32 list) mb mw c w =
    list_of_seq
     (\i. if mb <= i DIV 13 /\
             (i DIV 13 < c \/ i DIV 13 = c /\ i MOD 13 < w) /\
             1 <= i MOD 13 /\ i MOD 13 <= mw
          then word_ushr (EL (i MOD 13) rv) (i DIV 13) else EL i rv) 156`;;

let LENGTH_RD2_ROWS = prove
 (`!rv mb mw c w. LENGTH(rd2_rows rv mb mw c w) = 156`,
  REWRITE_TAC[rd2_rows; LENGTH_LIST_OF_SEQ]);;

let EL_RD2_ROWS = prove
 (`!rv mb mw c w i.
        i < 156
        ==> EL i (rd2_rows rv mb mw c w) =
            if mb <= i DIV 13 /\
               (i DIV 13 < c \/ i DIV 13 = c /\ i MOD 13 < w) /\
               1 <= i MOD 13 /\ i MOD 13 <= mw
            then word_ushr (EL (i MOD 13) rv) (i DIV 13) else EL i rv`,
  SIMP_TAC[rd2_rows; EL_LIST_OF_SEQ]);;

let RD2_ROWS_COND_TAC =
  REWRITE_TAC[rd2_rows] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

let RD2_ROWS_START = prove
 (`!rv mb mw. LENGTH rv = 156 ==> rd2_rows rv mb mw mb 0 = rv`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_RD2_ROWS] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_RD2_ROWS] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RD2_ROWS_W1 = prove
 (`!rv mb mw c. rd2_rows rv mb mw c 1 = rd2_rows rv mb mw c 0`,
  REPEAT GEN_TAC THEN RD2_ROWS_COND_TAC);;

let RD2_ROWS_NEXT = prove
 (`!rv mb mw c. rd2_rows rv mb mw c (mw + 1) = rd2_rows rv mb mw (c + 1) 0`,
  REPEAT GEN_TAC THEN RD2_ROWS_COND_TAC);;

let RD2_ROWS_ROW0 = prove
 (`!rv mb mw c w j.
        1 <= mb /\ j < 13 ==> EL j (rd2_rows rv mb mw c w) = EL j rv`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_RD2_ROWS; ARITH_RULE `j < 13 ==> j < 156`] THEN
  ASM_SIMP_TAC[DIV_LT] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let RD2_ROWS_STEP = prove
 (`!rv mb mw c w i.
        1 <= mb /\ mb <= c /\ 1 <= w /\ w <= mw /\ w < 13 /\ i < 156
        ==> EL i (rd2_rows rv mb mw c (w + 1)) =
            if i = 13 * c + w then word_ushr (EL w rv) c
            else EL i (rd2_rows rv mb mw c w)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_RD2_ROWS] THEN
  ASM_CASES_TAC `i = 13 * c + w` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(13 * c + w) DIV 13 = c /\ (13 * c + w) MOD 13 = w`
     (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[LT_REFL; ARITH_RULE `w < w + 1`];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`i:num`; `13`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `~(i = 13 * c + w)` THEN
    SPEC_TAC(`i DIV 13`,`q:num`) THEN SPEC_TAC(`i MOD 13`,`r:num`) THEN
    ARITH_TAC]);;

let RD2_ROWS_FINAL = prove
 (`!rv mb mw ce c w.
        mb <= c /\ c < ce /\ c < 12 /\ 1 <= w /\ w <= mw /\ w < 13
        ==> EL (13 * c + w) (rd2_rows rv mb mw ce 0) =
            word_ushr (EL w rv) c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `13 * c + w < 156` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_RD2_ROWS]] THEN
  SUBGOAL_THEN `(13 * c + w) DIV 13 = c /\ (13 * c + w) MOD 13 = w`
   (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(*** The loop over the rows at 0x6d5c, rows mb..ce - 1 of rankVal from ***)
(*** row 0 (rankVal0), a lemma with a frame of its own                  ***)

let rd2_rows_oinv = with_memsafe_loop `[wk:int64,624]` `[wk:int64,624]`
 `\i s.
  (read X2 s = word(mb + i) /\
   read X3 s = word_add wk (word(52 * (mb + i))) /\
   read X4 s = word(mw + 1) /\ read X6 s = word ce /\ read X20 s = wk /\
   read (memory :> bytes(wk,624)) s =
   num_of_wordlist(rd2_rows rv mb mw (mb + i) 0)) /\
  (read ZF s <=> mb + i = ce)`;;

let rd2_rows_iinv = with_memsafe_loop `[wk:int64,624]` `[wk:int64,624]`
 `\j s.
  (read X0 s = word(j + 1) /\ read X2 s = word(mb + i) /\
   read X3 s = word_add wk (word(52 * (mb + i))) /\
   read X4 s = word(mw + 1) /\ read X6 s = word ce /\ read X20 s = wk /\
   read (memory :> bytes(wk,624)) s =
   num_of_wordlist(rd2_rows rv mb mw (mb + i) (j + 1))) /\
  (read CF s /\ (read ZF s <=> j = mw))`;;

let rd2_rows_goal =
 `!pc (wk:int64) rv mb ce mw e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     1 <= mb /\ mb <= 12 /\ ce <= 12 /\ 1 <= mw /\ mw <= 12 /\
     LENGTH rv = 156 /\
     nonoverlapping (wk,624) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6d5c) /\
               read X20 s = wk /\ read X27 s = word mb /\
               read X6 s = word ce /\ read X4 s = word(mw + 1) /\
               read (memory :> bytes(wk,624)) s = num_of_wordlist rv /\
               read events s = e)
          (\s. read PC s = word(pc + 0x6da8) /\
               read (memory :> bytes(wk,624)) s =
               num_of_wordlist(rd2_rows rv mb mw (MAX mb ce) 0) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [wk,624] [wk,624]))
          (MAYCHANGE [PC; X0; X1; X2; X3] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(wk,624)])`;;

let RD2_JUSHR = prove
 (`!x:int32 n. n < 32 ==> word_jushr x (word n) = word_ushr x n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jushr; DIMINDEX_32; VAL_WORD] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 32 ==> n < 4294967296`]);;

(*** The word j + 1 of row mb + i: the load of word j + 1 of row 0, the ***)
(*** store and the update of the array                                   ***)

let RD2_ROWS_BODY_TAC =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`wk:int64`; `rd2_rows rv mb mw (mb + i) (j + 1)`; `156`;
                 `j + 1`; `s0:armstate`]
    READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_RD2_ROWS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`rv:int32 list`; `mb:num`; `mw:num`; `mb + i`; `j + 1`;
                 `j + 1`] RD2_ROWS_ROW0) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val (word (j + 1):int64) = j + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RD2_STEPS_TAC (1--2) THEN
  MP_TAC(ISPECL [`wk:int64`; `rd2_rows rv mb mw (mb + i) (j + 1)`;
                 `13 * (mb + i) + j + 1`; `s2:armstate`]
    READ_MEMORY_WORDLIST32_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_RD2_ROWS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 * (13 * c + j + 1) = 52 * c + 4 * (j + 1)`] THEN
  STRIP_TAC THEN RD2_STEPS_TAC (3--5) THEN W32_DECIDE_FLAGS_TAC THEN
  MP_TAC(ISPECL [`wk:int64`; `rd2_rows rv mb mw (mb + i) (j + 1)`;
                 `rd2_rows rv mb mw (mb + i) ((j + 1) + 1)`;
                 `13 * (mb + i) + j + 1`; `s5:armstate`]
    READ_MEMORY_WORDLIST32_UPDATE) THEN
  REWRITE_TAC[LENGTH_RD2_ROWS;
              ARITH_RULE `4 * (13 * c + j + 1) = 52 * c + 4 * (j + 1)`] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`rv:int32 list`; `mb:num`; `mw:num`; `mb + i`; `j + 1`;
                    `13 * (mb + i) + j + 1`] RD2_ROWS_STEP) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC RD2_JUSHR THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      X_GEN_TAC `t:num` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`rv:int32 list`; `mb:num`; `mw:num`; `mb + i`; `j + 1`;
                    `t:num`] RD2_ROWS_STEP) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[]];
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC] THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;;

let RD2_ROWS_LOOP = prove
 (rd2_rows_goal,
  REWRITE_TAC[GSYM puff_memsafe; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `ce <= mb` THENL
   [SUBGOAL_THEN `MAX mb ce = mb` SUBST1_TAC THENL
     [REWRITE_TAC[MAX] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RD2_ROWS_START] THEN
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--2) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAX mb ce = mb + (ce - mb)` SUBST1_TAC THENL
   [REWRITE_TAC[MAX] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `ce - mb` `pc + 0x6d78` `pc + 0x6da4`
    rd2_rows_oinv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--7) THEN PUFF_FINAL_TAC THEN
    ASM_SIMP_TAC[ADD_CLAUSES; RD2_ROWS_START] THEN CONV_TAC WORD_RULE;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_WHILE_PUP_TAC `mw:num` `pc + 0x6d80` `pc + 0x6d94`
      rd2_rows_iinv THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--2) THEN PUFF_FINAL_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; RD2_ROWS_W1];
      RD2_ROWS_BODY_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
      RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
      PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--4) THEN
      W32_DECIDE_FLAGS_TAC THEN PUFF_FINAL_TAC THEN
      ASM_REWRITE_TAC[RD2_ROWS_NEXT; GSYM ADD_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[]]);;

(*** The workspace before the rows: rankVal (156 words, rvl), rankStats, ***)
(*** a zero word and rankStart (14 words, rsl), and the sorted symbols   ***)

let rd2_wkparts =
 `read (memory :> bytes(wk,624)) s = num_of_wordlist (rvl:int32 list) /\
  read (memory :> bytes(word_add wk (word 624),52)) s =
  num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) 13) /\
  read (memory :> bytes32(word_add wk (word 676))) s = word 0 /\
  read (memory :> bytes(word_add wk (word 680),56)) s =
  num_of_wordlist (rsl:int32 list) /\
  read (memory :> bytes(word_add wk (word 736),256)) s = num_of_bytelist sl`;;

let rd2_wkparts_facts =
 `LENGTH (rvl:int32 list) = 156 /\
  (!w. 1 <= w /\ w <= mw
       ==> EL w rvl = word(huf_ustart ws w * 2 EXP (tl - ml))) /\
  LENGTH (rsl:int32 list) = 14 /\
  (!k. k <= mw ==> EL k rsl = word(huf_bstart ws (k + 1) - huf_rank ws 0))`;;

(*** The workspace after the rows as one number ***)

let rd2_wkv = new_definition
 `rd2_wkv ws ml tl mw (rvl:int32 list) (rsl:int32 list) =
    num_of_wordlist
     (APPEND (rd2_rows rvl ((ml + 1) - mw) mw
               (MAX ((ml + 1) - mw) ((tl + mw) - ml)) 0)
      (APPEND (list_of_seq (\j. word(huf_rank ws j):int32) 13)
       (APPEND [word 0] rsl)))`;;

(*** At 0x6d5c, after rankVal0 ***)

let rd2_rv0done =
  with_memsafe rd2_rr rd2_wr
   (mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6d5c)`;
      `read X4 s = word(mw + 1) /\ read X5 s = word(ml + 1) /\
       read X6 s = word((tl + mw) - ml) /\ read X12 s = word ml /\
       read X14 s = word mw /\ read X15 s = word tl /\
       read X19 s = word tl /\ read X20 s = wk /\ read X23 s = dtable /\
       read X25 s = word_zx(dtd:int32) /\ read X27 s = word((ml + 1) - mw) /\
       read X28 s = word h`;
      rd2_wkparts; rd2_common]));;

let rd2_rows_piece_goal = mk_rd2_goal [`rvl:int32 list`; `rsl:int32 list`]
  (list_mk_conj [rd2_hyps; subst [`rd2_wkv ws ml tl mw rvl rsl`,`wkv:num`]
                              rd2_facts; rd2_wkparts_facts])
  rd2_rv0done
  (subst [`rd2_wkv ws ml tl mw rvl rsl`,`wkv:num`] rd2_rowsdone);;

let READ_MEMORY_WORDLIST32_APPEND = prove
 (`!a:int64 (l1:int32 list) l2 s:armstate.
        read (memory :> bytes(a,4 * LENGTH l1)) s = num_of_wordlist l1 /\
        read (memory :> bytes(word_add a (word(4 * LENGTH l1)),
                              4 * LENGTH l2)) s = num_of_wordlist l2
        ==> read (memory :> bytes(a,4 * LENGTH l1 + 4 * LENGTH l2)) s =
            num_of_wordlist(APPEND l1 l2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND; DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `8 * 4 * n = 32 * n`]);;
(*** The parts of the workspace after the rows as the number rd2_wkv ***)

let RD2_WKV_COMBINE_TAC s =
  let rows = `rd2_rows rvl ((ml + 1) - mw) mw
                (MAX ((ml + 1) - mw) ((tl + mw) - ml)) 0`
  and ranks = `list_of_seq (\j. word(huf_rank ws j):int32) 13` in
  MP_TAC(ISPECL [`wk:int64`; rows; ranks; s]
    READ_MEMORY_WORDLIST32_APPEND) THEN
  REWRITE_TAC[LENGTH_RD2_ROWS; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`wk:int64`; list_mk_icomb "APPEND" [rows; ranks];
                 `word 0:int32`; s] READ_MEMORY_WORDLIST32_APPEND1) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_RD2_ROWS; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`wk:int64`;
    list_mk_icomb "APPEND" [list_mk_icomb "APPEND" [rows; ranks];
                            `[word 0:int32]`];
    `rsl:int32 list`; s] READ_MEMORY_WORDLIST32_APPEND) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_RD2_ROWS; LENGTH_LIST_OF_SEQ; LENGTH] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[GSYM rd2_wkv] THEN DISCH_TAC;;
let RD2_ROWS_PIECE = prove
 (rd2_rows_piece_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `wk:int64`; `rvl:int32 list`; `(ml + 1) - mw`;
    `(tl + mw) - ml`; `mw:num`] RD2_ROWS_LOOP))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s1" THEN
  EVENTS_UNABBREV_TAC THEN
  RD2_WKV_COMBINE_TAC `s1:armstate` THEN PUFF_FINAL_TAC THEN
  ASM_REWRITE_TAC[]);;

(*** The facts about the workspace number rd2_wkv for the fill ***)

let RD2_WKV_EL = prove
 (`!ws ml tl mw rvl rsl n.
        LENGTH(rvl:int32 list) = 156 /\ LENGTH(rsl:int32 list) = 14 /\
        n < 184
        ==> (rd2_wkv ws ml tl mw rvl rsl DIV 2 EXP (32 * n)) MOD 2 EXP 32 =
            val(EL n (APPEND (rd2_rows rvl ((ml + 1) - mw) mw
                               (MAX ((ml + 1) - mw) ((tl + mw) - ml)) 0)
                     (APPEND (list_of_seq (\j. word(huf_rank ws j):int32) 13)
                       (APPEND [word 0] rsl))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rd2_wkv; REWRITE_RULE[DIMINDEX_32]
   (INST_TYPE [`:32`,`:N`] NUM_OF_WORDLIST_EL)] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_RD2_ROWS; LENGTH_LIST_OF_SEQ;
                  LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let RD2_WKV_FACTS = prove
 (`!ws ml tl mw rvl rsl.
        huf_total ws = 2 EXP ml /\ ALL (\x. x <= mw) ws /\
        LENGTH ws <= 256 /\ 1 <= ml /\ ml <= tl /\ tl <= 12 /\
        1 <= mw /\ mw <= ml /\
        LENGTH (rvl:int32 list) = 156 /\
        (!w. 1 <= w /\ w <= mw
             ==> EL w rvl = word(huf_ustart ws w * 2 EXP (tl - ml))) /\
        LENGTH (rsl:int32 list) = 14 /\
        (!k. k <= mw
             ==> EL k rsl = word(huf_bstart ws (k + 1) - huf_rank ws 0))
        ==> (!w. 1 <= w /\ w <= mw
                 ==> (rd2_wkv ws ml tl mw rvl rsl DIV 2 EXP (32 * w))
                     MOD 2 EXP 32 =
                     huf_ustart ws w * 2 EXP (tl - ml)) /\
            (!c w. (ml + 1) - mw <= c /\ c + (ml + 1) - mw <= tl /\
                   1 <= w /\ w <= mw
                   ==> (rd2_wkv ws ml tl mw rvl rsl DIV
                        2 EXP (32 * (13 * c + w))) MOD 2 EXP 32 =
                       huf_rv ws ml (tl - c) w) /\
            (!k. k <= mw
                 ==> (rd2_wkv ws ml tl mw rvl rsl DIV
                      2 EXP (32 * (170 + k))) MOD 2 EXP 32 =
                     huf_bstart ws (k + 1) - huf_rank ws 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. w <= mw + 1
                    ==> huf_ustart ws w * 2 EXP (tl - ml) <= 2 EXP tl`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `mw:num`] HUF_U_ALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC HUF_USTART_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP tl <= 4096` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) RD2_WKV_EL (lhs w))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[EL_APPEND; LENGTH_RD2_ROWS; LENGTH_LIST_OF_SEQ; LENGTH;
              ARITH_RULE `SUC 0 = 1`] THENL
   [SUBGOAL_THEN `w < 156` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`rvl:int32 list`; `(ml + 1) - mw`; `mw:num`;
                   `MAX ((ml + 1) - mw) ((tl + mw) - ml)`; `0`; `w:num`]
      RD2_ROWS_ROW0) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LET_TRANS `2 EXP tl` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    SUBGOAL_THEN `13 * c + w < 156` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`rvl:int32 list`; `(ml + 1) - mw`; `mw:num`;
                   `MAX ((ml + 1) - mw) ((tl + mw) - ml)`; `c:num`; `w:num`]
      RD2_ROWS_FINAL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MAX] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_32] THEN
    SUBGOAL_THEN `huf_ustart ws w * 2 EXP (tl - ml) < 2 EXP 32`
     (fun th -> SIMP_TAC[th; MOD_LT]) THENL
     [TRANS_TAC LET_TRANS `2 EXP tl` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC HUF_RV_CODE THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(170 + k < 156) /\ ~((170 + k) - 156 < 13) /\
                  ~(((170 + k) - 156) - 13 < 1) /\
                  (((170 + k) - 156) - 13) - 1 = k`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`ws:num list`; `k + 1`] HUF_BSTART_LE) THEN
    ASM_ARITH_TAC]);;

(*** rankVal0, words 1..j of the rankVal array: the starts of the weights ***)
(*** in the table, the others as in rv                                    ***)

let rd2_rv0 = new_definition
 `rd2_rv0 (rv:int32 list) ws ml tl j =
    list_of_seq (\i. if 1 <= i /\ i <= j
                     then word(huf_ustart ws i * 2 EXP (tl - ml))
                     else EL i rv) 156`;;

let LENGTH_RD2_RV0 = prove
 (`!rv ws ml tl j. LENGTH(rd2_rv0 rv ws ml tl j) = 156`,
  REWRITE_TAC[rd2_rv0; LENGTH_LIST_OF_SEQ]);;

let EL_RD2_RV0 = prove
 (`!rv ws ml tl j i.
        i < 156
        ==> EL i (rd2_rv0 rv ws ml tl j) =
            if 1 <= i /\ i <= j then word(huf_ustart ws i * 2 EXP (tl - ml))
            else EL i rv`,
  SIMP_TAC[rd2_rv0; EL_LIST_OF_SEQ]);;

let RD2_RV0_0 = prove
 (`!rv ws ml tl. LENGTH rv = 156 ==> rd2_rv0 rv ws ml tl 0 = rv`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_RD2_RV0] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_RD2_RV0] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let RD2_RV0_STEP = prove
 (`!rv ws ml tl j i.
        i < 156
        ==> EL i (rd2_rv0 rv ws ml tl (j + 1)) =
            if i = j + 1 then word(huf_ustart ws (j + 1) * 2 EXP (tl - ml))
            else EL i (rd2_rv0 rv ws ml tl j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_RD2_RV0] THEN
  ASM_CASES_TAC `i = j + 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= j + 1`];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(*** The loop at 0x6d24 storing rankVal0[w] for w = 1..mw from rankStats ***)

let rd2_rv0_inv = with_memsafe_loop `[wk:int64,676]` `[wk:int64,624]`
 `\j s.
  (read X0 s = word((tl - ml) + j) /\
   read X2 s = word(huf_ustart ws (j + 1) * 2 EXP (tl - ml)) /\
   read X3 s = word_add wk (word(4 * (j + 1))) /\
   read X8 s = word((tl - ml) + mw) /\ read X20 s = wk /\
   read (memory :> bytes(wk,624)) s =
   num_of_wordlist(rd2_rv0 rv ws ml tl j) /\
   read (memory :> bytes(word_add wk (word 624),52)) s =
   num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) 13)) /\
  (read ZF s <=> j = mw)`;;

let rd2_rv0_goal =
 `!pc (wk:int64) rv ws ml tl mw e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     huf_total ws = 2 EXP ml /\ ALL (\x. x <= mw) ws /\ LENGTH ws <= 256 /\
     1 <= mw /\ mw <= ml /\ ml <= tl /\ tl <= 12 /\ LENGTH rv = 156 /\
     nonoverlapping (wk,676) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6d24) /\
               read X0 s = word(tl - ml) /\ read X4 s = word(mw + 1) /\
               read X20 s = wk /\
               read (memory :> bytes(wk,624)) s = num_of_wordlist rv /\
               read (memory :> bytes(word_add wk (word 624),52)) s =
               num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32)
                                           13) /\
               read events s = e)
          (\s. read PC s = word(pc + 0x6d5c) /\
               read (memory :> bytes(wk,624)) s =
               num_of_wordlist(rd2_rv0 rv ws ml tl mw) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [wk,676] [wk,624]))
          (MAYCHANGE [PC; X0; X1; X2; X3; X8] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(wk,624)])`;;

let RD2_RV0_ACC = prove
 (`!ws ml tl mw j.
        huf_total ws = 2 EXP ml /\ ALL (\x. x <= mw) ws /\ ml <= tl /\
        tl <= 12 /\ j + 1 <= mw
        ==> word_zx (word_add
                      (word_zx (word (huf_ustart ws (j + 1) *
                                      2 EXP (tl - ml)):int64):int32)
                      (word (2 EXP (tl - ml + j) * huf_rank ws (j + 1)))):
            int64 =
            word (huf_ustart ws ((j + 1) + 1) * 2 EXP (tl - ml)) /\
            word_zx (word (huf_ustart ws (j + 1) * 2 EXP (tl - ml)):int64):
            int32 =
            word (huf_ustart ws (j + 1) * 2 EXP (tl - ml))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `huf_ustart ws ((j + 1) + 1) * 2 EXP (tl - ml) <= 2 EXP tl`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `mw:num`] HUF_U_ALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC HUF_USTART_MONO THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `huf_ustart ws ((j + 1) + 1) * 2 EXP (tl - ml) =
    huf_ustart ws (j + 1) * 2 EXP (tl - ml) +
    2 EXP (tl - ml + j) * huf_rank ws (j + 1)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HUF_USTART_SUC] THEN
    SUBGOAL_THEN `2 EXP (j + 1) DIV 2 = 2 EXP j` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_1] THEN SIMP_TAC[DIV_MULT; ARITH_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[EXP_ADD] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP tl <= 4096` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_zx (word (huf_ustart ws (j + 1) * 2 EXP (tl - ml)):int64):int32 =
    word (huf_ustart ws (j + 1) * 2 EXP (tl - ml))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD]] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) then
    REWRITE_TAC[SYM th] else NO_TAC) THEN
  MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let RD2_RV0_LOOP = prove
 (rd2_rv0_goal,
  REWRITE_TAC[GSYM puff_memsafe; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_PUP_TAC `mw:num` `pc + 0x6d40` `pc + 0x6d58` rd2_rv0_inv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--7) THEN
    RD2_SET_REG_TAC `read X8 s7 = word ((tl - ml) + mw)`
     (ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `word_add (word_sub (word (tl - ml)) (word 1))
                             (word (mw + 1)):int32 = word ((tl - ml) + mw)`
      SUBST1_TAC THENL
       [SPEC_TAC(`tl - ml`,`a:num`) THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
      MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
      REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC) THEN
    PUFF_FINAL_TAC THEN
    ASM_SIMP_TAC[ADD_CLAUSES; RD2_RV0_0; HUF_START_1; MULT_CLAUSES];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    SUBGOAL_THEN `j + 1 < 13` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`word_add wk (word 624):int64`;
                   `list_of_seq (\j. word(huf_rank ws j):int32) 13`; `13`;
                   `j + 1`; `s0:armstate`]
      READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    REWRITE_TAC[WORD_ADD_ASSOC_NUM;
                ARITH_RULE `624 + 4 * (j + 1) = 4 * (j + 1) + 624`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`wk:int64`; `rd2_rv0 rv ws ml tl j`; `j + 1`;
                   `s0:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
    ASM_REWRITE_TAC[LENGTH_RD2_RV0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    RD2_STEPS_TAC (1--6) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `mw:num`; `j:num`]
      RD2_RV0_ACC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    W32_DECIDE_FLAGS_TAC THEN
    MP_TAC(ISPECL [`wk:int64`; `rd2_rv0 rv ws ml tl j`;
                   `rd2_rv0 rv ws ml tl (j + 1)`; `j + 1`; `s6:armstate`]
      READ_MEMORY_WORDLIST32_UPDATE) THEN
    REWRITE_TAC[LENGTH_RD2_RV0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[RD2_RV0_STEP; ARITH_RULE `j + 1 < 13 ==> j + 1 < 156`];
        ASM_ARITH_TAC;
        X_GEN_TAC `t:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[RD2_RV0_STEP]];
      DISCH_TAC] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(AP_TERM_TAC THEN TRY AP_TERM_TAC) THEN
    ARITH_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[]]);;

(*** At 0x6d1c, after the sort: rankStart[k] the end of the symbols of  ***)
(*** weight k (k >= 1), the symbols sorted                               ***)

let rd2_rs0 = new_definition
 `rd2_rs0 (rss:int32 list) =
    list_of_seq (\k. if k = 0 then word 0 else EL k rss) 14`;;

let LENGTH_RD2_RS0 = prove
 (`!rss. LENGTH(rd2_rs0 rss) = 14`,
  REWRITE_TAC[rd2_rs0; LENGTH_LIST_OF_SEQ]);;

let rd2_sortdone =
  with_memsafe rd2_rr rd2_wr
   (mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6d1c)`;
      `read X4 s = word(mw + 1) /\ read X5 s = word(ml + 1) /\
       read X6 s = word((tl + mw) - ml) /\ read X12 s = word ml /\
       read X14 s = word mw /\ read X15 s = word tl /\
       read X19 s = word tl /\ read X20 s = wk /\ read X23 s = dtable /\
       read X25 s = word_zx(dtd:int32) /\ read X27 s = word((ml + 1) - mw) /\
       read X28 s = word h`;
      subst [`rss:int32 list`,`rsl:int32 list`;
             `rv:int32 list`,`rvl:int32 list`] rd2_wkparts; rd2_common]));;

let rd2_sort_facts =
 `LENGTH (rv:int32 list) = 156 /\ LENGTH (rss:int32 list) = 14 /\
  (!k. 1 <= k /\ k <= mw
       ==> EL k rss = word(huf_bstart ws (k + 1) - huf_rank ws 0))`;;

(*** The facts throughout except those about the workspace number ***)

let rd2_base_facts =
  list_mk_conj(filter (fun t -> not(mem `wkv:num` (frees t)))
                      (conjuncts rd2_facts));;

let rd2_rv0_piece_goal = mk_rd2_goal [`rv:int32 list`; `rss:int32 list`]
  (list_mk_conj [rd2_hyps; rd2_base_facts; rd2_sort_facts])
  rd2_sortdone
  (subst [`rd2_rv0 rv ws ml tl mw`,`rvl:int32 list`;
          `rd2_rs0 rss`,`rsl:int32 list`] rd2_rv0done);;

let RD2_RV0_PIECE = prove
 (rd2_rv0_piece_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rss:int32 list`; `0`;
                 `s0:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM; WORD_ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN RD2_STEPS_TAC (1--2) THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rss:int32 list`;
                 `rd2_rs0 rss`; `0`; `s2:armstate`]
    READ_MEMORY_WORDLIST32_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_RD2_RS0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM; WORD_ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [SIMP_TAC[rd2_rs0; EL_LIST_OF_SEQ; ARITH] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    DISCH_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `wk:int64`; `rv:int32 list`; `ws:num list`; `ml:num`;
    `tl:num`; `mw:num`] RD2_RV0_LOOP))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s3" THEN
  EVENTS_UNABBREV_TAC THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

(*** The facts for the rows from those after the sort ***)

let RD2_SORT_WKPARTS = prove
 (`!ws ml tl mw rv rss.
        mw <= 12 /\
        LENGTH (rv:int32 list) = 156 /\ LENGTH (rss:int32 list) = 14 /\
        (!k. 1 <= k /\ k <= mw
             ==> EL k rss = word(huf_bstart ws (k + 1) - huf_rank ws 0))
        ==> LENGTH (rd2_rv0 rv ws ml tl mw) = 156 /\
            (!w. 1 <= w /\ w <= mw
                 ==> EL w (rd2_rv0 rv ws ml tl mw) =
                     word(huf_ustart ws w * 2 EXP (tl - ml))) /\
            LENGTH (rd2_rs0 rss) = 14 /\
            (!k. k <= mw
                 ==> EL k (rd2_rs0 rss) =
                     word(huf_bstart ws (k + 1) - huf_rank ws 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LENGTH_RD2_RV0; LENGTH_RD2_RS0] THEN CONJ_TAC THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `k < 156` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_RD2_RV0];
    SUBGOAL_THEN `k < 14` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[rd2_rs0; EL_LIST_OF_SEQ] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; HUF_START_1; SUB_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The counting sort of the symbols by weight (RD2_SORT_LOOP at 0x6ce8 and   *)
(* RD2_SORT_PIECE), rankStart (RD2_RSP_LOOP at 0x6c9c and RD2_RSTART_PIECE), *)
(* the largest weight with symbols (RD2_MAXW_LOOP at 0x6c60 and              *)
(* RD2_MAXW_PIECE) and the setup chained (RD2_SETUP).                        *)
(* ------------------------------------------------------------------------- *)

(*** The counting sort of readDTableX2: the symbols of weights 1.. first ***)
(*** (from 0), those of weight 0 after them (from N = n - rank 0), each  ***)
(*** weight in the order of the symbols                                  ***)

let rd2_pos0 = new_definition
 `rd2_pos0 ws v =
    if v = 0 then LENGTH ws - huf_rank ws 0
    else huf_bstart ws v - huf_rank ws 0`;;

let rd2_pos = new_definition
 `rd2_pos ws s =
    rd2_pos0 ws (EL s ws) + CARD {t | t < s /\ EL t ws = EL s ws}`;;

let rd2_sym = new_definition
 `rd2_sym ws p =
    if p < LENGTH ws - huf_rank ws 0 then huf_sorted ws (p + huf_rank ws 0)
    else huf_sorted ws (p - (LENGTH ws - huf_rank ws 0))`;;

(*** rankStart after k symbols placed (14 words, weights 0..mw + 1) and ***)
(*** the sorted symbols after k symbols placed                          ***)

let rd2_rsk = new_definition
 `rd2_rsk ws mw k =
    list_of_seq (\v. if v <= mw + 1
                     then word(rd2_pos0 ws v +
                               CARD {t | t < k /\ EL t ws = v}):int32
                     else word 0) 14`;;

let rd2_sl = new_definition
 `rd2_sl ws k (sl0:byte list) =
    list_of_seq (\p. if ?s. s < k /\ rd2_pos ws s = p
                     then word(rd2_sym ws p) else EL p sl0) 256`;;

let LENGTH_RD2_RSK = prove
 (`!ws mw k. LENGTH(rd2_rsk ws mw k) = 14`,
  REWRITE_TAC[rd2_rsk; LENGTH_LIST_OF_SEQ]);;

let LENGTH_RD2_SL = prove
 (`!ws k sl0. LENGTH(rd2_sl ws k sl0) = 256`,
  REWRITE_TAC[rd2_sl; LENGTH_LIST_OF_SEQ]);;

(*** The symbols before s of its weight are fewer than those of the weight ***)

let HUF_CARD_BEFORE_LT = prove
 (`!ws s. s < LENGTH ws
          ==> CARD {t | t < s /\ EL t ws = EL s ws} < huf_rank ws (EL s ws)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HUF_RANK_CARD] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN
  REWRITE_TAC[FINITE_NUMSEG_LT_RESTRICT; PSUBSET; SUBSET; IN_ELIM_THM;
              EXTENSION] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LT_TRANS]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[LT_REFL]);;

let RD2_POS_CASES = prove
 (`!ws s. s < LENGTH ws
          ==> (EL s ws = 0 ==>
               rd2_pos ws s = huf_pos ws s + (LENGTH ws - huf_rank ws 0) /\
               huf_pos ws s < huf_rank ws 0) /\
              (~(EL s ws = 0) ==>
               rd2_pos ws s = huf_pos ws s - huf_rank ws 0 /\
               huf_rank ws 0 <= huf_pos ws s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[rd2_pos; rd2_pos0; HUF_POS_WEIGHTS] THEN
  MP_TAC(SPECL [`ws:num list`; `s:num`] HUF_CARD_BEFORE_LT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                            REWRITE_TAC[th]) THEN
    REWRITE_TAC[huf_bstart; CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`ws:num list`; `1`; `EL s (ws:num list)`]
      HUF_BSTART_MONO) THEN
    REWRITE_TAC[HUF_START_1] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; ARITH_TAC]]);;

let RD2_POS_LT = prove
 (`!ws s. s < LENGTH ws ==> rd2_pos ws s < LENGTH ws`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `s:num`] RD2_POS_CASES) THEN
  MP_TAC(SPECL [`ws:num list`; `s:num`] HUF_POS_LT) THEN
  MP_TAC(SPECL [`ws:num list`; `0`] HUF_RANK_LE) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `EL s (ws:num list) = 0` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let RD2_SYM_POS = prove
 (`!ws s. s < LENGTH ws ==> rd2_sym ws (rd2_pos ws s) = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `s:num`] RD2_POS_CASES) THEN
  MP_TAC(SPECL [`ws:num list`; `s:num`] HUF_POS_LT) THEN
  MP_TAC(SPECL [`ws:num list`; `0`] HUF_RANK_LE) THEN
  ASM_REWRITE_TAC[rd2_sym] THEN
  ASM_CASES_TAC `EL s (ws:num list) = 0` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[ARITH_RULE `~(p + n < n)`; ADD_SUB; HUF_SORTED_POS];
    ASM_SIMP_TAC[ARITH_RULE `r <= p /\ p < n ==> p - r < n - r`;
                 SUB_ADD; HUF_SORTED_POS]]);;

(*** One more symbol placed: the sorted symbols and rankStart ***)

let EL_RD2_SL_STEP = prove
 (`!ws k sl0 p.
        k < LENGTH ws /\ p < 256
        ==> EL p (rd2_sl ws (k + 1) sl0) =
            if p = rd2_pos ws k then word k else EL p (rd2_sl ws k sl0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[rd2_sl; EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[ARITH_RULE `i < k + 1 <=> i < k \/ i = k`] THEN
  ASM_CASES_TAC `p = rd2_pos ws k` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `?s. (s < k \/ s = k) /\ rd2_pos ws s = rd2_pos ws k`
     (fun th -> REWRITE_TAC[th]) THENL
     [MESON_TAC[]; ASM_SIMP_TAC[RD2_SYM_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?s. (s < k \/ s = k) /\ rd2_pos ws s = p) <=>
                (?s. s < k /\ rd2_pos ws s = p)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

let EL_RD2_RSK_STEP = prove
 (`!ws mw k v.
        k < LENGTH ws /\ EL k ws <= mw /\ v < 14
        ==> EL v (rd2_rsk ws mw (k + 1)) =
            if v = EL k ws then word(rd2_pos ws k + 1)
            else EL v (rd2_rsk ws mw k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[rd2_rsk; EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[CARD_RESTRICT_LT_ADD1] THEN
  ASM_CASES_TAC `v = EL k (ws:num list)` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `w <= mw ==> w <= mw + 1`] THEN
    REWRITE_TAC[rd2_pos; ADD_ASSOC];
    SUBGOAL_THEN `~(EL k (ws:num list) = v)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[ADD_CLAUSES]]]);;

(*** After all n symbols ***)

let RD2_RSK_FINAL = prove
 (`!ws mw v.
        mw <= 12 /\ 1 <= v /\ v <= mw
        ==> EL v (rd2_rsk ws mw (LENGTH ws)) =
            word(huf_bstart ws (v + 1) - huf_rank ws 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v < 14` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[rd2_rsk; EL_LIST_OF_SEQ;
               ARITH_RULE `v <= mw ==> v <= mw + 1`] THEN
  REWRITE_TAC[GSYM HUF_RANK_CARD; rd2_pos0] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= v ==> ~(v = 0)`] THEN AP_TERM_TAC THEN
  REWRITE_TAC[HUF_BSTART_SUC] THEN
  MP_TAC(SPECL [`ws:num list`; `1`; `v:num`] HUF_BSTART_MONO) THEN
  REWRITE_TAC[HUF_START_1] THEN ASM_ARITH_TAC);;

let RD2_SL_FINAL = prove
 (`!ws sl0 w j.
        LENGTH ws <= 256 /\ 1 <= w /\ j < huf_rank ws w
        ==> EL (huf_bstart ws w - huf_rank ws 0 + j)
               (rd2_sl ws (LENGTH ws) sl0) =
            word(huf_sorted ws (huf_bstart ws w + j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `w:num`; `j:num`] HUF_SORTED_BUCKET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `huf_bstart ws w + j`] HUF_SORTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = huf_sorted ws (huf_bstart ws w + j)` THEN
  MP_TAC(SPECL [`ws:num list`; `s:num`] RD2_POS_CASES) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= w ==> ~(w = 0)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `huf_rank ws 0 <= huf_bstart ws w` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `1`; `w:num`] HUF_BSTART_MONO) THEN
    REWRITE_TAC[HUF_START_1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `huf_bstart ws w - huf_rank ws 0 + j = rd2_pos ws s`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rd2_pos ws s < 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `s:num`] RD2_POS_LT) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `rd2_pos ws s`)) THEN
  ASM_SIMP_TAC[rd2_sl; EL_LIST_OF_SEQ; RD2_SYM_POS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let RD2_SL_WSYMS = prove
 (`!ws sl0 w.
        LENGTH ws <= 256 /\ 1 <= w
        ==> SUB_LIST(huf_bstart ws w - huf_rank ws 0,huf_rank ws w)
                    (rd2_sl ws (LENGTH ws) sl0) =
            huf_wsyms ws w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `huf_bstart ws w - huf_rank ws 0 + huf_rank ws w <= 256`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `w + 1`] HUF_BSTART_LE) THEN
    MP_TAC(SPECL [`ws:num list`; `w:num`] HUF_BSTART_SUC) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH_RD2_SL; LENGTH_HUF_WSYMS] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j < huf_rank ws w` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_RD2_SL; huf_wsyms; EL_LIST_OF_SEQ;
               RD2_SL_FINAL]);;

(*** The sort loop at 0x6ce8 as a lemma with a frame of its own ***)

let rd2_sort_rr =
 `[word_add wk (word 680),56; word_add wk (word 736),256;
   word_add wk (word 992),LENGTH(ws:num list)]:(int64#num)list`
and rd2_sort_wr =
 `[word_add (wk:int64) (word 680),56; word_add wk (word 736),256]:
  (int64#num)list`;;

let rd2_sort_inv = with_memsafe_loop rd2_sort_rr rd2_sort_wr
 `\k s.
  (read X0 s = word k /\ read X3 s = word_add wk (word 680) /\
   read X8 s = word(LENGTH ws) /\ read X20 s = wk /\
   read X21 s = word_add wk (word 992) /\
   read (memory :> bytes(word_add wk (word 680),56)) s =
   num_of_wordlist(rd2_rsk ws mw k) /\
   read (memory :> bytes(word_add wk (word 736),256)) s =
   num_of_bytelist(rd2_sl ws k sl0) /\
   read (memory :> bytes(word_add wk (word 992),LENGTH ws)) s =
   num_of_bytelist(MAP word ws)) /\
  (read ZF s <=> k = LENGTH ws)`;;

let rd2_sort_goal =
 `!pc (wk:int64) ws mw sl0 e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     2 <= LENGTH ws /\ LENGTH ws <= 256 /\ ALL (\x. x <= mw) ws /\
     mw <= 12 /\ LENGTH(sl0:byte list) = 256 /\
     nonoverlapping (wk,1248) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6ce8) /\
               read X3 s = word_add wk (word 680) /\
               read X8 s = word(LENGTH ws) /\ read X20 s = wk /\
               read X21 s = word_add wk (word 992) /\
               read (memory :> bytes(word_add wk (word 680),56)) s =
               num_of_wordlist(rd2_rsk ws mw 0) /\
               read (memory :> bytes(word_add wk (word 736),256)) s =
               num_of_bytelist sl0 /\
               read (memory :> bytes(word_add wk (word 992),LENGTH ws)) s =
               num_of_bytelist(MAP word ws) /\
               read events s = e)
          (\s. read PC s = word(pc + 0x6d1c) /\
               read (memory :> bytes(word_add wk (word 680),56)) s =
               num_of_wordlist(rd2_rsk ws mw (LENGTH ws)) /\
               read (memory :> bytes(word_add wk (word 736),256)) s =
               num_of_bytelist(rd2_sl ws (LENGTH ws) sl0) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [word_add wk (word 680),56; word_add wk (word 736),256;
                       word_add wk (word 992),LENGTH ws]
                      [word_add wk (word 680),56; word_add wk (word 736),256]))
          (MAYCHANGE [PC; X0; X1; X2; X7; X8] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add wk (word 680),56);
                      memory :> bytes(word_add wk (word 736),256)])`;;

let RD2_SL_0 = prove
 (`!ws sl0. LENGTH(sl0:byte list) = 256 ==> rd2_sl ws 0 sl0 = sl0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rd2_sl; CONJUNCT1 LT; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

(*** The symbol k placed: its weight, rankStart at its weight and its    ***)
(*** byte stored at its position, both arrays updated                    ***)

let RD2_SORT_BODY_TAC =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`word_add wk (word 992):int64`; `MAP (word:num->byte) ws`;
                 `k:num`; `s0:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; WORD_ADD_ASSOC_NUM] THEN DISCH_TAC THEN
  RD2_STEPS_TAC [1] THEN
  SUBGOAL_THEN `EL k ws <= mw` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `ALL (\x. x <= mw) ws`)) THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(EL k ws):byte) = EL k ws /\
                val(word(EL k ws):int64) = EL k ws` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(EL k ws):byte) = EL k ws`]) THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rsk ws mw k`;
                 `EL k (ws:num list)`; `s1:armstate`]
    READ_MEMORY_WORDLIST32_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_RD2_RSK] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN STRIP_TAC THEN
  RD2_STEPS_TAC [2] THEN
  SUBGOAL_THEN `EL (EL k ws) (rd2_rsk ws mw k) = word(rd2_pos ws k)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SUBGOAL_THEN `EL k (ws:num list) < 14` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[rd2_rsk; EL_LIST_OF_SEQ;
                 ARITH_RULE `w <= mw ==> w <= mw + 1`] THEN
    REWRITE_TAC[rd2_pos];
    ALL_TAC] THEN
  SUBGOAL_THEN `rd2_pos ws k < LENGTH ws` ASSUME_TAC THENL
   [MATCH_MP_TAC RD2_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RD2_STEPS_TAC (3--5) THEN
  MP_TAC(ISPECL [`word_add wk (word 736):int64`; `rd2_sl ws k sl0`;
                 `rd2_pos ws k`; `1`; `s5:armstate`]
    READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_RD2_SL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN STRIP_TAC THEN
  RD2_STEPS_TAC (6--8) THEN PTR_DECIDE_FLAGS_TAC THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rsk ws mw k`;
                 `rd2_rsk ws mw (k + 1)`; `EL k (ws:num list)`;
                 `s8:armstate`] READ_MEMORY_WORDLIST32_UPDATE) THEN
  REWRITE_TAC[LENGTH_RD2_RSK; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `EL k (ws:num list) < 14` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_RD2_RSK_STEP] THEN
    X_GEN_TAC `v:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[EL_RD2_RSK_STEP];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`word_add wk (word 736):int64`; `rd2_sl ws k sl0`;
                 `rd2_sl ws (k + 1) sl0`; `rd2_pos ws k`;
                 `word_add wk (word (rd2_pos ws k + 736)):int64`;
                 `word k:byte`; `s8:armstate`]
    READ_MEMORY_BYTELIST_UPDATE1) THEN
  REWRITE_TAC[LENGTH_RD2_SL; WORD_ADD_ASSOC_NUM] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rd2_pos ws k < 256` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_RD2_SL_STEP] THEN
  ANTS_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; DISCH_TAC] THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;;

let RD2_SORT_LOOP = prove
 (rd2_sort_goal,
  REWRITE_TAC[GSYM puff_memsafe; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_PUP_TAC `LENGTH(ws:num list)` `pc + 0x6cf8` `pc + 0x6d18`
    rd2_sort_inv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--4) THEN PUFF_FINAL_TAC THEN
    ASM_SIMP_TAC[RD2_SL_0];
    RD2_SORT_BODY_TAC;
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[]]);;

(*** At 0x6ce8, after rankStart: the start of the sort ***)

let rd2_rsdone =
  with_memsafe rd2_rr rd2_wr
   (mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6ce8)`;
      `read X3 s = word_add wk (word 680) /\ read X4 s = word(mw + 1) /\
       read X5 s = word(ml + 1) /\ read X6 s = word((tl + mw) - ml) /\
       read X8 s = word(LENGTH(ws:num list)) /\ read X12 s = word ml /\
       read X14 s = word mw /\ read X15 s = word tl /\
       read X19 s = word tl /\ read X20 s = wk /\
       read X21 s = word_add wk (word 992) /\ read X23 s = dtable /\
       read X25 s = word_zx(dtd:int32) /\ read X27 s = word((ml + 1) - mw) /\
       read X28 s = word h`;
      `read (memory :> bytes(wk,624)) s = num_of_wordlist (rv:int32 list) /\
       read (memory :> bytes(word_add wk (word 624),52)) s =
       num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) 13) /\
       read (memory :> bytes32(word_add wk (word 676))) s = word 0 /\
       read (memory :> bytes(word_add wk (word 680),56)) s =
       num_of_wordlist(rd2_rsk ws mw 0) /\
       read (memory :> bytes(word_add wk (word 736),256)) s =
       num_of_bytelist (sl0:byte list) /\
       read (memory :> bytes(word_add wk (word 992),LENGTH ws)) s =
       num_of_bytelist(MAP word ws)`;
      rd2_common]));;

(*** The facts about the weights alone ***)

let rd2_wfacts =
  list_mk_conj(filter (fun t -> not(mem `wkv:num` (frees t)) &&
                                not(mem `sl:byte list` (frees t)))
                      (conjuncts rd2_facts));;

let rd2_sort_piece_goal = mk_rd2_goal [`rv:int32 list`; `sl0:byte list`]
  (list_mk_conj [rd2_hyps; rd2_wfacts;
                 `2 <= LENGTH(ws:num list) /\ LENGTH(sl0:byte list) = 256`])
  rd2_rsdone
  (subst [`rd2_rsk ws mw (LENGTH ws)`,`rss:int32 list`;
          `rd2_sl ws (LENGTH ws) sl0`,`sl:byte list`] rd2_sortdone);;

let RD2_SORT_PIECE = prove
 (rd2_sort_piece_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `wk:int64`; `ws:num list`; `mw:num`; `sl0:byte list`]
   RD2_SORT_LOOP))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s1" THEN
  EVENTS_UNABBREV_TAC THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

(*** rankStart while it is computed, rankStart[v] for v = 1..j ***)

let rd2_rsp = new_definition
 `rd2_rsp ws j =
    list_of_seq (\v. if 1 <= v /\ v <= j
                     then word(huf_bstart ws v - huf_rank ws 0):int32
                     else word 0) 14`;;

let LENGTH_RD2_RSP = prove
 (`!ws j. LENGTH(rd2_rsp ws j) = 14`,
  REWRITE_TAC[rd2_rsp; LENGTH_LIST_OF_SEQ]);;

let EL_RD2_RSP_STEP = prove
 (`!ws j v.
        v < 14
        ==> EL v (rd2_rsp ws (j + 1)) =
            if v = j + 1 then word(huf_bstart ws (j + 1) - huf_rank ws 0)
            else EL v (rd2_rsp ws j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[rd2_rsp; EL_LIST_OF_SEQ] THEN
  ASM_CASES_TAC `v = j + 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= j + 1`];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(*** The loop at 0x6c9c, rankStart[w] = the symbols of weights 1..w - 1 ***)

let rd2_rsp_inv = with_memsafe_loop
  `[word_add wk (word 624),112]:(int64#num)list`
  `[word_add (wk:int64) (word 680),56]:(int64#num)list`
 `\j s.
  (read X0 s = word_add wk (word(628 + 4 * j)) /\
   read X1 s = word(huf_bstart ws (j + 1) - huf_rank ws 0) /\
   read X3 s = word_add wk (word 680) /\
   read X8 s = word_add wk (word(628 + 4 * mw)) /\
   read (memory :> bytes(word_add wk (word 624),52)) s =
   num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) 13) /\
   read (memory :> bytes(word_add wk (word 680),56)) s =
   num_of_wordlist(rd2_rsp ws j)) /\
  (read ZF s <=> j = mw)`;;

let rd2_rsp_goal =
 `!pc (wk:int64) ws mw e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     1 <= mw /\ mw <= 12 /\ LENGTH ws <= 256 /\
     nonoverlapping (wk,736) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6c9c) /\
               read X4 s = word(mw + 1) /\ read X20 s = wk /\
               read (memory :> bytes(word_add wk (word 624),52)) s =
               num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32)
                                           13) /\
               read (memory :> bytes(word_add wk (word 680),56)) s =
               num_of_wordlist(rd2_rsp ws 0) /\
               read events s = e)
          (\s. read PC s = word(pc + 0x6cdc) /\
               read X1 s = word(huf_bstart ws (mw + 1) - huf_rank ws 0) /\
               read X3 s = word_add wk (word 680) /\
               read (memory :> bytes(word_add wk (word 680),56)) s =
               num_of_wordlist(rd2_rsp ws mw) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [word_add wk (word 624),112]
                                           [word_add wk (word 680),56]))
          (MAYCHANGE [PC; X0; X1; X2; X3; X7; X8] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add wk (word 680),56)])`;;

let RD2_RSP_LOOP = prove
 (rd2_rsp_goal,
  REWRITE_TAC[GSYM puff_memsafe; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_PUP_TAC `mw:num` `pc + 0x6cc0` `pc + 0x6cd8` rd2_rsp_inv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--9) THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; HUF_START_1; SUB_REFL] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`ws:num list`; `j + 1`] HUF_BSTART_LE) THEN
    MP_TAC(SPECL [`ws:num list`; `(j + 1) + 1`] HUF_BSTART_LE) THEN
    MP_TAC(SPECL [`ws:num list`; `j + 1`] HUF_RANK_LE) THEN
    MP_TAC(SPECL [`ws:num list`; `j + 1`] HUF_BSTART_SUC) THEN
    MP_TAC(SPECL [`ws:num list`; `1`; `j + 1`] HUF_BSTART_MONO) THEN
    REWRITE_TAC[HUF_START_1; ARITH_RULE `1 <= j + 1`] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`word_add wk (word 624):int64`;
                   `list_of_seq (\j. word(huf_rank ws j):int32) 13`; `13`;
                   `j + 1`; `s0:armstate`]
      READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    SUBGOAL_THEN `j + 1 < 13` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    REWRITE_TAC[WORD_ADD_ASSOC_NUM;
                ARITH_RULE `624 + 4 * (j + 1) = 628 + 4 * j`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rsp ws j`; `j + 1`;
                   `s0:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
    ASM_REWRITE_TAC[LENGTH_RD2_RSP] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN STRIP_TAC THEN
    RD2_STEPS_TAC (1--6) THEN PTR_DECIDE_FLAGS_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
     `((628 + 4 * j) + 4) + 52 = 680 + 4 * (j + 1)`]) THEN
    MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rsp ws j`;
                   `rd2_rsp ws (j + 1)`; `j + 1`; `s6:armstate`]
      READ_MEMORY_WORDLIST32_UPDATE) THEN
    REWRITE_TAC[LENGTH_RD2_RSP; WORD_ADD_ASSOC_NUM] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[EL_RD2_RSP_STEP;
                   ARITH_RULE `j + 1 < 13 ==> j + 1 < 14`] THEN
      X_GEN_TAC `v:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[EL_RD2_RSP_STEP];
      DISCH_TAC] THEN
    RD2_SET_REG_TAC
     `read X1 s6 = word(huf_bstart ws ((j + 1) + 1) - huf_rank ws 0)`
     (ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`huf_bstart ws ((j + 1) + 1) = huf_bstart ws (j + 1) +
                                      huf_rank ws (j + 1)`;
        `huf_rank ws 0 <= huf_bstart ws (j + 1)`] THEN
      ARITH_TAC) THEN
    RD2_SET_REG_TAC `read X0 s6 = word_add wk (word(628 + 4 * (j + 1)))`
     (ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[]]);;

(*** The start of the symbols past all weights, and rankStart for the sort ***)

let HUF_BSTART_ALL_LE = prove
 (`!ws m. ALL (\x. x <= m) ws ==> huf_bstart ws (m + 1) = LENGTH ws`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HUF_BSTART_CARD] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `t:num` THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:num` o REWRITE_RULE[GSYM ALL_EL]) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let rd2_rs1 = new_definition
 `rd2_rs1 ws mw =
    list_of_seq (\v. if v = 0 then word(LENGTH ws - huf_rank ws 0)
                     else EL v (rd2_rsp ws mw)) 14`;;

let LENGTH_RD2_RS1 = prove
 (`!ws mw. LENGTH(rd2_rs1 ws mw) = 14`,
  REWRITE_TAC[rd2_rs1; LENGTH_LIST_OF_SEQ]);;

let RD2_RSK_0 = prove
 (`!ws mw.
        ALL (\x. x <= mw) ws /\ mw <= 12
        ==> rd2_rsk ws mw 0 =
            list_of_seq (\v. if v = mw + 1
                             then word(LENGTH ws - huf_rank ws 0)
                             else EL v (rd2_rs1 ws mw)) 14`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_RD2_RSK; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `v:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[rd2_rsk; rd2_rs1; rd2_rsp; EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES; ADD_CLAUSES;
              rd2_pos0] THEN
  ASM_CASES_TAC `v = 0` THEN
  ASM_REWRITE_TAC[LE_0; ARITH_RULE `~(0 = m + 1)`] THEN
  ASM_CASES_TAC `v = mw + 1` THEN ASM_REWRITE_TAC[LE_REFL] THENL
   [ASM_SIMP_TAC[HUF_BSTART_ALL_LE];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(*** At 0x6c9c, after maxW: rankStart zero, the number of symbols on the ***)
(*** stack from readStats                                                ***)

let rd2_setup_mem =
 `read (memory :> bytes(wk,624)) s = num_of_wordlist (rv:int32 list) /\
  read (memory :> bytes(word_add wk (word 624),52)) s =
  num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) 13) /\
  read (memory :> bytes32(word_add wk (word 676))) s = word 0 /\
  read (memory :> bytes(word_add wk (word 680),56)) s =
  num_of_wordlist(rd2_rsp ws 0) /\
  read (memory :> bytes(word_add wk (word 736),256)) s =
  num_of_bytelist (sl0:byte list) /\
  read (memory :> bytes(word_add wk (word 992),LENGTH ws)) s =
  num_of_bytelist(MAP word ws) /\
  read (memory :> bytes32
         (word_add (word_sub stackpointer (word 208)) (word 204))) s =
  word(LENGTH(ws:num list))`;;

let rd2_maxwdone =
  with_memsafe rd2_rr rd2_wr
   (mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6c9c)`;
      `read X4 s = word(mw + 1) /\ read X5 s = word(ml + 1) /\
       read X6 s = word((tl + mw) - ml) /\ read X12 s = word ml /\
       read X14 s = word mw /\ read X15 s = word tl /\
       read X19 s = word tl /\ read X20 s = wk /\
       read X21 s = word_add wk (word 992) /\ read X23 s = dtable /\
       read X25 s = word_zx(dtd:int32) /\ read X27 s = word((ml + 1) - mw) /\
       read X28 s = word h`;
      rd2_setup_mem; rd2_common]));;

let rd2_rstart_piece_goal = mk_rd2_goal [`rv:int32 list`; `sl0:byte list`]
  (list_mk_conj [rd2_hyps; rd2_wfacts;
                 `2 <= LENGTH(ws:num list) /\ LENGTH(sl0:byte list) = 256`])
  rd2_maxwdone rd2_rsdone;;

let RD2_RSTART_PIECE = prove
 (rd2_rstart_piece_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `wk:int64`; `ws:num list`; `mw:num`] RD2_RSP_LOOP))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s1" THEN
  EVENTS_UNABBREV_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `mw:num`] HUF_BSTART_ALL_LE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rsp ws mw`; `0`;
                 `s1:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_RD2_RSP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM; WORD_ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN RD2_STEPS_TAC (2--3) THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rsp ws mw`;
                 `rd2_rs1 ws mw`; `0`; `s3:armstate`]
    READ_MEMORY_WORDLIST32_UPDATE) THEN
  REWRITE_TAC[LENGTH_RD2_RSP; rd2_rs1; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM; WORD_ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [SIMP_TAC[EL_LIST_OF_SEQ; ARITH] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    REWRITE_TAC[GSYM rd2_rs1] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rs1 ws mw`; `mw + 1`;
                 `s3:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
  REWRITE_TAC[LENGTH_RD2_RS1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mw <= 12` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UXTW_ABBREV_TAC `X4` `v4:int64` `mw + 1` THEN
  RD2_STEPS_TAC [4] THEN
  MP_TAC(ISPECL [`word_add wk (word 680):int64`; `rd2_rs1 ws mw`;
    `list_of_seq (\v. if v = mw + 1 then word(LENGTH ws - huf_rank ws 0)
                      else EL v (rd2_rs1 ws mw)) 14:int32 list`;
    `mw + 1`; `s4:armstate`] READ_MEMORY_WORDLIST32_UPDATE) THEN
  REWRITE_TAC[LENGTH_RD2_RS1; LENGTH_LIST_OF_SEQ; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `mw <= 12 ==> mw + 1 < 14`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `mw:num`] RD2_RSK_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

(*** maxW at 0x6c60: the largest weight with symbols, searched from ml ***)
(*** down, as a lemma with a frame of its own                          ***)

let HUF_RANK_ABOVE = prove
 (`!ws m v. ALL (\x. x <= m) ws /\ m < v ==> huf_rank ws v = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HUF_RANK_CARD] THEN
  SUBGOAL_THEN `{t | t < LENGTH(ws:num list) /\ EL t ws = v} = {}`
   (fun th -> REWRITE_TAC[th; CARD_CLAUSES]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:num` o REWRITE_RULE[GSYM ALL_EL]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let rd2_maxw_inv = with_memsafe_loop
  `[word_add wk (word 624),52]:(int64#num)list` `[]:(int64#num)list`
 `\j s.
  (read X5 s = word(ml + 1) /\ read X6 s = word(tl + 1) /\
   read X12 s = word ml /\ read X14 s = word(ml - j) /\
   read X20 s = wk /\
   read (memory :> bytes(word_add wk (word 624),52)) s =
   num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32) 13)) /\
  (read X0 s = word(huf_rank ws (ml - j)) /\ read X4 s = word(ml - j + 1))`;;

let rd2_maxw_goal =
 `!pc (wk:int64) ws ml tl mw e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     ALL (\x. x <= mw) ws /\ ~(huf_rank ws mw = 0) /\ LENGTH ws <= 256 /\
     1 <= mw /\ mw <= ml /\ ml <= tl /\ tl <= 12 /\
     nonoverlapping (wk,676) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6c60) /\
               read X6 s = word(tl + 1) /\ read X12 s = word ml /\
               read X19 s = word tl /\ read X20 s = wk /\
               read (memory :> bytes(word_add wk (word 624),52)) s =
               num_of_wordlist(list_of_seq (\j. word(huf_rank ws j):int32)
                                           13) /\
               read events s = e)
          (\s. read PC s = word(pc + 0x6c9c) /\
               read X4 s = word(mw + 1) /\ read X5 s = word(ml + 1) /\
               read X6 s = word((tl + mw) - ml) /\ read X14 s = word mw /\
               read X27 s = word((ml + 1) - mw) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [word_add wk (word 624),52] []))
          (MAYCHANGE [PC; X0; X4; X5; X6; X14; X27] ,,
           MAYCHANGE [events])`;;

(*** rankStats[w] as a 32-bit load at wk + 4 * (w + 156) in the state s ***)

let RD2_RANKSTAT_TAC w s =
  MP_TAC(ISPECL [`word_add wk (word 624):int64`;
                 `list_of_seq (\j. word(huf_rank ws j):int32) 13`; `13`;
                 w; s] READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,w),`13`))
  ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; WORD_ADD_ASSOC_NUM] THEN
  REWRITE_TAC[ARITH_RULE `624 + 4 * x = 4 * (x + 156)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN (subst [w,`x:num`] `val(word(x + 156):int64) = x + 156`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN ASM_ARITH_TAC; ALL_TAC];;

let RD2_MAXW_LOOP = prove
 (rd2_maxw_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `huf_rank ws ml < 2 EXP 32 /\ huf_rank ws mw < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`ws:num list`; `ml:num`] HUF_RANK_LE) THEN
    MP_TAC(SPECL [`ws:num list`; `mw:num`] HUF_RANK_LE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `mw:num = ml` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `mw:num = ml`)) THEN
    PUFF_INIT_TAC "s0" THEN RD2_RANKSTAT_TAC `ml:num` `s0:armstate` THEN
    RD2_STEPS_TAC (1--10) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `huf_rank ws ml = 0` ASSUME_TAC THENL
   [MATCH_MP_TAC HUF_RANK_ABOVE THEN EXISTS_TAC `mw:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `ml - mw` `pc + 0x6c78` `pc + 0x6c8c`
    rd2_maxw_inv THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    PUFF_INIT_TAC "s0" THEN RD2_RANKSTAT_TAC `ml:num` `s0:armstate` THEN
    RD2_STEPS_TAC (1--6) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[SUB_0];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    RD2_STEPS_TAC (1--4) THEN
    RD2_RANKSTAT_TAC `ml - i - 1` `s4:armstate` THEN
    RD2_STEPS_TAC [5] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_zx (word (huf_rank ws (ml - i - 1)):int32):int64 =
                  word (huf_rank ws (ml - i - 1))` SUBST1_TAC THENL
     [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
      REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
      MP_TAC(SPECL [`ws:num list`; `ml - i - 1`] HUF_RANK_LE) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN TRY AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    SUBGOAL_THEN `huf_rank ws (ml - i) = 0` ASSUME_TAC THENL
     [MATCH_MP_TAC HUF_RANK_ABOVE THEN EXISTS_TAC `mw:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `huf_rank ws (ml - i) = 0`]) THEN
    RD2_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    PUFF_INIT_TAC "s0" THEN
    SUBGOAL_THEN `ml - (ml - mw) = mw` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ml - (ml - mw) = mw`]) THEN
    RD2_STEPS_TAC (1--4) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(*** At 0x6c60, after the checks and the table log tl ***)

let rd2_tdone =
  with_memsafe rd2_rr rd2_wr
   (mk_abs(`s:armstate`,list_mk_conj
     [`read PC s = word(pc + 0x6c60)`;
      `read X6 s = word(tl + 1) /\ read X12 s = word ml /\
       read X15 s = word tl /\ read X19 s = word tl /\ read X20 s = wk /\
       read X21 s = word_add wk (word 992) /\ read X23 s = dtable /\
       read X25 s = word_zx(dtd:int32) /\ read X28 s = word h`;
      rd2_setup_mem; rd2_common]));;

let rd2_maxw_piece_goal = mk_rd2_goal [`rv:int32 list`; `sl0:byte list`]
  (list_mk_conj [rd2_hyps; rd2_wfacts])
  rd2_tdone rd2_maxwdone;;

let RD2_MAXW_PIECE = prove
 (rd2_maxw_piece_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `wk:int64`; `ws:num list`; `ml:num`; `tl:num`; `mw:num`]
   RD2_MAXW_LOOP))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  ARM_BIGSTEP_TAC RD2_EXEC "s1" THEN
  EVENTS_UNABBREV_TAC THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

(*** The frame of the pieces: idempotent and containing the identity, ***)
(*** for chaining the pieces and for the loops                        ***)

let RD2_FRAME_IDEMPOT = prove
 (mk_eq(list_mk_icomb ",," [rd2_frame; rd2_frame],rd2_frame),
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS] THEN
  MAYCHANGE_IDEMPOT_TAC);;

let RD2_FRAME_ID = prove
 (list_mk_icomb "subsumed" [`(=):armstate->armstate->bool`; rd2_frame],
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS] THEN
  SUBSUMED_ID_MAYCHANGE_TAC);;

let RD2_TRANS_TAC q =
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q THEN
  CONJ_TAC THENL [REWRITE_TAC[RD2_FRAME_IDEMPOT]; ALL_TAC];;

(*** The setup chained: from 0x6c60 to the weight loop at w = 1 ***)

let rd2_setup_wkv =
 `rd2_wkv ws ml tl mw (rd2_rv0 rv ws ml tl mw)
          (rd2_rs0 (rd2_rsk ws mw (LENGTH ws)))`
and rd2_setup_sl = `rd2_sl ws (LENGTH ws) sl0`;;

let rd2_setup_goal = mk_rd2_goal [`rv:int32 list`; `sl0:byte list`]
  (list_mk_conj [rd2_hyps; rd2_wfacts;
    `2 <= LENGTH(ws:num list) /\ LENGTH(sl0:byte list) = 256 /\
     LENGTH(rv:int32 list) = 156`])
  rd2_tdone
  (subst [rd2_setup_wkv,`wkv:num`; rd2_setup_sl,`sl:byte list`] rd2_winv1);;

(*** The facts about the workspace and the sorted symbols after the setup ***)

let RD2_SETUP_FACTS_TAC =
  SUBGOAL_THEN `mw <= 12 /\ tl <= 12` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `mw:num`; `rv:int32 list`;
                `rd2_rsk ws mw (LENGTH ws)`] RD2_SORT_WKPARTS) THEN
  ASM_REWRITE_TAC[LENGTH_RD2_RSK] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RD2_RSK_FINAL THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `mw:num`;
                `rd2_rv0 rv ws ml tl mw`;
                `rd2_rs0 (rd2_rsk ws mw (LENGTH ws))`] RD2_WKV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_RD2_SL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RD2_SL_WSYMS THEN ASM_REWRITE_TAC[];;

let RD2_SETUP = prove
 (rd2_setup_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RD2_TRANS_TAC rd2_maxwdone THEN CONJ_TAC THENL
   [MATCH_MP_TAC RD2_MAXW_PIECE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RD2_TRANS_TAC rd2_rsdone THEN CONJ_TAC THENL
   [MATCH_MP_TAC RD2_RSTART_PIECE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RD2_TRANS_TAC (subst [`rd2_rsk ws mw (LENGTH ws)`,`rss:int32 list`;
                        rd2_setup_sl,`sl:byte list`] rd2_sortdone) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RD2_SORT_PIECE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RD2_TRANS_TAC (subst [`rd2_rv0 rv ws ml tl mw`,`rvl:int32 list`;
                        `rd2_rs0 (rd2_rsk ws mw (LENGTH ws))`,
                        `rsl:int32 list`;
                        rd2_setup_sl,`sl:byte list`] rd2_rv0done) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RD2_RV0_PIECE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH_RD2_SL; LENGTH_RD2_RSK] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC RD2_SL_WSYMS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RD2_RSK_FINAL THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  RD2_TRANS_TAC (subst [rd2_setup_wkv,`wkv:num`; rd2_setup_sl,`sl:byte list`]
                   rd2_rowsdone) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RD2_ROWS_PIECE THEN ASM_REWRITE_TAC[] THEN
    RD2_SETUP_FACTS_TAC;
    MATCH_MP_TAC RD2_FSTART THEN ASM_REWRITE_TAC[] THEN
    RD2_SETUP_FACTS_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop over the weights w2 of the second symbol at 0x6f60: one weight   *)
(* w2, with the call of HUF_fillDTableX2ForWeight at the level 2             *)
(* (RD2_W2ITER), and the loop (RD2_W2LOOP).                                  *)
(* ------------------------------------------------------------------------- *)

(*** The loop over the weights w2 of the second symbol, from minW to the ***)
(*** end, for the symbol k of the weight w (level 2)                     ***)

let rd2_w2loop_goal = mk_rd2_goal [`w:num`; `k:num`] rd2_sym_hyps
  (rd2_expand(subst [`MAX 1 ((2 * ml + 2) - (w + tl))`,`w2:num`] rd2_w2inv))
  rd2_w2exit;;

(*** One weight w2 of the second symbol: the fill call for its symbols ***)
(*** at level 2, the next w2 or the end of the loop                    ***)

let rd2_w2next =
  let inv1 = rhs(concl(BETA_CONV(mk_comb(
               rd2_expand(subst [`w2 + 1`,`w2:num`] rd2_w2inv),
               `s:armstate`)))) in
  mk_abs(`s:armstate`,
    mk_disj(mk_conj(`w2 + 1 <= mw`,inv1),
            mk_conj(`(w2:num) = mw`,
                    rhs(concl(BETA_CONV(mk_comb(rd2_w2exit,
                                                `s:armstate`)))))));;

let rd2_w2iter_goal = mk_rd2_goal [`w:num`; `k:num`; `w2:num`]
  (list_mk_conj [rd2_sym_hyps;
    `MAX 1 ((2 * ml + 2) - (w + tl)) <= w2 /\ w2 <= mw`])
  (rd2_expand rd2_w2inv) rd2_w2next;;

(*** The addresses of rankStart[w2 - 1] and rankStart[w2] in the       ***)
(*** normalized form in which the simulation resolves the two loads of ***)
(*** the LDPSW [x25,#-4], and the address of its event                 ***)

let RD2_LDPSW_ADDR = prove
 (`!wk:int64 w2.
     1 <= w2
     ==> word_add wk (word(4 * (170 + (w2 - 1)))) =
         word_add wk (word_sub (word(680 + 4 * w2)) (word 4)) /\
         word_add wk (word(4 * (170 + w2))) =
         word_add wk (word_sub (word(680 + 4 * w2)) (word 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `680 + 4 * w2 = 4 * (170 + (w2 - 1)) + 4` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; CONV_TAC WORD_RULE];
    CONV_TAC WORD_RULE]);;

let RD2_LDPSW_EVENT = WORD_RULE
 `word_sub (word_add (x:int64) (word (680 + n))) (word 4) =
  word_add x (word (676 + n))`;;

(*** The workspace words of the weight w2 in s0: rankStart[w2 - 1],     ***)
(*** rankStart[w2] and rankVal[nb1][w2], and the bounds of its symbols  ***)

let RD2_W2_READS_TAC =
  RD2_WK32_TAC `4 * (170 + (w2 - 1))` `170 + (w2 - 1)` `s0:armstate` THEN
  RD2_WK32_TAC `4 * (170 + w2)` `170 + w2` `s0:armstate` THEN
  RD2_WK32_TAC `52 * ((ml + 1) - w) + 4 * w2` `13 * ((ml + 1) - w) + w2`
    `s0:armstate` THEN
  RD2_WKV_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`w2:num`; `1`] SUB_ADD)
                                (ASSUME `1 <= w2`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`wk:int64`; `w2:num`]
                                        RD2_LDPSW_ADDR)
                                 (ASSUME `1 <= w2`)]) THEN
  MP_TAC(SPECL [`ws:num list`; `w2:num`] HUF_BSTART_LE) THEN
  MP_TAC(SPECL [`ws:num list`; `w2 + 1`] HUF_BSTART_LE) THEN
  MP_TAC(SPECL [`ws:num list`; `1`; `w2:num`] HUF_BSTART_MONO) THEN
  MP_TAC(SPECL [`ws:num list`; `w2:num`] HUF_BSTART_SUC) THEN
  REWRITE_TAC[HUF_START_1] THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

(*** The entries of the weight w2 in those of the symbol k: from rv to  ***)
(*** rv1, L2 = 2^(r - nb2) for each of its symbols, within the L        ***)

let RD2_W2_FACTS_TAC =
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HUF_COMPLETE_ALL_LE) THEN
  SUBGOAL_THEN `tl - ((ml + 1) - w) = (tl + w) - (ml + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `huf_rv ws ml ((tl + w) - (ml + 1)) (w2 + 1) =
    huf_rv ws ml ((tl + w) - (ml + 1)) w2 +
    huf_rank ws w2 * 2 EXP (((tl + w) - (ml + 1)) - ((ml + 1) - w2)) /\
    huf_rv ws ml ((tl + w) - (ml + 1)) (w2 + 1) <= L /\
    (w2 = mw ==> huf_rv ws ml ((tl + w) - (ml + 1)) (w2 + 1) = L)`
  STRIP_ASSUME_TAC THENL
   [W(fun (asl,w) -> REWRITE_TAC
      [SYM(rd2_hidden asl `2 EXP ((tl + w) - (ml + 1)) = L`)]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HUF_RV_STEP THEN ASM_REWRITE_TAC[];
      TRANS_TAC LE_TRANS `huf_rv ws ml ((tl + w) - (ml + 1)) (mw + 1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HUF_RV_MONO THEN ASM_REWRITE_TAC[LE_ADD_RCANCEL];
        MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC HUF_RV_ALL THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HUF_RV_ALL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  RD2_ABBREV_TAC `L2 = 2 EXP (((tl + w) - (ml + 1)) - ((ml + 1) - w2))` THEN
  ABBREV_TAC `rv = huf_rv ws ml ((tl + w) - (ml + 1)) w2` THEN
  ABBREV_TAC `rv1 = huf_rv ws ml ((tl + w) - (ml + 1)) (w2 + 1)`;;

(*** The level-2 fill call at step 12, for the symbols of the weight w2 ***)

let RD2_L2_CALL_TAC =
  RD2_SET_REG_TAC `read X0 s10 = word_add dtable (word (4 + 4 * (st + rv)))`
   (ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_zx (word rv:int32):int64 = word rv` SUBST1_TAC THENL
     [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
      REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[WORD_SHL_WORD; WORD_ADD_ASSOC_NUM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC) THEN
  RD2_SET_REG_TAC `read X3 s10 = word (((ml + 1) - w) + ((ml + 1) - w2))`
   (ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC) THEN
  RD2_STEPS_TAC [11] THEN
  RD2_SET_REG_TAC
   `read X2 s11 =
    word_add (word_add wk (word (736 + huf_bstart ws w2 - huf_rank ws 0)))
             (word(huf_rank ws w2))`
   (ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMPLE_ARITH_TAC) THEN
  MP_TAC(ISPECL [`word_add wk (word 736):int64`; `sl:byte list`;
    `huf_bstart ws w2 - huf_rank ws 0`; `huf_rank ws w2`; `s11:armstate`]
    READ_MEMORY_BYTELIST_SLICE) THEN
  ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `w2:num` th)
    (CONJ (ASSUME `1 <= w2`) (ASSUME `w2 <= mw`))]) o
    check (fun th -> is_forall(concl th) &&
           can (find_term ((=) `huf_wsyms`)) (concl th))) THEN
  DISCH_TAC THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 28556):int64`;
    `word_add dtable (word (4 + 4 * (st + rv))):int64`;
    `word_add wk (word (736 + huf_bstart ws w2 - huf_rank ws 0)):int64`;
    `huf_wsyms ws w2`; `((ml + 1) - w) + ((ml + 1) - w2)`; `tl:num`;
    `huf_sorted ws (huf_bstart ws w + k)`; `2`]
    HUF_FILLDTABLEX2FORWEIGHT_CORRECT))) THEN
  REWRITE_TAC[LENGTH_HUF_WSYMS] THEN
  SUBGOAL_THEN `tl - (((ml + 1) - w) + ((ml + 1) - w2)) =
                ((tl + w) - (ml + 1)) - ((ml + 1) - w2)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> REWRITE_TAC
     (map (rd2_hidden asl)
       [`2 EXP (((tl + w) - (ml + 1)) - ((ml + 1) - w2)) = L2`])) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s12" THEN
  EVENTS_UNABBREV_TAC;;

(*** The level-2 block in the table and the prefix extended by it, to ***)
(*** the entries st + rv1                                             ***)

let RD2_L2_EXTEND_TAC =
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `w:num`; `k:num`; `w2:num`;
                `(ml + 1) - w`; `(tl + w) - (ml + 1)`; `(ml + 1) - w2`]
     HUF_DTABLE2_LEVEL2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (asl,w) -> REWRITE_TAC
     (map (rd2_hidden asl)
       [`2 EXP (tl - ml) = sc`; `huf_ustart ws w * sc = uu`;
        `2 EXP ((tl + w) - (ml + 1)) = L`;
        `2 EXP (((tl + w) - (ml + 1)) - ((ml + 1) - w2)) = L2`])) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `uu + k * L + rv = st + rv` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  W(fun (asl,w) ->
    let s = rand w in
    MP_TAC(ISPECL [`word_add dtable (word 4):int64`; `huf_dtable2 ws ml tl`;
                   `4 * (st + rv)`; `4 * L2 * huf_rank ws w2`; s]
      READ_MEMORY_BYTELIST_EXTEND)) THEN
  REWRITE_TAC[LENGTH_HUF_DTABLE2; WORD_ADD_ASSOC_NUM] THEN
  W(fun (asl,w) -> REWRITE_TAC
     (map (rd2_hidden asl) [`2 EXP tl = tt`])) THEN
  FIRST_ASSUM(SUBST1_TAC o
    check (fun th ->
      is_eq(concl th) &&
      can (term_match [] `SUB_LIST(4 * (st + rv),n) l:byte list`)
          (lhs(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `4 * (st + rv) + 4 * L2 * huf_rank ws w2 = 4 * (st + rv1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC];;

let RD2_W2ITER = prove
 (rd2_w2iter_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RD2_WEIGHT_FACTS_TAC THEN
  RD2_SYMBOL_FACTS_TAC THEN
  SUBGOAL_THEN `1 <= w2 /\ w2 <= ml /\ (ml + 1) - w2 <= (tl + w) - (ml + 1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `MAX 1 ((2 * ml + 2) - (w + tl)) <= w2` THEN
    REWRITE_TAC[ARITH_RULE `MAX a b <= c <=> a <= c /\ b <= c`] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  RD2_W2_READS_TAC THEN RD2_STEPS_TAC (1--10) THEN RD2_W2_FACTS_TAC THEN
  RD2_L2_CALL_TAC THEN RD2_L2_EXTEND_TAC THEN
  ASM_CASES_TAC `w2:num = mw` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `w2:num = mw`)) THEN
    RD2_STEPS_TAC (13--15) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `rv1:num = L`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RD2_LDPSW_EVENT]) THEN PUFF_FINAL_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(mw + 1 <= mw)`] THEN ASM_REWRITE_TAC[];
    RD2_STEPS_TAC (13--15) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RD2_LDPSW_EVENT]) THEN PUFF_FINAL_TAC THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[GSYM(ASSUME `rv1 = rv + huf_rank ws w2 * L2`)] THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) &&
         lhs(concl th) =
         `read (memory :> bytes(word_add dtable (word 4),4 * (st + rv1)))
               s15`
      then REWRITE_TAC[th] else NO_TAC) THEN
    RD2_REGS_TAC]);;

(*** The loop over w2 = minW..mw from the iterations ***)

let RD2_W2LOOP_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC ENSURES_LOOP_EXIT THEN
  MAP_EVERY EXISTS_TAC
   [`(mw + 1) - MAX 1 ((2 * ml + 2) - (w + tl))`;
    mk_abs(`i:num`,mk_abs(`s:armstate`,
      mk_conj(`MAX 1 ((2 * ml + 2) - (w + tl)) + i <= mw`,
              mk_comb(rd2_expand(subst
                [`MAX 1 ((2 * ml + 2) - (w + tl)) + i`,`w2:num`] rd2_w2inv),
                `s:armstate`))))] THEN
  REWRITE_TAC[RD2_FRAME_IDEMPOT; RD2_FRAME_ID] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_ALREADY THEN REWRITE_TAC[RD2_FRAME_ID] THEN
    BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAX] THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rd2_expand(subst
      [`MAX 1 ((2 * ml + 2) - (w + tl)) + i`,`w2:num`] rd2_w2inv)) THEN
    CONJ_TAC THENL [BETA_TAC THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (subst [`MAX 1 ((2 * ml + 2) - (w + tl)) + i`,`w2:num`]
                      rd2_w2next) THEN
    CONJ_TAC THENL
     [BETA_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RD2_W2ITER THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MAX] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC `\s:armstate. F` THEN
    REWRITE_TAC[ENSURES_TRIVIAL] THEN BETA_TAC THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[MAX] THEN ASM_ARITH_TAC];;

let RD2_W2LOOP = prove(rd2_w2loop_goal, RD2_W2LOOP_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loops chained: the symbols of a weight (RD2_SYMITER and RD2_SYMLOOP), *)
(* the weights (RD2_WITER2 and RD2_WLOOP), the fill (RD2_FILL) and the       *)
(* function from 0x6c60 to its return (RD2_FROMT).                           *)
(* ------------------------------------------------------------------------- *)

(*** The symbol k of the weight w (level 2): prefill, the loop over w2 ***)
(*** and the end of its entries                                        ***)

let rd2_symiter_goal = mk_rd2_goal [`w:num`; `k:num`] rd2_sym_hyps
  rd2_syminv rd2_symnext;;

let RD2_SYMITER = prove
 (rd2_symiter_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RD2_TRANS_TAC (rd2_expand(subst [`MAX 1 ((2 * ml + 2) - (w + tl))`,`w2:num`]
                                  rd2_w2inv)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RD2_PREFILL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RD2_TRANS_TAC rd2_w2exit THEN CONJ_TAC THENL
   [MATCH_MP_TAC RD2_W2LOOP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RD2_SYMTAIL THEN ASM_REWRITE_TAC[]]);;

(*** The loop over the symbols of the weight w at 0x6ee0 (level 2) ***)

let rd2_symloop_goal = mk_rd2_goal [`w:num`]
  (list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ 2 * ml + 2 <= tl + w + mw /\
     ~(huf_rank ws w = 0)`])
  rd2_syminv0 rd2_symdone;;

let RD2_SYMLOOP = prove
 (rd2_symloop_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC ENSURES_LOOP_EXIT THEN
  MAP_EVERY EXISTS_TAC
   [`huf_rank ws w`;
    mk_abs(`i:num`,mk_abs(`s:armstate`,
      mk_conj(`i < huf_rank ws w`,
              mk_comb(subst [`i:num`,`k:num`] rd2_syminv,`s:armstate`))))] THEN
  REWRITE_TAC[RD2_FRAME_IDEMPOT; RD2_FRAME_ID] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_ALREADY THEN REWRITE_TAC[RD2_FRAME_ID] THEN
    BETA_TAC THEN ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 0 < n`];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (subst [`i:num`,`k:num`] rd2_syminv) THEN
    CONJ_TAC THENL [BETA_TAC THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (subst [`i:num`,`k:num`] rd2_symnext) THEN CONJ_TAC THENL
     [BETA_TAC THEN GEN_TAC THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RD2_SYMITER THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `\s:armstate. F` THEN
    REWRITE_TAC[ENSURES_TRIVIAL] THEN BETA_TAC THEN REWRITE_TAC[LT_REFL]]);;

(*** One weight w (level 2): its symbols, none or the loop over them ***)

let rd2_witer2_goal = mk_rd2_goal [`w:num`]
  (list_mk_conj [rd2_hyps; rd2_facts;
    `1 <= w /\ w <= mw /\ 2 * ml + 2 <= tl + w + mw`])
  rd2_winv rd2_wnext;;

let RD2_WITER2 = prove
 (rd2_witer2_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `huf_rank ws w = 0` THENL
   [MATCH_MP_TAC RD2_W2EMPTY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RD2_TRANS_TAC rd2_syminv0 THEN CONJ_TAC THENL
   [MATCH_MP_TAC RD2_W2START THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RD2_TRANS_TAC rd2_symdone THEN CONJ_TAC THENL
   [MATCH_MP_TAC RD2_SYMLOOP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RD2_WTAIL2 THEN ASM_REWRITE_TAC[]]);;

(*** The loop over the weights w = 1..mw at 0x6e44 ***)

let rd2_wloop_goal = mk_rd2_goal []
  (list_mk_conj [rd2_hyps; rd2_facts]) rd2_winv1 rd2_fdone;;

let RD2_WLOOP = prove
 (rd2_wloop_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC ENSURES_LOOP_EXIT THEN
  MAP_EVERY EXISTS_TAC
   [`mw:num`;
    mk_abs(`i:num`,mk_abs(`s:armstate`,
      mk_conj(`i < mw`,
              mk_comb(subst [`i + 1`,`w:num`] rd2_winv,`s:armstate`))))] THEN
  REWRITE_TAC[RD2_FRAME_IDEMPOT; RD2_FRAME_ID] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_ALREADY THEN REWRITE_TAC[RD2_FRAME_ID] THEN
    BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> 0 < n`];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (subst [`i + 1`,`w:num`] rd2_winv) THEN
    CONJ_TAC THENL [BETA_TAC THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (subst [`i + 1`,`w:num`] rd2_wnext) THEN CONJ_TAC THENL
     [BETA_TAC THEN GEN_TAC THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
      ASM_CASES_TAC `tl + (i + 1) + mw < 2 * ml + 2` THENL
       [MATCH_MP_TAC RD2_WITER1; MATCH_MP_TAC RD2_WITER2] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `\s:armstate. F` THEN
    REWRITE_TAC[ENSURES_TRIVIAL] THEN BETA_TAC THEN REWRITE_TAC[LT_REFL]]);;

(*** The fill and the end: from the weight loop at w = 1 to the return ***)

let rd2_fill_goal = mk_rd2_goal []
  (list_mk_conj [rd2_hyps; rd2_facts]) rd2_winv1 rd2_fpost;;

let RD2_FILL = prove
 (rd2_fill_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RD2_TRANS_TAC rd2_fdone THEN CONJ_TAC THENL
   [MATCH_MP_TAC RD2_WLOOP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RD2_FEND THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(*** From 0x6c60, after the checks, to the return ***)

let rd2_fromt_goal = mk_rd2_goal [`rv:int32 list`; `sl0:byte list`]
  (list_mk_conj [rd2_hyps; rd2_wfacts;
    `2 <= LENGTH(ws:num list) /\ LENGTH(sl0:byte list) = 256 /\
     LENGTH(rv:int32 list) = 156`])
  rd2_tdone rd2_fpost;;

let RD2_FROMT = prove
 (rd2_fromt_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RD2_TRANS_TAC (subst [rd2_setup_wkv,`wkv:num`; rd2_setup_sl,`sl:byte list`]
                   rd2_winv1) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RD2_SETUP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RD2_FILL THEN ASM_REWRITE_TAC[] THEN RD2_SETUP_FACTS_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The whole function: the size of the workspace checked, HUF_readStats_wksp *)
(* called, its errors returned, a code length ml above mtl an error, and     *)
(* otherwise the table log and RD2_FROMT (HUF_READDTABLEX2_WKSP_CORRECT).    *)
(* ------------------------------------------------------------------------- *)

(*** HUF_readDTableX2_wksp (0x6b90): the table log tl as the code chooses ***)
(*** it from the maximum mtl of the header and the code length ml         ***)

let huf_tablelog2 = new_definition
 `huf_tablelog2 mtl ml = if mtl = 12 /\ ~(ml = 12) then 11 else mtl`;;

let rd2_goal =
 `!pc returnaddress stackpointer dtable src (l:byte list) wk wsz flags
    (dtd:int32) mtl fcpy fset ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 368) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     val dtd MOD 256 = mtl /\ mtl <= 12 /\
     LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 2124 <= 2 EXP 64 /\
     nonoverlapping (dtable:int64,4 + 4 * 2 EXP mtl) (wk,2124) /\
     nonoverlapping (dtable,4 + 4 * 2 EXP mtl)
                    (word_sub stackpointer (word 528),528) /\
     nonoverlapping (dtable,4 + 4 * 2 EXP mtl) (word pc,0x20018) /\
     nonoverlapping (dtable,4 + 4 * 2 EXP mtl) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (word_sub stackpointer (word 528),528) /\
     nonoverlapping (wk,2124) (word pc,0x20018) /\
     nonoverlapping (wk,2124) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 528),528)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 528),528) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 528),528) (ea,el)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6b90) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dtable; src; word(LENGTH l); wk; wsz; flags] s /\
               read (memory :> bytes32 dtable) s = dtd /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (2124 <= val(wsz:int64)
                ==> !ws ml h.
                      huf_weights T l ws ml h /\ ml <= mtl
                      ==> read X0 s = word h /\
                          read (memory :> bytes8(word_add dtable (word 1))) s =
                          word 1 /\
                          read (memory :> bytes8(word_add dtable (word 2))) s =
                          word(huf_tablelog2 mtl ml) /\
                          read (memory :> bytes(word_add dtable (word 4),
                                        4 * 2 EXP (huf_tablelog2 mtl ml))) s =
                          num_of_bytelist
                           (huf_dtable2 ws ml (huf_tablelog2 mtl ml))) /\
               (~(2124 <= val wsz /\
                  ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; dtable,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 528),528;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [dtable,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 528),528]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dtable,4 + 4 * 2 EXP mtl);
             memory :> bytes(wk,2124);
             memory :> bytes(word_sub stackpointer (word 528),528)])`;;

let RD2_TOP_START_TAC =
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
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0";;

let RD2_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 208)) (word 208):int64 =
  stackpointer`;;

let RD2_TOP_FRAME_TAC = RD2_FRAME_REBASE_TAC THEN MONOTONE_MAYCHANGE_TAC;;

(*** An error return, the reason proving that it is not a success ***)

let RD2_TOP_FAIL_TAC =
  RD2_FRAME_REBASE_TAC THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[RD2_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN TRY RD2_TOP_FRAME_TAC;;

(*** dsz = 2 EXP mtl abbreviated, for the reasoning about regions ***)

let RD2_DSZ_ABBREV_TAC =
  SUBGOAL_THEN `2 EXP mtl <= 4096` ASSUME_TAC THENL
   [SUBST1_TAC(ARITH_RULE `4096 = 2 EXP 12`) THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `dsz = 2 EXP mtl`;;

let RD2_DSZ_RULE th =
  REWRITE_RULE[ASSUME `2 EXP mtl = dsz`] (SPEC_ALL th);;

(*** The largest weight present, below ml ***)

let HUF_MAXW_EXISTS = prove
 (`!ws ml. ALL (\x. x <= ml) ws /\ MEM 1 ws
           ==> ?mw. 1 <= mw /\ mw <= ml /\ ALL (\x. x <= mw) ws /\
                    ~(huf_rank ws mw = 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\w. ALL (\x. x <= w) (ws:num list)` num_WOP) THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [EXISTS_TAC `ml:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mw:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mw:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= mw` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\x. x <= mw) ws` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ml:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[HUF_RANK_CARD; CARD_EQ_0; FINITE_NUMSEG_LT_RESTRICT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `mw - 1` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `ALL:(num->bool)->num list->bool`)) (concl th))) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_EL] THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:num` o check (fun th ->
    is_forall(concl th) &&
    not(can (find_term ((=) `ALL:(num->bool)->num list->bool`))
            (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:num` o REWRITE_RULE[GSYM ALL_EL] o
    check (fun th -> concl th = `ALL (\x. x <= mw) ws`)) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let HUF_WEIGHTS_MEM1 = prove
 (`!l ws ml h. huf_weights T l ws ml h ==> MEM 1 ws`,
  REWRITE_TAC[huf_weights] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MESON_TAC[]);;

(*** rankStart zero (and the word before it), from the stores of q0 = 0 ***)

let READ_MEMORY_BYTES128_ZERO_PREFIX = prove
 (`!a:int64 s:armstate n.
        read (memory :> bytes128 a) s = word 0 /\ n <= 16
        ==> read (memory :> bytes(a,n)) s = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `n:num`; `read memory s`]
    READ_BYTES_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 16 ==> MIN 16 n = n`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[VAL_READ_MEMORY_BYTES128; VAL_WORD_0; MOD_0]);;

let NUM_OF_WORDLIST_RD2_RSP_0 = prove
 (`!ws. num_of_wordlist(rd2_rsp ws 0) = 0`,
  GEN_TAC THEN REWRITE_TAC[rd2_rsp] THEN
  SIMP_TAC[ARITH_RULE `~(1 <= v /\ v <= 0)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[num_of_wordlist; VAL_WORD_0] THEN ARITH_TAC);;

let RD2_ZERO_RANKSTART = prove
 (`!wk:int64 ws s:armstate.
     read (memory :> bytes128 (word_add wk (word 676))) s = word 0 /\
     read (memory :> bytes128 (word_add wk (word 692))) s = word 0 /\
     read (memory :> bytes(word_add wk (word 708),12)) s = 0 /\
     read (memory :> bytes128 (word_add wk (word 720))) s = word 0
     ==> read (memory :> bytes32 (word_add wk (word 676))) s = word 0 /\
         read (memory :> bytes(word_add wk (word 680),56)) s =
         num_of_wordlist(rd2_rsp ws 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_RD2_RSP_0] THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add wk (word 676),60)) s = 0`
  MP_TAC THENL
   [SUBGOAL_THEN
     `!a:int64. read (memory :> bytes128 a) s = word 0
                ==> read (memory :> bytes(a,16)) s = 0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES128_ZERO_PREFIX THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `60 = 16 + 16 + 12 + 16`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `60 = 4 + 56`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[GSYM VAL_READ_MEMORY_BYTES32; VAL_WORD_0] THEN
  ASM_REWRITE_TAC[]);;

(*** Any memory as a list of 32-bit words ***)

let READ_MEMORY_WORDLIST32_EXISTS = prove
 (`!a:int64 n s:armstate.
        ?l:int32 list. LENGTH l = n /\
                       read (memory :> bytes(a,4 * n)) s = num_of_wordlist l`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [EXISTS_TAC `[]:int32 list` THEN
    REWRITE_TAC[LENGTH; MULT_CLAUSES; num_of_wordlist;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    FIRST_X_ASSUM(X_CHOOSE_THEN `l:int32 list` STRIP_ASSUME_TAC o
                  SPEC `s:armstate`) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `LENGTH(l:int32 list)`)) THEN
    EXISTS_TAC
     `APPEND l [read (memory :> bytes32(word_add a
                  (word(4 * LENGTH(l:int32 list))))) s]` THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD1; ADD_CLAUSES] THEN
    MATCH_MP_TAC READ_MEMORY_WORDLIST32_APPEND1 THEN
    ASM_REWRITE_TAC[]]);;

(*** Going on with a piece th, instantiated by insts, weakening its frame ***)

let RD2_GOON_TAC wtac th insts =
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
      CONJ_TAC THENL [RD2_TOP_FRAME_TAC; BETA_TAC THEN wtac]]);;

(*** The postcondition of the whole function from that of RD2_FROMT, for ***)
(*** the weights ws, ml with header of h bytes and the table log tl       ***)

let RD2_TOP_POST_TAC =
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`ws':num list`; `ml':num`; `h':num`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                  `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[huf_tablelog2];
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[]];;

(*** The table log at 0x6c40: mtl, or 11 if mtl = 12 and ml < 12 ***)

let rd2_tlog_goal =
 `!pc mtl ml (dtd:int32) e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     ml <= mtl /\ mtl <= 12 /\ word_and dtd (word 255) = word mtl
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6c40) /\
               read X19 s = word mtl /\ read X12 s = word ml /\
               read X25 s = word_zx dtd /\ read events s = e)
          (\s. read PC s = word(pc + 0x6c60) /\
               read X19 s = word(huf_tablelog2 mtl ml) /\
               read X15 s = word(huf_tablelog2 mtl ml) /\
               read X6 s = word(huf_tablelog2 mtl ml + 1) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [] []))
          (MAYCHANGE [PC; X6; X15; X19] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events])`;;

let RD2_TLOG_FIN_TAC n =
  ASM_REWRITE_TAC[] THEN PUFF_INIT_TAC "s0" THEN RD2_STEPS_TAC (1--n) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN TRY(MATCH_MP_TAC WORD_ZX_WORD_SMALL) THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC;;

let RD2_TLOG = prove
 (rd2_tlog_goal,
  REWRITE_TAC[GSYM puff_memsafe; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[huf_tablelog2] THEN
  ASM_CASES_TAC `mtl = 12` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC `ml = 12` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN RD2_TLOG_FIN_TAC 5;
      RD2_TLOG_FIN_TAC 8];
    RD2_TLOG_FIN_TAC 5]);;

let RD2_TLOG_BOUNDS = prove
 (`!mtl ml. ml <= mtl /\ mtl <= 12
            ==> ml <= huf_tablelog2 mtl ml /\ huf_tablelog2 mtl ml <= mtl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_tablelog2] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(*** The call of HUF_readStats_wksp at 0x6c24 (step 38) ***)

let RD2_CALL_TAC =
  SUBGOAL_THEN `~(word_sub stackpointer (word 208):int64 = word 160)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 208) = word 160 <=>
                           x = word 368`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add wk (word 992):int64) + 255 < 2 EXP 64`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`wk:int64`; `992`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `val(wk:int64) + 2124 <= 2 EXP 64` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `val(wk:int64) + 2124 <= 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN
  RD2_STEPS_TAC [38] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x6c28):int64`;
    `word_sub stackpointer (word 208):int64`;
    `word_add wk (word 992):int64`; `word_add wk (word 624):int64`;
    `word_add (word_sub stackpointer (word 208)) (word 204):int64`;
    `word_add (word_sub stackpointer (word 208)) (word 200):int64`;
    `src:int64`; `l:byte list`; `word_add wk (word 1248):int64`;
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
  ARM_BIGSTEP_TAC RD2_EXEC "s39" THEN EVENTS_UNABBREV_TAC;;

(*** No weights: the error code of HUF_readStats_wksp returned ***)

let RD2_NOWEIGHTS_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s39 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s39 = x0r`] THEN
  RD2_STEPS_TAC (40--41) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  RD2_STEPS_TAC (42--51) THEN RD2_TOP_FAIL_TAC;;

(*** The table log ml too large for the table: the error at 0x7018 ***)

let RD2_TABLELOG_ERROR_TAC =
  ZSTD_DECIDE_BRANCH_TAC THEN RD2_STEPS_TAC (46--55) THEN
  RD2_FRAME_REBASE_TAC THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[RD2_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [RD2_TOP_FRAME_TAC;
    MAP_EVERY X_GEN_TAC [`ws':num list`; `ml':num`; `h':num`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                  `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`ml':num <= mtl`; `ml':num = ml`;
                           `~(ml <= mtl)`] THEN ARITH_TAC];;

(*** The table log, the workspace as it is and the rest by RD2_FROMT ***)

let RD2_GO_TAC =
  ZSTD_DECIDE_BRANCH_TAC THEN
  NC_ASSUME_REWRITE_TAC [`word_and (dtd:int32) (word 255) = word mtl`] THEN
  ZSTD_SMALL_WORD_TAC THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `mtl:num`; `ml:num`; `dtd:int32`] RD2_TLOG))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS] THEN ARM_BIGSTEP_TAC RD2_EXEC "s46" THEN
  EVENTS_UNABBREV_TAC THEN
  MP_TAC(ISPECL [`wk:int64`; `156`; `s46:armstate`]
    READ_MEMORY_WORDLIST32_EXISTS) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `rv:int32 list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`word_add wk (word 736):int64`;
    `read (memory :> bytelist(word_add wk (word 736),256)) s46`;
    `256`; `s46:armstate`] READ_BYTELIST_EQ_BYTES) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`wk:int64`; `ws:num list`; `s46:armstate`]
    RD2_ZERO_RANKSTART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mtl:num`; `ml:num`] RD2_TLOG_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RD2_GOON_TAC RD2_TOP_POST_TAC (RD2_DSZ_RULE RD2_FROMT)
   [`huf_tablelog2 mtl ml`,`tl:num`;
    `read (memory :> bytelist(word_add wk (word 736),256)) s46`,
    `sl0:byte list`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];;

(*** The weights ws, ml with header of h bytes from HUF_readStats_wksp ***)

let RD2_WEIGHTS_TAC =
  FIRST_X_ASSUM(X_CHOOSE_THEN `ws:num list` (X_CHOOSE_THEN `ml:num`
     (X_CHOOSE_TAC `h:num`)) o check (is_exists o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ws:num list`; `ml:num`; `h:num`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `huf_weights`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUF_WEIGHTS_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HUF_WEIGHTS_MEM1) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`] HUF_MAXW_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mw:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word h:int64) = h` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RD2_STEPS_TAC (40--45) THEN
  ASM_CASES_TAC `ml <= mtl` THENL [RD2_GO_TAC; RD2_TABLELOG_ERROR_TAC];;

let HUF_READDTABLEX2_WKSP_CORRECT = prove
 (rd2_goal,
  RD2_TOP_START_TAC THEN RD2_DSZ_ABBREV_TAC THEN
  ASM_CASES_TAC `2124 <= val(wsz:int64)` THENL
   [ALL_TAC; RD2_STEPS_TAC (1--15) THEN RD2_TOP_FAIL_TAC] THEN
  SUBGOAL_THEN `word_and (dtd:int32) (word 255) = word mtl` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `255 = 2 EXP 8 - 1`] THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `m <= 12 ==> m < 4294967296`];
    ALL_TAC] THEN
  RD2_STEPS_TAC (1--22) THEN
  MP_TAC(ISPECL [`word_add wk (word 708):int64`; `s22:armstate`; `12`]
    READ_MEMORY_BYTES128_ZERO_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  RD2_STEPS_TAC (23--37) THEN RD2_CALL_TAC THEN
  ASM_CASES_TAC `?ws ml h. huf_weights T (l:byte list) ws ml h` THENL
   [RD2_WEIGHTS_TAC; RD2_NOWEIGHTS_TAC]);;

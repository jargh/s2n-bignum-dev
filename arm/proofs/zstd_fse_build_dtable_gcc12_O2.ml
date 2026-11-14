(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* FSE_buildDTable_internal(dt,normalizedCounter,maxSymbolValue,tableLog,    *)
(* workSpace,wkspSize) of zstd, at 0xe80 in the image, which builds the      *)
(* decoding table of an FSE code from its normalized counts: a header with   *)
(* tableLog and fastMode, and then for each state its baseline (newState),   *)
(* symbol and number of bits, as in the specification in rfc8878.ml. It      *)
(* returns 0, the checks of its arguments that would give an error code      *)
(* being excluded by the hypotheses.                                         *)
(* ========================================================================= *)

needs "arm/proofs/utils/zstd_huf.ml";;

(* ------------------------------------------------------------------------- *)
(* The table built. fse_dtable cs tl is the decoding table of the            *)
(* specification for the counts cs and the accuracy log tl, with 4 bytes for *)
(* each state: its baseline (in 2 bytes, little-endian), its symbol and its  *)
(* number of bits. fse_fast cs tl is the fastMode flag of the header, which  *)
(* is 1 if no count is 2^(tl - 1) or more. While the table is being built,   *)
(* fse_tbl cs tl tb0 P u has the entries of the states below u done and the  *)
(* symbols of the states satisfying P in place, the other bytes being those  *)
(* of tb0, the initial ones.                                                 *)
(* ------------------------------------------------------------------------- *)

let fse_fast = new_definition
 `fse_fast (cs:int list) tl =
    if ALL (\c. c < &(2 EXP (tl - 1))) cs then 1 else 0`;;

let fse_dtable = new_definition
 `fse_dtable (cs:int list) alog =
    list_of_seq
     (\i. word(if i MOD 4 = 0 then fse_base cs alog (i DIV 4) MOD 256
               else if i MOD 4 = 1 then fse_base cs alog (i DIV 4) DIV 256
               else if i MOD 4 = 2 then fse_symbol cs alog (i DIV 4)
               else fse_nbits cs alog (i DIV 4)):byte)
     (4 * 2 EXP alog)`;;

let fse_tbl = new_definition
 `fse_tbl (cs:int list) alog (tb0:byte list) (P:num->bool) u =
    list_of_seq
     (\i. if i DIV 4 < u then EL i (fse_dtable cs alog)
          else if i MOD 4 = 2 /\ P(i DIV 4)
          then word(fse_symbol cs alog (i DIV 4))
          else EL i tb0)
     (4 * 2 EXP alog)`;;

let FSE_DIVMOD4 = prove
 (`!u. (4 * u) DIV 4 = u /\ (4 * u) MOD 4 = 0 /\
       (4 * u + 1) DIV 4 = u /\ (4 * u + 1) MOD 4 = 1 /\
       (4 * u + 2) DIV 4 = u /\ (4 * u + 2) MOD 4 = 2 /\
       (4 * u + 3) DIV 4 = u /\ (4 * u + 3) MOD 4 = 3`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `u:num`;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `u:num`;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `2`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `u:num`;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `3`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `u:num`] THEN
  ARITH_TAC);;

let LENGTH_FSE_DTABLE = prove
 (`!cs alog. LENGTH(fse_dtable cs alog) = 4 * 2 EXP alog`,
  REWRITE_TAC[fse_dtable; LENGTH_LIST_OF_SEQ]);;

let LENGTH_FSE_TBL = prove
 (`!cs alog tb0 P u. LENGTH(fse_tbl cs alog tb0 P u) = 4 * 2 EXP alog`,
  REWRITE_TAC[fse_tbl; LENGTH_LIST_OF_SEQ]);;

let FSE_TBL_FULL = prove
 (`!cs alog tb0 P. fse_tbl cs alog tb0 P (2 EXP alog) = fse_dtable cs alog`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_FSE_TBL; LENGTH_FSE_DTABLE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[fse_tbl] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `i DIV 4 < 2 EXP alog` (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

let FSE_TBL_P_EQ = prove
 (`!cs alog tb0 P Q u.
        (!x. x < 2 EXP alog ==> (P x <=> Q x))
        ==> fse_tbl cs alog tb0 P u = fse_tbl cs alog tb0 Q u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_FSE_TBL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[fse_tbl] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `i DIV 4 < 2 EXP alog` (fun th -> ASM_SIMP_TAC[th]) THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

let FSE_TBL_SYM = prove
 (`!cs alog tb0 P v j.
        v < 2 EXP alog /\ j < 4 * 2 EXP alog
        ==> EL j (fse_tbl cs alog tb0 (\x. P x \/ x = v) 0) =
            if j = 4 * v + 2 then word(fse_symbol cs alog v)
            else EL j (fse_tbl cs alog tb0 P 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_tbl] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; CONJUNCT1 LT] THEN
  ASM_CASES_TAC `j = 4 * v + 2` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[FSE_DIVMOD4];
    ASM_CASES_TAC `j DIV 4 = v` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(j MOD 4 = 2)` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`j:num`; `4`] DIVISION) THEN ASM_ARITH_TAC]);;

let FSE_TBL_BUILD = prove
 (`!cs alog tb0 u j.
        u < 2 EXP alog /\ j < 4 * 2 EXP alog
        ==> EL j (fse_tbl cs alog tb0 (\x. T) (u + 1)) =
            if 4 * u <= j /\ j < 4 * u + 4 then EL j (fse_dtable cs alog)
            else EL j (fse_tbl cs alog tb0 (\x. T) u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_tbl] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `4 * u <= j /\ j < 4 * u + 4 <=> j DIV 4 = u`
  SUBST1_TAC THENL
   [SIMP_TAC[DIV_EQ_RANGE; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `j DIV 4 = u` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `u < u + 1`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `j < u + 1 <=> j < u \/ j = u`]);;

let EL_FSE_DTABLE = prove
 (`!cs alog u.
        u < 2 EXP alog
        ==> EL (4 * u) (fse_dtable cs alog) =
            word(fse_base cs alog u MOD 256) /\
            EL (4 * u + 1) (fse_dtable cs alog) =
            word(fse_base cs alog u DIV 256) /\
            EL (4 * u + 2) (fse_dtable cs alog) =
            word(fse_symbol cs alog u) /\
            EL (4 * u + 3) (fse_dtable cs alog) =
            word(fse_nbits cs alog u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_dtable] THEN
  W(fun (_,w) -> MAP_EVERY (fun t ->
    SUBGOAL_THEN (mk_binop `(<):num->num->bool` t `4 * 2 EXP alog`)
      ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC])
    [`4 * u`; `4 * u + 1`; `4 * u + 2`; `4 * u + 3`]) THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[FSE_DIVMOD4] THEN CONV_TAC NUM_REDUCE_CONV);;

let FSE_TBL_EL_SYM = prove
 (`!cs tl tb0 P u.
        u < 2 EXP tl /\ P u
        ==> EL (4 * u + 2) (fse_tbl cs tl tb0 P u) = word(fse_symbol cs tl u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_tbl] THEN
  SUBGOAL_THEN `4 * u + 2 < 4 * 2 EXP tl` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; FSE_DIVMOD4; LT_REFL]);;

let FSE_TBL_READ_SYM = prove
 (`!dt cs tl tb0 P u s:armstate.
        u < 2 EXP tl /\ P u /\
        read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
        num_of_bytelist(fse_tbl cs tl tb0 P u)
        ==> read (memory :> bytes8 (word_add dt (word ((4 + 4 * u) + 2)))) s =
            word(fse_symbol cs tl u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add dt (word 4):int64`; `fse_tbl cs tl tb0 P u`;
                 `4 * u + 2`; `s:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[FSE_TBL_EL_SYM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT AP_TERM_TAC THEN ARITH_TAC);;

let FSE_TBL_ENTRY_VAL = prove
 (`!cs tl tb0 u.
        u < 2 EXP tl /\ fse_base cs tl u < 65536 /\
        fse_symbol cs tl u < 256 /\ fse_nbits cs tl u < 256
        ==> num_of_bytelist
             (SUB_LIST(4 * u,4) (fse_tbl cs tl tb0 (\x. T) (u + 1))) =
            fse_base cs tl u +
            65536 * (fse_symbol cs tl u + 256 * fse_nbits cs tl u)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NUM_OF_BYTELIST_SUB_LIST_4 o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_FSE_TBL] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[fse_tbl] THEN
  SUBGOAL_THEN
   `4 * u < 4 * 2 EXP tl /\ 4 * u + 1 < 4 * 2 EXP tl /\
    4 * u + 2 < 4 * 2 EXP tl /\ 4 * u + 3 < 4 * 2 EXP tl`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; FSE_DIVMOD4; ARITH_RULE `u < u + 1`] THEN
  ASM_SIMP_TAC[EL_FSE_DTABLE] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL; RDIV_LT_EQ; ARITH_EQ;
               ARITH_RULE `x < 65536 ==> x < 256 * 256`] THEN
  MP_TAC(SPECL [`fse_base cs tl u`; `256`] DIVISION) THEN ARITH_TAC);;

let FSE_TBL_INIT = prove
 (`!cs alog (tb0:byte list).
        LENGTH tb0 = 4 * 2 EXP alog
        ==> fse_tbl cs alog tb0 (\v. 2 EXP alog <= v) 0 = tb0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_FSE_TBL] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[fse_tbl] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ; CONJUNCT1 LT] THEN
  SUBGOAL_THEN `~(2 EXP alog <= i DIV 4)` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[NOT_LE] THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The spread of the symbols over the table. With H the number of states for *)
(* the symbols whose counts are not -1, fse_placed tl H j v holds if the     *)
(* state v has its symbol in place after j steps of the walk: if it is a     *)
(* state of a symbol of count -1 (H <= v), placed before the walk, or has    *)
(* been visited.                                                             *)
(* ------------------------------------------------------------------------- *)

let fse_placed = new_definition
 `fse_placed alog H j v <=> H <= v \/ ?i. i < j /\ fse_pos alog i = v`;;

let FSE_PLACED_0 = prove
 (`!alog H v. fse_placed alog H 0 v <=> H <= v`,
  REWRITE_TAC[fse_placed; CONJUNCT1 LT]);;

let FSE_PLACED_SUC = prove
 (`!alog H j v.
        fse_placed alog H (j + 1) v <=>
        fse_placed alog H j v \/ (fse_pos alog j < H /\ v = fse_pos alog j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fse_placed; ARITH_RULE `i < j + 1 <=> i < j \/ i = j`] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  ASM_CASES_TAC `fse_pos alog j < H` THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[];
    MP_TAC(ARITH_RULE `~(fse_pos alog j < H)
                       ==> (fse_pos alog j = v ==> H <= v)`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let FSE_PLACED_SKIP = prove
 (`!alog H j.
        ~(fse_pos alog j < H)
        ==> fse_placed alog H (j + 1) = fse_placed alog H j`,
  REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC[FSE_PLACED_SUC]);;

let FSE_PLACED_ALL = prove
 (`!alog H j v.
        5 <= alog /\ (H = 0 \/ j = 2 EXP alog) /\ v < 2 EXP alog
        ==> fse_placed alog H j v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fse_placed] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[LE_0];
    DISJ2_TAC THEN ASM_REWRITE_TAC[fse_pos] THEN
    MATCH_MP_TAC FSE_POS_SURJ THEN ASM_REWRITE_TAC[]]);;

let FSE_TBL_PLACED_STEP = prove
 (`!cs alog tb0 H j.
        fse_pos alog j < H
        ==> fse_tbl cs alog tb0
              (\x. fse_placed alog H j x \/ x = fse_pos alog j) 0 =
            fse_tbl cs alog tb0 (fse_placed alog H (j + 1)) 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FSE_TBL_P_EQ THEN
  ASM_REWRITE_TAC[FSE_PLACED_SUC]);;

let FSE_TBL_PLACED_ALL = prove
 (`!cs alog tb0 H j.
        5 <= alog /\ (H = 0 \/ j = 2 EXP alog)
        ==> fse_tbl cs alog tb0 (fse_placed alog H j) 0 =
            fse_tbl cs alog tb0 (\x. T) 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FSE_TBL_P_EQ THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC FSE_PLACED_ALL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The flags computed in the loop over the counts, for the first u counts:   *)
(* fse_anyhigh cs u, whether some count is not -1, and fse_fastp cs tl u,    *)
(* whether all are below 2^(tl - 1). The code puts the second into the       *)
(* header as fastMode if the first holds, and 1 otherwise (FBD_BFI_HEADER    *)
(* for the insertion), which is fse_fast cs tl either way.                   *)
(* ------------------------------------------------------------------------- *)

let fse_anyhigh = new_definition
 `fse_anyhigh (cs:int list) u <=> ?t. t < u /\ ~(EL t cs = -- &1)`;;

let fse_fastp = new_definition
 `fse_fastp (cs:int list) tl u <=> !t. t < u ==> EL t cs < &(2 EXP (tl - 1))`;;

let FSE_ANYHIGH_0 = prove
 (`!cs. ~fse_anyhigh cs 0`,
  REWRITE_TAC[fse_anyhigh; CONJUNCT1 LT]);;

let FSE_FASTP_0 = prove
 (`!cs tl. fse_fastp cs tl 0`,
  REWRITE_TAC[fse_fastp; CONJUNCT1 LT]);;

let FSE_ANYHIGH_SUC = prove
 (`!cs u. fse_anyhigh cs (u + 1) <=>
          fse_anyhigh cs u \/ ~(EL u cs = -- &1)`,
  REWRITE_TAC[fse_anyhigh; EXISTS_LT_SUC]);;

let FSE_FASTP_SUC = prove
 (`!cs tl u. fse_fastp cs tl (u + 1) <=>
             fse_fastp cs tl u /\ EL u cs < &(2 EXP (tl - 1))`,
  REWRITE_TAC[fse_fastp; FORALL_LT_SUC]);;

let FSE_FAST_FASTP = prove
 (`!cs tl. fse_fast cs tl = if fse_fastp cs tl (LENGTH cs) then 1 else 0`,
  REWRITE_TAC[fse_fast; fse_fastp; ALL_EL]);;

let FSE_FASTP_ALL_LOW = prove
 (`!cs tl u. ~fse_anyhigh cs u ==> fse_fastp cs tl u`,
  REWRITE_TAC[fse_anyhigh; fse_fastp; NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC);;

let FBD_BFI_HEADER = prove
 (`!t b. t < 65536 /\ b <= 1
         ==> word_zx(word_insert (word_zx (word (t + 65536):int64):int32)
                                 (16,16)
                       (word_zx (word b:int64):int32):int32):int64 =
             word(t + 65536 * b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_zx (word (t + 65536):int64):int32 = word(t + 65536) /\
                word_zx (word b:int64):int32 = word b`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_INSERT_UPPER16 o
    rand o lhand o snd)
  THEN ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
                       DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(t + 65536) MOD 65536 = t` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[ARITH_RULE `65536 + t = 1 * 65536 + t`; MOD_MULT_ADD] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The state of the building. The counts cs, LENGTH cs of them, are 16-bit   *)
(* numbers at nc, the table goes at dt + 4 after its header at dt, and the   *)
(* workspace at wksp holds the next states of the symbols (16 bits each) and *)
(* then, if no count is -1, the symbols in order, for the spread, with 8     *)
(* bytes more for the stores of 8 bytes at a time. The counts are fse_valid  *)
(* for tl (they fill the table), 5 <= tl <= 12, and the checks of the        *)
(* arguments at the entry pass.                                              *)
(*                                                                           *)
(* The assertions below are at:                                              *)
(*                                                                           *)
(*   0xe80   fbd_entry, the entry                                            *)
(*   0xf18   fbd_linv, the loop over the counts, placing the symbols         *)
(*           of count -1, for the measure m = LENGTH cs - u                  *)
(*   0xf5c   fbd_gen, the general spread, if some count is -1                *)
(*   0xf70   fbd_ginv, a disjunction: before the states of the symbol        *)
(*           u, or (0xf88) before placing it at the state of step j, or      *)
(*           (0xfa0) skipping that state, of a symbol of count -1            *)
(*   0x1034  fbd_fast1, the spread if no count is -1: the symbols are        *)
(*           laid out in order in the workspace, 8 bytes at a time           *)
(*   0x1060  fbd_f1inv, a disjunction: before laying out the symbol u,       *)
(*           or (0x1078) after the first i of its bytes                      *)
(*   0x109c  fbd_fast2, then given to the states 2 at a time                 *)
(*   0x10ac  fbd_f2inv, before steps 2k and 2k + 1                           *)
(*   0xfd8   fbd_build, the building of the entries of the states            *)
(*   0xff0   fbd_binv, before the entry of the state u                       *)
(*                                                                           *)
(* and each has a theorem that it leads to the return with the table and     *)
(* header as in fbd_post, proved from those of the later ones. Each has the  *)
(* conjunct puff_memsafe e rr wr s, for the trace e at the entry, the loads  *)
(* being from the counts, the table and the workspace and the stores to the  *)
(* table and the workspace.                                                  *)
(* ------------------------------------------------------------------------- *)

let fbd_rr =
 `[nc,2 * LENGTH(cs:int list); dt,4 + 4 * 2 EXP tl;
   wksp,2 * LENGTH cs + 2 EXP tl + 8]:(int64#num)list`
and fbd_wr =
 `[dt,4 + 4 * 2 EXP tl;
   wksp,2 * LENGTH(cs:int list) + 2 EXP tl + 8]:(int64#num)list`;;

let fbd_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
  fse_valid cs tl /\ 5 <= tl /\ tl <= 12 /\ LENGTH(cs:int list) <= 256 /\
  LENGTH(tb0:byte list) = 4 * 2 EXP tl /\
  nonoverlapping (dt:int64,4 + 4 * 2 EXP tl) (nc:int64,2 * LENGTH cs) /\
  nonoverlapping (dt,4 + 4 * 2 EXP tl)
                 (wksp:int64,2 * LENGTH cs + 2 EXP tl + 8) /\
  nonoverlapping (wksp,2 * LENGTH cs + 2 EXP tl + 8) (nc,2 * LENGTH cs) /\
  nonoverlapping (dt,4 + 4 * 2 EXP tl) (word pc,32000) /\
  nonoverlapping (wksp,2 * LENGTH cs + 2 EXP tl + 8) (word pc,32000)`;;

let fbd_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [memory :> bytes(dt,4 + 4 * 2 EXP tl);
             memory :> bytes(wksp,2 * LENGTH(cs:int list) + 2 EXP tl + 8)]`;;

let fbd_vars =
 [`pc:num`; `returnaddress:int64`; `dt:int64`; `nc:int64`; `wksp:int64`;
  `cs:int list`; `tl:num`; `tb0:byte list`; `e:uarch_event list`];;

(*** The goal for a piece from pre to post, with the variables fbd_vars    ***)
(*** and extra quantified in this order                                    ***)

let mk_fbd_goal extra pre post =
  let tm = mk_imp(fbd_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; fbd_frame]) in
  let vs = fbd_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fbd_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** At the return: 0, with the header and the table ***)

let fbd_post = with_memsafe fbd_rr fbd_wr `\s.
  read PC s = returnaddress /\ read X0 s = word 0 /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_dtable cs tl)`;;

(*** At 0xe80, the entry, with the initial bytes tb0 of the table ***)

let fbd_entry = with_memsafe fbd_rr fbd_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0xe80) /\ read X30 s = returnaddress /\
  C_ARGUMENTS [dt; nc; word(LENGTH cs - 1); word tl; wksp; word wsz] s /\
  2 * LENGTH cs + 2 EXP tl + 8 <= wsz /\ wsz < 2 EXP 64 /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist tb0 /\
  read (memory :> bytes(nc,2 * LENGTH cs)) s =
  num_of_wordlist(MAP (iword:int->int16) cs)`;;

(*** At 0xf18, the loop over the counts: x5 is the last state not yet      ***)
(*** taken by a symbol of count -1 (highThreshold), x10 and x12 are the    ***)
(*** flags, and the workspace has the first next states                    ***)

let fbd_linv = with_memsafe fbd_rr fbd_wr `\m s. ?u.
  m = LENGTH cs - u /\ u < LENGTH cs /\
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0xf18) /\ read X30 s = returnaddress /\
  read X1 s = nc /\ read X4 s = wksp /\ read X9 s = word_add dt (word 4) /\
  read X14 s = dt /\ read X16 s = word(LENGTH cs - 1) /\
  read X17 s = word(LENGTH cs) /\ read X2 s = word(LENGTH cs - 1) /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\ read X11 s = word(2 EXP (tl - 1)) /\
  read X13 s = word(tl + 65536) /\ read X7 s = word u /\
  read X5 s = word(if fse_nlow cs u < 2 EXP tl
                   then (2 EXP tl - 1) - fse_nlow cs u else 4294967295) /\
  read X10 s = word(if fse_anyhigh cs u then 1 else 0) /\
  read X12 s = word(if fse_fastp cs tl u then 1 else 0) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0 (\v. 2 EXP tl - fse_nlow cs u <= v) 0) /\
  read (memory :> bytes(nc,2 * LENGTH cs)) s =
  num_of_wordlist(MAP (iword:int->int16) cs) /\
  read (memory :> bytes(wksp,2 * u)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) u)`;;

(*** At 0xf5c, the general spread, with x5 = H - 1 (or -1 if H = 0) ***)

let fbd_gen = with_memsafe fbd_rr fbd_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0xf5c) /\ read X30 s = returnaddress /\
  read X14 s = dt /\ read X9 s = word_add dt (word 4) /\ read X4 s = wksp /\
  read X1 s = nc /\ read X16 s = word(LENGTH cs - 1) /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\
  read X5 s = word(if LENGTH(fse_lowprob cs) < 2 EXP tl
                   then (2 EXP tl - LENGTH(fse_lowprob cs)) - 1
                   else 4294967295) /\
  ~(fse_lowprob cs = []) /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0
    (fse_placed tl (2 EXP tl - LENGTH(fse_lowprob cs)) 0) 0) /\
  read (memory :> bytes(nc,2 * LENGTH cs)) s =
  num_of_wordlist(MAP (iword:int->int16) cs) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) (LENGTH cs))`;;

(*** At 0xf70, 0xf88 and 0xfa0, with the symbol u in x13, the position of  ***)
(*** step j in x2 and i of the states of u done, for the measure (L - u) * ***)
(*** (2 * 2^tl + 4) + 2 * (2^tl - j) with L = LENGTH cs, plus 1 at 0xf70   ***)

let fbd_ginv = with_memsafe fbd_rr fbd_wr `\m s. ?u i j.
  u < LENGTH cs /\ j <= 2 EXP tl /\
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read X30 s = returnaddress /\
  read X14 s = dt /\ read X9 s = word_add dt (word 4) /\ read X4 s = wksp /\
  read X1 s = nc /\ read X16 s = word(LENGTH cs - 1) /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\
  read X5 s = word(if LENGTH(fse_lowprob cs) < 2 EXP tl
                   then (2 EXP tl - LENGTH(fse_lowprob cs)) - 1
                   else 4294967295) /\
  read X7 s = word(fse_step tl) /\
  read X13 s = word u /\ read X2 s = word(fse_pos tl j) /\
  (2 EXP tl <= LENGTH(fse_lowprob cs) ==> j = 0) /\
  ~(fse_lowprob cs = []) /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0
    (fse_placed tl (2 EXP tl - LENGTH(fse_lowprob cs)) j) 0) /\
  read (memory :> bytes(nc,2 * LENGTH cs)) s =
  num_of_wordlist(MAP (iword:int->int16) cs) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) (LENGTH cs)) /\
  (m = (LENGTH cs - u) * (2 * 2 EXP tl + 4) + 2 * (2 EXP tl - j) + 1 /\
   read PC s = word(pc + 0xf70) /\
   (LENGTH(fse_lowprob cs) < 2 EXP tl
    ==> fse_pos tl j < 2 EXP tl - LENGTH(fse_lowprob cs)) /\
   fse_ncell tl (2 EXP tl - LENGTH(fse_lowprob cs)) j = fse_cum cs u \/
   m = (LENGTH cs - u) * (2 * 2 EXP tl + 4) + 2 * (2 EXP tl - j) /\
   read PC s = word(pc + 0xf88) /\
   fse_pos tl j < 2 EXP tl - LENGTH(fse_lowprob cs) /\
   &1 <= EL u cs /\ i < num_of_int(EL u cs) /\
   read X8 s = word i /\ read X11 s = word(num_of_int(EL u cs)) /\
   read X12 s = word u /\
   fse_ncell tl (2 EXP tl - LENGTH(fse_lowprob cs)) j = fse_cum cs u + i \/
   m = (LENGTH cs - u) * (2 * 2 EXP tl + 4) + 2 * (2 EXP tl - j) /\
   read PC s = word(pc + 0xfa0) /\
   ~(fse_pos tl j < 2 EXP tl - LENGTH(fse_lowprob cs)) /\
   &1 <= EL u cs /\ i < num_of_int(EL u cs) /\
   read X8 s = word i /\ read X11 s = word(num_of_int(EL u cs)) /\
   read X12 s = word u /\
   fse_ncell tl (2 EXP tl - LENGTH(fse_lowprob cs)) j =
   fse_cum cs u + i + 1)`;;

(*** At 0x1034, the spread if no count is -1 ***)

let fbd_fast1 = with_memsafe fbd_rr fbd_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x1034) /\ read X30 s = returnaddress /\
  read X14 s = dt /\ read X9 s = word_add dt (word 4) /\ read X4 s = wksp /\
  read X1 s = nc /\ read X2 s = word(LENGTH cs - 1) /\
  read X17 s = word(LENGTH cs) /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\
  fse_lowprob cs = [] /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0 (fse_placed tl (2 EXP tl) 0) 0) /\
  read (memory :> bytes(nc,2 * LENGTH cs)) s =
  num_of_wordlist(MAP (iword:int->int16) cs) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) (LENGTH cs))`;;

(*** At 0x1060 and 0x1078, with the bytes of the symbols below u laid out  ***)
(*** (and i of those of u at 0x1078), for the measure (L - u) * (2^tl +    ***)
(*** 16) with L = LENGTH cs, minus i at 0x1078                             ***)

let fbd_f1inv = with_memsafe fbd_rr fbd_wr `\m s. ?u i.
  u < LENGTH cs /\
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read X30 s = returnaddress /\
  read X14 s = dt /\ read X9 s = word_add dt (word 4) /\ read X4 s = wksp /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\
  read X10 s = word_add wksp (word(2 * LENGTH cs)) /\
  read X11 s = word_add nc (word(2 * LENGTH cs)) /\
  read X12 s = word(2 EXP tl - 1) /\ read X13 s = word(fse_step tl) /\
  read X16 s = word 72340172838076673 /\
  read X7 s = word_add nc (word(2 * u)) /\ read X0 s = word(fse_cum cs u) /\
  read X2 s = word(u * 72340172838076673) /\
  fse_lowprob cs = [] /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0 (fse_placed tl (2 EXP tl) 0) 0) /\
  read (memory :> bytes(nc,2 * LENGTH cs)) s =
  num_of_wordlist(MAP (iword:int->int16) cs) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) (LENGTH cs)) /\
  (m = (LENGTH cs - u) * (2 EXP tl + 16) /\ read PC s = word(pc + 0x1060) /\
   read (memory :> bytes(word_add wksp (word(2 * LENGTH cs)),fse_cum cs u)) s =
   num_of_bytelist(MAP word (fse_symsp cs u)) \/
   m = (LENGTH cs - u) * (2 EXP tl + 16) - i /\
   read PC s = word(pc + 0x1078) /\
   8 <= i /\ i < num_of_int(EL u cs) /\
   read X5 s = word(num_of_int(EL u cs)) /\ read X1 s = word i /\
   read X8 s =
   word_add (word_add wksp (word(2 * LENGTH cs))) (word(fse_cum cs u)) /\
   read (memory :> bytes(word_add wksp (word(2 * LENGTH cs)),
                         fse_cum cs u + i)) s =
   num_of_bytelist(APPEND (MAP word (fse_symsp cs u))
                          (REPLICATE i (word u))))`;;

(*** At 0x109c, with the symbols laid out ***)

let fbd_fast2 = with_memsafe fbd_rr fbd_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x109c) /\ read X30 s = returnaddress /\
  read X14 s = dt /\ read X9 s = word_add dt (word 4) /\ read X4 s = wksp /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\
  read X10 s = word_add wksp (word(2 * LENGTH cs)) /\
  read X12 s = word(2 EXP tl - 1) /\ read X13 s = word(fse_step tl) /\
  fse_lowprob cs = [] /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0 (fse_placed tl (2 EXP tl) 0) 0) /\
  read (memory :> bytes(word_add wksp (word(2 * LENGTH cs)),2 EXP tl)) s =
  num_of_bytelist(MAP word (fse_syms cs)) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) (LENGTH cs))`;;

(*** At 0x10ac, with the symbols of steps below 2k placed, for the measure ***)
(*** 2^tl - 2k                                                             ***)

let fbd_f2inv = with_memsafe fbd_rr fbd_wr `\m s. ?k.
  m = 2 EXP tl - 2 * k /\ 2 * k < 2 EXP tl /\
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x10ac) /\ read X30 s = returnaddress /\
  read X14 s = dt /\ read X9 s = word_add dt (word 4) /\ read X4 s = wksp /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\
  read X10 s = word_add wksp (word(2 * LENGTH cs)) /\
  read X8 s = word_add (word_add wksp (word(2 * LENGTH cs))) (word 1) /\
  read X11 s = word(2 EXP tl) /\
  read X12 s = word(2 EXP tl - 1) /\ read X13 s = word(fse_step tl) /\
  read X0 s = word(2 * k) /\ read X1 s = word(fse_pos tl (2 * k)) /\
  fse_lowprob cs = [] /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0 (fse_placed tl (2 EXP tl) (2 * k)) 0) /\
  read (memory :> bytes(word_add wksp (word(2 * LENGTH cs)),2 EXP tl)) s =
  num_of_bytelist(MAP word (fse_syms cs)) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) (LENGTH cs))`;;

(*** At 0xfd8, with all the symbols placed ***)

let fbd_build = with_memsafe fbd_rr fbd_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0xfd8) /\ read X30 s = returnaddress /\
  read X14 s = dt /\ read X9 s = word_add dt (word 4) /\ read X4 s = wksp /\
  read X3 s = word tl /\ read X6 s = word(2 EXP tl - 1) /\
  read X15 s = word(2 EXP tl) /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0 (\x. T) 0) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq (\i. word(fse_init cs i):int16) (LENGTH cs))`;;

(*** At 0xff0, with the entries of the states below u done and the next    ***)
(*** states of the symbols counting those states, for the measure 2^tl - u ***)

let fbd_binv = with_memsafe fbd_rr fbd_wr `\m s. ?u.
  m = 2 EXP tl - u /\ u < 2 EXP tl /\
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0xff0) /\ read X30 s = returnaddress /\
  read X9 s = word_add dt (word(4 + 4 * u)) /\
  read X6 s = word_add dt (word(4 + 4 * 2 EXP tl)) /\
  read X4 s = wksp /\ read X3 s = word tl /\ read X15 s = word(2 EXP tl) /\
  read X7 s = word 31 /\
  read (memory :> bytes32 dt) s = word(tl + 65536 * fse_fast cs tl) /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_tbl cs tl tb0 (\x. T) u) /\
  read (memory :> bytes(wksp,2 * LENGTH cs)) s =
  num_of_wordlist(list_of_seq
    (\i. word(fse_init cs i +
              CARD {v | v < u /\ fse_symbol cs tl v = i}):int16)
    (LENGTH cs))`;;

(* ------------------------------------------------------------------------- *)
(* Tactics. Each piece abbreviates tt = 2^tl (FBD_ABBREV_TAC), since         *)
(* NONOVERLAPPING_TAC does not use facts with EXP of variables, and undoes   *)
(* it (FBD_UNABBREV_TAC) before going on with a later piece, whose           *)
(* hypotheses have 2 EXP tl. The simulation rewrites register values with    *)
(* all the equations and equivalences among the assumptions, so these        *)
(* rewrite assumptions selectively (FBD_ASSUME_REWRITE_TAC) and set the      *)
(* value of a register in a chosen form (FBD_SET_REG_TAC).                   *)
(* ------------------------------------------------------------------------- *)

let FBD_ABBREV_TAC =
  ABBREV_TAC `tt = 2 EXP tl` THEN
  SUBGOAL_THEN `32 <= tt /\ tt <= 4096` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN
    SUBGOAL_THEN `2 EXP 5 <= 2 EXP tl /\ 2 EXP tl <= 2 EXP 12` MP_TAC THENL
     [REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[]];
    ALL_TAC];;

let FBD_EXPAND_TT_TAC =
  FIRST_ASSUM(fun th -> if concl th = `2 EXP tl = tt`
                        then REWRITE_TAC[SYM th] else NO_TAC);;

let TRY_ANTS_TAC tac = TRY(ANTS_TAC THENL [tac; ALL_TAC]);;

let FBD_UNABBREV_TAC =
  FIRST_X_ASSUM(fun th ->
    if concl th = `2 EXP tl = tt`
    then RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) THEN REWRITE_TAC[SYM th]
    else NO_TAC);;

let FBD_ARITH_TAC : tactic = fun (asl,w as gl) ->
  try SIMPLE_ARITH_TAC gl with Failure _ ->
    failwith ("FBD_ARITH_TAC: " ^ string_of_term w);;

let FBD_ASSUME_REWRITE_TAC tms =
  RULE_ASSUM_TAC(fun th ->
    if mem (concl th) tms then th else REWRITE_RULE (map ASSUME tms) th);;

let FBD_CONTR_TAC : tactic = fun (asl,w as gl) ->
  let ths = map snd asl in
  let th = tryfind (fun th ->
      let c = concl th in
      if is_neg c then
        let th' = find (fun t -> concl t = rand c) ths in
        MP (NOT_ELIM th) th'
      else failwith "FBD_CONTR_TAC") ths in
  CONTR_TAC th gl;;

let FBD_SET_REG_TAC tm tac =
  SUBGOAL_THEN tm (fun th ->
    let l = lhs(concl th) in
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
      (fun th' -> is_eq(concl th') && lhs(concl th') = l))) THEN
    ASSUME_TAC th) THENL [tac; ALL_TAC];;

let FBD_CUR_STATE (asl,w) = rand w;;

(*** The store of the symbol b of the state v, at the address addr in the  ***)
(*** state s, with the table split around that byte, from P to P with v    ***)

let FBD_SYM_STORE_TAC P v addr b s =
  MP_TAC(ISPECL [`word_add dt (word 4):int64`;
    list_mk_icomb "fse_tbl" [`cs:int list`; `tl:num`; `tb0:byte list`; P;
                             `0`];
    list_mk_icomb "fse_tbl" [`cs:int list`; `tl:num`; `tb0:byte list`;
      mk_abs(`x:num`,mk_disj(mk_comb(P,`x:num`),mk_eq(`x:num`,v)));
      `0`];
    mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `4` v) `2`;
    addr; b; s] READ_MEMORY_BYTELIST_UPDATE1) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      SIMPLE_ARITH_TAC;
      MP_TAC(ISPECL [`cs:int list`; `tl:num`; `tb0:byte list`; P; v;
        mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `4` v)
                 `2`] FSE_TBL_SYM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `idx:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`cs:int list`; `tl:num`; `tb0:byte list`; P; v;
        `idx:num`] FSE_TBL_SYM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC];;

(*** The conjuncts of an invariant at the end of an iteration, with dtac   ***)
(*** choosing the disjunct                                                 ***)

let FBD_DISJ_FINISH_TAC dtac =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         dtac THEN ASM_REWRITE_TAC[] THEN FBD_ARITH_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         FBD_ARITH_TAC];;

(*** The measure in terms of w = LENGTH cs - (u + 1) ***)

let FBD_W_TAC =
  ABBREV_TAC `w = LENGTH(cs:int list) - (u + 1)` THEN
  SUBGOAL_THEN `LENGTH(cs:int list) - u = w + 1`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
              ASSUME_TAC th) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC];;

(*** Facts about the positions of the walk, and the masks with 2^tl - 1 of ***)
(*** the code, and the bounds of the positions in the assumptions, for the ***)
(*** small-word rules                                                      ***)

let FBD_POS_FACTS_TAC =
  SUBGOAL_THEN
   `(!a. word_and (word a) (word(tt - 1)):int64 = word(a MOD tt)) /\
    (!a. word_and (word(tt - 1)) (word a):int64 = word(a MOD tt)) /\
    (!a. word_and (word a) (word(tt - 1)):int32 = word(a MOD tt)) /\
    (!a. word_and (word(tt - 1)) (word a):int32 = word(a MOD tt)) /\
    (!j. fse_pos tl j MOD tt = fse_pos tl j) /\
    (!j. (fse_pos tl j + fse_step tl) MOD tt = fse_pos tl (j + 1)) /\
    (!j. (fse_step tl + fse_pos tl j) MOD tt = fse_pos tl (j + 1)) /\
    (!j. (fse_step tl + (fse_step tl + fse_pos tl j)) MOD tt =
         fse_pos tl (j + 2)) /\
    (!j. fse_pos tl j < tt)`
  STRIP_ASSUME_TAC THENL
   [FBD_EXPAND_TT_TAC THEN
    SIMP_TAC[WORD_AND_POW2_WORD; DIMINDEX_64; DIMINDEX_32;
             ARITH_RULE `tl <= 12 ==> tl <= 64 /\ tl <= 32`;
             ASSUME `tl <= 12`] THEN
    REWRITE_TAC[FSE_POS_SUC; FSE_POS_LT] THEN
    SIMP_TAC[MOD_LT; FSE_POS_LT];
    ALL_TAC];;

let FBD_POS_LT_TAC : tactic = fun (asl,w as gl) ->
  let is_pos t = match t with
      Comb(Comb(Const("fse_pos",_),_),_) -> true | _ -> false in
  let pts = setify(itlist (fun (_,th) acc ->
              find_terms is_pos (concl th) @ acc) asl []) in
  let have = map (concl o snd) asl in
  let lt = snd(find (fun (_,th) -> concl th = `!j. fse_pos tl j < tt`) asl) in
  let new_facts = mapfilter (fun t ->
     let th = SPEC (rand t) lt in
     if mem (concl th) have then failwith "" else th) pts in
  MAP_EVERY ASSUME_TAC new_facts gl;;

let FBD_NORM1_TAC =
  W(fun (asl,w) ->
    let ths = filter (fun th -> is_forall(concl th)) (map snd asl) in
    RULE_ASSUM_TAC(fun th ->
      if is_forall(concl th) then th else REWRITE_RULE ths th)) THEN
  FBD_POS_LT_TAC THEN ZSTD_SMALL_WORD_TAC;;

let FBD_NORM_TAC = FBD_POS_LT_TAC THEN ZSTD_SMALL_WORD_TAC THEN
                   FBD_NORM1_TAC THEN FBD_NORM1_TAC;;

(* ------------------------------------------------------------------------- *)
(* The building of the entries (0xfd8). The entry of the state u has the     *)
(* number of bits nb = tl - (31 - clz(x)) and the baseline (x << nb) - 2^tl, *)
(* for the next state x of its symbol, which is then incremented.            *)
(* ------------------------------------------------------------------------- *)

let FBD_BUILD = prove
 (mk_fbd_goal [] fbd_build fbd_post,
  ZSTD_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC fbd_binv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--6) THEN
    SUBGOAL_THEN `word_add (word_add dt (word 8)) (word (4 * (tt - 1))):int64 =
                  word_add dt (word(4 + 4 * tt))`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `tt - 0` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES; ADD_CLAUSES;
                    MULT_CLAUSES] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN ENSURES_EXISTS_PRE_TAC `u:num` THEN
  FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `u:num`] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `u:num`] FSE_NBITS_BASE) THEN
  ASM_REWRITE_TAC[EXP_ADD; EXP_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= bitsize(fse_next cs tl u) /\
                bitsize(fse_next cs tl u) <= tl + 1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE; LE_BITSIZE; ARITH_EQ; SUB_REFL; EXP] THEN
    ASM_REWRITE_TAC[EXP_ADD; EXP_1] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tl - (31 - (32 - bitsize(fse_next cs tl u))) =
                fse_nbits cs tl u` ASSUME_TAC THENL
   [REWRITE_TAC[fse_nbits] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fse_base cs tl u =
                2 EXP (fse_nbits cs tl u) * fse_next cs tl u - tt`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[fse_base]; ALL_TAC] THEN
  MP_TAC(ISPECL [`dt:int64`; `cs:int list`; `tl:num`; `tb0:byte list`;
    `\x:num. T`; `u:num`; `s0:armstate`] FSE_TBL_READ_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`word_add dt (word 4):int64`; `fse_tbl cs tl tb0 (\x. T) u`;
    `4 * u`; `4`; `s0:armstate`] READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`wksp:int64`; `list_of_seq (\i. word(fse_init cs i +
      CARD {v | v < u /\ fse_symbol cs tl v = i}):int16)
      (LENGTH(cs:int list))`;
    `fse_symbol cs tl u`; `s0:armstate`] READ_MEMORY_WORDLIST16_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; GSYM FSE_NEXT_INIT] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `u:num`] FSE_NEXT_INIT) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `sy = fse_symbol cs tl u` THEN
  ABBREV_TAC `x = fse_next cs tl u` THEN
  ZSTD_STEPS_TAC (1--14) THEN
  SUBGOAL_THEN `word_add (word_add dt (word (4 + 4 * u))) (word 4):int64 =
                word_add dt (word(4 + 4 * (u + 1)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub (word_add dt (word (4 + 4 * tt)))
                   (word_add dt (word (4 + 4 * (u + 1)))):int64) = 0 <=>
                u + 1 = tt`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PTR_EQ_OFFSETS o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP fse_nbits cs tl u * x - tt < 65536 /\ sy < 256 /\
                fse_nbits cs tl u < 256`
  STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add (word_add dt (word 4)) (word(4 * u)),4))
         s14 =
    num_of_bytelist (SUB_LIST (4 * u,4) (fse_tbl cs tl tb0 (\x. T) (u + 1)))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`cs:int list`; `tl:num`; `tb0:byte list`; `u:num`]
      FSE_TBL_ENTRY_VAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add dt (word 4)) (word (4 * u)):int64 =
      word_add dt (word(4 + 4 * u))`;
     READ_MEMORY_BYTES4_SPLIT] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 4 * tt /\ ~(4 * u <= j /\ j < 4 * u + 4)
        ==> EL j (fse_tbl cs tl tb0 (\x. T) (u + 1)) =
            EL j (fse_tbl cs tl tb0 (\x. T) u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`cs:int list`; `tl:num`; `tb0:byte list`; `u:num`; `j:num`]
      FSE_TBL_BUILD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add dt (word 4):int64`; `fse_tbl cs tl tb0 (\x. T) u`;
    `fse_tbl cs tl tb0 (\x. T) (u + 1)`; `4 * u`; `4`; `s14:armstate`]
    READ_MEMORY_BYTELIST_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!i. i < LENGTH cs /\ ~(i = sy)
        ==> EL i (list_of_seq (\i. word(fse_init cs i +
                    CARD {v | v < u + 1 /\ fse_symbol cs tl v = i}):int16)
                  (LENGTH cs)) =
            EL i (list_of_seq (\i. word(fse_init cs i +
                    CARD {v | v < u /\ fse_symbol cs tl v = i}):int16)
                  (LENGTH cs))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; CARD_RESTRICT_LT_ADD1] THEN
    REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wksp:int64`;
    `list_of_seq (\i. word(fse_init cs i +
       CARD {v | v < u /\ fse_symbol cs tl v = i}):int16)
       (LENGTH(cs:int list))`;
    `list_of_seq (\i. word(fse_init cs i +
       CARD {v | v < u + 1 /\ fse_symbol cs tl v = i}):int16)
       (LENGTH(cs:int list))`;
    `sy:num`; `s14:armstate`] READ_MEMORY_WORDLIST16_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ; CARD_RESTRICT_LT_ADD1] THEN
    REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ASM_CASES_TAC `u + 1 = tt` THENL
   [ZSTD_STEPS_TAC (15--17) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN `fse_tbl cs tl tb0 (\x. T) (u + 1) = fse_dtable cs tl`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ASSUME `u + 1 = tt`] THEN FBD_EXPAND_TT_TAC THEN
      REWRITE_TAC[FSE_TBL_FULL];
      ASM_REWRITE_TAC[]];
    ZSTD_STEPS_TAC [15] THEN PUFF_FINAL_TAC THEN
    DISJ1_TAC THEN EXISTS_TAC `tt - (u + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `u + 1`] THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The second part of the spread if no count is -1 (0x109c): the symbols     *)
(* laid out in order are given to the states of steps 2k and 2k + 1 of the   *)
(* walk.                                                                     *)
(* ------------------------------------------------------------------------- *)

let FBD_FAST2 = prove
 (mk_fbd_goal [] fbd_fast2 fbd_post,
  ZSTD_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC fbd_f2inv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--4) THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `tt - 2 * 0` THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; FSE_POS_0] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN ENSURES_EXISTS_PRE_TAC `k:num` THEN
  FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN FBD_POS_FACTS_TAC THEN
  SUBGOAL_THEN `2 * k + 2 <= tt` ASSUME_TAC THENL
   [SUBGOAL_THEN `EVEN tt` MP_TAC THENL
     [FBD_EXPAND_TT_TAC THEN REWRITE_TAC[EVEN_EXP; ARITH_EVEN] THEN
      SIMPLE_ARITH_TAC;
      REWRITE_TAC[EVEN_EXISTS] THEN DISCH_THEN(X_CHOOSE_TAC `d:num`) THEN
      UNDISCH_TAC `2 * k < tt` THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; ARITH_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(fse_syms cs) = tt` ASSUME_TAC THENL
   [UNDISCH_TAC `fse_valid cs tl` THEN
    ASM_REWRITE_TAC[fse_valid; LENGTH; ADD_CLAUSES] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_pos tl (2 * k) < tt /\ fse_pos tl (2 * k + 1) < tt`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `2 * k`] FSE_SYMBOL_POS) THEN
  REWRITE_TAC[ASSUME `fse_lowprob cs = []`; LENGTH; SUB_0; FSE_NCELL_ALL;
              FSE_POS_LT] THEN
  ASM_REWRITE_TAC[] THEN TRY_ANTS_TAC SIMPLE_ARITH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `2 * k + 1`] FSE_SYMBOL_POS) THEN
  REWRITE_TAC[ASSUME `fse_lowprob cs = []`; LENGTH; SUB_0; FSE_NCELL_ALL;
              FSE_POS_LT] THEN
  ASM_REWRITE_TAC[] THEN TRY_ANTS_TAC SIMPLE_ARITH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `2 * k`] EL_FSE_SYMS_POS) THEN
  ASM_REWRITE_TAC[] THEN TRY_ANTS_TAC SIMPLE_ARITH_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `2 * k + 1`] EL_FSE_SYMS_POS) THEN
  ASM_REWRITE_TAC[] THEN TRY_ANTS_TAC SIMPLE_ARITH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(fse_pos tl (2 * k) = fse_pos tl (2 * k + 1))` ASSUME_TAC
  THENL
   [REWRITE_TAC[fse_pos] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`tl:num`; `2 * k`; `2 * k + 1`] FSE_POS_INJ) THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add wksp (word(2 * LENGTH(cs:int list))):int64`;
    `MAP (word:num->byte) (fse_syms cs)`; `2 * k`; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN TRY_ANTS_TAC SIMPLE_ARITH_TAC THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE(LAND_CONV(TOP_DEPTH_CONV
    NORMALIZE_RELATIVE_ADDRESS_CONV))) THEN
  MP_TAC(ISPECL [`word_add wksp (word(2 * LENGTH(cs:int list))):int64`;
    `MAP (word:num->byte) (fse_syms cs)`; `1 + 2 * k`; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN TRY_ANTS_TAC SIMPLE_ARITH_TAC THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE(LAND_CONV(TOP_DEPTH_CONV
    NORMALIZE_RELATIVE_ADDRESS_CONV))) THEN
  SUBGOAL_THEN `2 * k < LENGTH(fse_syms cs) /\ 1 + 2 * k < LENGTH(fse_syms cs)`
   (fun th -> RULE_ASSUM_TAC(SIMP_RULE[EL_MAP; th])) THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!l:num list. EL (1 + 2 * k) l = EL (2 * k + 1) l`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add dt (word 4):int64`;
    `fse_tbl cs tl tb0 (fse_placed tl tt (2 * k)) 0`;
    `4 * fse_pos tl (2 * k) + 2`; `1`; `s0:armstate`]
    READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  ZSTD_STEPS_TAC (1--9) THEN
  FBD_SYM_STORE_TAC `fse_placed tl tt (2 * k)` `fse_pos tl (2 * k)`
    `word_add dt (word (4 + 4 * fse_pos tl (2 * k) + 2)):int64`
    `word (EL (2 * k) (fse_syms cs)):byte` `s9:armstate` THEN
  MP_TAC(ISPECL [`cs:int list`; `tl:num`; `tb0:byte list`; `tt:num`;
    `2 * k`] FSE_TBL_PLACED_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`word_add dt (word 4):int64`;
    `fse_tbl cs tl tb0 (fse_placed tl tt (2 * k + 1)) 0`;
    `4 * fse_pos tl (2 * k + 1) + 2`; `1`; `s9:armstate`]
    READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  ZSTD_STEPS_TAC (10--12) THEN
  FBD_SYM_STORE_TAC `fse_placed tl tt (2 * k + 1)` `fse_pos tl (2 * k + 1)`
    `word_add dt (word (4 + 4 * fse_pos tl (2 * k + 1) + 2)):int64`
    `word (EL (2 * k + 1) (fse_syms cs)):byte` `s12:armstate` THEN
  MP_TAC(ISPECL [`cs:int list`; `tl:num`; `tb0:byte list`; `tt:num`;
    `2 * k + 1`] FSE_TBL_PLACED_STEP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(2 * k + 1) + 1 = 2 * k + 2`] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `2 * k + 2 = tt` THENL
   [ZSTD_STEPS_TAC (13--15) THEN
    SUBGOAL_THEN `fse_tbl cs tl tb0 (fse_placed tl tt (2 * k + 2)) 0 =
                  fse_tbl cs tl tb0 (\x. T) 0`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC FSE_TBL_PLACED_ALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FBD_UNABBREV_TAC THEN ZSTD_CONTINUE_TAC FBD_BUILD [] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];
    ZSTD_STEPS_TAC (13--14) THEN PUFF_FINAL_TAC THEN
    DISJ1_TAC THEN EXISTS_TAC `tt - 2 * (k + 1)` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; EXISTS_TAC `k + 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 * (k + 1) = 2 * k + 2`] THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The first part (0x1034): the symbol u, with count c, is written out as c  *)
(* bytes at the end of those of the symbols below it, with 8 bytes stored at *)
(* a time (the last store going up to 7 bytes beyond).                       *)
(* ------------------------------------------------------------------------- *)

let FBD_F1_TRUNC_TAC ifv st =
  MP_TAC(ISPECL [`word_add wksp (word(2 * LENGTH(cs:int list))):int64`;
    mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,
      `MAP (word:num->byte) (fse_symsp cs u)`),
      list_mk_icomb "REPLICATE" [ifv; `word u:byte`]);
    mk_binop `(+):num->num->num` `fse_cum cs u` ifv;
    `fse_cum cs u + c`; st] READ_MEMORY_BYTES_TRUNC) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_FSE_SYMSP;
              LENGTH_REPLICATE] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMPLE_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`MAP (word:num->byte) (fse_symsp cs u)`; `word u:byte`;
                 `c:num`; ifv] SUB_LIST_APPEND_REPLICATE) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_FSE_SYMSP] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `APPEND (MAP word (fse_symsp cs u)) (REPLICATE c (word u)) =
                MAP (word:num->byte) (fse_symsp cs (u + 1))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[FSE_SYMSP_SUC; MAP_APPEND; MAP_REPLICATE;
                 INT_ARITH `&0:int <= x ==> max x (&0) = x`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let FBD_F1_NEXT_TAC =
  SUBGOAL_THEN `word_add (word_add nc (word (2 * u))) (word 2):int64 =
                word_add nc (word(2 * (u + 1)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub (word_add nc (word (2 * LENGTH(cs:int list))))
                   (word_add nc (word (2 * (u + 1)))):int64) = 0 <=>
                u + 1 = LENGTH cs`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PTR_EQ_OFFSETS o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
    ALL_TAC];;

let FBD_F1_EXIT_TAC =
  SUBGOAL_THEN `fse_cum cs (u + 1) = tt /\ fse_symsp cs (u + 1) = fse_syms cs`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_FSE_SYMS; GSYM FSE_SYMS_SYMSP] THEN
    UNDISCH_TAC `fse_valid cs tl` THEN
    ASM_REWRITE_TAC[fse_valid; LENGTH; ADD_CLAUSES] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FBD_UNABBREV_TAC THEN ZSTD_CONTINUE_TAC FBD_FAST2 [] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];;

let FBD_F1_LOOP_TAC =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `w * (tt + 16)` THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `u * k + k = (u + 1) * k`]) THEN
  MAP_EVERY EXISTS_TAC [`u + 1`; `0`] THEN
  FBD_DISJ_FINISH_TAC DISJ1_TAC;;

let FBD_FAST1 = prove
 (mk_fbd_goal [] fbd_fast1 fbd_post,
  ZSTD_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC fbd_f1inv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--11) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_VALID_LENGTH) THEN
    SUBGOAL_THEN
     `word_add (word_add nc (word 2)) (word (2 * (LENGTH cs - 1))):int64 =
      word_add nc (word(2 * LENGTH(cs:int list))) /\
      (tt DIV 8 + tt DIV 2) + 3 = fse_step tl`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        REWRITE_TAC[fse_step] THEN FBD_EXPAND_TT_TAC THEN ARITH_TAC];
      ALL_TAC] THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(LENGTH(cs:int list) - 0) * (tt + 16)` THEN
    MAP_EVERY EXISTS_TAC [`0`; `0`] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; fse_cum; FSE_SYMSP_0; MAP;
                    READ_MEMORY_BYTES_0; num_of_bytelist] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `u:num` THEN ENSURES_EXISTS_PRE_TAC `i:num` THEN
  FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN FBD_POS_FACTS_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_VALID_LENGTH) THEN
  SUBGOAL_THEN `&0 <= EL u (cs:int list)` ASSUME_TAC THENL
   [UNDISCH_TAC `fse_valid cs tl` THEN
    REWRITE_TAC[fse_valid; GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(EL u (cs:int list) = -- &1)` MP_TAC THENL
     [ASM_MESON_TAC[MEM_FSE_LOWPROB; MEM]; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_cum cs u + num_of_int(EL u cs) = fse_cum cs (u + 1) /\
                fse_cum cs (u + 1) <= tt`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`cs:int list`; `u + 1`; `LENGTH(cs:int list)`]
      FSE_CUM_MONO) THEN
    UNDISCH_TAC `fse_valid cs tl` THEN
    ASM_REWRITE_TAC[fse_valid; LENGTH; ADD_CLAUSES; GSYM LENGTH_FSE_SYMS;
                    ARITH_RULE `u + 1 <= n <=> u < n`] THEN
    ASM_SIMP_TAC[FSE_CUM_SUC; INT_ARITH `&0:int <= x ==> max x (&0) = x`];
    ALL_TAC] THEN
  ABBREV_TAC `c = num_of_int(EL u (cs:int list))` THEN
  MP_TAC(ISPECL [`nc:int64`; `MAP (iword:int->int16) cs`;
                 `LENGTH(cs:int list)`; `u:num`; `s0:armstate`]
    READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN
  SUBGOAL_THEN `iword(EL u cs):int16 = word c` SUBST1_TAC THENL
   [MP_TAC(ISPEC `EL u (cs:int list)` INT_OF_NUM_OF_INT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[WORD_IWORD];
    DISCH_TAC] THEN
  SUBGOAL_THEN `c <= tt /\ u < 256` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check
   (fun th -> is_disj(concl th) && free_in `PC` (concl th))) THENL
   [ZSTD_STEPS_TAC (1--3) THEN
    MP_TAC(ISPECL [`word_add wksp (word(2 * LENGTH(cs:int list))):int64`;
      `MAP (word:num->byte) (fse_symsp cs u)`; `fse_cum cs u`;
      `word_add wksp (word (2 * LENGTH cs + fse_cum cs u)):int64`;
      `u:num`; `s3:armstate`] READ_MEMORY_BYTELIST_APPEND64) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_FSE_SYMSP] THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      DISCH_TAC] THEN
    ASM_CASES_TAC `c <= 8` THENL
     [ZSTD_STEPS_TAC (4--6) THEN FBD_F1_TRUNC_TAC `8` `s6:armstate` THEN
      ZSTD_STEPS_TAC (7--10) THEN FBD_F1_NEXT_TAC THEN
      ASM_CASES_TAC `u + 1 = LENGTH(cs:int list)` THENL
       [ZSTD_STEPS_TAC [11] THEN FBD_F1_EXIT_TAC;
        FBD_W_TAC THEN ZSTD_STEPS_TAC [11] THEN FBD_F1_LOOP_TAC];
      ZSTD_STEPS_TAC (4--6) THEN FBD_W_TAC THEN
      PUFF_FINAL_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `(w + 1) * (tt + 16) - 8` THEN
      CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`u:num`; `8`] THEN
      FBD_DISJ_FINISH_TAC DISJ2_TAC];
    ZSTD_STEPS_TAC [1] THEN
    MP_TAC(ISPECL [`word_add wksp (word(2 * LENGTH(cs:int list))):int64`;
      `APPEND (MAP (word:num->byte) (fse_symsp cs u)) (REPLICATE i (word u))`;
      `fse_cum cs u + i`;
      `word_add wksp (word (2 * LENGTH cs + fse_cum cs u + i)):int64`;
      `u:num`; `s1:armstate`] READ_MEMORY_BYTELIST_APPEND64) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_FSE_SYMSP;
                      LENGTH_REPLICATE] THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      REWRITE_TAC[GSYM APPEND_ASSOC; GSYM REPLICATE_ADD; GSYM ADD_ASSOC] THEN
      DISCH_TAC] THEN
    ASM_CASES_TAC `i + 8 < c` THEN ZSTD_STEPS_TAC (2--4) THENL
     [FBD_W_TAC THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `(w + 1) * (tt + 16) - (i + 8)` THEN
      CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`u:num`; `i + 8`] THEN
      FBD_DISJ_FINISH_TAC DISJ2_TAC;
      FBD_F1_TRUNC_TAC `i + 8` `s4:armstate` THEN
      ZSTD_STEPS_TAC (5--8) THEN FBD_F1_NEXT_TAC THEN
      ASM_CASES_TAC `u + 1 = LENGTH(cs:int list)` THENL
       [ZSTD_STEPS_TAC [9] THEN FBD_F1_EXIT_TAC;
        FBD_W_TAC THEN ZSTD_STEPS_TAC [9] THEN FBD_F1_LOOP_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* The general spread (0xf5c): the symbol u is placed at the states of the   *)
(* next c steps of the walk that are below H, skipping those above, c being  *)
(* its count. After the last symbol the walk has done 2^tl steps             *)
(* (FSE_WALK_END), so the position is 0 again, and the check in the code     *)
(* that it is succeeds.                                                      *)
(* ------------------------------------------------------------------------- *)

let FBD_GS_EXIT_TAC jv =
  SUBGOAL_THEN
   (subst [jv,`jj:num`]
     `fse_tbl cs tl tb0 (fse_placed tl (tt - LENGTH(fse_lowprob cs)) jj) 0 =
      fse_tbl cs tl tb0 (\x. T) 0`)
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC FSE_TBL_PLACED_ALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FBD_UNABBREV_TAC THEN ZSTD_CONTINUE_TAC FBD_BUILD [] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];;

let FBD_GA_SKIP_TAC =
  ASM_CASES_TAC `u + 1 = LENGTH(cs:int list)` THENL
   [SUBGOAL_THEN `fse_cum cs u = tt - LENGTH(fse_lowprob cs)` ASSUME_TAC THENL
     [UNDISCH_TAC `fse_cum cs (u + 1) = fse_cum cs u` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(tt - LENGTH(fse_lowprob cs) = 0 \/ j = 2 EXP tl) /\
                  fse_pos tl j = 0`
    (CONJUNCTS_THEN ASSUME_TAC) THENL
     [ASM_CASES_TAC `tt <= LENGTH(fse_lowprob cs)` THENL
       [FIRST_X_ASSUM(fun th ->
          if is_imp(concl th) &&
             lhand(concl th) = `tt <= LENGTH(fse_lowprob cs)`
          then MP_TAC th else NO_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[FSE_POS_0] THEN DISJ1_TAC THEN FBD_ARITH_TAC;
        SUBGOAL_THEN `fse_pos tl j < tt - LENGTH(fse_lowprob cs)` ASSUME_TAC
        THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            is_imp(concl th) && is_binary "<" (lhand(concl th)))) THEN
          FBD_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `j = 2 EXP tl` ASSUME_TAC THENL
         [MATCH_MP_TAC FSE_WALK_END THEN
          EXISTS_TAC `tt - LENGTH(fse_lowprob cs)` THEN
          ASM_REWRITE_TAC[] THEN FBD_ARITH_TAC;
          REWRITE_TAC[ASSUME `j = 2 EXP tl`; FSE_POS_FULL]]];
      ALL_TAC] THEN
    ZSTD_STEPS_TAC (6--10) THEN FBD_GS_EXIT_TAC `j:num`;
    FBD_W_TAC THEN ZSTD_STEPS_TAC (6--10) THEN PUFF_FINAL_TAC THEN
    DISJ1_TAC THEN EXISTS_TAC `w * (2 * tt + 4) + 2 * (tt - j) + 1` THEN
    CONJ_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u + 1`; `0`; `j:num`] THEN
    FBD_DISJ_FINISH_TAC DISJ1_TAC];;

let FBD_GA_TAC =
  MP_TAC(ISPECL [`nc:int64`; `MAP (iword:int->int16) cs`;
                 `LENGTH(cs:int list)`; `u:num`; `s0:armstate`]
    READ_MEMORY_BYTES16_WORDLIST_VAL) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN FBD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `EL u (cs:int list) = -- &1` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    DISCH_TAC THEN ZSTD_STEPS_TAC (1--5) THEN
    SUBGOAL_THEN `fse_cum cs (u + 1) = fse_cum cs u` ASSUME_TAC THENL
     [REWRITE_TAC[FSE_CUM_SUC] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[INT_ARITH `max (-- &1:int) (&0) = &0`; NUM_OF_INT_OF_NUM;
                  ADD_CLAUSES];
      ALL_TAC] THEN
    FBD_GA_SKIP_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= EL u (cs:int list)` ASSUME_TAC THENL
   [UNDISCH_TAC `fse_valid cs tl` THEN
    REWRITE_TAC[fse_valid; GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `EL u (cs:int list)` INT_OF_NUM_OF_INT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = num_of_int(EL u (cs:int list))` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; GSYM WORD_IWORD] THEN
                       ASSUME_TAC th) THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `c = 0` THENL
   [ZSTD_STEPS_TAC (1--5) THEN
    SUBGOAL_THEN `fse_cum cs (u + 1) = fse_cum cs u` ASSUME_TAC THENL
     [REWRITE_TAC[FSE_CUM_SUC] THEN
      REWRITE_TAC[SYM(ASSUME `&c = EL u (cs:int list)`); ASSUME `c = 0`] THEN
      REWRITE_TAC[INT_ARITH `max (&0:int) (&0) = &0`; NUM_OF_INT_OF_NUM;
                  ADD_CLAUSES];
      ALL_TAC] THEN
    FBD_GA_SKIP_TAC;
    SUBGOAL_THEN `fse_cum cs (u + 1) = fse_cum cs u + c /\
                  fse_cum cs (u + 1) <= fse_cum cs (LENGTH cs)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FSE_CUM_SUC; SYM(ASSUME `&c = EL u (cs:int list)`)] THEN
        REWRITE_TAC[INT_ARITH `max (&c:int) (&0) = &c`; NUM_OF_INT_OF_NUM];
        MATCH_MP_TAC FSE_CUM_MONO THEN FBD_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH(fse_lowprob cs) < tt /\ &1 <= EL u (cs:int list) /\
                  u < 256`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `&c = EL u (cs:int list)`); INT_OF_NUM_LE] THEN
      FBD_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `fse_pos tl j < tt - LENGTH(fse_lowprob cs)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_imp(concl th) && is_binary "<" (lhand(concl th)))) THEN
      FBD_ARITH_TAC;
      ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--6) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(LENGTH(cs:int list) - u) * (2 * tt + 4) + 2 * (tt - j)` THEN
    CONJ_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:num`; `0`; `j:num`] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    FBD_DISJ_FINISH_TAC (DISJ2_TAC THEN DISJ1_TAC)];;

let FBD_FB0_TAC n =
  ASM_CASES_TAC `i + 1 = c` THENL
   [SUBGOAL_THEN `fse_ncell tl (tt - LENGTH(fse_lowprob cs)) (j + 1) =
                  fse_cum cs (u + 1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `u + 1 = LENGTH(cs:int list)` THENL
     [SUBGOAL_THEN `fse_cum cs (u + 1) = tt - LENGTH(fse_lowprob cs)`
      ASSUME_TAC THENL
       [REWRITE_TAC[ASSUME `u + 1 = LENGTH(cs:int list)`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `j + 1 = 2 EXP tl` ASSUME_TAC THENL
       [MATCH_MP_TAC FSE_WALK_END THEN
        EXISTS_TAC `tt - LENGTH(fse_lowprob cs)` THEN
        ASM_REWRITE_TAC[] THEN FBD_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `fse_pos tl (j + 1) = 0` ASSUME_TAC THENL
       [REWRITE_TAC[ASSUME `j + 1 = 2 EXP tl`; FSE_POS_FULL]; ALL_TAC] THEN
      ZSTD_STEPS_TAC (n--(n+7)) THEN FBD_GS_EXIT_TAC `j + 1`;
      FBD_W_TAC THEN ZSTD_STEPS_TAC (n--(n+7)) THEN PUFF_FINAL_TAC THEN
      DISJ1_TAC THEN
      EXISTS_TAC `w * (2 * tt + 4) + 2 * (tt - (j + 1)) + 1` THEN
      CONJ_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`u + 1`; `0`; `j + 1`] THEN
      FBD_DISJ_FINISH_TAC DISJ1_TAC];
    ZSTD_STEPS_TAC (n--(n+2)) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(LENGTH(cs:int list) - u) * (2 * tt + 4) + 2 * (tt - (j + 1))`
    THEN CONJ_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:num`; `i + 1`; `j + 1`] THEN
    FBD_DISJ_FINISH_TAC (DISJ2_TAC THEN DISJ1_TAC)];;

let FBD_GB_SETUP_TAC =
  SUBGOAL_THEN `LENGTH(fse_lowprob cs) < tt` ASSUME_TAC THENL
   [FBD_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = `LENGTH(fse_lowprob cs) < tt`
    then RULE_ASSUM_TAC(fun th' ->
           if concl th' = concl th then th' else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  SUBGOAL_THEN `&0 <= EL u (cs:int list)` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= EL u (cs:int list)` THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `EL u (cs:int list)` INT_OF_NUM_OF_INT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = num_of_int(EL u (cs:int list))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `fse_cum cs (u + 1) = fse_cum cs u + c /\
                fse_cum cs (u + 1) <= fse_cum cs (LENGTH cs) /\ u < 256`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FSE_CUM_SUC; SYM(ASSUME `&c = EL u (cs:int list)`)] THEN
      REWRITE_TAC[INT_ARITH `max (&c:int) (&0) = &c`; NUM_OF_INT_OF_NUM];
      MATCH_MP_TAC FSE_CUM_MONO THEN FBD_ARITH_TAC;
      FBD_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_step tl < tt` ASSUME_TAC THENL
   [FBD_EXPAND_TT_TAC THEN MATCH_MP_TAC FSE_STEP_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let FBD_GB_TAC =
  FBD_GB_SETUP_TAC THEN
  SUBGOAL_THEN `j < tt` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `j:num = tt` SUBST_ALL_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`tl:num`; `tt - LENGTH(fse_lowprob cs)`] FSE_NCELL_FULL) THEN
    ASM_REWRITE_TAC[] THEN FBD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_symbol cs tl (fse_pos tl j) = u` ASSUME_TAC THENL
   [MP_TAC(SPECL [`cs:int list`; `tl:num`; `j:num`] FSE_SYMBOL_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EL_FSE_SYMS THEN FBD_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add dt (word 4):int64`;
    `fse_tbl cs tl tb0 (fse_placed tl (tt - LENGTH(fse_lowprob cs)) j) 0`;
    `4 * fse_pos tl j + 2`; `1`; `s0:armstate`]
    READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN
  ANTS_TAC THENL [FBD_ARITH_TAC; STRIP_TAC] THEN
  FBD_POS_LT_TAC THEN
  ZSTD_STEPS_TAC (1--3) THEN FBD_NORM_TAC THEN ZSTD_STEPS_TAC [4] THEN
  FBD_SYM_STORE_TAC `fse_placed tl (tt - LENGTH(fse_lowprob cs)) j`
    `fse_pos tl j`
    `word_add dt (word (4 + 4 * fse_pos tl j + 2)):int64`
    `word u:byte` `s4:armstate` THEN
  MP_TAC(ISPECL [`cs:int list`; `tl:num`; `tb0:byte list`;
    `tt - LENGTH(fse_lowprob cs)`; `j:num`] FSE_TBL_PLACED_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `fse_ncell tl (tt - LENGTH(fse_lowprob cs)) (j + 1) =
                fse_cum cs u + i + 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FSE_NCELL_SUC] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `fse_pos tl (j + 1) < tt - LENGTH(fse_lowprob cs)` THEN
  ZSTD_STEPS_TAC (5--6) THENL
   [FBD_FB0_TAC 7;
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(LENGTH(cs:int list) - u) * (2 * tt + 4) + 2 * (tt - (j + 1))`
    THEN CONJ_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:num`; `i:num`; `j + 1`] THEN
    FBD_DISJ_FINISH_TAC (DISJ2_TAC THEN DISJ2_TAC)];;

let FBD_GC_TAC =
  SUBGOAL_THEN `fse_ncell tl (tt - LENGTH(fse_lowprob cs)) j <=
                tt - LENGTH(fse_lowprob cs)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tl:num`; `tt - LENGTH(fse_lowprob cs)`; `j:num`; `2 EXP tl`]
      FSE_NCELL_MONO) THEN
    MP_TAC(SPECL [`tl:num`; `tt - LENGTH(fse_lowprob cs)`] FSE_NCELL_FULL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(fun th -> if is_imp(concl th) then MATCH_MP_TAC th
                         else ACCEPT_TAC th) THEN
    FBD_ARITH_TAC;
    ALL_TAC] THEN
  FBD_GB_SETUP_TAC THEN
  SUBGOAL_THEN `j < tt` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `j:num = tt` SUBST_ALL_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(fse_pos tl tt < tt - LENGTH(fse_lowprob cs))` THEN
    FBD_EXPAND_TT_TAC THEN REWRITE_TAC[FSE_POS_FULL] THEN FBD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_placed tl (tt - LENGTH(fse_lowprob cs)) (j + 1) =
                fse_placed tl (tt - LENGTH(fse_lowprob cs)) j` ASSUME_TAC THENL
   [MATCH_MP_TAC FSE_PLACED_SKIP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if free_in `fse_tbl` (concl th) && free_in `memory` (concl th)
    then ASSUME_TAC(ONCE_REWRITE_RULE[GSYM(ASSUME
      `fse_placed tl (tt - LENGTH(fse_lowprob cs)) (j + 1) =
       fse_placed tl (tt - LENGTH(fse_lowprob cs)) j`)] th)
    else NO_TAC) THEN
  SUBGOAL_THEN `fse_ncell tl (tt - LENGTH(fse_lowprob cs)) (j + 1) =
                fse_cum cs u + i + 1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FSE_NCELL_SUC] THEN ARITH_TAC; ALL_TAC] THEN
  FBD_POS_LT_TAC THEN
  ZSTD_STEPS_TAC (1--2) THEN FBD_NORM_TAC THEN ZSTD_STEPS_TAC [3] THEN
  ASM_CASES_TAC `fse_pos tl (j + 1) < tt - LENGTH(fse_lowprob cs)` THEN
  ZSTD_STEPS_TAC [4] THENL
   [FBD_FB0_TAC 5;
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(LENGTH(cs:int list) - u) * (2 * tt + 4) + 2 * (tt - (j + 1))`
    THEN CONJ_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:num`; `i:num`; `j + 1`] THEN
    FBD_DISJ_FINISH_TAC (DISJ2_TAC THEN DISJ2_TAC)];;

let FBD_GEN = prove
 (mk_fbd_goal [] fbd_gen fbd_post,
  ZSTD_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC fbd_ginv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--5) THEN
    SUBGOAL_THEN `(tt DIV 8 + tt DIV 2) + 3 = fse_step tl`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[fse_step] THEN FBD_EXPAND_TT_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(LENGTH(cs:int list) - 0) * (2 * tt + 4) + 2 * (tt - 0) + 1`
    THEN MAP_EVERY EXISTS_TAC [`0`; `0`; `0`] THEN
    ASM_REWRITE_TAC[FSE_POS_0; FSE_NCELL_0; fse_cum; FSE_PLACED_0; LE_0] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_VALID_LENGTH) THEN
    FBD_DISJ_FINISH_TAC DISJ1_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `u:num` THEN ENSURES_EXISTS_PRE_TAC `i:num` THEN
  ENSURES_EXISTS_PRE_TAC `j:num` THEN
  FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN FBD_POS_FACTS_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_VALID_LENGTH) THEN
  SUBGOAL_THEN `LENGTH(fse_syms cs) = tt - LENGTH(fse_lowprob cs) /\
                LENGTH(fse_lowprob cs) <= tt /\
                fse_cum cs (LENGTH cs) = tt - LENGTH(fse_lowprob cs)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `fse_valid cs tl` THEN
    ASM_REWRITE_TAC[fse_valid; GSYM LENGTH_FSE_SYMS] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check
   (fun th -> is_disj(concl th) && free_in `PC` (concl th))) THENL
   [FBD_GA_TAC; FBD_GB_TAC; FBD_GC_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The entry and the loop over the counts (0xe80): a symbol of count -1 is   *)
(* placed at the highest state not yet taken and gets 1 as its first next    *)
(* state, and any other gets its count, the flags being updated. Then the    *)
(* header is stored and the code goes on with the general spread, or with    *)
(* the other one if no count is -1.                                          *)
(* ------------------------------------------------------------------------- *)

let FBD_L_BRANCH_TAC k =
  ASM_CASES_TAC `LENGTH(fse_lowprob cs) = 0` THENL
   [SUBGOAL_THEN `0 < tt` ASSUME_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
    FBD_ASSUME_REWRITE_TAC [`LENGTH(fse_lowprob cs) = 0`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUB_0]) THEN
    FBD_ASSUME_REWRITE_TAC [`0 < tt`] THEN
    ZSTD_STEPS_TAC [k; k + 1] THEN
    SUBGOAL_THEN `fse_lowprob cs = []` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
    SUBGOAL_THEN `(\v. tt <= v) = fse_placed tl tt 0`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[FUN_EQ_THM; FSE_PLACED_0]; ALL_TAC] THEN
    FBD_UNABBREV_TAC THEN ZSTD_CONTINUE_TAC FBD_FAST1 [] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(fse_lowprob cs = [])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(if LENGTH(fse_lowprob cs) < tt then (tt - 1) - LENGTH(fse_lowprob cs)
       else 4294967295) =
      (if LENGTH(fse_lowprob cs) < tt then (tt - LENGTH(fse_lowprob cs)) - 1
       else 4294967295)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `LENGTH(fse_lowprob cs) < tt` THENL
     [FBD_ASSUME_REWRITE_TAC [`LENGTH(fse_lowprob cs) < tt`];
      FBD_ASSUME_REWRITE_TAC [`~(LENGTH(fse_lowprob cs) < tt)`]]
    THEN
    (ZSTD_STEPS_TAC [k; k + 1] THEN
     SUBGOAL_THEN `(\v. tt - LENGTH(fse_lowprob cs) <= v) =
                   fse_placed tl (tt - LENGTH(fse_lowprob cs)) 0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
      [REWRITE_TAC[FUN_EQ_THM; FSE_PLACED_0]; ALL_TAC] THEN
     FBD_UNABBREV_TAC THEN ZSTD_CONTINUE_TAC FBD_GEN [] THEN
     MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[])];;

let FBD_L_EXIT_TAC n =
  FIRST_ASSUM(fun th -> if concl th = `u + 1 = LENGTH(cs:int list)`
                        then RULE_ASSUM_TAC(fun th' ->
                          if concl th' = concl th then th'
                          else REWRITE_RULE[th] th')
                        else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FSE_NLOW_LENGTH; GSYM FSE_FAST_FASTP]) THEN
  SUBGOAL_THEN `fse_fast cs tl <= 1 /\ tl < 65536` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[fse_fast] THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ARITH_TAC; FBD_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `fse_anyhigh cs (LENGTH cs)` THENL
   [FBD_ASSUME_REWRITE_TAC [`fse_anyhigh cs (LENGTH cs)`] THEN
    ZSTD_STEPS_TAC [n] THEN ARM_STEPS_TAC ZSTD_EXEC [n + 1] THEN
    MP_TAC(SPECL [`tl:num`; `fse_fast cs tl`] FBD_BFI_HEADER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ZSTD_STEPS_TAC [n + 2] THEN FBD_L_BRANCH_TAC (n + 3);
    FIRST [FBD_CONTR_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `fse_fast cs tl = 1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FSE_FAST_FASTP; FSE_FASTP_ALL_LOW]; ALL_TAC] THEN
    FBD_ASSUME_REWRITE_TAC [`~fse_anyhigh cs (LENGTH cs)`] THEN
    ZSTD_STEPS_TAC [n; n + 1] THEN
    SUBGOAL_THEN `tl + 65536 = tl + 65536 * fse_fast cs tl`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
    FBD_L_BRANCH_TAC (n + 2)];;

let FBD_L_LOW_TAC =
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `u:num`] FSE_NLOW_EL) THEN
  ASM_REWRITE_TAC[GSYM fse_nlow] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `fse_nlow cs u`] FSE_SYMBOL_LOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `fse_nlow cs u < tt` ASSUME_TAC THENL
   [FBD_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = `fse_nlow cs u < tt`
    then RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th'
                                   else REWRITE_RULE[th] th')
    else NO_TAC) THEN
  MP_TAC(ISPECL [`word_add dt (word 4):int64`;
    `fse_tbl cs tl tb0 (\v. tt - fse_nlow cs u <= v) 0`;
    `4 * (tt - 1 - fse_nlow cs u) + 2`; `1`; `s0:armstate`]
    READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_TBL] THEN
  ANTS_TAC THENL [FBD_ARITH_TAC; STRIP_TAC] THEN
  ZSTD_STEPS_TAC (1--8) THEN
  FBD_SYM_STORE_TAC `\v. tt - fse_nlow cs u <= v` `tt - 1 - fse_nlow cs u`
    `word_add dt (word (4 + 4 * (tt - 1 - fse_nlow cs u) + 2)):int64`
    `word u:byte` `s8:armstate` THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `fse_tbl cs tl tb0
      (\x. tt - fse_nlow cs u <= x \/ x = tt - 1 - fse_nlow cs u) 0 =
    fse_tbl cs tl tb0 (\v. tt - fse_nlow cs (u + 1) <= v) 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC FSE_TBL_P_EQ THEN ASM_REWRITE_TAC[FSE_NLOW_SUC] THEN
    REPEAT STRIP_TAC THEN FBD_ARITH_TAC;
    DISCH_TAC] THEN
  ZSTD_STEPS_TAC [9] THEN
  MP_TAC(ISPECL [`wksp:int64`;
    `list_of_seq (\i. word(fse_init cs i):int16) u`;
    `word_add wksp (word (2 * val(word u:int64))):int64`;
    `word 1:int16`; `s9:armstate`] READ_MEMORY_WORDLIST16_APPEND1) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VAL_WORD_LT64 THEN FBD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `APPEND (list_of_seq (\i. word(fse_init cs i):int16) u)
                       [word 1] =
                list_of_seq (\i. word(fse_init cs i)) (u + 1)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LIST_OF_SEQ_SNOC; fse_init]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `word_zx (word_sub (word (tt - 1 - fse_nlow cs u)) (word 1):int32):int64 =
    word(if fse_nlow cs (u + 1) < tt then (tt - 1) - fse_nlow cs (u + 1)
         else 4294967295)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[FSE_NLOW_SUC] THEN
    ASM_CASES_TAC `fse_nlow cs u + 1 < tt` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN
       `tt - 1 - fse_nlow cs u = (tt - 1 - (fse_nlow cs u + 1)) + 1`
      SUBST1_TAC THENL [FBD_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[WORD_ADD; WORD_RULE `word_sub (word_add x y) y = x`] THEN
      MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
      REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      FBD_ARITH_TAC;
      SUBGOAL_THEN `tt - 1 - fse_nlow cs u = 0` SUBST1_TAC THENL
       [FBD_ARITH_TAC; CONV_TAC WORD_REDUCE_CONV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fse_anyhigh cs (u + 1) <=> fse_anyhigh cs u) /\
                (fse_fastp cs tl (u + 1) <=> fse_fastp cs tl u)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM(CONJUNCT1 th);
                                          GSYM(CONJUNCT2 th)])) THENL
   [ASM_REWRITE_TAC[FSE_ANYHIGH_SUC; FSE_FASTP_SUC] THEN
    REWRITE_TAC[INT_ARITH `-- &1:int < &n`];
    ALL_TAC] THEN
  ASM_CASES_TAC `u + 1 = LENGTH(cs:int list)` THENL
   [ZSTD_STEPS_TAC (10--12) THEN FBD_L_EXIT_TAC 13;
    ZSTD_STEPS_TAC (10--13) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `LENGTH(cs:int list) - (u + 1)` THEN
    CONJ_TAC THENL [FBD_ARITH_TAC; EXISTS_TAC `u + 1`] THEN
    FBD_DISJ_FINISH_TAC ALL_TAC];;

let FBD_L_NONLOW_TAC =
  SUBGOAL_THEN `&0 <= EL u (cs:int list)` ASSUME_TAC THENL
   [UNDISCH_TAC `fse_valid cs tl` THEN
    REWRITE_TAC[fse_valid; GSYM ALL_EL] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `EL u (cs:int list)` INT_OF_NUM_OF_INT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = num_of_int(EL u (cs:int list))` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; GSYM WORD_IWORD] THEN
                       ASSUME_TAC th) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `c <= tt` ASSUME_TAC THENL
   [MP_TAC(SPECL [`cs:int list`; `u + 1`; `LENGTH(cs:int list)`]
      FSE_CUM_MONO) THEN
    REWRITE_TAC[FSE_CUM_SUC; GSYM LENGTH_FSE_SYMS;
                SYM(ASSUME `&c = EL u (cs:int list)`)] THEN
    REWRITE_TAC[INT_ARITH `max (&c:int) (&0) = &c`; NUM_OF_INT_OF_NUM] THEN
    FBD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_init cs u = c /\ fse_nlow cs (u + 1) = fse_nlow cs u /\
                fse_anyhigh cs (u + 1) /\
                (fse_fastp cs tl (u + 1) <=>
                 fse_fastp cs tl u /\ c < 2 EXP (tl - 1))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[fse_init; FSE_NLOW_SUC; ADD_CLAUSES; FSE_ANYHIGH_SUC;
                    FSE_FASTP_SUC] THEN
    REWRITE_TAC[SYM(ASSUME `&c = EL u (cs:int list)`); INT_OF_NUM_LT];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME
    `fse_nlow cs (u + 1) = fse_nlow cs u`)]) THEN
  ASM_CASES_TAC `c < 2 EXP (tl - 1)` THEN
  ZSTD_STEPS_TAC (1--6) THEN
  MP_TAC(ISPECL [`wksp:int64`;
    `list_of_seq (\i. word(fse_init cs i):int16) u`;
    `word_add wksp (word (2 * val(word u:int64))):int64`;
    `word c:int16`; `s6:armstate`] READ_MEMORY_WORDLIST16_APPEND1) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     MATCH_MP_TAC VAL_WORD_LT64 THEN FBD_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `APPEND (list_of_seq (\i. word(fse_init cs i):int16) u)
                        [word c] =
                 list_of_seq (\i. word(fse_init cs i)) (u + 1)`
   SUBST1_TAC THENL
    [ASM_REWRITE_TAC[LIST_OF_SEQ_SNOC]; DISCH_TAC] THEN
   ZSTD_STEPS_TAC (7--10) THEN
   W(fun gl -> let s = FBD_CUR_STATE gl in
     FBD_SET_REG_TAC
      (subst [s,`s:armstate`]
        `read X10 s = word(if fse_anyhigh cs (u + 1) then 1 else 0)`)
      (ASM_REWRITE_TAC[]) THEN
     FBD_SET_REG_TAC
      (subst [s,`s:armstate`]
        `read X12 s = word(if fse_fastp cs tl (u + 1) then 1 else 0)`)
      (ASM_REWRITE_TAC[])) THEN
   ASM_CASES_TAC `u + 1 = LENGTH(cs:int list)` THENL
    [ZSTD_STEPS_TAC [11] THEN FBD_L_EXIT_TAC 12;
     ZSTD_STEPS_TAC (11--12) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
     EXISTS_TAC `LENGTH(cs:int list) - (u + 1)` THEN
     CONJ_TAC THENL [FBD_ARITH_TAC; EXISTS_TAC `u + 1`] THEN
     FBD_DISJ_FINISH_TAC ALL_TAC]);;

let FBD_ENTRY = prove
 (mk_fbd_goal [`wsz:num`] fbd_entry fbd_post,
  ZSTD_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC fbd_linv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    REWRITE_TAC[C_ARGUMENTS] THEN FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_VALID_LENGTH) THEN
    SUBGOAL_THEN `2 EXP (tl - 1) <= 2048 /\ 2 * 2 EXP (tl - 1) = tt`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [TRANS_TAC LE_TRANS `2 EXP 11` THEN
        CONV_TAC(RAND_CONV NUM_REDUCE_CONV) THEN
        REWRITE_TAC[LE_REFL; LE_EXP] THEN FBD_ARITH_TAC;
        FBD_EXPAND_TT_TAC THEN
        SUBGOAL_THEN `tl = (tl - 1) + 1` (fun th -> GEN_REWRITE_TAC
          (RAND_CONV o RAND_CONV) [th]) THENL [FBD_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC];
      ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--30) THEN
    SUBGOAL_THEN `4294967296 * tl DIV 4294967296 + 65536 + tl MOD 65536 =
                  tl + 65536 /\ LENGTH(cs:int list) - 1 + 1 = LENGTH cs`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `tl DIV 4294967296 = 0 /\ tl MOD 65536 = tl`
         (CONJUNCTS_THEN SUBST1_TAC) THENL
         [CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN
          FBD_ARITH_TAC;
          ARITH_TAC];
        FBD_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if concl th = `2 EXP tl = tt`
                          then RULE_ASSUM_TAC(fun th' ->
                            if concl th' = concl th then th'
                            else REWRITE_RULE[th] th')
                          else NO_TAC) THEN
    SUBGOAL_THEN `fse_tbl cs tl tb0 (\v. tt - fse_nlow cs 0 <= v) 0 = tb0`
    ASSUME_TAC THENL
     [REWRITE_TAC[FSE_NLOW_0; SUB_0] THEN FBD_EXPAND_TT_TAC THEN
      MATCH_MP_TAC FSE_TBL_INIT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `LENGTH(cs:int list) - 0` THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[FSE_NLOW_0; FSE_ANYHIGH_0; FSE_FASTP_0; SUB_0;
                    MULT_CLAUSES; READ_MEMORY_BYTES_0; LIST_OF_SEQ_CLAUSES;
                    num_of_wordlist] THEN
    FBD_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN ENSURES_EXISTS_PRE_TAC `u:num` THEN
  FBD_ABBREV_TAC THEN PUFF_INIT_TAC "s0" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_VALID_LENGTH) THEN
  SUBGOAL_THEN `2 EXP (tl - 1) <= 2048 /\ 2 * 2 EXP (tl - 1) = tt /\
                LENGTH(fse_syms cs) + LENGTH(fse_lowprob cs) = tt /\
                fse_nlow cs u <= LENGTH(fse_lowprob cs) /\ u < 256`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [TRANS_TAC LE_TRANS `2 EXP 11` THEN
      CONV_TAC(RAND_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[LE_REFL; LE_EXP] THEN FBD_ARITH_TAC;
      FBD_EXPAND_TT_TAC THEN
      SUBGOAL_THEN `tl = (tl - 1) + 1` (fun th -> GEN_REWRITE_TAC
        (RAND_CONV o RAND_CONV) [th]) THENL [FBD_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC;
      UNDISCH_TAC `fse_valid cs tl` THEN ASM_REWRITE_TAC[fse_valid] THEN
      SIMP_TAC[];
      REWRITE_TAC[GSYM FSE_NLOW_LENGTH] THEN MATCH_MP_TAC FSE_NLOW_MONO THEN
      FBD_ARITH_TAC;
      FBD_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nc:int64`; `MAP (iword:int->int16) cs`;
                 `LENGTH(cs:int list)`; `u:num`; `s0:armstate`]
    READ_MEMORY_BYTES16_WORDLIST_VAL) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN FBD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `EL u (cs:int list) = -- &1` THENL
   [FBD_L_LOW_TAC; FBD_L_NONLOW_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For counts cs that are fse_valid for the accuracy log   *)
(* tl, with 5 <= tl <= 12, at most 256 of them, as 16-bit numbers at nc, and *)
(* a workspace of wsz bytes that is large enough, the result is 0, with the  *)
(* header holding tl and fastMode at dt and the decoding table of the        *)
(* specification after it. The loads are from the counts, the table and the  *)
(* workspace, and the stores to the table and the workspace.                 *)
(* ------------------------------------------------------------------------- *)

let FSE_BUILD_DTABLE_CORRECT = prove
 (`!pc returnaddress dt nc wksp cs tl wsz e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     fse_valid cs tl /\ 5 <= tl /\ tl <= 12 /\ LENGTH(cs:int list) <= 256 /\
     2 * LENGTH cs + 2 EXP tl + 8 <= wsz /\ wsz < 2 EXP 64 /\
     nonoverlapping (dt:int64,4 + 4 * 2 EXP tl) (nc:int64,2 * LENGTH cs) /\
     nonoverlapping (dt,4 + 4 * 2 EXP tl)
                    (wksp:int64,2 * LENGTH cs + 2 EXP tl + 8) /\
     nonoverlapping (wksp,2 * LENGTH cs + 2 EXP tl + 8) (nc,2 * LENGTH cs) /\
     nonoverlapping (dt,4 + 4 * 2 EXP tl) (word pc,32000) /\
     nonoverlapping (wksp,2 * LENGTH cs + 2 EXP tl + 8) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0xe80) /\ read X30 s = returnaddress /\
               C_ARGUMENTS [dt; nc; word(LENGTH cs - 1); word tl; wksp;
                            word wsz] s /\
               read (memory :> bytes(nc,2 * LENGTH cs)) s =
               num_of_wordlist(MAP (iword:int->int16) cs) /\
               read events s = e)
          (\s. read PC s = returnaddress /\ read X0 s = word 0 /\
               read (memory :> bytes32 dt) s =
               word(tl + 65536 * fse_fast cs tl) /\
               read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
               num_of_bytelist(fse_dtable cs tl) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [nc,2 * LENGTH cs; dt,4 + 4 * 2 EXP tl;
                       wksp,2 * LENGTH cs + 2 EXP tl + 8]
                      [dt,4 + 4 * 2 EXP tl;
                       wksp,2 * LENGTH cs + 2 EXP tl + 8]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(dt,4 + 4 * 2 EXP tl);
                      memory :> bytes(wksp,2 * LENGTH cs + 2 EXP tl + 8)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  W(fun (asl,w) ->
    let sv = `s:armstate` and tv = `tb0:byte list` in
    let body = rhs(concl(BETA_CONV(mk_comb(fbd_entry,sv)))) in
    EXISTS_TAC(mk_abs(sv,mk_exists(tv,
      mk_conj(`LENGTH(tb0:byte list) = 4 * 2 EXP tl`,body))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `bytelist_of_num (4 * 2 EXP tl)
      (read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s)` THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; puff_memsafe] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUM_OF_BYTELIST_OF_NUM_EQ THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      EXISTS_TAC `[]:uarch_event list` THEN
      REWRITE_TAC[APPEND; MEMACCESS_INBOUNDS_NIL]];
    ALL_TAC] THEN
  ENSURES_EXISTS_PRE_TAC `tb0:byte list` THEN
  ASM_CASES_TAC `LENGTH(tb0:byte list) = 4 * 2 EXP tl` THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`pc:num`; `returnaddress:int64`; `dt:int64`; `nc:int64`;
                  `wksp:int64`; `cs:int list`; `tl:num`; `tb0:byte list`;
                  `e:uarch_event list`; `wsz:num`] FBD_ENTRY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM) th)) THEN
    REWRITE_TAC[puff_memsafe];
    REWRITE_TAC[ensures]]);;

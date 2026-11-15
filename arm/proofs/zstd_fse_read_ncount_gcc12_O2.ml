(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* FSE_readNCount_body_default(normalizedCounter,maxSVPtr,tableLogPtr,       *)
(* headerBuffer,hbSize) of zstd, at 0x940 in the image, which reads the      *)
(* description of an FSE table at the start of the input (section 4.1.1 of   *)
(* RFC 8878) in the zstd dialect of the specification in rfc8878.ml: the     *)
(* Accuracy_Log, at most 15, and then the probabilities of the symbols, at   *)
(* most *maxSVPtr + 1 of them. It stores them as 16-bit numbers in           *)
(* normalizedCounter, their number less 1 in *maxSVPtr and the Accuracy_Log  *)
(* in *tableLogPtr, and returns the number of bytes of the description, or   *)
(* an error code if there is no description. It calls memset and memcpy, and *)
(* itself for an input of fewer than 8 bytes.                                *)
(* ========================================================================= *)

needs "arm/proofs/utils/zstd_huf.ml";;

(* ------------------------------------------------------------------------- *)
(* The window of bits that the code keeps in a register: the 32 - bc bits    *)
(* from position 8 * ofs + bc, given by a 4-byte load at offset ofs and a    *)
(* shift by bc, its low bits, and the runs of 1 bits at its bottom (pairs of *)
(* them are repeat flags 3), which the code counts with rbit and clz.        *)
(* ------------------------------------------------------------------------- *)

let ZSTD_BITS_WINDOW = prove
 (`!l ofs bc.
        bc <= 32
        ==> ((num_of_bytelist l DIV 2 EXP (8 * ofs)) MOD 2 EXP 32) DIV
            2 EXP bc =
            zstd_bits l (8 * ofs + bc) (32 - bc)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ZSTD_BITS_NUM] THEN
  SUBGOAL_THEN `2 EXP 32 = 2 EXP bc * 2 EXP (32 - bc)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[DIV_MOD; EXP_ADD; DIV_DIV; MULT_ASSOC]]);;

let ZSTD_BITS_WINDOW_MOD = prove
 (`!l ofs bc k.
        ofs + 4 <= LENGTH l /\ bc <= 31 /\ k <= 25 /\
        (bc <= 7 \/ ofs + 4 = LENGTH l)
        ==> zstd_bits l (8 * ofs + bc) (32 - bc) MOD 2 EXP k =
            zstd_bits l (8 * ofs + bc) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[ZSTD_BITS_SPLIT;
                 ARITH_RULE `bc <= 7 /\ k <= 25 ==> k <= 32 - bc`];
    ALL_TAC] THEN
  ASM_CASES_TAC `k <= 32 - bc` THENL
   [ASM_SIMP_TAC[ZSTD_BITS_SPLIT]; ALL_TAC] THEN
  SUBGOAL_THEN `zstd_bits l (8 * ofs + bc) k =
                zstd_bits l (8 * ofs + bc) (32 - bc)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `k = (32 - bc) + (k - (32 - bc))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ZSTD_BITS_ADD]] THEN
    SUBGOAL_THEN `zstd_bits l ((8 * ofs + bc) + (32 - bc)) (k - (32 - bc)) = 0`
     (fun th -> REWRITE_TAC[th; MULT_CLAUSES; ADD_CLAUSES]) THEN
    MATCH_MP_TAC ZSTD_BITS_BEYOND THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP (32 - bc)` THEN
    REWRITE_TAC[ZSTD_BITS_BOUND; LE_EXP] THEN ASM_ARITH_TAC]);;

let WORD_CTZ_NOT_OR31 = prove
 (`!x:int32 t.
        word_ctz (word_or (word_not x) (word 2147483648)) = t
        ==> t <= 31 /\ val x MOD 2 EXP t = 2 EXP t - 1 /\
            (t < 31 ==> ~bit t x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_CTZ_UNIQUE_GEN; DIMINDEX_32] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_NOT; DIMINDEX_32;
              ARITH_RULE `2147483648 = 2 EXP 31`; BIT_WORD_POW2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `t <= 31` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `31`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `word_and x (word(2 EXP t - 1)) = word(2 EXP t - 1):int32`
    MP_TAC THENL
     [REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_MASK_WORD; DIMINDEX_32] THEN
      X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < t` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `i < 32 /\ ~(i = 31)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
      MATCH_MP_TAC(ARITH_RULE `a < b ==> a - 1 < b`) THEN
      REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `t < 31 ==> ~(t = 31)`]]);;

let MOD_POW2_ONES = prove
 (`!w t. w MOD 2 EXP t = 2 EXP t - 1 <=> !i. i < t ==> ODD(w DIV 2 EXP i)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[EXP; MOD_1; CONJUNCT1 LT] THEN ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[LT; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXP; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_MOD; ODD_MOD] THEN
  MP_TAC(SPECL [`w:num`; `2 EXP t`] MOD_LT_EQ) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  MP_TAC(SPECL [`w DIV 2 EXP t`; `2`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(w DIV 2 EXP t) MOD 2`,`d:num`) THEN
  SPEC_TAC(`w MOD 2 EXP t`,`m:num`) THEN
  MP_TAC(SPECL [`2`; `t:num`] EXP_EQ_0) THEN REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`2 EXP t`,`e:num`) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `d < 2 ==> d = 0 \/ d = 1`)) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_ARITH_TAC);;

let MOD4_LT3 = prove
 (`!y. y MOD 4 < 3 <=> ~(ODD y /\ ODD(y DIV 2))`,
  GEN_TAC THEN REWRITE_TAC[ODD_MOD] THEN
  MP_TAC(SPECL [`y:num`; `2`; `2`] MOD_MULT_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`y:num`; `2`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`y DIV 2`; `2`] MOD_LT_EQ) THEN ARITH_TAC);;

let ZSTD_WINDOW_PAIRS = prove
 (`!w t. w MOD 2 EXP t = 2 EXP t - 1 /\ ~ODD(w DIV 2 EXP t)
         ==> w MOD 2 EXP (2 * (t DIV 2)) = 2 EXP (2 * (t DIV 2)) - 1 /\
             (w DIV 2 EXP (2 * (t DIV 2))) MOD 4 < 3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOD_POW2_ONES; MOD4_LT3] THEN
  SUBGOAL_THEN `t = 2 * t DIV 2 \/ t = 2 * t DIV 2 + 1` MP_TAC THENL
   [MP_TAC(SPECL [`t:num`; `2`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`t DIV 2`,`r:num`) THEN GEN_TAC THEN
  REWRITE_TAC[DIV_DIV;
              ONCE_REWRITE_RULE[MULT_SYM] (GSYM(CONJUNCT2 EXP)); ADD1] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The counts in memory: fse_nclist cs n has the probabilities cs as 16-bit  *)
(* numbers, padded with 0 to n of them, as the memset of the buffer and the  *)
(* stores of the code leave it.                                              *)
(* ------------------------------------------------------------------------- *)

let fse_nclist = new_definition
 `fse_nclist (cs:int list) n =
    list_of_seq (\i. iword(if i < LENGTH cs then EL i cs else &0):int16) n`;;

let LENGTH_FSE_NCLIST = prove
 (`!cs n. LENGTH(fse_nclist cs n) = n`,
  REWRITE_TAC[fse_nclist; LENGTH_LIST_OF_SEQ]);;

let EL_FSE_NCLIST = prove
 (`!cs n i. i < n
            ==> EL i (fse_nclist cs n) =
                iword(if i < LENGTH cs then EL i cs else &0)`,
  SIMP_TAC[fse_nclist; EL_LIST_OF_SEQ]);;

let FSE_NCLIST_APPEND_ZEROS = prove
 (`!cs k n. fse_nclist (APPEND cs (REPLICATE k (&0))) n = fse_nclist cs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_FSE_NCLIST] THEN
  SIMP_TAC[EL_FSE_NCLIST] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; EL_APPEND] THEN
  ASM_CASES_TAC `i < LENGTH(cs:int list)` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
    W(fun (_,w) -> MP_TAC(ISPECL [rand(lhs w); lhand(lhs w)] MEM_EL)) THEN
    ASM_REWRITE_TAC[LENGTH_REPLICATE; MEM_REPLICATE] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[]]]);;

let FSE_NCLIST_NIL = prove
 (`!n. num_of_wordlist(fse_nclist [] n) = 0`,
  INDUCT_TAC THEN
  REWRITE_TAC[fse_nclist; LIST_OF_SEQ_0; num_of_wordlist] THEN
  REWRITE_TAC[GSYM fse_nclist] THEN
  REWRITE_TAC[fse_nclist; ADD1; LIST_OF_SEQ_ADD1; NUM_OF_WORDLIST_APPEND] THEN
  REWRITE_TAC[GSYM fse_nclist; LENGTH; CONJUNCT1 LT] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_SING; GSYM WORD_IWORD; VAL_WORD_0] THEN
  ARITH_TAC);;

let EL_FSE_NCLIST_SNOC = prove
 (`!cs x n i.
        i < n
        ==> EL i (fse_nclist (APPEND cs [x]) n) =
            if i = LENGTH cs then iword x else EL i (fse_nclist cs n)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_FSE_NCLIST] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND; ADD_CLAUSES; LT] THEN
  ASM_CASES_TAC `i < LENGTH(cs:int list)` THEN
  ASM_SIMP_TAC[LT_IMP_NE] THEN
  ASM_CASES_TAC `i = LENGTH(cs:int list)` THEN
  ASM_REWRITE_TAC[SUB_REFL; EL; HD]);;

(* ------------------------------------------------------------------------- *)
(* Facts about the words of the computations of the code: the threshold for  *)
(* the number of bits of a field, the counts stored, the bit position after  *)
(* a wrap around into the last 4 bytes, comparisons and selections.          *)
(* ------------------------------------------------------------------------- *)

let NC_THR_UPDATE = prove
 (`!b. 1 <= b /\ b <= 16
       ==> word_zx (word_jshl (word 1) (word_sub (word 31) (word (32 - b))):
                    int32):int64 = word(2 EXP (b - 1)) /\
           word(32 - (32 - b)):int64 = word b`,
  REPEAT STRIP_TAC THENL
   [ALL_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `word_sub (word 31) (word (32 - b)):int32 = word(b - 1)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[WORD_RULE
     `word_sub (x:N word) y = z <=> x = word_add z y`] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[word_jshl; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `((b - 1) MOD 2 EXP 32) MOD 32 = b - 1` SUBST1_TAC THENL
   [SIMP_TAC[MOD_LT; ARITH_RULE `b <= 16 ==> b - 1 < 2 EXP 32`;
             ASSUME `b <= 16`] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_SHL_WORD; MULT_CLAUSES] THEN
  MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONJ_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 16` THEN
  REWRITE_TAC[LT_EXP; LE_EXP] THEN ASM_ARITH_TAC);;

let NC_COUNT_NONZERO = prove
 (`!v. v <= 65536 /\ ~(v = 1) ==> ~(val(iword(&v - &1):int32) = 0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v = 0` THENL
   [UNDISCH_TAC `val(iword(&v - &1):int32) = 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    UNDISCH_TAC `val(iword(&v - &1):int32) = 0` THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; ARITH_RULE `~(v = 0) ==> 1 <= v`;
                 GSYM WORD_IWORD; VAL_WORD; DIMINDEX_32] THEN
    SUBGOAL_THEN `(v - 1) MOD 2 EXP 32 = v - 1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let NC_COUNT_ZERO = prove
 (`val(iword(&1 - &1):int32) = 0`,
  REWRITE_TAC[INT_SUB_REFL; GSYM WORD_IWORD; VAL_WORD_0]);;

let DIVISION_8 = prove
 (`!b. b = 8 * (b DIV 8) + b MOD 8 /\ b MOD 8 < 8`,
  GEN_TAC THEN MP_TAC(SPECL [`b:num`; `8`] DIVISION) THEN ARITH_TAC);;

let DIVISION_8_ALT = prove
 (`!b. 8 * (b DIV 8) + b MOD 8 = b /\ b MOD 8 < 8`,
  MESON_TAC[DIVISION_8]);;

let NC_WINDOW_LEMMA = prove
 (`!l ofs bc.
        bc < 32
        ==> word_zx (word_jushr
                      (word ((num_of_bytelist l DIV 2 EXP (8 * ofs)) MOD
                             4294967296):int32)
                      (word bc)):int64 =
            word(zstd_bits l (8 * ofs + bc) (32 - bc))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `ofs:num`; `bc:num`] ZSTD_BITS_WINDOW) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[word_jushr; DIMINDEX_32; VAL_WORD] THEN
  SUBGOAL_THEN `(bc MOD 2 EXP 32) MOD 32 = bc` SUBST1_TAC THENL
   [SUBGOAL_THEN `bc MOD 2 EXP 32 = bc` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `32` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `y = (num_of_bytelist l DIV 2 EXP (8 * ofs)) MOD 4294967296` THEN
  SUBGOAL_THEN `y < 4294967296` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `y DIV 2 EXP bc < 4294967296` ASSUME_TAC THENL
   [TRANS_TAC LET_TRANS `y:num` THEN ASM_REWRITE_TAC[DIV_LE] THEN
    REWRITE_TAC[DIV_LE];
    ASM_SIMP_TAC[MOD_LT] THEN
    MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LTE_TRANS `4294967296` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let WORD_SUB_LE = prove
 (`!m n. n <= m ==> word_sub (word m) (word n):N word = word(m - n)`,
  SIMP_TAC[WORD_SUB]);;

let NC_WRAP_BC = prove
 (`!(hb:int64) len ofs bq.
        ofs + 4 <= len /\ 8 * (len - 4 - ofs) <= bq /\ bq < 2 EXP 31
        ==> word_zx
             (word_and
               (word_sub (word bq)
                 (word_shl
                   (word_zx (word_sub (word_add hb (word (len - 4)))
                                      (word_add hb (word ofs)):int64):int32)
                   3))
               (word 31):int32):int64 =
            word((bq - 8 * (len - 4 - ofs)) MOD 32)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_add (hb:int64) (word x)) (word_add hb (word y)) =
    word_sub (word x) (word y)`] THEN
  ASM_SIMP_TAC[WORD_SUB_LE;
               ARITH_RULE `ofs + 4 <= len ==> ofs <= len - 4`] THEN
  SUBGOAL_THEN `word_zx (word (len - 4 - ofs):int64):int32 =
                word (len - 4 - ofs)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_SHL_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[WORD_SUB_LE] THEN
  MP_TAC(INST_TYPE [`:32`,`:N`]
    (SPECL [`bq - 8 * (len - 4 - ofs)`; `5`] WORD_AND_POW2_WORD)) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`bq - 8 * (len - 4 - ofs)`; `32`] MOD_LT_EQ) THEN
  ARITH_TAC);;

let UXTW_ABBREV_TAC r v k =
  let wk = mk_comb(`word:num->int64`,k) in
  let e1 = mk_eq(mk_comb(`val:int64->num`,
             mk_comb(`word_zx:int32->int64`,
               mk_comb(`word_zx:int64->int32`,v))),k)
  and e2 = mk_eq(mk_comb(`val:int64->num`,
             mk_comb(`word_zx:int32->int64`,
               mk_comb(`word_zx:int32->int32`,
                 mk_comb(`word_zx:int64->int32`,v)))),k) in
  REG_ABBREV_TAC r v wk THEN
  MAP_EVERY (fun e ->
    SUBGOAL_THEN e ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME(mk_eq(wk,v)))) THEN
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      REFL_TAC;
      ALL_TAC]) [e1; e2];;

let WORD_PC_NE = prove
 (`!pc a b. pc + a < 2 EXP 64 /\ pc + b < 2 EXP 64 /\ ~(a = b)
            ==> ~(word(pc + a):int64 = word(pc + b))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num`) THEN
  ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC);;

let NC_PC_NE_TAC a b =
  let th = SPECL [`pc:num`; mk_small_numeral a; mk_small_numeral b]
                 WORD_PC_NE in
  MP_TAC th THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; DISCH_TAC];;

let NC_REM_NEG = prove
 (`!n. n < 2 EXP 31 ==> word_zx(word((n + 1) + 4294967295):int32):int64 =
                        word n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word((n + 1) + 4294967295):int32 = word n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_32] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + 4294967295 = 1 * 2 EXP 32 + n`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC]);;

(*** Replace the fact about a register in the current state by tm, proved ***)
(*** by tac from the assumptions                                          ***)

let NC_SET_REG_TAC tm tac =
  SUBGOAL_THEN tm (fun th ->
    let l = lhs(concl th) in
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
      (fun th' -> is_eq(concl th') && lhs(concl th') = l))) THEN
    ASSUME_TAC th) THENL [tac; ALL_TAC];;

let NC_COUNT_POS_N = prove
 (`!v. 1 <= v ==> iword(&v - &1):N word = word(v - 1)`,
  SIMP_TAC[INT_OF_NUM_SUB; GSYM WORD_IWORD]);;

let NC_IVAL_SMALL = prove
 (`!n. n < 2 EXP 31 ==> ival(word n:int32) = &n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_IWORD] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  ASM_SIMP_TAC[INT_OF_NUM_LT; INT_ARITH `--(&2147483648) <= &x:int`] THEN
  UNDISCH_TAC `n < 2 EXP 31` THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_LT]);;

let NC_ONES_BOUND = prove
 (`!w k t. w < 2 EXP k /\ w MOD 2 EXP t = 2 EXP t - 1 ==> t <= k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP (k + 1) <= 2 EXP t` MP_TAC THENL
   [REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `w MOD 2 EXP t = w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP k` THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; EXP_1] THEN
  MP_TAC(SPECL [`2`; `k:num`] EXP_EQ_0) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_ARITH_TAC);;

let NC_ONES_MONO = prove
 (`!w t k. k <= t /\ w MOD 2 EXP t = 2 EXP t - 1
           ==> w MOD 2 EXP k = 2 EXP k - 1`,
  REWRITE_TAC[MOD_POW2_ONES] THEN MESON_TAC[LTE_TRANS]);;

let NC_SHL3_MUL = prove
 (`!x:N word. word_shl x 3 = word_mul x (word 8)`,
  GEN_TAC THEN REWRITE_TAC[word_shl] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

let NC_WRAP_SHIFT = prove
 (`!(x:int32) (a:int64) b.
        word_sub x (word_shl (word_zx (word_sub a b):int32) 3) =
        word_sub (word_add x (word 24))
                 (word_shl (word_zx (word_sub (word_add a (word 3)) b):int32)
                           3)`,
  SIMP_TAC[WORD_ZX_SUB; WORD_ZX_ADD; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[NC_SHL3_MUL] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  CONV_TAC WORD_RULE);;

let NC_WRAP_BC7 = prove
 (`!(hb:int64) len ofs bc.
        7 <= len /\ len - 7 < ofs /\ ofs + 4 <= len /\ bc <= 8
        ==> word_zx
             (word_and
               (word_sub (word bc)
                 (word_shl
                   (word_zx (word_sub (word_add hb (word (len - 7)))
                                      (word_add hb (word ofs)):int64):int32)
                   3))
               (word 31):int32):int64 =
            word(((bc + 24) - 8 * (len - 4 - ofs)) MOD 32)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[NC_WRAP_SHIFT] THEN
  SUBGOAL_THEN `word_add (word_add hb (word (len - 7))) (word 3):int64 =
                word_add hb (word (len - 4))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN MATCH_MP_TAC NC_WRAP_BC THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The measure of the loop. In a run of repeat flags, nc_inner len ofs bc    *)
(* decreases with each group of 12 flags 3: by 12 bits when the window moves *)
(* on by 3 bytes, and when it wraps around, as the window then has fewer     *)
(* than 24 bits left or no more 3s.                                          *)
(* ------------------------------------------------------------------------- *)

let nc_inner = new_definition
 `nc_inner len ofs bc =
    4 * (len - ofs) + (if bc = 8 then 2 else if bc < 8 then 1 else 0)`;;

let NC_INNER_NOWRAP = prove
 (`!len ofs bc.
        ofs + 7 <= len ==> nc_inner len (ofs + 3) bc < nc_inner len ofs bc`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nc_inner] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let NC_INNER_WRAP = prove
 (`!len ofs bc.
        7 <= len /\ len - 7 < ofs /\ ofs + 4 <= len /\ bc <= 8
        ==> nc_inner len (len - 4) (((bc + 24) - 8 * (len - 4 - ofs)) MOD 32) <
            nc_inner len ofs bc`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `ofs + 4 = len` THENL
   [SUBGOAL_THEN `((bc + 24) - 8 * (len - 4 - ofs)) MOD 32 =
                  if bc = 8 then 0 else bc + 24`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `(bc + 24) - 8 * (len - 4 - ofs) = bc + 24`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
      REWRITE_TAC[nc_inner] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC];
    REWRITE_TAC[nc_inner] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let NC_ZEROS_LAST_BITS = prove
 (`!l ofs bc t.
        ofs + 4 <= LENGTH l /\ bc <= 31 /\ (bc <= 7 \/ ofs + 4 = LENGTH l) /\
        t <= 23 /\
        zstd_bits l (8 * ofs + bc) (32 - bc) MOD 2 EXP t = 2 EXP t - 1 /\
        ~ODD(zstd_bits l (8 * ofs + bc) (32 - bc) DIV 2 EXP t)
        ==> zstd_bits l (8 * ofs + bc) (2 * (t DIV 2)) =
            2 EXP (2 * (t DIV 2)) - 1 /\
            zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2 =
            (zstd_bits l (8 * ofs + bc) (32 - bc) DIV 2 EXP (2 * (t DIV 2)))
            MOD 4 /\
            zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2 < 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `2 * (t DIV 2) + 2 <= 25` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t:num`; `2`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `ofs:num`; `bc:num`; `2 * (t DIV 2) + 2`]
    ZSTD_BITS_WINDOW_MOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o SYM)] THEN
  MP_TAC(SPECL [`l:byte list`; `ofs:num`; `bc:num`; `2 * (t DIV 2)`]
    ZSTD_BITS_WINDOW_MOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o SYM)] THEN
  MP_TAC(SPECL [`zstd_bits l (8 * ofs + bc) (32 - bc)`; `t:num`]
    ZSTD_WINDOW_PAIRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2 =
    (zstd_bits l (8 * ofs + bc) (32 - bc) DIV 2 EXP (2 * (t DIV 2))) MOD 4`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; `8 * ofs + bc`; `2 * (t DIV 2) + 2`;
                  `2 * (t DIV 2)`] ZSTD_BITS_SPLIT) THEN
    REWRITE_TAC[ARITH_RULE `n <= n + 2`; ARITH_RULE `(n + 2) - n = 2`] THEN
    DISCH_THEN(SUBST1_TAC o SYM o REWRITE_RULE[GSYM ADD_ASSOC] o
               CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIV_MOD; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[]]);;

let NC_AND_MASK = prove
 (`!w k. k <= 32
         ==> word_and (word(2 EXP k - 1)) (word w):int32 =
             word(w MOD 2 EXP k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:32`,`:N`]
   (SPECL [`w:num`; `k:num`] WORD_AND_POW2_WORD)) THEN
  ASM_REWRITE_TAC[DIMINDEX_32] THEN SIMP_TAC[]);;

let NC_JUSHR_AND3 = prove
 (`!w k. w < 2 EXP 32 /\ k < 32
         ==> word_and (word_jushr (word w:int32) (word k)) (word 3) =
             word((w DIV 2 EXP k) MOD 4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k MOD 2 EXP 32 = k /\ k MOD 32 = k /\ w MOD 2 EXP 32 = w`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `k < 32` THEN UNDISCH_TAC `w < 2 EXP 32` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[word_jushr; word_ushr; DIMINDEX_32; VAL_WORD] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  MP_TAC(SPECL [`w DIV 2 EXP k`; `2`] NC_AND_MASK) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The theorems for the pieces of the function. They have the hypotheses     *)
(* nc_hyps, the regions nc_rr that may be read and nc_wr that may be         *)
(* written, and the frame nc_frame, with the callee-saved registers, which   *)
(* the code saves in its stack frame of 80 bytes, and the postcondition      *)
(* nc_post: the counts read as the specification gives them, or an error     *)
(* code if there is no description. nc_entry is the precondition at the      *)
(* entry, for an input of hbSize >= 8 bytes.                                 *)
(* ------------------------------------------------------------------------- *)

let nc_rr =
 `[hb,LENGTH(l:byte list); maxsvp,4; nc,2 * (maxsv + 1);
   word_sub stackpointer (word 80),80; word_add (word pc) (word 0x20010),8;
   ea,el]:(int64#num)list`
and nc_wr =
 `[nc,2 * (maxsv + 1); maxsvp,4; tlp,4;
   word_sub stackpointer (word 80),80]:(int64#num)list`;;

let nc_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\
  memset_memsafe_contract fset ea el ev /\
  8 <= LENGTH(l:byte list) /\ LENGTH l < 2 EXP 24 /\
  val(hb:int64) + LENGTH l + 8 < 2 EXP 64 /\ maxsv <= 255 /\
  nonoverlapping (nc:int64,2 * (maxsv + 1)) (word pc,0x20018) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (hb,LENGTH l) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (ea:int64,el) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (maxsvp:int64,4) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (tlp:int64,4) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (word_sub stackpointer (word 80),80) /\
  nonoverlapping (maxsvp,4) (word pc,0x20018) /\
  nonoverlapping (maxsvp,4) (hb,LENGTH l) /\
  nonoverlapping (maxsvp,4) (ea,el) /\
  nonoverlapping (maxsvp,4) (tlp,4) /\
  nonoverlapping (maxsvp,4) (word_sub stackpointer (word 80),80) /\
  nonoverlapping (tlp,4) (word pc,0x20018) /\
  nonoverlapping (tlp,4) (hb,LENGTH l) /\
  nonoverlapping (tlp,4) (ea,el) /\
  nonoverlapping (tlp,4) (word_sub stackpointer (word 80),80) /\
  nonoverlapping (word_sub stackpointer (word 80),80) (word pc,0x20018) /\
  nonoverlapping (word_sub stackpointer (word 80),80) (hb,LENGTH l) /\
  nonoverlapping (word_sub stackpointer (word 80),80) (ea,el)`;;

let nc_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [X19; X20; X21; X22; X23; X24; X29; X30; SP] ,,
  MAYCHANGE [memory :> bytes(nc,2 * (maxsv + 1)); memory :> bytes(maxsvp,4);
             memory :> bytes(tlp,4);
             memory :> bytes(word_sub stackpointer (word 80),80)]`;;

let nc_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `nc:int64`;
  `maxsvp:int64`; `tlp:int64`; `hb:int64`; `l:byte list`; `maxsv:num`;
  `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`; `x23:int64`;
  `x24:int64`; `x29:int64`; `fset:int64`; `ea:int64`; `el:num`; `ev:num`;
  `e:uarch_event list`];;

let mk_nc_goal extra pre post =
  let tm = mk_imp(nc_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; nc_frame]) in
  let vs = nc_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_nc_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let nc_post = with_memsafe nc_rr nc_wr `\s.
  read PC s = returnaddress /\ read SP s = stackpointer /\
  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
  read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
  read X29 s = x29 /\ read X30 s = returnaddress /\
  (!cs alog m.
      fse_ncount T 15 (maxsv + 1) l (cs,alog,m)
      ==> read X0 s = word m /\
          read (memory :> bytes(nc,2 * (maxsv + 1))) s =
          num_of_wordlist(fse_nclist cs (maxsv + 1)) /\
          read (memory :> bytes32 maxsvp) s = word(LENGTH cs - 1) /\
          read (memory :> bytes32 tlp) s = word alog) /\
  ((!r. ~fse_ncount T 15 (maxsv + 1) l r) ==> zstd_is_error(read X0 s))`;;

let nc_entry = with_memsafe nc_rr nc_wr `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x940) /\ read SP s = stackpointer /\
  read X30 s = returnaddress /\
  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
  read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
  read X29 s = x29 /\
  C_ARGUMENTS [nc; maxsvp; tlp; hb; word(LENGTH l)] s /\
  read (memory :> bytes32 maxsvp) s = word maxsv /\
  read (memory :> bytes(hb,LENGTH l)) s = num_of_bytelist l /\
  read (memory :> bytes64(word_add (word pc) (word 0x20010))) s = fset /\
  read (memory :> bytes(ea,el)) s = ev`;;

(* ------------------------------------------------------------------------- *)
(* The facts that hold all through the loop over the fields: the pointers    *)
(* and constants in registers, the saved registers and the input in memory,  *)
(* and the Accuracy_Log alog. nc_endp is the precondition at the end, 0xb9c, *)
(* where the code checks that the points have been used up exactly, the      *)
(* number of counts and the position, and works out the result.              *)
(* ------------------------------------------------------------------------- *)

let nc_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  zstd_bits l 0 4 + 5 = alog /\ alog <= 15 /\
  read SP s = word_sub stackpointer (word 80) /\
  read X0 s = word_add hb (word(LENGTH(l:byte list) - 7)) /\
  read X1 s = word_add hb (word(LENGTH l)) /\
  read X13 s = word_add hb (word(LENGTH l - 4)) /\
  read X3 s = word 1 /\ read X11 s = word 31 /\ read X12 s = word 32 /\
  read X19 s = word(maxsv + 1) /\ read X20 s = nc /\ read X21 s = maxsvp /\
  read X22 s = hb /\ read X23 s = tlp /\ read X24 s = word(LENGTH l) /\
  read (memory :> bytes64 (word_sub stackpointer (word 80))) s = x29 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 80)) (word 8))) s =
  returnaddress /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 80)) (word 16))) s = x19 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 80)) (word 24))) s = x20 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 80)) (word 32))) s = x21 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 80)) (word 40))) s = x22 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 80)) (word 48))) s = x23 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 80)) (word 56))) s = x24 /\
  read (memory :> bytes32 maxsvp) s = word maxsv /\
  read (memory :> bytes32 tlp) s = word alog /\
  read (memory :> bytes(hb,LENGTH l)) s = num_of_bytelist l`;;

let nc_endp = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`,
 mk_exists(`rmn:num`,list_mk_exists([`cs:int list`; `ofs:num`; `bc:num`],
  mk_conj(`read PC s = word(pc + 0xb9c) /\
           ofs + 4 <= LENGTH(l:byte list) /\ bc <= 47 /\
           (bc <= 23 \/ ofs + 4 = LENGTH l) /\
           read X8 s = word rmn /\ rmn < 2 EXP 31 /\
           read X4 s = word bc /\ read X5 s = word_add hb (word ofs) /\
           ((rmn = 1 /\ read X6 s = word(LENGTH cs) /\
             1 <= LENGTH cs /\ LENGTH cs <= maxsv + 1 /\
             (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
                  r = (cs,8 * ofs + bc)) /\
             read (memory :> bytes(nc,2 * (maxsv + 1))) s =
             num_of_wordlist(fse_nclist cs (maxsv + 1))) \/
            (~(rmn = 1) /\
             (!r. ~fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r)))`,
          nc_common)))));;

let NC_END = prove
 (mk_nc_goal [`alog:num`] nc_endp nc_post,
  ZSTD_INTRO_TAC THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
   [`rmn:num`; `cs:int list`; `ofs:num`; `bc:num`] THEN
  PUFF_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check
    (fun th -> is_disj(concl th) && free_in `rmn:num` (concl th))) THENL
   [ZSTD_STEPS_TAC (1--6) THEN ASM_CASES_TAC `bc <= 32` THEN
    ZSTD_STEPS_TAC (7--9) THENL
     [ZSTD_STEPS_TAC (10--20) THEN PUFF_FINAL_TAC THEN
      MP_TAC(SPECL [`l:byte list`; `maxsv + 1`; `alog:num`; `cs:int list`;
                    `8 * ofs + bc`] FSE_NCOUNT_RESULT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `8 * ofs + bc <= 8 * LENGTH(l:byte list)` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE;
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[WORD_RULE
         `word_sub (word_add (word_add (hb:int64) (word a)) (word b)) hb =
          word(a + b)`] THEN
        AP_TERM_TAC THEN
        REWRITE_TAC[ARITH_RULE `(8 * ofs + bc) + 7 = ofs * 8 + bc + 7`] THEN
        SIMP_TAC[DIV_MULT_ADD; ARITH_EQ];
        MATCH_MP_TAC(TAUT `~p ==> (p ==> q)`) THEN
        REWRITE_TAC[NOT_FORALL_THM] THEN MESON_TAC[]];
      ZSTD_STEPS_TAC (10--14) THEN PUFF_FINAL_TAC THEN
      MP_TAC(SPECL [`l:byte list`; `maxsv + 1`; `alog:num`; `cs:int list`;
                    `8 * ofs + bc`] FSE_NCOUNT_RESULT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(8 * ofs + bc <= 8 * LENGTH(l:byte list))`
      ASSUME_TAC THENL
       [UNDISCH_TAC `~(bc <= 32)` THEN
        UNDISCH_TAC `bc <= 23 \/ ofs + 4 = LENGTH(l:byte list)` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM; zstd_is_error] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC WORD_RULE];
    ZSTD_STEPS_TAC (1--8) THEN PUFF_FINAL_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `maxsv + 1`; `alog:num`] FSE_NCOUNT_FAIL) THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[zstd_is_error] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_RULE]);;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop, for the measure m: pts points left, the counts *)
(* cs so far and the window at offset ofs and bit bc, with either a field    *)
(* next (at 0xa30 or 0xab8), or a run of repeat flags (at 0xb04) after a     *)
(* probability 0, with zz probabilities 0 from the flags so far. In both     *)
(* cases what the specification reads from the start is what it reads from   *)
(* there, which is how the reading is followed as the code goes on. nc_a54   *)
(* is the state after a field, with its value v, and nc_a6c that after the   *)
(* store of the count.                                                       *)
(* ------------------------------------------------------------------------- *)

let nc_state =
 `1 <= pts /\ pts <= 2 EXP alog /\ LENGTH(cs:int list) < maxsv + 1 /\
  ofs + 4 <= LENGTH(l:byte list) /\ bc <= 31 /\
  (bc <= 7 \/ ofs + 4 = LENGTH l) /\
  read X8 s = word(pts + 1) /\
  read X9 s = word(2 EXP (bitsize(pts + 1) - 1)) /\
  read X10 s = word(bitsize(pts + 1)) /\
  read X5 s = word_add hb (word ofs) /\ read X14 s = word bc /\
  read X4 s = word(zstd_bits l (8 * ofs + bc) (32 - bc)) /\
  read (memory :> bytes(nc,2 * (maxsv + 1))) s =
  num_of_wordlist(fse_nclist cs (maxsv + 1))`;;

let nc_field_disj =
 `(read PC s = word(pc + 0xa30) \/ read PC s = word(pc + 0xab8)) /\
  m = ((maxsv + 2) - LENGTH(cs:int list)) * (4 * LENGTH(l:byte list) + 4) /\
  read X6 s = word(LENGTH cs) /\
  (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
       fse_counts T l (maxsv + 1) (pts,cs,8 * ofs + bc) r)`;;

let nc_zeros_disj =
 `read PC s = word(pc + 0xb04) /\
  m = ((maxsv + 2) - (LENGTH(cs:int list) + 1 + zz)) *
      (4 * LENGTH(l:byte list) + 4) + nc_inner (LENGTH l) ofs bc + 1 /\
  read X6 s = word(LENGTH cs + 1 + zz) /\
  zz + 36 * nc_inner (LENGTH l) ofs bc <= 36 * (4 * LENGTH l + 2) /\
  (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
       ?z q'. fse_zeros T l (0,zz,8 * ofs + bc) (z,q') /\
              fse_counts T l (maxsv + 1)
                (pts,APPEND cs (REPLICATE (z + 1) (&0)),q') r)`;;

let nc_inv = with_memsafe nc_rr nc_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   list_mk_exists([`pts:num`; `cs:int list`; `ofs:num`; `bc:num`; `zz:num`],
     list_mk_conj[nc_state; nc_common;
                  mk_disj(nc_field_disj,nc_zeros_disj)])));;

let nc_loopp = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`,
  mk_conj(`read PC s = word(pc + 0xa30) /\
           read X8 s = word(2 EXP alog + 1) /\ read X9 s = word(2 EXP alog) /\
           read X10 s = word(alog + 1) /\ read X6 s = word 0 /\
           read X5 s = hb /\ read X14 s = word 4 /\
           read X4 s = word(zstd_bits l 4 28) /\
           read (memory :> bytes(nc,2 * (maxsv + 1))) s = 0`,nc_common)));;

(*** At 0xa54 X4 holds the new bit position, not the window ***)

let nc_state_a54 =
  list_mk_conj(filter (fun t -> not(free_in `X4` t)) (conjuncts nc_state));;

let nc_a54 = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`,
  list_mk_conj
   [`read PC s = word(pc + 0xa54) /\
     fse_field l pts (8 * ofs + bc) = (v,8 * ofs + bq) /\
     read X2 s = word v /\ read X4 s = word bq /\
     read X6 s = word(LENGTH(cs:int list)) /\
     (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
          fse_counts T l (maxsv + 1) (pts,cs,8 * ofs + bc) r)`;
    nc_state_a54; nc_common]));;

let nc_a54_post =
  let m = `m:num` and s = `s:armstate` in
  let app f xs = rhs(concl(DEPTH_CONV BETA_CONV (list_mk_comb(f,xs)))) in
  mk_abs(s,mk_disj
   (mk_exists(m,mk_conj
     (`m < ((maxsv + 2) - LENGTH(cs:int list)) *
           (4 * LENGTH(l:byte list) + 4)`,app nc_inv [m; s])),
    app nc_post [s]));;

let nc_a6c = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`, mk_conj(
 `read PC s = word(pc + 0xa6c) /\
  LENGTH(cs:int list) < maxsv + 1 /\
  ofs + 4 <= LENGTH(l:byte list) /\ bq <= 47 /\
  (bq <= 23 \/ ofs + 4 = LENGTH l) /\
  1 <= rmn /\ rmn <= 2 EXP alog + 1 /\ v <= 2 EXP alog + 1 /\
  2 <= nb /\ nb <= 16 /\ rmn < 2 EXP nb /\
  (v = 1 ==> 2 EXP (nb - 1) <= rmn) /\
  read X8 s = word rmn /\ read X9 s = word(2 EXP (nb - 1)) /\
  read X10 s = word nb /\
  read X6 s = word(LENGTH cs + 1) /\ read X4 s = word bq /\
  read X5 s = word_add hb (word ofs) /\
  read X2 s = word_zx(iword(&v - &1):int32) /\
  read (memory :> bytes(nc,2 * (maxsv + 1))) s =
  num_of_wordlist(fse_nclist (APPEND cs [&v - &1]) (maxsv + 1)) /\
  (rmn = 1 /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        r = (APPEND cs [&v - &1],8 * ofs + bq)) \/
   2 <= rmn /\ ~(v = 1) /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        fse_counts T l (maxsv + 1)
          (rmn - 1,APPEND cs [&v - &1],fse_reload T l (8 * ofs + bq)) r) \/
   2 <= rmn /\ v = 1 /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        ?z q'. fse_zeros T l (0,0,fse_reload T l (8 * ofs + bq)) (z,q') /\
               fse_counts T l (maxsv + 1)
                 (rmn - 1,APPEND cs (REPLICATE (z + 1) (&0)),q') r))`,
 nc_common)));;

(* ------------------------------------------------------------------------- *)
(* Simulation: NC_STEP_TAC n is ZSTD_STEP_TAC n, deciding branches on the    *)
(* signed comparisons of the code and on tests of a register for 0, and      *)
(* forgetting the flags once a branch is decided. The other tactics rewrite  *)
(* assumptions, replace the fact about a register, and put the window after  *)
(* a load and a shift and the pointer to the input in their normal forms.    *)
(* ------------------------------------------------------------------------- *)

let WORD_CMP_32_SFLAGS_ALT = prove
 (`!x y. x < 2147483648 /\ y < 2147483648
         ==> &x - ival(word y:int32) = ival(word_sub (word x) (word y):int32)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `y:num`] WORD_CMP_32_SFLAGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o el 1 o CONJUNCTS) THEN
  SUBGOAL_THEN `ival(word x:int32) = &x /\ ival(word y:int32) = &y`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[WORD_IWORD] THEN CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC(NUM_REDUCE_CONV THENC
      INT_REDUCE_CONV) THEN
    ASM_SIMP_TAC[INT_OF_NUM_LT; INT_ARITH `--(&2147483648) <= &x:int`];
    REFL_TAC]);;

(*** Drop the facts about the flags in the current state ***)

let NC_DROP_FLAGS_TAC : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let flags = [`NF`; `ZF`; `CF`; `VF`] in
  let is_flag t =
    let t' = if is_neg t then rand t else t in
    let t'' = if is_eq t' then lhs t' else t' in
    match t'' with
      Comb(Comb(Const("read",_),c),s') -> s' = s && mem c flags
    | _ -> false in
  (REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_flag o concl)))) gl;;

(*** Decide a branch on val x = 0, with the fact about it ***)

let NC_PC_VAL_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) ->
    let c = concl th in
    let c' = if is_neg c then rand c else c in
    if is_eq c' && is_comb(lhs c') &&
       (try fst(dest_const(rator(lhs c'))) = "val" with Failure _ -> false) &&
       rhs c' = `0`
    then th else failwith "") asl in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),r)
        when is_cond r -> REWRITE_RULE ths th
    | _ -> th) gl;;

let NC_STEP_TAC n =
  let pc_conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),t)
          when s' = s -> is_cond t
      | _ -> false) asl in
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  let pipeline =
    TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
    TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                      WORD_CMP_64_SFLAGS) THEN
    TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
    PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
    TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC THEN
    (fun gl -> if pc_conditional gl then
                 (TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int32`
                                    WORD_CMP_32_SFLAGS_ALT) THEN
                  PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC) gl
               else ALL_TAC gl) in
  ARM_STEPS_TAC ZSTD_EXEC [n] THEN ZSTD_SMALL_WORD_TAC THEN
  (fun gl ->
     if pc_conditional gl then
       (NC_PC_VAL_TAC THEN
        (fun gl' -> if pc_conditional gl' then pipeline gl' else ALL_TAC gl')
        THEN NC_DROP_FLAGS_TAC) gl
     else if conditional gl then pipeline gl
     else ALL_TAC gl);;

let NC_STEPS_TAC ns = MAP_EVERY NC_STEP_TAC ns;;

(*** Rewrite the assumptions with the facts tms, keeping those facts ***)

let NC_ASSUME_REWRITE_TAC tms =
  RULE_ASSUM_TAC(fun th ->
    if mem (concl th) tms then th else REWRITE_RULE (map ASSUME tms) th);;

(*** Abbreviate the threshold 2^(nb - 1) as thr, with its bounds ***)

let NC_THR_TAC =
  SUBGOAL_THEN `2 <= 2 EXP (nb - 1) /\ 2 EXP (nb - 1) <= 32768 /\
                2 EXP nb = 2 * 2 EXP (nb - 1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [TRANS_TAC LE_TRANS `2 EXP 1` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC];
      TRANS_TAC LE_TRANS `2 EXP 15` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_EXP] THEN SIMPLE_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
      REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `thr = 2 EXP (nb - 1)` THEN
  NC_ASSUME_REWRITE_TAC [`2 EXP (nb - 1) = thr`];;

(*** The window load at the state s with the new offset ofs' ***)

let NC_LOAD_FACT_TAC ofs' s =
  MP_TAC(SPECL [`hb:int64`; `LENGTH(l:byte list)`; `num_of_bytelist l`;
                ofs'; s] READ_MEMORY_BYTES32_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** The window after the shift, in terms of zstd_bits ***)

let NC_X4_TAC : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let rd = mk_comb(`read X4`,s) in
  let th = snd(find (fun (_,th) -> let c = concl th in
                       is_eq c && lhs c = rd) asl) in
  let pat = `word_zx (word_jushr
               (word ((num_of_bytelist l DIV 2 EXP (8 * ofs)) MOD
                      4294967296):int32) (word bc)):int64` in
  let i = term_match [] pat (rhs(concl th)) in
  let ofs' = instantiate i `ofs:num` and bc' = instantiate i `bc:num` in
  let lth = SPECL [`l:byte list`; ofs'; bc'] NC_WINDOW_LEMMA in
  let bth = TAC_PROOF((asl,lhand(concl lth)), SIMPLE_ARITH_TAC) in
  let eth = MP lth bth in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th then
                              ASSUME_TAC(REWRITE_RULE[eth] th')
                            else NO_TAC)) gl;;

(*** Normalize the value of X5 to word_add hb (word k) ***)

let NC_X5_NORM_TAC : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let conv = TRY_CONV(REWR_CONV(WORD_RULE
    `word_add (word_add (hb:int64) (word a)) (word b) =
     word_add hb (word(a + b))`)) in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("X5",_)),s')),_)
        when s' = s -> CONV_RULE(RAND_CONV conv) th
    | _ -> th) gl;;

(*** The new position after the reload, for each of its three cases ***)

let NC_RELOAD_POS_TAC ofs' bc' =
  SUBGOAL_THEN (mk_eq(`fse_reload T l (8 * ofs + bq)`,
                      mk_binop `(+):num->num->num`
                        (mk_binop `( * ):num->num->num` `8` ofs') bc'))
  ASSUME_TAC THENL
   [FIRST
     [MP_TAC(SPECL [`l:byte list`; `8 * ofs + bq`] FSE_RELOAD_NOWRAP) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      SIMPLE_ARITH_TAC;
      MP_TAC(SPECL [`l:byte list`; `8 * ofs + bq`] FSE_RELOAD_WRAP) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC];
    ALL_TAC];;

(*** The reload, from the step k at 0xa94 to the test of the count at ab4, ***)
(*** then fin ofs' bc' for the new offset and bit count                    ***)

let NC_RELOAD_TAC k fin =
  MP_TAC(SPEC `bq:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `ofs <= LENGTH(l:byte list) - 7` THENL
   [SUBGOAL_THEN `bq <= 23` ASSUME_TAC THENL
     [UNDISCH_TAC `bq <= 23 \/ ofs + 4 = LENGTH(l:byte list)` THEN
      UNDISCH_TAC `ofs <= LENGTH(l:byte list) - 7` THEN
      UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN ARITH_TAC;
      ALL_TAC] THEN
    NC_STEPS_TAC (k--(k+5)) THEN
    NC_LOAD_FACT_TAC `ofs + bq DIV 8`
      (mk_var("s"^string_of_int(k+5),`:armstate`)) THEN
    NC_STEPS_TAC ((k+6)--(k+7)) THEN NC_X4_TAC THEN
    NC_STEPS_TAC [k+8] THEN NC_PC_VAL_TAC THEN NC_X5_NORM_TAC THEN
    NC_RELOAD_POS_TAC `ofs + bq DIV 8` `bq MOD 8` THEN
    fin `ofs + bq DIV 8` `bq MOD 8`;
    SUBGOAL_THEN
     `val(word_add (word_add hb (word ofs)) (word (bq DIV 8)):int64) =
      val hb + ofs + bq DIV 8`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      MATCH_MP_TAC VAL_WORD_ADD_NOWRAP THEN
      UNDISCH_TAC `val(hb:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64` THEN
      UNDISCH_TAC `ofs + 4 <= LENGTH(l:byte list)` THEN
      UNDISCH_TAC `bq <= 47` THEN
      UNDISCH_TAC `8 * bq DIV 8 + bq MOD 8 = bq` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `ofs + bq DIV 8 <= LENGTH(l:byte list) - 4` THENL
     [NC_STEPS_TAC (k--(k+7)) THEN
      NC_LOAD_FACT_TAC `ofs + bq DIV 8`
        (mk_var("s"^string_of_int(k+7),`:armstate`)) THEN
      NC_STEPS_TAC ((k+8)--(k+9)) THEN NC_X4_TAC THEN
      NC_STEPS_TAC [k+10] THEN NC_PC_VAL_TAC THEN NC_X5_NORM_TAC THEN
      NC_RELOAD_POS_TAC `ofs + bq DIV 8` `bq MOD 8` THEN
      fin `ofs + bq DIV 8` `bq MOD 8`;
      NC_STEPS_TAC (k--(k+10)) THEN
      MP_TAC(SPECL [`hb:int64`; `LENGTH(l:byte list)`; `ofs:num`; `bq:num`]
        NC_WRAP_BC) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      MP_TAC(SPECL [`bq - 8 * (LENGTH(l:byte list) - 4 - ofs)`; `32`]
        MOD_LT_EQ) THEN
      REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
      NC_LOAD_FACT_TAC `LENGTH(l:byte list) - 4`
        (mk_var("s"^string_of_int(k+10),`:armstate`)) THEN
      NC_STEPS_TAC ((k+11)--(k+12)) THEN NC_X4_TAC THEN
      NC_STEPS_TAC [k+13] THEN NC_PC_VAL_TAC THEN
      NC_RELOAD_POS_TAC `LENGTH(l:byte list) - 4`
        `(bq - 8 * (LENGTH(l:byte list) - 4 - ofs)) MOD 32` THEN
      fin `LENGTH(l:byte list) - 4`
          `(bq - 8 * (LENGTH(l:byte list) - 4 - ofs)) MOD 32`]];;

(*** The invariant for the next field, at ab8, from a6c ***)

let NC_FIELD_FIN_TAC ofs' bc' =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `((maxsv + 2) - (LENGTH(cs:int list) + 1)) *
              (4 * LENGTH(l:byte list) + 4)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LT_MULT_RCANCEL] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`rmn - 1`; `APPEND cs [&v - &1]:int list`; ofs'; bc'; `0`] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `n + SUC 0 = n + 1`] THEN
  SUBGOAL_THEN `rmn - 1 + 1 = rmn` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [SIMPLE_ARITH_TAC; DISJ1_TAC THEN SIMPLE_ARITH_TAC;
         DISJ2_TAC THEN SIMPLE_ARITH_TAC];;

(* ------------------------------------------------------------------------- *)
(* From the reload at 0xa94 to the field or the repeat flags after it.       *)
(* ------------------------------------------------------------------------- *)

let NC_INNER_BOUND = prove
 (`!len ofs bc. nc_inner len ofs bc <= 4 * len + 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nc_inner] THEN
  REPEAT COND_CASES_TAC THEN ARITH_TAC);;

let NC_MEASURE_LT = prove
 (`!k b x. x < b ==> k * b + x < (k + 1) * b`,
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

let FSE_NCLIST_APPEND_ZERO = prove
 (`!cs n. fse_nclist (APPEND cs [&1 - &1]) n = fse_nclist cs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_SUB_REFL] THEN
  MP_TAC(SPECL [`cs:int list`; `1`; `n:num`] FSE_NCLIST_APPEND_ZEROS) THEN
  REWRITE_TAC[num_CONV `1`; REPLICATE]);;

(*** The invariant for the zero flags, at b04, from a6c ***)

let NC_ZEROS_FIN_TAC ofs' bc' =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC (subst [ofs',`ofs':num`; bc',`bc':num`]
   `((maxsv + 2) - (LENGTH(cs:int list) + 1 + 0)) *
    (4 * LENGTH(l:byte list) + 4) + nc_inner (LENGTH l) ofs' bc' + 1`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN `(maxsv + 2) - LENGTH(cs:int list) =
                  ((maxsv + 2) - (LENGTH cs + 1)) + 1` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; MATCH_MP_TAC NC_MEASURE_LT] THEN
    MP_TAC(SPECL [`LENGTH(l:byte list)`; ofs'; bc'] NC_INNER_BOUND) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rmn - 1`; `cs:int list`; ofs'; bc'; `0`] THEN
  SUBGOAL_THEN `rmn - 1 + 1 = rmn` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FSE_NCLIST_APPEND_ZERO]) THEN
  NC_PC_NE_TAC 2820 2608 THEN NC_PC_NE_TAC 2820 2744 THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(SPECL [`LENGTH(l:byte list)`; ofs'; bc'] NC_INNER_BOUND) THEN
  REPEAT CONJ_TAC THEN
  FIRST [SIMPLE_ARITH_TAC; DISJ1_TAC THEN SIMPLE_ARITH_TAC;
         DISJ2_TAC THEN SIMPLE_ARITH_TAC; ARITH_TAC];;

let NC_V_LE_TAC =
  TRANS_TAC LE_TRANS `2 EXP alog + 1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= 32768 ==> a + 1 <= 65536`) THEN
  TRANS_TAC LE_TRANS `2 EXP 15` THEN REWRITE_TAC[LE_EXP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The piece from 0xa94: the reload of the window, and the test of whether   *)
(* the count was 0, with the repeat flags next then.                         *)
(* ------------------------------------------------------------------------- *)

let nc_a94 = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`, mk_conj(
 `read PC s = word(pc + 0xa94) /\
  LENGTH(cs:int list) + 1 < maxsv + 1 /\
  ofs + 4 <= LENGTH(l:byte list) /\ bq <= 47 /\
  (bq <= 23 \/ ofs + 4 = LENGTH l) /\
  2 <= rmn /\ rmn <= 2 EXP alog + 1 /\ v <= 65536 /\
  read X8 s = word rmn /\ read X9 s = word(2 EXP (bitsize rmn - 1)) /\
  read X10 s = word(bitsize rmn) /\
  read X6 s = word(LENGTH cs + 1) /\ read X4 s = word bq /\
  read X5 s = word_add hb (word ofs) /\
  read X2 s = word_zx(iword(&v - &1):int32) /\
  read (memory :> bytes(nc,2 * (maxsv + 1))) s =
  num_of_wordlist(fse_nclist (APPEND cs [&v - &1]) (maxsv + 1)) /\
  (~(v = 1) /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        fse_counts T l (maxsv + 1)
          (rmn - 1,APPEND cs [&v - &1],fse_reload T l (8 * ofs + bq)) r) \/
   v = 1 /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        ?z q'. fse_zeros T l (0,0,fse_reload T l (8 * ofs + bq)) (z,q') /\
               fse_counts T l (maxsv + 1)
                 (rmn - 1,APPEND cs (REPLICATE (z + 1) (&0)),q') r))`,
 nc_common)));;

let NC_A94 = prove
 (mk_nc_goal [`alog:num`; `cs:int list`; `v:num`; `ofs:num`; `bq:num`;
              `rmn:num`] nc_a94 nc_a54_post,
  ZSTD_INTRO_TAC THEN GLOBALIZE_PRECONDITION_TAC THEN
  PUFF_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check
    (fun th -> is_disj(concl th) && free_in `fse_zeros` (concl th))) THENL
   [SUBGOAL_THEN `~(val(iword(&v - &1):int32) = 0)` ASSUME_TAC THENL
     [MATCH_MP_TAC NC_COUNT_NONZERO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    NC_RELOAD_TAC 1 NC_FIELD_FIN_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASSUME_TAC NC_COUNT_ZERO THEN
    NC_RELOAD_TAC 1 NC_ZEROS_FIN_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The piece from 0xa6c: the update of the threshold and of the number of    *)
(* bits for the next field, the end of the loop when there is at most 1      *)
(* point left, and the check of the number of counts.                        *)
(* ------------------------------------------------------------------------- *)

(*** From a8c (step k): the check of the number of symbols, then going on ***)
(*** with NC_A94, or to the end with an error                              ***)

let NC_CHARNUM2_TAC k errcs insts =
  ASM_CASES_TAC `LENGTH(cs:int list) + 1 < maxsv + 1` THEN
  NC_STEPS_TAC (k--(k+1)) THENL
   [ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) NC_A94 insts THEN
    MEMSAFE_ELIM_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [SIMPLE_ARITH_TAC; NC_V_LE_TAC; ALL_TAC];
    ZSTD_CONTINUE_TAC NC_END [] THEN MEMSAFE_ELIM_TAC THEN
    MAP_EVERY EXISTS_TAC [`rmn:num`; errcs; `ofs:num`; `bq:num`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    TRY DISJ2_TAC THEN TRY(CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    TRY(MATCH_MP_TAC(TAUT `~q ==> ~(p /\ q)`)) THEN
    MATCH_MP_TAC FSE_COUNTS_FULL THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_REPLICATE] THEN
    SIMPLE_ARITH_TAC];;

let NC_A6C = prove
 (mk_nc_goal [`alog:num`; `cs:int list`; `v:num`; `ofs:num`; `bq:num`;
              `rmn:num`; `nb:num`] nc_a6c nc_a54_post,
  ZSTD_INTRO_TAC THEN GLOBALIZE_PRECONDITION_TAC THEN NC_THR_TAC THEN
  PUFF_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o check
    (fun th -> is_disj(concl th) && free_in `rmn:num` (concl th))) THENL
   [NC_STEPS_TAC (1--4) THEN
    ZSTD_CONTINUE_TAC NC_END [] THEN MEMSAFE_ELIM_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `APPEND cs [&v - &1]:int list`; `ofs:num`;
                          `bq:num`] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ASM_CASES_TAC `rmn < thr` THENL
     [NC_STEPS_TAC (1--8) THEN
      MP_TAC(SPEC `bitsize rmn` NC_THR_UPDATE) THEN ANTS_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= b <=> ~(b = 0)`; BITSIZE_EQ_0;
                    BITSIZE_LE] THEN
        CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        TRANS_TAC LTE_TRANS `2 EXP nb` THEN ASM_REWRITE_TAC[LE_EXP] THEN
        SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      NC_CHARNUM2_TAC 9 `APPEND cs [&v - &1]:int list` [];
      SUBGOAL_THEN `bitsize rmn = nb` ASSUME_TAC THENL
       [REWRITE_TAC[BITSIZE_UNIQUE_EQ] THEN ASM_REWRITE_TAC[] THEN
        SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      NC_STEPS_TAC (1--2) THEN
      NC_CHARNUM2_TAC 3 `APPEND cs [&v - &1]:int list` []];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    SUBGOAL_THEN `bitsize rmn = nb` ASSUME_TAC THENL
     [REWRITE_TAC[BITSIZE_UNIQUE_EQ] THEN ASM_REWRITE_TAC[] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    NC_STEPS_TAC (1--2) THEN
    NC_CHARNUM2_TAC 3 `APPEND cs (REPLICATE (z + 1) (&0)):int list`
      [`1`,`v:num`]]);;

(* ------------------------------------------------------------------------- *)
(* The piece from 0xa54: the store of the count v - 1 and the update of the  *)
(* points left.                                                              *)
(* ------------------------------------------------------------------------- *)

let NC_A54_MEM_TAC =
  MP_TAC(ISPECL [`nc:int64`; `fse_nclist cs (maxsv + 1)`;
                 `fse_nclist (APPEND cs [&v - &1]) (maxsv + 1)`;
                 `LENGTH(cs:int list)`; `s6:armstate`]
    READ_MEMORY_WORDLIST16_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_NCLIST] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_FSE_NCLIST_SNOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    ASM_SIMP_TAC[NC_COUNT_POS_N; ARITH_RULE `~(v = 0) ==> 1 <= v`] THEN
    SIMP_TAC[];
    DISCH_TAC];;

let NC_A54_MEM0_TAC =
  MP_TAC(ISPECL [`nc:int64`; `fse_nclist cs (maxsv + 1)`;
                 `fse_nclist (APPEND cs [&0 - &1]) (maxsv + 1)`;
                 `LENGTH(cs:int list)`; `s6:armstate`]
    READ_MEMORY_WORDLIST16_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_NCLIST] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_FSE_NCLIST_SNOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN SIMP_TAC[];
    DISCH_TAC];;

let NC_A54 = prove
 (mk_nc_goal [`alog:num`; `pts:num`; `cs:int list`; `ofs:num`; `bc:num`;
              `v:num`; `bq:num`] nc_a54 nc_a54_post,
  ZSTD_INTRO_TAC THEN GLOBALIZE_PRECONDITION_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `pts:num`; `8 * ofs + bc`; `v:num`;
                `8 * ofs + bq`] FSE_FIELD_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN `bq <= bc + bitsize(pts + 1) /\
                  bc + bitsize(pts + 1) <= bq + 1` STRIP_ASSUME_TAC THENL
     [MP_TAC th THEN ARITH_TAC; ALL_TAC]) THEN
  SUBGOAL_THEN `bitsize(pts + 1) <= 16 /\ pts <= 32768 /\ v <= 65536`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `pts <= 32768` ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS `2 EXP alog` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP 15` THEN REWRITE_TAC[LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[BITSIZE_LE] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `bq <= 47 /\ (bq <= 23 \/ ofs + 4 = LENGTH(l:byte list))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check
     (fun th -> concl th = `bc <= 7 \/ ofs + 4 = LENGTH(l:byte list)`)) THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_points v <= pts` ASSUME_TAC THENL
   [MATCH_MP_TAC FSE_POINTS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `maxsv + 1`; `pts:num`; `cs:int list`;
                `8 * ofs + bc`; `v:num`; `8 * ofs + bq`] FSE_COUNTS_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `pts + 1` BITSIZE) THEN DISCH_TAC THEN
  SUBGOAL_THEN `v = 1 ==> 2 EXP (bitsize(pts + 1) - 1) <=
                          (pts + 1) - fse_points v`
  ASSUME_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[fse_points] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUB_0] THEN
    MATCH_MP_TAC BITSIZE_REV THEN ARITH_TAC;
    ALL_TAC] THEN
  PUFF_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`nc:int64`; `fse_nclist cs (maxsv + 1)`;
                 `LENGTH(cs:int list)`; `s0:armstate`]
    READ_MEMORY_WORDLIST16_SPLIT) THEN
  ASM_REWRITE_TAC[LENGTH_FSE_NCLIST] THEN STRIP_TAC THEN
  UXTW_ABBREV_TAC `X6` `v6:int64` `LENGTH(cs:int list)` THEN
  ASM_CASES_TAC `v = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN NC_STEPS_TAC (1--6) THEN
    UNDISCH_THEN `word(LENGTH(cs:int list)):int64 = v6`
      (SUBST_ALL_TAC o SYM) THEN
    NC_SET_REG_TAC `read X6 s6 = word(LENGTH(cs:int list) + 1)`
     (ASM_REWRITE_TAC[] THEN
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      REFL_TAC) THEN
    NC_SET_REG_TAC `read X8 s6 = word((pts + 1) - fse_points 0)`
     (ASM_REWRITE_TAC[fse_points] THEN
      REWRITE_TAC[ARITH_RULE `(pts + 1) - 1 = pts`] THEN
      MATCH_MP_TAC NC_REM_NEG THEN SIMPLE_ARITH_TAC) THEN
    NC_SET_REG_TAC `read X2 s6 = word_zx(iword(&0 - &1):int32)`
     (ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
    NC_A54_MEM0_TAC THEN
    ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) NC_A6C
     [`0`,`v:num`; `(pts + 1) - fse_points 0`,`rmn:num`;
      `bitsize(pts + 1)`,`nb:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC;
    MP_TAC(ISPEC `v - 1` NC_IVAL_SMALL) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    NC_STEPS_TAC (1--6) THEN
    UNDISCH_THEN `word(LENGTH(cs:int list)):int64 = v6`
      (SUBST_ALL_TAC o SYM) THEN
    NC_SET_REG_TAC `read X6 s6 = word(LENGTH(cs:int list) + 1)`
     (ASM_REWRITE_TAC[] THEN
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      REFL_TAC) THEN
    NC_SET_REG_TAC `read X8 s6 = word((pts + 1) - fse_points v)`
     (ASM_REWRITE_TAC[fse_points] THEN
      REWRITE_TAC[INT_OF_NUM_LT; ARITH_RULE `~(n < 0)`]) THEN
    NC_SET_REG_TAC `read X2 s6 = word_zx(iword(&v - &1):int32)`
     (ASM_SIMP_TAC[NC_COUNT_POS_N; ARITH_RULE `~(v = 0) ==> 1 <= v`] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
      REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMPLE_ARITH_TAC) THEN
    NC_A54_MEM_TAC THEN
    ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) NC_A6C
     [`(pts + 1) - fse_points v`,`rmn:num`; `bitsize(pts + 1)`,`nb:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The piece from 0xb4c: the reload of the window after a run of repeat      *)
(* flags, and on with the next field.                                        *)
(* ------------------------------------------------------------------------- *)

(*** The reload after the flags, from b4c (step k) to the field at a30 ***)

let NC_RELOAD_B4C_TAC k fin =
  MP_TAC(SPEC `bq:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `ofs <= LENGTH(l:byte list) - 7` THENL
   [SUBGOAL_THEN `bq <= 31` ASSUME_TAC THENL
     [UNDISCH_TAC `bq <= 31 \/ ofs + 4 = LENGTH(l:byte list)` THEN
      UNDISCH_TAC `ofs <= LENGTH(l:byte list) - 7` THEN
      UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN ARITH_TAC;
      ALL_TAC] THEN
    NC_STEPS_TAC (k--(k+4)) THEN
    NC_LOAD_FACT_TAC `ofs + bq DIV 8`
      (mk_var("s"^string_of_int(k+4),`:armstate`)) THEN
    NC_STEPS_TAC [k+5; k+6] THEN NC_X4_TAC THEN
    NC_STEPS_TAC [k+7] THEN NC_X5_NORM_TAC THEN
    NC_RELOAD_POS_TAC `ofs + bq DIV 8` `bq MOD 8` THEN
    fin `ofs + bq DIV 8` `bq MOD 8`;
    SUBGOAL_THEN
     `val(word_add (word_add hb (word ofs)) (word (bq DIV 8)):int64) =
      val hb + ofs + bq DIV 8`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      MATCH_MP_TAC VAL_WORD_ADD_NOWRAP THEN
      UNDISCH_TAC `val(hb:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64` THEN
      UNDISCH_TAC `ofs + 4 <= LENGTH(l:byte list)` THEN
      UNDISCH_TAC `bq <= 55` THEN
      UNDISCH_TAC `8 * bq DIV 8 + bq MOD 8 = bq` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `ofs + bq DIV 8 <= LENGTH(l:byte list) - 4` THENL
     [NC_STEPS_TAC (k--(k+7)) THEN
      NC_LOAD_FACT_TAC `ofs + bq DIV 8`
        (mk_var("s"^string_of_int(k+7),`:armstate`)) THEN
      NC_STEPS_TAC [k+8; k+9] THEN NC_X4_TAC THEN
      NC_STEPS_TAC [k+10] THEN NC_X5_NORM_TAC THEN
      NC_RELOAD_POS_TAC `ofs + bq DIV 8` `bq MOD 8` THEN
      fin `ofs + bq DIV 8` `bq MOD 8`;
      NC_STEPS_TAC (k--(k+11)) THEN
      MP_TAC(SPECL [`hb:int64`; `LENGTH(l:byte list)`; `ofs:num`; `bq:num`]
        NC_WRAP_BC) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      MP_TAC(SPECL [`bq - 8 * (LENGTH(l:byte list) - 4 - ofs)`; `32`]
        MOD_LT_EQ) THEN
      REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
      NC_LOAD_FACT_TAC `LENGTH(l:byte list) - 4`
        (mk_var("s"^string_of_int(k+11),`:armstate`)) THEN
      NC_STEPS_TAC [k+12; k+13] THEN NC_X4_TAC THEN
      NC_STEPS_TAC [k+14] THEN
      NC_RELOAD_POS_TAC `LENGTH(l:byte list) - 4`
        `(bq - 8 * (LENGTH(l:byte list) - 4 - ofs)) MOD 32` THEN
      fin `LENGTH(l:byte list) - 4`
          `(bq - 8 * (LENGTH(l:byte list) - 4 - ofs)) MOD 32`]];;

let nc_b4c = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`, list_mk_conj
 [`read PC s = word(pc + 0xb4c) /\
   1 <= pts /\ pts <= 2 EXP alog /\
   LENGTH(cs:int list) + z + 1 < maxsv + 1 /\
   ofs + 4 <= LENGTH(l:byte list) /\ bq <= 55 /\
   (bq <= 31 \/ ofs + 4 = LENGTH l) /\
   read X8 s = word(pts + 1) /\
   read X9 s = word(2 EXP (bitsize(pts + 1) - 1)) /\
   read X10 s = word(bitsize(pts + 1)) /\
   read X6 s = word(LENGTH cs + z + 1) /\ read X4 s = word bq /\
   read X5 s = word_add hb (word ofs) /\ read X15 s = word_add hb (word ofs) /\
   read (memory :> bytes(nc,2 * (maxsv + 1))) s =
   num_of_wordlist(fse_nclist cs (maxsv + 1)) /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        fse_counts T l (maxsv + 1)
         (pts,APPEND cs (REPLICATE (z + 1) (&0)),
          fse_reload T l (8 * ofs + bq)) r)`;
  nc_common]));;

let nc_b4c_post =
  let m = `m:num` and s = `s:armstate` in
  let app f xs = rhs(concl(DEPTH_CONV BETA_CONV (list_mk_comb(f,xs)))) in
  mk_abs(s,mk_disj
   (mk_exists(m,mk_conj
     (`m < ((maxsv + 2) - (LENGTH(cs:int list) + z + 1)) *
           (4 * LENGTH(l:byte list) + 4) + 1`,app nc_inv [m; s])),
    app nc_post [s]));;

let NC_FIELD_FIN2_TAC ofs' bc' =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `((maxsv + 2) - (LENGTH(cs:int list) + z + 1)) *
              (4 * LENGTH(l:byte list) + 4)` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`pts:num`; `APPEND cs (REPLICATE (z + 1) (&0)):int list`; ofs'; bc';
    `0`] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; FSE_NCLIST_APPEND_ZEROS] THEN
  REWRITE_TAC[ARITH_RULE `a + z + 1 = a + (z + 1)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [SIMPLE_ARITH_TAC; DISJ1_TAC THEN SIMPLE_ARITH_TAC;
         DISJ2_TAC THEN SIMPLE_ARITH_TAC];;

let NC_B4C = prove
 (mk_nc_goal [`alog:num`; `pts:num`; `cs:int list`; `z:num`; `ofs:num`;
              `bq:num`] nc_b4c nc_b4c_post,
  ZSTD_INTRO_TAC THEN GLOBALIZE_PRECONDITION_TAC THEN
  PUFF_INIT_TAC "s0" THEN NC_RELOAD_B4C_TAC 1 NC_FIELD_FIN2_TAC);;

(* ------------------------------------------------------------------------- *)
(* The piece for a field, from 0xa30 or 0xab8 to 0xa54: a value of nb - 1    *)
(* bits if it is small, of nb bits otherwise, less the number of small       *)
(* values if it is high.                                                     *)
(* ------------------------------------------------------------------------- *)

let nc_fieldp = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`, list_mk_conj
 [nc_state; nc_common;
  `(read PC s = word(pc + 0xa30) \/ read PC s = word(pc + 0xab8)) /\
   read X6 s = word(LENGTH(cs:int list)) /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        fse_counts T l (maxsv + 1) (pts,cs,8 * ofs + bc) r)`]));;

let NC_FIELD_SETUP_TAC =
  ABBREV_TAC `nb = bitsize(pts + 1)` THEN
  SUBGOAL_THEN `2 <= nb /\ nb <= 16 /\ pts + 1 < 2 EXP nb /\
                2 EXP (nb - 1) <= pts + 1 /\ 2 EXP nb = 2 * 2 EXP (nb - 1) /\
                2 EXP (nb - 1) <= 32768`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n <= 1)`; BITSIZE_LE] THEN
      SIMPLE_ARITH_TAC;
      REWRITE_TAC[BITSIZE_LE] THEN CONV_TAC(RAND_CONV NUM_REDUCE_CONV) THEN
      TRANS_TAC LET_TRANS `2 EXP alog + 1` THEN CONJ_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `a <= 32768 ==> a + 1 < 65536`) THEN
      TRANS_TAC LE_TRANS `2 EXP 15` THEN REWRITE_TAC[LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[BITSIZE];
      MATCH_MP_TAC BITSIZE_REV THEN ARITH_TAC;
      REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `2 <= n ==> n = SUC(n - 1)`) THEN
      REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n <= 1)`; BITSIZE_LE] THEN
      SIMPLE_ARITH_TAC;
      TRANS_TAC LE_TRANS `2 EXP 15` THEN REWRITE_TAC[LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC(ARITH_RULE `n <= 16 ==> n - 1 <= 15`) THEN
      REWRITE_TAC[BITSIZE_LE] THEN CONV_TAC(RAND_CONV NUM_REDUCE_CONV) THEN
      TRANS_TAC LET_TRANS `2 EXP alog + 1` THEN CONJ_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `a <= 32768 ==> a + 1 < 65536`) THEN
      TRANS_TAC LE_TRANS `2 EXP 15` THEN REWRITE_TAC[LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `w = zstd_bits l (8 * ofs + bc) (32 - bc)` THEN
  SUBGOAL_THEN
   `w MOD 2 EXP (nb - 1) = zstd_bits l (8 * ofs + bc) (nb - 1) /\
    w MOD 2 EXP nb = zstd_bits l (8 * ofs + bc) nb /\ w < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ZSTD_BITS_WINDOW_MOD THEN ASM_REWRITE_TAC[] THEN
      SIMPLE_ARITH_TAC;
      MATCH_MP_TAC ZSTD_BITS_WINDOW_MOD THEN ASM_REWRITE_TAC[] THEN
      SIMPLE_ARITH_TAC;
      TRANS_TAC LTE_TRANS `2 EXP (32 - bc)` THEN
      REWRITE_TAC[ZSTD_BITS_BOUND; LE_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`w:num`; `nb - 1`] NC_AND_MASK) THEN
  MP_TAC(SPECL [`w:num`; `nb:num`] NC_AND_MASK) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `thr = 2 EXP (nb - 1)` THEN
  NC_ASSUME_REWRITE_TAC [`2 EXP (nb - 1) = thr`] THEN
  NC_ASSUME_REWRITE_TAC [`2 EXP nb = 2 * thr`];;

let MOD_LE_MOD2 = prove
 (`!w t. ~(t = 0) ==> w MOD t <= w MOD (2 * t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w MOD t = (w MOD (t * 2)) MOD t` SUBST1_TAC THENL
   [REWRITE_TAC[MOD_MOD]; ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[MOD_LE]);;

let NC_FIELD_A54_TAC vtm bqtm =
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) NC_A54
    [vtm,`v:num`; bqtm,`bq:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FSE_FIELD_ALT] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT CONJ_TAC THEN FIRST[ARITH_TAC; SIMPLE_ARITH_TAC];;

let NC_FIELD = prove
 (mk_nc_goal [`alog:num`; `pts:num`; `cs:int list`; `ofs:num`; `bc:num`]
   nc_fieldp nc_a54_post,
  ZSTD_INTRO_TAC THEN GLOBALIZE_PRECONDITION_TAC THEN NC_FIELD_SETUP_TAC THEN
  MP_TAC(SPECL [`w:num`; `thr:num`] MOD_LE_MOD2) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  PUFF_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && free_in `PC` (concl th))) THEN
  (ASM_CASES_TAC `zstd_bits l (8 * ofs + bc) (nb - 1) < 2 * thr - (pts + 2)`
   THEN NC_STEPS_TAC (1--4) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `word_and (word (thr - 1)) (word w):int32 = word (w MOD thr)`]) THEN
   ZSTD_SMALL_WORD_TAC THEN NC_STEPS_TAC (5--7) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
    `2 * thr - 1 - (pts + 1) = 2 * thr - (pts + 2)`]) THENL
    [NC_STEPS_TAC (8--9) THEN
     NC_FIELD_A54_TAC `zstd_bits l (8 * ofs + bc) (nb - 1)` `(nb - 1) + bc`;
     NC_STEPS_TAC [8] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
      `word_and (word (2 * thr - 1)) (word w):int32 = word (w MOD (2 * thr))`])
     THEN ZSTD_SMALL_WORD_TAC THEN
     ASM_CASES_TAC `zstd_bits l (8 * ofs + bc) nb < thr` THENL
      [NC_STEPS_TAC (9--13) THEN
       NC_FIELD_A54_TAC `zstd_bits l (8 * ofs + bc) nb` `bc + nb`;
       MP_TAC(SPECL [`l:byte list`; `8 * ofs + bc`; `nb:num`]
         ZSTD_BITS_BOUND) THEN
       ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
       MP_TAC(SPEC `zstd_bits l (8 * ofs + bc) nb - thr` NC_IVAL_SMALL) THEN
       ANTS_TAC THENL
        [MATCH_MP_TAC(ARITH_RULE
          `x < 2 * t /\ t <= 32768 ==> x - t < 2 EXP 31`) THEN
         ASM_REWRITE_TAC[];
         DISCH_TAC] THEN
       NC_STEPS_TAC (9--13) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
        `ival(word(zstd_bits l (8 * ofs + bc) nb - thr):int32) =
         &(zstd_bits l (8 * ofs + bc) nb - thr)`;
        INT_OF_NUM_LT; ARITH_RULE `~(n < 0)`]) THEN
       NC_FIELD_A54_TAC
        `zstd_bits l (8 * ofs + bc) nb - (2 * thr - (pts + 2))` `bc + nb`]]));;

(* ------------------------------------------------------------------------- *)
(* The piece for the repeat flags, from 0xb04: groups of 12 flags 3 found as *)
(* at least 24 ones at the bottom of the window, and then the last ones, the *)
(* probabilities 0 being counted but not stored, as the buffer is already    *)
(* zero, and then the check of the number of counts.                         *)
(* ------------------------------------------------------------------------- *)

let nc_zerosp = with_memsafe nc_rr nc_wr (mk_abs(`s:armstate`, list_mk_conj
 [nc_state; nc_common;
  `read PC s = word(pc + 0xb04) /\
   read X6 s = word(LENGTH(cs:int list) + 1 + zz) /\
   zz + 36 * nc_inner (LENGTH l) ofs bc <= 36 * (4 * LENGTH l + 2) /\
   (!r. fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r <=>
        ?z q'. fse_zeros T l (0,zz,8 * ofs + bc) (z,q') /\
               fse_counts T l (maxsv + 1)
                 (pts,APPEND cs (REPLICATE (z + 1) (&0)),q') r)`]));;

let nc_zeros_post =
  let m = `m:num` and s = `s:armstate` in
  let app f xs = rhs(concl(DEPTH_CONV BETA_CONV (list_mk_comb(f,xs)))) in
  mk_abs(s,mk_disj
   (mk_exists(m,mk_conj
     (`m < ((maxsv + 2) - (LENGTH(cs:int list) + 1 + zz)) *
           (4 * LENGTH(l:byte list) + 4) + nc_inner (LENGTH l) ofs bc + 1`,
      app nc_inv [m; s])),
    app nc_post [s]));;

(*** Arithmetic from the relevant assumptions or from the given ones ***)

let NC_ARITH_TAC : tactic =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="] in
  let avoiders = ["read"; "write"; "val"; "word"] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n avoiders | _ -> false in
  let rec arith tm =
    is_num_relop tm || (is_neg tm && arith(dest_neg tm)) ||
    ((is_disj tm || is_conj tm) && arith(lhand tm) && arith(rand tm)) in
  let filtered tm = arith tm && not(can (find_term avoiderp) tm) in
  W(fun (asl,w) ->
    let gvs = frees w in
    let asl' = filter (fun (_,th) -> let c = concl th in
                         filtered c && subset (frees c) gvs) asl in
    MAP_EVERY (MP_TAC o snd) asl' THEN CONV_TAC ARITH_RULE);;

let NC_ARITH_FROM_TAC tms =
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm)) tms THEN ARITH_TAC;;

let NC_PC_NE_FAST_TAC a b =
  let th = SPECL [`pc:num`; mk_small_numeral a; mk_small_numeral b]
                 WORD_PC_NE in
  MP_TAC th THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `pc + 131096 <= 2 EXP 64` THEN ARITH_TAC;
    DISCH_TAC];;

(*** The window w and the number t of ones at its bottom ***)

let NC_ZEROS_SETUP_TAC =
  ABBREV_TAC `w = zstd_bits l (8 * ofs + bc) (32 - bc)` THEN
  SUBGOAL_THEN `w < 2 EXP (32 - bc)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[ZSTD_BITS_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `w < 2 EXP 32` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (32 - bc)` THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (word w:int64):int32 = word w` ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `w < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = word_ctz(word_or (word_not (word w:int32))
                                  (word 2147483648))` THEN
  MP_TAC(SPECL [`word w:int32`; `t:num`] WORD_CTZ_NOT_OR31) THEN
  ASM_REWRITE_TAC[BIT_VAL] THEN
  SUBGOAL_THEN `val(word w:int32) = w` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `t <= 32 - bc` ASSUME_TAC THENL
   [MATCH_MP_TAC NC_ONES_BOUND THEN EXISTS_TAC `w:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (word t:int32):int64 = word t` ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `t <= 31` THEN ARITH_TAC;
    ALL_TAC];;

(*** The steps to the rbit and clz, giving t ***)

let NC_ZEROS_CTZ_TAC =
  NC_STEPS_TAC (1--4) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_zx (word w:int64):int32 = word w`;
                              WORD_CLZ_REVERSEFIELDS]) THEN
  NC_ASSUME_REWRITE_TAC
   [`word_ctz (word_or (word_not (word w:int32)) (word 2147483648)) = t`] THEN
  NC_ASSUME_REWRITE_TAC [`word_zx (word t:int32):int64 = word t`];;

(*** At least 12 repeat flags 3 ***)

let NC_ZEROS_12_TAC =
  SUBGOAL_THEN `bc <= 8` ASSUME_TAC THENL
   [UNDISCH_TAC `t <= 32 - bc` THEN UNDISCH_TAC `24 <= t` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `zstd_bits l (8 * ofs + bc) 24 = 2 EXP 24 - 1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; `ofs:num`; `bc:num`; `24`]
      ZSTD_BITS_WINDOW_MOD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NC_ONES_MONO THEN EXISTS_TAC `t:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `zz:num`; `8 * ofs + bc`] FSE_ZEROS_12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(*** Back at b04 after 12 repeat flags 3 ***)

let NC_ZEROS_LOOP_FIN_TAC ofs' bc' =
  W(fun (asl,w) ->
    let s = rand w in
    NC_SET_REG_TAC
     (subst [s,`s:armstate`]
       `read X6 s = word(LENGTH(cs:int list) + 1 + zz + 36)`)
     (ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC)) THEN
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC (subst [ofs',`ofs':num`; bc',`bc':num`]
   `((maxsv + 2) - (LENGTH(cs:int list) + 1 + zz + 36)) *
    (4 * LENGTH(l:byte list) + 4) + nc_inner (LENGTH l) ofs' bc' + 1`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `a <= b /\ x < y ==> a + x + 1 < b + y + 1`) THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`pts:num`; `cs:int list`; ofs'; bc'; `zz + 36`] THEN
  NC_PC_NE_FAST_TAC 2820 2608 THEN NC_PC_NE_FAST_TAC 2820 2744 THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NC_ARITH_TAC;;

let NC_ZEROS_NOWRAP_TAC =
  NC_STEPS_TAC (8--11) THEN
  NC_LOAD_FACT_TAC `ofs + 3` `s11:armstate` THEN
  NC_STEPS_TAC [12; 13] THEN NC_X4_TAC THEN NC_X5_NORM_TAC THEN
  SUBGOAL_THEN `fse_reload T l ((8 * ofs + bc) + 24) = 8 * (ofs + 3) + bc`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; `(8 * ofs + bc) + 24`] FSE_RELOAD_NOWRAP) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ofs <= LENGTH(l:byte list) - 7` THEN
      UNDISCH_TAC `bc <= 8` THEN UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN
      ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`LENGTH(l:byte list)`; `ofs:num`; `bc:num`]
    NC_INNER_NOWRAP) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ofs <= LENGTH(l:byte list) - 7` THEN
    UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN ARITH_TAC;
    DISCH_TAC] THEN
  NC_ZEROS_LOOP_FIN_TAC `ofs + 3` `bc:num`;;

let NC_ZEROS_WRAP_TAC =
  NC_STEPS_TAC (8--14) THEN
  MP_TAC(SPECL [`hb:int64`; `LENGTH(l:byte list)`; `ofs:num`; `bc:num`]
    NC_WRAP_BC7) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~(ofs <= LENGTH(l:byte list) - 7)` THEN
    UNDISCH_TAC `ofs + 4 <= LENGTH(l:byte list)` THEN
    UNDISCH_TAC `bc <= 8` THEN UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN
    ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(SPECL [`(bc + 24) - 8 * (LENGTH(l:byte list) - 4 - ofs)`; `32`]
    MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
  NC_STEPS_TAC [15] THEN
  NC_LOAD_FACT_TAC `LENGTH(l:byte list) - 4` `s15:armstate` THEN
  NC_STEPS_TAC [16; 17] THEN NC_X4_TAC THEN
  SUBGOAL_THEN
   `fse_reload T l ((8 * ofs + bc) + 24) =
    8 * (LENGTH l - 4) + ((bc + 24) - 8 * (LENGTH l - 4 - ofs)) MOD 32`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; `(8 * ofs + bc) + 24`] FSE_RELOAD_WRAP) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(ofs <= LENGTH(l:byte list) - 7)` THEN
      UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(ofs <= LENGTH(l:byte list) - 7)` THEN
    UNDISCH_TAC `ofs + 4 <= LENGTH(l:byte list)` THEN
    UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`LENGTH(l:byte list)`; `ofs:num`; `bc:num`] NC_INNER_WRAP) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~(ofs <= LENGTH(l:byte list) - 7)` THEN
    UNDISCH_TAC `ofs + 4 <= LENGTH(l:byte list)` THEN
    UNDISCH_TAC `bc <= 8` THEN UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  NC_ZEROS_LOOP_FIN_TAC `LENGTH(l:byte list) - 4`
   `((bc + 24) - 8 * (LENGTH(l:byte list) - 4 - ofs)) MOD 32`;;

(*** The postcondition of the reload piece gives that of the zeros piece ***)

let NC_ZEROS_WTAC =
  GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a <= b ==> m < a + 1 ==> m < b + c + 1`) THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ARITH_TAC;
      DISCH_THEN ACCEPT_TAC];
    DISCH_THEN ACCEPT_TAC];;

(*** Fewer than 12 repeat flags 3, then one less than 3 ***)

let NC_ZEROS_LAST_TAC =
  SUBGOAL_THEN `t <= 23` ASSUME_TAC THENL
   [UNDISCH_TAC `~(24 <= t)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * (t DIV 2) <= t /\ t DIV 2 <= 11` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`t:num`; `2`] DIVISION) THEN ARITH_TAC;
      SUBGOAL_THEN `11 = 23 DIV 2` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV;
        MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `ofs:num`; `bc:num`; `t:num`]
    NC_ZEROS_LAST_BITS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `t <= 23` THEN ARITH_TAC;
    STRIP_TAC] THEN
  NC_STEPS_TAC (7--16) THEN
  MP_TAC(SPECL [`w:num`; `2 * (t DIV 2)`] NC_JUSHR_AND3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    NC_ARITH_FROM_TAC [`2 * (t DIV 2) <= t`; `t <= 23`];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       rand(concl th) = `(w DIV 2 EXP (2 * (t DIV 2))) MOD 4`
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN ASSUME_TAC(SYM th)
    else NO_TAC) THEN
  NC_SET_REG_TAC
   `read X6 s16 =
    word(LENGTH(cs:int list) +
         (zz + 3 * (t DIV 2) + zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2) +
         1)`
   (ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM WORD_ADD] THEN
    SUBGOAL_THEN
     `zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2 +
      (2 * (t DIV 2) + t DIV 2) + LENGTH(cs:int list) + 1 + zz =
      LENGTH cs +
      (zz + 3 * (t DIV 2) + zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2) + 1`
    SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPECL [`LENGTH(l:byte list)`; `ofs:num`; `bc:num`]
      NC_INNER_BOUND) THEN
    NC_ARITH_FROM_TAC
     [`LENGTH(cs:int list) < maxsv + 1`; `maxsv <= 255`;
      `zz + 36 * nc_inner (LENGTH(l:byte list)) ofs bc <=
       36 * (4 * LENGTH l + 2)`;
      `LENGTH(l:byte list) < 2 EXP 24`; `t DIV 2 <= 11`;
      `zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2 < 3`]) THEN
  NC_SET_REG_TAC `read X4 s16 = word(bc + 2 * (t DIV 2) + 2)`
   (ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC) THEN
  ASM_CASES_TAC
   `LENGTH(cs:int list) +
    (zz + 3 * (t DIV 2) + zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2) + 1 <
    maxsv + 1` THEN
  NC_STEPS_TAC [17; 18] THENL
   [ZSTD_CONTINUE_WITH_TAC NC_ZEROS_WTAC NC_B4C
     [`zz + 3 * (t DIV 2) + zstd_bits l (8 * ofs + bc + 2 * (t DIV 2)) 2`,
      `z:num`; `bc + 2 * (t DIV 2) + 2`,`bq:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [NC_ARITH_FROM_TAC [`bc <= 31`; `t DIV 2 <= 11`];
      NC_ARITH_FROM_TAC [`bc <= 7 \/ ofs + 4 = LENGTH(l:byte list)`;
                         `t DIV 2 <= 11`];
      MATCH_MP_TAC FSE_ZEROS_LAST_COUNTS THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `!r. ~fse_counts T l (maxsv + 1) (2 EXP alog,[],4) r`
    ASSUME_TAC THENL
     [GEN_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                               free_in `fse_zeros` (concl th)
                            then REWRITE_TAC[th] else NO_TAC) THEN
      MP_TAC(SPECL [`l:byte list`; `maxsv + 1`; `pts:num`; `cs:int list`;
                    `zz:num`; `ofs:num`; `bc:num`; `t DIV 2`]
        FSE_ZEROS_LAST_COUNTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC FSE_COUNTS_FULL THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN NC_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `pts <= 32768` ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS `2 EXP alog` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP 15` THEN REWRITE_TAC[LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word_zx (word (pts + 1):int64):int32) = 1)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `word_zx (word (pts + 1):int64):int32 = word(pts + 1)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
        REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `pts <= 32768` THEN
        ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
        SUBGOAL_THEN `(pts + 1) MOD 2 EXP 32 = pts + 1` SUBST1_TAC THENL
         [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
          UNDISCH_TAC `pts <= 32768` THEN ARITH_TAC;
          UNDISCH_TAC `1 <= pts` THEN ARITH_TAC]];
      ALL_TAC] THEN
    NC_STEPS_TAC (19--21) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
     `~(val(word_zx (word (pts + 1):int64):int32) = 1)`]) THEN
    NC_STEPS_TAC (22--26) THEN
    PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `maxsv + 1`; `alog:num`] FSE_NCOUNT_FAIL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; zstd_is_error] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_RULE];;

let NC_ZEROS = prove
 (mk_nc_goal [`alog:num`; `pts:num`; `cs:int list`; `ofs:num`; `bc:num`;
              `zz:num`] nc_zerosp nc_zeros_post,
  ZSTD_INTRO_TAC THEN GLOBALIZE_PRECONDITION_TAC THEN NC_ZEROS_SETUP_TAC THEN
  PUFF_INIT_TAC "s0" THEN NC_ZEROS_CTZ_TAC THEN NC_STEPS_TAC (5--6) THEN
  ASM_CASES_TAC `24 <= t` THENL
   [NC_STEPS_TAC [7] THEN NC_ZEROS_12_TAC THEN
    ASM_CASES_TAC `ofs <= LENGTH(l:byte list) - 7` THENL
     [NC_ZEROS_NOWRAP_TAC; NC_ZEROS_WRAP_TAC];
    NC_ZEROS_LAST_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop over the fields and the runs of repeat flags, with the measure   *)
(* and the invariant above, from the start at 0xa30 with all the points left *)
(* and no counts.                                                            *)
(* ------------------------------------------------------------------------- *)

let BITSIZE_POW2_SUC = prove
 (`!k. 1 <= k ==> bitsize(2 EXP k + 1) = k + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM; BITSIZE_LE] THEN
  REWRITE_TAC[ARITH_RULE `k + 1 <= n <=> ~(n <= k)`; BITSIZE_LE] THEN
  SUBGOAL_THEN `2 <= 2 EXP k` MP_TAC THENL
   [TRANS_TAC LE_TRANS `2 EXP 1` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ]];
    REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC]);;

let NC_LOOP = prove
 (mk_nc_goal [`alog:num`] nc_loopp nc_post,
  ZSTD_INTRO_TAC THEN
  MATCH_MP_TAC(ISPEC nc_inv ENSURES_WHILE_MEASURE) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    SUBSUMED_ID_MAYCHANGE_TAC;
    MATCH_MP_TAC ENSURES_ALREADY THEN CONJ_TAC THENL
     [ALL_TAC; SUBSUMED_ID_MAYCHANGE_TAC] THEN
    X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `((maxsv + 2) - LENGTH([]:int list)) *
                (4 * LENGTH(l:byte list) + 4)` THEN
    MAP_EVERY EXISTS_TAC [`2 EXP alog`; `[]:int list`; `0`; `4`; `0`] THEN
    SUBGOAL_THEN `bitsize(2 EXP alog + 1) = alog + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC BITSIZE_POW2_SUC THEN
      UNDISCH_TAC `zstd_bits l 0 4 + 5 = alog` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_SUB; LENGTH; FSE_NCLIST_NIL; WORD_ADD_0;
                    MULT_CLAUSES; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[ensures] THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THEN
  ASSUME_TAC(ISPEC `s:armstate` MAYCHANGE_STARTER) THEN
  DISCH_THEN(X_CHOOSE_THEN `pts:num` (X_CHOOSE_THEN `cs:int list`
   (X_CHOOSE_THEN `ofs:num` (X_CHOOSE_THEN `bc:num`
   (X_CHOOSE_THEN `zz:num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) && free_in `fse_counts` (concl th)))
  THENL
   [ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) NC_FIELD [] THEN
    ASM_REWRITE_TAC[];
    ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) NC_ZEROS [] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* From the entry, for an input of at least 8 bytes: the saving of           *)
(* registers, the memset of the buffer of counts and the Accuracy_Log, and   *)
(* on with the loop.                                                         *)
(* ------------------------------------------------------------------------- *)

(*** The Accuracy_Log field ***)

let NC_HEADER_AND = prove
 (`!l. word_zx (word_and (word (num_of_bytelist l MOD 4294967296)) (word 15)
                :int32):int64 =
       word(zstd_bits l 0 4) /\
       word_and (word (num_of_bytelist l MOD 4294967296)) (word 15):int32 =
       word(zstd_bits l 0 4)`,
  SUBGOAL_THEN
   `!l. word_and (word (num_of_bytelist l MOD 4294967296)) (word 15):int32 =
        word(zstd_bits l 0 4)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
    MP_TAC(SPECL [`num_of_bytelist l MOD 4294967296`; `4`] NC_AND_MASK) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ZSTD_BITS_NUM; EXP; DIV_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `4294967296 = 16 * 268435456`; MOD_MOD];
    GEN_TAC THEN MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
    MP_TAC(SPECL [`l:byte list`; `0`; `4`] ZSTD_BITS_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let NC_ENTRY = prove
 (mk_nc_goal [] nc_entry nc_post,
  ZSTD_INTRO_TAC THEN REWRITE_TAC[C_ARGUMENTS] THEN PUFF_INIT_TAC "s0" THEN
  ZSTD_STEPS_TAC (1--18) THEN
  ZSTD_STEPS_TAC [19] THEN PUFF_ADRP_TAC THEN ZSTD_STEPS_TAC (20--22) THEN
  SUBGOAL_THEN `val(word(2 * (maxsv + 1)):int64) = 2 * (maxsv + 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `maxsv <= 255` THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_MEMSET_TAC
   [ASSUME `val(word(2 * (maxsv + 1)):int64) = 2 * (maxsv + 1)`]
   `nc:int64` `word 0:int64` `word(2 * (maxsv + 1)):int64`
   `word(pc + 2528):int64` 23 THEN
  MP_TAC(SPECL [`hb:int64`; `LENGTH(l:byte list)`; `num_of_bytelist l`;
                `0`; `s23:armstate`] READ_MEMORY_BYTES32_SLICE) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; EXP; DIV_1] THEN
  ANTS_TAC THENL [UNDISCH_TAC `8 <= LENGTH(l:byte list)` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  ZSTD_STEPS_TAC (24--26) THEN RULE_ASSUM_TAC(REWRITE_RULE[NC_HEADER_AND]) THEN
  MP_TAC(SPECL [`l:byte list`; `0`; `4`] ZSTD_BITS_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ZSTD_STEPS_TAC (27--28) THEN
  ASM_CASES_TAC `zstd_bits l 0 4 + 5 <= 15` THENL
   [ZSTD_STEPS_TAC (29--43) THEN
    SUBGOAL_THEN `2 EXP (zstd_bits l 0 4 + 5) <= 32768` ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS `2 EXP 15` THEN REWRITE_TAC[LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_zx (word (2 EXP (zstd_bits l 0 4 + 5) + 1):int32):int64 =
      word (2 EXP (zstd_bits l 0 4 + 5) + 1) /\
      word_zx (word (2 EXP (zstd_bits l 0 4 + 5)):int32):int64 =
      word (2 EXP (zstd_bits l 0 4 + 5)) /\
      word (zstd_bits l 0 4 + 6):int64 = word((zstd_bits l 0 4 + 5) + 1) /\
      (num_of_bytelist l MOD 4294967296) DIV 16 = zstd_bits l 4 28`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
        REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
        UNDISCH_TAC `2 EXP (zstd_bits l 0 4 + 5) <= 32768` THEN ARITH_TAC;
        MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
        REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
        UNDISCH_TAC `2 EXP (zstd_bits l 0 4 + 5) <= 32768` THEN ARITH_TAC;
        AP_TERM_TAC THEN ARITH_TAC;
        MP_TAC(SPECL [`l:byte list`; `0`; `4`] ZSTD_BITS_WINDOW) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`nc:int64`; `2 * (maxsv + 1)`; `s43:armstate`]
      READ_MEMORY_BYTES_ZERO) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[WORD_ZX_0]; DISCH_TAC] THEN
    ZSTD_CONTINUE_TAC NC_LOOP [`zstd_bits l 0 4 + 5`,`alog:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[];
    ZSTD_STEPS_TAC (29--34) THEN PUFF_FINAL_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `maxsv + 1`] FSE_NCOUNT_ALOG) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(zstd_bits l 0 4 + 5 <= 15)` THEN ARITH_TAC;
      DISCH_TAC] THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; zstd_is_error] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_RULE]);;

(* ------------------------------------------------------------------------- *)
(* The same as a subroutine, in the usual form.                              *)
(* ------------------------------------------------------------------------- *)

let nc_std_rr =
 `[hb,LENGTH(l:byte list); maxsvp,4; nc,2 * (maxsv + 1);
   word_sub stackpointer (word 80),80; word(pc + 0x20010),8;
   ea,el]:(int64#num)list`;;

let nc_std_pre = `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x940) /\ read SP s = stackpointer /\
  read X30 s = returnaddress /\
  C_ARGUMENTS [nc; maxsvp; tlp; hb; word(LENGTH l)] s /\
  read (memory :> bytes32 maxsvp) s = word maxsv /\
  read (memory :> bytes(hb,LENGTH l)) s = num_of_bytelist l /\
  read (memory :> bytes64(word(pc + 0x20010))) s = fset /\
  read (memory :> bytes(ea,el)) s = ev /\
  read events s = e`;;

let nc_std_post rr wr = mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = returnaddress /\
   (!cs alog m.
      fse_ncount T 15 (maxsv + 1) l (cs,alog,m)
      ==> read X0 s = word m /\
          read (memory :> bytes(nc,2 * (maxsv + 1))) s =
          num_of_wordlist(fse_nclist cs (maxsv + 1)) /\
          read (memory :> bytes32 maxsvp) s = word(LENGTH cs - 1) /\
          read (memory :> bytes32 tlp) s = word alog) /\
   ((!r. ~fse_ncount T 15 (maxsv + 1) l r) ==> zstd_is_error(read X0 s))`;
  mk_exists(`e2:uarch_event list`,mk_conj(
   `read events s = APPEND e2 e`,
   list_mk_icomb "memaccess_inbounds" [`e2:uarch_event list`; rr; wr]))]);;

let NC_MAIN = prove
 (list_mk_forall
   (filter (fun v -> not(mem (fst(dest_var v))
                ["x19";"x20";"x21";"x22";"x23";"x24";"x29"])) nc_vars,
    mk_imp(nc_hyps,
     list_mk_icomb "ensures" [`arm`; nc_std_pre;
       nc_std_post nc_std_rr nc_wr;
       `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(nc,2 * (maxsv + 1));
                   memory :> bytes(maxsvp,4); memory :> bytes(tlp,4);
                   memory :> bytes(word_sub stackpointer (word 80),80)]`])),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS] THEN
  ENSURES_PRESERVED_TAC "x19" `X19` THEN
  ENSURES_PRESERVED_TAC "x20" `X20` THEN
  ENSURES_PRESERVED_TAC "x21" `X21` THEN
  ENSURES_PRESERVED_TAC "x22" `X22` THEN
  ENSURES_PRESERVED_TAC "x23" `X23` THEN
  ENSURES_PRESERVED_TAC "x24" `X24` THEN
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC nc_frame THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
                MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
                SOME_FLAGS] THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
  MAP_EVERY EXISTS_TAC [nc_entry; nc_post] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM(SPECL [`pc:num`; `0x20010`] WORD_ADD)] THEN
    REWRITE_TAC[puff_memsafe] THEN EXISTS_TAC `[]:uarch_event list` THEN
    ASM_REWRITE_TAC[APPEND; MEMACCESS_INBOUNDS_NIL];
    X_GEN_TAC `s:armstate` THEN BETA_TAC THEN REWRITE_TAC[puff_memsafe] THEN
    REWRITE_TAC[GSYM(SPECL [`pc:num`; `0x20010`] WORD_ADD)] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `e2:uarch_event list` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NC_ENTRY THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Inputs of fewer than 8 bytes. The code copies them with memcpy into a     *)
(* buffer of 8 bytes on the stack, zeroed first, calls itself on it and      *)
(* returns its result if it is an error or at most hbSize, and an error      *)
(* otherwise. The final theorem has the hypotheses, precondition, regions    *)
(* and frame of this case, with the stack frame of the inner call too. The   *)
(* stack pointer must not be 0: the buffer would then be at the very top of  *)
(* the address space, and the comparisons of the pointers into it by the     *)
(* code would wrap around.                                                   *)
(* ------------------------------------------------------------------------- *)

let nc_fin_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 0) /\
  memcpy_memsafe_contract fcpy ea el ev /\
  memset_memsafe_contract fset ea el ev /\
  LENGTH(l:byte list) < 2 EXP 24 /\ val(hb:int64) + LENGTH l + 8 < 2 EXP 64 /\
  maxsv <= 255 /\
  nonoverlapping (nc:int64,2 * (maxsv + 1)) (word pc,0x20018) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (hb,LENGTH l) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (ea:int64,el) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (maxsvp:int64,4) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (tlp:int64,4) /\
  nonoverlapping (nc,2 * (maxsv + 1)) (word_sub stackpointer (word 160),160) /\
  nonoverlapping (maxsvp,4) (word pc,0x20018) /\
  nonoverlapping (maxsvp,4) (hb,LENGTH l) /\
  nonoverlapping (maxsvp,4) (ea,el) /\
  nonoverlapping (maxsvp,4) (tlp,4) /\
  nonoverlapping (maxsvp,4) (word_sub stackpointer (word 160),160) /\
  nonoverlapping (tlp,4) (word pc,0x20018) /\
  nonoverlapping (tlp,4) (hb,LENGTH l) /\
  nonoverlapping (tlp,4) (ea,el) /\
  nonoverlapping (tlp,4) (word_sub stackpointer (word 160),160) /\
  nonoverlapping (word_sub stackpointer (word 160),160) (word pc,0x20018) /\
  nonoverlapping (word_sub stackpointer (word 160),160) (hb,LENGTH l) /\
  nonoverlapping (word_sub stackpointer (word 160),160) (ea,el)`;;

let nc_fin_pre = `\s.
  aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x940) /\ read SP s = stackpointer /\
  read X30 s = returnaddress /\
  C_ARGUMENTS [nc; maxsvp; tlp; hb; word(LENGTH l)] s /\
  read (memory :> bytes32 maxsvp) s = word maxsv /\
  read (memory :> bytes(hb,LENGTH l)) s = num_of_bytelist l /\
  read (memory :> bytes64(word(pc + 0x20000))) s = fcpy /\
  read (memory :> bytes64(word(pc + 0x20010))) s = fset /\
  read (memory :> bytes(ea,el)) s = ev /\
  read events s = e`;;

let nc_fin_rr =
 `[hb,LENGTH(l:byte list); maxsvp,4; nc,2 * (maxsv + 1);
   word_sub stackpointer (word 160),160; word(pc + 0x20000),8;
   word(pc + 0x20010),8; ea,el]:(int64#num)list`
and nc_fin_wr =
 `[nc,2 * (maxsv + 1); maxsvp,4; tlp,4;
   word_sub stackpointer (word 160),160]:(int64#num)list`;;

let nc_fin_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [memory :> bytes(nc,2 * (maxsv + 1)); memory :> bytes(maxsvp,4);
             memory :> bytes(tlp,4);
             memory :> bytes(word_sub stackpointer (word 160),160)]`;;

let nc_fin_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `nc:int64`;
  `maxsvp:int64`; `tlp:int64`; `hb:int64`; `l:byte list`; `maxsv:num`;
  `fcpy:int64`; `fset:int64`; `ea:int64`; `el:num`; `ev:num`;
  `e:uarch_event list`];;

let mk_nc_fin_goal extra =
  list_mk_forall(nc_fin_vars,
   mk_imp(list_mk_conj(nc_fin_hyps::extra),
    list_mk_icomb "ensures"
     [`arm`; nc_fin_pre; nc_std_post nc_fin_rr nc_fin_wr; nc_fin_frame]));;

(*** The stack pointer, aligned and nonzero, is not near either end ***)

let NC_STACK_BOUNDS = prove
 (`!sp:int64. aligned 16 sp /\ ~(sp = word 0)
              ==> 8 <= val sp /\ val sp + 8 < 2 EXP 64`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64; GSYM VAL_EQ_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT2) ASSUME_TAC) THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  MP_TAC(ISPEC `sp:int64` VAL_BOUND_64) THEN
  UNDISCH_TAC `~(val(sp:int64) = 0)` THEN ASM_REWRITE_TAC[MULT_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THENL
   [ASM_ARITH_TAC;
    SUBGOAL_THEN `k < 1152921504606846976` MP_TAC THENL
     [ASM_ARITH_TAC; ARITH_TAC]]);;

(*** The 8-byte buffer of the short path, zeroed and then partly copied ***)

let NC_BUF_SPLIT = prove
 (`!(a:int64) k s.
        k <= 8 /\ read (memory :> bytes64 a) s = word 0
        ==> read (memory :> bytes(word_add a (word k),8 - k)) s = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,k + (8 - k))) s = 0` MP_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `k <= 8 ==> k + (8 - k) = 8`;
                 READ_MEMORY_BYTES_8; VAL_WORD_0];
    ONCE_REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0;
                ARITH_EQ] THEN
    SIMP_TAC[]]);;

let NC_BUF_COMBINE = prove
 (`!(a:int64) k x s.
        k <= 8 /\ read (memory :> bytes(a,k)) s = x /\
        read (memory :> bytes(word_add a (word k),8 - k)) s = 0
        ==> read (memory :> bytes(a,8)) s = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `8 = k + (8 - k)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

(*** The self-call on the 8-byte buffer, at step n ***)

let NC_SELF_CALL_TAC ths vars n =
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL vars NC_MAIN))) THEN
  REWRITE_TAC ths THEN REWRITE_TAC[WORD_SUB_SUB_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  REWRITE_TAC ths THEN REWRITE_TAC[WORD_SUB_SUB_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ARM_BIGSTEP_TAC ZSTD_EXEC ("s"^string_of_int n) THEN EVENTS_UNABBREV_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC);;

(*** The result after the self-call: the count, an error, or -20 ***)

let NC_SELECT = prove
 (`!len (x:int64).
        (if (if len < val x
             then &(val x) - &18446744073709551496:int =
                  &(val (word_sub x (word 18446744073709551496)))
             else T) /\
            ~(if len < val x then val x = 18446744073709551496 else F)
         then x else word 18446744073709551596) =
        (if val x <= len \/ 18446744073709551496 < val x then x
         else word 18446744073709551596)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(&(val(x:int64)) - &18446744073709551496:int =
     &(val (word_sub x (word 18446744073709551496)))) <=>
    18446744073709551496 <= val x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`x:int64`; `word 18446744073709551496:int64`]
      VAL_WORD_SUB_CASES) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[INT_OF_NUM_SUB];
      REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `len < val(x:int64)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[ARITH_RULE `len < v ==> ~(v <= len)`] THEN
    REWRITE_TAC[ARITH_RULE `k <= v /\ ~(v = k) <=> k < v`];
    ASM_SIMP_TAC[ARITH_RULE `~(len < v) ==> v <= len`]]);;

let FSE_NCOUNT_PAD = prove
 (`!n l cs alog m.
        LENGTH l < 8
        ==> (fse_ncount T 15 n l (cs,alog,m) <=>
             fse_ncount T 15 n (APPEND l (REPLICATE (8 - LENGTH l) (word 0)))
                        (cs,alog,m) /\
             m <= LENGTH l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FSE_NCOUNT_SHORT THEN
  ASM_REWRITE_TAC[ZSTD_BITS_PAD; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  ASM_ARITH_TAC);;

(*** The short path, for fewer than 8 bytes ***)

let NC_SHORT = prove
 (mk_nc_fin_goal [`LENGTH(l:byte list) < 8`],
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(MATCH_MP NC_STACK_BOUNDS
   (CONJ (ASSUME `aligned 16 (stackpointer:int64)`)
         (ASSUME `~(stackpointer:int64 = word 0)`))) THEN
  STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS] THEN
  ENSURES_PRESERVED_TAC "x19" `X19` THEN
  ENSURES_PRESERVED_TAC "x20" `X20` THEN
  ENSURES_PRESERVED_TAC "x21" `X21` THEN
  ENSURES_PRESERVED_TAC "x22" `X22` THEN
  ENSURES_PRESERVED_TAC "x23" `X23` THEN
  ENSURES_PRESERVED_TAC "x24" `X24` THEN
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `131072`] WORD_ADD]) THEN
  ZSTD_STEPS_TAC (1--18) THEN
  MP_TAC(ISPECL [`word_add (word_sub stackpointer (word 80)) (word 72):int64`;
                 `LENGTH(l:byte list)`; `s18:armstate`] NC_BUF_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `LENGTH(l:byte list) < 8` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  ZSTD_STEPS_TAC (19--20) THEN PUFF_ADRP_TAC THEN ZSTD_STEPS_TAC (21--23) THEN
  SUBGOAL_THEN `val(word(LENGTH(l:byte list)):int64) = LENGTH l`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `LENGTH(l:byte list) < 8` THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_MEMCPY_TAC
   [ASSUME `val(word(LENGTH(l:byte list)):int64) = LENGTH l`]
   `word_add (word_sub stackpointer (word 80)) (word 72):int64` `hb:int64`
   `word(LENGTH(l:byte list)):int64` `word(pc + 2444):int64`
   `num_of_bytelist l` 24 THEN
  ZSTD_STEPS_TAC (25--30) THEN
  MP_TAC(ISPECL [`word_add (word_sub stackpointer (word 80)) (word 72):int64`;
                 `LENGTH(l:byte list)`; `num_of_bytelist l`; `s30:armstate`]
    NC_BUF_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `LENGTH(l:byte list) < 8` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND l (REPLICATE (8 - LENGTH l) (word 0:byte))) = 8`
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN
    UNDISCH_TAC `LENGTH(l:byte list) < 8` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_add (word_sub stackpointer (word 80)) (word 72):int64) + 16 <
    18446744073709551616`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_add (word_sub x (word 80)) (word 72):int64 =
                           word_sub x (word 8)`] THEN
    MP_TAC(ISPECL [`stackpointer:int64`; `word 8:int64`]
      VAL_WORD_SUB_CASES) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `val(stackpointer:int64) + 8 < 2 EXP 64` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  NC_SELF_CALL_TAC
   [ASSUME `LENGTH(APPEND l (REPLICATE (8 - LENGTH l) (word 0:byte))) = 8`;
    NUM_OF_BYTELIST_PAD]
   [`pc:num`; `word(pc + 2468):int64`; `word_sub stackpointer (word 80):int64`;
    `nc:int64`; `maxsvp:int64`; `tlp:int64`;
    `word_add (word_sub stackpointer (word 80)) (word 72):int64`;
    `APPEND l (REPLICATE (8 - LENGTH l) (word 0:byte))`; `maxsv:num`;
    `fset:int64`; `ea:int64`; `el:num`; `ev:num`] 31 THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s31 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s31 = x0r`] THEN
  ZSTD_STEPS_TAC (32--36) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NC_SELECT]) THEN ZSTD_STEPS_TAC (37--41) THEN
  PUFF_FINAL_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub stackpointer (word 80):int64 =
      word_add (word_sub stackpointer (word 160)) (word 80)`;
      WORD_ADD_ASSOC_NUM]) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
    MONOTONE_MAYCHANGE_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_sub x (word 80)) (word 80):int64 = x`]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`maxsv + 1`; `l:byte list`; `cs:int list`; `alog:num`;
                  `m:num`] FSE_NCOUNT_PAD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`cs:int list`; `alog:num`; `m:num`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `x0r:int64` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`T`; `15`; `maxsv + 1`;
                  `APPEND l (REPLICATE (8 - LENGTH l) (word 0:byte))`;
                  `cs:int list`; `alog:num`; `m:num`] FSE_NCOUNT_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `val(word m:int64) = m` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `m <= 8` THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN
    ASM_CASES_TAC
     `?cs alog m.
        fse_ncount T 15 (maxsv + 1)
          (APPEND l (REPLICATE (8 - LENGTH l) (word 0:byte))) (cs,alog,m)`
    THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `cs:int list` (X_CHOOSE_THEN `alog:num`
        (X_CHOOSE_TAC `m:num`))) THEN
      MP_TAC(SPECL [`T`; `15`; `maxsv + 1`;
                    `APPEND l (REPLICATE (8 - LENGTH l) (word 0:byte))`;
                    `cs:int list`; `alog:num`; `m:num`] FSE_NCOUNT_LENGTH) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`cs:int list`; `alog:num`; `m:num`] o
        check (fun th -> is_forall(concl th) &&
                         free_in `x0r:int64` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(m <= LENGTH(l:byte list))` ASSUME_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC `!r. ~fse_ncount T 15 (maxsv + 1) l r` THEN
        DISCH_THEN(MP_TAC o SPEC `(cs:int list,alog:num,m:num)`) THEN
        ASM_SIMP_TAC[FSE_NCOUNT_PAD];
        ALL_TAC] THEN
      SUBGOAL_THEN `val(word m:int64) = m /\ ~(18446744073709551496 < m)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT;
          ALL_TAC] THEN
        UNDISCH_TAC `m <= 8` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
                                     free_in `x0r:int64` (concl th))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[zstd_is_error] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For an input l of LENGTH l bytes at hb, and maxsv at    *)
(* maxsvp, the result is the size of the description at the start of l in    *)
(* bytes, with the counts at nc, their number less 1 at maxsvp and the       *)
(* Accuracy_Log at tlp, if l has a description (in the zstd dialect, with at *)
(* most maxsv + 1 counts and an Accuracy_Log of at most 15), and an error    *)
(* code otherwise. The accesses, including those of memcpy and memset, are   *)
(* loads from the input, maxsvp, the counts, the stack, the pointers to      *)
(* memcpy and memset and their region (ea,el), and stores to the counts,     *)
(* maxsvp, tlp and the stack.                                                *)
(* ------------------------------------------------------------------------- *)

let NC_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 80):int64 =
  word_add (word_sub stackpointer (word 160)) (word 80)`;;

let FSE_READ_NCOUNT_CORRECT = prove
 (mk_nc_fin_goal [],
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `LENGTH(l:byte list) < 8` THENL
   [MP_TAC(SPECL nc_fin_vars NC_SHORT) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(SPECL [`pc:num`; `returnaddress:int64`; `stackpointer:int64`;
                `nc:int64`; `maxsvp:int64`; `tlp:int64`; `hb:int64`;
                `l:byte list`; `maxsv:num`; `fset:int64`; `ea:int64`;
                `el:num`; `ev:num`; `e:uarch_event list`] NC_MAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           UNDISCH_TAC `~(LENGTH(l:byte list) < 8)` THEN ARITH_TAC;
           NONOVERLAPPING_TAC];
    DISCH_TAC] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
    MAYCHANGE [memory :> bytes(nc,2 * (maxsv + 1));
               memory :> bytes(maxsvp,4); memory :> bytes(tlp,4);
               memory :> bytes(word_sub stackpointer (word 80),80)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
                MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
                SOME_FLAGS] THEN
    REWRITE_TAC[NC_STACK_REBASE] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
  MAP_EVERY EXISTS_TAC [nc_std_pre; nc_std_post nc_std_rr nc_wr] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `s:armstate` THEN
  BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `e2:uarch_event list` THEN ASM_REWRITE_TAC[] THEN
  MEMSAFE_OPAQUE_TAC
   (MEMSAFE_NORM_CONV (stack_bases [nc_fin_rr; nc_fin_wr])));;

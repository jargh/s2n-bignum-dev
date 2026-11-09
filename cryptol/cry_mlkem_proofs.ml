(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proofs that the translated Cryptol functions of cryptol/cry_mlkem.ml      *)
(* agree with the specification in common/fips203.ml, up to the ML-KEM API   *)
(* of each parameter set (CRY_MLKEM512, CRY_MLKEM768, CRY_MLKEM1024 at the   *)
(* end).                                                                     *)
(* ========================================================================= *)

needs "cryptol/cry_mlkem.ml";;

(* ------------------------------------------------------------------------- *)
(* Rounding, compression and decompression.                                  *)
(* ------------------------------------------------------------------------- *)

let CRY_ROUNDNEAREST_INT = prove
 (`!a b. &0 < b
         ==> cry_roundNearest(real_of_int a / real_of_int b) =
             mlkem_round(a,b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cry_roundNearest] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `mlkem_round(a,b)`] MLKEM_ROUND_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[int_le; int_lt; int_mul_th; int_add_th; int_of_num_th] THEN
  ABBREV_TAC `n = real_of_int(mlkem_round(a,b))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < real_of_int b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM int_of_num_th; GSYM int_lt]; ALL_TAC] THEN
  SUBGOAL_THEN `floor(real_of_int a / real_of_int b + &1 / &2) = n`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN CONJ_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[INTEGER_REAL_OF_INT]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `n <= x + &1 / &2 <=> n - &1 / &2 <= x`;
                REAL_ARITH `x + &1 / &2 < n + &1 <=> x < n + &1 / &2`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "n" THEN REWRITE_TAC[int_tybij]]);;

let CRY_COMPRESS = prove
 (`!x. &(val(cry_Compress x:N word)) = mlkem_compress (dimindex(:N)) x`,
  GEN_TAC THEN REWRITE_TAC[cry_Compress; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `(&2 pow dimindex(:N) / &3329) * real_of_int x =
    real_of_int(&2 pow dimindex(:N) * x) / real_of_int(&3329)`
  SUBST1_TAC THENL
   [REWRITE_TAC[int_mul_th; int_pow_th; int_of_num_th] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[CRY_ROUNDNEAREST_INT; INT_ARITH `&0:int < &3329`] THEN
  REWRITE_TAC[mlkem_compress] THEN ONCE_REWRITE_TAC[GSYM IWORD_REM_SIZE] THEN
  MATCH_MP_TAC INT_VAL_IWORD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_REM_POS; MATCH_MP_TAC INT_LT_REM] THEN
  REWRITE_TAC[INT_LT_POW2; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ]);;

let CRY_DECOMPRESS = prove
 (`!y:N word.
        dimindex(:N) < 12
        ==> cry_Decompress y = mlkem_decompress (dimindex(:N)) (&(val y))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[cry_Decompress; mlkem_decompress; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `(&3329 / &2 pow dimindex(:N)) * real_of_int(&(val(y:N word))) =
    real_of_int(&3329 * &(val y)) / real_of_int(&2 pow dimindex(:N))`
  SUBST1_TAC THENL
   [REWRITE_TAC[int_mul_th; int_pow_th; int_of_num_th] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[CRY_ROUNDNEAREST_INT; INT_LT_POW2] THEN
  MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[mlkem_round] THEN
  ABBREV_TAC `d = dimindex(:N)` THEN
  MP_TAC(ISPEC `y:N word` VAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP d <= 2 EXP 11` MP_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_POW] THEN
  MP_TAC(SPEC `d:num` INT_LT_POW2) THEN
  SPEC_TAC(`(&2 pow d):int`,`p:int`) THEN
  MP_TAC(SPEC `val(y:N word)` INT_POS) THEN
  SPEC_TAC(`&(val(y:N word)):int`,`v:int`) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC INT_LE_DIV THEN ASM_INT_ARITH_TAC;
    ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_ARITH `&0:int < p ==> &0 < &2 * p`] THEN
    ASM_INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Generic lemmas about the list functions of the translation.               *)
(* ------------------------------------------------------------------------- *)

let LENGTH_CRY_RANGE = prove
 (`!a b. LENGTH(cry_range a b) = (b + 1) - a`,
  REWRITE_TAC[cry_range; LENGTH_LIST_OF_SEQ]);;

let EL_CRY_RANGE = prove
 (`!a b i. i < (b + 1) - a ==> EL i (cry_range a b) = a + i`,
  SIMP_TAC[cry_range; EL_LIST_OF_SEQ]);;

let CRY_JOIN_CLAUSES = prove
 (`cry_join ([]:(A list) list) = [] /\
   (!h t. cry_join (CONS (h:A list) t) = APPEND h (cry_join t))`,
  REWRITE_TAC[cry_join; ITLIST]);;

let LENGTH_CRY_JOIN_MAP = prove
 (`!(f:A->B list) n l.
        (!x. MEM x l ==> LENGTH(f x) = n)
        ==> LENGTH(cry_join(MAP f l)) = n * LENGTH l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; CRY_JOIN_CLAUSES; LENGTH; MEM; LENGTH_APPEND] THEN
  ASM_SIMP_TAC[MULT_CLAUSES] THEN ARITH_TAC);;

let EL_CRY_JOIN_MAP = prove
 (`!(f:A->B list) n l i.
        (!x. MEM x l ==> LENGTH(f x) = n) /\ i < n * LENGTH l
        ==> EL i (cry_join(MAP f l)) = EL (i MOD n) (f(EL (i DIV n) l))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; MULT_CLAUSES; LT; MAP; CRY_JOIN_CLAUSES; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH((f:A->B list) h) = n` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i < n` THENL
   [ASM_SIMP_TAC[EL_APPEND; DIV_LT; MOD_LT; EL; HD]; ALL_TAC] THEN
  ASM_REWRITE_TAC[EL_APPEND] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `i < 0 + 0 * LENGTH(t:A list)` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `i DIV n = SUC((i - n) DIV n) /\ i MOD n = (i - n) MOD n`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [SUBGOAL_THEN `i = (i - n) + 1 * n` (fun th -> GEN_REWRITE_TAC
      (BINOP_CONV o LAND_CONV o LAND_CONV) [th])
    THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ADD1]];
    ALL_TAC] THEN
  REWRITE_TAC[EL; TL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `i < n + n * LENGTH(t:A list)` THEN
  UNDISCH_TAC `~(i < n)` THEN ARITH_TAC);;

let LENGTH_CRY_GROUPBY = prove
 (`!each (l:A list). LENGTH(cry_groupBy each l) = LENGTH l DIV each`,
  REWRITE_TAC[cry_groupBy; LENGTH_LIST_OF_SEQ]);;

let EL_CRY_GROUPBY = prove
 (`!each (l:A list) i.
        i < LENGTH l DIV each
        ==> EL i (cry_groupBy each l) =
            list_of_seq (\j. EL (each * i + j) l) each`,
  SIMP_TAC[cry_groupBy; EL_LIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* Bits of byte lists and of binary digit sums.                              *)
(* ------------------------------------------------------------------------- *)

let DIV_ADD_POW2_MULT = prove
 (`!a b k m. k <= m
             ==> (a + 2 EXP m * b) DIV 2 EXP k =
                 a DIV 2 EXP k + 2 EXP (m - k) * b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP m = 2 EXP (m - k) * 2 EXP k` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUM_RING `a + (x * y) * b:num = (x * b) * y + a`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN REWRITE_TAC[ADD_SYM]);;

let BIT_EL_BYTELIST = prove
 (`!l:byte list k.
        k < 8 * LENGTH l
        ==> (bit (k MOD 8) (EL (k DIV 8) l) <=>
             ODD(num_of_bytelist l DIV 2 EXP k))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; MULT_CLAUSES; LT] THEN
  REWRITE_TAC[num_of_bytelist; ARITH_RULE `256 = 2 EXP 8`] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_CASES_TAC `k < 8` THENL
   [ASM_SIMP_TAC[DIV_LT; MOD_LT; EL; HD; BIT_VAL; DIV_ADD_POW2_MULT;
                 LT_IMP_LE] THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ODD_EXP; ARITH_ODD] THEN
    ASM_SIMP_TAC[ARITH_RULE `k < 8 ==> ~(8 - k = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `k DIV 8 = SUC((k - 8) DIV 8) /\ k MOD 8 = (k - 8) MOD 8`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [SUBGOAL_THEN `k = (k - 8) + 1 * 8` (fun th -> GEN_REWRITE_TAC
      (BINOP_CONV o LAND_CONV o LAND_CONV) [th])
    THENL [ASM_ARITH_TAC;
           SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ADD1; ARITH_EQ]];
    ALL_TAC] THEN
  REWRITE_TAC[EL; TL] THEN
  FIRST_X_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand) th o
    lhand o snd)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `2 EXP k = 2 EXP 8 * 2 EXP (k - 8)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  SIMP_TAC[DIV_ADD_POW2_MULT; LE_REFL; SUB_REFL; EXP; MULT_CLAUSES] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  SIMP_TAC[DIV_LT; ADD_CLAUSES]);;

let NUMSEG_LT_1 = prove
 (`{i | i < 1} = {0}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN ARITH_TAC);;

let ODD_BINARY_DIGITSUM = prove
 (`!c n k. ODD(nsum {i | i < n} (\i. 2 EXP i * bitval(c i)) DIV 2 EXP k) <=>
           k < n /\ c k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_MOD] THEN
  MP_TAC(ISPECL [`2`; `\i. bitval((c:num->bool) i)`; `n:num`; `k:num`]
         DIGITSUM_DIV_NUMSEG) THEN
  REWRITE_TAC[BITVAL_BOUND_ALT] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`2`; `\i. bitval((c:num->bool)(i + k))`; `n - k`; `1`]
         DIGITSUM_MOD_NUMSEG) THEN
  REWRITE_TAC[BITVAL_BOUND_ALT; EXP_1] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `k < n` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[ARITH_RULE `k < n ==> MIN (n - k) 1 = 1`] THEN
    REWRITE_TAC[NUMSEG_LT_1; NSUM_SING] THEN
    REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; BITVAL_EQ_1];
    ASM_SIMP_TAC[ARITH_RULE `~(k < n) ==> MIN (n - k) 1 = 0`] THEN
    REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* BitsToBytes.                                                              *)
(* ------------------------------------------------------------------------- *)

let NSUM_LT_SUC_LEFT = prove
 (`!f n. nsum {t | t < SUC n} f = f 0 + nsum {t | t < n} (\t. f(SUC t))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[NUMSEG_CLAUSES_LT] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN ARITH_TAC);;

let CRY_WSUM_LIST_OF_SEQ_WORD = prove
 (`!f n. cry_wsum (list_of_seq (\t. word(f t):N word) n) =
         word(nsum {t | t < n} f)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[cry_wsum; LIST_OF_SEQ; ITLIST] THEN
  REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
  X_GEN_TAC `f:num->num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\t. (f:num->num)(SUC t)` o
    REWRITE_RULE[cry_wsum]) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NSUM_LT_SUC_LEFT; WORD_ADD]);;

let EL_ZIP = prove
 (`!(l1:A list) (l2:B list) n.
        LENGTH l1 = LENGTH l2 /\ n < LENGTH l1
        ==> EL n (ZIP l1 l2) = EL n l1,EL n l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; CONJUNCT1 LT; ZIP] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC]);;

let CRY_LIST_OF_SEQ_EQ = prove
 (`!(f:num->A) g n. (!i. i < n ==> f i = g i)
                    ==> list_of_seq f n = list_of_seq g n`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let LENGTH_CRY_BITSTOBYTES = prove
 (`!b. LENGTH(cry_BitsToBytes b) = LENGTH b DIV 8`,
  GEN_TAC THEN REWRITE_TAC[cry_BitsToBytes] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH_MAP; LENGTH_CRY_GROUPBY] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LENGTH_ZIP o lhand o snd) THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_ARITH_TAC);;

let BIT_EL_CRY_BITSTOBYTES = prove
 (`!b k. 8 divides LENGTH b /\ k < LENGTH b
         ==> (bit (k MOD 8) (EL (k DIV 8) (cry_BitsToBytes b)) <=> EL k b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVIDES_DIV_MULT] THEN STRIP_TAC THEN
  ABBREV_TAC `m = LENGTH(b:bool list) DIV 8` THEN
  SUBGOAL_THEN `k DIV 8 < m` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `zl = ZIP (MAP (\bi. word(bitval bi):byte) b)
                       (cry_range 0 (LENGTH b - 1))` THEN
  SUBGOAL_THEN `LENGTH(zl:(byte#num)list) = LENGTH(b:bool list)`
  ASSUME_TAC THENL
   [EXPAND_TAC "zl" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) LENGTH_ZIP o lhand o snd) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cry_BitsToBytes] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `k DIV 8 < LENGTH(cry_groupBy 8 (zl:(byte#num)list))` ASSUME_TAC
  THENL [ASM_REWRITE_TAC[LENGTH_CRY_GROUPBY]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  SUBGOAL_THEN `k DIV 8 < LENGTH(zl:(byte#num)list) DIV 8` ASSUME_TAC
  THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_CRY_GROUPBY; MAP_LIST_OF_SEQ; o_DEF] THEN
  SUBGOAL_THEN
   `!t. t < 8
        ==> (\(bi,i). word_mul bi (word(2 EXP (i MOD 8))):byte)
            (EL (8 * k DIV 8 + t) (zl:(byte#num)list)) =
            word(2 EXP t * bitval(EL (8 * k DIV 8 + t) b))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `8 * k DIV 8 + t < LENGTH(b:bool list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "zl" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) EL_ZIP o rand o lhand o snd) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; EL_CRY_RANGE; ARITH_RULE
     `x < n ==> x < (n - 1 + 1) - 0`] THEN
    REWRITE_TAC[ADD_CLAUSES; WORD_MUL] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT] THEN REWRITE_TAC[WORD_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `list_of_seq
     (\x. (\(bi,i). word_mul bi (word(2 EXP (i MOD 8))):byte)
          (EL (8 * k DIV 8 + x) (zl:(byte#num)list))) 8 =
    list_of_seq (\t. word(2 EXP t * bitval(EL (8 * k DIV 8 + t) b))) 8`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CRY_LIST_OF_SEQ_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CRY_WSUM_LIST_OF_SEQ_WORD; BIT_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ODD_BINARY_DIGITSUM] THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
  MP_TAC(SPECL [`k:num`; `8`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN MESON_TAC[MULT_SYM; ADD_SYM]);;

let ODD_MOD_POW2_DIV = prove
 (`!y m k. k < m
           ==> (ODD((y MOD 2 EXP m) DIV 2 EXP k) <=> ODD(y DIV 2 EXP k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP m = 2 EXP k * 2 EXP (m - k)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_MOD; ODD_MOD_POW2] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < m ==> ~(m - k = 0)`]);;

let BIT_EL_BYTELIST_OF_NUM = prove
 (`!n x k. k < 8 * n
           ==> (bit (k MOD 8) (EL (k DIV 8) (bytelist_of_num n x)) <=>
                ODD(x DIV 2 EXP k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`bytelist_of_num n x`; `k:num`] BIT_EL_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
  ASM_SIMP_TAC[ODD_MOD_POW2_DIV]);;

let BYTELIST_EQ_BITS = prove
 (`!l1 l2:byte list.
        LENGTH l1 = LENGTH l2 /\
        (!k. k < 8 * LENGTH l1
             ==> (bit (k MOD 8) (EL (k DIV 8) l1) <=>
                  bit (k MOD 8) (EL (k DIV 8) l2)))
        ==> l1 = l2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIST_EQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_8] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j * 8 + t`) THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ;
               ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `j < LENGTH(l2:byte list)` THEN UNDISCH_TAC `t < 8` THEN
  ARITH_TAC);;

let LENGTH_CRY_BYTESTOBITS = prove
 (`!C. LENGTH(cry_BytesToBits C) = 8 * LENGTH C`,
  GEN_TAC THEN REWRITE_TAC[cry_BytesToBits] THEN
  MATCH_MP_TAC LENGTH_CRY_JOIN_MAP THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN CONV_TAC NUM_REDUCE_CONV);;

let EL_CRY_BYTESTOBITS = prove
 (`!C k. k < 8 * LENGTH C
         ==> EL k (cry_BytesToBits C) = bit (k MOD 8) (EL (k DIV 8) C)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cry_BytesToBits] THEN
  MP_TAC(ISPECL [`\Ci:byte. MAP (\j. bit 0 (word_ushr Ci j)) (cry_range 0 7)`;
                 `8`; `C:byte list`; `k:num`] EL_CRY_JOIN_MAP) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[EL_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE; MOD_LT_EQ; ARITH_EQ;
           ARITH_RULE `(7 + 1) - 0 = 8`; BIT_WORD_USHR; ADD_CLAUSES]);;

let ODD_DIGITSUM_BLOCKS = prove
 (`!d n (v:num->num) k.
        ~(d = 0) /\ (!i. i < n ==> v i < 2 EXP d) /\ k < d * n
        ==> (ODD(nsum {i | i < n} (\i. 2 EXP (d * i) * v i) DIV 2 EXP k) <=>
             ODD(v(k DIV d) DIV 2 EXP (k MOD d)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `d:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = k DIV d` THEN ABBREV_TAC `r = k MOD d` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `q < n` ASSUME_TAC THENL
   [SUBGOAL_THEN `q * d < n * d` MP_TAC THENL
     [UNDISCH_TAC `q * d + r < d * n` THEN ARITH_TAC;
      ASM_SIMP_TAC[LT_MULT_RCANCEL]];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `q * d + r = d * q + r`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; GSYM EXP_EXP] THEN
  MP_TAC(ISPECL [`2 EXP d`; `v:num->num`; `n:num`; `q:num`]
         DIGITSUM_DIV_NUMSEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  W(fun (asl,w) -> let y = lhand(rand(lhand w)) in
     MP_TAC(SPECL [y; `d:num`; `r:num`] ODD_MOD_POW2_DIV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`2 EXP d`; `\i. (v:num->num)(i + q)`; `n - q`; `1`]
         DIGITSUM_MOD_NUMSEG) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[EXP_1] THEN DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `q < n ==> MIN (n - q) 1 = 1`] THEN
  REWRITE_TAC[NUMSEG_LT_1; NSUM_SING; EXP; MULT_CLAUSES; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* ByteEncode.                                                               *)
(* ------------------------------------------------------------------------- *)

let CRY_DIV8_256 = prove
 (`!d. (d * 256) DIV 8 = 32 * d`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `d * 256 = 8 * (32 * d)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let cry_byteencode_ef =
 `((\ajs. MAP (\a:N word. bit 0 a) ajs) o
   (\a. MAP (\j. word_ushr a j) (cry_range 0 (d - 1))))`;;

let CRY_BYTEENCODE = prove
 (`!Fv:(N word) list.
        LENGTH Fv = 256
        ==> cry_ByteEncode Fv =
            mlkem_encode (dimindex(:N)) 256 (\i. &(val(EL i Fv)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cry_ByteEncode; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `d = dimindex(:N)` THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MAP_o] THEN
  ABBREV_TAC
   `b = cry_join (MAP ((\ajs. MAP (\a:N word. bit 0 a) ajs) o
                       (\a. MAP (\j. word_ushr a j) (cry_range 0 (d - 1))))
                      (Fv:(N word) list))` THEN
  SUBGOAL_THEN
   `!x:N word. LENGTH(((\ajs. MAP (\a:N word. bit 0 a) ajs) o
                (\a. MAP (\j. word_ushr a j) (cry_range 0 (d - 1)))) x) = d`
  ASSUME_TAC THENL
   [REWRITE_TAC[o_THM; LENGTH_MAP; LENGTH_CRY_RANGE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(b:bool list) = d * 256` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    MP_TAC(ISPECL [cry_byteencode_ef; `d:num`; `Fv:(N word) list`]
           LENGTH_CRY_JOIN_MAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < d * 256
        ==> EL k b = bit (k MOD d) (EL (k DIV d) (Fv:(N word) list))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "b" THEN
    MP_TAC(ISPECL [cry_byteencode_ef; `d:num`; `Fv:(N word) list`; `k:num`]
           EL_CRY_JOIN_MAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[o_THM; EL_MAP; LENGTH_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE;
                 MOD_LT_EQ; ARITH_RULE `~(d = 0) ==> (d - 1 + 1) - 0 = d`;
                 ARITH_RULE `~(d = 0) ==> d - 1 + 1 = d`;
                 BIT_WORD_USHR; ADD_CLAUSES];
    ALL_TAC] THEN
  MATCH_MP_TAC BYTELIST_EQ_BITS THEN
  REWRITE_TAC[LENGTH_CRY_BITSTOBYTES; MLKEM_ENCODE_LENGTH; CRY_DIV8_256] THEN
  ASM_REWRITE_TAC[CRY_DIV8_256] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k < d * 256` ASSUME_TAC THENL
   [UNDISCH_TAC `k < 8 * 32 * d` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`b:bool list`; `k:num`] BIT_EL_CRY_BITSTOBYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[DIVIDES_DIV_MULT] THEN
    REWRITE_TAC[CRY_DIV8_256] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[mlkem_encode; CRY_DIV8_256] THEN
  ASM_SIMP_TAC[BIT_EL_BYTELIST_OF_NUM; ARITH_RULE
   `k < d * 256 ==> k < 8 * 32 * d`] THEN
  SUBGOAL_THEN
   `nsum {i | i < 256}
     (\i. num_of_int (&(val (EL i (Fv:(N word)list))) rem &2 pow d) *
          2 EXP (d * i)) =
    nsum {i | i < 256} (\i. 2 EXP (d * i) * val(EL i Fv))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
    MP_TAC(ISPEC `EL i (Fv:(N word)list)` VAL_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:num`; `256`; `\i. val(EL i (Fv:(N word)list))`; `k:num`]
         ODD_DIGITSUM_BLOCKS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `EL i (Fv:(N word)list)` VAL_BOUND) THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BIT_VAL]]);;

(* ------------------------------------------------------------------------- *)
(* ByteDecode, and the 12-bit versions.                                      *)
(* ------------------------------------------------------------------------- *)

let ZIP_LIST_OF_SEQ_RANGE = prove
 (`!(f:num->A) d.
        ~(d = 0)
        ==> ZIP (list_of_seq f d) (cry_range 0 (d - 1)) =
            list_of_seq (\j. f j,j) d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH(list_of_seq (f:num->A) d) = LENGTH(cry_range 0 (d - 1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_CRY_RANGE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ] THEN ASM_SIMP_TAC[LENGTH_ZIP] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_CRY_RANGE] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`list_of_seq (f:num->A) d`; `cry_range 0 (d - 1)`; `j:num`]
         EL_ZIP) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_CRY_RANGE] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `j < d` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_CRY_RANGE;
               ARITH_RULE `j < d ==> j < (d - 1 + 1) - 0`; ADD_CLAUSES]);;

let LENGTH_CRY_BYTEDECODE = prove
 (`!B. LENGTH B = 32 * dimindex(:N)
       ==> LENGTH(cry_ByteDecode B:(N word)list) = 256`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_ByteDecode; LET_DEF; LET_END_DEF; LENGTH_MAP; cry_split;
              LENGTH_CRY_GROUPBY; LENGTH_CRY_BYTESTOBITS] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 32 * d = 256 * d`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[DIV_MULT; DIMINDEX_NONZERO]);;

let LT_MULT_ADD_BLOCK = prove
 (`!d n i j. i < n /\ j < d ==> d * i + j < d * n`,
  REPEAT STRIP_TAC THEN TRANS_TAC LTE_TRANS `d * (i + 1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]);;

let VAL_EL_CRY_BYTEDECODE = prove
 (`!B i. LENGTH B = 32 * dimindex(:N) /\ i < 256
         ==> val(EL i (cry_ByteDecode B:(N word) list)) =
             (num_of_bytelist B DIV 2 EXP (dimindex(:N) * i)) MOD
             2 EXP dimindex(:N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cry_ByteDecode; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `d = dimindex(:N)` THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
  ABBREV_TAC `bb = cry_BytesToBits B` THEN
  SUBGOAL_THEN `LENGTH(bb:bool list) = d * 256` ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN ASM_REWRITE_TAC[LENGTH_CRY_BYTESTOBITS] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cry_split 256 (bb:bool list) = cry_groupBy d bb`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[cry_split] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[DIV_MULT; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `i < LENGTH(cry_groupBy d (bb:bool list))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_CRY_GROUPBY] THEN ASM_SIMP_TAC[DIV_MULT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  SUBGOAL_THEN `i < LENGTH(bb:bool list) DIV d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIV_MULT]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_CRY_GROUPBY; ZIP_LIST_OF_SEQ_RANGE; MAP_LIST_OF_SEQ;
               o_DEF] THEN
  REWRITE_TAC[WORD_SHL_WORD; CRY_WSUM_LIST_OF_SEQ_WORD] THEN
  ASM_REWRITE_TAC[VAL_WORD] THEN
  SIMP_TAC[MOD_LT; BINARY_DIGITSUM_BOUND] THEN
  SUBGOAL_THEN
   `!x. x < d
        ==> EL (d * i + x) (bb:bool list) =
            ODD(num_of_bytelist B DIV 2 EXP (d * i + x))`
  MP_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `d * i + x < 8 * LENGTH(B:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `8 * 32 * d = d * 256`] THEN
      MATCH_MP_TAC LT_MULT_ADD_BLOCK THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "bb" THEN ASM_SIMP_TAC[EL_CRY_BYTESTOBITS; BIT_EL_BYTELIST];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `num_of_bytelist B DIV 2 EXP (d * i)`; `d:num`]
         DIGITSUM_WORKS_GEN) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `x:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BITVAL_ODD; EXP_ADD; DIV_DIV]);;

let CRY_BYTEDECODE = prove
 (`!B. LENGTH B = 32 * dimindex(:N) /\ dimindex(:N) < 12
       ==> LENGTH(cry_ByteDecode B:(N word)list) = 256 /\
           !i. i < 256
               ==> &(val(EL i (cry_ByteDecode B:(N word)list))) =
                   mlkem_decode (dimindex(:N)) B i`,
  SIMP_TAC[LENGTH_CRY_BYTEDECODE; VAL_EL_CRY_BYTEDECODE] THEN
  REWRITE_TAC[mlkem_decode; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;

let CRY_BYTEENCODE12 = prove
 (`!Fv. LENGTH Fv = 256 /\ (!i. i < 256 ==> &0 <= EL i Fv /\ EL i Fv < &4096)
        ==> cry_ByteEncode12 Fv = mlkem_encode 12 256 (\i. EL i Fv)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `cry_ByteEncode12 Fv = cry_ByteEncode (MAP (\f. iword f:12 word) Fv)`
  SUBST1_TAC THENL
   [REWRITE_TAC[cry_ByteEncode12; cry_ByteEncode; LET_DEF; LET_END_DEF;
                DIMINDEX_12];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRY_BYTEENCODE o lhand o snd) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; DIMINDEX_12] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MLKEM_ENCODE_EQ THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_MAP] THEN MATCH_MP_TAC INT_VAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_12] THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_SIMP_TAC[]);;

let CRY_BYTEDECODE12 = prove
 (`!B. LENGTH B = 384
       ==> LENGTH(cry_ByteDecode12 B) = 256 /\
           !i. i < 256 ==> EL i (cry_ByteDecode12 B) = mlkem_decode 12 B i`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `cry_ByteDecode12 B =
    MAP (\f:12 word. &(val f) rem &3329) (cry_ByteDecode B)`
  SUBST1_TAC THENL
   [REWRITE_TAC[cry_ByteDecode12; cry_ByteDecode; LET_DEF; LET_END_DEF;
                DIMINDEX_12];
    ALL_TAC] THEN
  MP_TAC(ISPEC `B:byte list`
          (INST_TYPE [`:12`,`:N`] LENGTH_CRY_BYTEDECODE)) THEN
  ASM_REWRITE_TAC[DIMINDEX_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN
  MP_TAC(SPECL [`B:byte list`; `i:num`]
          (INST_TYPE [`:12`,`:N`] VAL_EL_CRY_BYTEDECODE)) THEN
  ASM_REWRITE_TAC[DIMINDEX_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mlkem_decode; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* SamplePolyCBD.                                                            *)
(* ------------------------------------------------------------------------- *)

let CRY_ZSUM_REM = prove
 (`!l. cry_zsum l = ITLIST (+) l (&0) rem &3329`,
  REWRITE_TAC[cry_zsum; INTEGER_MOD_RING_CLAUSES] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[]);;

let ITLIST_ADD_LIST_OF_SEQ_NUM = prove
 (`!f n. ITLIST (+) (list_of_seq (\j. &(f j):int) n) (&0) =
         &(nsum {j | j < n} f)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ; ITLIST; CONJUNCT1 LT; EMPTY_GSPEC;
              NSUM_CLAUSES] THEN
  X_GEN_TAC `f:num->num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\t. (f:num->num)(SUC t)`) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NSUM_LT_SUC_LEFT; INT_OF_NUM_ADD]);;

let CRY_RANGE_0 = prove
 (`!n. ~(n = 0) ==> cry_range 0 (n - 1) = list_of_seq (\i. i) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cry_range; ADD_CLAUSES] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let CRY_SAMPLEPOLYCBD = prove
 (`!eta B. LENGTH B = 64 * eta /\ ~(eta = 0)
           ==> LENGTH(cry_SamplePolyCBD eta B) = 256 /\
               mlkem_poly (\i. EL i (cry_SamplePolyCBD eta B)) =
               mlkem_cbd eta B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cry_SamplePolyCBD; mlkem_cbd; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mlkem_poly; FUN_EQ_THM] THEN X_GEN_TAC `m:1->num` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ABBREV_TAC `i = (m:1->num) one` THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE; ARITH_RULE
    `i < 256 ==> i < (255 + 1) - 0`] THEN
  REWRITE_TAC[ADD_CLAUSES; INTEGER_MOD_RING_CLAUSES; CRY_ZSUM_REM] THEN
  ASM_SIMP_TAC[CRY_RANGE_0; MAP_LIST_OF_SEQ; o_DEF] THEN
  SUBGOAL_THEN
   `!t. t < 2 * eta
        ==> EL (2 * i * eta + t)
               (MAP (\bit. if bit then &1 else &0) (cry_BytesToBits B)) =
            &((num_of_bytelist B DIV 2 EXP (2 * eta * i + t)) MOD 2):int`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `2 * i * eta + t < 8 * LENGTH(B:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NUM_RING `2 * i * eta = (2 * eta) * i`;
                      ARITH_RULE `8 * 64 * eta = (2 * eta) * 256`] THEN
      MATCH_MP_TAC LT_MULT_ADD_BLOCK THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `2 * i * eta + t < LENGTH(cry_BytesToBits B)` ASSUME_TAC
    THENL [REWRITE_TAC[LENGTH_CRY_BYTESTOBITS] THEN FIRST_ASSUM ACCEPT_TAC;
           ALL_TAC] THEN
    MP_TAC(ISPECL [`\bit. if bit then &1 else &0:int`;
                   `2 * i * eta + t`; `cry_BytesToBits B`] EL_MAP) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`B:byte list`; `2 * i * eta + t`] EL_CRY_BYTESTOBITS) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`B:byte list`; `2 * i * eta + t`] BIT_EL_BYTELIST) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[NUM_RING `2 * i * eta = 2 * eta * i`; GSYM BITVAL_ODD] THEN
    REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `list_of_seq (\x. EL (2 * i * eta + x)
                   (MAP (\bit. if bit then &1 else &0) (cry_BytesToBits B)))
                eta =
    list_of_seq (\x. &((num_of_bytelist B DIV 2 EXP (2 * eta * i + x)) MOD 2)
                     :int) eta /\
    list_of_seq (\x. EL (2 * i * eta + eta + x)
                   (MAP (\bit. if bit then &1 else &0) (cry_BytesToBits B)))
                eta =
    list_of_seq (\x. &((num_of_bytelist B DIV 2 EXP (2 * eta * i + eta + x))
                       MOD 2):int) eta`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC CRY_LIST_OF_SEQ_EQ THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ITLIST_ADD_LIST_OF_SEQ_NUM] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* SampleNTT. First, the 12-bit candidates d1, d2 of the Cryptol filter are  *)
(* the fields mlkem_xof_field of fips203.ml.                                 *)
(* ------------------------------------------------------------------------- *)

let VAL_CRY_FILTER_D1 = prove
 (`!s. val(cry_filter_d1 s) = val(s 0) + 256 * (val(s 1) MOD 16)`,
  GEN_TAC THEN REWRITE_TAC[cry_filter_d1; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_UMOD; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_12; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `(s:num->byte) 0` VAL_BOUND) THEN
  MP_TAC(ISPEC `(s:num->byte) 1` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ARITH_RULE `x < 256 ==> x < 4096`; MOD_LT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val((s:num->byte) 1) MOD 16 < 16` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 16 ==> 256 * x < 4096`;
               ARITH_RULE `a < 256 /\ x < 16 ==> a + 256 * x < 4096`]);;

let VAL_CRY_FILTER_D2 = prove
 (`!s. val(cry_filter_d2 s) = val(s 1) DIV 16 + 16 * val(s 2)`,
  GEN_TAC THEN REWRITE_TAC[cry_filter_d2; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_UDIV; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_12; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `(s:num->byte) 1` VAL_BOUND) THEN
  MP_TAC(ISPEC `(s:num->byte) 2` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ARITH_RULE `x < 256 ==> x < 4096`; MOD_LT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val((s:num->byte) 1) DIV 16 < 16` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 256 ==> 16 * x < 4096`;
               ARITH_RULE `a < 16 /\ x < 256 ==> a + 16 * x < 4096`]);;

let NSUM_LT_ADD_SPLIT = prove
 (`!f m n. nsum {t | t < m + n} f =
           nsum {t | t < m} f + nsum {t | t < n} (\t. f(m + t))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
  REWRITE_TAC[NUMSEG_CLAUSES_LT] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NSUM_BITS_WORD = prove
 (`!x:N word.
        nsum {t | t < dimindex(:N)} (\t. bitval(bit t x) * 2 EXP t) = val x`,
  REWRITE_TAC[val_def] THEN REWRITE_TAC[MULT_AC]);;

let VAL_CRY_FILTER_CAND = prove
 (`!s n. val(cry_filter_cand s n) = mlkem_xof_field s n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cry_filter_cand; mlkem_xof_field; LET_DEF; LET_END_DEF] THEN
  DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
      REWRITE_RULE[EVEN_EXISTS]) THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
    REWRITE_TAC[VAL_CRY_FILTER_D1; ADD_CLAUSES] THEN
    MP_TAC(ISPECL
     [`\t. bitval (bit ((12 * 2 * m + t) MOD 8)
                       ((s:num->byte) ((12 * 2 * m + t) DIV 8))) *
           2 EXP t`; `8`; `4`] NSUM_LT_ADD_SPLIT) THEN
    CONV_TAC(LAND_CONV(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV))) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    BINOP_TAC THENL
     [MP_TAC(ISPEC `(s:num->byte)(3 * m)`
             (INST_TYPE [`:8`,`:N`] NSUM_BITS_WORD)) THEN
      REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE `12 * 2 * m + t = (3 * m) * 8 + t`] THEN
      ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ARITH_EQ;
                   ADD_CLAUSES];
      MP_TAC(ISPECL [`(s:num->byte)(3 * m + 1)`; `4`] VAL_MOD) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
      MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `12 * 2 * m + 8 + t = (3 * m + 1) * 8 + t`] THEN
      ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ARITH_EQ;
                   ADD_CLAUSES; ARITH_RULE `t < 4 ==> t < 8`] THEN
      REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
      REWRITE_RULE[ODD_EXISTS]) THEN
    REWRITE_TAC[GSYM NOT_EVEN; EVEN; EVEN_MULT; ARITH_EVEN] THEN
    SUBGOAL_THEN `SUC(2 * m) DIV 2 = m` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VAL_CRY_FILTER_D2] THEN
    MP_TAC(ISPECL
     [`\t. bitval (bit ((12 * SUC (2 * m) + t) MOD 8)
                       ((s:num->byte) ((12 * SUC (2 * m) + t) DIV 8))) *
           2 EXP t`; `4`; `8`] NSUM_LT_ADD_SPLIT) THEN
    CONV_TAC(LAND_CONV(LAND_CONV(ONCE_DEPTH_CONV NUM_ADD_CONV))) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    BINOP_TAC THENL
     [MP_TAC(ISPECL [`(s:num->byte)(3 * m + 1)`; `4`] VAL_DIV_ALT) THEN
      REWRITE_TAC[DIMINDEX_8] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `12 * SUC(2 * m) + t = (3 * m + 1) * 8 + (t + 4)`] THEN
      ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ARITH_EQ;
                   ADD_CLAUSES; ARITH_RULE `t < 4 ==> t + 4 < 8`] THEN
      REWRITE_TAC[MULT_SYM];
      MP_TAC(ISPEC `(s:num->byte)(3 * m + 2)`
             (INST_TYPE [`:8`,`:N`] NSUM_BITS_WORD)) THEN
      REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM NSUM_LMUL] THEN
      MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `12 * SUC(2 * m) + 4 + t = (3 * m + 2) * 8 + t`] THEN
      ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ARITH_EQ;
                   ADD_CLAUSES] THEN
      REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The subsequence of the elements of a stream that satisfy a predicate      *)
(* (cry_stream_filter), and its one-step recursion equation.                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_LT_RESTRICT = prove
 (`!n (q:num->bool). FINITE {j | j < n /\ q j}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{j:num | j < n}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let CARD_LT_SUC_RESTRICT = prove
 (`!q n. CARD {j | j < SUC n /\ q j} =
         CARD {j | j < n /\ q j} + (if q n then 1 else 0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `{j | j < SUC n /\ q j} = n INSERT {j | j < n /\ q j}`
     SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT] THEN
      ASM_MESON_TAC[];
      SIMP_TAC[CARD_CLAUSES; FINITE_LT_RESTRICT; IN_ELIM_THM; LT_REFL] THEN
      ARITH_TAC];
    REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; LT] THEN ASM_MESON_TAC[]]);;

let CARD_LT_ADD_SPLIT = prove
 (`!q m n. CARD {j | j < m + n /\ q j} =
           CARD {j | j < m /\ q j} + CARD {j | j < n /\ q(m + j)}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES];
    ASM_REWRITE_TAC[ADD_CLAUSES; CARD_LT_SUC_RESTRICT] THEN ARITH_TAC]);;

let INFINITE_SHIFT_1 = prove
 (`!q. INFINITE {j | q j} ==> INFINITE {j | q(j + 1)}`,
  GEN_TAC THEN
  REWRITE_TAC[INFINITE; num_FINITE; IN_ELIM_THM; CONTRAPOS_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN EXISTS_TAC `a + 1` THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x - 1`) THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1] THEN ARITH_TAC);;

let STREAM_FILTER_INDEX_LT = prove
 (`!p (c:num->A) j1 j2.
        p(c j1) /\ j1 < j2
        ==> CARD {j | j < j1 /\ p(c j)} < CARD {j | j < j2 /\ p(c j)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `CARD(j1 INSERT {j | j < j1 /\ p((c:num->A) j)})` THEN
  CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_LT_RESTRICT] THEN
    REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN ARITH_TAC;
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_LT_RESTRICT] THEN
    REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[LT_TRANS]]);;

let STREAM_FILTER_AT = prove
 (`!p (c:num->A) n j.
        p(c j) /\ CARD {j' | j' < j /\ p(c j')} = n
        ==> cry_stream_filter p c n = c j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cry_stream_filter] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `i:num` THEN EQ_TAC THENL
   [STRIP_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  ASM_MESON_TAC[STREAM_FILTER_INDEX_LT; LT_REFL; LT_CASES]);;

let STREAM_FILTER_EXISTS = prove
 (`!p (c:num->A).
        INFINITE {j | p(c j)}
        ==> !n. ?j. p(c j) /\ CARD {j' | j' < j /\ p(c j')} = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INFINITE; num_FINITE; IN_ELIM_THM; NOT_EXISTS_THM;
              NOT_FORALL_THM; NOT_IMP; NOT_LE] THEN
  DISCH_TAC THEN INDUCT_TAC THENL
   [SUBGOAL_THEN `?x. p((c:num->A) x)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{j' | j' < k /\ p((c:num->A) j')} = j INSERT {j' | j' < j /\ p(c j')}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN ASM_MESON_TAC[LT_TRANS; LT_CASES];
      SIMP_TAC[CARD_CLAUSES; FINITE_LT_RESTRICT] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; LT_REFL]]]);;

let CRY_SAPPEND_NIL = prove
 (`!t:num->A. cry_sappend [] t = t`,
  REWRITE_TAC[cry_sappend; LENGTH; CONJUNCT1 LT; SUB_0; ETA_AX]);;

let CRY_SAPPEND_APPEND = prove
 (`!l1 l2 (t:num->A).
        cry_sappend l1 (cry_sappend l2 t) = cry_sappend (APPEND l1 l2) t`,
  REWRITE_TAC[cry_sappend; FUN_EQ_THM; LENGTH_APPEND; EL_APPEND] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(AP_TERM_TAC THEN ARITH_TAC) THEN ASM_ARITH_TAC);;

let STREAM_FILTER_STEP = prove
 (`!p (c:num->A).
        INFINITE {j | p(c j)}
        ==> cry_stream_filter p c =
            cry_sappend (if p(c 0) then [c 0] else [])
                        (cry_stream_filter p (\j. c(j + 1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A->bool`; `\j. (c:num->A)(j + 1)`]
         STREAM_FILTER_EXISTS) THEN
  ASM_SIMP_TAC[INFINITE_SHIFT_1] THEN DISCH_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; cry_sappend] THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
   `!m j. p((c:num->A)(j + 1)) /\
          CARD {j' | j' < j /\ p(c(j' + 1))} = m
          ==> cry_stream_filter p c ((if p(c 0) then 1 else 0) + m) =
              c(j + 1) /\
              cry_stream_filter p (\j. c(j + 1)) m = c(j + 1)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC STREAM_FILTER_AT THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[CARD_LT_ADD_SPLIT] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `1 + j = j + 1`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `CARD {j' | j' < 1 /\ p((c:num->A) j')} = if p(c 0) then 1 else 0`
      SUBST1_TAC THENL
       [REWRITE_TAC[ONE; CARD_LT_SUC_RESTRICT; CONJUNCT1 LT; EMPTY_GSPEC;
                    CARD_CLAUSES; ADD_CLAUSES];
        ARITH_TAC];
      MATCH_MP_TAC(BETA_RULE(ISPECL [`p:A->bool`; `\j. (c:num->A)(j + 1)`]
                     STREAM_FILTER_AT)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `p((c:num->A) 0):bool` THEN ASM_REWRITE_TAC[LENGTH] THENL
   [REWRITE_TAC[ARITH_RULE `n < SUC 0 <=> n = 0`] THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[EL; HD] THENL
     [MATCH_MP_TAC STREAM_FILTER_AT THEN
      ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES];
      FIRST_X_ASSUM(X_CHOOSE_TAC `j:num` o SPEC `n - SUC 0`) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n - SUC 0`; `j:num`]) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 1 + n - SUC 0 = n`]];
    REWRITE_TAC[CONJUNCT1 LT; SUB_0] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `j:num` o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The recursion equation of the Cryptol filter, and its uniqueness.         *)
(* ------------------------------------------------------------------------- *)

let CARD_LT_2 = prove
 (`!q. CARD {j | j < 2 /\ q j} =
       (if q 0 then 1 else 0) + (if q 1 then 1 else 0)`,
  REWRITE_TAC[TWO; ONE; CARD_LT_SUC_RESTRICT; CONJUNCT1 LT; EMPTY_GSPEC;
              CARD_CLAUSES; ADD_CLAUSES]);;

let CRY_FILTER_CAND_01 = prove
 (`!s. cry_filter_cand s 0 = cry_filter_d1 s /\
       cry_filter_cand s 1 = cry_filter_d2 s`,
  REWRITE_TAC[cry_filter_cand; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; ETA_AX]);;

let CRY_FILTER_CAND_SHIFT = prove
 (`!s j. cry_filter_cand s (j + 2) = cry_filter_cand (\i. s(i + 3)) j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cry_filter_cand; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[EVEN_ADD; ARITH_EVEN] THEN
  SUBGOAL_THEN `(j + 2) DIV 2 = j DIV 2 + 1` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `j + 2 = 1 * 2 + j`] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `3 * (k + 1) + i = (3 * k + i) + 3`]]);;

let CRY_FILTER_INFINITE_SHIFT = prove
 (`!s. INFINITE {j | val(cry_filter_cand s j) < 3329}
       ==> INFINITE {j | val(cry_filter_cand (\i. s(i + 3)) j) < 3329}`,
  GEN_TAC THEN REWRITE_TAC[GSYM CRY_FILTER_CAND_SHIFT] THEN
  REWRITE_TAC[ARITH_RULE `j + 2 = (j + 1) + 1`] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\j. val(cry_filter_cand s (j + 1)) < 3329`
         INFINITE_SHIFT_1) THEN
  MP_TAC(ISPEC `\j. val(cry_filter_cand s j) < 3329` INFINITE_SHIFT_1) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CRY_FILTER_COUNT2 = prove
 (`!s. CARD {j | j < 2 /\ val(cry_filter_cand s j) < 3329} =
       LENGTH(APPEND
        (if val(cry_filter_d1 s) < 3329 then [cry_filter_d1 s] else [])
        (if val(cry_filter_d2 s) < 3329 then [cry_filter_d2 s] else []))`,
  GEN_TAC THEN REWRITE_TAC[CARD_LT_2; CRY_FILTER_CAND_01] THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(cry_filter_d1 s) < 3329`; `val(cry_filter_d2 s) < 3329`] THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; LENGTH_APPEND] THEN ARITH_TAC);;

let CRY_SAPPEND_CASES = prove
 (`!P1 P2 (d1:A) d2 t.
        cry_sappend (if P1 then [d1] else [])
                    (cry_sappend (if P2 then [d2] else []) t) =
        if P1 /\ P2 then cry_sappend [d1; d2] t
        else if P1 then cry_sappend [d1] t
        else if P2 then cry_sappend [d2] t
        else t`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [`P1:bool`; `P2:bool`] THEN
  ASM_REWRITE_TAC[CRY_SAPPEND_APPEND; CRY_SAPPEND_NIL; APPEND]);;

(* The right-hand side of the recursion equation of filter, for any f in     *)
(* place of filter, in the form "a list of 0, 1 or 2 values, then f ctx".    *)

let CRY_FILTER_RHS = prove
 (`!(f:(num->byte)->num->12 word) s.
     (let ctx = \i. s(i + 3) in
      let C0 = (word_zx (s 0):12 word) and C1 = (word_zx (s 1):12 word)
      and C2 = (word_zx (s 2):12 word) in
      let d1 = word_add C0 (word_mul (word 256) (word_umod C1 (word 16)))
      and d2 = word_add (word_udiv C1 (word 16)) (word_mul (word 16) C2)
      in if val d1 < 3329 /\ val d2 < 3329
         then cry_sappend [d1; d2] (f ctx)
         else if val d1 < 3329 then cry_sappend [d1] (f ctx)
         else if val d2 < 3329 then cry_sappend [d2] (f ctx)
         else f ctx) =
     cry_sappend
      (APPEND (if val(cry_filter_d1 s) < 3329 then [cry_filter_d1 s] else [])
              (if val(cry_filter_d2 s) < 3329 then [cry_filter_d2 s] else []))
      (f (\i. s(i + 3)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF] cry_filter_d1);
              GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF] cry_filter_d2)] THEN
  REWRITE_TAC[GSYM CRY_SAPPEND_CASES; CRY_SAPPEND_APPEND]);;

let CRY_FILTER_STEP2 = prove
 (`!s. INFINITE {j | val(cry_filter_cand s j) < 3329}
       ==> cry_filter s =
           cry_sappend
            (APPEND
              (if val(cry_filter_d1 s) < 3329 then [cry_filter_d1 s] else [])
              (if val(cry_filter_d2 s) < 3329 then [cry_filter_d2 s] else []))
            (cry_filter (\i. s(i + 3)))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM CRY_SAPPEND_APPEND] THEN
  GEN_REWRITE_TAC LAND_CONV [cry_filter] THEN
  MP_TAC(ISPECL [`\x:12 word. val x < 3329`; `cry_filter_cand s`]
         STREAM_FILTER_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\x:12 word. val x < 3329`;
                 `\j. cry_filter_cand s (j + 1)`] STREAM_FILTER_STEP) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `\j. val(cry_filter_cand s j) < 3329` INFINITE_SHIFT_1) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(j + 1) + 1 = j + 2`; CRY_FILTER_CAND_SHIFT] THEN
  REWRITE_TAC[ADD_CLAUSES; CRY_FILTER_CAND_01; ETA_AX; cry_filter]);;

(* The recursion equation of the Cryptol filter holds for cry_filter on      *)
(* every stream with infinitely many candidates below q. (On other streams   *)
(* the Cryptol filter is undefined after the last such candidate.)           *)

let CRY_FILTER_EQN = prove
 (`!s. INFINITE {j | val(cry_filter_cand s j) < 3329}
       ==> cry_filter s =
           let ctx = \i. s(i + 3) in
           let C0 = (word_zx (s 0):12 word) and C1 = (word_zx (s 1):12 word)
           and C2 = (word_zx (s 2):12 word) in
           let d1 = word_add C0 (word_mul (word 256) (word_umod C1 (word 16)))
           and d2 = word_add (word_udiv C1 (word 16)) (word_mul (word 16) C2)
           in if val d1 < 3329 /\ val d2 < 3329
              then cry_sappend [d1; d2] (cry_filter ctx)
              else if val d1 < 3329 then cry_sappend [d1] (cry_filter ctx)
              else if val d2 < 3329 then cry_sappend [d2] (cry_filter ctx)
              else cry_filter ctx`,
  REWRITE_TAC[CRY_FILTER_RHS] THEN MATCH_ACCEPT_TAC CRY_FILTER_STEP2);;

(* And cry_filter is the only solution of the equation on those streams.     *)

let CRY_FILTER_UNIQUE = prove
 (`!g. (!s. INFINITE {j | val(cry_filter_cand s j) < 3329}
            ==> g s =
                let ctx = \i. s(i + 3) in
                let C0 = (word_zx (s 0):12 word)
                and C1 = (word_zx (s 1):12 word)
                and C2 = (word_zx (s 2):12 word) in
                let d1 = word_add C0
                          (word_mul (word 256) (word_umod C1 (word 16)))
                and d2 = word_add (word_udiv C1 (word 16))
                          (word_mul (word 16) C2)
                in if val d1 < 3329 /\ val d2 < 3329
                   then cry_sappend [d1; d2] (g ctx)
                   else if val d1 < 3329 then cry_sappend [d1] (g ctx)
                   else if val d2 < 3329 then cry_sappend [d2] (g ctx)
                   else g ctx)
       ==> !s. INFINITE {j | val(cry_filter_cand s j) < 3329}
               ==> g s = cry_filter s`,
  GEN_TAC THEN REWRITE_TAC[CRY_FILTER_RHS] THEN
  DISCH_THEN(LABEL_TAC "geq") THEN
  SUBGOAL_THEN
   `!j s n. INFINITE {j | val(cry_filter_cand s j) < 3329} /\
            val(cry_filter_cand s j) < 3329 /\
            CARD {j' | j' < j /\ val(cry_filter_cand s j') < 3329} = n
            ==> g s n = cry_filter s n`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `s:num->byte` THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`\x:12 word. val x < 3329`; `cry_filter_cand s`]
           STREAM_FILTER_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `j:num` o SPEC `n:num`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:num->byte`; `n:num`] THEN STRIP_TAC THEN
  USE_THEN "geq" (MP_TAC o SPEC `s:num->byte`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `s:num->byte` CRY_FILTER_STEP2) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[cry_sappend; GSYM CRY_FILTER_COUNT2] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 <= j` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:12 word. val x < 3329`; `cry_filter_cand s`;
                   `j:num`; `2`] STREAM_FILTER_INDEX_LT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
  ASM_SIMP_TAC[CRY_FILTER_INFINITE_SHIFT; GSYM CRY_FILTER_CAND_SHIFT;
               SUB_ADD] THEN
  MP_TAC(ISPECL [`\j. val(cry_filter_cand (s:num->byte) j) < 3329`;
                 `2`; `j - 2`] CARD_LT_ADD_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= j ==> 2 + j - 2 = j`] THEN
  REWRITE_TAC[ARITH_RULE `2 + j = j + 2`] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* SampleNTT itself. Its entries agree with mlkem_sample_ntt up to the rem,  *)
(* which is the identity whenever mlkem_sample_ntt picks a value below q:    *)
(* under the hypothesis of KPKE_KEYGEN_FIPS, or if the XOF output has        *)
(* infinitely many 12-bit fields below q.                                    *)
(* ------------------------------------------------------------------------- *)

let CRY_SAMPLENTT = prove
 (`!B. LENGTH(cry_SampleNTT B) = 256 /\
       !i. i < 256
           ==> EL i (cry_SampleNTT B) = mlkem_sample_ntt B i rem &3329`,
  GEN_TAC THEN REWRITE_TAC[cry_SampleNTT; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[cry_filter; cry_stream_filter; mlkem_sample_ntt; LET_DEF;
              LET_END_DEF; cry_XOF; mlkem_xof; VAL_CRY_FILTER_CAND]);;

let CRY_SAMPLENTT_EQ = prove
 (`!B i. i < 256 /\ mlkem_sample_ntt B i < &3329
         ==> EL i (cry_SampleNTT B) = mlkem_sample_ntt B i`,
  SIMP_TAC[CRY_SAMPLENTT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mlkem_sample_ntt; LET_DEF; LET_END_DEF; INT_POS]);;

let MLKEM_SAMPLE_NTT_BOUND = prove
 (`!B. INFINITE {j | mlkem_xof_field (mlkem_xof B) j < 3329}
       ==> !i. mlkem_sample_ntt B i < &3329`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mlkem_sample_ntt; LET_DEF; LET_END_DEF; INT_OF_NUM_LT] THEN
  MP_TAC(ISPECL [`\x. x < 3329`; `mlkem_xof_field (mlkem_xof B)`]
         STREAM_FILTER_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]);;

let CRY_SAMPLENTT_INFINITE = prove
 (`!B. INFINITE {j | mlkem_xof_field (mlkem_xof B) j < 3329}
       ==> LENGTH(cry_SampleNTT B) = 256 /\
           !i. i < 256 ==> EL i (cry_SampleNTT B) = mlkem_sample_ntt B i`,
  SIMP_TAC[CRY_SAMPLENTT; CRY_SAMPLENTT_EQ; MLKEM_SAMPLE_NTT_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* BitRev7, and NaiveNTT. In NaiveNTT the exponent of zeta is computed in    *)
(* [8], i.e. modulo 256, which is harmless since zeta has order 256.         *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_7 = DIMINDEX_CONV `dimindex(:7)`;;

let VAL_CRY_BITREV7 = prove
 (`!i:byte. val(cry_BitRev7 i) = bitreverse7(val i)`,
  GEN_TAC THEN REWRITE_TAC[cry_BitRev7; bitreverse7] THEN
  SUBGOAL_THEN `~(val(i:byte) > 255)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GT; NOT_LT] THEN MP_TAC(ISPEC `i:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_ushr (word_reversefields 1 i) 1:byte =
    word_zx (word_reversefields 1 (word_zx i:7 word))`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_ZX;
                BIT_WORD_REVERSEFIELDS; DIMINDEX_8; DIMINDEX_7] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    SIMP_TAC[VAL_WORD_ZX; DIMINDEX_7; DIMINDEX_8; ARITH; word_zx]]);;

let ZETA_POW_MOD_256 = prove
 (`!e. (&17 pow (e MOD 256)) rem &3329 = (&17 pow e) rem &3329`,
  GEN_TAC THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; INT_OF_NUM_EQ; GSYM CONG] THEN
  MP_TAC(SPECL [`17`; `3329`; `e MOD 256`; `e:num`] ORDER_DIVIDES_EXPDIFF) THEN
  REWRITE_TAC[MLKEM_ZETA_ORDER; CONG_LMOD; CONG_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONV_TAC COPRIME_CONV);;

let ISUM_LT_SUC_LEFT = prove
 (`!f n. isum {t | t < SUC n} f = f 0 + isum {t | t < n} (\t. f(SUC t))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[NUMSEG_CLAUSES_LT] THEN
  SIMP_TAC[ISUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; ISUM_CLAUSES; INT_ADD_AC]);;

let ITLIST_ADD_LIST_OF_SEQ_INT = prove
 (`!f n. ITLIST (+) (list_of_seq f n) (&0) = isum {j | j < n} f`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ; ITLIST; CONJUNCT1 LT; EMPTY_GSPEC;
              ISUM_CLAUSES] THEN
  X_GEN_TAC `f:num->int` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\t. (f:num->int)(SUC t)`) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ISUM_LT_SUC_LEFT]);;

let CRY_ZSUM_MAP_RANGE = prove
 (`!(g:N word->int) n.
        cry_zsum (MAP g (MAP word (cry_range 0 n))) =
        isum (0..n) (\j. g(word j)) rem &3329`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CRY_ZSUM_REM; cry_range; ADD_CLAUSES; SUB_0] THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ; ITLIST_ADD_LIST_OF_SEQ_INT; o_DEF] THEN
  SUBGOAL_THEN `{j | j < n + 1} = 0..n` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC);;

let LENGTH_CRY_JOIN_PAIRS = prove
 (`!(f:A->B) g l. LENGTH(cry_join(MAP (\x. [f x; g x]) l)) = 2 * LENGTH l`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LENGTH_CRY_JOIN_MAP THEN
  REWRITE_TAC[LENGTH; ARITH]);;

let EL_CRY_JOIN_PAIRS = prove
 (`!(f:A->B) g l i.
        i < 2 * LENGTH l
        ==> EL i (cry_join(MAP (\x. [f x; g x]) l)) =
            if EVEN i then f(EL (i DIV 2) l) else g(EL (i DIV 2) l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:A. [(f:A->B) x; g x]`; `2`; `l:A list`; `i:num`]
         EL_CRY_JOIN_MAP) THEN
  ASM_REWRITE_TAC[LENGTH; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EVEN_MOD] THEN
  SUBGOAL_THEN `i MOD 2 = 0 \/ i MOD 2 = 1` MP_TAC THENL
   [MP_TAC(SPECL [`i:num`; `2`] MOD_LT_EQ) THEN ARITH_TAC;
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[ONE; EL; HD; TL]]);;

let CRY_ZETA_EXP = prove
 (`!i. i < 256
       ==> val(word_add (word_mul (word 2) (cry_BitRev7 (word i)))
                        (word 1):byte) =
           2 * bitreverse7 i + 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD; VAL_CRY_BITREV7;
              DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPEC `i:num` BITREVERSE7_BOUND) THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `b < 128 ==> 2 * b < 256`;
           ARITH_RULE `b < 128 ==> 2 * b + 1 < 256`]);;

let CRY_ZETA_TERM = prove
 (`!i j. i < 256 /\ j < 256
         ==> ring_pow (integer_mod_ring 3329) (&17)
              (val(word_mul (word_add (word_mul (word 2)
                                                (cry_BitRev7 (word i)))
                                      (word 1))
                            (word j))) =
             (&17 pow ((2 * bitreverse7 i + 1) * j)) rem &3329`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_MUL] THEN ASM_SIMP_TAC[CRY_ZETA_EXP] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ZETA_POW_MOD_256]);;

let CRY_NAIVENTT = prove
 (`!f. LENGTH f = 256
       ==> LENGTH(cry_NaiveNTT f) = 256 /\
           !k. k < 256
               ==> EL k (cry_NaiveNTT f) =
                   mlkem_ntt (mlkem_poly (\i. EL i f)) k`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[cry_NaiveNTT; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_CRY_JOIN_PAIRS; LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_CRY_JOIN_PAIRS o lhand o snd) THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `k DIV 2 < 128` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE; ARITH;
               ARITH_RULE `k < 128 ==> k < (127 + 1) - 0`] THEN
  REWRITE_TAC[ADD_CLAUSES; CRY_ZSUM_MAP_RANGE] THEN
  SIMP_TAC[MLKEM_NTT_FORWARD; MLKEM_POLY_IN_RQ; COEFF_MLKEM_POLY] THEN
  ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o REWRITE_RULE[EVEN_MOD; NOT_EVEN; ODD_MOD]) THEN
  REWRITE_TAC[INT_REM_EQ; ADD_CLAUSES] THEN MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[CRY_ZETA_TERM; ARITH_RULE `j <= 127 ==> j < 256`;
               ARITH_RULE `k < 128 ==> k < 256`] THEN
  REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `j <= 127 ==> j < 256`;
               ARITH_RULE `j <= 127 ==> 2 * j < 256`;
               ARITH_RULE `j <= 127 ==> 2 * j + 1 < 256`] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The fast NTT (fast_nttl, ct_butterfly). By induction on the level, entry  *)
(* t of fast_nttl (n + 2) v (2^(6-n) + K) is entry t MOD 2 of the residue of *)
(* v modulo X^2 - zeta^(2 * BitRev7 i + 1) with i = K * 2^(n+1) + t DIV 2,   *)
(* written as a sum (CRY_FAST_NTTL). Two finite facts are proved by          *)
(* evaluation: the table zeta_expc, and an identity about BitRev7.           *)
(* ------------------------------------------------------------------------- *)

let ISUM_LT_ADD_SPLIT = prove
 (`!f m n. isum {t | t < m + n} f =
           isum {t | t < m} f + isum {t | t < n} (\t. f(m + t))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; ISUM_CLAUSES;
              INT_ADD_RID] THEN
  REWRITE_TAC[NUMSEG_CLAUSES_LT] THEN
  SIMP_TAC[ISUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  ASM_REWRITE_TAC[INT_ADD_AC]);;

let CRY_SPLIT_2 = prove
 (`!(l:A list) n.
        LENGTH l = 2 * n /\ ~(n = 0)
        ==> LENGTH(EL 0 (cry_split 2 l)) = n /\
            LENGTH(EL 1 (cry_split 2 l)) = n /\
            (!i. i < n ==> EL i (EL 0 (cry_split 2 l)) = EL i l) /\
            (!i. i < n ==> EL i (EL 1 (cry_split 2 l)) = EL (n + i) l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cry_split] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(2 * n) DIV 2 = n /\ (2 * n) DIV n = 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_CRY_GROUPBY; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; ARITH;
                 MULT_CLAUSES; ADD_CLAUSES]]);;

let LENGTH_CRY_CT_BUTTERFLY = prove
 (`!hm v z. LENGTH(cry_ct_butterfly hm v z) = 2 * 2 EXP hm`,
  REWRITE_TAC[cry_ct_butterfly; LET_DEF; LET_END_DEF; LENGTH_APPEND;
              LENGTH_LIST_OF_SEQ] THEN
  ARITH_TAC);;

let EL_CRY_CT_BUTTERFLY = prove
 (`!hm v z x.
        x < 2 * 2 EXP hm
        ==> EL x (cry_ct_butterfly hm v z) =
            if x < 2 EXP hm
            then (EL x v + z * EL (x + 2 EXP hm) v) rem &3329
            else (EL (x - 2 EXP hm) v - z * EL x v) rem &3329`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_ct_butterfly; LET_DEF; LET_END_DEF; EL_APPEND;
              LENGTH_LIST_OF_SEQ] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; INTEGER_MOD_RING_CLAUSES;
               ARITH_RULE `~(x < h) /\ x < 2 * h ==> x - h < h`;
               ARITH_RULE `~(x < h) ==> x - h + h = x`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let CRY_BITREVERSE7_CLAUSES = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [bitreverse7] THENC WORD_REDUCE_CONV)
 (map (curry mk_comb `bitreverse7` o mk_small_numeral) (0--127)));;

let CRY_ZETA_EXPC = prove
 (`!k. k < 128 ==> EL k cry_zeta_expc = (&17 pow bitreverse7 k) rem &3329`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[cry_zeta_expc] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[CRY_BITREVERSE7_CLAUSES] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let BITREVERSE7_SPLIT = prove
 (`!j K u. j <= 6 /\ K < 2 EXP (6 - j) /\ u < 2 EXP (j + 1)
           ==> ((2 * bitreverse7(K * 2 EXP (j + 1) + u) + 1) * 2 EXP j)
               MOD 256 =
               (bitreverse7(2 EXP (6 - j) + K) + 128 * (u DIV 2 EXP j))
               MOD 256`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM;
              ARITH_RULE `j <= 6 <=> j < 7`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CRY_BITREVERSE7_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZETA_POW_SPLIT = prove
 (`!j K u. j <= 6 /\ K < 2 EXP (6 - j) /\ u < 2 EXP (j + 1)
           ==> (&17 pow ((2 * bitreverse7(K * 2 EXP (j + 1) + u) + 1) *
                         2 EXP j)) rem &3329 =
               (if u < 2 EXP j then &17 pow bitreverse7(2 EXP (6 - j) + K)
                else --(&17 pow bitreverse7(2 EXP (6 - j) + K))) rem &3329`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ZETA_POW_MOD_256] THEN
  ASM_SIMP_TAC[BITREVERSE7_SPLIT] THEN REWRITE_TAC[ZETA_POW_MOD_256] THEN
  SUBGOAL_THEN `u DIV 2 EXP j = if u < 2 EXP j then 0 else 1`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[DIV_LT] THEN MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `u - 2 EXP j` THEN
    UNDISCH_TAC `u < 2 EXP (j + 1)` THEN REWRITE_TAC[EXP_ADD] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[INT_POW_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a:int == -- &1) (mod n) ==> (x * a == --x) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let LENGTH_CRY_FAST_NTTL = prove
 (`!n v k. LENGTH v = 2 EXP (n + 2)
           ==> LENGTH(cry_fast_nttl (n + 2) v k) = 2 EXP (n + 2)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[cry_fast_nttl] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n + 2 <= 2)`; ARITH_RULE `0 + 2 <= 2`] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH_APPEND;
              ARITH_RULE `(SUC n + 2) - 1 = n + 2`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LENGTH_CRY_CT_BUTTERFLY] THENL
   [CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(ISPECL
     [`cry_ct_butterfly (n + 2) v (EL (val(k:byte)) cry_zeta_expc)`;
      `2 EXP (n + 2)`] CRY_SPLIT_2) THEN
    REWRITE_TAC[LENGTH_CRY_CT_BUTTERFLY; EXP_EQ_0; ARITH_EQ] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[ADD_CLAUSES; EXP] THEN
    ARITH_TAC]);;

let ISUM_LT_2 = prove
 (`!f. isum {y | y < 2} f = f 0 + f 1`,
  REWRITE_TAC[TWO; ISUM_LT_SUC_LEFT; CONJUNCT1 LT; EMPTY_GSPEC;
              ISUM_CLAUSES; INT_ADD_RID; ONE]);;

let INT_CONG_REM_SELF = prove
 (`!x n:int. (x rem n == x) (mod n)`,
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

let CT_CONG_PLUS = INTEGER_RULE
 `!a b z Z n:int. (Z == z) (mod n) ==> (a + z * b == a + b * Z) (mod n)`
and CT_CONG_MINUS = INTEGER_RULE
 `!a b z Z n:int. (Z == --z) (mod n) ==> (a - z * b == a + b * Z) (mod n)`;;

let CT_TERM_CONG_PLUS = prove
 (`!a b zr z0 zp w n:int.
        (zr == z0) (mod n) /\ (zp == z0) (mod n)
        ==> ((a + zr * b) rem n * w == a * w + b * (zp * w)) (mod n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a + zr * b:int`; `n:int`] INT_CONG_REM_SELF) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN INTEGER_TAC);;

let CT_TERM_CONG_MINUS = prove
 (`!a b zr z0 zp w n:int.
        (zr == z0) (mod n) /\ (zp == --z0) (mod n)
        ==> ((a - zr * b) rem n * w == a * w + b * (zp * w)) (mod n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a - zr * b:int`; `n:int`] INT_CONG_REM_SELF) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN INTEGER_TAC);;

let CRY_FAST_NTTL = prove
 (`!n v K t.
     n <= 6 /\ LENGTH v = 2 EXP (n + 2) /\ K < 2 EXP (6 - n) /\
     t < 2 EXP (n + 2)
     ==> EL t (cry_fast_nttl (n + 2) v (word(2 EXP (6 - n) + K))) =
         isum {y | y < 2 EXP (n + 1)}
          (\y. EL (2 * y + t MOD 2) v *
               &17 pow ((2 * bitreverse7(K * 2 EXP (n + 1) + t DIV 2) + 1) *
                        y)) rem &3329`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[cry_fast_nttl] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n + 2 <= 2)`; ARITH_RULE `0 + 2 <= 2`] THENL
   [RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val(word(64 + K):byte) = 64 + K` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[EL_CRY_CT_BUTTERFLY; ARITH; CRY_ZETA_EXPC;
                 ARITH_RULE `K < 64 ==> 64 + K < 128`] THEN
    REWRITE_TAC[ISUM_LT_2; MULT_CLAUSES; ADD_CLAUSES; INT_POW;
                INT_MUL_RID] THEN
    MP_TAC(SPECL [`0`; `K:num`; `t DIV 2`] ZETA_POW_SPLIT) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
    SUBGOAL_THEN `t = 0 \/ t = 1 \/ t = 2 \/ t = 3` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
    FIRST [MATCH_ACCEPT_TAC CT_CONG_PLUS; MATCH_ACCEPT_TAC CT_CONG_MINUS];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; ARITH_RULE `(SUC n + 2) - 1 = n + 2`] THEN
  SUBGOAL_THEN
   `2 EXP (6 - n) = 2 * 2 EXP (6 - SUC n) /\ 2 EXP (6 - SUC n) <= 32 /\
    2 EXP (SUC n + 1) = 2 * 2 EXP (n + 1) /\
    2 EXP (SUC n + 2) = 4 * 2 EXP (n + 1) /\
    2 EXP (n + 2) = 2 * 2 EXP (n + 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `SUC n <= 6 ==> 6 - n = SUC(6 - SUC n)`; EXP];
      TRANS_TAC LE_TRANS `2 EXP 5` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_EXP] THEN ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
      REWRITE_TAC[ADD_CLAUSES; EXP];
      REWRITE_TAC[ARITH_RULE `SUC n + 2 = SUC(SUC(n + 1))`; EXP] THEN
      ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; EXP]];
    ALL_TAC] THEN
  ABBREV_TAC `P = 2 EXP (6 - SUC n)` THEN
  ABBREV_TAC `H = 2 EXP (n + 1)` THEN
  SUBGOAL_THEN `val(word(P + K):byte) = P + K` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `bf = cry_ct_butterfly (n + 2) v (EL (P + K) cry_zeta_expc)` THEN
  MP_TAC(ISPECL [`bf:int list`; `2 * H`] CRY_SPLIT_2) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "bf" THEN ASM_REWRITE_TAC[LENGTH_CRY_CT_BUTTERFLY] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `s0:int list = EL 0 (cry_split 2 bf)` THEN
  ABBREV_TAC `s1:int list = EL 1 (cry_split 2 bf)` THEN
  STRIP_TAC THEN REWRITE_TAC[EL_APPEND] THEN
  MP_TAC(SPECL [`n:num`; `s0:int list`; `word((P + K) * 2):byte`]
         LENGTH_CRY_FAST_NTTL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(P + K) * 2 = 2 * P + 2 * K`] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s0:int list`; `2 * K`; `t:num`] o
                check (is_forall o concl)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `{y | y < 2 * H} = {y | y < H + H}` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * H = H + H`]; ALL_TAC] THEN
    REWRITE_TAC[ISUM_LT_ADD_SPLIT; INT_REM_EQ] THEN
    SIMP_TAC[GSYM ISUM_ADD; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC INT_CONG_ISUM THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `(2 * K) * H = K * 2 * H`;
                ARITH_RULE `2 * (H + y) + r = (2 * y + r) + 2 * H`;
                LEFT_ADD_DISTRIB; INT_POW_ADD] THEN
    SUBGOAL_THEN `2 * y + t MOD 2 < 2 * H` ASSUME_TAC THENL
     [MP_TAC(SPECL [`t:num`; `2`] MOD_LT_EQ) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_THEN `cry_ct_butterfly (n + 2) v (EL (P + K) cry_zeta_expc) = bf`
     (SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[EL_CRY_CT_BUTTERFLY;
                 ARITH_RULE `x < 2 * H ==> x < 2 * 2 * H`; CRY_ZETA_EXPC;
                 ARITH_RULE `K < P /\ P <= 32 ==> P + K < 128`] THEN
    MATCH_MP_TAC CT_TERM_CONG_PLUS THEN
    EXISTS_TAC `(&17:int) pow bitreverse7 (P + K)` THEN
    REWRITE_TAC[INT_CONG_REM_SELF] THEN
    MP_TAC(SPECL [`n + 1`; `K:num`; `t DIV 2`] ZETA_POW_SPLIT) THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`;
                ARITH_RULE `6 - (n + 1) = 6 - SUC n`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[INT_REM_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t'. t = 2 * H + t'` (X_CHOOSE_THEN `t':num` SUBST_ALL_TAC)
  THENL [EXISTS_TAC `t - 2 * H` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t' < 2 * H` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(2 * H + t') MOD 2 = t' MOD 2 /\ (2 * H + t') DIV 2 = H + t' DIV 2`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `2 * H + t' = H * 2 + t'`] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB2;
              ARITH_RULE `(P + K) * 2 + 1 = 2 * P + (2 * K + 1)`] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s1:int list`; `2 * K + 1`; `t':num`] o
              check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(2 * K + 1) * H + x = K * 2 * H + (H + x)`] THEN
  SUBGOAL_THEN `{y | y < 2 * H} = {y | y < H + H}` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * H = H + H`]; ALL_TAC] THEN
  REWRITE_TAC[ISUM_LT_ADD_SPLIT; INT_REM_EQ] THEN
  SIMP_TAC[GSYM ISUM_ADD; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * (H + y) + r = 2 * H + (2 * y + r)`;
              LEFT_ADD_DISTRIB; INT_POW_ADD] THEN
  SUBGOAL_THEN `2 * y + t' MOD 2 < 2 * H` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t':num`; `2`] MOD_LT_EQ) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_THEN `cry_ct_butterfly (n + 2) v (EL (P + K) cry_zeta_expc) = bf`
   (SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[EL_CRY_CT_BUTTERFLY;
               ARITH_RULE `x < 2 * H ==> 2 * H + x < 2 * 2 * H`;
               ARITH_RULE `~(2 * H + x < 2 * H)`; ADD_SUB2;
               CRY_ZETA_EXPC;
               ARITH_RULE `K < P /\ P <= 32 ==> P + K < 128`] THEN
  MATCH_MP_TAC CT_TERM_CONG_MINUS THEN
  EXISTS_TAC `(&17:int) pow bitreverse7 (P + K)` THEN
  REWRITE_TAC[INT_CONG_REM_SELF] THEN
  MP_TAC(SPECL [`n + 1`; `K:num`; `H + t' DIV 2`] ZETA_POW_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`;
              ARITH_RULE `6 - (n + 1) = 6 - SUC n`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(H + x < H)`] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `x < H ==> H + x < 2 * H`; RDIV_LT_EQ;
                 ARITH_EQ] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[INT_REM_EQ]]);;

let CRY_FAST_NTT = prove
 (`!f. LENGTH f = 256
       ==> LENGTH(cry_fast_ntt f) = 256 /\
           !k. k < 256
               ==> EL k (cry_fast_ntt f) =
                   mlkem_ntt (mlkem_poly (\i. EL i f)) k`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cry_fast_ntt] THEN
  MP_TAC(SPECL [`6`; `f:int list`; `word 1:byte`] LENGTH_CRY_FAST_NTTL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`6`; `f:int list`; `0`; `k:num`] CRY_FAST_NTTL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[MLKEM_NTT_FORWARD; MLKEM_POLY_IN_RQ; COEFF_MLKEM_POLY] THEN
  SUBGOAL_THEN `{y | y < 128} = 0..127` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `2 * j + k MOD 2 < 256` (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a rem n == a) (mod n) ==> (a * w == a rem n * w) (mod n)`) THEN
  REWRITE_TAC[INT_CONG_REM_SELF]);;

(* The property naive_fast_ntt_equiv stated (and checked) in the Cryptol     *)
(* specification.                                                            *)

let CRY_NAIVE_FAST_NTT_EQUIV = prove
 (`!f. LENGTH f = 256 ==> cry_NaiveNTT f = cry_fast_ntt f`,
  SIMP_TAC[LIST_EQ; CRY_NAIVENTT; CRY_FAST_NTT]);;

(* ------------------------------------------------------------------------- *)
(* MultiplyNTTs (exactly fips203_multiply_ntts, with no assumptions), G and  *)
(* PRF.                                                                      *)
(* ------------------------------------------------------------------------- *)

let CRY_MULTIPLYNTTS = prove
 (`!f g. LENGTH(cry_MultiplyNTTs f g) = 256 /\
         !n. n < 256
             ==> EL n (cry_MultiplyNTTs f g) =
                 fips203_multiply_ntts (\i. EL i f) (\i. EL i g) n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cry_MultiplyNTTs; cry_BaseCaseMultiply; LET_DEF;
              LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_CRY_JOIN_PAIRS; LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_CRY_JOIN_PAIRS o lhand o snd) THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `n DIV 2 < 128` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE; ARITH;
               ARITH_RULE `k < 128 ==> k < (127 + 1) - 0`] THEN
  ASM_SIMP_TAC[CRY_ZETA_EXP; ARITH_RULE `k < 128 ==> k < 256`;
               ADD_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `k < 128 ==> k < 256`;
               ARITH_RULE `k < 128 ==> 2 * k < 256`;
               ARITH_RULE `k < 128 ==> 2 * k + 1 < 256`] THEN
  REWRITE_TAC[fips203_multiply_ntts; mlkem_zq] THEN
  ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
                  REWRITE_RULE[EVEN_EXISTS]) THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ];
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
                  REWRITE_RULE[NOT_EVEN; ODD_EXISTS]) THEN
    SUBGOAL_THEN `SUC(2 * m) DIV 2 = m` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1` THEN ARITH_TAC;
      REWRITE_TAC[SUC_SUB1; ADD1; ADD_SUB]]]);;

let CRY_PRF = prove
 (`cry_PRF = mlkem_prf`,
  REWRITE_TAC[FUN_EQ_THM; cry_PRF; mlkem_prf]);;

let CRY_G = prove
 (`!c. cry_G c = mlkem_g c`,
  GEN_TAC THEN REWRITE_TAC[cry_G; mlkem_g; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPECL [`sha3_512 c`; `32`] CRY_SPLIT_2) THEN
  REWRITE_TAC[sha3_512; LENGTH_LIST_OF_SEQ; ARITH] THEN
  STRIP_TAC THEN REWRITE_TAC[PAIR_EQ; mlkem_slice] THEN
  ASM_SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Encoding vectors of polynomials (ByteEncode12_Vec), via splitting         *)
(* mlkem_encode at byte boundaries.                                          *)
(* ------------------------------------------------------------------------- *)

let ITLIST_APPEND_ACC = prove
 (`!l (x:A list). ITLIST APPEND l x = APPEND (ITLIST APPEND l []) x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; APPEND] THEN GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[APPEND_ASSOC]);;

let CRY_JOIN_APPEND = prove
 (`!l1 l2:(A list) list.
        cry_join (APPEND l1 l2) = APPEND (cry_join l1) (cry_join l2)`,
  REWRITE_TAC[cry_join; ITLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ITLIST_APPEND_ACC] THEN REWRITE_TAC[APPEND_NIL]);;

let BYTELIST_OF_NUM_ADD = prove
 (`!a b x y. x < 256 EXP a
             ==> bytelist_of_num (a + b) (x + 256 EXP a * y) =
                 APPEND (bytelist_of_num a x) (bytelist_of_num b y)`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; EXP; MULT_CLAUSES; bytelist_of_num; APPEND] THEN
  REPEAT STRIP_TAC THENL [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `x + (256 * e) * y = (e * y) * 256 + x`] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; CONS_11] THEN
  SUBGOAL_THEN `256 EXP a * y + x DIV 256 = x DIV 256 + 256 EXP a * y`
  SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]);;

let MLKEM_ENCODE_APPEND = prove
 (`!d m n f. 8 divides (d * m)
             ==> mlkem_encode d (m + n) f =
                 APPEND (mlkem_encode d m f)
                        (mlkem_encode d n (\i. f(m + i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  REWRITE_TAC[mlkem_encode; NSUM_LT_ADD_SPLIT] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `8 * c + x = c * 8 + x`] THEN
  SIMP_TAC[DIV_MULT_ADD; DIV_MULT; ARITH_EQ] THEN
  REWRITE_TAC[EXP_MULT; ARITH; MULT_ASSOC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(a:num) * b * c = b * a * c`] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; NSUM_LMUL] THEN
  SUBGOAL_THEN
   `nsum {i | i < n}
     (\i. num_of_int (f (m + i) rem &2 pow d) * 256 EXP c * 2 EXP d EXP i) =
    256 EXP c *
    nsum {i | i < n} (\i. num_of_int (f (m + i) rem &2 pow d) * 2 EXP d EXP i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM NSUM_LMUL] THEN AP_TERM_TAC THEN ABS_TAC THEN
    REWRITE_TAC[MULT_AC];
    MATCH_MP_TAC BYTELIST_OF_NUM_ADD] THEN
  SUBGOAL_THEN `256 EXP c = (2 EXP d) EXP m` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIGITSUM_BOUND THEN
  REWRITE_TAC[MLKEM_ENCODE_DIGIT]);;

let MLKEM_ENCODE_BLOCKS = prove
 (`!d k (ff:num->num->int).
        8 divides (d * 256)
        ==> mlkem_encode d (256 * k) (\n. ff (n DIV 256) (n MOD 256)) =
            cry_join (list_of_seq (\i. mlkem_encode d 256 (ff i)) k)`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; CRY_JOIN_CLAUSES; mlkem_encode] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[bytelist_of_num];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `256 * SUC k = 256 * k + 256`; list_of_seq;
              CRY_JOIN_APPEND; CRY_JOIN_CLAUSES; APPEND_NIL] THEN
  MP_TAC(ISPECL [`d:num`; `256 * k`; `256`;
                 `\n. (ff:num->num->int) (n DIV 256) (n MOD 256)`]
         MLKEM_ENCODE_APPEND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `d * 256 * k = (d * 256) * k`] THEN
    ASM_SIMP_TAC[DIVIDES_RMUL];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `256 * k + i = k * 256 + i`] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ;
               ADD_CLAUSES]);;

let CRY_BYTEENCODE12_VEC = prove
 (`!Fv k (gg:num->num->int).
        LENGTH Fv = k /\
        (!i. i < k ==> LENGTH(EL i Fv) = 256) /\
        (!i n. i < k /\ n < 256
               ==> EL n (EL i Fv) = gg i n /\ &0 <= gg i n /\ gg i n < &4096)
        ==> cry_ByteEncode12_Vec Fv =
            mlkem_encode 12 (256 * k) (\n. gg (n DIV 256) (n MOD 256))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`12`; `k:num`; `gg:num->num->int`] MLKEM_ENCODE_BLOCKS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[divides] THEN EXISTS_TAC `384` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[cry_ByteEncode12_Vec] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [LIST_EQ] THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRY_BYTEENCODE12 o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MLKEM_ENCODE_EQ THEN ASM_SIMP_TAC[]);;

let CRY_BYTEENCODE12_VEC_ALT = prove
 (`!Fv k (G:num->int).
        LENGTH Fv = k /\
        (!i. i < k ==> LENGTH(EL i Fv) = 256) /\
        (!i n. i < k /\ n < 256
               ==> EL n (EL i Fv) = G(256 * i + n) /\
                   &0 <= G(256 * i + n) /\ G(256 * i + n) < &4096)
        ==> cry_ByteEncode12_Vec Fv = mlkem_encode 12 (256 * k) G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Fv:(int list) list`; `k:num`;
                 `\i n. (G:num->int)(256 * i + n)`] CRY_BYTEENCODE12_VEC) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MLKEM_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sums of polynomials and the dot products (dotVecVec, dotMatVec).          *)
(* ------------------------------------------------------------------------- *)

let CRY_ZSUM_CLAUSES = prove
 (`cry_zsum [] = &0 /\
   !x l. cry_zsum (CONS x l) =
         ring_add (integer_mod_ring 3329) x (cry_zsum l)`,
  REWRITE_TAC[cry_zsum; ITLIST; INTEGER_MOD_RING_CLAUSES]);;

let LENGTH_ITLIST_TQ_ADD = prove
 (`!L. ALL (\x. LENGTH x = 256) L
       ==> LENGTH(ITLIST cry_tq_add L cry_tq_zero) = 256`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; ALL] THENL
   [REWRITE_TAC[cry_tq_zero; LENGTH_LIST_OF_SEQ];
    STRIP_TAC THEN REWRITE_TAC[cry_tq_add] THEN ASM_SIMP_TAC[LENGTH_MAP2]]);;

let EL_ITLIST_TQ_ADD = prove
 (`!L m. ALL (\x. LENGTH x = 256) L /\ m < 256
         ==> EL m (ITLIST cry_tq_add L cry_tq_zero) = cry_zsum (MAP (EL m) L)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; ALL; MAP; CRY_ZSUM_CLAUSES] THENL
   [SIMP_TAC[cry_tq_zero; EL_LIST_OF_SEQ];
    REPEAT STRIP_TAC THEN REWRITE_TAC[cry_tq_add] THEN
    ASM_SIMP_TAC[EL_MAP2; LENGTH_ITLIST_TQ_ADD]]);;

let CRY_DOTVECVEC = prove
 (`!v1 v2 k.
        LENGTH v1 = k /\ LENGTH v2 = k
        ==> LENGTH(cry_dotVecVec v1 v2) = 256 /\
            !m. m < 256
                ==> EL m (cry_dotVecVec v1 v2) =
                    isum {j | j < k}
                     (\j. EL m (cry_MultiplyNTTs (EL j v1) (EL j v2))) rem
                    &3329`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cry_dotVecVec] THEN
  SUBGOAL_THEN
   `MAP2 cry_MultiplyNTTs v1 v2 =
    list_of_seq (\j. cry_MultiplyNTTs (EL j v1) (EL j v2)) k`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [LIST_EQ] THEN
    ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_LIST_OF_SEQ; EL_MAP2; EL_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (\x. LENGTH x = 256)
        (list_of_seq (\j. cry_MultiplyNTTs (EL j v1) (EL j v2)) k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[EL_LIST_OF_SEQ; CRY_MULTIPLYNTTS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_ITLIST_TQ_ADD; EL_ITLIST_TQ_ADD] THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ; CRY_ZSUM_REM; ITLIST_ADD_LIST_OF_SEQ_INT;
              o_DEF]);;

let CRY_DOTVECVEC_RANGE = prove
 (`!(f:num->int list) g k.
        ~(k = 0)
        ==> LENGTH(cry_dotVecVec (MAP f (cry_range 0 (k - 1)))
                                 (MAP g (cry_range 0 (k - 1)))) = 256 /\
            !m. m < 256
                ==> EL m (cry_dotVecVec (MAP f (cry_range 0 (k - 1)))
                                        (MAP g (cry_range 0 (k - 1)))) =
                    isum {j | j < k}
                     (\j. EL m (cry_MultiplyNTTs (f j) (g j))) rem &3329`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`MAP (f:num->int list) (cry_range 0 (k - 1))`;
                 `MAP (g:num->int list) (cry_range 0 (k - 1))`; `k:num`]
         CRY_DOTVECVEC) THEN
  ASM_SIMP_TAC[LENGTH_MAP; LENGTH_CRY_RANGE;
               ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`] THEN
  STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ISUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE; ADD_CLAUSES;
               ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`]);;

(* ------------------------------------------------------------------------- *)
(* K-PKE KeyGen. The hypothesis on SampleNTT is that of KPKE_KEYGEN_FIPS in  *)
(* common/fips203_theory.ml, which the proof reuses.                         *)
(* ------------------------------------------------------------------------- *)

let CRY_NTT_CBD = prove
 (`!eta B. LENGTH B = 64 * eta /\ ~(eta = 0)
           ==> LENGTH(cry_NTT (cry_SamplePolyCBD eta B)) = 256 /\
               !n. n < 256
                   ==> EL n (cry_NTT (cry_SamplePolyCBD eta B)) =
                       mlkem_ntt (mlkem_cbd eta B) n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CRY_SAMPLEPOLYCBD) THEN
  ASM_SIMP_TAC[cry_NTT; CRY_FAST_NTT]);;

let FIPS203_MULTIPLY_NTTS_IN_ZQ = prove
 (`!a b n. fips203_multiply_ntts a b n IN ring_carrier mlkem_zq`,
  REWRITE_TAC[fips203_multiply_ntts; IN_MLKEM_ZQ] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[mlkem_zq; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLKEM_NTT_BOUND = prove
 (`!f k. f IN ring_carrier mlkem_rq
         ==> &0 <= mlkem_ntt f k /\ mlkem_ntt f k < &3329`,
  SIMP_TAC[MLKEM_NTT_FORWARD; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let LENGTH_MLKEM_PRF = prove
 (`!eta s b. LENGTH(mlkem_prf eta s b) = 64 * eta`,
  REWRITE_TAC[mlkem_prf; LENGTH_LIST_OF_SEQ]);;

let DIV_MOD_256_BLOCK = prove
 (`!i n. n < 256 ==> (256 * i + n) DIV 256 = i /\ (256 * i + n) MOD 256 = n`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `256 * i + n = i * 256 + n`] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ;
               ADD_CLAUSES]);;

let RING_ADD_MLKEM_ZQ_BOUND = prove
 (`!x y. &0 <= ring_add mlkem_zq x y /\ ring_add mlkem_zq x y < &4096`,
  REWRITE_TAC[mlkem_zq; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[INT_REM_POS_EQ] THEN CONV_TAC INT_REDUCE_CONV THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC INT_LT_TRANS THEN
  EXISTS_TAC `&3329:int` THEN REWRITE_TAC[INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let RING_SUM_MLKEM_ZQ_MULTIPLY = prove
 (`!s a b n.
        FINITE s
        ==> ring_sum mlkem_zq s (\j. fips203_multiply_ntts (a j) (b j) n) =
            isum s (\j. fips203_multiply_ntts (a j) (b j) n) rem &3329`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_zq] THEN
  MATCH_MP_TAC RING_SUM_INTEGER_MOD_RING THEN
  ASM_REWRITE_TAC[ARITH_EQ; GSYM mlkem_zq; FIPS203_MULTIPLY_NTTS_IN_ZQ]);;

let CRY_K_PKE_KEYGEN = prove
 (`!k eta1 eta2 du dv d.
        ~(k = 0) /\ ~(eta1 = 0) /\
        (!i j n. i < k /\ j < k /\ n < 256
                 ==> mlkem_sample_ntt
                      (APPEND (FST(mlkem_g(APPEND d [word k])))
                              [word j; word i]) n < &3329)
        ==> cry_K_PKE_KeyGen k eta1 d = kpke_keygen (k,eta1,eta2,du,dv) d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[KPKE_KEYGEN_FIPS] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  REWRITE_TAC[cry_K_PKE_KeyGen; cry_NTT_Vec; cry_vec_add; CRY_G; CRY_PRF] THEN
  SPEC_TAC(`mlkem_g (APPEND d [word k])`,`p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`rho:byte list`; `sigma:byte list`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST] THEN
  DISCH_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  SUBGOAL_THEN `(k - 1 + 1) - 0 = k /\ (2 * k - 1 + 1) - k = k`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CRY_BYTEENCODE12_VEC_ALT THEN
  REWRITE_TAC[cry_dotMatVec] THEN
  ASM_SIMP_TAC[LENGTH_MAP; LENGTH_MAP2; LENGTH_CRY_RANGE; EL_MAP; EL_MAP2;
               EL_CRY_RANGE; ADD_CLAUSES; DIV_MOD_256_BLOCK] THEN
  MP_TAC(GEN `b:byte` (SPECL [`eta1:num`; `mlkem_prf eta1 sigma b`]
         CRY_NTT_CBD)) THEN
  ASM_REWRITE_TAC[LENGTH_MLKEM_PRF; FORALL_AND_THM] THEN STRIP_TAC THENL
   [REWRITE_TAC[RING_ADD_MLKEM_ZQ_BOUND; GSYM MAP_o] THEN
    ASM_SIMP_TAC[CRY_DOTVECVEC_RANGE; cry_tq_add; LENGTH_MAP2; EL_MAP2] THEN
    REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `i:num` THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    SIMP_TAC[RING_SUM_MLKEM_ZQ_MULTIPLY; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[mlkem_zq] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CRY_MULTIPLYNTTS; APPEND] THEN
    MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN
    ASM_SIMP_TAC[CRY_SAMPLENTT_EQ];
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`mlkem_cbd eta1 (mlkem_prf eta1 sigma (word i))`; `n:num`]
           MLKEM_NTT_BOUND) THEN
    REWRITE_TAC[MLKEM_CBD_IN_RQ] THEN INT_ARITH_TAC]);;

(* The same with the hypothesis that each SampleNTT terminates, i.e. that    *)
(* each XOF stream has infinitely many 12-bit fields < q.                    *)

let CRY_K_PKE_KEYGEN_INFINITE = prove
 (`!k eta1 eta2 du dv d.
        ~(k = 0) /\ ~(eta1 = 0) /\
        (!i j. i < k /\ j < k
               ==> INFINITE
                    {t | mlkem_xof_field
                          (mlkem_xof (APPEND (FST(mlkem_g(APPEND d [word k])))
                                             [word j; word i])) t < 3329})
        ==> cry_K_PKE_KeyGen k eta1 d = kpke_keygen (k,eta1,eta2,du,dv) d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CRY_K_PKE_KEYGEN THEN
  ASM_SIMP_TAC[MLKEM_SAMPLE_NTT_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* The inverse NTT. By induction on the level, fast_invnttl undoes fast_nttl *)
(* up to a factor 2 at each level (CRY_FAST_INVNTTL_NTTL), using that the    *)
(* zetas of the two butterflies multiply to -1 (an evaluation over the 127   *)
(* index pairs). So fast_invntt inverts fast_ntt, the Cryptol property       *)
(* fast_ntt_inverts, and it is mlkem_ntt_inv. NaiveNTTInv is mlkem_ntt_inv   *)
(* by the formula MLKEM_NTT_INV_COEFF, reindexed by the bit reversal.        *)
(* ------------------------------------------------------------------------- *)

let LENGTH_CRY_GS_BUTTERFLY = prove
 (`!hm v z. LENGTH(cry_gs_butterfly hm v z) = 2 * 2 EXP hm`,
  REWRITE_TAC[cry_gs_butterfly; LET_DEF; LET_END_DEF; LENGTH_APPEND;
              LENGTH_LIST_OF_SEQ] THEN
  ARITH_TAC);;

let EL_CRY_GS_BUTTERFLY = prove
 (`!hm v z x.
        x < 2 * 2 EXP hm
        ==> EL x (cry_gs_butterfly hm v z) =
            if x < 2 EXP hm
            then (EL x v + EL (x + 2 EXP hm) v) rem &3329
            else (z * (EL x v - EL (x - 2 EXP hm) v)) rem &3329`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_gs_butterfly; LET_DEF; LET_END_DEF; EL_APPEND;
              LENGTH_LIST_OF_SEQ] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; INTEGER_MOD_RING_CLAUSES;
               ARITH_RULE `~(x < h) /\ x < 2 * h ==> x - h < h`;
               ARITH_RULE `~(x < h) ==> x - h + h = x`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let LENGTH_CRY_FAST_INVNTTL = prove
 (`!lv v k. 2 <= lv ==> LENGTH(cry_fast_invnttl lv v k) = 2 EXP lv`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[cry_fast_invnttl] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_CRY_GS_BUTTERFLY; GSYM(CONJUNCT2 EXP)] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let BITREVERSE7_MIRROR = prove
 (`!n K. n <= 6 /\ K < 2 EXP (6 - n)
         ==> bitreverse7(2 EXP (6 - n) + K) +
             bitreverse7(2 EXP (6 - n) + (2 EXP (6 - n) - 1 - K)) = 128`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM;
              ARITH_RULE `n <= 6 <=> n < 7`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CRY_BITREVERSE7_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZETA_EXPC_MIRROR = prove
 (`!n K. n <= 6 /\ K < 2 EXP (6 - n)
         ==> (EL (2 EXP (6 - n) + K) cry_zeta_expc *
              EL (2 EXP (6 - n) + (2 EXP (6 - n) - 1 - K)) cry_zeta_expc ==
              -- &1) (mod &3329)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (6 - n) <= 64` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `2 EXP 6` THEN
    CONJ_TAC THENL [REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
                    CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CRY_ZETA_EXPC; ARITH_RULE
   `p <= 64 /\ K < p ==> p + K < 128 /\ p + (p - 1 - K) < 128`] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[GSYM INT_POW_ADD] THEN ASM_SIMP_TAC[BITREVERSE7_MIRROR] THEN
  CONV_TAC INT_REDUCE_CONV);;

let INTEGER_GOAL_TAC:tactic = W(fun (_,w) -> ACCEPT_TAC(INTEGER_RULE w));;

let GS_CT_UPPER1 = INTEGER_RULE
 `!a b w z n:int.
    (z * w == -- &1) (mod n)
    ==> (z * ((a - w * b) - (a + w * b)) == &2 * b) (mod n)`;;

let GS_CT_UPPER = INTEGER_RULE
 `!a b c w z n:int.
    (z * w == -- &1) (mod n)
    ==> (z * (c * (a - w * b) - c * (a + w * b)) == (&2 * c) * b) (mod n)`;;

let CRY_SPLIT_2_APPEND = prove
 (`!(A:X list) B.
        LENGTH A = LENGTH B /\ ~(LENGTH A = 0)
        ==> EL 0 (cry_split 2 (APPEND A B)) = A /\
            EL 1 (cry_split 2 (APPEND A B)) = B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`APPEND (A:X list) B`; `LENGTH(A:X list)`] CRY_SPLIT_2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[LIST_EQ] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `~(a + i < a)`; ADD_SUB2]);;

let CRY_FAST_INVNTTL_NTTL = prove
 (`!n p K x.
     n <= 6 /\ LENGTH p = 2 EXP (n + 2) /\ K < 2 EXP (6 - n) /\
     x < 2 EXP (n + 2)
     ==> EL x (cry_fast_invnttl (n + 2)
                (cry_fast_nttl (n + 2) p
                   (word(2 EXP (6 - n) + (2 EXP (6 - n) - 1 - K))))
                (word(2 EXP (6 - n) + K))) =
         (&2 pow (n + 1) * EL x p) rem &3329`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[cry_fast_invnttl] THEN REWRITE_TAC[LE_REFL] THEN
    ONCE_REWRITE_TAC[cry_fast_nttl] THEN REWRITE_TAC[LE_REFL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val(word(64 + K):byte) = 64 + K /\
                  val(word(64 + (63 - K)):byte) = 64 + (63 - K)`
     (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONJ_TAC THEN
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[EL_CRY_GS_BUTTERFLY; ARITH] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[EL_CRY_CT_BUTTERFLY; ARITH; ARITH_RULE `x < 2 ==> x + 2 < 4`;
                 ARITH_RULE `x < 4 ==> x - 2 < 4`;
                 ARITH_RULE `x < 4 ==> x - 2 < 2`;
                 ARITH_RULE `~(x + 2 < 2)`; ADD_SUB;
                 ARITH_RULE `~(x < 2) ==> x - 2 + 2 = x`] THEN
    REWRITE_TAC[INT_POW_1] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THENL
     [INTEGER_GOAL_TAC;
      MP_TAC(SPECL [`0`; `K:num`] ZETA_EXPC_MIRROR) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      MATCH_ACCEPT_TAC GS_CT_UPPER1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP (6 - n) = 2 * 2 EXP (6 - SUC n) /\ 2 EXP (6 - SUC n) <= 32 /\
    2 EXP (SUC n + 2) = 4 * 2 EXP (n + 1) /\
    2 EXP (n + 2) = 2 * 2 EXP (n + 1) /\ n <= 6`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `SUC n <= 6 ==> 6 - n = SUC(6 - SUC n)`; EXP];
      TRANS_TAC LE_TRANS `2 EXP 5` THEN CONJ_TAC THENL
       [REWRITE_TAC[LE_EXP] THEN ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
      REWRITE_TAC[ARITH_RULE `SUC n + 2 = SUC(SUC(n + 1))`; EXP] THEN
      ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; EXP];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC n + 1 = SUC(n + 1)`; INT_POW] THEN
  ABBREV_TAC `P = 2 EXP (6 - SUC n)` THEN
  ABBREV_TAC `H = 2 EXP (n + 1)` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[cry_fast_invnttl] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n + 2 <= 2)`; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[cry_fast_nttl] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n + 2 <= 2)`; LET_DEF; LET_END_DEF;
              ARITH_RULE `(SUC n + 2) - 1 = n + 2`] THEN
  SUBGOAL_THEN `val(word(P + K):byte) = P + K /\
                val(word(P + (P - 1 - K)):byte) = P + (P - 1 - K)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD] THEN
  ABBREV_TAC
   `CT = cry_ct_butterfly (n + 2) p (EL (P + (P - 1 - K)) cry_zeta_expc)` THEN
  SUBGOAL_THEN `~(H = 0) /\ x < 4 * H /\ 2 * K + 1 < 2 * P /\ 2 * K < 2 * P`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CT:int list`; `2 * H`] CRY_SPLIT_2) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "CT" THEN ASM_REWRITE_TAC[LENGTH_CRY_CT_BUTTERFLY] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S0:int list = EL 0 (cry_split 2 CT)` THEN
  ABBREV_TAC `S1:int list = EL 1 (cry_split 2 CT)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(P + (P - 1 - K)) * 2 = 2 * P + (2 * P - 1 - (2 * K + 1)) /\
    (P + (P - 1 - K)) * 2 + 1 = 2 * P + (2 * P - 1 - 2 * K) /\
    (P + K) * 2 + 1 = 2 * P + (2 * K + 1) /\
    (P + K) * 2 = 2 * P + 2 * K`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CRY_SPLIT_2_APPEND; LENGTH_CRY_FAST_NTTL; MULT_EQ_0;
               ARITH_EQ] THEN
  ASM_SIMP_TAC[EL_CRY_GS_BUTTERFLY; ARITH_RULE `x < 4 * H ==> x < 2 * 2 * H`;
               EL_APPEND; LENGTH_CRY_FAST_INVNTTL;
               ARITH_RULE `2 <= n + 2`] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[ARITH_RULE `~(x + 2 * H < 2 * H)`; ADD_SUB] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_THEN
     `cry_ct_butterfly (n + 2) p (EL (P + (P - 1 - K)) cry_zeta_expc) = CT`
     (SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[EL_CRY_CT_BUTTERFLY;
                 ARITH_RULE `x < 2 * H ==> x < 2 * 2 * H`;
                 ARITH_RULE `x < 2 * H ==> 2 * H + x < 2 * 2 * H`;
                 ARITH_RULE `~(2 * H + x < 2 * H)`; ADD_SUB2] THEN
    SUBGOAL_THEN `x + 2 * H = 2 * H + x` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`(&2 pow (n + 1)):int`,`c:int`) THEN GEN_TAC THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
    INTEGER_GOAL_TAC;
    SUBGOAL_THEN `x - 2 * H < 2 * H /\ 2 * H + (x - 2 * H) = x /\
                  x - 2 * H + 2 * H = x`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
    UNDISCH_THEN
     `cry_ct_butterfly (n + 2) p (EL (P + (P - 1 - K)) cry_zeta_expc) = CT`
     (SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[EL_CRY_CT_BUTTERFLY;
                 ARITH_RULE `x < 4 * H ==> x < 2 * 2 * H`;
                 ARITH_RULE `x < 2 * H ==> x < 2 * 2 * H`] THEN
    MP_TAC(SPECL [`SUC n`; `K:num`] ZETA_EXPC_MIRROR) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`(&2 pow (n + 1)):int`,`c:int`) THEN GEN_TAC THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
    MATCH_ACCEPT_TAC GS_CT_UPPER]);;

let RECIP_ZQ_17 = prove
 (`ring_inv (integer_mod_ring 3329) (&17) = &1175`,
  MATCH_MP_TAC RING_LINV_UNIQUE THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

let RECIP_ZQ_128 = prove
 (`ring_inv (integer_mod_ring 3329) (&128) = &3303`,
  MATCH_MP_TAC RING_LINV_UNIQUE THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV);;

let ZETA_INV_POW_MOD_256 = prove
 (`!e. (&1175 pow (e MOD 256)) rem &3329 = (&1175 pow e) rem &3329`,
  GEN_TAC THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; INT_OF_NUM_EQ; GSYM CONG] THEN
  MP_TAC(SPECL [`1175`; `3329`; `e MOD 256`; `e:num`]
         ORDER_DIVIDES_EXPDIFF) THEN
  ANTS_TAC THENL [CONV_TAC COPRIME_CONV; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `256` THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL; GSYM ORDER_DIVIDES] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CRY_ZETA_INV_TERM = prove
 (`!i j. i < 256 /\ j < 256
         ==> ring_pow (integer_mod_ring 3329)
              (ring_inv (integer_mod_ring 3329) (&17))
              (val(word_mul (word_add (word_mul (word 2)
                                                (cry_BitRev7 (word j)))
                                      (word 1))
                            (word i))) =
             (&1175 pow ((2 * bitreverse7 j + 1) * i)) rem &3329`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RECIP_ZQ_17; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_MUL] THEN ASM_SIMP_TAC[CRY_ZETA_EXP] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ZETA_INV_POW_MOD_256]);;

(* The Cryptol property fast_ntt_inverts.                                    *)

let CRY_FAST_INVNTT_NTT = prove
 (`!f. LENGTH f = 256 /\ (!i. i < 256 ==> &0 <= EL i f /\ EL i f < &3329)
       ==> cry_fast_invntt (cry_fast_ntt f) = f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_fast_invntt; cry_fast_ntt; LET_DEF; LET_END_DEF;
              RECIP_ZQ_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_REWRITE_TAC I [LIST_EQ] THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE; ARITH;
               ARITH_RULE `x < 256 ==> x < (255 + 1) - 0`; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`6`; `f:int list`; `0`; `x:num`] CRY_FAST_INVNTTL_NTTL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
  TRANS_TAC EQ_TRANS `EL x (f:int list) rem &3329` THEN CONJ_TAC THENL
   [CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN INTEGER_GOAL_TAC;
    MATCH_MP_TAC INT_REM_LT THEN ASM_SIMP_TAC[]]);;

let MLKEM_NTT_INV_COEFF_BOUND = prove
 (`!a k. (!i. i < 256 ==> &0 <= a i /\ a i < &3329) /\ k < 256
         ==> &0 <= coeff k (mlkem_ntt_inv a) /\
             coeff k (mlkem_ntt_inv a) < &3329`,
  SIMP_TAC[MLKEM_NTT_INV_COEFF; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let CRY_FAST_INVNTT = prove
 (`!a. LENGTH a = 256 /\ (!i. i < 256 ==> &0 <= EL i a /\ EL i a < &3329)
       ==> LENGTH(cry_fast_invntt a) = 256 /\
           !k. k < 256
               ==> EL k (cry_fast_invntt a) =
                   coeff k (mlkem_ntt_inv (\i. EL i a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `\i. EL i (a:int list)` MLKEM_NTT_INV) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `\i. EL i (a:int list)` MLKEM_NTT_INV_COEFF_BOUND) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `P = mlkem_ntt_inv (\i. EL i (a:int list))` THEN
  SUBGOAL_THEN
   `a = cry_fast_ntt (list_of_seq (\i. coeff i (P:(1->num)->int)) 256)`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `list_of_seq (\i. coeff i (P:(1->num)->int)) 256`
           CRY_FAST_NTT) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [LIST_EQ] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `mlkem_poly (\i. EL i (list_of_seq (\i. coeff i P) 256)) =
      mlkem_poly (\i. coeff i P)`
    SUBST1_TAC THENL
     [REWRITE_TAC[mlkem_poly; FUN_EQ_THM] THEN GEN_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
      ASM_SIMP_TAC[MLKEM_POLY_COEFF]];
    ALL_TAC] THEN
  MP_TAC(SPEC `list_of_seq (\i. coeff i (P:(1->num)->int)) 256`
         CRY_FAST_INVNTT_NTT) THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let ISUM_BITREVERSE7 = prove
 (`!f. isum (0..127) f = isum (0..127) (f o bitreverse7)`,
  GEN_TAC THEN MATCH_MP_TAC ISUM_BIJECTION THEN
  REWRITE_TAC[IN_NUMSEG; LE_0; ARITH_RULE `x <= 127 <=> x < 128`;
              BITREVERSE7_BOUND] THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `bitreverse7 y` THEN
  ASM_SIMP_TAC[BITREVERSE7_BOUND; BITREVERSE7_BITREVERSE7] THEN
  ASM_MESON_TAC[BITREVERSE7_BITREVERSE7]);;

let REM_MUL_CONG = prove
 (`!s s' c n:int. (s == s') (mod n) ==> ((s rem n) * c == c * s') (mod n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`s:int`; `n:int`] INT_CONG_REM_SELF) THEN
  POP_ASSUM MP_TAC THEN INTEGER_TAC);;

let CRY_NAIVENTTINV = prove
 (`!a. LENGTH a = 256 /\ (!i. i < 256 ==> &0 <= EL i a /\ EL i a < &3329)
       ==> LENGTH(cry_NaiveNTTInv a) = 256 /\
           !k. k < 256
               ==> EL k (cry_NaiveNTTInv a) =
                   coeff k (mlkem_ntt_inv (\i. EL i a))`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cry_NaiveNTTInv; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_JOIN_PAIRS; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_MAP o lhand o snd) THEN
  REWRITE_TAC[LENGTH_CRY_JOIN_PAIRS; LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_CRY_JOIN_PAIRS o lhand o
    lhand o snd) THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `k DIV 2 < 128` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE; ARITH;
               ARITH_RULE `k < 128 ==> k < (127 + 1) - 0`] THEN
  REWRITE_TAC[ADD_CLAUSES; CRY_ZSUM_MAP_RANGE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLKEM_NTT_INV_COEFF o rand o snd) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [ISUM_BITREVERSE7] THEN
  REWRITE_TAC[o_DEF] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV)
   [INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o REWRITE_RULE[EVEN_MOD; NOT_EVEN; ODD_MOD]) THEN
  REWRITE_TAC[INT_REM_EQ; ADD_CLAUSES] THEN
  MATCH_MP_TAC REM_MUL_CONG THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CRY_ZETA_INV_TERM; ARITH_RULE `j <= 127 ==> j < 256`;
               ARITH_RULE `k < 128 ==> k < 256`;
               BITREVERSE7_BITREVERSE7; ARITH_RULE `j <= 127 ==> j < 128`] THEN
  REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `j <= 127 ==> j < 256`;
               ARITH_RULE `j <= 127 ==> 2 * j < 256`;
               ARITH_RULE `j <= 127 ==> 2 * j + 1 < 256`] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

(* The other NTT properties of the Cryptol specification: naive_fast_invntt_ *)
(* equiv, fast_invntt_inverts, NaiveNTT_Inverts and NaiveNTTInv_Inverts.     *)

let CRY_NAIVE_FAST_INVNTT_EQUIV = prove
 (`!f. LENGTH f = 256 /\ (!i. i < 256 ==> &0 <= EL i f /\ EL i f < &3329)
       ==> cry_NaiveNTTInv f = cry_fast_invntt f`,
  SIMP_TAC[LIST_EQ; CRY_NAIVENTTINV; CRY_FAST_INVNTT]);;

let CRY_FAST_NTT_INVNTT = prove
 (`!a. LENGTH a = 256 /\ (!i. i < 256 ==> &0 <= EL i a /\ EL i a < &3329)
       ==> cry_fast_ntt (cry_fast_invntt a) = a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `a:int list` CRY_FAST_INVNTT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `cry_fast_invntt a` CRY_FAST_NTT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC I [LIST_EQ] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC `\i. EL i (a:int list)` MLKEM_NTT_INV) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mlkem_poly (\i. EL i (cry_fast_invntt a)) =
    mlkem_poly (\i. coeff i (mlkem_ntt_inv (\i. EL i a)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[mlkem_poly; FUN_EQ_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[MLKEM_POLY_COEFF]]);;

let CRY_FAST_NTT_BOUND = prove
 (`!f n. LENGTH f = 256 /\ n < 256
         ==> &0 <= EL n (cry_fast_ntt f) /\ EL n (cry_fast_ntt f) < &3329`,
  SIMP_TAC[CRY_FAST_NTT; MLKEM_NTT_BOUND; MLKEM_POLY_IN_RQ]);;

let CRY_NAIVENTT_INVERTS = prove
 (`!f. LENGTH f = 256 /\ (!i. i < 256 ==> &0 <= EL i f /\ EL i f < &3329)
       ==> cry_NaiveNTTInv (cry_NaiveNTT f) = f`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CRY_NAIVE_FAST_NTT_EQUIV] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRY_NAIVE_FAST_INVNTT_EQUIV o
    lhand o snd) THEN
  ASM_SIMP_TAC[CRY_FAST_NTT; CRY_FAST_NTT_BOUND] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CRY_FAST_INVNTT_NTT]);;

let CRY_NAIVENTTINV_INVERTS = prove
 (`!f. LENGTH f = 256 /\ (!i. i < 256 ==> &0 <= EL i f /\ EL i f < &3329)
       ==> cry_NaiveNTT (cry_NaiveNTTInv f) = f`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CRY_NAIVE_FAST_INVNTT_EQUIV] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRY_NAIVE_FAST_NTT_EQUIV o
    lhand o snd) THEN
  ASM_SIMP_TAC[CRY_FAST_INVNTT] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CRY_FAST_NTT_INVNTT]);;

(* ------------------------------------------------------------------------- *)
(* Byte strings: a slice of a byte string is a field of its number, so the   *)
(* fields of a block or a prefix are fields of the whole string.             *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_BYTELIST_DIGITSUM = prove
 (`!l. num_of_bytelist l =
       nsum {i | i < LENGTH l} (\i. 256 EXP i * val(EL i l))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[num_of_bytelist; LENGTH; CONJUNCT1 LT; EMPTY_GSPEC;
              NSUM_CLAUSES] THEN
  ASM_REWRITE_TAC[NSUM_LT_SUC_LEFT; EL; HD; TL; EXP; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; NSUM_LMUL]);;

let NUM_OF_BYTELIST_SLICE = prove
 (`!l a n. a + n <= LENGTH l
           ==> num_of_bytelist (list_of_seq (\t. EL (a + t) l) n) =
               (num_of_bytelist l DIV 256 EXP a) MOD 256 EXP n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NUM_OF_BYTELIST_DIGITSUM] THEN
  MP_TAC(ISPECL [`256`; `\i. val(EL i (l:byte list))`; `LENGTH(l:byte list)`;
                 `a:num`] DIGITSUM_DIV_NUMSEG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPEC `EL i (l:byte list)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_MOD_NUMSEG o rand o snd) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `EL (i + a) (l:byte list)` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; ARITH_RULE
   `a + n <= l ==> MIN (l - a) n = n`] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ADD_SYM]);;

let FIELD_OF_SLICE = prove
 (`!N d i j.
        j < 256
        ==> ((N DIV 256 EXP (32 * d * i)) MOD 256 EXP (32 * d) DIV
             2 EXP (d * j)) MOD 2 EXP d =
            (N DIV 2 EXP (d * (256 * i + j))) MOD 2 EXP d`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN
   `MIN (8 * 32 * d * i + 8 * 32 * d) (8 * 32 * d * i + d * j + d) =
    d * (2 EXP 8 * i + j) + d`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `d * j + d <= d * 256` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `d * j + d = d * (j + 1)`] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let MLKEM_DECODE_CHUNK = prove
 (`!d B i j.
        j < 256 /\ 32 * d * (i + 1) <= LENGTH B
        ==> mlkem_decode d (list_of_seq (\t. EL (32 * d * i + t) B) (32 * d))
                         j =
            mlkem_decode d B (256 * i + j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_decode; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_SLICE; FIELD_OF_SLICE; ARITH_RULE
   `32 * d * (i + 1) <= l ==> 32 * d * i + 32 * d <= l`]);;

let MLKEM_DECODE_PREFIX = prove
 (`!d B L j.
        d * (j + 1) <= 8 * L /\ L <= LENGTH B
        ==> mlkem_decode d (list_of_seq (\t. EL t B) L) j =
            mlkem_decode d B j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_decode; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`B:byte list`; `0`; `L:num`] NUM_OF_BYTELIST_SLICE) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; EXP; DIV_1] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `d * (j + 1) <= 8 * L ==> MIN (8 * L) (d * j + d) =
                                                   d * j + d`]);;

let CRY_ATAT_RANGE = prove
 (`!(xs:A list) a b.
        cry_atat xs (cry_range a b) =
        list_of_seq (\i. EL (a + i) xs) ((b + 1) - a)`,
  REWRITE_TAC[cry_atat; cry_range; MAP_LIST_OF_SEQ; o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Vectors: ByteDecode_Vec, ByteDecode12_Vec, ByteEncode_Vec, transpose.     *)
(* ------------------------------------------------------------------------- *)

let CRY_SPLIT_BLOCK = prove
 (`!k (B:A list) c.
        LENGTH B = c * k /\ ~(k = 0) /\ ~(c = 0)
        ==> LENGTH(cry_split k B) = k /\
            !i. i < k ==> EL i (cry_split k B) =
                          list_of_seq (\t. EL (c * i + t) B) c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cry_split] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c * k) DIV k = c /\ (c * k) DIV c = k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[LENGTH_CRY_GROUPBY; EL_CRY_GROUPBY]]);;

let CRY_BYTEDECODE_VEC = prove
 (`!k B. LENGTH B = 32 * dimindex(:N) * k /\ ~(k = 0) /\ dimindex(:N) < 12
         ==> LENGTH(cry_ByteDecode_Vec k B:((N word) list) list) = k /\
             !i. i < k
                 ==> LENGTH(EL i (cry_ByteDecode_Vec k B:
                                    ((N word) list) list)) = 256 /\
                     !j. j < 256
                         ==> &(val(EL j (EL i (cry_ByteDecode_Vec k B:
                                                ((N word) list) list)))) =
                             mlkem_decode (dimindex(:N)) B (256 * i + j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cry_ByteDecode_Vec] THEN
  MP_TAC(ISPECL [`k:num`; `B:byte list`; `32 * dimindex(:N)`]
         CRY_SPLIT_BLOCK) THEN
  ASM_REWRITE_TAC[MULT_ASSOC; MULT_EQ_0; DIMINDEX_NONZERO; ARITH_EQ] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `list_of_seq (\t. EL (32 * dimindex(:N) * i + t)
                                  (B:byte list))
                            (32 * dimindex(:N))` CRY_BYTEDECODE) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; MULT_ASSOC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC MLKEM_DECODE_CHUNK THEN ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let CRY_BYTEDECODE12_VEC = prove
 (`!k B. LENGTH B = 384 * k /\ ~(k = 0)
         ==> LENGTH(cry_ByteDecode12_Vec k B) = k /\
             !i. i < k
                 ==> LENGTH(EL i (cry_ByteDecode12_Vec k B)) = 256 /\
                     !j. j < 256
                         ==> EL j (EL i (cry_ByteDecode12_Vec k B)) =
                             mlkem_decode 12 B (256 * i + j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cry_ByteDecode12_Vec] THEN
  MP_TAC(ISPECL [`k:num`; `B:byte list`; `384`] CRY_SPLIT_BLOCK) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `list_of_seq (\t. EL (384 * i + t) (B:byte list)) 384`
         CRY_BYTEDECODE12) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`12`; `B:byte list`; `i:num`; `j:num`] MLKEM_DECODE_CHUNK) THEN
  REWRITE_TAC[ARITH_RULE `32 * 12 * i = 384 * i`;
              ARITH_RULE `32 * 12 = 384`] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let CRY_BYTEENCODE_VEC = prove
 (`!(Fv:((N word) list) list) k G.
        LENGTH Fv = k /\
        (!i. i < k ==> LENGTH(EL i Fv) = 256) /\
        (!i n. i < k /\ n < 256 ==> &(val(EL n (EL i Fv))) = G(256 * i + n))
        ==> cry_ByteEncode_Vec Fv = mlkem_encode (dimindex(:N)) (256 * k) G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `k:num`;
                 `\i n. (G:num->int)(256 * i + n)`] MLKEM_ENCODE_BLOCKS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[divides] THEN EXISTS_TAC `32 * dimindex(:N)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mlkem_encode (dimindex(:N)) (256 * k)
     (\n. (\i n. (G:num->int)(256 * i + n)) (n DIV 256) (n MOD 256)) =
    mlkem_encode (dimindex(:N)) (256 * k) G`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLKEM_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[cry_ByteEncode_Vec] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [LIST_EQ] THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRY_BYTEENCODE o lhand o snd) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MLKEM_ENCODE_EQ THEN ASM_SIMP_TAC[]);;

let LENGTH_CRY_TRANSPOSE = prove
 (`!cols (M:(A list) list). LENGTH(cry_transpose cols M) = cols`,
  REWRITE_TAC[cry_transpose; LENGTH_LIST_OF_SEQ]);;

let EL_CRY_TRANSPOSE = prove
 (`!cols (M:(A list) list) i.
        i < cols ==> EL i (cry_transpose cols M) = MAP (\row. EL i row) M`,
  SIMP_TAC[cry_transpose; EL_LIST_OF_SEQ]);;

let COEFF_MLKEM_CBD = prove
 (`!eta B n. LENGTH B = 64 * eta /\ ~(eta = 0) /\ n < 256
             ==> coeff n (mlkem_cbd eta B) =
                 EL n (cry_SamplePolyCBD eta B) rem &3329`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`eta:num`; `B:byte list`] CRY_SAMPLEPOLYCBD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY]);;

(* ------------------------------------------------------------------------- *)
(* K-PKE Encrypt, through the NTT-domain form KPKE_ENCRYPT_FIPS, under its   *)
(* hypothesis on SampleNTT and the lengths given by the Cryptol types.       *)
(* ------------------------------------------------------------------------- *)

let CRY_DOTVECVEC_LENGTH = prove
 (`!v1 v2. LENGTH v1 = LENGTH v2
           ==> LENGTH(cry_dotVecVec v1 v2) = 256 /\
               !m. m < 256
                   ==> EL m (cry_dotVecVec v1 v2) =
                       isum {j | j < LENGTH v1}
                        (\j. EL m (cry_MultiplyNTTs (EL j v1) (EL j v2))) rem
                       &3329`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CRY_DOTVECVEC THEN
  ASM_REWRITE_TAC[]);;

let CRY_NTTINV_DOT = prove
 (`!v1 v2 n.
        LENGTH v1 = LENGTH v2 /\ n < 256
        ==> LENGTH(cry_NTTInv (cry_dotVecVec v1 v2)) = 256 /\
            EL n (cry_NTTInv (cry_dotVecVec v1 v2)) =
            coeff n (mlkem_ntt_inv
                      (\t. isum {j | j < LENGTH v1}
                            (\j. EL t (cry_MultiplyNTTs (EL j v1) (EL j v2)))
                           rem &3329))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`v1:(int list) list`; `v2:(int list) list`]
         CRY_DOTVECVEC_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `cry_dotVecVec v1 v2` CRY_FAST_INVNTT) THEN
  ASM_SIMP_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ; ARITH; INT_OF_NUM_EQ;
               INT_OF_NUM_LT; cry_NTTInv] THEN
  DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN ASM_SIMP_TAC[]);;

let LENGTH_CRY_NTTINV = prove
 (`!v. LENGTH(cry_NTTInv v) = 256`,
  REWRITE_TAC[cry_NTTInv; cry_fast_invntt; LET_DEF; LET_END_DEF;
              LENGTH_MAP; LENGTH_CRY_RANGE] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let RING_SUM_MLKEM_ZQ_BOUND = prove
 (`!s (f:K->int).
        &0 <= ring_sum mlkem_zq s f /\ ring_sum mlkem_zq s f < &3329`,
  REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM]);;

let MLKEM_NTT_INV_RING_SUM = prove
 (`!s (f:num->K->int).
        mlkem_ntt_inv (\n. ring_sum mlkem_zq s (f n))
        IN ring_carrier mlkem_rq`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `\n. ring_sum mlkem_zq s ((f:num->K->int) n)`
         MLKEM_NTT_INV) THEN
  REWRITE_TAC[RING_SUM_MLKEM_ZQ_BOUND] THEN SIMP_TAC[]);;

let CRY_K_PKE_ENCRYPT = prove
 (`!k eta1 eta2 ek m r.
     ~(k = 0) /\ ~(eta1 = 0) /\ ~(eta2 = 0) /\
     dimindex(:DU) < 12 /\ dimindex(:DV) < 12 /\
     LENGTH ek = 384 * k + 32 /\ LENGTH m = 32 /\
     (!i j n. i < k /\ j < k /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice (384 * k) 32 ek) [word j; word i])
                   n < &3329)
     ==> cry_K_PKE_Encrypt (:DU) (:DV) k eta1 eta2 ek m r =
         kpke_encrypt (k,eta1,eta2,dimindex(:DU),dimindex(:DV)) ek m r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[KPKE_ENCRYPT_FIPS] THEN
  REWRITE_TAC[cry_K_PKE_Encrypt; CRY_PRF; CRY_ATAT_RANGE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `((384 * k + 32 - 1) + 1) - 384 * k = 32 /\
                (384 * k - 1 + 1) - 0 = 384 * k /\
                (k - 1 + 1) - 0 = k /\ (2 * k - 1 + 1) - k = k`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM mlkem_slice; ADD_CLAUSES] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC CRY_BYTEENCODE_VEC THEN
    REWRITE_TAC[cry_Compress_Mat; cry_Compress_Vec; cry_vec_add;
                cry_NTTInv_Vec; cry_NTT_Vec; cry_dotMatVec; cry_tq_add] THEN
    ASM_SIMP_TAC[LENGTH_MAP; LENGTH_MAP2; LENGTH_CRY_TRANSPOSE;
                 LENGTH_CRY_RANGE;
                 ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`;
                 ARITH_RULE `~(k = 0) ==> (2 * k - 1 + 1) - k = k`] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THENL [DISCH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP; EL_MAP2; LENGTH_MAP; LENGTH_MAP2;
                 LENGTH_CRY_TRANSPOSE; LENGTH_CRY_RANGE; EL_CRY_TRANSPOSE;
                 EL_CRY_RANGE;
                 ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`;
                 ARITH_RULE `~(k = 0) ==> (2 * k - 1 + 1) - k = k`] THENL
     [REWRITE_TAC[cry_Compress_Vec; cry_tq_add; LENGTH_MAP] THEN
      ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_CRY_NTTINV; CRY_SAMPLEPOLYCBD;
                   LENGTH_MLKEM_PRF];
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[DIV_MOD_256_BLOCK] THEN
    REWRITE_TAC[cry_Compress_Vec; cry_tq_add] THEN
    ASM_SIMP_TAC[EL_MAP; EL_MAP2; LENGTH_MAP2; LENGTH_CRY_NTTINV;
                 CRY_SAMPLEPOLYCBD; LENGTH_MLKEM_PRF; CRY_COMPRESS] THEN
    AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand o rand) CRY_NTTINV_DOT o
      lhand o lhand o snd) THEN
    ASM_SIMP_TAC[LENGTH_MAP; LENGTH_CRY_RANGE;
                 ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_NTT_INV_RING_SUM; MLKEM_CBD_IN_RQ] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_CBD; LENGTH_MLKEM_PRF] THEN
    REWRITE_TAC[mlkem_zq; INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN
    X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM mlkem_zq] THEN
    SIMP_TAC[RING_SUM_MLKEM_ZQ_MULTIPLY; FINITE_NUMSEG_LT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CRY_MULTIPLYNTTS] THEN
    MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE;
                 ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`; ADD_CLAUSES;
                 APPEND; CRY_SAMPLENTT_EQ; CRY_NTT_CBD; LENGTH_MLKEM_PRF];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(mlkem_slice 0 (384 * k) ek) = 384 * k`
  ASSUME_TAC THENL [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `mlkem_slice 0 (384 * k) ek`]
         CRY_BYTEDECODE12_VEC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(cry_ByteDecode m:(1 word) list) = 256` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CRY_BYTEDECODE; DIMINDEX_1; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(cry_SamplePolyCBD eta2 (mlkem_prf eta2 r (word (2 * k)))) = 256`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CRY_SAMPLEPOLYCBD; LENGTH_MLKEM_PRF]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRY_BYTEENCODE o lhand o snd) THEN
  REWRITE_TAC[cry_Compress_Vec; cry_tq_add; LENGTH_MAP] THEN
  ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_CRY_NTTINV; cry_Decompress_Vec;
               LENGTH_MAP] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_MAP; EL_MAP2; LENGTH_MAP2; LENGTH_MAP; LENGTH_CRY_NTTINV;
               CRY_COMPRESS] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand o rand) CRY_NTTINV_DOT o
    lhand o lhand o lhand o snd) THEN
  ASM_SIMP_TAC[cry_NTT_Vec; LENGTH_MAP; LENGTH_CRY_RANGE;
               ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_NTT_INV_RING_SUM; MLKEM_CBD_IN_RQ;
           RING_ADD; MLKEM_POLY_IN_RQ] THEN
  ASM_SIMP_TAC[COEFF_MLKEM_CBD; LENGTH_MLKEM_PRF; COEFF_MLKEM_POLY;
               CRY_DECOMPRESS; DIMINDEX_1; ARITH; CRY_BYTEDECODE] THEN
  REWRITE_TAC[mlkem_zq; INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM mlkem_zq] THEN
  SIMP_TAC[RING_SUM_MLKEM_ZQ_MULTIPLY; FINITE_NUMSEG_LT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CRY_MULTIPLYNTTS] THEN
  MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_CRY_RANGE; EL_CRY_RANGE;
               ARITH_RULE `~(k = 0) ==> (k - 1 + 1) - 0 = k`; ADD_CLAUSES;
               CRY_NTT_CBD; LENGTH_MLKEM_PRF] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[mlkem_slice] THEN
  REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
  MATCH_MP_TAC MLKEM_DECODE_PREFIX THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  TRANS_TAC LE_TRANS `12 * 256 * k` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* K-PKE Decrypt, through KPKE_DECRYPT_FIPS.                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_POLY_EQ = prove
 (`!a b. (!i. i < 256 ==> a i = b i) ==> mlkem_poly a = mlkem_poly b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_poly; FUN_EQ_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let CRY_K_PKE_DECRYPT = prove
 (`!k eta1 eta2 dk c.
     ~(k = 0) /\ dimindex(:DU) < 12 /\ dimindex(:DV) < 12 /\
     LENGTH dk = 384 * k /\
     LENGTH c = 32 * (dimindex(:DU) * k + dimindex(:DV))
     ==> cry_K_PKE_Decrypt (:DU) (:DV) k dk c =
         kpke_decrypt (k,eta1,eta2,dimindex(:DU),dimindex(:DV)) dk c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[KPKE_DECRYPT_FIPS] THEN
  REWRITE_TAC[cry_K_PKE_Decrypt; CRY_ATAT_RANGE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `du = dimindex(:DU)` THEN ABBREV_TAC `dv = dimindex(:DV)` THEN
  SUBGOAL_THEN `~(du = 0) /\ ~(dv = 0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["du"; "dv"] THEN REWRITE_TAC[DIMINDEX_NONZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `(32 * du * k - 1 + 1) - 0 = 32 * du * k /\
                ((32 * (du * k + dv) - 1) + 1) - 32 * du * k = 32 * dv`
   (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `~(du * k = 0)` MP_TAC THENL
     [ASM_REWRITE_TAC[MULT_EQ_0]; ALL_TAC] THEN
    SPEC_TAC(`du * k`,`p:num`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM mlkem_slice; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`k:num`; `dk:byte list`] CRY_BYTEDECODE12_VEC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(mlkem_slice 0 (32 * du * k) c) = 32 * du * k /\
                LENGTH(mlkem_slice (32 * du * k) (32 * dv) c) = 32 * dv`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `mlkem_slice 0 (32 * du * k) c`]
         (INST_TYPE [`:DU`,`:N`] CRY_BYTEDECODE_VEC)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `mlkem_slice (32 * du * k) (32 * dv) c`
         (INST_TYPE [`:DV`,`:N`] CRY_BYTEDECODE)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRY_BYTEENCODE o lhand o snd) THEN
  REWRITE_TAC[cry_Compress_Vec; cry_tq_sub; cry_Decompress_Vec; LENGTH_MAP;
              DIMINDEX_1] THEN
  ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_MAP; LENGTH_CRY_NTTINV] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_MAP; EL_MAP2; LENGTH_MAP2; LENGTH_MAP; LENGTH_CRY_NTTINV;
               CRY_COMPRESS; DIMINDEX_1; CRY_DECOMPRESS] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand o rand) CRY_NTTINV_DOT o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[cry_NTT_Vec; cry_Decompress_Mat; LENGTH_MAP] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SIMP_TAC[MLKEM_RQ_COEFF_SUB; MLKEM_NTT_INV_RING_SUM; MLKEM_POLY_IN_RQ] THEN
  ASM_SIMP_TAC[COEFF_MLKEM_POLY] THEN
  REWRITE_TAC[mlkem_zq; INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM mlkem_zq] THEN
  SIMP_TAC[RING_SUM_MLKEM_ZQ_MULTIPLY; FINITE_NUMSEG_LT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CRY_MULTIPLYNTTS] THEN
  MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; cry_NTT; cry_Decompress_Vec] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_MAP] THEN REWRITE_TAC[cry_Decompress_Vec] THEN
  MP_TAC(ISPEC `MAP cry_Decompress
                 (EL j (cry_ByteDecode_Vec k (mlkem_slice 0 (32 * du * k) c):
                        ((DU word) list) list))` CRY_FAST_NTT) THEN
  ASM_SIMP_TAC[LENGTH_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MLKEM_POLY_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; CRY_DECOMPRESS] THEN AP_TERM_TAC THEN
  REWRITE_TAC[mlkem_slice; ADD_CLAUSES; ETA_AX] THEN
  MATCH_MP_TAC MLKEM_DECODE_PREFIX THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 32 * d * k = d * 256 * k`] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM: the internal functions, and the API with its input checks. The    *)
(* Cryptol Encaps and Decaps leave the checks to the caller; combined with   *)
(* them they are mlkem_encaps and mlkem_decaps (CRY_ENCAPS, CRY_DECAPS).     *)
(* ------------------------------------------------------------------------- *)

let CRY_H = prove
 (`cry_H = mlkem_h`,
  REWRITE_TAC[FUN_EQ_THM; cry_H; mlkem_h]);;

let CRY_J = prove
 (`cry_J = mlkem_j`,
  REWRITE_TAC[FUN_EQ_THM; cry_J; mlkem_j]);;

let CRY_KEYGEN_INTERNAL = prove
 (`!k eta1 eta2 du dv d z.
        ~(k = 0) /\ ~(eta1 = 0) /\
        (!i j n. i < k /\ j < k /\ n < 256
                 ==> mlkem_sample_ntt
                      (APPEND (FST(mlkem_g(APPEND d [word k])))
                              [word j; word i]) n < &3329)
        ==> cry_KeyGen_internal k eta1 d z =
            mlkem_keygen_internal (k,eta1,eta2,du,dv) d z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_KeyGen_internal; mlkem_keygen_internal; CRY_H] THEN
  ASM_SIMP_TAC[CRY_K_PKE_KEYGEN] THEN
  SPEC_TAC(`kpke_keygen (k,eta1,eta2,du,dv) d`,`p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let CRY_ENCAPS_INTERNAL = prove
 (`!k eta1 eta2 ek m.
     ~(k = 0) /\ ~(eta1 = 0) /\ ~(eta2 = 0) /\
     dimindex(:DU) < 12 /\ dimindex(:DV) < 12 /\
     LENGTH ek = 384 * k + 32 /\ LENGTH m = 32 /\
     (!i j n. i < k /\ j < k /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice (384 * k) 32 ek) [word j; word i])
                   n < &3329)
     ==> cry_Encaps_internal (:DU) (:DV) k eta1 eta2 ek m =
         mlkem_encaps_internal (k,eta1,eta2,dimindex(:DU),dimindex(:DV)) ek m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_Encaps_internal; mlkem_encaps_internal; CRY_H; CRY_G] THEN
  SPEC_TAC(`mlkem_g (APPEND m (mlkem_h ek))`,`p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[CRY_K_PKE_ENCRYPT]);;

let LENGTH_KPKE_DECRYPT = prove
 (`!k eta1 eta2 du dv dk c.
        LENGTH(kpke_decrypt (k,eta1,eta2,du,dv) dk c) = 32`,
  REWRITE_TAC[kpke_decrypt; LET_DEF; LET_END_DEF; MLKEM_ENCODE_LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CRY_DECAPS_INTERNAL = prove
 (`!k eta1 eta2 dk c.
     ~(k = 0) /\ ~(eta1 = 0) /\ ~(eta2 = 0) /\
     dimindex(:DU) < 12 /\ dimindex(:DV) < 12 /\
     LENGTH dk = 768 * k + 96 /\
     LENGTH c = 32 * (dimindex(:DU) * k + dimindex(:DV)) /\
     (!i j n. i < k /\ j < k /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice (384 * k) 32
                             (mlkem_slice (384 * k) (384 * k + 32) dk))
                           [word j; word i]) n < &3329)
     ==> cry_Decaps_internal (:DU) (:DV) k eta1 eta2 dk c =
         mlkem_decaps_internal (k,eta1,eta2,dimindex(:DU),dimindex(:DV)) dk c`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_Decaps_internal; mlkem_decaps_internal; CRY_ATAT_RANGE;
              CRY_G; CRY_J] THEN
  SUBGOAL_THEN
   `(384 * k - 1 + 1) - 0 = 384 * k /\
    ((768 * k + 32 - 1) + 1) - 384 * k = 384 * k + 32 /\
    ((768 * k + 64 - 1) + 1) - (768 * k + 32) = 32 /\
    ((768 * k + 96 - 1) + 1) - (768 * k + 64) = 32`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM mlkem_slice; ADD_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`k:num`; `eta1:num`; `eta2:num`;
                `mlkem_slice 0 (384 * k) dk`; `c:byte list`]
         CRY_K_PKE_DECRYPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ];
    DISCH_THEN SUBST1_TAC] THEN
  SPEC_TAC(`mlkem_g (APPEND (kpke_decrypt (k,eta1,eta2,dimindex (:DU),
                                          dimindex (:DV))
                              (mlkem_slice 0 (384 * k) dk) c)
                             (mlkem_slice (768 * k + 32) 32 dk))`,
           `p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MAP_EVERY X_GEN_TAC [`K':byte list`; `r':byte list`] THEN
  MP_TAC(SPECL [`k:num`; `eta1:num`; `eta2:num`;
                `mlkem_slice (384 * k) (384 * k + 32) dk`;
                `kpke_decrypt (k,eta1,eta2,dimindex (:DU),dimindex (:DV))
                              (mlkem_slice 0 (384 * k) dk) c`;
                `r':byte list`] CRY_K_PKE_ENCRYPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_KPKE_DECRYPT; mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    REWRITE_TAC[mlkem_slice];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[COND_SWAP] THEN MESON_TAC[]);;

let CRY_KEYGEN = prove
 (`!k eta1 eta2 du dv d z.
        ~(k = 0) /\ ~(eta1 = 0) /\
        (!i j n. i < k /\ j < k /\ n < 256
                 ==> mlkem_sample_ntt
                      (APPEND (FST(mlkem_g(APPEND d [word k])))
                              [word j; word i]) n < &3329)
        ==> cry_KeyGen k eta1 (SOME d) (SOME z) =
            mlkem_keygen (k,eta1,eta2,du,dv) d z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cry_KeyGen; mlkem_keygen] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CRY_KEYGEN_INTERNAL] THEN
  SPEC_TAC(`mlkem_keygen_internal (k,eta1,eta2,du,dv) d z`,
           `p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let MLKEM_DECODE_12_BOUND = prove
 (`!B j. &0 <= mlkem_decode 12 B j /\ mlkem_decode 12 B j < &3329`,
  REWRITE_TAC[mlkem_decode; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let CRY_ENCAPSULATIONKEYCHECK = prove
 (`!k eta1 eta2 du dv ek.
        ~(k = 0) /\ LENGTH ek = 384 * k + 32
        ==> (cry_encapsulationKeyCheck k ek <=>
             mlkem_ek_check (k,eta1,eta2,du,dv) ek)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cry_encapsulationKeyCheck; mlkem_ek_check; LET_DEF;
              LET_END_DEF; CRY_ATAT_RANGE] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> (384 * k - 1 + 1) - 0 = 384 * k`] THEN
  REWRITE_TAC[GSYM mlkem_slice] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `LENGTH(mlkem_slice 0 (384 * k) ek) = 384 * k` ASSUME_TAC
  THENL [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `mlkem_slice 0 (384 * k) ek`]
         CRY_BYTEDECODE12_VEC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CRY_BYTEENCODE12_VEC_ALT THEN ASM_SIMP_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[mlkem_slice; ADD_CLAUSES; ETA_AX] THEN
    MATCH_MP_TAC MLKEM_DECODE_PREFIX THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    TRANS_TAC LE_TRANS `12 * 256 * k` THEN CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ARITH_TAC];
    REWRITE_TAC[MLKEM_DECODE_12_BOUND];
    MP_TAC(SPECL [`ek:byte list`; `256 * i + n`] MLKEM_DECODE_12_BOUND) THEN
    INT_ARITH_TAC]);;

let CRY_ENCAPS = prove
 (`!k eta1 eta2 ek m.
     ~(k = 0) /\ ~(eta1 = 0) /\ ~(eta2 = 0) /\
     dimindex(:DU) < 12 /\ dimindex(:DV) < 12 /\
     LENGTH ek = 384 * k + 32 /\ LENGTH m = 32 /\
     (!i j n. i < k /\ j < k /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice (384 * k) 32 ek) [word j; word i])
                   n < &3329)
     ==> cry_Encaps (:DU) (:DV) k eta1 eta2 ek (SOME m) =
         mlkem_encaps_internal (k,eta1,eta2,dimindex(:DU),dimindex(:DV))
                               ek m /\
         mlkem_encaps (k,eta1,eta2,dimindex(:DU),dimindex(:DV)) ek m =
         if cry_encapsulationKeyCheck k ek
         then SOME(cry_Encaps (:DU) (:DV) k eta1 eta2 ek (SOME m))
         else NONE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[cry_Encaps] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[CRY_ENCAPS_INTERNAL] THEN
    SPEC_TAC(`mlkem_encaps_internal
               (k,eta1,eta2,dimindex(:DU),dimindex(:DV)) ek m`,
             `p:byte list#byte list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[mlkem_encaps; GSYM CRY_ENCAPSULATIONKEYCHECK]]);;

let CRY_DECAPSULATIONINPUTCHECK = prove
 (`!k eta1 eta2 du dv dk c.
        LENGTH dk = 768 * k + 96 /\ LENGTH c = 32 * (du * k + dv)
        ==> (cry_decapsulationInputCheck k dk c <=>
             mlkem_decaps_check (k,eta1,eta2,du,dv) dk c)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[cry_decapsulationInputCheck; cry_decapsulationKeyCheck;
                  mlkem_decaps_check; LET_DEF; LET_END_DEF; CRY_ATAT_RANGE;
                  CRY_H] THEN
  SUBGOAL_THEN
   `((768 * k + 32 - 1) + 1) - 384 * k = 384 * k + 32 /\
    ((768 * k + 64 - 1) + 1) - (768 * k + 32) = 32`
   (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM mlkem_slice]);;

let CRY_DECAPS = prove
 (`!k eta1 eta2 dk c.
     ~(k = 0) /\ ~(eta1 = 0) /\ ~(eta2 = 0) /\
     dimindex(:DU) < 12 /\ dimindex(:DV) < 12 /\
     LENGTH dk = 768 * k + 96 /\
     LENGTH c = 32 * (dimindex(:DU) * k + dimindex(:DV)) /\
     (!i j n. i < k /\ j < k /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice (384 * k) 32
                             (mlkem_slice (384 * k) (384 * k + 32) dk))
                           [word j; word i]) n < &3329)
     ==> cry_Decaps (:DU) (:DV) k eta1 eta2 dk c =
         mlkem_decaps_internal (k,eta1,eta2,dimindex(:DU),dimindex(:DV))
                               dk c /\
         mlkem_decaps (k,eta1,eta2,dimindex(:DU),dimindex(:DV)) dk c =
         if cry_decapsulationInputCheck k dk c
         then SOME(cry_Decaps (:DU) (:DV) k eta1 eta2 dk c)
         else NONE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[cry_Decaps; CRY_DECAPS_INTERNAL];
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[mlkem_decaps; GSYM CRY_DECAPSULATIONINPUTCHECK]]);;

(* ------------------------------------------------------------------------- *)
(* The three parameter sets of FIPS 203 (mlkem512, mlkem768, mlkem1024 of    *)
(* common/fips203.ml): the Cryptol API with d_u and d_v as the word types,   *)
(* and the lengths given by the Cryptol types, is the fips203.ml API.        *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_5 = DIMINDEX_CONV `dimindex(:5)`;;
let DIMINDEX_10 = DIMINDEX_CONV `dimindex(:10)`;;
let DIMINDEX_11 = DIMINDEX_CONV `dimindex(:11)`;;

let CRY_MLKEM512 = prove
 (`(!d z. (!i j n. i < 2 /\ j < 2 /\ n < 256
                  ==> mlkem_sample_ntt
                       (APPEND (FST(mlkem_g(APPEND d [word 2])))
                               [word j; word i]) n < &3329)
          ==> cry_KeyGen 2 3 (SOME d) (SOME z) = mlkem_keygen mlkem512 d z) /\
   (!ek m. LENGTH ek = 800 /\ LENGTH m = 32 /\
           (!i j n. i < 2 /\ j < 2 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 768 32 ek) [word j; word i])
                         n < &3329)
           ==> mlkem_encaps mlkem512 ek m =
               if cry_encapsulationKeyCheck 2 ek
               then SOME(cry_Encaps (:10) (:4) 2 3 2 ek (SOME m))
               else NONE) /\
   (!dk c. LENGTH dk = 1632 /\ LENGTH c = 768 /\
           (!i j n. i < 2 /\ j < 2 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 768 32
                                   (mlkem_slice 768 800 dk))
                                 [word j; word i]) n < &3329)
           ==> mlkem_decaps mlkem512 dk c =
               if cry_decapsulationInputCheck 2 dk c
               then SOME(cry_Decaps (:10) (:4) 2 3 2 dk c)
               else NONE)`,
  REWRITE_TAC[mlkem512] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC CRY_KEYGEN THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`2`; `3`; `2`; `ek:byte list`; `m:byte list`]
           (INST_TYPE [`:10`,`:DU`; `:4`,`:DV`] CRY_ENCAPS));
    MP_TAC(SPECL [`2`; `3`; `2`; `dk:byte list`; `c:byte list`]
           (INST_TYPE [`:10`,`:DU`; `:4`,`:DV`] CRY_DECAPS))] THEN
  REWRITE_TAC[DIMINDEX_4; DIMINDEX_5; DIMINDEX_10; DIMINDEX_11] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CRY_MLKEM768 = prove
 (`(!d z. (!i j n. i < 3 /\ j < 3 /\ n < 256
                  ==> mlkem_sample_ntt
                       (APPEND (FST(mlkem_g(APPEND d [word 3])))
                               [word j; word i]) n < &3329)
          ==> cry_KeyGen 3 2 (SOME d) (SOME z) = mlkem_keygen mlkem768 d z) /\
   (!ek m. LENGTH ek = 1184 /\ LENGTH m = 32 /\
           (!i j n. i < 3 /\ j < 3 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 1152 32 ek) [word j; word i])
                         n < &3329)
           ==> mlkem_encaps mlkem768 ek m =
               if cry_encapsulationKeyCheck 3 ek
               then SOME(cry_Encaps (:10) (:4) 3 2 2 ek (SOME m))
               else NONE) /\
   (!dk c. LENGTH dk = 2400 /\ LENGTH c = 1088 /\
           (!i j n. i < 3 /\ j < 3 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 1152 32
                                   (mlkem_slice 1152 1184 dk))
                                 [word j; word i]) n < &3329)
           ==> mlkem_decaps mlkem768 dk c =
               if cry_decapsulationInputCheck 3 dk c
               then SOME(cry_Decaps (:10) (:4) 3 2 2 dk c)
               else NONE)`,
  REWRITE_TAC[mlkem768] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC CRY_KEYGEN THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`3`; `2`; `2`; `ek:byte list`; `m:byte list`]
           (INST_TYPE [`:10`,`:DU`; `:4`,`:DV`] CRY_ENCAPS));
    MP_TAC(SPECL [`3`; `2`; `2`; `dk:byte list`; `c:byte list`]
           (INST_TYPE [`:10`,`:DU`; `:4`,`:DV`] CRY_DECAPS))] THEN
  REWRITE_TAC[DIMINDEX_4; DIMINDEX_5; DIMINDEX_10; DIMINDEX_11] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CRY_MLKEM1024 = prove
 (`(!d z. (!i j n. i < 4 /\ j < 4 /\ n < 256
                  ==> mlkem_sample_ntt
                       (APPEND (FST(mlkem_g(APPEND d [word 4])))
                               [word j; word i]) n < &3329)
          ==> cry_KeyGen 4 2 (SOME d) (SOME z) = mlkem_keygen mlkem1024 d z) /\
   (!ek m. LENGTH ek = 1568 /\ LENGTH m = 32 /\
           (!i j n. i < 4 /\ j < 4 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 1536 32 ek) [word j; word i])
                         n < &3329)
           ==> mlkem_encaps mlkem1024 ek m =
               if cry_encapsulationKeyCheck 4 ek
               then SOME(cry_Encaps (:11) (:5) 4 2 2 ek (SOME m))
               else NONE) /\
   (!dk c. LENGTH dk = 3168 /\ LENGTH c = 1568 /\
           (!i j n. i < 4 /\ j < 4 /\ n < 256
                    ==> mlkem_sample_ntt
                         (APPEND (mlkem_slice 1536 32
                                   (mlkem_slice 1536 1568 dk))
                                 [word j; word i]) n < &3329)
           ==> mlkem_decaps mlkem1024 dk c =
               if cry_decapsulationInputCheck 4 dk c
               then SOME(cry_Decaps (:11) (:5) 4 2 2 dk c)
               else NONE)`,
  REWRITE_TAC[mlkem1024] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC CRY_KEYGEN THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`4`; `2`; `2`; `ek:byte list`; `m:byte list`]
           (INST_TYPE [`:11`,`:DU`; `:5`,`:DV`] CRY_ENCAPS));
    MP_TAC(SPECL [`4`; `2`; `2`; `dk:byte list`; `c:byte list`]
           (INST_TYPE [`:11`,`:DU`; `:5`,`:DV`] CRY_DECAPS))] THEN
  REWRITE_TAC[DIMINDEX_4; DIMINDEX_5; DIMINDEX_10; DIMINDEX_11] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

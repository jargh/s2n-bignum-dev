(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Probabilistic correctness of Lemire's algorithm, using the HOL Light      *)
(* Probability library. This is NOT needed by the machine-code proofs and   *)
(* is not part of the usual s2n-bignum build: it needs Probability/make.ml  *)
(* from the HOL Light distribution (which in turn uses Multivariate).       *)
(*                                                                           *)
(* The draws are modelled as random variables Y 0, Y 1, Y 2, ... with values *)
(* in [0,N) on an arbitrary probability space p, mutually independent and   *)
(* each uniformly distributed, i.e. taking each value k < N with             *)
(* probability 1/N. The step from counting to probability is then:           *)
(*                                                                           *)
(*   LEMIRE_TAPE_PROB: for any set T of "tapes" (lists of n values < N), the *)
(*   probability that the first n draws form a tape in T is |T| / N^n.       *)
(*                                                                           *)
(* Combined with the exact counts in common/lemire.ml this gives:            *)
(*                                                                           *)
(*   LEMIRE_PROB_FINITE: with n draws available the algorithm succeeds with  *)
(*   result r with probability (1 - ((N MOD s) / N)^n) / s, the same for     *)
(*   every r < s, so conditional on success the result is exactly uniform.   *)
(*                                                                           *)
(*   LEMIRE_PROB_UNIFORM: with an unbounded supply of draws, the result is   *)
(*   r with probability exactly 1 / s, for each r < s, and                   *)
(*                                                                           *)
(*   LEMIRE_PROB_TERMINATES: the loop terminates with probability 1.         *)
(* ========================================================================= *)

needs "Probability/make.ml";;
needs "common/lemire.ml";;

(*** common/lemire.ml prioritizes num; here we just annotate the reals ***)

(* ------------------------------------------------------------------------- *)
(* Cylinder sets, and the bridge between counting and probability.           *)
(* ------------------------------------------------------------------------- *)

let PROB_POINT_EVENT = prove
 (`!p:A prob_space X c.
        random_variable p X
        ==> {x | x IN prob_carrier p /\ X x = c} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `{c:real}`]
    DISTRIBUTION_IN_EVENTS) THEN
  ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CLOSED_IMP_BOREL_IN THEN
  REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_SING]);;

let LEMIRE_CYLINDER = prove
 (`!p:A prob_space Y N n b.
      (!m. mutually_indep_rv p (\i w. &(Y i w)) m) /\
      (!i k. k < N
             ==> prob p {w | w IN prob_carrier p /\ Y i w = k} = inv(&N)) /\
      (!i. i < n ==> b i < N)
      ==> {w | w IN prob_carrier p /\ !i. i < n ==> Y i w = b i}
          IN prob_events p /\
          prob p {w | w IN prob_carrier p /\ !i. i < n ==> Y i w = b i} =
          inv(&N) pow n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "indep")
   (CONJUNCTS_THEN2 (LABEL_TAC "unif") (LABEL_TAC "bnd"))) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)
   (SPEC `n:num` num_CASES) THENL
   [REWRITE_TAC[LT; real_pow] THEN
    REWRITE_TAC[SET_RULE `{x | x IN s} = s`] THEN
    REWRITE_TAC[PROB_SPACE; PROB_CARRIER_IN_EVENTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w | w IN prob_carrier p /\ !i. i < SUC m ==> Y i w = b i} =
    INTERS (IMAGE (\k. {x | x IN prob_carrier (p:A prob_space) /\
                            (\i w. &(Y i w)) k x = (\k. &(b k)) k}) (0..m))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; INTERS_IMAGE; IN_ELIM_THM; IN_NUMSEG;
                REAL_OF_NUM_EQ; LE_0; LT_SUC_LE] THEN
    MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  USE_THEN "indep" (MP_TAC o SPEC `m:num`) THEN
  REWRITE_TAC[mutually_indep_rv] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rv") (LABEL_TAC "prod")) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT; LE_0] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC PROB_POINT_EVENT THEN
    USE_THEN "rv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "prod" (MP_TAC o SPECL [`0..m`; `\k. &((b:num->num) k):real`]) THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET_REFL; NUMSEG_EMPTY; NOT_LT; LE_0] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `product (0..m) (\k:num. inv(&N))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN USE_THEN "unif" MATCH_MP_TAC THEN
      USE_THEN "bnd" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[PRODUCT_CONST_NUMSEG; ADD1; SUB_0]]]);;

let LIST_OF_SEQ_EQ_EL = prove
 (`!f n (l:A list).
        list_of_seq f n = l <=> LENGTH l = n /\ !i. i < n ==> f i = EL i l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[]]);;

let LEMIRE_TAPE_PROB = prove
 (`!p:A prob_space Y N n ts.
      (!m. mutually_indep_rv p (\i w. &(Y i w)) m) /\
      (!i k. k < N
             ==> prob p {w | w IN prob_carrier p /\ Y i w = k} = inv(&N)) /\
      ts SUBSET {l | LENGTH l = n /\ ALL (\w. w < N) l}
      ==> {w | w IN prob_carrier p /\ list_of_seq (\i. Y i w) n IN ts}
          IN prob_events p /\
          prob p {w | w IN prob_carrier p /\ list_of_seq (\i. Y i w) n IN ts} =
          &(CARD ts) * inv(&N) pow n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "indep")
   (CONJUNCTS_THEN2 (LABEL_TAC "unif") (LABEL_TAC "sub"))) THEN
  SUBGOAL_THEN `FINITE(ts:num list->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{l | LENGTH l = n /\ ALL (\w. w < N) l}` THEN
    ASM_REWRITE_TAC[REWRITE_RULE[HAS_SIZE] LEMIRE_TAPES_HAS_SIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN (ts:num list->bool)
        ==> {w | w IN prob_carrier (p:A prob_space) /\
                 !i. i < n ==> (Y:num->A->num) i w = EL i l}
            IN prob_events p /\
            prob p {w | w IN prob_carrier p /\ !i. i < n ==> Y i w = EL i l} =
            inv(&N) pow n`
  (LABEL_TAC "cyl") THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    MATCH_MP_TAC LEMIRE_CYLINDER THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sub" (MP_TAC o SPEC `l:num list` o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; GSYM ALL_EL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w | w IN prob_carrier p /\ list_of_seq (\i. (Y:num->A->num) i w) n IN
         (ts:num list->bool)} =
    UNIONS (IMAGE (\l. {w | w IN prob_carrier (p:A prob_space) /\
                            !i. i < n ==> Y i w = EL i l}) ts)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `list_of_seq (\i. (Y:num->A->num) i w) n` THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ];
      DISCH_THEN(X_CHOOSE_THEN `l:num list` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `list_of_seq (\i. (Y:num->A->num) i w) n = l`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[LIST_OF_SEQ_EQ_EL] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "sub" (MP_TAC o SPEC `l:num list` o REWRITE_RULE[SUBSET]) THEN
      ASM_SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PROB_FINITE_ADDITIVE_IMAGE o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`l1:num list`; `l2:num list`] THEN
    STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                               IN_ELIM_THM] THEN
    X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(l1:num list = l2)` THEN REWRITE_TAC[LIST_EQ] THEN
    USE_THEN "sub" (fun th -> MP_TAC(SPEC `l1:num list` (REWRITE_RULE[SUBSET] th)) THEN
                              MP_TAC(SPEC `l2:num list` (REWRITE_RULE[SUBSET] th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (ts:num list->bool) (\l. inv(&N) pow n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[SUM_CONST]]);;

(* ------------------------------------------------------------------------- *)
(* The probability of success with a given result, with n draws available.   *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_PROB_FINITE = prove
 (`!p:A prob_space Y N s n r.
      (!m. mutually_indep_rv p (\i w. &(Y i w)) m) /\
      (!i w. w IN prob_carrier p ==> Y i w < N) /\
      (!i k. k < N
             ==> prob p {w | w IN prob_carrier p /\ Y i w = k} = inv(&N)) /\
      ~(s = 0) /\ s <= N /\ r < s
      ==> {w | w IN prob_carrier p /\
               ~(lemire_draws N s n (\i. Y i w) = 0) /\
               lemire_result N s (\i. Y i w) = r} IN prob_events p /\
          prob p {w | w IN prob_carrier p /\
                      ~(lemire_draws N s n (\i. Y i w) = 0) /\
                      lemire_result N s (\i. Y i w) = r} =
          (&1 - (&(N MOD s) / &N) pow n) / &s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "indep")
   (CONJUNCTS_THEN2 (LABEL_TAC "range")
   (CONJUNCTS_THEN2 (LABEL_TAC "unif") STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC
   `S = {l | LENGTH l = n /\ ALL (\w. w < N) l /\
             ~(lemire_draws N s n (\i. EL i l) = 0) /\
             lemire_result N s (\i. EL i l) = r}` THEN
  SUBGOAL_THEN
   `{w | w IN prob_carrier p /\
         ~(lemire_draws N s n (\i. (Y:num->A->num) i w) = 0) /\
         lemire_result N s (\i. Y i w) = r} =
    {w | w IN prob_carrier p /\ list_of_seq (\i. Y i w) n IN S}`
  SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `w:A` THEN
    ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`N:num`; `s:num`; `n:num`;
                   `\i. EL i (list_of_seq (\i. (Y:num->A->num) i w) n)`;
                   `\i. (Y:num->A->num) i w`] LEMIRE_DRAWS_PREFIX) THEN
    SIMP_TAC[EL_LIST_OF_SEQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM ALL_EL] THEN
    SIMP_TAC[EL_LIST_OF_SEQ] THEN
    USE_THEN "range" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_CASES_TAC `lemire_draws N s n (\i. (Y:num->A->num) i w) = 0` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->num`; `N:num`; `n:num`;
                 `S:num list->bool`] LEMIRE_TAPE_PROB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) SUBST1_TAC) THEN
  MP_TAC(SPECL [`N:num`; `s:num`; `n:num`; `r:num`] LEMIRE_SUCCESS_COUNT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `real_of_num` o CONJUNCT2) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  SUBGOAL_THEN `~(&N:real = &0) /\ ~(&s:real = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_POW_INV] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* With an unbounded supply of draws: exact uniformity and termination.      *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_PROB_UNIFORM = prove
 (`!p:A prob_space Y N s r.
      (!m. mutually_indep_rv p (\i w. &(Y i w)) m) /\
      (!i w. w IN prob_carrier p ==> Y i w < N) /\
      (!i k. k < N
             ==> prob p {w | w IN prob_carrier p /\ Y i w = k} = inv(&N)) /\
      ~(s = 0) /\ s <= N /\ r < s
      ==> {w | w IN prob_carrier p /\
               (?i. lemire_accept N s (Y i w)) /\
               lemire_result N s (\i. Y i w) = r} IN prob_events p /\
          prob p {w | w IN prob_carrier p /\
                      (?i. lemire_accept N s (Y i w)) /\
                      lemire_result N s (\i. Y i w) = r} = inv(&s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `A = \n. {w | w IN prob_carrier p /\
                ~(lemire_draws N s n (\i. (Y:num->A->num) i w) = 0) /\
                lemire_result N s (\i. Y i w) = r}` THEN
  SUBGOAL_THEN
   `!n. (A:num->A->bool) n IN prob_events p /\
        prob p (A n) = (&1 - (&(N MOD s) / &N) pow n) / &s`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LEMIRE_PROB_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w | w IN prob_carrier p /\
         (?i. lemire_accept N s ((Y:num->A->num) i w)) /\
         lemire_result N s (\i. Y i w) = r} =
    UNIONS {(A:num->A->bool) n | n IN (:num)}`
  SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN
    REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `w:A` THEN
    MP_TAC(ISPECL [`N:num`; `s:num`; `\i. (Y:num->A->num) i w`]
      LEMIRE_DRAWS_EVENTUALLY) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `A:num->A->bool`]
    PROB_CONTINUITY_FROM_BELOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[LEMIRE_DRAWS_MONO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. (&1 - (&(N MOD s) / &N) pow n) / &s` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN `((\n. (&(N MOD s) / &N) pow n) ---> &0) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REALLIM_POWN THEN
    SUBGOAL_THEN `N MOD s < N /\ 0 < N` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`N:num`; `s:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s <= N` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LT_LDIV_EQ;
                 REAL_OF_NUM_LT; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`; `\n:num. &1 - (&(N MOD s) / &N) pow n`;
                 `\n:num. &s`; `&1 - &0`; `&s`] REALLIM_DIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[REALLIM_CONST];
      REWRITE_TAC[REALLIM_CONST];
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ]];
    REWRITE_TAC[REAL_SUB_RZERO; real_div; REAL_MUL_LID]]);;

let LEMIRE_PROB_TERMINATES = prove
 (`!p:A prob_space Y N s.
      (!m. mutually_indep_rv p (\i w. &(Y i w)) m) /\
      (!i w. w IN prob_carrier p ==> Y i w < N) /\
      (!i k. k < N
             ==> prob p {w | w IN prob_carrier p /\ Y i w = k} = inv(&N)) /\
      ~(s = 0) /\ s <= N
      ==> {w | w IN prob_carrier p /\ ?i. lemire_accept N s (Y i w)}
          IN prob_events p /\
          prob p {w | w IN prob_carrier p /\ ?i. lemire_accept N s (Y i w)} =
          &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{w | w IN prob_carrier p /\ ?i. lemire_accept N s ((Y:num->A->num) i w)} =
    UNIONS (IMAGE (\r. {w | w IN prob_carrier p /\
                            (?i. lemire_accept N s (Y i w)) /\
                            lemire_result N s (\i. Y i w) = r})
                  {r | r < s})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      EXISTS_TAC `lemire_result N s (\i. (Y:num->A->num) i w)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LEMIRE_RESULT_LT THEN ASM_SIMP_TAC[] THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r < s
        ==> {w | w IN prob_carrier p /\
                 (?i. lemire_accept N s ((Y:num->A->num) i w)) /\
                 lemire_result N s (\i. Y i w) = r} IN prob_events p /\
            prob p {w | w IN prob_carrier p /\
                        (?i. lemire_accept N s (Y i w)) /\
                        lemire_result N s (\i. Y i w) = r} = inv(&s)`
  (LABEL_TAC "each") THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC LEMIRE_PROB_UNIFORM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PROB_FINITE_ADDITIVE_IMAGE o
    lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {r | r < s} (\r:num. inv(&s))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ]]);;

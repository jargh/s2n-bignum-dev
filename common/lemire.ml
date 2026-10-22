(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mathematical model of Lemire's "nearly divisionless" algorithm for a     *)
(* uniformly distributed random integer in [0,s) from uniform words in      *)
(* [0,N), usually N = 2^64. See Daniel Lemire, "Fast Random Integer         *)
(* Generation in an Interval", ACM TOMACS 29(1), 2019 (arXiv 1805.10941).   *)
(*                                                                           *)
(* For a single draw x < N the algorithm forms x * s and accepts the draw   *)
(* if the low part (x * s) MOD N is >= N MOD s, in which case the output is *)
(* the high part (x * s) DIV N. The key fact (Lemma 4.1 in the paper) is    *)
(* that each output r < s arises from exactly N DIV s accepted draws, and   *)
(* this is proved here in the form of an explicit bijection between the    *)
(* accepted draws and pairs (r,j) with r < s and j < N DIV s, following the *)
(* SPARK and Verus formalizations in awslabs/LibFormalPQC (lemire/), whose  *)
(* "First", "Index" and "Decode" are lemire_first and its inverse here.     *)
(*                                                                           *)
(* This file only uses core HOL Light, so it is shared by the machine-code  *)
(* proofs and by the probabilistic analysis in common/lemire_probability.ml *)
(* ========================================================================= *)

(*** Everything here is natural-number arithmetic. Make sure the parser
 *** defaults to num even if (as with the Probability library) a loaded
 *** library has prioritized real or vector arithmetic.
 ***)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* A single draw.                                                            *)
(* ------------------------------------------------------------------------- *)

let lemire_accept = new_definition
 `lemire_accept N s x <=> N MOD s <= (x * s) MOD N`;;

let lemire_output = new_definition
 `lemire_output N s x = (x * s) DIV N`;;

(*** The smallest accepted draw with output r, as in SPARK's "First" ***)

let lemire_first = new_definition
 `lemire_first N s r = (r * N + N MOD s + s - 1) DIV s`;;

let LEMIRE_FIRST_BOUNDS = prove
 (`!N s r. ~(s = 0)
           ==> r * N + N MOD s <= lemire_first N s r * s /\
               lemire_first N s r * s < r * N + N MOD s + s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[lemire_first] THEN
  MP_TAC(SPECL [`r * N + N MOD s + s - 1`; `s:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(*** SPARK's Lemma_Encode: an accepted draw is in [first(r),first(r)+N/s) ***)

let LEMIRE_ENCODE = prove
 (`!N s x. ~(s = 0) /\ x < N /\ lemire_accept N s x
           ==> lemire_output N s x < s /\
               lemire_first N s (lemire_output N s x) <= x /\
               x < lemire_first N s (lemire_output N s x) + N DIV s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[lemire_accept]) THEN
  REWRITE_TAC[lemire_output] THEN
  ABBREV_TAC `r = (x * s) DIV N` THEN
  MP_TAC(SPECL [`N:num`; `s:num`; `r:num`] LEMIRE_FIRST_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f = lemire_first N s r` THEN
  MP_TAC(SPECL [`x * s`; `N:num`] DIVISION) THEN
  MP_TAC(SPECL [`N:num`; `s:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(MESON[LT_MULT_RCANCEL] `r * N < s * N ==> r < s`) THEN
    MP_TAC(SPECL [`x:num`; `N:num`; `s:num`] LT_MULT_RCANCEL) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(MESON[LT_MULT_RCANCEL; ARITH_RULE `f < x + 1 <=> f <= x`]
     `f * s < (x + 1) * s ==> f <= x`) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(MESON[LT_MULT_RCANCEL] `x * s < (f + c) * s ==> x < f + c`) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN ASM_ARITH_TAC]);;

(*** SPARK's Lemma_Decode: first(r) + j is an accepted draw with output r ***)

let LEMIRE_DECODE = prove
 (`!N s r j. ~(s = 0) /\ r < s /\ j < N DIV s
             ==> lemire_first N s r + j < N /\
                 lemire_accept N s (lemire_first N s r + j) /\
                 lemire_output N s (lemire_first N s r + j) = r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `s:num`; `r:num`] LEMIRE_FIRST_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f = lemire_first N s r` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `s:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(j + 1) * s <= N DIV s * s` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(r + 1) * N <= s * N` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * N + N MOD s <= (f + j) * s /\ (f + j) * s < r * N + N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_ADD_DISTRIB; MULT_CLAUSES]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`(f + j) * s`; `N:num`; `r:num`; `(f + j) * s - r * N`]
    DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[lemire_accept; lemire_output] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC(MESON[LT_MULT_RCANCEL] `x * s < N * s ==> x < N`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_ADD_DISTRIB; MULT_CLAUSES]) THEN
  ASM_ARITH_TAC);;

(*** The bijection between accepted draws and pairs (r,j) ***)

let LEMIRE_BIJECTION = prove
 (`!N s. ~(s = 0)
         ==> BIJ (\x. lemire_output N s x,
                      x - lemire_first N s (lemire_output N s x))
                 {x | x < N /\ lemire_accept N s x}
                 ({r | r < s} CROSS {j | j < N DIV s})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BIJ; INJ; SURJ; IN_ELIM_THM; IN_CROSS; FORALL_PAIR_THM;
              EXISTS_PAIR_THM; PAIR_EQ] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ (a ==> c) ==> (a /\ b) /\ (a /\ c)`) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `s:num`; `x:num`] LEMIRE_ENCODE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `s:num`; `x:num`] LEMIRE_ENCODE) THEN
    MP_TAC(SPECL [`N:num`; `s:num`; `y:num`] LEMIRE_ENCODE) THEN
    UNDISCH_TAC `x - lemire_first N s (lemire_output N s x) =
                 y - lemire_first N s (lemire_output N s y)` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`r:num`; `j:num`] THEN STRIP_TAC THEN
    EXISTS_TAC `lemire_first N s r + j` THEN
    ASM_SIMP_TAC[LEMIRE_DECODE] THEN ARITH_TAC]);;

(*** Hence Lemma 4.1: each output arises from exactly N DIV s draws ***)

let LEMIRE_FIBER = prove
 (`!N s r. ~(s = 0) /\ r < s
           ==> {x | x < N /\ lemire_accept N s x /\ lemire_output N s x = r} =
               IMAGE (\j. lemire_first N s r + j) {j | j < N DIV s}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:num` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN MP_TAC(SPECL [`N:num`; `s:num`; `x:num`] LEMIRE_ENCODE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `x - lemire_first N s r` THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[LEMIRE_DECODE]]);;

let LEMIRE_COUNT = prove
 (`!N s r. ~(s = 0) /\ r < s
           ==> CARD {x | x < N /\ lemire_accept N s x /\
                         lemire_output N s x = r} = N DIV s`,
  SIMP_TAC[LEMIRE_FIBER] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; EQ_ADD_LCANCEL] THEN
  MESON_TAC[]);;

let LEMIRE_ACCEPT_COUNT = prove
 (`!N s. ~(s = 0) ==> CARD {x | x < N /\ lemire_accept N s x} = s * N DIV s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `s:num`] LEMIRE_BIJECTION) THEN
  ASM_REWRITE_TAC[BIJ; INJ; SURJ] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD({r | r < s} CROSS {j | j < N DIV s})` THEN
  CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[CARD_CROSS; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\x. lemire_output N s x,
                              x - lemire_first N s (lemire_output N s x))
                         {x | x < N /\ lemire_accept N s x})` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < N}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]]);;

let LEMIRE_REJECT_COUNT = prove
 (`!N s. ~(s = 0) ==> CARD {x | x < N /\ ~lemire_accept N s x} = N MOD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | x < N /\ ~lemire_accept N s x} =
                {x | x < N} DIFF {x | x < N /\ lemire_accept N s x}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[CARD_DIFF; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[LEMIRE_ACCEPT_COUNT; CARD_NUMSEG_LT] THEN
  MP_TAC(SPECL [`N:num`; `s:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The rejection loop over a sequence of draws x(0), x(1), x(2), ...        *)
(* lemire_draws N s n x is the number of draws consumed when at most n are  *)
(* available, or 0 if all of the first n draws are rejected, and the result *)
(* is the output from the first accepted draw.                               *)
(* ------------------------------------------------------------------------- *)

let lemire_draws = new_definition
 `lemire_draws N s n (x:num->num) =
    if ?i. i < n /\ lemire_accept N s (x i)
    then (minimal i. lemire_accept N s (x i)) + 1 else 0`;;

let lemire_result = new_definition
 `lemire_result N s (x:num->num) =
    lemire_output N s (x(minimal i. lemire_accept N s (x i)))`;;

let LEMIRE_DRAWS_0 = prove
 (`!N s x. lemire_draws N s 0 x = 0`,
  REWRITE_TAC[lemire_draws; LT]);;

let LEMIRE_DRAWS_NONZERO = prove
 (`!N s n x. ~(lemire_draws N s n x = 0) ==> ?i. lemire_accept N s (x i)`,
  REWRITE_TAC[lemire_draws] THEN MESON_TAC[]);;

let MINIMAL_SHIFT = prove
 (`!P:num->bool. ~P 0 /\ (?i. P i)
                 ==> (minimal) P = SUC((minimal) (\i. P(SUC i)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  SUBGOAL_THEN `?i. (\i. P(SUC i)) i` MP_TAC THENL
   [REWRITE_TAC[] THEN ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC]);;

let EXISTS_LT_SUC_SHIFT = prove
 (`!P n. (?i. i < SUC n /\ P i) <=> P 0 \/ (?j. j < n /\ P(SUC j))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` MP_TAC) THEN
    STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
    REWRITE_TAC[LT_SUC] THEN MESON_TAC[];
    MESON_TAC[LT_SUC; LT_0]]);;

let LEMIRE_DRAWS_SHIFT = prove
 (`!N s n x.
      lemire_draws N s (SUC n) x =
      if lemire_accept N s (x 0) then 1
      else if lemire_draws N s n (\i. x(SUC i)) = 0 then 0
      else lemire_draws N s n (\i. x(SUC i)) + 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lemire_draws; EXISTS_LT_SUC_SHIFT] THEN
  ASM_CASES_TAC `lemire_accept N s (x 0)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(ARITH_RULE `n = 0 ==> n + 1 = 1`) THEN
    MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[LT];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `~(n + 1 = 0)`] THEN
  MP_TAC(ISPEC `\i:num. lemire_accept N s ((x:num->num) i)` MINIMAL_SHIFT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

let LEMIRE_RESULT_SHIFT = prove
 (`!N s x. (?i. lemire_accept N s (x i))
           ==> lemire_result N s x =
               if lemire_accept N s (x 0) then lemire_output N s (x 0)
               else lemire_result N s (\i. x(SUC i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lemire_result] THEN
  COND_CASES_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
    ASM_REWRITE_TAC[LT];
    MP_TAC(ISPEC `\i:num. lemire_accept N s ((x:num->num) i)`
      MINIMAL_SHIFT) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(*** The same two facts for a list of draws with a new one at the front ***)

let LEMIRE_CONS = prove
 (`!N s n w t.
    lemire_draws N s (SUC n) (\i. EL i (CONS w t)) =
     (if lemire_accept N s w then 1
      else if lemire_draws N s n (\i. EL i t) = 0 then 0
      else lemire_draws N s n (\i. EL i t) + 1) /\
    (~(lemire_draws N s (SUC n) (\i. EL i (CONS w t)) = 0)
     ==> lemire_result N s (\i. EL i (CONS w t)) =
         if lemire_accept N s w then lemire_output N s w
         else lemire_result N s (\i. EL i t))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LEMIRE_DRAWS_SHIFT; EL; HD; TL; ETA_AX];
    DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP LEMIRE_DRAWS_NONZERO) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LEMIRE_RESULT_SHIFT th]) THEN
    REWRITE_TAC[EL; HD; TL; ETA_AX]]);;

(*** Characterizing the outcome of the loop by the first accepted draw ***)

let LEMIRE_DRAWS_RESULT_FIRST = prove
 (`!N s n (x:num->num) k.
        k < n /\ lemire_accept N s (x k) /\
        (!j. j < k ==> ~lemire_accept N s (x j))
        ==> lemire_draws N s n x = k + 1 /\
            lemire_result N s x = lemire_output N s (x k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(minimal i. lemire_accept N s ((x:num->num) i)) = k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lemire_draws; lemire_result] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let LEMIRE_DRAWS_NONE = prove
 (`!N s n (x:num->num).
        (!j. j < n ==> ~lemire_accept N s (x j))
        ==> lemire_draws N s n x = 0`,
  REWRITE_TAC[lemire_draws] THEN MESON_TAC[]);;

let LEMIRE_ACCEPT_FAST = prove
 (`!N s x. ~(s = 0) /\ s <= (x * s) MOD N ==> lemire_accept N s x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lemire_accept] THEN
  MP_TAC(SPECL [`N:num`; `s:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(*** The loop only looks at the draws it actually consumes ***)

let LEMIRE_DRAWS_PREFIX = prove
 (`!N s n (x:num->num) y.
        (!i. i < n ==> x i = y i)
        ==> lemire_draws N s n x = lemire_draws N s n y /\
            (~(lemire_draws N s n x = 0)
             ==> lemire_result N s x = lemire_result N s y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "agree") THEN
  ASM_CASES_TAC `?i. i < n /\ lemire_accept N s ((x:num->num) i)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `lemire_draws N s n (x:num->num) = 0 /\
                  lemire_draws N s n (y:num->num) = 0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LEMIRE_DRAWS_NONE THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THENL
       [ASM_MESON_TAC[];
        REMOVE_THEN "agree" (MP_TAC o SPEC `j:num`) THEN ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `?i. lemire_accept N s ((x:num->num) i)` MP_TAC THENL
   [ASM_MESON_TAC[]; GEN_REWRITE_TAC LAND_CONV [MINIMAL]] THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `k = minimal i. lemire_accept N s ((x:num->num) i)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")) THEN
  SUBGOAL_THEN `k < n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o
      check (is_exists o concl)) THEN
    TRANS_TAC LET_TRANS `i:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:num->num) k = x k` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "agree" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < k ==> ~lemire_accept N s ((y:num->num) j)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:num->num) j = x j` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "agree" MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      USE_THEN "min" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `s:num`; `n:num`; `x:num->num`; `k:num`]
    LEMIRE_DRAWS_RESULT_FIRST) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `s:num`; `n:num`; `y:num->num`; `k:num`]
    LEMIRE_DRAWS_RESULT_FIRST) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[]);
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[]);;

let LEMIRE_DRAWS_EVENTUALLY = prove
 (`!N s (x:num->num).
        (?i. lemire_accept N s (x i)) <=>
        (?n. ~(lemire_draws N s n x = 0))`,
  REWRITE_TAC[lemire_draws] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN EXISTS_TAC `i + 1` THEN
    COND_CASES_TAC THENL [ARITH_TAC; ASM_MESON_TAC[ARITH_RULE `i < i + 1`]];
    MESON_TAC[]]);;

let LEMIRE_DRAWS_MONO = prove
 (`!N s n (x:num->num).
        ~(lemire_draws N s n x = 0) ==> ~(lemire_draws N s (SUC n) x = 0)`,
  REWRITE_TAC[lemire_draws] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  ASM_MESON_TAC[LT_SUC_LE; LT_IMP_LE]);;

let LEMIRE_RESULT_LT = prove
 (`!N s (x:num->num).
        ~(s = 0) /\ (!i. x i < N) /\ (?i. lemire_accept N s (x i))
        ==> lemire_result N s x < s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN REWRITE_TAC[lemire_result] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `s:num`;
                `(x:num->num)(minimal i. lemire_accept N s (x i))`]
    LEMIRE_ENCODE) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Counting over all N^n "tapes" of n draws, i.e. lists of length n with    *)
(* entries < N. Exactly (N MOD s)^n tapes are rejected throughout, and for  *)
(* each r < s there are exactly (N^n - (N MOD s)^n) / s tapes for which the *)
(* loop succeeds with result r. In particular conditional on success the    *)
(* result is exactly uniformly distributed over [0,s).                      *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CONS_CROSS = prove
 (`!(A:A->bool) B m n.
      A HAS_SIZE m /\ B HAS_SIZE n
      ==> {CONS w l | w IN A /\ l IN B} HAS_SIZE (m * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{CONS w l | w IN A /\ l IN B} =
                IMAGE (\(w:A,l). CONS w l) (A CROSS B)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_CROSS; EXISTS_PAIR_THM;
                IN_ELIM_THM] THEN
    MESON_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_SIMP_TAC[HAS_SIZE_CROSS; FORALL_PAIR_THM; CONS_11; PAIR_EQ]]);;

let LENGTH_SUC_ALL_SET = prove
 (`!P Q n. {l:A list | LENGTH l = SUC n /\ ALL Q l /\ P l} =
           {CONS w l | w IN {w | Q w} /\
                       l IN {l | LENGTH l = n /\ ALL Q l /\ P(CONS w l)}}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[LENGTH_EQ_CONS] THEN MESON_TAC[ALL]);;

let LEMIRE_TAPES_HAS_SIZE = prove
 (`!N n. {l | LENGTH l = n /\ ALL (\w. w < N) l} HAS_SIZE N EXP n`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH_EQ_NIL; EXP] THEN
    SUBGOAL_THEN `{l:num list | l = [] /\ ALL (\w. w < N) l} = {[]}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN MESON_TAC[ALL];
      REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING]];
    MP_TAC(ISPECL [`\l:num list. T`; `\w:num. w < N`; `n:num`]
      LENGTH_SUC_ALL_SET) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EXP] THEN MATCH_MP_TAC HAS_SIZE_CONS_CROSS THEN
    ASM_REWRITE_TAC[HAS_SIZE_NUMSEG_LT]]);;

let LEMIRE_COND_0 = prove
 (`!a b c. (if a then 1 else if b then 0 else c + 1) = 0 <=> ~a /\ b`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let LEMIRE_FAIL_CONS = prove
 (`!N s n l.
    (LENGTH l = SUC n /\ ALL (\w. w < N) l /\
     lemire_draws N s (SUC n) (\i. EL i l) = 0) <=>
    ?w t. (w < N /\ ~lemire_accept N s w) /\
          (LENGTH t = n /\ ALL (\w. w < N) t /\
           lemire_draws N s n (\i. EL i t) = 0) /\
          l = CONS w t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_CONS] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `w:num` (X_CHOOSE_THEN `t:num list` STRIP_ASSUME_TAC))
     MP_TAC) THEN
    ASM_REWRITE_TAC[ALL; LEMIRE_CONS; LEMIRE_COND_0] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`w:num`; `t:num list`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w:num`; `t:num list`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ALL; LEMIRE_CONS; LEMIRE_COND_0; CONS_11] THEN
    MAP_EVERY EXISTS_TAC [`w:num`; `t:num list`] THEN ASM_REWRITE_TAC[]]);;

let LEMIRE_SUCCESS_CONS = prove
 (`!N s n r l.
    (LENGTH l = SUC n /\ ALL (\w. w < N) l /\
     ~(lemire_draws N s (SUC n) (\i. EL i l) = 0) /\
     lemire_result N s (\i. EL i l) = r) <=>
    (?w t. (w < N /\ lemire_accept N s w /\ lemire_output N s w = r) /\
           (LENGTH t = n /\ ALL (\w. w < N) t) /\
           l = CONS w t) \/
    (?w t. (w < N /\ ~lemire_accept N s w) /\
           (LENGTH t = n /\ ALL (\w. w < N) t /\
            ~(lemire_draws N s n (\i. EL i t) = 0) /\
            lemire_result N s (\i. EL i t) = r) /\
           l = CONS w t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_CONS] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `w:num` (X_CHOOSE_THEN `t:num list` STRIP_ASSUME_TAC))
     MP_TAC) THEN
    ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP (CONJUNCT2(SPEC_ALL LEMIRE_CONS)) th]) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(lemire_draws N s (SUC n) (\i. EL i (CONS w t)) = 0)` THEN
    REWRITE_TAC[CONJUNCT1(SPEC_ALL LEMIRE_CONS); LEMIRE_COND_0;
                DE_MORGAN_THM] THEN
    REWRITE_TAC[CONS_11; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_CASES_TAC `lemire_accept N s w` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(if lemire_accept N s w then lemire_output N s w
                  else lemire_result N s (\i. EL i t)) = r` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:num list` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
    (CONJ_TAC THENL
      [MAP_EVERY EXISTS_TAC [`w:num`; `t:num list`] THEN ASM_REWRITE_TAC[];
       ALL_TAC]) THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    (CONJ_TAC THENL
      [ASM_REWRITE_TAC[CONJUNCT1(SPEC_ALL LEMIRE_CONS); LEMIRE_COND_0;
                       ADD_EQ_0; ARITH_EQ];
       ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      REWRITE_TAC[MATCH_MP (CONJUNCT2(SPEC_ALL LEMIRE_CONS)) th]) THEN
    ASM_REWRITE_TAC[]]);;

let LEMIRE_FAIL_HAS_SIZE = prove
 (`!N s n. ~(s = 0)
           ==> {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                    lemire_draws N s n (\i. EL i l) = 0}
               HAS_SIZE (N MOD s) EXP n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[LENGTH_EQ_NIL; EXP; LEMIRE_DRAWS_0] THEN
    SUBGOAL_THEN `{l:num list | l = [] /\ ALL (\w. w < N) l} = {[]}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN MESON_TAC[ALL];
      REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING]];
    ALL_TAC] THEN
  REWRITE_TAC[LEMIRE_FAIL_CONS; EXP] THEN
  SUBGOAL_THEN
   `{l | ?w t. (w < N /\ ~lemire_accept N s w) /\
               (LENGTH t = n /\ ALL (\w. w < N) t /\
                lemire_draws N s n (\i. EL i t) = 0) /\
               l = CONS w t} =
    {CONS w t | w IN {w | w < N /\ ~lemire_accept N s w} /\
                t IN {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                          lemire_draws N s n (\i. EL i l) = 0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_CONS_CROSS THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{w:num | w < N}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ASM_SIMP_TAC[LEMIRE_REJECT_COUNT]]);;

let LEMIRE_SUCCESS_COUNT = prove
 (`!N s n r.
      ~(s = 0) /\ r < s
      ==> FINITE {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                      ~(lemire_draws N s n (\i. EL i l) = 0) /\
                      lemire_result N s (\i. EL i l) = r} /\
          s * CARD {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                        ~(lemire_draws N s n (\i. EL i l) = 0) /\
                        lemire_result N s (\i. EL i l) = r} +
          (N MOD s) EXP n = N EXP n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  (MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{l | LENGTH l = SUC n /\ ALL (\w. w < N) l} UNION
                 {l | LENGTH l = 0 /\ ALL (\w. w < N) l}` THEN
     REWRITE_TAC[FINITE_UNION] THEN
     REWRITE_TAC[REWRITE_RULE[HAS_SIZE] LEMIRE_TAPES_HAS_SIZE] THEN
     SET_TAC[];
     DISCH_TAC]) THENL
   [REWRITE_TAC[LEMIRE_DRAWS_0; EXP; EMPTY_GSPEC; CARD_CLAUSES] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEMIRE_SUCCESS_CONS] THEN
  REWRITE_TAC[SET_RULE `{x:A | P x \/ Q x} = {x | P x} UNION {x | Q x}`] THEN
  SUBGOAL_THEN
   `{l | ?w t. (w < N /\ lemire_accept N s w /\ lemire_output N s w = r) /\
               (LENGTH t = n /\ ALL (\w. w < N) t) /\ l = CONS w t} =
    {CONS w t | w IN {w | w < N /\ lemire_accept N s w /\
                          lemire_output N s w = r} /\
                t IN {l | LENGTH l = n /\ ALL (\w. w < N) l}} /\
    {l | ?w t. (w < N /\ ~lemire_accept N s w) /\
               (LENGTH t = n /\ ALL (\w. w < N) t /\
                ~(lemire_draws N s n (\i. EL i t) = 0) /\
                lemire_result N s (\i. EL i t) = r) /\
               l = CONS w t} =
    {CONS w t | w IN {w | w < N /\ ~lemire_accept N s w} /\
                t IN {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                          ~(lemire_draws N s n (\i. EL i l) = 0) /\
                          lemire_result N s (\i. EL i l) = r}}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                       ~(lemire_draws N s n (\i. EL i l) = 0) /\
                       lemire_result N s (\i. EL i l) = r}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{w | w < N /\ lemire_accept N s w /\ lemire_output N s w = r}
    HAS_SIZE N DIV s /\
    {w | w < N /\ ~lemire_accept N s w} HAS_SIZE N MOD s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; LEMIRE_COUNT; LEMIRE_REJECT_COUNT] THEN
    CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{w:num | w < N}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{w | w < N /\ lemire_accept N s w /\ lemire_output N s w = r}`;
    `{l | LENGTH l = n /\ ALL (\w. w < N) l}`;
    `N DIV s`; `N EXP n`] HAS_SIZE_CONS_CROSS) THEN
  MP_TAC(ISPECL
   [`{w | w < N /\ ~lemire_accept N s w}`; `S:num list->bool`;
    `N MOD s`; `CARD(S:num list->bool)`] HAS_SIZE_CONS_CROSS) THEN
  ASM_REWRITE_TAC[LEMIRE_TAPES_HAS_SIZE; HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNION o
    rand o lhand o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    MESON_TAC[CONS_11];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `s:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `s * CARD(S:num list->bool) + (N MOD s) EXP n = N EXP n` THEN
  REWRITE_TAC[EXP] THEN CONV_TAC NUM_RING);;

(*** Exact uniformity conditional on success: the same count for each r ***)

let LEMIRE_SUCCESS_UNIFORM = prove
 (`!N s n r1 r2.
      ~(s = 0) /\ r1 < s /\ r2 < s
      ==> CARD {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                    ~(lemire_draws N s n (\i. EL i l) = 0) /\
                    lemire_result N s (\i. EL i l) = r1} =
          CARD {l | LENGTH l = n /\ ALL (\w. w < N) l /\
                    ~(lemire_draws N s n (\i. EL i l) = 0) /\
                    lemire_result N s (\i. EL i l) = r2}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `s:num`; `n:num`; `r1:num`] LEMIRE_SUCCESS_COUNT) THEN
  MP_TAC(SPECL [`N:num`; `s:num`; `n:num`; `r2:num`] LEMIRE_SUCCESS_COUNT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
  MATCH_MP_TAC(MESON[EQ_MULT_LCANCEL]
   `~(s = 0) /\ s * a = s * b ==> a:num = b`) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`t = (N MOD s) EXP n`; `m = N EXP n`] THEN
  ASM_ARITH_TAC);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Facts about the specification of Huffman-coded literals in the Zstandard  *)
(* format in rfc8878.ml, for the proofs about zstd's code.                   *)
(* ========================================================================= *)

needs "common/rfc8878.ml";;

(* ------------------------------------------------------------------------- *)
(* The canonical prefix code of a list of weights ws: the symbols present    *)
(* (with a nonzero weight) in the order huf_before, of weight and then of    *)
(* symbol, and the first of the states that each is given, huf_start, the    *)
(* states being given out in that order, 2^(w - 1) to a symbol of weight w.  *)
(* ------------------------------------------------------------------------- *)

let huf_present = new_definition
 `huf_present (ws:num list) = {t | t < LENGTH ws /\ ~(EL t ws = 0)}`;;

let huf_before = new_definition
 `huf_before (ws:num list) t s <=>
    EL t ws < EL s ws \/ EL t ws = EL s ws /\ t < s`;;

let huf_start = new_definition
 `huf_start (ws:num list) s =
    nsum {t | t IN huf_present ws /\ huf_before ws t s}
         (\t. 2 EXP (EL t ws - 1))`;;

let huf_total = new_definition
 `huf_total (ws:num list) = nsum (huf_present ws) (\t. 2 EXP (EL t ws - 1))`;;

let HUF_CODE_START = prove
 (`!ws s. huf_code ws s = huf_start ws s DIV 2 EXP (EL s ws - 1)`,
  REWRITE_TAC[huf_code; huf_start; huf_present; huf_before; IN_ELIM_THM;
              CONJ_ASSOC]);;

let FINITE_HUF_PRESENT = prove
 (`!ws. FINITE(huf_present ws)`,
  GEN_TAC THEN REWRITE_TAC[huf_present] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:num | t < LENGTH(ws:num list)}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]);;

let HUF_BEFORE_IRREFL = prove
 (`!ws t. ~huf_before ws t t`,
  REWRITE_TAC[huf_before; LT_REFL]);;

let HUF_BEFORE_TRANS = prove
 (`!ws r s t. huf_before ws r s /\ huf_before ws s t ==> huf_before ws r t`,
  REWRITE_TAC[huf_before] THEN ARITH_TAC);;

let HUF_BEFORE_TOTAL = prove
 (`!ws s t. ~(s = t) ==> huf_before ws s t \/ huf_before ws t s`,
  REWRITE_TAC[huf_before] THEN ARITH_TAC);;

(* The states of a symbol come after those of the symbols before it, and     *)
(* before the end of all of them.                                            *)

let HUF_START_INSERT = prove
 (`!ws s. nsum {u | u IN huf_present ws /\ huf_before ws u s}
               (\t. 2 EXP (EL t ws - 1)) + 2 EXP (EL s ws - 1) =
          nsum (s INSERT {u | u IN huf_present ws /\ huf_before ws u s})
               (\t. 2 EXP (EL t ws - 1))`,
  SIMP_TAC[NSUM_CLAUSES; FINITE_RESTRICT; FINITE_HUF_PRESENT] THEN
  REWRITE_TAC[IN_ELIM_THM; HUF_BEFORE_IRREFL] THEN ARITH_TAC);;

let HUF_START_STEP = prove
 (`!ws s t. t IN huf_present ws /\ huf_before ws t s
            ==> huf_start ws t + 2 EXP (EL t ws - 1) <= huf_start ws s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_start; HUF_START_INSERT] THEN
  MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
  SIMP_TAC[FINITE_RESTRICT; FINITE_HUF_PRESENT] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[HUF_BEFORE_TRANS]);;

let HUF_START_END = prove
 (`!ws s. s IN huf_present ws
          ==> huf_start ws s + 2 EXP (EL s ws - 1) <= huf_total ws`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[huf_start; huf_total; HUF_START_INSERT] THEN
  MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_HUF_PRESENT] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* So the ranges of states of the symbols are disjoint and cover all the     *)
(* states.                                                                   *)

let HUF_INTERVALS_DISJOINT = prove
 (`!ws s t y.
        s IN huf_present ws /\ t IN huf_present ws /\
        huf_start ws s <= y /\ y < huf_start ws s + 2 EXP (EL s ws - 1) /\
        huf_start ws t <= y /\ y < huf_start ws t + 2 EXP (EL t ws - 1)
        ==> s = t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:num = t` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o SPEC `ws:num list` o
              MATCH_MP HUF_BEFORE_TOTAL) THENL
   [MP_TAC(SPECL [`ws:num list`; `t:num`; `s:num`] HUF_START_STEP);
    MP_TAC(SPECL [`ws:num list`; `s:num`; `t:num`] HUF_START_STEP)] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let HUF_INTERVALS_COVER = prove
 (`!ws y. y < huf_total ws
          ==> ?s. s IN huf_present ws /\ huf_start ws s <= y /\
                  y < huf_start ws s + 2 EXP (EL s ws - 1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `iv = \s. {y | huf_start ws s <= y /\
                            y < huf_start ws s + 2 EXP (EL s ws - 1)}` THEN
  SUBGOAL_THEN `UNIONS (IMAGE iv (huf_present ws)) = {y | y < huf_total ws}`
  MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "iv" THEN REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[HUF_START_END; LTE_TRANS];
      W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNIONS_IMAGE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FINITE_HUF_PRESENT] THEN EXPAND_TAC "iv" THEN
        CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{y:num | y < huf_start ws t + 2 EXP (EL t ws - 1)}` THEN
          REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
          REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
          ASM_MESON_TAC[HUF_INTERVALS_DISJOINT]];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_NUMSEG_LT; huf_total] THEN
        MATCH_MP_TAC NSUM_EQ THEN EXPAND_TAC "iv" THEN REWRITE_TAC[] THEN
        X_GEN_TAC `t:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN
         `{y | huf_start ws t <= y /\
               y < huf_start ws t + 2 EXP (EL t ws - 1)} =
          IMAGE (\i. huf_start ws t + i) {i | i < 2 EXP (EL t ws - 1)}`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN GEN_TAC THEN
          EQ_TAC THENL
           [DISCH_TAC THEN EXISTS_TAC `x - huf_start ws t` THEN ASM_ARITH_TAC;
            STRIP_TAC THEN ASM_ARITH_TAC];
          SIMP_TAC[CARD_IMAGE_INJ; FINITE_NUMSEG_LT; EQ_ADD_LCANCEL;
                   CARD_NUMSEG_LT]]]];
    REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "iv" THEN REWRITE_TAC[IN_ELIM_THM]]);;

(* For a complete code, the first state of a symbol of weight w is a         *)
(* multiple of 2^(w - 1), so that its code is a prefix of its states.        *)

let HUF_START_ALIGNED = prove
 (`!ws ml s. huf_total ws = 2 EXP ml /\ s IN huf_present ws /\
             EL s ws <= ml + 1
             ==> 2 EXP (EL s ws - 1) divides huf_start ws s`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = huf_present ws` THEN
  ABBREV_TAC `f = \t. 2 EXP (EL t ws - 1)` THEN
  SUBGOAL_THEN
   `huf_start ws s = nsum {u | u IN P /\ EL u ws < EL s ws} f +
                     nsum {u | u IN P /\ EL u ws = EL s ws /\ u < s} f`
  SUBST1_TAC THENL
   [REWRITE_TAC[huf_start; huf_before] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "f" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) (GSYM NSUM_UNION) o rand o snd) THEN
    EXPAND_TAC "P" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_HUF_PRESENT] THEN
    ANTS_TAC THENL [SET_TAC[LT_REFL]; DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC DIVIDES_NSUM THEN EXPAND_TAC "P" THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_HUF_PRESENT; IN_ELIM_THM] THEN
    EXPAND_TAC "f" THEN SIMP_TAC[DIVIDES_REFL]] THEN
  MATCH_MP_TAC DIVIDES_ADD_REVR THEN
  EXISTS_TAC `nsum {u | u IN P /\ ~(EL u ws < EL s ws)} f` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIVIDES_NSUM THEN EXPAND_TAC "P" THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_HUF_PRESENT; IN_ELIM_THM] THEN
    EXPAND_TAC "f" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `nsum {u | u IN P /\ ~(EL u ws < EL s ws)} f +
                nsum {u | u IN P /\ EL u ws < EL s ws} f = 2 EXP ml`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[huf_total] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) (GSYM NSUM_UNION) o lhand o snd) THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_HUF_PRESENT] THEN
    ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `{u | u IN huf_present ws /\ ~(EL u ws < EL s ws)} UNION
      {u | u IN huf_present ws /\ EL u ws < EL s ws} = huf_present ws`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[GSYM huf_total]];
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Numbers read from the bits.                                               *)
(* ------------------------------------------------------------------------- *)

let ZSTD_BITS_BOUND = prove
 (`!l p n. zstd_bits l p n < 2 EXP n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[zstd_bits; EXP; ARITH] THEN GEN_TAC THEN
  MP_TAC(SPEC `zstd_bit l p` BITVAL_BOUND) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p + 1`) THEN ARITH_TAC);;

let ZSTD_BITS_ADD = prove
 (`!l p m n.
        zstd_bits l p (m + n) =
        zstd_bits l p m + 2 EXP m * zstd_bits l (p + m) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[zstd_bits; ADD_CLAUSES; MULT_CLAUSES; EXP] THEN
  REWRITE_TAC[ARITH_RULE `SUC(p + m) = (p + 1) + m`] THEN ARITH_TAC);;

let ZSTD_DIVMOD_ADD_MULT = prove
 (`!a b n. a < n ==> (a + n * b) DIV n = b /\ (a + n * b) MOD n = a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_ARITH_TAC);;

let ZSTD_BITS_SPLIT = prove
 (`!l p n k.
        k <= n
        ==> zstd_bits l p n MOD 2 EXP k = zstd_bits l p k /\
            zstd_bits l p n DIV 2 EXP k = zstd_bits l (p + k) (n - k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[ADD_SUB2; ZSTD_BITS_ADD] THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `k:num`] ZSTD_BITS_BOUND) THEN
  SIMP_TAC[ZSTD_DIVMOD_ADD_MULT]);;

let ZSTD_BITS_BEYOND = prove
 (`!l p n. 8 * LENGTH l <= p ==> zstd_bits l p n = 0`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[zstd_bits] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p + 1`) THEN
  ASM_SIMP_TAC[zstd_bit; ARITH_RULE `a <= p ==> a <= p + 1 /\ ~(p < a)`;
               BITVAL_CLAUSES] THEN ARITH_TAC);;

let ZSTD_BACK_BOUND = prove
 (`!st q k. zstd_back st q k < 2 EXP k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zstd_back] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
  REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ; ZSTD_BITS_BOUND]);;

let ZSTD_BACK_TOP = prove
 (`!st q k n. n <= q /\ n <= k
              ==> zstd_back st q k DIV 2 EXP (k - n) =
                  zstd_bits st 0 q DIV 2 EXP (q - n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zstd_back; DIV_DIV; GSYM EXP_ADD] THEN
  SUBGOAL_THEN `q + k - n = k + (q - n)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
  SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]);;

let DIV_EQ_RANGE = prove
 (`!y d k. ~(d = 0) ==> (y DIV d = k <=> k * d <= y /\ y < (k + 1) * d)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`y:num`; `d:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `y - k * d` THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Decoding a state of ml bits for a complete code: the symbol of the range  *)
(* that contains it, whose code is a prefix of it.                           *)
(* ------------------------------------------------------------------------- *)

let huf_complete = new_definition
 `huf_complete ws ml <=>
    huf_total ws = 2 EXP ml /\ (!s. s IN huf_present ws ==> EL s ws <= ml)`;;

let huf_symbol = new_definition
 `huf_symbol ws y =
    @s. s IN huf_present ws /\ huf_start ws s <= y /\
        y < huf_start ws s + 2 EXP (EL s ws - 1)`;;

let HUF_SYMBOL = prove
 (`!ws y. y < huf_total ws
          ==> huf_symbol ws y IN huf_present ws /\
              huf_start ws (huf_symbol ws y) <= y /\
              y < huf_start ws (huf_symbol ws y) +
                  2 EXP (EL (huf_symbol ws y) ws - 1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HUF_INTERVALS_COVER) THEN
  REWRITE_TAC[huf_symbol] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  REWRITE_TAC[]);;

let HUF_SYMBOL_UNIQUE = prove
 (`!ws y s. s IN huf_present ws /\ huf_start ws s <= y /\
            y < huf_start ws s + 2 EXP (EL s ws - 1)
            ==> huf_symbol ws y = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `y:num`] HUF_SYMBOL) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[HUF_START_END; LTE_TRANS]; ALL_TAC] THEN
  ASM_MESON_TAC[HUF_INTERVALS_DISJOINT]);;

let HUF_SYMBOL_CODE = prove
 (`!ws ml s y. huf_complete ws ml /\ s IN huf_present ws /\ y < 2 EXP ml
               ==> (huf_symbol ws y = s <=>
                    y DIV 2 EXP (EL s ws - 1) = huf_code ws s)`,
  REWRITE_TAC[huf_complete] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `s:num`] HUF_START_ALIGNED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[HUF_CODE_START] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ; DIV_EQ_RANGE] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`ws:num list`; `y:num`] HUF_SYMBOL) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC HUF_SYMBOL_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let HUF_PRESENT_WEIGHT = prove
 (`!ws ml s. huf_complete ws ml /\ s IN huf_present ws
             ==> ~(EL s ws = 0) /\ EL s ws <= ml`,
  REWRITE_TAC[huf_complete] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[huf_present; IN_ELIM_THM]; ASM_SIMP_TAC[]]);;

let HUF_CODE_BOUND = prove
 (`!ws ml s. huf_complete ws ml /\ s IN huf_present ws
             ==> huf_code ws s < 2 EXP ((ml + 1) - EL s ws)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `s:num`] HUF_PRESENT_WEIGHT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [huf_complete]) THEN
  REWRITE_TAC[HUF_CODE_START] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `~(w = 0) /\ w <= ml ==> (w - 1) + (ml + 1) - w = ml`] THEN
  MP_TAC(SPECL [`ws:num list`; `s:num`] HUF_START_END) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(2 EXP (EL s ws - 1) = 0)` MP_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ARITH_TAC]);;

let HUF_BITS_BOUND = prove
 (`!ws ml out. huf_complete ws ml /\
               ALL (\c:byte. val c IN huf_present ws) out
               ==> FST(huf_bits ws ml out) < 2 EXP SND(huf_bits ws ml out)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[huf_bits; ALL; EXP; ARITH] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `val(h:byte)`] HUF_CODE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`huf_code ws (val(h:byte))`,`c:num`) THEN
  SPEC_TAC(`FST(huf_bits ws ml t)`,`v:num`) THEN
  SPEC_TAC(`SND(huf_bits ws ml t)`,`n:num`) THEN
  SPEC_TAC(`(ml + 1) - EL (val(h:byte)) ws`,`k:num`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP_ADD] THEN REPEAT DISCH_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP n * (c + 1)` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Parsing a stream st from position q by repeatedly decoding the top ml     *)
(* bits as a state (with 0 bits below position 0), which is what the         *)
(* decoding tables do; for a complete code, the codes of the symbols parsed  *)
(* are the bits used, so that a single Huffman-coded stream is one that is   *)
(* parsed using exactly all its bits.                                        *)
(* ------------------------------------------------------------------------- *)

let huf_parse = define
 `(huf_parse ws ml (st:byte list) q [] q' <=> q' = q) /\
  (huf_parse ws ml st q (CONS (c:byte) out) q' <=>
     val c = huf_symbol ws (zstd_back st q ml) /\
     (ml + 1) - EL (val c) ws <= q /\
     huf_parse ws ml st (q - ((ml + 1) - EL (val c) ws)) out q')`;;

let HUF_PARSE_BITS = prove
 (`!ws ml (st:byte list) out q q'.
        huf_complete ws ml /\ huf_parse ws ml st q out q'
        ==> ALL (\c:byte. val c IN huf_present ws) out /\ q' <= q /\
            SND(huf_bits ws ml out) = q - q' /\
            zstd_bits st 0 q DIV 2 EXP q' = FST(huf_bits ws ml out)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[huf_parse; huf_bits; ALL] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL; SUB_REFL] THEN
    SIMP_TAC[DIV_LT; ZSTD_BITS_BOUND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ABBREV_TAC `s = val(h:byte)` THEN
  ABBREV_TAC `y = zstd_back st q ml` THEN
  ABBREV_TAC `len = (ml + 1) - EL s ws` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q - len:num`; `q':num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `y < 2 EXP ml` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[ZSTD_BACK_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `s IN huf_present ws` ASSUME_TAC THENL
   [ASM_MESON_TAC[HUF_SYMBOL; huf_complete]; ALL_TAC] THEN
  SUBGOAL_THEN `~(EL s ws = 0) /\ EL s ws <= ml` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HUF_PRESENT_WEIGHT]; ALL_TAC] THEN
  SUBGOAL_THEN `y DIV 2 EXP (EL s ws - 1) = huf_code ws s` ASSUME_TAC THENL
   [ASM_MESON_TAC[HUF_SYMBOL_CODE]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rand(concl th) = `huf_symbol ws y`)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `zstd_bits st (q - len) len = huf_code ws s` ASSUME_TAC THENL
   [MP_TAC(SPECL [`st:byte list`; `0`; `q:num`; `q - len:num`]
      ZSTD_BITS_SPLIT) THEN
    MP_TAC(SPECL [`st:byte list`; `q:num`; `ml:num`; `len:num`]
      ZSTD_BACK_TOP) THEN
    ASM_SIMP_TAC[ARITH_RULE `l <= q ==> q - (q - l) = l`; ADD_CLAUSES] THEN
    SUBGOAL_THEN `len <= ml /\ q - len <= q /\ ml - len = EL s ws - 1`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`st:byte list`; `0`; `q - len:num`; `len:num`]
    ZSTD_BITS_ADD) THEN
  ASM_SIMP_TAC[SUB_ADD; ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> rand(concl th) = `FST (huf_bits ws ml t)`)) THEN
  SUBGOAL_THEN `2 EXP (q - len) = 2 EXP q' * 2 EXP (q - len - q')`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; MULT_SYM] THEN
  REWRITE_TAC[ADD_SYM]);;

let HUF_BITS_PARSE = prove
 (`!ws ml (st:byte list) out q.
        huf_complete ws ml /\ ALL (\c:byte. val c IN huf_present ws) out /\
        SND(huf_bits ws ml out) <= q /\
        zstd_bits st 0 q DIV 2 EXP (q - SND(huf_bits ws ml out)) =
        FST(huf_bits ws ml out)
        ==> huf_parse ws ml st q out (q - SND(huf_bits ws ml out))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[huf_parse; huf_bits; ALL; SUB_0] THEN
  REPEAT GEN_TAC THEN
  ABBREV_TAC `s = val(h:byte)` THEN
  ABBREV_TAC `y = zstd_back st q ml` THEN
  ABBREV_TAC `len = (ml + 1) - EL s ws` THEN
  ABBREV_TAC `n = SND(huf_bits ws ml t)` THEN
  ABBREV_TAC `v = FST(huf_bits ws ml t)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(EL s ws = 0) /\ EL s ws <= ml` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HUF_PRESENT_WEIGHT]; ALL_TAC] THEN
  SUBGOAL_THEN `v < 2 EXP n` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["v"; "n"] THEN MATCH_MP_TAC HUF_BITS_BOUND THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `zstd_bits st 0 q DIV 2 EXP (q - len) = huf_code ws s`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `q - len = (q - (len + n)) + n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD; GSYM DIV_DIV]] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; DIV_LT; ADD_CLAUSES];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `s:num`; `y:num`]
      HUF_SYMBOL_CODE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "y" THEN
      REWRITE_TAC[ZSTD_BACK_BOUND];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`st:byte list`; `q:num`; `ml:num`; `len:num`]
      ZSTD_BACK_TOP) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `q - (len + n) = (q - len) - n` SUBST1_TAC THENL
   [ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`st:byte list`; `0`; `q:num`; `q - len:num`]
    ZSTD_BITS_SPLIT) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
  SUBGOAL_THEN `2 EXP (q - len) = 2 EXP ((q - len) - n) * 2 EXP n`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM DIV_MOD]] THEN
  SUBGOAL_THEN `(q - len) - n = q - (len + n)` SUBST1_TAC THENL
   [ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let HUF_STREAM_PARSE = prove
 (`!ws ml (st:byte list) out.
        huf_complete ws ml
        ==> (huf_stream ws ml st out <=>
             ?r. zstd_end st r /\ huf_parse ws ml st r out 0)`,
  let all_tac =
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_comb(concl th) &&
      fst(strip_comb(concl th)) = `ALL:(byte->bool)->byte list->bool`)) THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[huf_present; IN_ELIM_THM] in
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_stream] THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `SND(huf_bits ws ml out)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `out:byte list`;
                  `SND(huf_bits ws ml out)`] HUF_BITS_PARSE) THEN
    ASM_REWRITE_TAC[SUB_REFL; EXP; DIV_1; LE_REFL] THEN
    ANTS_TAC THENL [all_tac; REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `out:byte list`;
                  `r:num`; `0`] HUF_PARSE_BITS) THEN
    ASM_REWRITE_TAC[SUB_0; EXP; DIV_1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN all_tac]);;

(* ------------------------------------------------------------------------- *)
(* The same as a function, decoding k symbols one after another from         *)
(* position q: the symbols, the position after them and whether each used no *)
(* more bits than were left. The code's loops follow this, and the stream is *)
(* the codes of out exactly when this decodes out from the end and ends at   *)
(* position 0 with no bits missing.                                          *)
(* ------------------------------------------------------------------------- *)

let huf_decode = define
 `(huf_decode ws ml (st:byte list) q 0 = ([]:byte list,q,T)) /\
  (huf_decode ws ml st q (SUC k) =
     let p = FST(SND(huf_decode ws ml st q k)) in
     let s = huf_symbol ws (zstd_back st p ml) in
     let nb = (ml + 1) - EL s ws in
     (APPEND (FST(huf_decode ws ml st q k)) [word s:byte],
      p - nb,
      (SND(SND(huf_decode ws ml st q k)) /\ nb <= p)))`;;

let LIST_SNOC_INDUCT = prove
 (`!P:A list->bool. P [] /\ (!t h. P t ==> P (APPEND t [h])) ==> !l. P l`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!l:A list. P(REVERSE l)` MP_TAC THENL
   [LIST_INDUCT_TAC THEN ASM_SIMP_TAC[REVERSE];
    MESON_TAC[REVERSE_REVERSE]]);;

let APPEND_SING_EQ = prove
 (`!l1 l2 (x:A) y. APPEND l1 [x] = APPEND l2 [y] <=> l1 = l2 /\ x = y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_THEN(MP_TAC o AP_TERM `REVERSE:A list->A list`) THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND; CONS_11] THEN
  MESON_TAC[REVERSE_REVERSE]);;

let HUF_DECODE_LENGTH = prove
 (`!ws ml (st:byte list) q k. LENGTH(FST(huf_decode ws ml st q k)) = k`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[huf_decode; LENGTH; LET_DEF; LET_END_DEF;
                  LENGTH_APPEND] THEN
  ARITH_TAC);;

let HUF_PARSE_SNOC = prove
 (`!ws ml (st:byte list) out c q q'.
        huf_parse ws ml st q (APPEND out [c]) q' <=>
        ?p. huf_parse ws ml st q out p /\
            val c = huf_symbol ws (zstd_back st p ml) /\
            (ml + 1) - EL (val c) ws <= p /\
            q' = p - ((ml + 1) - EL (val c) ws)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; huf_parse] THEN MESON_TAC[]);;

let HUF_DECODE_PARSE = prove
 (`!ws ml (st:byte list) q.
        huf_complete ws ml /\ LENGTH ws <= 256
        ==> !out q'. huf_parse ws ml st q out q' <=>
                     huf_decode ws ml st q (LENGTH out) = (out,q',T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC LIST_SNOC_INDUCT THEN
  CONJ_TAC THENL
   [REWRITE_TAC[huf_parse; LENGTH; huf_decode; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:byte list`; `h:byte`] THEN DISCH_TAC THEN
  X_GEN_TAC `q':num` THEN
  REWRITE_TAC[HUF_PARSE_SNOC; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[huf_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`huf_decode ws ml st q (LENGTH(t:byte list))`,
           `d:byte list#num#bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`o0:byte list`; `p0:num`; `k0:bool`] THEN
  REWRITE_TAC[APPEND_SING_EQ; GSYM CONJ_ASSOC] THEN
  ASM_CASES_TAC `o0:byte list = t` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k0:bool` THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  ABBREV_TAC `s = huf_symbol ws (zstd_back (st:byte list) p0 ml)` THEN
  SUBGOAL_THEN `s < 256` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    MP_TAC(SPECL [`ws:num list`; `zstd_back (st:byte list) p0 ml`]
      HUF_SYMBOL) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[huf_complete]) THEN
    ASM_REWRITE_TAC[ZSTD_BACK_BOUND; huf_present; IN_ELIM_THM] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word s:byte = h <=> val h = s` SUBST1_TAC THENL
   [EQ_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[VAL_WORD; DIMINDEX_8; MOD_LT; ARITH_RULE `2 EXP 8 = 256`;
                 WORD_VAL];
    ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* The top bits of a state of k bits are those of fewer bits.                *)

let ZSTD_BACK_DIV = prove
 (`!st q k m. m <= k
              ==> zstd_back st q k DIV 2 EXP (k - m) = zstd_back st q m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zstd_back; DIV_DIV] THEN
  SUBGOAL_THEN `2 EXP k = 2 EXP (k - m) * 2 EXP m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
  SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]);;

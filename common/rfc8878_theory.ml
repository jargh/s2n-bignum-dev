(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Facts about the specification of Huffman-coded literals in the Zstandard  *)
(* format in rfc8878.ml, and of the FSE tables used for their weights, their *)
(* descriptions, the decoding of the weights and the Huffman tree            *)
(* descriptions, for the proofs about zstd's code.                           *)
(* ========================================================================= *)

needs "common/rfc8878.ml";;
needs "Library/pocklington.ml";;

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

(* ------------------------------------------------------------------------- *)
(* Lemmas about list_of_seq, FILTER, ITLIST and ASSOC.                       *)
(* ------------------------------------------------------------------------- *)

let LIST_OF_SEQ_0 = prove
 (`!f:num->A. list_of_seq f 0 = []`,
  REWRITE_TAC[list_of_seq]);;

let LIST_OF_SEQ_SING = prove
 (`!f:num->A. list_of_seq f 1 = [f 0]`,
  REWRITE_TAC[num_CONV `1`; list_of_seq; APPEND]);;

let LIST_OF_SEQ_ADD1 = prove
 (`!f:num->A n. list_of_seq f (n + 1) = APPEND (list_of_seq f n) [f n]`,
  REWRITE_TAC[GSYM ADD1; list_of_seq]);;

let LIST_OF_SEQ_ADD_APPEND = prove
 (`!(f:num->A) m n.
        list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f(m + i)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ_0; APPEND_NIL] THEN
  REWRITE_TAC[ADD1; ADD_ASSOC; LIST_OF_SEQ_ADD1] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC]);;

let MEM_LIST_OF_SEQ = prove
 (`!(f:num->A) n x. MEM x (list_of_seq f n) <=> ?i. i < n /\ x = f i`,
  REWRITE_TAC[MEM_EXISTS_EL; LENGTH_LIST_OF_SEQ] THEN
  MESON_TAC[EL_LIST_OF_SEQ]);;

let LENGTH_FILTER_LIST_OF_SEQ_SUC = prove
 (`!P (f:num->A) j.
        LENGTH(FILTER P (list_of_seq f (j + 1))) =
        LENGTH(FILTER P (list_of_seq f j)) + (if P(f j) then 1 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD1; FILTER_APPEND; LENGTH_APPEND; FILTER] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let LENGTH_FILTER_LIST_OF_SEQ = prove
 (`!P (f:num->A) n.
        LENGTH(FILTER P (list_of_seq f n)) = CARD {j | j < n /\ P(f j)}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_0; FILTER; LENGTH; CONJUNCT1 LT; EMPTY_GSPEC;
              CARD_CLAUSES] THEN
  REWRITE_TAC[ADD1; LENGTH_FILTER_LIST_OF_SEQ_SUC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE {j | j < n /\ P((f:num->A) j)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN
     `{j | j < n + 1 /\ P((f:num->A) j)} = n INSERT {j | j < n /\ P(f j)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
      X_GEN_TAC `j:num` THEN ASM_CASES_TAC `j:num = n` THEN
      ASM_REWRITE_TAC[ARITH_RULE `j < n + 1 <=> j < n \/ j = n`; LT_REFL];
      ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; LT_REFL; ADD1]];
    REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN ASM_CASES_TAC `j:num = n` THEN
    ASM_REWRITE_TAC[ARITH_RULE `j < n + 1 <=> j < n \/ j = n`; LT_REFL]]);;

let LENGTH_FILTER_LIST_OF_SEQ_MONO = prove
 (`!P (f:num->A) m n.
        m <= n
        ==> LENGTH(FILTER P (list_of_seq f m)) <=
            LENGTH(FILTER P (list_of_seq f n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_FILTER_LIST_OF_SEQ] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LTE_TRANS];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]]);;

let EL_FILTER_LIST_OF_SEQ = prove
 (`!P (f:num->A) n j.
        j < n /\ P(f j)
        ==> EL (LENGTH(FILTER P (list_of_seq f j)))
               (FILTER P (list_of_seq f n)) = f j`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
    REWRITE_RULE[LT_EXISTS]) THEN
  REWRITE_TAC[ARITH_RULE `j + SUC d = j + 1 + d`] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD_APPEND; LIST_OF_SEQ_SING; ADD_CLAUSES] THEN
  REWRITE_TAC[FILTER_APPEND; FILTER] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; LENGTH; ARITH; EL; HD]);;

let EL_FILTER_LIST_OF_SEQ_EXISTS = prove
 (`!P (f:num->A) n i.
        i < LENGTH(FILTER P (list_of_seq f n))
        ==> ?j. j < n /\ P(f j) /\ LENGTH(FILTER P (list_of_seq f j)) = i`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_0; FILTER; LENGTH; LT] THEN
  REWRITE_TAC[ADD1; LENGTH_FILTER_LIST_OF_SEQ_SUC] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < LENGTH(FILTER P (list_of_seq (f:num->A) n))` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[ARITH_RULE `j < n ==> j < n + 1`];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let FILTER_LIST_OF_SEQ_INJ = prove
 (`!P (f:num->A) n i k.
        (!x y. x < n /\ y < n /\ f x = f y ==> x = y) /\
        i < LENGTH(FILTER P (list_of_seq f n)) /\
        k < LENGTH(FILTER P (list_of_seq f n)) /\
        EL i (FILTER P (list_of_seq f n)) = EL k (FILTER P (list_of_seq f n))
        ==> i = k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A->bool`; `f:num->A`; `n:num`; `i:num`]
    EL_FILTER_LIST_OF_SEQ_EXISTS) THEN
  MP_TAC(ISPECL [`P:A->bool`; `f:num->A`; `n:num`; `k:num`]
    EL_FILTER_LIST_OF_SEQ_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `jk:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ji:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`P:A->bool`; `f:num->A`; `n:num`; `jk:num`]
    EL_FILTER_LIST_OF_SEQ) THEN
  MP_TAC(ISPECL [`P:A->bool`; `f:num->A`; `n:num`; `ji:num`]
    EL_FILTER_LIST_OF_SEQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ji:num = jk` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let ITLIST_APPEND_NIL = prove
 (`!l (x:A list). ITLIST APPEND l x = APPEND (ITLIST APPEND l []) x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; APPEND] THEN
  X_GEN_TAC `x:A list` THEN
  FIRST_X_ASSUM(fun th -> SUBST1_TAC(SPEC `x:A list` th)) THEN
  REWRITE_TAC[APPEND_ASSOC]);;

let ASSOC_APPEND = prove
 (`!l1 l2 (a:A).
        ASSOC a (APPEND l1 (l2:(A#B)list)) =
        if MEM a (MAP FST l1) then ASSOC a l1 else ASSOC a l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; MAP; MEM; ASSOC] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `FST(h:A#B) = a` THEN
  ASM_REWRITE_TAC[]);;

let ASSOC_ZIP_INDEX = prove
 (`!(l1:A list) (l2:B list) k.
        LENGTH l1 = LENGTH l2 /\ k < LENGTH l1 /\
        (!i. i < LENGTH l1 /\ EL i l1 = EL k l1 ==> i = k)
        ==> ASSOC (EL k l1) (ZIP l1 l2) = EL k l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(k < 0)`; SUC_INJ] THEN
  REWRITE_TAC[ZIP; ASSOC] THEN INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[EL; HD; LT_0; NOT_SUC];
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `t':B list`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
    ASM_REWRITE_TAC[EL; TL; LT_SUC; SUC_INJ]]);;

(* ------------------------------------------------------------------------- *)
(* The spread of the symbols over an FSE table of 2^alog states walks        *)
(* through the states with the step fse_step alog, visiting the state        *)
(* fse_pos alog j at its step j. The step is odd for alog >= 5, so the walk  *)
(* is a permutation of the states. fse_ncell alog H j counts the states      *)
(* below H visited before step j.                                            *)
(* ------------------------------------------------------------------------- *)

let FSE_STEP_ODD = prove
 (`!alog. 5 <= alog ==> ODD(fse_step alog)`,
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[fse_step] THEN
  SUBGOAL_THEN `2 EXP (5 + k) DIV 2 = 2 * 2 EXP (k + 3) /\
                2 EXP (5 + k) DIV 8 = 2 * 2 EXP (k + 1)`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC;
    REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]]);;

let FSE_STEP_LT = prove
 (`!alog. 5 <= alog ==> fse_step alog < 2 EXP alog`,
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[fse_step; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[DIV_MULT2; ARITH_EQ; ARITH_RULE `32 * x = 2 * 16 * x`;
           ARITH_RULE `32 * x = 8 * 4 * x`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  MP_TAC(SPEC `k:num` (REWRITE_RULE[GSYM NOT_LE] EXP_EQ_0)) THEN
  REWRITE_TAC[ARITH_EQ] THEN MP_TAC(SPECL [`2`; `k:num`] EXP_EQ_0) THEN
  REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let FSE_POS_INJ = prove
 (`!alog i j.
        5 <= alog /\ i < 2 EXP alog /\ j < 2 EXP alog /\
        (i * fse_step alog) MOD 2 EXP alog = (j * fse_step alog) MOD 2 EXP alog
        ==> i = j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(i == j) (mod (2 EXP alog))` MP_TAC THENL
   [MATCH_MP_TAC CONG_MULT_RCANCEL THEN EXISTS_TAC `fse_step alog` THEN
    ASM_REWRITE_TAC[CONG] THEN
    REWRITE_TAC[COPRIME_REXP] THEN DISJ1_TAC THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_2] THEN
    ASM_SIMP_TAC[FSE_STEP_ODD];
    ASM_SIMP_TAC[CONG; MOD_LT]]);;

let FSE_POS_SURJ = prove
 (`!alog u. 5 <= alog /\ u < 2 EXP alog
            ==> ?j. j < 2 EXP alog /\ (j * fse_step alog) MOD 2 EXP alog = u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{j:num | j < 2 EXP alog}`;
                 `\j. (j * fse_step alog) MOD 2 EXP alog`]
    SURJECTIVE_IFF_INJECTIVE) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FSE_POS_INJ THEN
    EXISTS_TAC `alog:num` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `u:num`) THEN ASM_REWRITE_TAC[]]);;

let FSE_POS_CARD = prove
 (`!alog H.
        5 <= alog /\ H <= 2 EXP alog
        ==> CARD {j | j < 2 EXP alog /\
                      (j * fse_step alog) MOD 2 EXP alog < H} = H`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\j. (j * fse_step alog) MOD 2 EXP alog)
                         {j | j < 2 EXP alog /\
                              (j * fse_step alog) MOD 2 EXP alog < H})` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FSE_POS_INJ THEN EXISTS_TAC `alog:num` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{j:num | j < 2 EXP alog}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]];
    GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `u:num` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(SPECL [`alog:num`; `u:num`] FSE_POS_SURJ) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]]]);;

let fse_pos = new_definition
 `fse_pos alog j = (j * fse_step alog) MOD 2 EXP alog`;;

let FSE_POS_LT = prove
 (`!alog j. fse_pos alog j < 2 EXP alog`,
  REWRITE_TAC[fse_pos; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let FSE_POS_0 = prove
 (`!alog. fse_pos alog 0 = 0`,
  REWRITE_TAC[fse_pos; MULT_CLAUSES; MOD_0]);;

let FSE_POS_FULL = prove
 (`!alog. fse_pos alog (2 EXP alog) = 0`,
  REWRITE_TAC[fse_pos; MOD_MULT]);;

let FSE_MOD_ADD_MOD = prove
 (`!a b n. (a MOD n + b) MOD n = (a + b) MOD n /\
           (a + b MOD n) MOD n = (a + b) MOD n`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let FSE_POS_SUC = prove
 (`!alog j.
        (fse_pos alog j + fse_step alog) MOD 2 EXP alog =
        fse_pos alog (j + 1) /\
        (fse_step alog + fse_pos alog j) MOD 2 EXP alog =
        fse_pos alog (j + 1) /\
        (fse_step alog + (fse_step alog + fse_pos alog j)) MOD 2 EXP alog =
        fse_pos alog (j + 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fse_pos; ADD_ASSOC; FSE_MOD_ADD_MOD] THEN
  REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let fse_ncell = new_definition
 `fse_ncell alog H j =
    LENGTH(FILTER (\u. u < H)
            (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog) j))`;;

let FSE_NCELL_0 = prove
 (`!alog H. fse_ncell alog H 0 = 0`,
  REWRITE_TAC[fse_ncell; LIST_OF_SEQ_0; FILTER; LENGTH]);;

let FSE_NCELL_SUC = prove
 (`!alog H j.
        fse_ncell alog H (j + 1) =
        fse_ncell alog H j + (if fse_pos alog j < H then 1 else 0)`,
  REWRITE_TAC[fse_ncell; LENGTH_FILTER_LIST_OF_SEQ_SUC; fse_pos]);;

let FSE_NCELL_MONO = prove
 (`!alog H m n. m <= n ==> fse_ncell alog H m <= fse_ncell alog H n`,
  REWRITE_TAC[fse_ncell] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LENGTH_FILTER_LIST_OF_SEQ_MONO THEN ASM_REWRITE_TAC[]);;

let FSE_NCELL_FULL = prove
 (`!alog H. 5 <= alog /\ H <= 2 EXP alog
            ==> fse_ncell alog H (2 EXP alog) = H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_ncell; LENGTH_FILTER_LIST_OF_SEQ] THEN
  MATCH_MP_TAC FSE_POS_CARD THEN ASM_REWRITE_TAC[]);;

let FSE_NCELL_ALL = prove
 (`!alog j. fse_ncell alog (2 EXP alog) j = j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fse_ncell; LENGTH_FILTER_LIST_OF_SEQ] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[CARD_NUMSEG_LT]);;

let FSE_WALK_END = prove
 (`!alog H j.
        5 <= alog /\ H <= 2 EXP alog /\ j <= 2 EXP alog /\
        fse_pos alog j < H /\ fse_ncell alog H j = H
        ==> j = 2 EXP alog`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`alog:num`; `H:num`; `j + 1`; `2 EXP alog`]
    FSE_NCELL_MONO) THEN
  ASM_SIMP_TAC[FSE_NCELL_FULL; FSE_NCELL_SUC] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The symbols of the FSE table for the counts cs. The symbols with a count  *)
(* of -1 take one state each, downward from the top. The others, fse_syms    *)
(* cs, each symbol s with a count c >= 1 being there c times in order of s,  *)
(* are given in turn to the other states, fse_cells cs alog, in the order of *)
(* the walk. fse_cum cs s counts those of the symbols below s.               *)
(* ------------------------------------------------------------------------- *)

let fse_syms = new_definition
 `fse_syms (cs:int list) =
    ITLIST APPEND
     (list_of_seq (\s. REPLICATE (num_of_int(max (EL s cs) (&0))) s)
                  (LENGTH cs)) []`;;

let fse_cells = new_definition
 `fse_cells (cs:int list) alog =
    FILTER (\u. u < 2 EXP alog - LENGTH(fse_lowprob cs))
           (list_of_seq (\j. (j * fse_step alog) MOD 2 EXP alog)
                        (2 EXP alog))`;;

let FSE_SPREAD_ALT = prove
 (`!cs alog.
        fse_spread cs alog =
        APPEND (ZIP (fse_cells cs alog) (fse_syms cs))
         (ZIP (list_of_seq (\j. 2 EXP alog - 1 - j) (LENGTH(fse_lowprob cs)))
              (fse_lowprob cs))`,
  REWRITE_TAC[fse_spread; fse_cells; fse_syms] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let LENGTH_FSE_CELLS = prove
 (`!cs alog.
        5 <= alog /\ LENGTH(fse_lowprob cs) <= 2 EXP alog
        ==> LENGTH(fse_cells cs alog) = 2 EXP alog - LENGTH(fse_lowprob cs)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fse_cells; LENGTH_FILTER_LIST_OF_SEQ] THEN
  MATCH_MP_TAC FSE_POS_CARD THEN ASM_ARITH_TAC);;

let FSE_EXPAND_L_TAC =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `L:num list` &&
       is_comb(lhs(concl th)) &&
       fst(strip_comb(lhs(concl th))) =
         `FILTER:(num->bool)->num list->num list`
    then SUBST1_TAC(SYM th) else NO_TAC);;

let FSE_SYMBOL_CELL = prove
 (`!cs alog j.
        5 <= alog /\
        LENGTH(fse_syms cs) + LENGTH(fse_lowprob cs) = 2 EXP alog /\
        j < 2 EXP alog /\
        (j * fse_step alog) MOD 2 EXP alog <
        2 EXP alog - LENGTH(fse_lowprob cs)
        ==> fse_symbol cs alog ((j * fse_step alog) MOD 2 EXP alog) =
            EL (LENGTH(FILTER (\u. u < 2 EXP alog - LENGTH(fse_lowprob cs))
                       (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog)
                                    j)))
               (fse_syms cs)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `H = 2 EXP alog - LENGTH(fse_lowprob cs)` THEN
  ABBREV_TAC `L = FILTER (\u. u < H)
     (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog) (2 EXP alog))` THEN
  SUBGOAL_THEN `fse_cells cs alog = L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[fse_cells] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k = LENGTH(FILTER (\u. u < H)
                  (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog)
                               j))` THEN
  SUBGOAL_THEN `EL k L = (j * fse_step alog) MOD 2 EXP alog` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN FSE_EXPAND_L_TAC THEN
    MP_TAC(ISPECL [`\u:num. u < H`;
                   `\i. (i * fse_step alog) MOD 2 EXP alog`;
                   `2 EXP alog`; `j:num`] EL_FILTER_LIST_OF_SEQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(L:num list) = H` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `fse_cells cs alog = L`)) THEN
    EXPAND_TAC "H" THEN MATCH_MP_TAC LENGTH_FSE_CELLS THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k < H` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `!b. k < b /\ b <= H ==> k < H`) THEN
    EXISTS_TAC `LENGTH(FILTER (\u. u < H)
                  (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog)
                               (j + 1)))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "k" THEN REWRITE_TAC[LENGTH_FILTER_LIST_OF_SEQ_SUC] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
        check (fun th -> concl th = `LENGTH(L:num list) = H`)) THEN
      FSE_EXPAND_L_TAC THEN
      MATCH_MP_TAC LENGTH_FILTER_LIST_OF_SEQ_MONO THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[fse_symbol; FSE_SPREAD_ALT; ASSOC_APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MAP FST (ZIP L (fse_syms cs)) = L:num list` SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_FST_ZIP THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `EL k L = (j * fse_step alog) MOD 2 EXP alog`)) THEN
  SUBGOAL_THEN `MEM (EL k L) (L:num list)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC ASSOC_ZIP_INDEX THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\u:num. u < H`;
                 `\i. (i * fse_step alog) MOD 2 EXP alog`;
                 `2 EXP alog`; `i:num`; `k:num`] FILTER_LIST_OF_SEQ_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FSE_POS_INJ THEN EXISTS_TAC `alog:num` THEN ASM_REWRITE_TAC[]);;

let FSE_SYMBOL_LOW = prove
 (`!cs alog i.
        5 <= alog /\
        LENGTH(fse_syms cs) + LENGTH(fse_lowprob cs) = 2 EXP alog /\
        i < LENGTH(fse_lowprob cs)
        ==> fse_symbol cs alog (2 EXP alog - 1 - i) = EL i (fse_lowprob cs)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fse_symbol; FSE_SPREAD_ALT; ASSOC_APPEND] THEN
  SUBGOAL_THEN `LENGTH(fse_cells cs alog) = LENGTH(fse_syms cs)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`cs:int list`; `alog:num`] LENGTH_FSE_CELLS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP] THEN
  SUBGOAL_THEN `~MEM (2 EXP alog - 1 - i) (fse_cells cs alog)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[fse_cells; MEM_FILTER] THEN
    MATCH_MP_TAC(TAUT `~p ==> ~(p /\ q)`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ll = list_of_seq (\j. 2 EXP alog - 1 - j)
                               (LENGTH(fse_lowprob cs))` THEN
  SUBGOAL_THEN `LENGTH(ll:num list) = LENGTH(fse_lowprob cs) /\
                !j. j < LENGTH(fse_lowprob cs)
                    ==> EL j ll = 2 EXP alog - 1 - j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ll" THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[EL_LIST_OF_SEQ];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [SYM(MATCH_MP th (ASSUME `i < LENGTH(fse_lowprob cs)`))]) THEN
  MATCH_MP_TAC ASSOC_ZIP_INDEX THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i':num` THEN STRIP_TAC THEN
  UNDISCH_TAC `EL i' ll = EL i (ll:num list)` THEN ASM_SIMP_TAC[] THEN
  ASM_ARITH_TAC);;

let fse_cum = define
 `(fse_cum (cs:int list) 0 = 0) /\
  (fse_cum cs (SUC s) = fse_cum cs s + num_of_int(max (EL s cs) (&0)))`;;

let FSE_CUM_SUC = prove
 (`!cs s. fse_cum cs (s + 1) = fse_cum cs s + num_of_int(max (EL s cs) (&0))`,
  REWRITE_TAC[GSYM ADD1; fse_cum]);;

let FSE_CUM_MONO = prove
 (`!cs s t. s <= t ==> fse_cum cs s <= fse_cum cs t`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL];
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[LE_REFL];
      REWRITE_TAC[fse_cum] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;

let FSE_CUM_FIND = prove
 (`!cs n k.
        k < fse_cum cs n
        ==> ?s. s < n /\ fse_cum cs s <= k /\ k < fse_cum cs (s + 1)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[fse_cum; CONJUNCT1 LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `k < fse_cum cs n` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[ARITH_RULE `s < n ==> s < SUC n`];
    EXISTS_TAC `n:num` THEN REWRITE_TAC[GSYM ADD1; fse_cum] THEN
    ASM_ARITH_TAC]);;

let LENGTH_FSE_SYMS_PREFIX = prove
 (`!(cs:int list) s.
        LENGTH(ITLIST APPEND
                (list_of_seq (\t. REPLICATE (num_of_int(max (EL t cs) (&0))) t)
                             s) []) = fse_cum cs s`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[fse_cum; LIST_OF_SEQ_0; ITLIST; LENGTH] THEN
  REWRITE_TAC[ADD1; LIST_OF_SEQ_ADD1; ITLIST_APPEND; ITLIST] THEN
  ONCE_REWRITE_TAC[ITLIST_APPEND_NIL] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; APPEND_NIL; LENGTH_REPLICATE; LENGTH;
                  ADD_CLAUSES]);;

let LENGTH_FSE_SYMS = prove
 (`!cs. LENGTH(fse_syms cs) = fse_cum cs (LENGTH cs)`,
  REWRITE_TAC[fse_syms; LENGTH_FSE_SYMS_PREFIX]);;

let EL_FSE_SYMS = prove
 (`!(cs:int list) s k.
        s < LENGTH cs /\ fse_cum cs s <= k /\ k < fse_cum cs (s + 1)
        ==> EL k (fse_syms cs) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_syms] THEN
  SUBGOAL_THEN `LENGTH(cs:int list) = s + 1 + (LENGTH cs - (s + 1))`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD_APPEND; LIST_OF_SEQ_SING; ITLIST_APPEND;
              ITLIST] THEN
  ONCE_REWRITE_TAC[ITLIST_APPEND_NIL] THEN
  REWRITE_TAC[ADD_CLAUSES; APPEND_NIL] THEN
  REWRITE_TAC[EL_APPEND; LENGTH_FSE_SYMS_PREFIX; LENGTH_REPLICATE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD1; fse_cum]) THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= k ==> ~(k < a)`] THEN
  COND_CASES_TAC THENL
   [W(fun (_,w) -> MP_TAC(ISPECL [rand(lhs w); lhand(lhs w)] MEM_EL)) THEN
    ASM_REWRITE_TAC[LENGTH_REPLICATE; MEM_REPLICATE] THEN SIMP_TAC[];
    ASM_ARITH_TAC]);;

let EL_FSE_SYMS_EQ = prove
 (`!cs s k.
        k < fse_cum cs (LENGTH cs)
        ==> (EL k (fse_syms cs) = s <=>
             s < LENGTH cs /\ fse_cum cs s <= k /\ k < fse_cum cs (s + 1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC o
    MATCH_MP FSE_CUM_FIND) THEN
  MP_TAC(SPECL [`cs:int list`; `t:num`; `k:num`] EL_FSE_SYMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `~(t < s) /\ ~(s < t) ==> t = s`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`cs:int list`; `t + 1`; `s:num`] FSE_CUM_MONO);
    MP_TAC(SPECL [`cs:int list`; `s + 1`; `t:num`] FSE_CUM_MONO)] THEN
  ASM_ARITH_TAC);;

let EL_FSE_SYMS_POS = prove
 (`!cs k.
        k < LENGTH(fse_syms cs)
        ==> EL k (fse_syms cs) < LENGTH cs /\
            &1 <= EL (EL k (fse_syms cs)) cs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_FSE_SYMS] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC o
    MATCH_MP FSE_CUM_FIND) THEN
  MP_TAC(SPECL [`cs:int list`; `t:num`; `k:num`] EL_FSE_SYMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `k < fse_cum cs (t + 1)` THEN
  UNDISCH_TAC `fse_cum cs t <= k` THEN
  REWRITE_TAC[GSYM ADD1; fse_cum] THEN
  MP_TAC(ISPEC `max (EL t (cs:int list)) (&0)` INT_OF_NUM_OF_INT) THEN
  REWRITE_TAC[INT_ARITH `&0:int <= max x (&0)`] THEN
  SPEC_TAC(`num_of_int(max (EL t (cs:int list)) (&0))`,`n:num`) THEN
  GEN_TAC THEN DISCH_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `1 <= n` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MEM_FSE_LOWPROB = prove
 (`!cs s. MEM s (fse_lowprob cs) <=> s < LENGTH cs /\ EL s cs = -- &1`,
  REWRITE_TAC[fse_lowprob; MEM_FILTER; MEM_LIST_OF_SEQ] THEN MESON_TAC[]);;

let EL_FSE_LOWPROB = prove
 (`!cs i.
        i < LENGTH(fse_lowprob cs)
        ==> EL i (fse_lowprob cs) < LENGTH cs /\
            EL (EL i (fse_lowprob cs)) cs = -- &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM MEM_FSE_LOWPROB] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `i:num` THEN
  ASM_REWRITE_TAC[]);;

let FSE_CELL_COUNT_LT = prove
 (`!alog H j.
        5 <= alog /\ H <= 2 EXP alog /\ j < 2 EXP alog /\
        (j * fse_step alog) MOD 2 EXP alog < H
        ==> LENGTH(FILTER (\u. u < H)
                     (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog) j))
            < H`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `!k b H:num. k < b /\ b <= H ==> k < H`) THEN
  EXISTS_TAC `LENGTH(FILTER (\u. u < H)
                (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog)
                             (j + 1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH_FILTER_LIST_OF_SEQ_SUC] THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    MP_TAC(SPECL [`alog:num`; `H:num`] FSE_POS_CARD) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`\u:num. u < H`; `\i. (i * fse_step alog) MOD 2 EXP alog`;
      `2 EXP alog`] LENGTH_FILTER_LIST_OF_SEQ)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC LENGTH_FILTER_LIST_OF_SEQ_MONO THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Counts that fill the table exactly (fse_valid), the first of the next     *)
(* states of each symbol (fse_init), and so the bounds on the next states,   *)
(* the numbers of bits and the baselines in the decoding table.              *)
(* ------------------------------------------------------------------------- *)

let fse_valid = new_definition
 `fse_valid (cs:int list) alog <=>
    ALL (\c. -- &1 <= c) cs /\
    LENGTH(fse_syms cs) + LENGTH(fse_lowprob cs) = 2 EXP alog`;;

let FSE_VALID_LENGTH = prove
 (`!cs alog. fse_valid cs alog ==> 1 <= LENGTH cs`,
  REWRITE_TAC[fse_valid; ARITH_RULE `1 <= n <=> ~(n = 0)`; LENGTH_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
   `LENGTH (fse_syms cs) + LENGTH (fse_lowprob cs) = 2 EXP alog` THEN
  ASM_REWRITE_TAC[fse_syms; fse_lowprob; LENGTH; LIST_OF_SEQ_0;
                  ITLIST; FILTER; ADD_CLAUSES] THEN
  REWRITE_TAC[EQ_SYM_EQ; EXP_EQ_0; ARITH_EQ]);;

let fse_init = new_definition
 `fse_init (cs:int list) s =
    if EL s cs = -- &1 then 1 else num_of_int(EL s cs)`;;

let FSE_NEXT_INIT = prove
 (`!cs alog u.
        fse_next cs alog u =
        fse_init cs (fse_symbol cs alog u) +
        CARD {v | v < u /\ fse_symbol cs alog v = fse_symbol cs alog u}`,
  REWRITE_TAC[fse_next; fse_init] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let FSE_SYMBOL_CASES = prove
 (`!cs alog v.
        5 <= alog /\ fse_valid cs alog /\ v < 2 EXP alog
        ==> (v < 2 EXP alog - LENGTH(fse_lowprob cs) /\
             ?j. j < 2 EXP alog /\ (j * fse_step alog) MOD 2 EXP alog = v /\
                 LENGTH(FILTER (\u. u < 2 EXP alog - LENGTH(fse_lowprob cs))
                    (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog) j))
                 < LENGTH(fse_syms cs) /\
                 fse_symbol cs alog v =
                 EL (LENGTH(FILTER
                       (\u. u < 2 EXP alog - LENGTH(fse_lowprob cs))
                       (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog)
                                    j)))
                    (fse_syms cs)) \/
            (2 EXP alog - LENGTH(fse_lowprob cs) <= v /\
             2 EXP alog - 1 - v < LENGTH(fse_lowprob cs) /\
             fse_symbol cs alog v = EL (2 EXP alog - 1 - v) (fse_lowprob cs))`,
  REWRITE_TAC[fse_valid] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v < 2 EXP alog - LENGTH(fse_lowprob cs)` THEN
  ASM_REWRITE_TAC[NOT_LT] THENL
   [DISJ1_TAC THEN
    MP_TAC(SPECL [`alog:num`; `v:num`] FSE_POS_SURJ) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `LENGTH(fse_syms cs) = 2 EXP alog - LENGTH(fse_lowprob cs)`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FSE_CELL_COUNT_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      FIRST_ASSUM(SUBST1_TAC o SYM o check
       (fun th -> is_eq(concl th) && rhs(concl th) = `v:num`)) THEN
      MATCH_MP_TAC FSE_SYMBOL_CELL THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    MP_TAC(SPECL [`cs:int list`; `alog:num`; `2 EXP alog - 1 - v`]
      FSE_SYMBOL_LOW) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `2 EXP alog - 1 - (2 EXP alog - 1 - v) = v` SUBST1_TAC THENL
     [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let FSE_SYMBOL_RANGE = prove
 (`!cs alog v.
        5 <= alog /\ fse_valid cs alog /\ v < 2 EXP alog
        ==> fse_symbol cs alog v < LENGTH cs /\
            (EL (fse_symbol cs alog v) cs = -- &1 \/
             &1 <= EL (fse_symbol cs alog v) cs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FSE_SYMBOL_CASES) THEN STRIP_TAC THENL
   [ABBREV_TAC `k = LENGTH(FILTER
                (\u. u < 2 EXP alog - LENGTH(fse_lowprob cs))
                (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog) j))` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_FSE_SYMS]) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC o
      MATCH_MP FSE_CUM_FIND) THEN
    MP_TAC(SPECL [`cs:int list`; `t:num`; `k:num`] EL_FSE_SYMS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    UNDISCH_TAC `k < fse_cum cs (t + 1)` THEN
    UNDISCH_TAC `fse_cum cs t <= k` THEN
    REWRITE_TAC[GSYM ADD1; fse_cum] THEN
    MP_TAC(ISPEC `max (EL t (cs:int list)) (&0)` INT_OF_NUM_OF_INT) THEN
    REWRITE_TAC[INT_ARITH `&0:int <= max x (&0)`] THEN
    SPEC_TAC(`num_of_int(max (EL t (cs:int list)) (&0))`,`n:num`) THEN
    GEN_TAC THEN DISCH_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `1 <= n` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    SUBGOAL_THEN `MEM (fse_symbol cs alog v) (fse_lowprob cs)` MP_TAC THENL
     [ASM_REWRITE_TAC[MEM_EXISTS_EL] THEN
      EXISTS_TAC `2 EXP alog - 1 - v` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[MEM_FSE_LOWPROB]]]);;

let FSE_SYMBOL_POS = prove
 (`!cs alog j.
        5 <= alog /\ fse_valid cs alog /\ j < 2 EXP alog /\
        fse_pos alog j < 2 EXP alog - LENGTH(fse_lowprob cs)
        ==> fse_symbol cs alog (fse_pos alog j) =
            EL (fse_ncell alog (2 EXP alog - LENGTH(fse_lowprob cs)) j)
               (fse_syms cs)`,
  REWRITE_TAC[fse_valid; fse_pos; fse_ncell] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FSE_SYMBOL_CELL THEN ASM_REWRITE_TAC[]);;

let FSE_NLOW_EL = prove
 (`!cs s.
        s < LENGTH cs /\ EL s cs = -- &1
        ==> LENGTH(FILTER (\t. EL t cs = -- &1) (list_of_seq (\t. t) s))
            < LENGTH(fse_lowprob cs) /\
            EL (LENGTH(FILTER (\t. EL t cs = -- &1) (list_of_seq (\t. t) s)))
               (fse_lowprob cs) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[fse_lowprob] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `!k b H:num. k < b /\ b <= H ==> k < H`) THEN
    EXISTS_TAC `LENGTH(FILTER (\t. EL t (cs:int list) = -- &1)
                  (list_of_seq (\t. t) (s + 1)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_FILTER_LIST_OF_SEQ_SUC] THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      MATCH_MP_TAC LENGTH_FILTER_LIST_OF_SEQ_MONO THEN ASM_ARITH_TAC];
    MP_TAC(ISPECL [`\t. EL t (cs:int list) = -- &1`; `\t:num. t`;
                   `LENGTH(cs:int list)`; `s:num`] EL_FILTER_LIST_OF_SEQ) THEN
    ASM_REWRITE_TAC[]]);;

let FSE_SYMBOL_CARD_LE = prove
 (`!cs alog s.
        5 <= alog /\ fse_valid cs alog /\ s < LENGTH cs
        ==> CARD {v | v < 2 EXP alog /\ fse_symbol cs alog v = s}
            <= fse_init cs s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_init] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {2 EXP alog - 1 -
      LENGTH(FILTER (\t. EL t (cs:int list) = -- &1)
                    (list_of_seq (\t. t) s))}` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_SING; LE_REFL]] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `v:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`cs:int list`; `alog:num`; `v:num`] FSE_SYMBOL_CASES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THENL
     [ABBREV_TAC `k = LENGTH(FILTER
         (\u. u < 2 EXP alog - LENGTH(fse_lowprob cs))
         (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog) j))` THEN
      SUBGOAL_THEN `EL k (fse_syms cs) = s` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`cs:int list`; `k:num`] EL_FSE_SYMS_POS) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MP_TAC(SPECL [`cs:int list`; `s:num`] FSE_NLOW_EL) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `2 EXP alog - 1 - v =
        LENGTH(FILTER (\t. EL t (cs:int list) = -- &1)
                      (list_of_seq (\t. t) s))`
      MP_TAC THENL [ALL_TAC; UNDISCH_TAC `v < 2 EXP alog` THEN ARITH_TAC] THEN
      MP_TAC(ISPECL [`\t. EL t (cs:int list) = -- &1`; `\t:num. t`;
        `LENGTH(cs:int list)`; `2 EXP alog - 1 - v`;
        `LENGTH(FILTER (\t. EL t (cs:int list) = -- &1)
                       (list_of_seq (\t. t) s))`]
        FILTER_LIST_OF_SEQ_INJ) THEN
      REWRITE_TAC[GSYM fse_lowprob] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN `&0 <= EL s (cs:int list)` ASSUME_TAC THENL
     [UNDISCH_TAC `fse_valid cs alog` THEN
      REWRITE_TAC[fse_valid; GSYM ALL_EL] THEN
      DISCH_THEN(MP_TAC o SPEC `s:num` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(IMAGE (\i. EL (fse_cum cs s + i) (fse_cells cs alog))
                           {i | i < num_of_int(EL s cs)})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `v:num` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`cs:int list`; `alog:num`; `v:num`] FSE_SYMBOL_CASES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THENL
       [ABBREV_TAC `k = LENGTH(FILTER
           (\u. u < 2 EXP alog - LENGTH(fse_lowprob cs))
           (list_of_seq (\i. (i * fse_step alog) MOD 2 EXP alog) j))` THEN
        SUBGOAL_THEN `EL k (fse_syms cs) = s` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(SPECL [`cs:int list`; `s:num`; `k:num`] EL_FSE_SYMS_EQ) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[LENGTH_FSE_SYMS]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[GSYM ADD1; fse_cum] THEN STRIP_TAC THEN
        EXISTS_TAC `k - fse_cum cs s` THEN CONJ_TAC THENL
         [SUBGOAL_THEN `fse_cum cs s + k - fse_cum cs s = k` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          EXPAND_TAC "k" THEN REWRITE_TAC[fse_cells] THEN
          FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
           check (fun th -> is_eq(concl th) && rhs(concl th) = `v:num`)) THEN
          CONV_TAC SYM_CONV THEN
          MP_TAC(BETA_RULE(ISPECL
           [`\u:num. u < 2 EXP alog - LENGTH(fse_lowprob cs)`;
            `\i. (i * fse_step alog) MOD 2 EXP alog`;
            `2 EXP alog`; `j:num`] EL_FILTER_LIST_OF_SEQ)) THEN
          ASM_MESON_TAC[];
          UNDISCH_TAC `k < fse_cum cs s + num_of_int (max (EL s cs) (&0))` THEN
          ASM_SIMP_TAC[INT_ARITH `&0:int <= x ==> max x (&0) = x`] THEN
          UNDISCH_TAC `fse_cum cs s <= k` THEN ARITH_TAC];
        SUBGOAL_THEN `EL (2 EXP alog - 1 - v) (fse_lowprob cs) = s` MP_TAC
        THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(SPECL [`cs:int list`; `2 EXP alog - 1 - v`] EL_FSE_LOWPROB) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD {i | i < num_of_int(EL s (cs:int list))}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_IMAGE_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT];
        REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]]]]);;

let FSE_INIT_LE = prove
 (`!cs alog s.
        fse_valid cs alog /\ s < LENGTH cs
        ==> fse_init cs s <= 2 EXP alog`,
  REWRITE_TAC[fse_valid; fse_init] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= EL s (cs:int list)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\c. -- &1 <= c) (cs:int list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `s:num`) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cs:int list`; `s + 1`; `LENGTH(cs:int list)`]
    FSE_CUM_MONO) THEN
  ASM_REWRITE_TAC[ARITH_RULE `s + 1 <= n <=> s < n`; GSYM ADD1; fse_cum] THEN
  ASM_SIMP_TAC[INT_ARITH `&0:int <= x ==> max x (&0) = x`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_FSE_SYMS]) THEN ASM_ARITH_TAC);;

let FSE_NEXT_BOUNDS = prove
 (`!cs alog u.
        5 <= alog /\ fse_valid cs alog /\ u < 2 EXP alog
        ==> 1 <= fse_init cs (fse_symbol cs alog u) /\
            fse_init cs (fse_symbol cs alog u) <= 2 EXP alog /\
            fse_init cs (fse_symbol cs alog u) <= fse_next cs alog u /\
            fse_next cs alog u < 2 * fse_init cs (fse_symbol cs alog u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN ASSUME_TAC o MATCH_MP FSE_SYMBOL_RANGE) THEN
  REWRITE_TAC[FSE_NEXT_INIT] THEN
  ABBREV_TAC `t = fse_symbol cs alog u` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[fse_init] THEN COND_CASES_TAC THEN REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `&1 <= EL t (cs:int list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    MP_TAC(ISPEC `EL t (cs:int list)` INT_OF_NUM_OF_INT) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FSE_INIT_LE THEN ASM_REWRITE_TAC[];
    ARITH_TAC;
    MATCH_MP_TAC(ARITH_RULE `!i c. c < i ==> i + c < 2 * i`) THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `CARD {v | v < 2 EXP alog /\ fse_symbol cs alog v = t}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM; EXTENSION] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[LT_TRANS];
          DISCH_THEN(MP_TAC o SPEC `u:num`) THEN ASM_REWRITE_TAC[LT_REFL]];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{v:num | v < 2 EXP alog}` THEN
        REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]];
      MATCH_MP_TAC FSE_SYMBOL_CARD_LE THEN ASM_REWRITE_TAC[]]]);;

let FSE_NBITS_BASE = prove
 (`!cs alog u.
        5 <= alog /\ fse_valid cs alog /\ u < 2 EXP alog
        ==> 1 <= fse_next cs alog u /\
            fse_next cs alog u < 2 EXP (alog + 1) /\
            fse_nbits cs alog u <= alog /\
            2 EXP alog <= 2 EXP (fse_nbits cs alog u) * fse_next cs alog u /\
            2 EXP (fse_nbits cs alog u) * fse_next cs alog u <
            2 EXP (alog + 1) /\
            fse_base cs alog u + 2 EXP (fse_nbits cs alog u) <= 2 EXP alog`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FSE_NEXT_BOUNDS) THEN
  REWRITE_TAC[fse_base; fse_nbits] THEN
  ABBREV_TAC `x = fse_next cs alog u` THEN
  SUBGOAL_THEN `1 <= x /\ x < 2 EXP (alog + 1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXP_ADD; EXP_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `1 <= bitsize x /\ bitsize x <= alog + 1 /\
    2 EXP (bitsize x - 1) <= x /\ x < 2 EXP bitsize x`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE; BITSIZE; LE_BITSIZE; ARITH_EQ; SUB_REFL; EXP] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BITSIZE_REV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `b = bitsize x` THEN
  SUBGOAL_THEN
   `2 EXP ((alog + 1) - b) * 2 EXP (b - 1) = 2 EXP alog /\
    2 EXP ((alog + 1) - b) * 2 EXP b = 2 EXP (alog + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `p = 2 EXP ((alog + 1) - b)` THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP alog <= p * x` ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `2 EXP alog`)) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p * x + p <= 2 EXP (alog + 1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
      check (fun th -> is_eq(concl th) &&
                       rhs(concl th) = `2 EXP (alog + 1)`)) THEN
    REWRITE_TAC[ARITH_RULE `p * x + p = p * (x + 1)`; LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p * x + p <= 2 EXP (alog + 1)` THEN
  UNDISCH_TAC `2 EXP alog <= p * x` THEN
  UNDISCH_TAC `~(p = 0)` THEN UNDISCH_TAC `1 <= b` THEN
  REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Prefixes of fse_syms, and the number of counts of -1 among the first u,   *)
(* for the loop invariants in the proofs of zstd's code.                     *)
(* ------------------------------------------------------------------------- *)

let fse_symsp = new_definition
 `fse_symsp (cs:int list) s =
    ITLIST APPEND
     (list_of_seq (\t. REPLICATE (num_of_int(max (EL t cs) (&0))) t) s) []`;;

let FSE_SYMSP_0 = prove
 (`!cs. fse_symsp cs 0 = []`,
  REWRITE_TAC[fse_symsp; LIST_OF_SEQ_0; ITLIST]);;

let FSE_SYMSP_SUC = prove
 (`!cs s. fse_symsp cs (s + 1) =
          APPEND (fse_symsp cs s)
                 (REPLICATE (num_of_int(max (EL s cs) (&0))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fse_symsp; LIST_OF_SEQ_ADD1] THEN
  REWRITE_TAC[ITLIST_APPEND; ITLIST] THEN
  ONCE_REWRITE_TAC[ITLIST_APPEND_NIL] THEN REWRITE_TAC[APPEND_NIL]);;

let LENGTH_FSE_SYMSP = prove
 (`!cs s. LENGTH(fse_symsp cs s) = fse_cum cs s`,
  REWRITE_TAC[fse_symsp; LENGTH_FSE_SYMS_PREFIX]);;

let FSE_SYMS_SYMSP = prove
 (`!cs. fse_syms cs = fse_symsp cs (LENGTH cs)`,
  REWRITE_TAC[fse_syms; fse_symsp]);;

let fse_nlow = new_definition
 `fse_nlow (cs:int list) u =
    LENGTH(FILTER (\t. EL t cs = -- &1) (list_of_seq (\t. t) u))`;;

let FSE_NLOW_0 = prove
 (`!cs. fse_nlow cs 0 = 0`,
  REWRITE_TAC[fse_nlow; LIST_OF_SEQ_0; FILTER; LENGTH]);;

let FSE_NLOW_SUC = prove
 (`!cs u. fse_nlow cs (u + 1) =
          fse_nlow cs u + (if EL u cs = -- &1 then 1 else 0)`,
  REWRITE_TAC[fse_nlow; LENGTH_FILTER_LIST_OF_SEQ_SUC]);;

let FSE_NLOW_LENGTH = prove
 (`!cs. fse_nlow cs (LENGTH cs) = LENGTH(fse_lowprob cs)`,
  REWRITE_TAC[fse_nlow; fse_lowprob]);;

let FSE_NLOW_MONO = prove
 (`!cs m n. m <= n ==> fse_nlow cs m <= fse_nlow cs n`,
  REWRITE_TAC[fse_nlow; LENGTH_FILTER_LIST_OF_SEQ_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Reading FSE table descriptions in the zstd dialect (fse_counts T and      *)
(* fse_zeros T, where every position is inside), as zstd's FSE_readNCount    *)
(* does. The relations are deterministic, so that the reading from a         *)
(* position can be followed as a chain of equivalences: for the repeat       *)
(* flags, a flag 3 and the 11 after it, the last flag, 12 flags 3 at a time  *)
(* and the last ones.                                                        *)
(* ------------------------------------------------------------------------- *)

let FSE_INSIDE_T = prove
 (`!l q. fse_inside T l q`,
  REWRITE_TAC[fse_inside]);;

let FSE_ZEROS_STEP3 = prove
 (`!l k z p r.
        zstd_bits l p 2 = 3 /\ k < 11
        ==> (fse_zeros T l (k,z,p) r <=> fse_zeros T l (k + 1,z + 3,p + 2) r)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_ZEROS_CASES] THEN
  REWRITE_TAC[PAIR_EQ; FSE_INSIDE_T] THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (is_var o rhs o concl))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `z:num`; `p:num`] THEN
    ASM_REWRITE_TAC[]]);;

let FSE_ZEROS_STEP11 = prove
 (`!l z p r.
        zstd_bits l p 2 = 3
        ==> (fse_zeros T l (11,z,p) r <=>
             fse_zeros T l (0,z + 3,fse_reload T l (p + 2)) r)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_ZEROS_CASES] THEN
  REWRITE_TAC[PAIR_EQ; FSE_INSIDE_T] THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (is_var o rhs o concl))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:num`; `p:num`] THEN
    ASM_REWRITE_TAC[]]);;

let FSE_ZEROS_STOP = prove
 (`!l k z p r.
        zstd_bits l p 2 < 3
        ==> (fse_zeros T l (k,z,p) r <=>
             r = (z + zstd_bits l p 2,fse_reload T l (p + 2)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_ZEROS_CASES] THEN
  REWRITE_TAC[PAIR_EQ; FSE_INSIDE_T] THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (is_var o rhs o concl))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `z:num`; `p:num`] THEN
    ASM_REWRITE_TAC[]]);;

let ZSTD_BITS_ONES_SPLIT = prove
 (`!l p j.
        zstd_bits l p (2 + 2 * j) = 2 EXP (2 + 2 * j) - 1
        ==> zstd_bits l p 2 = 3 /\
            zstd_bits l (p + 2) (2 * j) = 2 EXP (2 * j) - 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ZSTD_BITS_ADD; EXP_ADD] THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `2`] ZSTD_BITS_BOUND) THEN
  MP_TAC(SPECL [`l:byte list`; `p + 2`; `2 * j`] ZSTD_BITS_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let FSE_ZEROS_ONES = prove
 (`!l j k z p r.
        k + j <= 11 /\ zstd_bits l p (2 * j) = 2 EXP (2 * j) - 1
        ==> (fse_zeros T l (k,z,p) r <=>
             fse_zeros T l (k + j,z + 3 * j,p + 2 * j) r)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC j = 2 + 2 * j`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ZSTD_BITS_ONES_SPLIT) THEN
  MP_TAC(SPECL [`l:byte list`; `k:num`; `z:num`; `p:num`; `r:num#num`]
    FSE_ZEROS_STEP3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `z + 3`; `p + 2`; `r:num#num`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + j = k + SUC j /\
                          (z + 3) + 3 * j = z + 3 * SUC j /\
                          (p + 2) + 2 * j = p + 2 + 2 * j`]);;

let FSE_ZEROS_12 = prove
 (`!l z p r.
        zstd_bits l p 24 = 2 EXP 24 - 1
        ==> (fse_zeros T l (0,z,p) r <=>
             fse_zeros T l (0,z + 36,fse_reload T l (p + 24)) r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `11`] ZSTD_BITS_ONES_SPLIT) THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `22`; `2`] ZSTD_BITS_ADD) THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `22`] ZSTD_BITS_BOUND) THEN
  MP_TAC(SPECL [`l:byte list`; `p + 22`; `2`] ZSTD_BITS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `zstd_bits l p 22 = 4194303 /\ zstd_bits l (p + 22) 2 = 3`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `11`; `0`; `z:num`; `p:num`; `r:num#num`]
    FSE_ZEROS_ONES) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[FSE_ZEROS_STEP11] THEN
  REWRITE_TAC[ARITH_RULE `(z + 33) + 3 = z + 36 /\ (p + 22) + 2 = p + 24`]);;

let FSE_ZEROS_LAST = prove
 (`!l j z p r.
        j <= 11 /\ zstd_bits l p (2 * j) = 2 EXP (2 * j) - 1 /\
        zstd_bits l (p + 2 * j) 2 < 3
        ==> (fse_zeros T l (0,z,p) r <=>
             r = (z + 3 * j + zstd_bits l (p + 2 * j) 2,
                  fse_reload T l (p + 2 * j + 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `j:num`; `0`; `z:num`; `p:num`; `r:num#num`]
    FSE_ZEROS_ONES) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[FSE_ZEROS_STOP; ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* A field as zstd reads it, the points it uses up, and the position after a *)
(* refill of the window, inside the input or wrapping around into its last   *)
(* 32 bits.                                                                  *)
(* ------------------------------------------------------------------------- *)

let FSE_FIELD_ALT = prove
 (`!l pts p.
        fse_field l pts p =
        let nb = bitsize(pts + 1) in
        let small = 2 EXP nb - (pts + 2) in
        if zstd_bits l p (nb - 1) < small
        then (zstd_bits l p (nb - 1),p + nb - 1)
        else if zstd_bits l p nb < 2 EXP (nb - 1)
        then (zstd_bits l p nb,p + nb)
        else (zstd_bits l p nb - small,p + nb)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fse_field] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[ZSTD_BITS_SPLIT; ARITH_RULE `n - 1 <= n`]);;

let FSE_FIELD_BOUNDS = prove
 (`!l pts p v q.
        1 <= pts /\ fse_field l pts p = (v,q)
        ==> 2 <= bitsize(pts + 1) /\ v <= pts + 1 /\
            (q = p + bitsize(pts + 1) - 1 \/ q = p + bitsize(pts + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= bitsize(pts + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n <= 1)`; BITSIZE_LE] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[FSE_FIELD_ALT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb = bitsize(pts + 1)` THEN
  SUBGOAL_THEN `2 EXP (nb - 1) <= pts + 1 /\ pts + 1 < 2 EXP nb /\
                2 EXP nb = 2 * 2 EXP (nb - 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN REWRITE_TAC[BITSIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BITSIZE_REV THEN ARITH_TAC;
      REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `nb:num`] ZSTD_BITS_BOUND) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ]) THEN
  ASM_ARITH_TAC);;

let FSE_POINTS_LE = prove
 (`!v pts. 1 <= pts /\ v <= pts + 1 ==> fse_points v <= pts`,
  REWRITE_TAC[fse_points] THEN ARITH_TAC);;

let FSE_RELOAD_NOWRAP = prove
 (`!l p. 8 <= LENGTH l /\ p < 8 * LENGTH l ==> fse_reload T l p = p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_reload] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[ARITH_RULE `8 <= n ==> MAX n 8 = n`; GSYM NOT_LT]);;

let FSE_RELOAD_WRAP = prove
 (`!l p. 8 <= LENGTH l /\ 8 * LENGTH l <= p + 32
         ==> fse_reload T l p =
             8 * (LENGTH l - 4) + ((p + 32) - 8 * LENGTH l) MOD 32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_reload] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[ARITH_RULE `8 <= n ==> MAX n 8 = n`] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `(p + 32) - 8 * LENGTH(l:byte list) =
                  1 * 32 + (p - 8 * LENGTH l)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `((p + 32) - 8 * LENGTH(l:byte list)) MOD 32 =
                  (p + 32) - 8 * LENGTH l` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The steps of fse_counts T: no more counts once there are n of them, the   *)
(* last field, which uses up the points left, the other fields, and a        *)
(* probability 0 with the repeat flags after it.                             *)
(* ------------------------------------------------------------------------- *)

let FSE_FIELD_SAME_TAC : tactic = fun (asl,w as gl) ->
  let is_field th =
    let c = concl th in
    is_eq c &&
    (try fst(dest_const(fst(strip_comb(lhs c)))) = "fse_field"
     with Failure _ -> false) in
  let fths = filter is_field (map snd asl) in
  let rec find2 l =
    match l with
      th1::rest ->
        (try let th2 = find (fun th -> lhs(concl th) = lhs(concl th1) &&
                                       rhs(concl th) <> rhs(concl th1)) rest in
             (th1,th2)
         with Failure _ -> find2 rest)
    | [] -> failwith "FSE_FIELD_SAME_TAC" in
  let th1,th2 = find2 fths in
  STRIP_ASSUME_TAC(REWRITE_RULE[PAIR_EQ] (TRANS (SYM th1) th2)) gl;;

let FSE_VAR_SUBST_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_var(lhs(concl th)) && is_var(rhs(concl th)))));;

let FSE_COUNTS_FULL = prove
 (`!zstd l n pts cs p r.
        ~(LENGTH cs < n) ==> ~fse_counts zstd l n (pts,cs,p) r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[FSE_COUNTS_CASES] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN FSE_VAR_SUBST_TAC THEN ASM_MESON_TAC[]);;

let FSE_COUNTS_LAST = prove
 (`!l n pts cs p v q r.
        1 <= pts /\ LENGTH cs < n /\ fse_field l pts p = (v,q) /\
        fse_points v = pts
        ==> (fse_counts T l n (pts,cs,p) r <=> r = (APPEND cs [&v - &1],q))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_COUNTS_CASES] THEN
  REWRITE_TAC[PAIR_EQ; FSE_INSIDE_T] THEN EQ_TAC THENL
   [STRIP_TAC THEN FSE_VAR_SUBST_TAC THEN FSE_FIELD_SAME_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_var(rhs(concl th))))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[fse_points]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`pts:num`; `cs:int list`; `p:num`; `v:num`; `q:num`] THEN
    ASM_REWRITE_TAC[]]);;

let FSE_COUNTS_NEXT = prove
 (`!l n pts cs p v q r.
        LENGTH cs < n /\ fse_field l pts p = (v,q) /\
        ~(v = 1) /\ fse_points v < pts
        ==> (fse_counts T l n (pts,cs,p) r <=>
             fse_counts T l n
               (pts - fse_points v,APPEND cs [&v - &1],fse_reload T l q) r)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_COUNTS_CASES] THEN
  REWRITE_TAC[PAIR_EQ; FSE_INSIDE_T] THEN EQ_TAC THENL
   [STRIP_TAC THEN FSE_VAR_SUBST_TAC THEN FSE_FIELD_SAME_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_var(rhs(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`pts:num`; `cs:int list`; `p:num`; `v:num`; `q:num`] THEN
    ASM_REWRITE_TAC[]]);;

let FSE_COUNTS_ZERO = prove
 (`!l n pts cs p q r.
        1 <= pts /\ LENGTH cs < n /\ fse_field l pts p = (1,q)
        ==> (fse_counts T l n (pts,cs,p) r <=>
             ?z q'. fse_zeros T l (0,0,fse_reload T l q) (z,q') /\
                    fse_counts T l n
                     (pts,APPEND cs (REPLICATE (z + 1) (&0)),q') r)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_COUNTS_CASES] THEN
  REWRITE_TAC[PAIR_EQ; FSE_INSIDE_T] THEN EQ_TAC THENL
   [STRIP_TAC THEN FSE_VAR_SUBST_TAC THEN FSE_FIELD_SAME_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_var(rhs(concl th))))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[fse_points]) THEN
    ASM_REWRITE_TAC[] THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[];
    STRIP_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`pts:num`; `cs:int list`; `p:num`; `q:num`;
                          `z:num`; `q':num`] THEN
    ASM_REWRITE_TAC[]]);;

let FSE_COUNTS_STEP = prove
 (`!l n pts cs p v q.
        1 <= pts /\ LENGTH cs < n /\ fse_field l pts p = (v,q)
        ==> ((pts + 1) - fse_points v = 1 /\
             (!r. fse_counts T l n (pts,cs,p) r <=>
                  r = (APPEND cs [&v - &1],q))) \/
            (2 <= (pts + 1) - fse_points v /\ ~(v = 1) /\
             (!r. fse_counts T l n (pts,cs,p) r <=>
                  fse_counts T l n
                   ((pts + 1) - fse_points v - 1,APPEND cs [&v - &1],
                    fse_reload T l q) r)) \/
            (2 <= (pts + 1) - fse_points v /\ v = 1 /\
             (!r. fse_counts T l n (pts,cs,p) r <=>
                  ?z q'. fse_zeros T l (0,0,fse_reload T l q) (z,q') /\
                         fse_counts T l n
                          ((pts + 1) - fse_points v - 1,
                           APPEND cs (REPLICATE (z + 1) (&0)),q') r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `pts:num`; `p:num`; `v:num`; `q:num`]
    FSE_FIELD_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `fse_points v <= pts` ASSUME_TAC THENL
   [MATCH_MP_TAC FSE_POINTS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `fse_points v = pts` THENL
   [DISJ1_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC FSE_COUNTS_LAST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `v = 1` THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[fse_points] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SUB_0; ADD_SUB] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC FSE_COUNTS_ZERO THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(pts + 1) - fse_points v - 1 = pts - fse_points v`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC FSE_COUNTS_NEXT THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let FSE_ZEROS_LAST_COUNTS = prove
 (`!l n pts cs zz ofs bc j.
        j <= 11 /\ zstd_bits l (8 * ofs + bc) (2 * j) = 2 EXP (2 * j) - 1 /\
        zstd_bits l (8 * ofs + bc + 2 * j) 2 < 3
        ==> !r. (?z q'. fse_zeros T l (0,zz,8 * ofs + bc) (z,q') /\
                        fse_counts T l n
                          (pts,APPEND cs (REPLICATE (z + 1) (&0)),q') r) <=>
                fse_counts T l n
                  (pts,
                   APPEND cs (REPLICATE
                    ((zz + 3 * j + zstd_bits l (8 * ofs + bc + 2 * j) 2) + 1)
                    (&0)),
                   fse_reload T l (8 * ofs + bc + 2 * j + 2)) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[GSYM ADD_ASSOC]
   (SPECL [`l:byte list`; `j:num`; `zz:num`; `8 * ofs + bc`]
     FSE_ZEROS_LAST)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; PAIR_EQ]) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The result of fse_ncount T from that of fse_counts T, and its size.       *)
(* ------------------------------------------------------------------------- *)

let FSE_NCOUNT_RESULT = prove
 (`!l n alog cs q.
        zstd_bits l 0 4 + 5 = alog /\ alog <= 15 /\
        (!r. fse_counts T l n (2 EXP alog,[],4) r <=> r = (cs,q))
        ==> !cs' alog' m.
                fse_ncount T 15 n l (cs',alog',m) <=>
                cs' = cs /\ alog' = alog /\ q <= 8 * LENGTH l /\
                m = (q + 7) DIV 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fse_ncount] THEN
  ASM_CASES_TAC `alog':num = alog` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q':num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `q':num = q`))
    THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[]]);;

let FSE_NCOUNT_FAIL = prove
 (`!l n alog.
        zstd_bits l 0 4 + 5 = alog /\
        (!r. ~fse_counts T l n (2 EXP alog,[],4) r)
        ==> !r. ~fse_ncount T 15 n l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; fse_ncount] THEN ASM_MESON_TAC[]);;

let FSE_NCOUNT_ALOG = prove
 (`!l n. 15 < zstd_bits l 0 4 + 5 ==> !r. ~fse_ncount T 15 n l r`,
  REWRITE_TAC[FORALL_PAIR_THM; fse_ncount] THEN ARITH_TAC);;

let FSE_NCOUNT_LENGTH = prove
 (`!zstd maxalog n l cs alog m.
        fse_ncount zstd maxalog n l (cs,alog,m) ==> m <= LENGTH l`,
  REWRITE_TAC[fse_ncount] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LE_LDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Inputs with the same bits and the same rounded-up length give the same    *)
(* counts; so an input of fewer than 8 bytes has the description of 8 bytes  *)
(* with the same bits, provided that it is within the input.                 *)
(* ------------------------------------------------------------------------- *)

let FSE_ZEROS_CONG = prove
 (`!l l'. (!p n. zstd_bits l' p n = zstd_bits l p n) /\
          MAX (LENGTH l') 8 = MAX (LENGTH l) 8
          ==> !x y. fse_zeros T l x y ==> fse_zeros T l' x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p. fse_reload T l' p = fse_reload T l p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[fse_reload]; ALL_TAC] THEN
  MATCH_MP_TAC FSE_ZEROS_INDUCT THEN REWRITE_TAC[FSE_INSIDE_T] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM(ASSUME `!p n. zstd_bits l' p n = zstd_bits l p n`);
              GSYM(ASSUME `!p. fse_reload T l' p = fse_reload T l p`)] THEN
  MESON_TAC[FSE_ZEROS_RULES; FSE_INSIDE_T]);;

let FSE_COUNTS_CONG = prove
 (`!l l' n. (!p k. zstd_bits l' p k = zstd_bits l p k) /\
            MAX (LENGTH l') 8 = MAX (LENGTH l) 8
            ==> !x y. fse_counts T l n x y ==> fse_counts T l' n x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p. fse_reload T l' p = fse_reload T l p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[fse_reload]; ALL_TAC] THEN
  SUBGOAL_THEN `!pts p. fse_field l' pts p = fse_field l pts p` ASSUME_TAC
  THENL [ASM_REWRITE_TAC[fse_field]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `l':byte list`] FSE_ZEROS_CONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC FSE_COUNTS_INDUCT THEN REWRITE_TAC[FSE_INSIDE_T] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM(ASSUME `!pts p. fse_field l' pts p = fse_field l pts p`);
              GSYM(ASSUME `!p. fse_reload T l' p = fse_reload T l p`)] THEN
  ASM_MESON_TAC[FSE_COUNTS_RULES; FSE_INSIDE_T]);;

let FSE_NCOUNT_SHORT = prove
 (`!n l l' cs alog m.
        LENGTH l < 8 /\ LENGTH l' = 8 /\
        (!p k. zstd_bits l' p k = zstd_bits l p k)
        ==> (fse_ncount T 15 n l (cs,alog,m) <=>
             fse_ncount T 15 n l' (cs,alog,m) /\ m <= LENGTH l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAX (LENGTH(l':byte list)) 8 = 8 /\
                MAX (LENGTH(l:byte list)) 8 = 8`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. fse_counts T l n x y <=> fse_counts T l' n x y`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`l:byte list`; `l':byte list`; `n:num`] FSE_COUNTS_CONG) THEN
    MP_TAC(SPECL [`l':byte list`; `l:byte list`; `n:num`] FSE_COUNTS_CONG) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. (q + 7) DIV 8 <= LENGTH(l:byte list) <=> q <= 8 * LENGTH l`
  ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC[LE_LDIV_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[fse_ncount] THEN EQ_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
   (fun th -> concl th = `alog = zstd_bits l 0 4 + 5`)) THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    UNDISCH_TAC `m <= LENGTH(l:byte list)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The table descriptions determine their probabilities, the number of       *)
(* bytes they use and their Accuracy_Log, which are within their bounds.     *)
(* ------------------------------------------------------------------------- *)

let FSE_ZEROS_DET = prove
 (`!zstd (l:byte list) x r r'.
        fse_zeros zstd l x r /\ fse_zeros zstd l x r' ==> r = r'`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FSE_ZEROS_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[FSE_ZEROS_CASES] THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_var(rhs(concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  ASM_REWRITE_TAC[] THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

let FSE_ZEROS_SAME_TAC : tactic = fun (asl,w as gl) ->
  let is_z th = try fst(dest_const(fst(strip_comb(concl th)))) = "fse_zeros"
                with Failure _ -> false in
  let zths = filter is_z (map snd asl) in
  let rec find2 l =
    match l with
      th1::rest ->
        (try let th2 = find (fun th -> rator(concl th) = rator(concl th1) &&
                                       rand(concl th) <> rand(concl th1))
                            rest in
             (th1,th2)
         with Failure _ -> find2 rest)
    | [] -> failwith "FSE_ZEROS_SAME_TAC" in
  let th1,th2 = find2 zths in
  STRIP_ASSUME_TAC(REWRITE_RULE[PAIR_EQ]
    (MATCH_MP FSE_ZEROS_DET (CONJ th1 th2))) gl;;

let FSE_DET_CASE_TAC =
  FSE_FIELD_SAME_TAC THEN FSE_VAR_SUBST_TAC THEN
  TRY(FSE_ZEROS_SAME_TAC THEN FSE_VAR_SUBST_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let c = concl th in
    is_eq c && is_var(lhs c) && not(free_in (lhs c) (rhs c))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fse_points; ARITH_EQ]) THEN
  REWRITE_TAC[] THEN
  FIRST [MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC;
         FIRST_ASSUM(fun th ->
           let c = concl th in
           if is_imp c && is_forall(rand c) then
             MP_TAC th THEN ANTS_TAC THENL
              [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]
           else NO_TAC)];;

let FSE_COUNTS_DET = prove
 (`!zstd (l:byte list) n pts cs p r r'.
        1 <= pts /\ fse_counts zstd l n (pts,cs,p) r /\
        fse_counts zstd l n (pts,cs,p) r'
        ==> r = r'`,
  SUBGOAL_THEN
   `!zstd (l:byte list) n x r.
        fse_counts zstd l n x r
        ==> 1 <= FST x ==> !r'. fse_counts zstd l n x r' ==> r = r'`
   (fun th -> MESON_TAC[th; FST]) THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FSE_COUNTS_INDUCT THEN REWRITE_TAC[FST] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[FSE_COUNTS_CASES] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FSE_VAR_SUBST_TAC THEN
  FSE_DET_CASE_TAC);;

let FSE_NCOUNT_DET = prove
 (`!zstd ma ma' n (l:byte list) cs alog m cs' alog' m'.
        fse_ncount zstd ma n l (cs,alog,m) /\
        fse_ncount zstd ma' n l (cs',alog',m')
        ==> cs' = cs /\ alog' = alog /\ m' = m`,
  REWRITE_TAC[fse_ncount] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q':num` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `alog':num = alog` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`zstd:bool`; `l:byte list`; `n:num`; `2 EXP alog`;
                 `[]:int list`; `4`; `(cs:int list,q:num)`;
                 `(cs':int list,q':num)`] FSE_COUNTS_DET) THEN
  ASM_REWRITE_TAC[PAIR_EQ; ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0;
                  ARITH_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FSE_COUNTS_LENGTH_LE = prove
 (`!zstd (l:byte list) n x r. fse_counts zstd l n x r ==> LENGTH(FST r) <= n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FSE_COUNTS_INDUCT THEN
  REWRITE_TAC[FST; LENGTH_APPEND; LENGTH] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_ARITH_TAC);;

let FSE_NCOUNT_BOUNDS = prove
 (`!zstd ma n (l:byte list) cs alog m.
        fse_ncount zstd ma n l (cs,alog,m)
        ==> LENGTH cs <= n /\ 5 <= alog /\ alog <= ma /\ m <= LENGTH l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_NCOUNT_LENGTH) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[fse_ncount] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY ASM_ARITH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FSE_COUNTS_LENGTH_LE) THEN
  REWRITE_TAC[FST]);;

(* ------------------------------------------------------------------------- *)
(* The probabilities of a description fill the table exactly.                *)
(* ------------------------------------------------------------------------- *)

let FSE_CUM_APPEND = prove
 (`!cs ds s. s <= LENGTH cs ==> fse_cum (APPEND cs ds) s = fse_cum cs s`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[fse_cum; ADD1] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `s + 1 <= n ==> s <= n`] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `s + 1 <= n ==> s < n`]);;

let FSE_NLOW_APPEND = prove
 (`!cs ds u. u <= LENGTH cs ==> fse_nlow (APPEND cs ds) u = fse_nlow cs u`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[FSE_NLOW_0; ADD1; FSE_NLOW_SUC] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `u + 1 <= n ==> u <= n`] THEN
  ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `u + 1 <= n ==> u < n`]);;

let FSE_POINTS_SNOC = prove
 (`!cs c. LENGTH(fse_syms (APPEND cs [c])) +
          LENGTH(fse_lowprob (APPEND cs [c])) =
          (LENGTH(fse_syms cs) + LENGTH(fse_lowprob cs)) +
          num_of_int(max c (&0)) + (if c = -- &1 then 1 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_FSE_SYMS; GSYM FSE_NLOW_LENGTH; LENGTH_APPEND; LENGTH;
              ARITH_RULE `n + SUC 0 = n + 1`] THEN
  REWRITE_TAC[FSE_CUM_SUC; FSE_NLOW_SUC] THEN
  SIMP_TAC[FSE_CUM_APPEND; FSE_NLOW_APPEND; LE_REFL] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN ARITH_TAC);;

let FSE_POINTS_COUNT = prove
 (`!v. num_of_int(max (&v - &1) (&0)) +
       (if &v - &1:int = -- &1 then 1 else 0) = fse_points v`,
  GEN_TAC THEN REWRITE_TAC[fse_points] THEN ASM_CASES_TAC `v = 0` THEN
  ASM_REWRITE_TAC[] THENL
   [CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
    CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `&v - &1:int = &(v - 1)` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_SUB THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `max (&n) (&0):int = &n`; NUM_OF_INT_OF_NUM;
                INT_ARITH `~(&n:int = -- &1)`] THEN
    ARITH_TAC]);;

let FSE_POINTS_ZEROS = prove
 (`!k cs. LENGTH(fse_syms (APPEND cs (REPLICATE k (&0)))) +
          LENGTH(fse_lowprob (APPEND cs (REPLICATE k (&0)))) =
          LENGTH(fse_syms cs) + LENGTH(fse_lowprob cs)`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; APPEND_NIL] THEN GEN_TAC THEN
  SUBGOAL_THEN `APPEND (cs:int list) (CONS (&0) (REPLICATE k (&0))) =
                APPEND (APPEND cs [&0]) (REPLICATE k (&0))`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FSE_POINTS_SNOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN ARITH_TAC);;

let FSE_COUNTS_POINTS = prove
 (`!zstd l n x y.
        fse_counts zstd l n x y
        ==> ALL (\c. -- &1 <= c) (FST(SND x))
            ==> ALL (\c. -- &1 <= c) (FST y) /\
                LENGTH(fse_syms (FST y)) + LENGTH(fse_lowprob (FST y)) =
                (LENGTH(fse_syms (FST(SND x))) +
                 LENGTH(fse_lowprob (FST(SND x)))) + FST x`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`zstd:bool`; `l:byte list`; `n:num`;
   `\x:num#int list#num y:int list#num.
      ALL (\c. -- &1 <= c) (FST(SND x))
      ==> ALL (\c. -- &1 <= c) (FST y) /\
          LENGTH(fse_syms (FST y)) + LENGTH(fse_lowprob (FST y)) =
          (LENGTH(fse_syms (FST(SND x))) +
           LENGTH(fse_lowprob (FST(SND x)))) + FST x`]
    FSE_COUNTS_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[FST; SND; ALL_APPEND; ALL] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [STRIP_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[FSE_POINTS_SNOC; FSE_POINTS_COUNT] THEN
    REWRITE_TAC[INT_ARITH `-- &1:int <= &v - &1`];
    STRIP_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check
      (fun th -> is_imp(concl th) && free_in `fse_syms` (concl th))) THEN
    ASM_REWRITE_TAC[FSE_POINTS_SNOC; FSE_POINTS_COUNT;
                    INT_ARITH `-- &1:int <= &v - &1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check
      (fun th -> is_imp(concl th) && free_in `fse_syms` (concl th))) THEN
    ASM_REWRITE_TAC[FSE_POINTS_ZEROS; ALL_REPLICATE] THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN REWRITE_TAC[]]);;

let FSE_NCOUNT_VALID = prove
 (`!zstd maxalog n l cs alog m.
        fse_ncount zstd maxalog n l (cs,alog,m) ==> fse_valid cs alog`,
  REWRITE_TAC[fse_ncount; fse_valid] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FSE_COUNTS_POINTS) THEN
  REWRITE_TAC[FST; SND; ALL] THEN
  REWRITE_TAC[LENGTH_FSE_SYMS; GSYM FSE_NLOW_LENGTH; LENGTH; fse_cum;
              FSE_NLOW_0; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The steps of fse_weights: too many weights, the last two, and the update  *)
(* of the state to decode next with the bits after it.                       *)
(* ------------------------------------------------------------------------- *)

let FSE_WEIGHTS_FULL = prove
 (`!cs alog (st:byte list) s s' q ws w.
        ~(LENGTH ws + 2 <= 255) ==> ~fse_weights cs alog st (s,s',q,ws) w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[FSE_WEIGHTS_CASES] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_var(rhs(concl th))))) THEN
  ASM_MESON_TAC[]);;

let FSE_WEIGHTS_STOP = prove
 (`!cs alog (st:byte list) s s' q ws w.
        LENGTH ws + 2 <= 255 /\ q < fse_nbits cs alog s
        ==> (fse_weights cs alog st (s,s',q,ws) w <=>
             w = APPEND ws [fse_symbol cs alog s; fse_symbol cs alog s'])`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_WEIGHTS_CASES] THEN
  REWRITE_TAC[PAIR_EQ] THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_var(rhs(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:num`; `s':num`; `q:num`; `ws:num list`] THEN
    ASM_REWRITE_TAC[]]);;

let FSE_WEIGHTS_STEP = prove
 (`!cs alog (st:byte list) s s' q ws w.
        LENGTH ws + 2 <= 255 /\ fse_nbits cs alog s <= q
        ==> (fse_weights cs alog st (s,s',q,ws) w <=>
             fse_weights cs alog st
              (s',fse_base cs alog s + zstd_back st q (fse_nbits cs alog s),
               q - fse_nbits cs alog s,APPEND ws [fse_symbol cs alog s]) w)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FSE_WEIGHTS_CASES] THEN
  REWRITE_TAC[PAIR_EQ] THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_var(rhs(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:num`; `s':num`; `q:num`; `ws:num list`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The weights of the stream st for the probabilities cs and Accuracy_Log    *)
(* alog, fse_stream cs alog st w, as in fse_weight_block from the end of st; *)
(* so the weights of a block are those of the stream after its description,  *)
(* which zstd reads with an Accuracy_Log of at most 15.                      *)
(* ------------------------------------------------------------------------- *)

let ZSTD_END_UNIQUE = prove
 (`!(st:byte list) r r'. zstd_end st r /\ zstd_end st r' ==> r = r'`,
  REWRITE_TAC[zstd_end] THEN MESON_TAC[LT_CASES]);;

let fse_stream = new_definition
 `fse_stream cs alog (st:byte list) w <=>
    ?r. zstd_end st r /\ 2 * alog <= r /\
        fse_weights cs alog st
          (zstd_back st r alog,zstd_back st (r - alog) alog,r - 2 * alog,[])
          w`;;

let FSE_STREAM_EQ = prove
 (`!cs alog (st:byte list) r w.
        zstd_end st r /\ 2 * alog <= r
        ==> (fse_stream cs alog st w <=>
             fse_weights cs alog st
              (zstd_back st r alog,zstd_back st (r - alog) alog,
               r - 2 * alog,[]) w)`,
  REWRITE_TAC[fse_stream] THEN MESON_TAC[ZSTD_END_UNIQUE]);;

let FSE_STREAM_SHORT = prove
 (`!cs alog (st:byte list) r w.
        zstd_end st r /\ r < 2 * alog ==> ~fse_stream cs alog st w`,
  REWRITE_TAC[fse_stream] THEN MESON_TAC[ZSTD_END_UNIQUE; NOT_LE]);;

let FSE_STREAM_NOEND = prove
 (`!cs alog (st:byte list) w.
        (!r. ~zstd_end st r) ==> ~fse_stream cs alog st w`,
  REWRITE_TAC[fse_stream] THEN MESON_TAC[]);;

let ZSTD_SUBLIST_SUB_LIST = prove
 (`!(l:byte list) a n.
        a + n <= LENGTH l ==> zstd_sublist l a n = SUB_LIST(a,n) l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[zstd_sublist; LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_SUB_LIST] THEN
  ASM_SIMP_TAC[ARITH_RULE `a + n <= l ==> MIN n (l - a) = n`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_SUB_LIST]);;

let LENGTH_ZSTD_SUBLIST = prove
 (`!(l:byte list) a n. LENGTH(zstd_sublist l a n) = n`,
  REWRITE_TAC[zstd_sublist; LENGTH_LIST_OF_SEQ]);;

let FSE_WEIGHT_BLOCK_STREAM = prove
 (`!(blk:byte list) cs alog m w.
        fse_ncount T 15 256 blk (cs,alog,m)
        ==> (fse_weight_block T blk w <=>
             alog <= 6 /\ LENGTH cs <= (if alog = 6 then 12 else 92) /\
             fse_stream cs alog (zstd_sublist blk m (LENGTH blk - m)) w)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fse_weight_block; fse_stream] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `cs':int list` (X_CHOOSE_THEN `alog':num`
      (X_CHOOSE_THEN `m':num` (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC)))) THEN
    MP_TAC(SPECL [`T`; `6`; `15`; `256`; `blk:byte list`; `cs':int list`;
                  `alog':num`; `m':num`; `cs:int list`; `alog:num`; `m:num`]
      FSE_NCOUNT_DET) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `fse_ncount T 6 256 blk (cs',alog',m')` THEN
      REWRITE_TAC[fse_ncount] THEN ARITH_TAC;
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`cs:int list`; `alog:num`; `m:num`; `r:num`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `fse_ncount T 15 256 blk (cs,alog,m)` THEN
    REWRITE_TAC[fse_ncount] THEN ASM_MESON_TAC[]]);;

let FSE_WEIGHT_BLOCK_NONE = prove
 (`!(blk:byte list) w.
        (!r. ~fse_ncount T 15 256 blk r) ==> ~fse_weight_block T blk w`,
  REWRITE_TAC[fse_weight_block; FORALL_PAIR_THM; fse_ncount] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cs:int list`; `alog:num`; `m:num`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ARITH_RULE `a <= 6 ==> a <= 15`]);;

(* ------------------------------------------------------------------------- *)
(* The weights of a block, and the description of a Huffman tree at the      *)
(* start of a list of bytes, are determined by them, and the weights of a    *)
(* block are at most 255 numbers below 256.                                  *)
(* ------------------------------------------------------------------------- *)

let FSE_WEIGHTS_DET = prove
 (`!cs alog (st:byte list) x w w'.
        fse_weights cs alog st x w /\ fse_weights cs alog st x w' ==> w' = w`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FSE_WEIGHTS_INDUCT THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_SIMP_TAC[FSE_WEIGHTS_STOP; FSE_WEIGHTS_STEP]);;

let FSE_WEIGHT_BLOCK_DET = prove
 (`!(blk:byte list) w w'.
        fse_weight_block T blk w /\ fse_weight_block T blk w' ==> w' = w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fse_weight_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `cs:int list` (X_CHOOSE_THEN `alog:num`
     (X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC))))
   (X_CHOOSE_THEN `cs':int list` (X_CHOOSE_THEN `alog':num`
     (X_CHOOSE_THEN `m':num` (X_CHOOSE_THEN `r':num` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`T`; `6`; `6`; `256`; `blk:byte list`; `cs:int list`;
                `alog:num`; `m:num`; `cs':int list`; `alog':num`; `m':num`]
    FSE_NCOUNT_DET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `r':num = r` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[ZSTD_END_UNIQUE]; ASM_MESON_TAC[FSE_WEIGHTS_DET]]);;

let HUF_HEADER_DET = prove
 (`!(l:byte list) w h w' h'.
        huf_header T l w h /\ huf_header T l w' h' ==> w' = w /\ h' = h`,
  REWRITE_TAC[huf_header] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let c = concl th in is_eq c && is_var(lhs c)))) THEN
  REWRITE_TAC[] THEN TRY ASM_ARITH_TAC THEN
  ASM_MESON_TAC[FSE_WEIGHT_BLOCK_DET]);;

let FSE_WEIGHTS_BOUNDS = prove
 (`!cs alog (st:byte list) s s' q ws w.
        5 <= alog /\ fse_valid cs alog /\
        s < 2 EXP alog /\ s' < 2 EXP alog /\
        fse_weights cs alog st (s,s',q,ws) w
        ==> LENGTH w <= 255 /\
            (ALL (\x. x < LENGTH cs) ws ==> ALL (\x. x < LENGTH cs) w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `!x w. fse_weights cs alog (st:byte list) x w
          ==> FST x < 2 EXP alog /\ FST(SND x) < 2 EXP alog
              ==> LENGTH w <= 255 /\
                  (ALL (\x. x < LENGTH cs) (SND(SND(SND x)))
                   ==> ALL (\x. x < LENGTH cs) w)`
   (fun th -> STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP th) THEN
              ASM_REWRITE_TAC[FST; SND]) THEN
  MATCH_MP_TAC FSE_WEIGHTS_INDUCT THEN REWRITE_TAC[FST; SND] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FSE_SYMBOL_RANGE];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun ih -> STRIP_TAC THEN MP_TAC ih) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`cs:int list`; `alog:num`; `s:num`] FSE_NBITS_BASE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`st:byte list`; `q:num`; `fse_nbits cs alog s`]
        ZSTD_BACK_BOUND) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ALL_APPEND; ALL; FSE_SYMBOL_RANGE]]);;

let FSE_WEIGHT_BLOCK_BOUNDS = prove
 (`!(blk:byte list) w.
        fse_weight_block T blk w ==> LENGTH w <= 255 /\ ALL (\x. x < 256) w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fse_weight_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:int list` (X_CHOOSE_THEN `alog:num`
     (X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FSE_NCOUNT_BOUNDS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FSE_NCOUNT_VALID) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    FSE_WEIGHTS_BOUNDS)) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND; ALL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\x. x < LENGTH(cs:int list)) w` THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The sum of 2^(Weight - 1) over the weights, huf_total, as zstd computes   *)
(* it, adding 2^Weight DIV 2 one weight at a time, and the number of the     *)
(* weights j, huf_rank ws j. The weights 1 make the sum even or odd.         *)
(* ------------------------------------------------------------------------- *)

let HUF_EXP_DIV2 = prove
 (`!x. 2 EXP x DIV 2 = if x = 0 then 0 else 2 EXP (x - 1)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; NOT_SUC; SUC_SUB1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let HUF_TOTAL_ALT = prove
 (`!ws. huf_total ws = nsum {i | i < LENGTH ws} (\i. 2 EXP (EL i ws) DIV 2)`,
  GEN_TAC THEN REWRITE_TAC[huf_total; huf_present] THEN
  SUBGOAL_THEN
   `{t | t < LENGTH ws /\ ~(EL t ws = 0)} =
    {t | t IN {t | t < LENGTH ws} /\ ~(EL t ws = 0)}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NSUM_RESTRICT_SET] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; HUF_EXP_DIV2; COND_SWAP]);;

let HUF_TOTAL_SPEC = prove
 (`!ws. nsum {i | i < LENGTH ws /\ ~(EL i ws = 0)} (\i. 2 EXP (EL i ws - 1)) =
        huf_total ws`,
  REWRITE_TAC[huf_total; huf_present]);;

let HUF_TOTAL_NIL = prove
 (`huf_total [] = 0`,
  REWRITE_TAC[HUF_TOTAL_ALT; LENGTH; NSUM_CLAUSES_NUMSEG_LT]);;

let HUF_TOTAL_APPEND1 = prove
 (`!ws x. huf_total (APPEND ws [x]) = huf_total ws + 2 EXP x DIV 2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HUF_TOTAL_ALT; LENGTH_APPEND; LENGTH; ADD_CLAUSES;
              NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  SIMP_TAC[IN_ELIM_THM]);;

let HUF_TOTAL_EL = prove
 (`!ws i. i < LENGTH ws ==> 2 EXP (EL i ws) DIV 2 <= huf_total ws`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HUF_TOTAL_ALT] THEN
  MP_TAC(ISPECL [`\i. 2 EXP (EL i ws) DIV 2`; `{i | i < LENGTH(ws:num list)}`;
                 `i:num`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ARITH_TAC);;

let HUF_TOTAL_BOUND = prove
 (`!w. ALL (\x. x <= 12) w ==> huf_total w <= 2048 * LENGTH w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HUF_TOTAL_ALT] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_LT] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC NSUM_BOUND THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[GSYM ALL_EL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRANS_TAC LE_TRANS `2 EXP 12 DIV 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV]);;

let huf_rank = new_definition
 `huf_rank (ws:num list) j =
    nsum {i | i < LENGTH ws} (\i. if EL i ws = j then 1 else 0)`;;

let HUF_RANK_NIL = prove
 (`!j. huf_rank [] j = 0`,
  REWRITE_TAC[huf_rank; LENGTH; NSUM_CLAUSES_NUMSEG_LT]);;

let HUF_RANK_APPEND1 = prove
 (`!ws x j. huf_rank (APPEND ws [x]) j =
            huf_rank ws j + (if x = j then 1 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[huf_rank; LENGTH_APPEND; LENGTH; ADD_CLAUSES;
              NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  SIMP_TAC[IN_ELIM_THM]);;

let HUF_RANK_LE = prove
 (`!ws j. huf_rank ws j <= LENGTH ws`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_rank] THEN
  MP_TAC(ISPECL [`{i | i < LENGTH(ws:num list)}`;
                 `\i. if EL i ws = (j:num) then 1 else 0`; `1`]
    NSUM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; MULT_CLAUSES] THEN
  ANTS_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC; REWRITE_TAC[]]);;

let HUF_RANK_MEM = prove
 (`!ws j. ~(huf_rank ws j = 0) <=> MEM j ws`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[huf_rank; NSUM_EQ_0_IFF; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REWRITE_TAC[MEM_EXISTS_EL; ARITH_RULE `(if p then 1 else 0) = 0 <=> ~p`] THEN
  MESON_TAC[]);;

let HUF_TOTAL_PARITY = prove
 (`!ws. EVEN(huf_total ws) <=> EVEN(huf_rank ws 1)`,
  GEN_TAC THEN REWRITE_TAC[HUF_TOTAL_ALT; huf_rank] THEN
  SPEC_TAC(`LENGTH(ws:num list)`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EVEN_ADD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[HUF_EXP_DIV2] THEN
  ASM_CASES_TAC `EL n (ws:num list) = 0` THEN ASM_REWRITE_TAC[EVEN] THEN
  ASM_CASES_TAC `EL n (ws:num list) = 1` THEN ASM_REWRITE_TAC[EVEN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EVEN_EXP; ARITH_EVEN] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The weights as zstd's HUF_readStats checks them, huf_readstats w ws ml,   *)
(* for the weights w of a description, ws being them with the last one and   *)
(* ml Max_Number_of_Bits: every weight at most 12 (which the bound on ml     *)
(* implies), the sum nonzero with at most 12 bits, the rest to 2^ml a power  *)
(* of 2, and at least 2 weights 1, an even number of them (which follows     *)
(* from the sum of ws being 2^ml). For a description of h bytes with the     *)
(* weights w, these are the weights of huf_weights T.                        *)
(* ------------------------------------------------------------------------- *)

let huf_readstats = new_definition
 `huf_readstats w ws ml <=>
    ALL (\x. x <= 12) w /\ ~(huf_total w = 0) /\
    ml = bitsize(huf_total w) /\ ml <= 12 /\
    2 EXP (bitsize(2 EXP ml - huf_total w) - 1) = 2 EXP ml - huf_total w /\
    ws = APPEND w [bitsize(2 EXP ml - huf_total w)] /\
    2 <= huf_rank ws 1 /\ EVEN(huf_rank ws 1)`;;

let HUF_READSTATS_NONE = prove
 (`!w. (!ws ml. ~huf_readstats w ws ml) <=>
       ~(ALL (\x. x <= 12) w /\ ~(huf_total w = 0) /\
         bitsize(huf_total w) <= 12 /\
         2 EXP (bitsize(2 EXP bitsize(huf_total w) - huf_total w) - 1) =
         2 EXP bitsize(huf_total w) - huf_total w /\
         2 <= huf_rank (APPEND w [bitsize(2 EXP bitsize(huf_total w) -
                                          huf_total w)]) 1 /\
         EVEN(huf_rank (APPEND w [bitsize(2 EXP bitsize(huf_total w) -
                                          huf_total w)]) 1))`,
  GEN_TAC THEN REWRITE_TAC[huf_readstats] THEN MESON_TAC[]);;

let HUF_READSTATS_SOME = prove
 (`!w ws ml.
        huf_readstats w ws ml <=>
        ALL (\x. x <= 12) w /\ ~(huf_total w = 0) /\
        bitsize(huf_total w) <= 12 /\
        2 EXP (bitsize(2 EXP bitsize(huf_total w) - huf_total w) - 1) =
        2 EXP bitsize(huf_total w) - huf_total w /\
        2 <= huf_rank (APPEND w [bitsize(2 EXP bitsize(huf_total w) -
                                         huf_total w)]) 1 /\
        EVEN(huf_rank (APPEND w [bitsize(2 EXP bitsize(huf_total w) -
                                         huf_total w)]) 1) /\
        ml = bitsize(huf_total w) /\
        ws = APPEND w [bitsize(2 EXP bitsize(huf_total w) - huf_total w)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_readstats] THEN MESON_TAC[]);;

let HUF_WEIGHTS_READSTATS = prove
 (`!(l:byte list) w h.
        huf_header T l w h
        ==> !ws ml h'. huf_weights T l ws ml h' <=>
                       h' = h /\ huf_readstats w ws ml`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_weights; huf_readstats] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[HUF_TOTAL_SPEC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w':num list` (X_CHOOSE_THEN `k:num`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`l:byte list`; `w:num list`; `h:num`; `w':num list`;
                  `h':num`] HUF_HEADER_DET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `ws:num list`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `ml:num`)) THEN
    MP_TAC(SPEC `huf_total w` BITSIZE) THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[BITSIZE_POW2; ADD_SUB] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM ALL_EL] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`w:num list`; `i:num`] HUF_TOTAL_EL) THEN
      ASM_REWRITE_TAC[HUF_EXP_DIV2] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `2 EXP 12 <= 2 EXP (EL i w - 1) /\
                    2 EXP bitsize(huf_total w) <= 2 EXP 12`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `EVEN(huf_rank (APPEND w [k + 1]) 1)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM HUF_TOTAL_PARITY; HUF_TOTAL_APPEND1; HUF_EXP_DIV2;
                  ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
      SUBGOAL_THEN `huf_total w + 2 EXP k = 2 EXP bitsize(huf_total w)`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[EVEN_EXP; ARITH_EVEN; BITSIZE_EQ_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`APPEND w [k + 1]`; `1`] HUF_RANK_MEM) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `EVEN(huf_rank (APPEND w [k + 1]) 1)` THEN
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN ARITH_TAC;
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `ws:num list`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `ml:num`)) THEN
    MAP_EVERY EXISTS_TAC
     [`w:num list`;
      `bitsize(2 EXP bitsize(huf_total w) - huf_total w) - 1`] THEN
    SUBGOAL_THEN `~(2 EXP bitsize(huf_total w) - huf_total w = 0)`
    ASSUME_TAC THENL
     [MP_TAC(SPEC `huf_total w` BITSIZE) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[BITSIZE_EQ_0;
                    ARITH_RULE `~(b = 0) ==> b - 1 + 1 = b`];
      REWRITE_TAC[GSYM HUF_RANK_MEM] THEN ASM_ARITH_TAC]]);;

let HUF_WEIGHTS_NOHEADER = prove
 (`!(l:byte list).
        (!w h. ~huf_header T l w h) ==> !ws ml h. ~huf_weights T l ws ml h`,
  REWRITE_TAC[huf_weights] THEN MESON_TAC[]);;

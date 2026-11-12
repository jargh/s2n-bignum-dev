(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Properties of the DEFLATE specification: canonical Huffman codes are      *)
(* prefix-free, so a symbol is decoded in at most one way, and so decoding   *)
(* is deterministic.                                                         *)
(* ========================================================================= *)

needs "common/rfc1951.ml";;

(* ------------------------------------------------------------------------- *)
(* Reading numbers from the bit stream.                                      *)
(* ------------------------------------------------------------------------- *)

let DEFLATE_BITS_BOUND = prove
 (`!l p n. deflate_bits l p n < 2 EXP n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[deflate_bits; EXP; ARITH] THEN GEN_TAC THEN
  MP_TAC(SPEC `deflate_bit l p` BITVAL_BOUND) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p + 1`) THEN ARITH_TAC);;

let DEFLATE_CODEBITS_BOUND = prove
 (`!l p n. deflate_codebits l p n < 2 EXP n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[deflate_codebits; EXP; ARITH] THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p + 1`) THEN
  BOOL_CASES_TAC `deflate_bit l p` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  ARITH_TAC);;

let DEFLATE_CODEBITS_ADD = prove
 (`!l p m n.
        deflate_codebits l p (m + n) =
        2 EXP n * deflate_codebits l p m + deflate_codebits l (p + m) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[deflate_codebits; ADD_CLAUSES; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `SUC(p + m) = (p + 1) + m`] THEN ARITH_TAC);;

let DEFLATE_CODEBITS_1 = prove
 (`!l q. deflate_codebits l q 1 = deflate_bits l q 1`,
  REWRITE_TAC[num_CONV `1`; deflate_codebits; deflate_bits] THEN ARITH_TAC);;

let DEFLATE_CODEBITS_SCALED = prove
 (`!l p m d e.
        deflate_codebits l p (m + d) * 2 EXP e <
        (deflate_codebits l p m + 1) * 2 EXP (d + e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DEFLATE_CODEBITS_ADD; EXP_ADD] THEN
  SUBGOAL_THEN
   `deflate_codebits l (p + m) d * 2 EXP e < 2 EXP d * 2 EXP e`
  MP_TAC THENL
   [REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ; DEFLATE_CODEBITS_BOUND];
    ARITH_TAC]);;

let DEFLATE_BITS_ADD = prove
 (`!l p m n.
        deflate_bits l p (m + n) =
        deflate_bits l p m + 2 EXP m * deflate_bits l (p + m) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[deflate_bits; ADD_CLAUSES; MULT_CLAUSES; EXP] THEN
  REWRITE_TAC[ARITH_RULE `SUC(p + m) = (p + 1) + m`] THEN ARITH_TAC);;

let DIVMOD_ADD_MULT = prove
 (`!a b n. a < n ==> (a + n * b) DIV n = b /\ (a + n * b) MOD n = a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_ARITH_TAC);;

let DEFLATE_BITS_SPLIT = prove
 (`!l p n k.
        k <= n
        ==> deflate_bits l p n MOD 2 EXP k = deflate_bits l p k /\
            deflate_bits l p n DIV 2 EXP k = deflate_bits l (p + k) (n - k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[ADD_SUB2; DEFLATE_BITS_ADD] THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `k:num`] DEFLATE_BITS_BOUND) THEN
  SIMP_TAC[DIVMOD_ADD_MULT]);;

let DIVMOD_8_ADD = prove
 (`!i k. k < 8 ==> (8 * i + k) DIV 8 = i /\ (8 * i + k) MOD 8 = k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_ARITH_TAC);;

(* Unfold deflate_bits l p n for a numeral n.                                *)

let rec DEFLATE_BITS_UNFOLD_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("deflate_bits",_),_),_),k) when is_numeral k ->
      if dest_small_numeral k = 0 then REWR_CONV (CONJUNCT1 deflate_bits) tm
      else (RAND_CONV num_CONV THENC REWR_CONV (CONJUNCT2 deflate_bits) THENC
            RAND_CONV(RAND_CONV DEFLATE_BITS_UNFOLD_CONV)) tm
  | _ -> failwith "DEFLATE_BITS_UNFOLD_CONV";;

let DEFLATE_BITS_BYTE = prove
 (`!l i. deflate_bits l (8 * i) 8 = val(EL i l:byte)`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV DEFLATE_BITS_UNFOLD_CONV) THEN
  REWRITE_TAC[deflate_bit; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SIMP_TAC[DIVMOD_8_ADD; ARITH;
           REWRITE_RULE[ADD_CLAUSES] (SPECL [`i:num`; `0`] DIVMOD_8_ADD)] THEN
  SPEC_TAC(`EL i l:byte`,`b:byte`) THEN
  REWRITE_TAC[val_def; DIMINDEX_8; NUMSEG_LT; ARITH] THEN GEN_TAC THEN
  CONV_TAC(RAND_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let DEFLATE_BITS_EXTEND = prove
 (`!l p n i. p + n = 8 * i
             ==> deflate_bits l p n + 2 EXP n * val(EL i l:byte) =
                 deflate_bits l p (n + 8)`,
  SIMP_TAC[DEFLATE_BITS_ADD; DEFLATE_BITS_BYTE]);;

(* ------------------------------------------------------------------------- *)
(* Canonical codes. Codes are assigned in the order below, and scaled by     *)
(* 2^(15 - length), the code of s is the sum of 2^(15 - length) over the     *)
(* symbols before s. So, seen as intervals of 15-bit numbers, the codes      *)
(* follow each other in that order without overlapping, and no code is a     *)
(* prefix of another when the code lengths are at most 15.                   *)
(* ------------------------------------------------------------------------- *)

let FINITE_RESTRICT_LT = prove
 (`!n P. FINITE {t:num | t < n /\ P t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:num | t < n}` THEN
  SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM]);;

let CARD_RESTRICT_LT_ADD1 = prove
 (`!P i. CARD {t | t < i + 1 /\ P t} =
         CARD {t | t < i /\ P t} + (if P i then 1 else 0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{t | t < i + 1 /\ P t} =
    if P i then i INSERT {t | t < i /\ P t} else {t | t < i /\ P t}`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `t < i + 1 <=> t < i \/ t = i`] THEN
    ASM_MESON_TAC[];
    COND_CASES_TAC THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RESTRICT_LT; IN_ELIM_THM; LT_REFL] THEN
    ARITH_TAC]);;

let CARD_RESTRICT_LT_LE = prove
 (`!P i. CARD {t | t < i /\ P t} <= i`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SET_TAC[]);;

let ALL_REPLICATE = prove
 (`!P n x:A. ALL P (REPLICATE n x) <=> n = 0 \/ P x`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; ALL; NOT_SUC] THEN
  MESON_TAC[]);;

let ALL_LAST = prove
 (`!P l:A list. ~(l = []) /\ ALL P l ==> P(LAST l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; ALL; LAST] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let huffman_before = new_definition
 `huffman_before (lens:num list) t s <=>
    ~(EL t lens = 0) /\
    (EL t lens < EL s lens \/ EL t lens = EL s lens /\ t < s)`;;

let HUFFMAN_BEFORE_IRREFL = prove
 (`!lens s. ~huffman_before lens s s`,
  REWRITE_TAC[huffman_before; LT_REFL]);;

let HUFFMAN_BEFORE_TRANS = prove
 (`!lens r s t.
        huffman_before lens r s /\ huffman_before lens s t
        ==> huffman_before lens r t`,
  REWRITE_TAC[huffman_before] THEN ARITH_TAC);;

let HUFFMAN_BEFORE_TOTAL = prove
 (`!lens s t.
        ~(EL s lens = 0) /\ ~(EL t lens = 0)
        ==> huffman_before lens s t \/ s = t \/ huffman_before lens t s`,
  REWRITE_TAC[huffman_before] THEN ARITH_TAC);;

let HUFFMAN_CODE_SCALED = prove
 (`!lens s.
        s < LENGTH lens /\ ~(EL s lens = 0) /\ EL s lens <= 15
        ==> huffman_code lens s * 2 EXP (15 - EL s lens) =
            nsum {t | t < LENGTH lens /\ huffman_before lens t s}
                 (\t. 2 EXP (15 - EL t lens))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huffman_code; huffman_before] THEN
  ABBREV_TAC `L = EL s (lens:num list)` THEN
  SUBGOAL_THEN
   `{t | t < LENGTH lens /\ ~(EL t lens = 0) /\
         (EL t lens < L \/ EL t lens = L /\ t < s)} =
    {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < L} UNION
    {t | t < s /\ EL t (lens:num list) = L}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `t:num` THEN
    ASM_CASES_TAC `EL t (lens:num list) = L` THEN ASM_REWRITE_TAC[LT_REFL] THEN
    ASM_MESON_TAC[LT_TRANS];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_RESTRICT_LT; DISJOINT; EXTENSION; IN_INTER;
                IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[LT_REFL];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM NSUM_RMUL] THEN BINOP_TAC THEN
  SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT_LT; GSYM NSUM_RMUL] THEN
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[IN_ELIM_THM; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HUFFMAN_SCALED_BEFORE = prove
 (`!lens s t.
        s < LENGTH lens /\ huffman_before lens s t
        ==> nsum {u | u < LENGTH lens /\ huffman_before lens u s}
                 (\u. 2 EXP (15 - EL u lens)) + 2 EXP (15 - EL s lens) <=
            nsum {u | u < LENGTH lens /\ huffman_before lens u t}
                 (\u. 2 EXP (15 - EL u lens))`,
  REPEAT STRIP_TAC THEN TRANS_TAC LE_TRANS
   `nsum (s INSERT {u | u < LENGTH lens /\ huffman_before lens u s})
         (\u. 2 EXP (15 - EL u lens))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[NSUM_CLAUSES; FINITE_RESTRICT_LT; IN_ELIM_THM;
             HUFFMAN_BEFORE_IRREFL] THEN ARITH_TAC;
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_RESTRICT_LT; SUBSET; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[HUFFMAN_BEFORE_TRANS; LT_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of Huffman decoding.                                           *)
(* ------------------------------------------------------------------------- *)

let HUFFMAN_DECODE_NOT_BEFORE = prove
 (`!l lens p s q t q'.
        ALL (\n. n <= 15) lens /\
        huffman_decode l lens p s q /\ huffman_decode l lens p t q'
        ==> ~huffman_before lens s t`,
  REWRITE_TAC[GSYM ALL_EL; huffman_decode] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`lens:num list`; `s:num`; `t:num`] HUFFMAN_SCALED_BEFORE) THEN
  ASM_SIMP_TAC[GSYM HUFFMAN_CODE_SCALED] THEN
  SUBGOAL_THEN `EL s lens <= EL t lens /\ EL t (lens:num list) <= 15`
  MP_TAC THENL
   [ASM_MESON_TAC[huffman_before; LT_IMP_LE; LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d:num` o REWRITE_RULE[LE_EXISTS])
   (X_CHOOSE_TAC `e:num` o REWRITE_RULE[LE_EXISTS])) THEN
  SUBGOAL_THEN `15 - EL s lens = d + e /\ 15 - EL t (lens:num list) = e`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `deflate_codebits l p (EL s lens) = huffman_code lens s` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `deflate_codebits l p (EL t lens) = huffman_code lens t` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBST1_TAC(ASSUME `EL t lens = EL s (lens:num list) + d`) THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `EL s (lens:num list)`;
                `d:num`; `e:num`] DEFLATE_CODEBITS_SCALED) THEN
  ARITH_TAC);;

let HUFFMAN_DECODE_UNIQUE = prove
 (`!l lens p s q s' q'.
        ALL (\n. n <= 15) lens /\
        huffman_decode l lens p s q /\ huffman_decode l lens p s' q'
        ==> s' = s /\ q' = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lens:num list`; `s:num`; `s':num`] HUFFMAN_BEFORE_TOTAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[huffman_decode]; ALL_TAC] THEN
  ASM_MESON_TAC[HUFFMAN_DECODE_NOT_BEFORE; huffman_decode]);;

(* Given two Huffman decodes at the same position with the same code among   *)
(* the assumptions, and the bound on the code lengths, equate the symbols    *)
(* and the end positions, substituting for variables, or close the goal if   *)
(* the symbols are different numerals.                                       *)

let HUFFMAN_UNIQUE_TAC:tactic =
  let all15 = `ALL (\n. n <= 15)` in
  let dest_decode tm =
    match strip_comb tm with
      Const("huffman_decode",_),[l;c;p;s;q] -> (l,c,p),(s,q)
    | _ -> failwith "dest_decode" in
  let subst th =
    let l,r = dest_eq(concl th) in
    if l = r then ALL_TAC
    else if is_var l then SUBST_ALL_TAC th
    else if is_var r then SUBST_ALL_TAC(SYM th)
    else if is_numeral l && is_numeral r then
      CONTR_TAC(EQ_MP (NUM_EQ_CONV(concl th)) th)
    else failwith "HUFFMAN_UNIQUE_TAC" in
  fun (asl,w as gl) ->
    let ths = map snd asl in
    let decs = mapfilter (fun th -> dest_decode(concl th),th) ths in
    let pick ((k1,v1),th1) ((k2,v2),th2) =
      if k1 = k2 && v1 <> v2 then
        let (_,c,_) = k1 in
        let b = find (fun th -> aconv (concl th) (mk_comb(all15,c))) ths in
        let th = MATCH_MP HUFFMAN_DECODE_UNIQUE (CONJ b (CONJ th1 th2)) in
        EVERY(map subst (CONJUNCTS th))
      else failwith "pick" in
    tryfind (fun d1 -> tryfind (pick d1) decs) decs gl;;

let SUBST_VARS_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)));;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of the decoding of block data.                                 *)
(* ------------------------------------------------------------------------- *)

let DEFLATE_LENDIST_UNIQUE = prove
 (`!l ll dl p len distance q len' distance' q'.
        ALL (\n. n <= 15) ll /\ ALL (\n. n <= 15) dl /\
        deflate_lendist l ll dl p len distance q /\
        deflate_lendist l ll dl p len' distance' q'
        ==> len' = len /\ distance' = distance /\ q' = q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[deflate_lendist] THEN STRIP_TAC THEN
  REPEAT HUFFMAN_UNIQUE_TAC THEN ASM_REWRITE_TAC[]);;

let DEFLATE_CODES_UNIQUE = prove
 (`!l ll dl x r r'.
        ALL (\n. n <= 15) ll /\ ALL (\n. n <= 15) dl /\
        deflate_codes l ll dl x r /\ deflate_codes l ll dl x r'
        ==> r' = r`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `deflate_codes l ll dl x r'` THEN
  SPEC_TAC(`r':byte list#num`,`r':byte list#num`) THEN
  UNDISCH_TAC `deflate_codes l ll dl x r` THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
   [`r:byte list#num`; `x:byte list#num`] THEN
  MATCH_MP_TAC DEFLATE_CODES_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[deflate_lendist] THEN
  STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[DEFLATE_CODES_CASES] THEN
  REWRITE_TAC[PAIR_EQ; deflate_lendist] THEN STRIP_TAC THEN
  SUBST_VARS_TAC THEN REPEAT HUFFMAN_UNIQUE_TAC THEN SUBST_VARS_TAC THEN
  FIRST [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

let DEFLATE_FIXED_BOUND = prove
 (`ALL (\n. n <= 15) deflate_fixed_ll /\ ALL (\n. n <= 15) deflate_fixed_dl`,
  REWRITE_TAC[deflate_fixed_dl; ALL_REPLICATE; ARITH] THEN
  REWRITE_TAC[deflate_fixed_ll; GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The code lengths of a dynamic block.                                      *)
(* ------------------------------------------------------------------------- *)

let DEFLATE_LENGTHS_UNIQUE = prove
 (`!l cl n x r r'.
        ALL (\n. n <= 15) cl /\
        deflate_lengths l cl n x r /\ deflate_lengths l cl n x r'
        ==> r' = r`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `deflate_lengths l cl n x r'` THEN
  SPEC_TAC(`r':num list#num`,`r':num list#num`) THEN
  UNDISCH_TAC `deflate_lengths l cl n x r` THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
   [`r:num list#num`; `x:num list#num`] THEN
  MATCH_MP_TAC DEFLATE_LENGTHS_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[DEFLATE_LENGTHS_CASES] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  SUBST_VARS_TAC THEN REPEAT HUFFMAN_UNIQUE_TAC THEN SUBST_VARS_TAC THEN
  FIRST [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

let DEFLATE_LENGTHS_LENGTH = prove
 (`!l cl n x r. deflate_lengths l cl n x r ==> LENGTH(FST r) = n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC DEFLATE_LENGTHS_INDUCT THEN SIMP_TAC[FST]);;

let DEFLATE_LENGTHS_BOUND = prove
 (`!l cl n x r.
        deflate_lengths l cl n x r
        ==> ALL (\k. k <= 15) (FST x) ==> ALL (\k. k <= 15) (FST r)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC DEFLATE_LENGTHS_INDUCT THEN
  REWRITE_TAC[FST; ALL_APPEND; ALL; ALL_REPLICATE; LE_0] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[BETA_RULE(ISPEC `\k. k <= 15` ALL_LAST)] THEN
  ASM_ARITH_TAC);;

(* Every code length code length is given, in the order of the RFC.          *)

let DEFLATE_CLEN_ORDER = prove
 (`!P. (!i. i < 19 ==> P(EL i deflate_clen_order)) <=> (!j. j < 19 ==> P j)`,
  GEN_TAC THEN CONV_TAC(BINOP_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[deflate_clen_order] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of the decoding of blocks, and of the whole input.             *)
(* ------------------------------------------------------------------------- *)

let DEFLATE_STORED_UNIQUE = prove
 (`!l out p r r'.
        deflate_stored l (out,p) r /\ deflate_stored l (out,p) r' ==> r' = r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[deflate_stored] THEN STRIP_TAC THEN
  SUBST_VARS_TAC THEN REFL_TAC);;

let DEFLATE_DYNAMIC_UNIQUE = prove
 (`!l out p r r'.
        deflate_dynamic l (out,p) r /\ deflate_dynamic l (out,p) r'
        ==> r' = r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[deflate_dynamic] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nlen':num = nlen /\ ndist':num = ndist /\ ncode':num = ncode`
  (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cl':num list = cl` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[LIST_EQ] THEN
    ONCE_REWRITE_TAC[GSYM DEFLATE_CLEN_ORDER] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\n. n <= 15) (cl:num list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM ALL_EL] THEN
    ONCE_REWRITE_TAC[GSYM DEFLATE_CLEN_ORDER] THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LE_0] THEN
    MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 3 ==> x <= 15`) THEN
    REWRITE_TAC[DEFLATE_BITS_BOUND];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:byte list`; `cl:num list`; `nlen + ndist:num`;
                 `[]:num list,p + 14 + 3 * ncode`; `lens:num list,q:num`;
                 `lens':num list,q':num`] DEFLATE_LENGTHS_UNIQUE) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DEFLATE_LENGTHS_LENGTH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DEFLATE_LENGTHS_BOUND) THEN
  REWRITE_TAC[FST; ALL] THEN REWRITE_TAC[GSYM ALL_EL] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC DEFLATE_CODES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`l:byte list`; `list_of_seq (\i. EL i (lens:num list)) nlen`;
    `list_of_seq (\i. EL (nlen + i) (lens:num list)) ndist`;
    `out:byte list,q:num`] THEN
  ASM_REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let DEFLATE_BLOCK_UNIQUE = prove
 (`!l btype out p r r'.
        deflate_block l btype (out,p) r /\ deflate_block l btype (out,p) r'
        ==> r' = r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[deflate_block] THEN
  ASM_CASES_TAC `btype = 0` THEN ASM_REWRITE_TAC[ARITH_EQ] THENL
   [MESON_TAC[DEFLATE_STORED_UNIQUE]; ALL_TAC] THEN
  ASM_CASES_TAC `btype = 1` THEN ASM_REWRITE_TAC[ARITH_EQ] THENL
   [MESON_TAC[DEFLATE_CODES_UNIQUE; DEFLATE_FIXED_BOUND]; ALL_TAC] THEN
  MESON_TAC[DEFLATE_DYNAMIC_UNIQUE]);;

let DEFLATE_BLOCKS_UNIQUE = prove
 (`!l x r r'. deflate_blocks l x r /\ deflate_blocks l x r' ==> r' = r`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC DEFLATE_BLOCKS_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[DEFLATE_BLOCKS_CASES] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN SUBST_VARS_TAC THEN ASM_MESON_TAC[DEFLATE_BLOCK_UNIQUE]);;

(* Decoding is deterministic: a compressed data set has at most one          *)
(* decoding, which uses a definite number of bytes.                          *)

let DEFLATE_DECODE_UNIQUE = prove
 (`!l out n out' n'.
        deflate_decode l out n /\ deflate_decode l out' n'
        ==> out' = out /\ n' = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[deflate_decode] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `[]:byte list,0`; `out:byte list,q:num`;
                 `out':byte list,q':num`] DEFLATE_BLOCKS_UNIQUE) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The codes are those of the algorithm in section 3.2.2 of the RFC, which   *)
(* counts the codes of each length (bl_count) and computes the first code of *)
(* each length (next_code) by a recurrence. A table-driven decoder also uses *)
(* the number of codes shorter than each length (huffman_index) and lists    *)
(* the symbols in the order of their codes, with s at position               *)
(* huffman_rank lens s. A code c of length n > 0 is the code of a symbol if  *)
(* and only if huffman_first lens n <= c < huffman_first lens n +            *)
(* huffman_count lens n, and that symbol is at position                      *)
(* huffman_index lens n + (c - huffman_first lens n) in the list.            *)
(* ------------------------------------------------------------------------- *)

let huffman_count = new_definition
 `huffman_count (lens:num list) n =
    CARD {s | s < LENGTH lens /\ EL s lens = n}`;;

let huffman_first = new_definition
 `huffman_first (lens:num list) n =
    nsum {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < n}
         (\t. 2 EXP (n - EL t lens))`;;

let huffman_index = new_definition
 `huffman_index (lens:num list) n =
    CARD {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < n}`;;

let huffman_rank = new_definition
 `huffman_rank (lens:num list) s =
    CARD {t | t < LENGTH lens /\ huffman_before lens t s}`;;

let HUFFMAN_CODE_FIRST = prove
 (`!lens s. huffman_code lens s =
            huffman_first lens (EL s lens) +
            CARD {t | t < s /\ EL t lens = EL s lens}`,
  REWRITE_TAC[huffman_code; huffman_first]);;

let HUFFMAN_FIRST_CLAUSES = prove
 (`!lens. huffman_first lens 0 = 0 /\ huffman_first lens 1 = 0 /\
          !n. ~(n = 0)
              ==> huffman_first lens (n + 1) =
                  2 * (huffman_first lens n + huffman_count lens n)`,
  GEN_TAC THEN REWRITE_TAC[huffman_first; huffman_count] THEN
  REWRITE_TAC[LT; ARITH_RULE `x < 1 <=> x = 0`;
              TAUT `~p /\ p <=> F`; EMPTY_GSPEC; NSUM_CLAUSES] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < n + 1} =
    {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < n} UNION
    {t | t < LENGTH lens /\ EL t (lens:num list) = n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_RESTRICT_LT; DISJOINT; EXTENSION; IN_INTER;
                IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM NSUM_LMUL] THEN BINOP_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT_LT; GSYM NSUM_LMUL] THEN
    MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) - n = 1`] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let HUFFMAN_INDEX_CLAUSES = prove
 (`!lens. huffman_index lens 0 = 0 /\ huffman_index lens 1 = 0 /\
          !n. ~(n = 0)
              ==> huffman_index lens (n + 1) =
                  huffman_index lens n + huffman_count lens n`,
  GEN_TAC THEN REWRITE_TAC[huffman_index; huffman_count] THEN
  REWRITE_TAC[LT; ARITH_RULE `x < 1 <=> x = 0`;
              TAUT `~p /\ p <=> F`; EMPTY_GSPEC; CARD_CLAUSES] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < n + 1} =
    {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < n} UNION
    {t | t < LENGTH lens /\ EL t (lens:num list) = n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CARD_UNION THEN
    REWRITE_TAC[FINITE_RESTRICT_LT; EXTENSION; IN_INTER;
                IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC]);;

let HUFFMAN_RANK = prove
 (`!lens s.
        s < LENGTH lens /\ ~(EL s lens = 0)
        ==> huffman_rank lens s =
            huffman_index lens (EL s lens) +
            CARD {t | t < s /\ EL t lens = EL s lens}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[huffman_rank; huffman_index; huffman_before] THEN
  ABBREV_TAC `L = EL s (lens:num list)` THEN
  SUBGOAL_THEN
   `{t | t < LENGTH lens /\ ~(EL t lens = 0) /\
         (EL t lens < L \/ EL t lens = L /\ t < s)} =
    {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < L} UNION
    {t | t < s /\ EL t (lens:num list) = L}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `t:num` THEN
    ASM_CASES_TAC `EL t (lens:num list) = L` THEN ASM_REWRITE_TAC[LT_REFL] THEN
    ASM_MESON_TAC[LT_TRANS];
    MATCH_MP_TAC CARD_UNION THEN
    REWRITE_TAC[FINITE_RESTRICT_LT; EXTENSION; IN_INTER;
                IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[LT_REFL]]);;

let HUFFMAN_COUNT_RANK = prove
 (`!lens s.
        s < LENGTH lens
        ==> CARD {t | t < s /\ EL t lens = EL s lens} <
            huffman_count lens (EL s lens)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huffman_count] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN
  REWRITE_TAC[FINITE_RESTRICT_LT; PSUBSET; SUBSET; EXTENSION; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[LT_TRANS];
    DISCH_THEN(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[LT_REFL]]);;

let HUFFMAN_RANK_LT_LENGTH = prove
 (`!lens t. t < LENGTH lens ==> huffman_rank lens t < LENGTH lens`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huffman_rank] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[PSUBSET; SUBSET; EXTENSION; IN_ELIM_THM] THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:num`) THEN
  ASM_REWRITE_TAC[HUFFMAN_BEFORE_IRREFL]);;

let HUFFMAN_RANK_MONO = prove
 (`!lens t u.
        t < LENGTH lens /\ huffman_before lens t u
        ==> huffman_rank lens t < huffman_rank lens u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huffman_rank] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_RESTRICT_LT] THEN
  REWRITE_TAC[PSUBSET; SUBSET; EXTENSION; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HUFFMAN_BEFORE_TRANS]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:num`) THEN
  ASM_REWRITE_TAC[HUFFMAN_BEFORE_IRREFL]);;

let HUFFMAN_RANK_INJ = prove
 (`!lens t u.
        t < LENGTH lens /\ u < LENGTH lens /\
        ~(EL t lens = 0) /\ ~(EL u lens = 0) /\
        huffman_rank lens t = huffman_rank lens u
        ==> t = u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`lens:num list`; `t:num`; `u:num`] HUFFMAN_BEFORE_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`lens:num list`; `t:num`; `u:num`] HUFFMAN_RANK_MONO);
    MP_TAC(SPECL [`lens:num list`; `u:num`; `t:num`] HUFFMAN_RANK_MONO)] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let CARD_RANK_EXISTS = prove
 (`!P n j. j < CARD {t | t < n /\ P t}
           ==> ?t. t < n /\ P t /\ CARD {u | u < t /\ P u} = j`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES]; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN
  SUBGOAL_THEN
   `{t | t < SUC n /\ P t} =
    if P n then n INSERT {t | t < n /\ P t} else {t | t < n /\ P t}`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RESTRICT_LT; IN_ELIM_THM; LT_REFL] THEN
  REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let HUFFMAN_CODE_RANGE = prove
 (`!lens s.
        s < LENGTH lens
        ==> huffman_first lens (EL s lens) <= huffman_code lens s /\
            huffman_code lens s <
            huffman_first lens (EL s lens) + huffman_count lens (EL s lens)`,
  SIMP_TAC[HUFFMAN_CODE_FIRST; LE_ADD; LT_ADD_LCANCEL; HUFFMAN_COUNT_RANK]);;

let HUFFMAN_CODE_EXISTS = prove
 (`!lens n c.
        ~(n = 0) /\ huffman_first lens n <= c /\
        c < huffman_first lens n + huffman_count lens n
        ==> ?s. s < LENGTH lens /\ EL s lens = n /\
                huffman_code lens s = c /\
                huffman_rank lens s =
                huffman_index lens n + (c - huffman_first lens n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\t. EL t (lens:num list) = n`; `LENGTH(lens:num list)`;
    `c - huffman_first lens n`] CARD_RANK_EXISTS)) THEN
  REWRITE_TAC[GSYM huffman_count] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[HUFFMAN_CODE_FIRST; HUFFMAN_RANK] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Decoding with the tables, trying the lengths n = 1, 2, ... in turn: the   *)
(* code is found at length n if the first n bits are in the range of the     *)
(* codes of length n, and there is no code if none of the lengths up to 15   *)
(* has its code in range, or if the input runs out first. The bounds that    *)
(* the Kraft inequality gives for the tables.                                *)
(* ------------------------------------------------------------------------- *)

let HUFFMAN_DECODE_NOT_FOUND = prove
 (`!l lens p n.
        ALL (\x. x <= 15) lens /\
        (!m. 0 < m /\ m < n /\ p + m <= 8 * LENGTH l
             ==> huffman_first lens m + huffman_count lens m <=
                 deflate_codebits l p m) /\
        (16 <= n \/ 8 * LENGTH l < p + n)
        ==> ~(?s q. huffman_decode l lens p s q)`,
  REWRITE_TAC[GSYM ALL_EL; huffman_decode; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`l:byte list`; `lens:num list`; `p:num`; `n:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "m") ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`s:num`; `q:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lens:num list`; `s:num`] HUFFMAN_CODE_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EL s (lens:num list) <= 15` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "m" (MP_TAC o SPEC `EL s (lens:num list)`) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let HUFFMAN_DECODE_FOUND = prove
 (`!l lens p n.
        ~(n = 0) /\ p + n <= 8 * LENGTH l /\
        huffman_first lens n <= deflate_codebits l p n /\
        deflate_codebits l p n < huffman_first lens n + huffman_count lens n
        ==> ?s. huffman_decode l lens p s (p + n) /\
                huffman_rank lens s =
                huffman_index lens n +
                (deflate_codebits l p n - huffman_first lens n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`lens:num list`; `n:num`; `deflate_codebits l p n`]
               HUFFMAN_CODE_EXISTS) THEN
  ASM_REWRITE_TAC[huffman_decode] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let HUFFMAN_FIRST_COUNT = prove
 (`!lens n.
        ~(n = 0)
        ==> huffman_first lens n + huffman_count lens n =
            nsum {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens <= n}
                 (\t. 2 EXP (n - EL t lens))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huffman_first; huffman_count] THEN
  SUBGOAL_THEN
   `{t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens <= n} =
    {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens < n} UNION
    {t | t < LENGTH lens /\ EL t (lens:num list) = n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_RESTRICT_LT; DISJOINT; EXTENSION; IN_INTER;
                IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT_LT] THEN
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[IN_ELIM_THM; SUB_REFL; EXP]);;

let HUFFMAN_FIRST_COUNT_BOUND = prove
 (`!lens n.
        huffman_kraft lens <= 2 EXP 15 /\ ~(n = 0) /\ n <= 15
        ==> huffman_first lens n + huffman_count lens n <= 2 EXP n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HUFFMAN_FIRST_COUNT] THEN
  W(fun (asl,w) ->
    let tm = lhand w in
    SUBGOAL_THEN (mk_binop `(<=):num->num->bool`
                   (mk_binop `( * ):num->num->num` `2 EXP (15 - n)` tm)
                   `2 EXP (15 - n) * 2 EXP n`) MP_TAC) THENL
   [ALL_TAC; REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]] THEN
  REWRITE_TAC[GSYM EXP_ADD; GSYM NSUM_LMUL] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 15 ==> 15 - n + n = 15`] THEN
  TRANS_TAC LE_TRANS `huffman_kraft lens` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[huffman_kraft] THEN
  TRANS_TAC LE_TRANS
   `nsum {t | t < LENGTH lens /\ ~(EL t lens = 0) /\ EL t lens <= n}
         (\s. 2 EXP (15 - EL s (lens:num list)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC NSUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM EXP_ADD] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_RESTRICT_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let HUFFMAN_FIRST_COUNT_OVER = prove
 (`!lens n.
        ~(n = 0) /\ n <= 15 /\
        2 EXP n < huffman_first lens n + huffman_count lens n
        ==> 2 EXP 15 < huffman_kraft lens`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`lens:num list`; `n:num`] HUFFMAN_FIRST_COUNT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let HUFFMAN_COUNT_LE_LENGTH = prove
 (`!lens n. huffman_count lens n <= LENGTH lens`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huffman_count] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SET_TAC[]);;

let HUFFMAN_INDEX_LE_LENGTH = prove
 (`!lens n. huffman_index lens n <= LENGTH lens`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huffman_index] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Kraft sum and the conditions on code lengths in terms of the counts.  *)
(* ------------------------------------------------------------------------- *)

let HUFFMAN_COUNT_SUM = prove
 (`!lens. ALL (\n. n <= 15) lens
          ==> nsum (0..15) (huffman_count lens) = LENGTH lens`,
  GEN_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s. EL s (lens:num list)`; `\s:num. 1`;
                 `{s:num | s < LENGTH(lens:num list)}`; `0..15`]
                NSUM_GROUP) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
               IN_NUMSEG; LE_0] THEN
  SIMP_TAC[NSUM_CONST; FINITE_NUMSEG_LT; FINITE_RESTRICT_LT;
           CARD_NUMSEG_LT; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[huffman_count]);;

let HUFFMAN_KRAFT_COUNT = prove
 (`!lens. ALL (\n. n <= 15) lens
          ==> huffman_kraft lens =
              nsum (1..15) (\n. huffman_count lens n * 2 EXP (15 - n))`,
  GEN_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN DISCH_TAC THEN
  REWRITE_TAC[huffman_kraft] THEN
  MP_TAC(ISPECL
   [`\s. EL s (lens:num list)`; `\s. 2 EXP (15 - EL s (lens:num list))`;
    `{s:num | s < LENGTH(lens:num list) /\ ~(EL s lens = 0)}`; `1..15`]
   NSUM_GROUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_RESTRICT_LT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                IN_NUMSEG] THEN
    ASM_MESON_TAC[ARITH_RULE `~(n = 0) ==> 1 <= n`];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN BETA_TAC THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN {s | s < LENGTH lens /\ ~(EL s lens = 0)} /\ EL x lens = n} =
    {s | s < LENGTH lens /\ EL s (lens:num list) = n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `nsum {s | s < LENGTH lens /\ EL s (lens:num list) = n}
         (\s. 2 EXP (15 - n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
    SIMP_TAC[NSUM_CONST; FINITE_RESTRICT_LT; huffman_count]]);;

let HUFFMAN_KRAFT_FIRST_COUNT = prove
 (`!lens. ALL (\x. x <= 15) lens
          ==> huffman_first lens 15 + huffman_count lens 15 =
              huffman_kraft lens`,
  GEN_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN DISCH_TAC THEN
  SIMP_TAC[HUFFMAN_FIRST_COUNT; ARITH_EQ; huffman_kraft] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let HUFFMAN_KRAFT_ALL_ZERO = prove
 (`!lens. ALL (\x. x = 0) lens ==> huffman_kraft lens = 0`,
  GEN_TAC THEN REWRITE_TAC[GSYM ALL_EL; huffman_kraft] THEN DISCH_TAC THEN
  MATCH_MP_TAC NSUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let HUFFMAN_COUNT_ALL_ZERO = prove
 (`!lens. huffman_count lens 0 = LENGTH lens <=> ALL (\n. n = 0) lens`,
  GEN_TAC THEN REWRITE_TAC[huffman_count; GSYM ALL_EL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_LT] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`{s | s < LENGTH lens /\ EL s (lens:num list) = 0}`;
                   `{s:num | s < LENGTH(lens:num list)}`] CARD_SUBSET_EQ) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM; EXTENSION] THEN
    MESON_TAC[];
    DISCH_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

let HUFFMAN_COUNT_ALL_LE1 = prove
 (`!lens. ALL (\n. n <= 15) lens
          ==> (huffman_count lens 0 + huffman_count lens 1 = LENGTH lens <=>
               ALL (\n. n <= 1) lens)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP HUFFMAN_COUNT_SUM) THEN
  MP_TAC(ISPECL [`huffman_count lens`; `0`; `15`] NSUM_CLAUSES_LEFT) THEN
  MP_TAC(ISPECL [`huffman_count lens`; `1`; `15`] NSUM_CLAUSES_LEFT) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ARITH] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `a + b = a + b + c <=> c = 0`] THEN
  SIMP_TAC[NSUM_EQ_0_IFF; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[huffman_count] THEN
  SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT_LT] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  UNDISCH_TAC `ALL (\n. n <= 15) lens` THEN REWRITE_TAC[GSYM ALL_EL] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`EL i (lens:num list)`; `i:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `i:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ARITH_TAC]);;

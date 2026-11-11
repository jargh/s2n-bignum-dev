(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Checks of the RFC 1951 spec by evaluation: the fixed Huffman codes agree  *)
(* with the table in section 3.2.6 of the RFC, and are complete.             *)
(* ========================================================================= *)

needs "common/rfc1951.ml";;

let NSUM_RESTRICT_LT = prove
 (`!n P (g:num->num).
        ~(n = 0)
        ==> nsum {t | t < n /\ P t} g =
            nsum (0..n-1) (\t. if P t then g t else 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{t | t < n /\ P t} = {t | t IN 0..n-1 /\ P t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> (a /\ c <=> b /\ c)`) THEN ASM_ARITH_TAC;
    REWRITE_TAC[NSUM_RESTRICT_SET]]);;

let CARD_RESTRICT_LT = prove
 (`!n P. ~(n = 0)
         ==> CARD {t | t < n /\ P t} =
             nsum (0..n-1) (\t. if P t then 1 else 0)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT; FINITE_NUMSEG_LT;
           SET_RULE `{t | t < n /\ P t} = {t | t IN {t | t < n} /\ P t}`] THEN
  ASM_SIMP_TAC[NSUM_RESTRICT_LT; GSYM NSUM_RESTRICT_SET; SET_RULE
   `{t | t IN {t | t < n} /\ P t} = {t | t < n /\ P t}`]);;

let EL_REPLICATE_LT = prove
 (`!n (x:A) i. i < n ==> EL i (REPLICATE n x) = x`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT; REPLICATE] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC] THEN ASM_MESON_TAC[]);;

(* The fixed code lengths, element by element.                               *)

let LENGTH_DEFLATE_FIXED = prove
 (`LENGTH deflate_fixed_ll = 288 /\ LENGTH deflate_fixed_dl = 32`,
  REWRITE_TAC[deflate_fixed_ll; deflate_fixed_dl; LENGTH_LIST_OF_SEQ;
              LENGTH_REPLICATE]);;

let EL_DEFLATE_FIXED = prove
 (`(!t. t < 288
        ==> EL t deflate_fixed_ll =
            if t < 144 then 8 else if t < 256 then 9
            else if t < 280 then 7 else 8) /\
   (!t. t < 32 ==> EL t deflate_fixed_dl = 5)`,
  SIMP_TAC[deflate_fixed_ll; deflate_fixed_dl; EL_LIST_OF_SEQ;
           EL_REPLICATE_LT]);;

let EL_FIXED_CONV =
  let pth_ll,pth_dl = CONJ_PAIR EL_DEFLATE_FIXED in
  fun tm ->
    match tm with
      Comb(Comb(Const("EL",_),t),Const(c,_)) when is_numeral t ->
        let pth = if c = "deflate_fixed_ll" then pth_ll
                  else if c = "deflate_fixed_dl" then pth_dl
                  else failwith "EL_FIXED_CONV" in
        let th = SPEC t pth in
        let th' = MP th (EQT_ELIM(NUM_LT_CONV(lhand(concl th)))) in
        CONV_RULE (RAND_CONV NUM_REDUCE_CONV) th'
    | _ -> failwith "EL_FIXED_CONV";;

let FIXED_CONV =
  REWRITE_CONV[huffman_code; huffman_kraft; LENGTH_DEFLATE_FIXED;
               CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES] THENC
  SIMP_CONV[NSUM_RESTRICT_LT; CARD_RESTRICT_LT; ARITH_EQ] THENC
  NUM_REDUCE_CONV THENC
  DEPTH_CONV EXPAND_NSUM_CONV THENC
  DEPTH_CONV EL_FIXED_CONV THENC
  NUM_REDUCE_CONV;;

let FIXED_CHECK tm =
  time prove(tm,CONV_TAC(LAND_CONV FIXED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

(* The table in section 3.2.6, and completeness of both fixed codes.         *)

let FIXED_CODES_RFC = map FIXED_CHECK
 [`huffman_code deflate_fixed_ll 0 = 0b00110000`;
  `huffman_code deflate_fixed_ll 143 = 0b10111111`;
  `huffman_code deflate_fixed_ll 144 = 0b110010000`;
  `huffman_code deflate_fixed_ll 255 = 0b111111111`;
  `huffman_code deflate_fixed_ll 256 = 0b0000000`;
  `huffman_code deflate_fixed_ll 279 = 0b0010111`;
  `huffman_code deflate_fixed_ll 280 = 0b11000000`;
  `huffman_code deflate_fixed_ll 287 = 0b11000111`;
  `huffman_code deflate_fixed_dl 0 = 0`;
  `huffman_code deflate_fixed_dl 31 = 31`;
  `huffman_kraft deflate_fixed_ll = 2 EXP 15`;
  `huffman_kraft deflate_fixed_dl = 2 EXP 15`];;

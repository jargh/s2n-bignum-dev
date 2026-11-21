(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The arithmetic of poly1305-donna64 (lib/crypto/poly1305-donna64.c), for  *)
(* the proofs of poly1305_core_blocks and poly1305_core_emit: numbers are in *)
(* three limbs of 44, 44 and 42 bits, partly reduced modulo p = 2^130 - 5.   *)
(* POLY1305_DONNA_BLOCK is one block (multiplication by r with 20 * r for    *)
(* the wrap-around), POLY1305_DONNA_EMIT the final reduction and the         *)
(* addition of the nonce, both with the computation as gcc's code does it.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* The arithmetic of a block: the product of the limbs modulo p, and the     *)
(* bounds and the congruence for the limbs after the partial reduction.      *)
(* ------------------------------------------------------------------------- *)

let POLY1305_DONNA_IDENT = prove
 (`!a0 a1 a2 r0 r1 r2.
     (a0 + 2 EXP 44 * a1 + 2 EXP 88 * a2) *
     (r0 + 2 EXP 44 * r1 + 2 EXP 88 * r2) =
     ((a0 * r0 + a1 * (20 * r2) + a2 * (20 * r1)) +
      2 EXP 44 * (a0 * r1 + a1 * r0 + a2 * (20 * r2)) +
      2 EXP 88 * (a0 * r2 + a1 * r1 + a2 * r0)) +
     (2 EXP 130 - 5) * (4 * (a1 * r2 + a2 * r1) + 2 EXP 46 * a2 * r2)`,
  REPEAT GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let POLY1305_DIV_BOUND = prove
 (`!x k m. x < 2 EXP (k + m) ==> x DIV 2 EXP k < 2 EXP m`,
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; EXP_ADD]);;

let POLY1305_DIVB_TAC =
  MATCH_MP_TAC POLY1305_DIV_BOUND THEN
  CONV_TAC(RAND_CONV(RAND_CONV NUM_ADD_CONV)) THEN ASM_REWRITE_TAC[];;

let POLY1305_MUL_LT a ba b bb =
  MATCH_MP LT_MULT2 (CONJ (ASSUME (mk_binop `(<):num->num->bool` a ba))
                          (ASSUME (mk_binop `(<):num->num->bool` b bb)));;

let POLY1305_MOD_EQ = prove
 (`!x y p. (?k. x + p * k = y) ==> x MOD p = y MOD p`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let POLY1305_DONNA_BLOCK = prove
 (`!h0 h1 h2 r0 r1 r2 t0 t1 hb a0 a1 a2 d0 d1 d2 f.
     h0 < 2 EXP 44 /\ h1 < 2 EXP 45 /\ h2 < 2 EXP 42 /\
     r0 < 2 EXP 44 /\ r1 < 2 EXP 44 /\ r2 < 2 EXP 36 /\
     t0 < 2 EXP 64 /\ t1 < 2 EXP 64 /\ hb <= 1 /\
     a0 = t0 MOD 2 EXP 44 + h0 /\
     a1 = (t0 DIV 2 EXP 44 + 2 EXP 20 * t1 MOD 2 EXP 24) + h1 /\
     a2 = (2 EXP 40 * hb + t1 DIV 2 EXP 24) + h2 /\
     d0 = a0 * r0 + a1 * (20 * r2) + a2 * (20 * r1) /\
     d1 = (a0 * r1 + a1 * r0 + a2 * (20 * r2)) + d0 DIV 2 EXP 44 /\
     d2 = (a0 * r2 + a1 * r1 + a2 * r0) + d1 DIV 2 EXP 44 /\
     f = 5 * d2 DIV 2 EXP 42 + d0 MOD 2 EXP 44
     ==> a0 < 2 EXP 45 /\ a1 < 2 EXP 46 /\ a2 < 2 EXP 43 /\
         d0 < 2 EXP 93 /\ d1 < 2 EXP 92 /\ d2 < 2 EXP 92 /\ f < 2 EXP 54 /\
         d1 MOD 2 EXP 44 + f DIV 2 EXP 44 < 2 EXP 45 /\
         (f MOD 2 EXP 44 + 2 EXP 44 * (d1 MOD 2 EXP 44 + f DIV 2 EXP 44) +
          2 EXP 88 * d2 MOD 2 EXP 42) MOD (2 EXP 130 - 5) =
         ((h0 + 2 EXP 44 * h1 + 2 EXP 88 * h2 +
           t0 + 2 EXP 64 * t1 + 2 EXP 128 * hb) *
          (r0 + 2 EXP 44 * r1 + 2 EXP 88 * r2)) MOD (2 EXP 130 - 5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(MP (ARITH_RULE `r1 < 2 EXP 44 ==> 20 * r1 < 20 * 2 EXP 44`)
                (ASSUME `r1 < 2 EXP 44`)) THEN
  ASSUME_TAC(MP (ARITH_RULE `r2 < 2 EXP 36 ==> 20 * r2 < 20 * 2 EXP 36`)
                (ASSUME `r2 < 2 EXP 36`)) THEN
  SUBGOAL_THEN `a0 < 2 EXP 45 /\ a1 < 2 EXP 46 /\ a2 < 2 EXP 43`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`t0:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    MP_TAC(SPECL [`t1:num`; `2 EXP 24`] MOD_LT_EQ) THEN
    SUBGOAL_THEN `t0 DIV 2 EXP 44 < 2 EXP 20` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `t1 DIV 2 EXP 24 < 2 EXP 40` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ASSUME `a0 = t0 MOD 2 EXP 44 + h0`;
      ASSUME `a1 = (t0 DIV 2 EXP 44 + 2 EXP 20 * t1 MOD 2 EXP 24) + h1`;
      ASSUME `a2 = (2 EXP 40 * hb + t1 DIV 2 EXP 24) + h2`] THEN
    MAP_EVERY UNDISCH_TAC
     [`h0 < 2 EXP 44`; `h1 < 2 EXP 45`; `h2 < 2 EXP 42`; `hb <= 1`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d0 < 2 EXP 93` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `d0 = a0 * r0 + a1 * (20 * r2) + a2 * (20 * r1)`] THEN
    MP_TAC(POLY1305_MUL_LT `a0:num` `2 EXP 45` `r0:num` `2 EXP 44`) THEN
    MP_TAC(POLY1305_MUL_LT `a1:num` `2 EXP 46` `20 * r2` `20 * 2 EXP 36`) THEN
    MP_TAC(POLY1305_MUL_LT `a2:num` `2 EXP 43` `20 * r1` `20 * 2 EXP 44`) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d1 < 2 EXP 92` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME
      `d1 = (a0 * r1 + a1 * r0 + a2 * (20 * r2)) + d0 DIV 2 EXP 44`] THEN
    MP_TAC(POLY1305_MUL_LT `a0:num` `2 EXP 45` `r1:num` `2 EXP 44`) THEN
    MP_TAC(POLY1305_MUL_LT `a1:num` `2 EXP 46` `r0:num` `2 EXP 44`) THEN
    MP_TAC(POLY1305_MUL_LT `a2:num` `2 EXP 43` `20 * r2` `20 * 2 EXP 36`) THEN
    SUBGOAL_THEN `d0 DIV 2 EXP 44 < 2 EXP 49` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d2 < 2 EXP 92` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME
      `d2 = (a0 * r2 + a1 * r1 + a2 * r0) + d1 DIV 2 EXP 44`] THEN
    MP_TAC(POLY1305_MUL_LT `a0:num` `2 EXP 45` `r2:num` `2 EXP 36`) THEN
    MP_TAC(POLY1305_MUL_LT `a1:num` `2 EXP 46` `r1:num` `2 EXP 44`) THEN
    MP_TAC(POLY1305_MUL_LT `a2:num` `2 EXP 43` `r0:num` `2 EXP 44`) THEN
    SUBGOAL_THEN `d1 DIV 2 EXP 44 < 2 EXP 48` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f < 2 EXP 54` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `f = 5 * d2 DIV 2 EXP 42 + d0 MOD 2 EXP 44`] THEN
    MP_TAC(SPECL [`d0:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    SUBGOAL_THEN `d2 DIV 2 EXP 42 < 2 EXP 50` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPLICATE_TAC 7 (CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`d1:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    SUBGOAL_THEN `f DIV 2 EXP 44 < 2 EXP 10` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f MOD 2 EXP 44 + 2 EXP 44 * (d1 MOD 2 EXP 44 + f DIV 2 EXP 44) +
    2 EXP 88 * d2 MOD 2 EXP 42 + (2 EXP 130 - 5) * d2 DIV 2 EXP 42 =
    d0 + 2 EXP 44 * (a0 * r1 + a1 * r0 + a2 * (20 * r2)) +
    2 EXP 88 * (a0 * r2 + a1 * r1 + a2 * r0)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`f:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`d0:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`d1:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`d2:num`; `2 EXP 42`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`f = 5 * d2 DIV 2 EXP 42 + d0 MOD 2 EXP 44`;
      `d2 = (a0 * r2 + a1 * r1 + a2 * r0) + d1 DIV 2 EXP 44`;
      `d1 = (a0 * r1 + a1 * r0 + a2 * (20 * r2)) + d0 DIV 2 EXP 44`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `h0 + 2 EXP 44 * h1 + 2 EXP 88 * h2 + t0 + 2 EXP 64 * t1 + 2 EXP 128 * hb =
    a0 + 2 EXP 44 * a1 + 2 EXP 88 * a2`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`t0:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`t1:num`; `2 EXP 24`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`a0 = t0 MOD 2 EXP 44 + h0`;
      `a1 = (t0 DIV 2 EXP 44 + 2 EXP 20 * t1 MOD 2 EXP 24) + h1`;
      `a2 = (2 EXP 40 * hb + t1 DIV 2 EXP 24) + h2`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[POLY1305_DONNA_IDENT] THEN
  UNDISCH_THEN `d0 = a0 * r0 + a1 * (20 * r2) + a2 * (20 * r1)`
   (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC POLY1305_MOD_EQ THEN
  EXISTS_TAC
   `d2 DIV 2 EXP 42 + 4 * (a1 * r2 + a2 * r1) + 2 EXP 46 * a2 * r2` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_eq(concl th) && can (find_term ((=) `2 EXP 130 - 5`)) (concl th))) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The limbs of the block from its two words t0 and t1, and of the top limb  *)
(* with 2^128 * hibit (hibit << 40 in the top limb).                         *)
(* ------------------------------------------------------------------------- *)

let POLY1305_M1_WORD = prove
 (`!(t0:int64) (t1:int64).
     word_and (word_subword (word_join t1 t0:int128) (44,64):int64)
              (word 17592186044415) =
     word_add (word_ushr t0 44) (word_shl (word_and t1 (word 16777215)) 20)`,
  BITBLAST_TAC);;

let POLY1305_M2_WORD = prove
 (`!hb t1:int64.
     word_or (word_shl hb 40) (word_ushr t1 24) =
     word_add (word_shl hb 40) (word_ushr t1 24)`,
  BITBLAST_TAC);;

let POLY1305_M1 = prove
 (`!(t0:int64) (t1:int64).
     val(word_and (word_subword (word_join t1 t0:int128) (44,64):int64)
                  (word 17592186044415)) =
     val t0 DIV 2 EXP 44 + 2 EXP 20 * val t1 MOD 2 EXP 24`,
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY1305_M1_WORD] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_SHL; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `16777215 = 2 EXP 24 - 1`; VAL_WORD_AND_MASK_WORD] THEN
  MP_TAC(SPECL [`val(t1:int64)`; `2 EXP 24`] MOD_LT_EQ) THEN
  SUBGOAL_THEN `val(t0:int64) DIV 2 EXP 44 < 2 EXP 20` MP_TAC THENL
   [MATCH_MP_TAC POLY1305_DIV_BOUND THEN
    CONV_TAC(RAND_CONV(RAND_CONV NUM_ADD_CONV)) THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND];
    ALL_TAC] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP 20 * val(t1:int64) MOD 2 EXP 24 < 2 EXP 64`
  ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let POLY1305_M2 = prove
 (`!hb t1:int64.
     val hb <= 1
     ==> val(word_or (word_shl hb 40) (word_ushr t1 24)) =
         2 EXP 40 * val hb + val t1 DIV 2 EXP 24`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[POLY1305_M2_WORD] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_SHL; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(t1:int64) DIV 2 EXP 24 < 2 EXP 40` MP_TAC THENL
   [MATCH_MP_TAC POLY1305_DIV_BOUND THEN
    CONV_TAC(RAND_CONV(RAND_CONV NUM_ADD_CONV)) THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP 40 * val(hb:int64) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* Modular arithmetic for a step of the accumulator.                        *)

let POLY1305_MOD_STEP = prove
 (`!x y t r p. x MOD p = y MOD p ==> ((x + t) * r) MOD p = ((y + t) * r) MOD p`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The final reduction (two rounds of carries, the subtraction of p if the  *)
(* value is at least p, selected by the top limb y of the value plus 5) and *)
(* the addition of the nonce t0 + 2^64 * t1, packed in 128 bits.            *)
(* ------------------------------------------------------------------------- *)

let POLY1305_DONNA_EMIT = prove
 (`!h0 h1 h2 t0 t1 x0a c1 x0c x0d x0e x0h h0f h1f h2f g0 g1 y s0 s1 s2
    n0 n1 n2.
     h0 < 2 EXP 44 /\ h1 < 2 EXP 45 /\ h2 < 2 EXP 42 /\
     t0 < 2 EXP 64 /\ t1 < 2 EXP 64 /\
     x0a = h2 + h1 DIV 2 EXP 44 /\ c1 = x0a DIV 2 EXP 42 /\
     x0c = 5 * c1 + h0 /\ x0d = h1 MOD 2 EXP 44 + x0c DIV 2 EXP 44 /\
     x0e = x0a MOD 2 EXP 42 + x0d DIV 2 EXP 44 /\
     x0h = 5 * x0e DIV 2 EXP 42 + x0c MOD 2 EXP 44 /\
     h0f = x0h MOD 2 EXP 44 /\ h1f = x0d MOD 2 EXP 44 + x0h DIV 2 EXP 44 /\
     h2f = x0e MOD 2 EXP 42 /\
     g0 = h0f + 5 /\ g1 = h1f + g0 DIV 2 EXP 44 /\ y = h2f + g1 DIV 2 EXP 44 /\
     (if 2 EXP 42 <= y
      then s0 = g0 MOD 2 EXP 44 /\ s1 = g1 MOD 2 EXP 44 /\ s2 = y - 2 EXP 42
      else s0 = h0f /\ s1 = h1f /\ s2 = h2f) /\
     n0 = t0 MOD 2 EXP 44 + s0 /\
     n1 = ((t0 DIV 2 EXP 44 + 2 EXP 20 * t1 MOD 2 EXP 24) + s1) +
          n0 DIV 2 EXP 44 /\
     n2 = (s2 + t1 DIV 2 EXP 24) + n1 DIV 2 EXP 44
     ==> x0a <= 2 EXP 42 /\ c1 <= 1 /\ x0c < 2 EXP 44 + 5 /\
         x0d <= 2 EXP 44 /\ x0e <= 2 EXP 42 /\ x0h < 2 EXP 44 + 5 /\
         h1f <= 2 EXP 44 /\
         g1 < 2 EXP 45 /\ y < 2 EXP 43 /\
         s0 < 2 EXP 44 /\ s1 <= 2 EXP 44 /\ s2 < 2 EXP 42 /\
         n0 < 2 EXP 45 /\ n1 < 2 EXP 46 /\ n2 < 2 EXP 43 /\
         (n0 MOD 2 EXP 44 + 2 EXP 44 * n1 MOD 2 EXP 44 +
          2 EXP 88 * n2 MOD 2 EXP 42) MOD 2 EXP 128 =
         ((h0 + 2 EXP 44 * h1 + 2 EXP 88 * h2) MOD (2 EXP 130 - 5) +
          t0 + 2 EXP 64 * t1) MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (*** Round A bounds ***)
  SUBGOAL_THEN `h1 DIV 2 EXP 44 <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    POLY1305_DIVB_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0a <= 2 EXP 42` ASSUME_TAC THENL
   [UNDISCH_TAC `x0a = h2 + h1 DIV 2 EXP 44` THEN
    UNDISCH_TAC `h2 < 2 EXP 42` THEN UNDISCH_TAC `h1 DIV 2 EXP 44 <= 1` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1 <= 1` ASSUME_TAC THENL
   [UNDISCH_TAC `c1 = x0a DIV 2 EXP 42` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    MATCH_MP_TAC POLY1305_DIV_BOUND THEN UNDISCH_TAC `x0a <= 2 EXP 42` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0c < 2 EXP 44 + 5` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`x0c = 5 * c1 + h0`; `c1 <= 1`; `h0 < 2 EXP 44`] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0c DIV 2 EXP 44 <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    MATCH_MP_TAC POLY1305_DIV_BOUND THEN UNDISCH_TAC `x0c < 2 EXP 44 + 5` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0d <= 2 EXP 44` ASSUME_TAC THENL
   [MP_TAC(SPECL [`h1:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`x0d = h1 MOD 2 EXP 44 + x0c DIV 2 EXP 44`; `x0c DIV 2 EXP 44 <= 1`] THEN
    ARITH_TAC; ALL_TAC] THEN
  (*** Round B bounds ***)
  SUBGOAL_THEN `x0d DIV 2 EXP 44 <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    MATCH_MP_TAC POLY1305_DIV_BOUND THEN UNDISCH_TAC `x0d <= 2 EXP 44` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0e <= 2 EXP 42` ASSUME_TAC THENL
   [MP_TAC(SPECL [`x0a:num`; `2 EXP 42`] MOD_LT_EQ) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`x0e = x0a MOD 2 EXP 42 + x0d DIV 2 EXP 44`; `x0d DIV 2 EXP 44 <= 1`] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0e DIV 2 EXP 42 <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    MATCH_MP_TAC POLY1305_DIV_BOUND THEN UNDISCH_TAC `x0e <= 2 EXP 42` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0h < 2 EXP 44 + 5` ASSUME_TAC THENL
   [MP_TAC(SPECL [`x0c:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`x0h = 5 * x0e DIV 2 EXP 42 + x0c MOD 2 EXP 44`;
      `x0e DIV 2 EXP 42 <= 1`] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0h DIV 2 EXP 44 <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    MATCH_MP_TAC POLY1305_DIV_BOUND THEN UNDISCH_TAC `x0h < 2 EXP 44 + 5` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h0f < 2 EXP 44 /\ h1f <= 2 EXP 44 /\ h2f < 2 EXP 42`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`x0h:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    MP_TAC(SPECL [`x0d:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    MP_TAC(SPECL [`x0e:num`; `2 EXP 42`] MOD_LT_EQ) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`h0f = x0h MOD 2 EXP 44`;
      `h1f = x0d MOD 2 EXP 44 + x0h DIV 2 EXP 44`;
      `h2f = x0e MOD 2 EXP 42`; `x0h DIV 2 EXP 44 <= 1`] THEN
    ARITH_TAC; ALL_TAC] THEN
  (*** The fully carried value H' and its congruence ***)
  SUBGOAL_THEN
   `h0 + 2 EXP 44 * h1 + 2 EXP 88 * h2 =
    (h0f + 2 EXP 44 * h1f + 2 EXP 88 * h2f) +
    (2 EXP 130 - 5) * (c1 + x0e DIV 2 EXP 42)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`h1:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`x0a:num`; `2 EXP 42`] DIVISION) THEN
    MP_TAC(SPECL [`x0c:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`x0d:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`x0e:num`; `2 EXP 42`] DIVISION) THEN
    MP_TAC(SPECL [`x0h:num`; `2 EXP 44`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`x0a = h2 + h1 DIV 2 EXP 44`; `c1 = x0a DIV 2 EXP 42`;
      `x0c = 5 * c1 + h0`; `x0d = h1 MOD 2 EXP 44 + x0c DIV 2 EXP 44`;
      `x0e = x0a MOD 2 EXP 42 + x0d DIV 2 EXP 44`;
      `x0h = 5 * x0e DIV 2 EXP 42 + x0c MOD 2 EXP 44`;
      `h0f = x0h MOD 2 EXP 44`; `h1f = x0d MOD 2 EXP 44 + x0h DIV 2 EXP 44`;
      `h2f = x0e MOD 2 EXP 42`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  (*** The selected value is H mod p ***)
  SUBGOAL_THEN `g0 DIV 2 EXP 44 <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    MATCH_MP_TAC POLY1305_DIV_BOUND THEN
    MAP_EVERY UNDISCH_TAC [`g0 = h0f + 5`; `h0f < 2 EXP 44`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `g1 < 2 EXP 45` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`g1 = h1f + g0 DIV 2 EXP 44`; `h1f <= 2 EXP 44`;
      `g0 DIV 2 EXP 44 <= 1`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `g1 DIV 2 EXP 44 <= 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
    POLY1305_DIVB_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y < 2 EXP 43` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`y = h2f + g1 DIV 2 EXP 44`; `h2f < 2 EXP 42`;
      `g1 DIV 2 EXP 44 <= 1`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h0f + 2 EXP 44 * h1f + 2 EXP 88 * h2f) + 5 =
    g0 MOD 2 EXP 44 + 2 EXP 44 * g1 MOD 2 EXP 44 + 2 EXP 88 * y`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:num`; `2 EXP 44`] DIVISION) THEN
    MP_TAC(SPECL [`g1:num`; `2 EXP 44`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC
     [`g0 = h0f + 5`; `g1 = h1f + g0 DIV 2 EXP 44`;
      `y = h2f + g1 DIV 2 EXP 44`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:num`; `2 EXP 44`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`g1:num`; `2 EXP 44`] MOD_LT_EQ) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `s0 + 2 EXP 44 * s1 + 2 EXP 88 * s2 =
    (h0f + 2 EXP 44 * h1f + 2 EXP 88 * h2f) MOD (2 EXP 130 - 5) /\
    s0 < 2 EXP 44 /\ s1 <= 2 EXP 44 /\ s2 < 2 EXP 42`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    COND_CASES_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) &&
      mem (lhand(concl th)) [`s0:num`; `s1:num`; `s2:num`]))) THENL
     [REPEAT CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
        MAP_EVERY UNDISCH_TAC
         [`(h0f + 2 EXP 44 * h1f + 2 EXP 88 * h2f) + 5 =
           g0 MOD 2 EXP 44 + 2 EXP 44 * g1 MOD 2 EXP 44 + 2 EXP 88 * y`;
          `2 EXP 42 <= y`; `g0 MOD 2 EXP 44 < 2 EXP 44`;
          `g1 MOD 2 EXP 44 < 2 EXP 44`; `y < 2 EXP 43`;
          `h0f < 2 EXP 44`; `h1f <= 2 EXP 44`; `h2f < 2 EXP 42`] THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
        ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        MAP_EVERY UNDISCH_TAC [`g1 MOD 2 EXP 44 < 2 EXP 44`] THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
        MAP_EVERY UNDISCH_TAC [`y < 2 EXP 43`; `2 EXP 42 <= y`] THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC];
      REPEAT CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
        MAP_EVERY UNDISCH_TAC
         [`(h0f + 2 EXP 44 * h1f + 2 EXP 88 * h2f) + 5 =
           g0 MOD 2 EXP 44 + 2 EXP 44 * g1 MOD 2 EXP 44 + 2 EXP 88 * y`;
          `~(2 EXP 42 <= y)`; `g0 MOD 2 EXP 44 < 2 EXP 44`;
          `g1 MOD 2 EXP 44 < 2 EXP 44`] THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
        ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h0 + 2 EXP 44 * h1 + 2 EXP 88 * h2) MOD (2 EXP 130 - 5) =
    s0 + 2 EXP 44 * s1 + 2 EXP 88 * s2`
  ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME
      `s0 + 2 EXP 44 * s1 + 2 EXP 88 * s2 =
       (h0f + 2 EXP 44 * h1f + 2 EXP 88 * h2f) MOD (2 EXP 130 - 5)`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY1305_MOD_EQ THEN
    EXISTS_TAC `c1 + x0e DIV 2 EXP 42` THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (*** The nonce and the packing ***)
  SUBGOAL_THEN `n0 < 2 EXP 45 /\ n1 < 2 EXP 46 /\ n2 < 2 EXP 43`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`t0:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    MP_TAC(SPECL [`t1:num`; `2 EXP 24`] MOD_LT_EQ) THEN
    SUBGOAL_THEN `t0 DIV 2 EXP 44 < 2 EXP 20` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `t1 DIV 2 EXP 24 < 2 EXP 40` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `n0 < 2 EXP 45` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`n0 = t0 MOD 2 EXP 44 + s0`; `t0 MOD 2 EXP 44 < 2 EXP 44`;
        `s0 < 2 EXP 44`] THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `n0 DIV 2 EXP 44 <= 1` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x <= 1`) THEN
      POLY1305_DIVB_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `n1 < 2 EXP 46` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`n1 = ((t0 DIV 2 EXP 44 + 2 EXP 20 * t1 MOD 2 EXP 24) + s1) +
              n0 DIV 2 EXP 44`;
        `t0 DIV 2 EXP 44 < 2 EXP 20`; `t1 MOD 2 EXP 24 < 2 EXP 24`;
        `s1 <= 2 EXP 44`; `n0 DIV 2 EXP 44 <= 1`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `n1 DIV 2 EXP 44 <= 3` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 2 ==> x <= 3`) THEN
      POLY1305_DIVB_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`n2 = (s2 + t1 DIV 2 EXP 24) + n1 DIV 2 EXP 44`; `s2 < 2 EXP 42`;
      `t1 DIV 2 EXP 24 < 2 EXP 40`; `n1 DIV 2 EXP 44 <= 3`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  REPLICATE_TAC 15 (CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) &&
    rand(concl th) = `s0 + 2 EXP 44 * s1 + 2 EXP 88 * s2`)) THEN
  MATCH_MP_TAC POLY1305_MOD_EQ THEN EXISTS_TAC `4 * n2 DIV 2 EXP 42` THEN
  MP_TAC(SPECL [`t0:num`; `2 EXP 44`] DIVISION) THEN
  MP_TAC(SPECL [`t1:num`; `2 EXP 24`] DIVISION) THEN
  MP_TAC(SPECL [`n0:num`; `2 EXP 44`] DIVISION) THEN
  MP_TAC(SPECL [`n1:num`; `2 EXP 44`] DIVISION) THEN
  MP_TAC(SPECL [`n2:num`; `2 EXP 42`] DIVISION) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  MAP_EVERY UNDISCH_TAC
   [`n0 = t0 MOD 2 EXP 44 + s0`;
    `n1 = ((t0 DIV 2 EXP 44 + 2 EXP 20 * t1 MOD 2 EXP 24) + s1) +
          n0 DIV 2 EXP 44`;
    `n2 = (s2 + t1 DIV 2 EXP 24) + n1 DIV 2 EXP 44`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

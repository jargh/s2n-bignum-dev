(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemire's uniform random integer below a bound, threshold without UDIV.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/word_recip.ml";;
needs "common/lemire.ml";;

(**** print_literal_from_elf "arm/random/lemire_random_divfree_VARIABLE_TIME.o";;
 ****)

let lemire_random_divfree_mc = define_assert_from_elf
  "lemire_random_divfree_mc" "arm/random/lemire_random_divfree_VARIABLE_TIME.o"
[
  0xb40008e2;       (* arm_CBZ X2 (word 284) *)
  0xf9400064;       (* arm_LDR X4 X3 (Immediate_Offset (word 0)) *)
  0x9b017c85;       (* arm_MUL X5 X4 X1 *)
  0x9bc17c86;       (* arm_UMULH X6 X4 X1 *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0xeb0100bf;       (* arm_CMP X5 X1 *)
  0x54000862;       (* arm_BCS (word 268) *)
  0xaa0003e9;       (* arm_MOV X9 X0 *)
  0xaa0103ea;       (* arm_MOV X10 X1 *)
  0xaa0203eb;       (* arm_MOV X11 X2 *)
  0xaa0303ec;       (* arm_MOV X12 X3 *)
  0xdac0102d;       (* arm_CLZ X13 X1 *)
  0x9acd2020;       (* arm_LSLV X0 X1 X13 *)
  0xd350fc02;       (* arm_LSR X2 X0 16 *)
  0xd240c041;       (* arm_EOR X1 X2 (rvalue (word 562949953421311)) *)
  0x91000442;       (* arm_ADD X2 X2 (rvalue (word 1)) *)
  0xd360fc21;       (* arm_LSR X1 X1 32 *)
  0x9b01fc44;       (* arm_MNEG X4 X2 X1 *)
  0xd371fc83;       (* arm_LSR X3 X4 49 *)
  0x9b037c63;       (* arm_MUL X3 X3 X3 *)
  0xd362fc84;       (* arm_LSR X4 X4 34 *)
  0x8b040064;       (* arm_ADD X4 X3 X4 *)
  0xb2620063;       (* arm_ORR X3 X3 (rvalue (word 1073741824)) *)
  0x9b037c83;       (* arm_MUL X3 X4 X3 *)
  0xd35efc63;       (* arm_LSR X3 X3 30 *)
  0xd3628424;       (* arm_LSL X4 X1 30 *)
  0x9b031021;       (* arm_MADD X1 X1 X3 X4 *)
  0xd35efc21;       (* arm_LSR X1 X1 30 *)
  0x9b01fc44;       (* arm_MNEG X4 X2 X1 *)
  0xd358fc84;       (* arm_LSR X4 X4 24 *)
  0x9b017c84;       (* arm_MUL X4 X4 X1 *)
  0xd370bc21;       (* arm_LSL X1 X1 16 *)
  0xd358fc84;       (* arm_LSR X4 X4 24 *)
  0x8b040021;       (* arm_ADD X1 X1 X4 *)
  0x9b01fc44;       (* arm_MNEG X4 X2 X1 *)
  0xd360fc84;       (* arm_LSR X4 X4 32 *)
  0x9b017c84;       (* arm_MUL X4 X4 X1 *)
  0xd3618021;       (* arm_LSL X1 X1 31 *)
  0xd351fc84;       (* arm_LSR X4 X4 17 *)
  0x8b040021;       (* arm_ADD X1 X1 X4 *)
  0x9b017c03;       (* arm_MUL X3 X0 X1 *)
  0x9bc17c04;       (* arm_UMULH X4 X0 X1 *)
  0x93c3f083;       (* arm_EXTR X3 X4 X3 60 *)
  0xd361fc24;       (* arm_LSR X4 X1 33 *)
  0xaa2303e3;       (* arm_MVN X3 X3 *)
  0x9b037c83;       (* arm_MUL X3 X4 X3 *)
  0xd37ff821;       (* arm_LSL X1 X1 1 *)
  0xd361fc63;       (* arm_LSR X3 X3 33 *)
  0x8b030021;       (* arm_ADD X1 X1 X3 *)
  0xb1000423;       (* arm_ADDS X3 X1 (rvalue (word 1)) *)
  0xda831063;       (* arm_CINV X3 X3 Condition_EQ *)
  0x9bc37c04;       (* arm_UMULH X4 X0 X3 *)
  0xab000084;       (* arm_ADDS X4 X4 X0 *)
  0x9a832020;       (* arm_CSEL X0 X1 X3 Condition_CS *)
  0xd24015ad;       (* arm_EOR X13 X13 (rvalue (word 63)) *)
  0xd341fc00;       (* arm_LSR X0 X0 1 *)
  0xb2410000;       (* arm_ORR X0 X0 (rvalue (word 9223372036854775808)) *)
  0x9acd2400;       (* arm_LSRV X0 X0 X13 *)
  0x9b0afc08;       (* arm_MNEG X8 X0 X10 *)
  0xeb0a0104;       (* arm_SUBS X4 X8 X10 *)
  0x9a882088;       (* arm_CSEL X8 X4 X8 Condition_CS *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0xeb0800bf;       (* arm_CMP X5 X8 *)
  0x54000142;       (* arm_BCS (word 40) *)
  0xeb0b00ff;       (* arm_CMP X7 X11 *)
  0x540000c2;       (* arm_BCS (word 24) *)
  0xf8677984;       (* arm_LDR X4 X12 (Shiftreg_Offset X7 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0x9b0a7c85;       (* arm_MUL X5 X4 X10 *)
  0x9bca7c86;       (* arm_UMULH X6 X4 X10 *)
  0x17fffff8;       (* arm_B (word 268435424) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0x14000002;       (* arm_B (word 8) *)
  0xf9000006;       (* arm_STR X6 X0 (Immediate_Offset (word 0)) *)
  0xaa0703e0;       (* arm_MOV X0 X7 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let LEMIRE_RANDOM_DIVFREE_EXEC = ARM_MK_EXEC_RULE lemire_random_divfree_mc;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about the machine-level arithmetic.                           *)
(* ------------------------------------------------------------------------- *)

let READ_WORDLIST_EL = prove
 (`!x n (l:int64 list) k s.
        LENGTH l = n /\
        read (memory :> bytes(x,8 * n)) s = num_of_wordlist l /\
        k < n
        ==> read (memory :> bytes64(word_add x (word(8 * k)))) s = EL k l`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_var(rhs(concl th)))) THEN
  MP_TAC(ISPECL [`x:int64`; `LENGTH(l:int64 list)`; `k:num`; `s:armstate`]
    (INST_TYPE [`:8`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  REWRITE_TAC[WORDLIST_OF_NUM_OF_WORDLIST] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[bytes64; wbytes; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_MUL_MOD = prove
 (`!a s:int64. word_mul a s = word((val a * val s) MOD 2 EXP 64)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
              MOD_MOD_REFL]);;

let VAL_WORD_THRESHOLD = prove
 (`!s:int64. ~(val s = 0)
             ==> val(word(2 EXP 64 MOD val s):int64) = 2 EXP 64 MOD val s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `val(s:int64)` THEN
  ASM_SIMP_TAC[MOD_LT_EQ; LT_IMP_LE; VAL_BOUND_64]);;

(*** The normalization of s, shifting it left by clz(s) places ***)

let WORD_JSHL_CLZ = prove
 (`!s:int64. ~(s = word 0)
             ==> word_jshl s (word(word_clz s)) = word_shl s (word_clz s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jshl; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(ISPEC `s:int64` WORD_CLZ_LT_DIMINDEX) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `c < 64 ==> c < 2 EXP 64`]);;

let VAL_WORD_SHL_CLZ = prove
 (`!s:int64. val(word_shl s (word_clz s)) = 2 EXP (word_clz s) * val s`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SHL; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND_CLZ; LE_REFL]);;

let MSB_WORD_SHL_CLZ = prove
 (`!s:int64. ~(s = word 0) ==> 2 EXP 63 <= val(word_shl s (word_clz s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SHL_CLZ] THEN
  MP_TAC(ISPECL [`s:int64`; `word_clz(s:int64) + 1`] VAL_BOUND_CLZ) THEN
  ASM_REWRITE_TAC[DIMINDEX_64; ARITH_RULE `~(c + 1 <= c)`; EXP_ADD] THEN
  ARITH_TAC);;

let BIT63_WORD_SHL_CLZ = prove
 (`!s:int64. ~(s = word 0) ==> bit 63 (word_shl s (word_clz s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `word_shl s (word_clz s):int64` MSB_VAL) THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MSB_WORD_SHL_CLZ]);;

(*** The mneg and the shift by 63 - clz(s) computed as clz(s) XOR 63 ***)

let WORD_MNEG_LEMMA = prove
 (`!a b:int64. iword(&0 - ival a * ival b) = word_neg(word_mul a b)`,
  CONV_TAC WORD_RULE);;

let WORD_JUSHR_CLZ = prove
 (`!s:int64.
        ~(s = word 0)
        ==> !y:int64. word_jushr y (word_xor (word(word_clz s)) (word 63)) =
                      word_ushr y (63 - word_clz s)`,
  GEN_TAC THEN REWRITE_TAC[word_jushr; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM WORD_CLZ_LT_DIMINDEX; DIMINDEX_64] THEN
  SPEC_TAC(`word_clz(s:int64)`,`c:num`) THEN GEN_TAC THEN
  DISCH_TAC THEN GEN_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `c < 64` THEN SPEC_TAC(`c:num`,`c:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

(*** From the reciprocal to the threshold: first the pure arithmetic ***)

let LEMIRE_RECIP_QUOTIENT = prove
 (`!S C K M.
        ~(S = 0) /\ K * C = 2 EXP 64 /\ ~(K = 0) /\ K <= 2 EXP 64 /\
        2 EXP 64 <= M /\
        M * (C * S) < 2 EXP 64 * 2 EXP 64 /\
        2 EXP 64 * 2 EXP 64 <= (M + 1) * (C * S)
        ==> 1 <= (M DIV K) * S /\
            (M DIV K) * S < 2 EXP 64 /\
            2 EXP 64 <= (M DIV K + 1) * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `K:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`M MOD K`,`r:num`) THEN SPEC_TAC(`M DIV K`,`q:num`) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`2 EXP 64 <= 0 * K + r`; `r < K`; `K <= 2 EXP 64`] THEN
    ARITH_TAC;
    SUBGOAL_THEN `(q * S) * (K * C) < 2 EXP 64 * (K * C)` MP_TAC THENL
     [TRANS_TAC LET_TRANS `(q * K + r) * (C * S)` THEN CONJ_TAC THENL
       [REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
        MATCH_MP_TAC(ARITH_RULE `a:num = b ==> a <= b + c`) THEN
        REWRITE_TAC[MULT_AC];
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]];
    SUBGOAL_THEN `2 EXP 64 * (K * C) <= ((q + 1) * S) * (K * C)` MP_TAC THENL
     [TRANS_TAC LE_TRANS `((q * K + r) + 1) * (C * S)` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        TRANS_TAC LE_TRANS `((q + 1) * K) * (C * S)` THEN CONJ_TAC THENL
         [REWRITE_TAC[LE_MULT_RCANCEL] THEN UNDISCH_TAC `r < K` THEN ARITH_TAC;
          REWRITE_TAC[MULT_AC; LE_REFL]]];
      ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]]]);;

(*** The final correction, given 1 <= q * s < 2^64 <= (q + 1) * s ***)

let LEMIRE_THRESHOLD_CORRECTION = prove
 (`!s q:int64.
        1 <= val q * val s /\ val q * val s < 2 EXP 64 /\
        2 EXP 64 <= (val q + 1) * val s
        ==> (if val s <= val(word_neg(word_mul q s))
             then word_sub (word_neg(word_mul q s)) s
             else word_neg(word_mul q s)) =
            word(2 EXP 64 MOD val s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word_neg(word_mul q s):int64) = 2 EXP 64 - val q * val s`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_NEG_CASES; VAL_WORD_MUL; DIMINDEX_64; MOD_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `word_neg(word_mul q s):int64 = s` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SUB_REFL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[MOD_EQ_0] THEN EXISTS_TAC `val(q:int64) + 1` THEN
    ASM_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC `val(q:int64)` THEN ASM_ARITH_TAC]);;

(*** The quotient approximation from the reciprocal and clz result ***)

let LEMIRE_RECIP_Q = prove
 (`!s:int64 rcp:int64.
        ~(s = word 0)
        ==> val(word_ushr (word_or (word_ushr rcp 1)
                                   (word 9223372036854775808))
                          (63 - word_clz s)) =
            (2 EXP 64 + val rcp) DIV 2 EXP (64 - word_clz s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM WORD_CLZ_LT_DIMINDEX; DIMINDEX_64] THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) WORD_ADD_OR o
    lhand o rand o lhand o snd) THEN
  ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(ISPEC `rcp:int64` VAL_BOUND_64) THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `9223372036854775808 MOD 2 EXP 64 = 2 EXP 63`] THEN
  SUBGOAL_THEN
   `(val(rcp:int64) DIV 2 EXP 1 + 2 EXP 63) MOD 2 EXP 64 =
    (2 EXP 64 + val rcp) DIV 2 EXP 1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(MESON[MOD_LT] `a = b /\ a < n ==> a MOD n = b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 EXP 64 + r = 2 EXP 63 * 2 EXP 1 + r`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE `a < 2 EXP 63 ==> a + 2 EXP 63 < 2 EXP 64`) THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(*** Putting it together, in the form the simulation produces ***)

let LEMIRE_RECIP_THRESHOLD = prove
 (`!s:int64 rcp:int64.
     ~(s = word 0) /\
     &2 pow 64 + &(val rcp) < &2 pow 128 / &(2 EXP word_clz s * val s) /\
     &2 pow 128 / &(2 EXP word_clz s * val s) <= &2 pow 64 + &(val rcp) + &1
     ==> (if val s <= val(word_neg(word_mul
               (word_ushr (word_or (word_ushr rcp 1)
                                   (word 9223372036854775808))
                          (63 - word_clz s)) s))
          then word_sub (word_neg(word_mul
               (word_ushr (word_or (word_ushr rcp 1)
                                   (word 9223372036854775808))
                          (63 - word_clz s)) s)) s
          else word_neg(word_mul
               (word_ushr (word_or (word_ushr rcp 1)
                                   (word 9223372036854775808))
                          (63 - word_clz s)) s)) =
         word(2 EXP 64 MOD val s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC LEMIRE_THRESHOLD_CORRECTION THEN
  ASM_SIMP_TAC[LEMIRE_RECIP_Q] THEN
  MP_TAC(SPECL [`val(s:int64)`; `2 EXP word_clz(s:int64)`;
                `2 EXP (64 - word_clz(s:int64))`; `2 EXP 64 + val(rcp:int64)`]
         LEMIRE_RECIP_QUOTIENT) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `word_clz(s:int64) < 64 /\ ~(val s = 0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0; GSYM DIMINDEX_64; WORD_CLZ_LT_DIMINDEX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM EXP_ADD; EXP_EQ_0; ARITH_EQ; LE_EXP; LE_ADD] THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(2 EXP word_clz s * val(s:int64)):real` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(SIMP_RULE
   [ASSUME `&0 < &(2 EXP word_clz s * val(s:int64)):real`;
    REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
  REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `64 + 64 = 128`; GSYM ADD_ASSOC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The slow path computing the threshold, up to the start of the main loop. *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_DIVFREE_SLOW = prove
 (`!z s n x (l:int64 list) z0 pc.
    ~(val s = 0) /\ nonoverlapping (word pc,0x130) (z,8) /\
    LENGTH l = val n /\ ~(val n = 0) /\
    ~(val s <= (val(EL 0 l) * val s) MOD 2 EXP 64)
    ==> ensures arm
         (\st. aligned_bytes_loaded st (word pc) lemire_random_divfree_mc /\
               read PC st = word pc /\
               read X0 st = z /\ read X1 st = s /\
               read X2 st = n /\ read X3 st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0)
         (\st. aligned_bytes_loaded st (word pc) lemire_random_divfree_mc /\
               read PC st = word(pc + 0xf8) /\
               read X0 st = z /\ read X10 st = s /\
               read X11 st = n /\ read X12 st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0 /\
               read X7 st = word 1 /\
               read X8 st = word(2 EXP 64 MOD val s) /\
               read X5 st = word(val(EL 0 l) * val s) /\
               read X6 st = word((val(EL 0 l) * val s) DIV 2 EXP 64))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes64 z])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `s:int64`; `n:int64`; `x:int64`; `l:int64 list`;
    `z0:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(s:int64 = word 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `read (memory :> bytes64 (word_add x (word(8 * 0)))) s0 =
                EL 0 (l:int64 list)` MP_TAC THENL
   [MATCH_MP_TAC READ_WORDLIST_EL THEN EXISTS_TAC `val(n:int64)` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(val(n:int64) = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_TAC THEN

  (*** The initial part, where the test for the fast path fails ***)

  ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD; DIMINDEX_64;
                              MOD_MOD_REFL]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** Save registers and normalize s ***)

  ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (8--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_JSHL_CLZ (ASSUME `~(s:int64 = word 0)`)]) THEN

  (*** The reciprocal, using the existing proof of the word_recip code ***)

  ARM_SUBROUTINE_SIM_TAC
   (lemire_random_divfree_mc,LEMIRE_RANDOM_DIVFREE_EXEC,0x34,
    (GEN_REWRITE_CONV RAND_CONV [word_recip_mc] THENC TRIM_LIST_CONV)
    `TRIM_LIST (0,4) word_recip_mc`,
    WORD_RECIP_CORE_CORRECT)
   [`read X0 s`; `pc + 0x34`] 14 THEN
  ABBREV_TAC `rcp = read X0 s14` THEN
  FIRST_X_ASSUM(MP_TAC o check
   (can (find_term ((=) `bit:num->int64->bool`)) o concl)) THEN
  REWRITE_TAC[ASSUME `read X0 s14 = rcp`] THEN
  ASM_SIMP_TAC[BIT63_WORD_SHL_CLZ; VAL_WORD_SHL_CLZ] THEN STRIP_TAC THEN

  (*** The quotient approximation, correction and restoration of z ***)

  ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (15--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [WORD_MNEG_LEMMA;
    MATCH_MP WORD_JUSHR_CLZ (ASSUME `~(s:int64 = word 0)`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LEMIRE_RECIP_THRESHOLD THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main loop, from the point where x6:x5 = x[k-1] * s and the words     *)
(* x[0],...,x[k-2] have all been rejected, by induction on d = n - k.       *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_DIVFREE_LOOP = prove
 (`!z s n x (l:int64 list) z0 pc d k.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x130) (z,8) /\
    LENGTH l = val n /\ 1 <= k /\ k + d = val n /\
    (!j. j < k - 1 ==> ~lemire_accept (2 EXP 64) (val s) (val(EL j l)))
    ==> ensures arm
         (\st. aligned_bytes_loaded st (word pc) lemire_random_divfree_mc /\
               read PC st = word(pc + 0xf8) /\
               read X0 st = z /\ read X10 st = s /\
               read X11 st = n /\ read X12 st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0 /\
               read X7 st = word k /\
               read X8 st = word(2 EXP 64 MOD val s) /\
               read X5 st = word(val(EL (k - 1) l) * val s) /\
               read X6 st = word((val(EL (k - 1) l) * val s) DIV 2 EXP 64))
         (\st. read PC st = word(pc + 0x12c) /\
               read X0 st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes64 z])`,
  let BRANCH_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE
     [ADD_CLAUSES;
      MATCH_MP VAL_WORD_THRESHOLD (ASSUME `~(val(s:int64) = 0)`);
      VAL_WORD; DIMINDEX_64; MOD_MOD_REFL; GSYM lemire_accept]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC in
  let ACCEPT_TAC =
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--2) THEN
    BRANCH_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2 EXP 64`; `val(s:int64)`; `val(n:int64)`;
                   `\i. val(EL i (l:int64 list))`; `k - 1`]
           LEMIRE_DRAWS_RESULT_FIRST) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th; lemire_output])] THEN
    ASM_REWRITE_TAC[] in
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `s:int64`; `n:int64`; `x:int64`; `l:int64 list`;
    `z0:int64`; `pc:num`] THEN
  INDUCT_TAC THEN X_GEN_TAC `k:num` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (SUBGOAL_THEN
    `k - 1 < val(n:int64) /\ k - 1 + 1 = k /\ ~(k = 0) /\ ~(val n = 0)`
   STRIP_ASSUME_TAC THENL
    [MAP_EVERY UNDISCH_TAC [`1 <= k`] THEN
     FIRST_ASSUM(MP_TAC o check (fun th ->
       is_eq(concl th) && rhs(concl th) = `val(n:int64)`)) THEN
     ARITH_TAC;
     ALL_TAC]) THEN
  ASM_CASES_TAC
   `lemire_accept (2 EXP 64) (val(s:int64)) (val(EL (k - 1) (l:int64 list)))`
  THENL
   [ACCEPT_TAC;

    SUBGOAL_THEN `k = val(n:int64)` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `k + 0 = val(n:int64)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_VAL] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--2) THEN
    BRANCH_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (3--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `a = 0
      ==> (word 0:int64) = word a /\ (y:int64) = (if a = 0 then y else b)`) THEN
    MATCH_MP_TAC LEMIRE_DRAWS_NONE THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `j < val(n:int64) - 1` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `j = val(n:int64) - 1` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC [`j < val(n:int64)`; `~(j < val(n:int64) - 1)`] THEN
    ARITH_TAC;

    ACCEPT_TAC;

    SUBGOAL_THEN `k < val(n:int64)` ASSUME_TAC THENL
     [UNDISCH_TAC `k + SUC d = val(n:int64)` THEN ARITH_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0xf8`
     `\st. read X0 st = z /\ read X10 st = s /\
           read X11 st = n /\ read X12 st = x /\
           read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
           read (memory :> bytes64 z) st = z0 /\
           read X7 st = word (k + 1) /\
           read X8 st = word(2 EXP 64 MOD val s) /\
           read X5 st = word(val(EL k (l:int64 list)) * val s) /\
           read X6 st = word((val(EL k l) * val s) DIV 2 EXP 64)` THEN
    CONJ_TAC THENL
     [ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes64 (word_add x (word(8 * k)))) s0 =
        EL k (l:int64 list)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC READ_WORDLIST_EL THEN EXISTS_TAC `val(n:int64)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--2) THEN
      BRANCH_TAC THEN
      SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        TRANS_TAC LT_TRANS `val(n:int64)` THEN ASM_REWRITE_TAC[VAL_BOUND_64];
        ALL_TAC] THEN
      ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (3--4) THEN
      TRY(FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
          ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC) THEN
      ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (5--9) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; GSYM WORD_ADD];
      FIRST_X_ASSUM(MP_TAC o SPEC `k + 1` o check (fun th ->
        can (find_term (fun t -> t = `arm`)) (concl th))) THEN
      REWRITE_TAC[ADD_SUB] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ARITH_TAC;
          UNDISCH_TAC `k + SUC d = val(n:int64)` THEN ARITH_TAC;
          X_GEN_TAC `j:num` THEN DISCH_TAC THEN
          ASM_CASES_TAC `j < k - 1` THEN ASM_SIMP_TAC[] THEN
          SUBGOAL_THEN `j = k - 1` (fun th -> ASM_REWRITE_TAC[th]) THEN
          MAP_EVERY UNDISCH_TAC [`j < k`; `~(j < k - 1)`] THEN ARITH_TAC];
        REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the whole function.                                        *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_DIVFREE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x130) (z,8)
    ==> ensures arm
         (\st. aligned_bytes_loaded st (word pc) lemire_random_divfree_mc /\
               read PC st = word pc /\
               C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read PC st = word(pc + 0x12c) /\
               C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                     X10; X11; X12; X13] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes64 z])`,
  let PREFIX_TAC =
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `read (memory :> bytes64 (word_add x (word(8 * 0)))) s0 =
                  EL 0 (l:int64 list)` MP_TAC THENL
     [MATCH_MP_TAC READ_WORDLIST_EL THEN EXISTS_TAC `val(n:int64)` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(val(n:int64) = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--7) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD; DIMINDEX_64;
                                MOD_MOD_REFL]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC in
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `s:int64`; `n:int64`; `x:int64`; `l:int64 list`;
    `z0:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MATCH_MP WORDLIST_FROM_MEMORY_EQ_ALT
   (REWRITE_RULE[GSYM DIMINDEX_64]
     (ARITH_RULE `64 * val(n:int64) = 8 * (8 * val n)`))] THEN
  ASM_CASES_TAC `LENGTH(l:int64 list) = val(n:int64)` THEN
  ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN

  (*** The trivial case n = 0 where there are no words at all ***)

  ASM_CASES_TAC `val(n:int64) = 0` THENL
   [ARM_SIM_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--4) THEN
    REWRITE_TAC[LEMIRE_DRAWS_0];
    ALL_TAC] THEN

  (*** The fast path, accepting x[0] since l >= s ***)

  ASM_CASES_TAC
   `val(s:int64) <= (val(EL 0 (l:int64 list)) * val s) MOD 2 EXP 64` THENL
   [PREFIX_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (8--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2 EXP 64`; `val(s:int64)`; `val(n:int64)`;
                   `\i. val(EL i (l:int64 list))`; `0`]
           LEMIRE_DRAWS_RESULT_FIRST) THEN
    REWRITE_TAC[LT] THEN BETA_TAC THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `~(val(n:int64) = 0)` THEN ARITH_TAC;
        MATCH_MP_TAC LEMIRE_ACCEPT_FAST THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[lemire_output] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** The slow path: compute the threshold and enter the main loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0xf8`
   `\st. read X0 st = z /\ read X10 st = s /\
         read X11 st = n /\ read X12 st = x /\
         read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
         read (memory :> bytes64 z) st = z0 /\
         read X7 st = word 1 /\
         read X8 st = word(2 EXP 64 MOD val s) /\
         read X5 st = word(val(EL 0 (l:int64 list)) * val s) /\
         read X6 st = word((val(EL 0 l) * val s) DIV 2 EXP 64)` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`z:int64`; `s:int64`; `n:int64`; `x:int64`;
                  `l:int64 list`; `z0:int64`; `pc:num`]
      LEMIRE_RANDOM_DIVFREE_SLOW) THEN
    REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`z:int64`; `s:int64`; `n:int64`; `x:int64`;
                  `l:int64 list`; `z0:int64`; `pc:num`;
                  `val(n:int64) - 1`; `1`]
      LEMIRE_RANDOM_DIVFREE_LOOP) THEN
    REWRITE_TAC[SOME_FLAGS; SUB_REFL; LT; LE_REFL; NONOVERLAPPING_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(val(n:int64) = 0)` THEN ARITH_TAC; REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the subroutine.                                            *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_DIVFREE_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc returnaddress.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x130) (z,8)
    ==> ensures arm
         (\st. aligned_bytes_loaded st (word pc) lemire_random_divfree_mc /\
               read PC st = word pc /\
               read X30 st = returnaddress /\
               C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read PC st = returnaddress /\
               C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes64 z])`,
  ARM_ADD_RETURN_NOSTACK_TAC LEMIRE_RANDOM_DIVFREE_EXEC
    LEMIRE_RANDOM_DIVFREE_CORRECT);;

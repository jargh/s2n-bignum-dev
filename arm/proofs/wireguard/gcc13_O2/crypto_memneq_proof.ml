(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of crypto_memneq_spec.ml. With n = val size, the     *)
(* code for n = 16 is straight-line; otherwise a loop over the n DIV 8 words *)
(* (if n >= 8) reaches join1 and a loop over the n MOD 8 remaining bytes (if *)
(* any) the return. The or of the xors, in X0, is the invariant's only       *)
(* abstraction: it is zero exactly when the bytes so far are equal, x MOD    *)
(* 2^b = y MOD 2^b for the b bits compared.                                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_spec.ml";;

let WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "__crypto_memneq"];;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* The bound of the word loop, 8 * (n DIV 8), as the code computes it from   *)
(* n >= 8, and the number of the remaining bytes.                            *)

let MEMNEQ_WORDS_BOUND = prove
 (`!s:int64. word_add (word_and (word_sub s (word 8))
                                (word 18446744073709551608)) (word 8) =
             word(8 * (val s DIV 8))`,
  GEN_TAC THEN
  SUBGOAL_THEN `word_add (word_and (word_sub s (word 8))
                                   (word 18446744073709551608)) (word 8) =
                word_and s (word_not(word(2 EXP 3 - 1))):int64`
  SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `s:int64` VAL_BOUND_64) THEN ARITH_TAC);;

let MEMNEQ_TAIL_LENGTH = prove
 (`!s:int64. word_and s (word 7) = word(val s MOD 8)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`s:int64`; `3`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* The xor of two bytes in the byte loop, as the simulation gives it.        *)

let MEMNEQ_BYTE_XOR = prove
 (`!p q:byte.
     word_and
      ((word_zx:int32->int64)
        (word_xor ((word_zx:int64->int32) ((word_zx:int32->int64)
                     ((word_zx:byte->int32) p)))
                  ((word_zx:int64->int32) ((word_zx:int32->int64)
                     ((word_zx:byte->int32) q)))))
      (word 255) = word 0 <=> p = q`,
  BITBLAST_TAC);;

(* At the end: all the n bytes compared.                                     *)

let MEMNEQ_BOUNDS_TAC =
  SUBGOAL_THEN `x < 2 EXP (8 * val(size:int64)) /\ y < 2 EXP (8 * val size)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN EXPAND_TAC "y" THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The state at join1, and the invariants of the two loops.                  *)
(* ------------------------------------------------------------------------- *)

let memneq_join_tm =
 `\s. read X30 s = returnaddress /\
      read X5 s = word_add a (word(8 * (val(size:int64) DIV 8))) /\
      read X1 s = word_add b (word(8 * (val size DIV 8))) /\
      read X2 s = word(val size MOD 8) /\
      (read X0 s = word 0 <=>
       x MOD 2 EXP (64 * (val size DIV 8)) =
       y MOD 2 EXP (64 * (val size DIV 8))) /\
      read (memory :> bytes(a,val size)) s = x /\
      read (memory :> bytes(b,val size)) s = y`;;

let memneq_loop1_tm =
 `\i s. (read X30 s = returnaddress /\
         read X5 s = a /\ read X1 s = b /\ read X2 s = size /\
         read X7 s = word(8 * (val(size:int64) DIV 8)) /\
         read X3 s = word(8 * i) /\
         (read X0 s = word 0 <=> x MOD 2 EXP (64 * i) = y MOD 2 EXP (64 * i)) /\
         read (memory :> bytes(a,val size)) s = x /\
         read (memory :> bytes(b,val size)) s = y) /\
        (read ZF s <=> i = val size DIV 8)`;;

let memneq_loop2_tm =
 `\j s. (read X30 s = returnaddress /\
         read X5 s = word_add a (word(8 * (val(size:int64) DIV 8))) /\
         read X1 s = word_add b (word(8 * (val size DIV 8))) /\
         read X2 s = word(val size MOD 8) /\
         read X4 s = word j /\
         (read X0 s = word 0 <=>
          x MOD 2 EXP (64 * (val size DIV 8) + 8 * j) =
          y MOD 2 EXP (64 * (val size DIV 8) + 8 * j)) /\
         read (memory :> bytes(a,val size)) s = x /\
         read (memory :> bytes(b,val size)) s = y) /\
        (read ZF s <=> j = val size MOD 8)`;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_EXEC in
  let ls7 = MP (SPECL [`size:int64`; `7`] WG_VAL_LS_COND)
               (ARITH_RULE `7 < 2 EXP 64`)
  and rth = MP (SPEC `val(size:int64) MOD 8` WG_VAL_WORD_SMALL)
               (ARITH_RULE `val(size:int64) MOD 8 < 2 EXP 64`) in
  MAP_EVERY X_GEN_TAC [`a:int64`; `b:int64`; `size:int64`; `x:num`; `y:num`;
                       `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ASM_CASES_TAC `val(size:int64) = 16` THENL
   [(*** The unrolled code for 16 bytes ***)

    SUBGOAL_THEN `size:int64 = word 16` SUBST_ALL_TAC THENL
     [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
      ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV VAL_WORD_NUMERAL_CONV) THEN
    REWRITE_TAC[ARITH_RULE `16 = 8 * 2`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "a_" `read (memory :> bytes (a,8 * 2)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "b_" `read (memory :> bytes (b,8 * 2)) s0` THEN
    ARM_STEPS_TAC EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
    EXPAND_TAC "x" THEN EXPAND_TAC "y" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(size:int64 = word 16)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(val(size:int64) = 16)` THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + __crypto_memneq_join1` memneq_join_tm THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `val(size:int64) <= 7` THENL
     [(*** Fewer than 8 bytes: straight to join1 ***)

      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--3) THEN
      WG_PC_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0;
                        ASSUME `~(size:int64 = word 16)`] THEN
      ARM_STEPS_TAC EXEC (4--6) THEN
      WG_PC_REWRITE_TAC[ls7; ASSUME `val(size:int64) <= 7`] THEN
      SUBGOAL_THEN `val(size:int64) DIV 8 = 0 /\ val size MOD 8 = val size`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[DIV_LT; MOD_LT; ARITH_RULE `n <= 7 ==> n < 8`];
        ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_VAL; EXP; MOD_1];
      ALL_TAC] THEN

    (*** The loop over the words ***)

    ENSURES_WHILE_PUP_TAC `val(size:int64) DIV 8` `pc + __crypto_memneq_loop1`
     `pc + __crypto_memneq_loop1_back` memneq_loop1_tm THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;

      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--3) THEN
      WG_PC_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0;
                        ASSUME `~(size:int64 = word 16)`] THEN
      ARM_STEPS_TAC EXEC (4--6) THEN
      WG_PC_REWRITE_TAC[ls7; ASSUME `~(val(size:int64) <= 7)`] THEN
      ARM_STEPS_TAC EXEC (7--12) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[MEMNEQ_WORDS_BOUND; MULT_CLAUSES; EXP; MOD_1];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `acc:int64` `read X0` THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `8 * i + 8 <= val(size:int64)` ASSUME_TAC THENL
       [UNDISCH_TAC `i < val(size:int64) DIV 8` THEN
        MP_TAC(SPECL [`val(size:int64)`; `8`] DIV_MUL_LE) THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`a:int64`; `val(size:int64)`; `x:num`; `8 * i`;
                    `s0:armstate`] WG_READ_BYTES64_OF_NUM) THEN
      MP_TAC(SPECL [`b:int64`; `val(size:int64)`; `y:num`; `8 * i`;
                    `s0:armstate`] WG_READ_BYTES64_OF_NUM) THEN
      ASM_REWRITE_TAC[ARITH_RULE `8 * 8 * i = 64 * i`] THEN
      REPEAT DISCH_TAC THEN
      ARM_STEPS_TAC EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `8 * i + 8 = 8 * (i + 1)`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0; WG_WORD_EQ_MOD64] THEN
        ASM_REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`;
                        WG_MOD_EXP_ADD_EQ];
        W(MP_TAC o PART_MATCH (lhand o rand) WG_VAL_WORD_SUB_EQ_0 o
          lhand o snd) THEN
        ANTS_TAC THENL
         [MP_TAC(ISPEC `size:int64` VAL_BOUND_64) THEN
          MP_TAC(SPECL [`val(size:int64)`; `8`] DIV_MUL_LE) THEN
          UNDISCH_TAC `8 * i + 8 <= val(size:int64)` THEN ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN ARITH_TAC]];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `acc:int64` `read X0` THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

      GHOST_INTRO_TAC `acc:int64` `read X0` THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MEMNEQ_TAIL_LENGTH]];

    GHOST_INTRO_TAC `acc:int64` `read X0` THEN
    ASM_CASES_TAC `val(size:int64) MOD 8 = 0` THENL
     [(*** No bytes remaining ***)

      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MEMNEQ_BOUNDS_TAC THEN
      SUBGOAL_THEN `64 * val(size:int64) DIV 8 = 8 * val size` SUBST1_TAC THENL
       [MP_TAC(SPECL [`val(size:int64)`; `8`] DIVISION) THEN
        UNDISCH_TAC `val(size:int64) MOD 8 = 0` THEN ARITH_TAC;
        ASM_SIMP_TAC[MOD_LT]];
      ALL_TAC] THEN

    (*** The loop over the remaining bytes ***)

    ENSURES_WHILE_PUP_TAC `val(size:int64) MOD 8` `pc + __crypto_memneq_loop2`
     `pc + __crypto_memneq_loop2_back` memneq_loop2_tm THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];

      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC [1] THEN
      WG_PC_REWRITE_TAC[rth; ASSUME `~(val(size:int64) MOD 8 = 0)`] THEN
      ARM_STEPS_TAC EXEC [2] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `acc:int64` `read X0` THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `8 * val(size:int64) DIV 8 + j < val size` ASSUME_TAC THENL
       [MP_TAC(SPECL [`val(size:int64)`; `8`] DIVISION) THEN
        UNDISCH_TAC `j < val(size:int64) MOD 8` THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`a:int64`; `val(size:int64)`; `x:num`;
                    `8 * val(size:int64) DIV 8 + j`; `s0:armstate`]
        WG_READ_BYTES8_OF_NUM) THEN
      MP_TAC(SPECL [`b:int64`; `val(size:int64)`; `y:num`;
                    `8 * val(size:int64) DIV 8 + j`; `s0:armstate`]
        WG_READ_BYTES8_OF_NUM) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      ARM_STEPS_TAC EXEC (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN CONJ_TAC THENL
       [REWRITE_TAC[WORD_OR_EQ_0; MEMNEQ_BYTE_XOR; WG_WORD_EQ_MOD256] THEN
        ASM_REWRITE_TAC[ARITH_RULE `8 * (8 * k + j) = 64 * k + 8 * j`] THEN
        REWRITE_TAC[ARITH_RULE
         `64 * k + 8 * (j + 1) = (64 * k + 8 * j) + 8`] THEN
        GEN_REWRITE_TAC RAND_CONV [WG_MOD_EXP_ADD_EQ] THEN
        CONV_TAC NUM_REDUCE_CONV;
        W(MP_TAC o PART_MATCH (lhand o rand) WG_VAL_WORD_SUB_EQ_0 o
          lhand o snd) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `j < val(size:int64) MOD 8` THEN ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN REFL_TAC]];

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `acc:int64` `read X0` THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

      GHOST_INTRO_TAC `acc:int64` `read X0` THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MEMNEQ_BOUNDS_TAC THEN
      SUBGOAL_THEN
       `64 * val(size:int64) DIV 8 + 8 * val size MOD 8 = 8 * val size`
      SUBST1_TAC THENL
       [MP_TAC(SPECL [`val(size:int64)`; `8`] DIVISION) THEN ARITH_TAC;
        ASM_SIMP_TAC[MOD_LT]]]]);;

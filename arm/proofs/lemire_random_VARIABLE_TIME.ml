(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemire's "nearly divisionless" uniform random integer below a bound.     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/lemire.ml";;

(**** print_literal_from_elf "arm/random/lemire_random_VARIABLE_TIME.o";;
 ****)

let lemire_random_mc = define_assert_from_elf "lemire_random_mc"
  "arm/random/lemire_random_VARIABLE_TIME.o"
[
  0xb4000262;       (* arm_CBZ X2 (word 76) *)
  0xf9400064;       (* arm_LDR X4 X3 (Immediate_Offset (word 0)) *)
  0x9b017c85;       (* arm_MUL X5 X4 X1 *)
  0x9bc17c86;       (* arm_UMULH X6 X4 X1 *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0xeb0100bf;       (* arm_CMP X5 X1 *)
  0x540001e2;       (* arm_BCS (word 60) *)
  0xcb0103e8;       (* arm_NEG X8 X1 *)
  0x9ac10909;       (* arm_UDIV X9 X8 X1 *)
  0x9b01a128;       (* arm_MSUB X8 X9 X1 X8 *)
  0xeb0800bf;       (* arm_CMP X5 X8 *)
  0x54000142;       (* arm_BCS (word 40) *)
  0xeb0200ff;       (* arm_CMP X7 X2 *)
  0x540000c2;       (* arm_BCS (word 24) *)
  0xf8677864;       (* arm_LDR X4 X3 (Shiftreg_Offset X7 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0x9b017c85;       (* arm_MUL X5 X4 X1 *)
  0x9bc17c86;       (* arm_UMULH X6 X4 X1 *)
  0x17fffff8;       (* arm_B (word 268435424) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0x14000002;       (* arm_B (word 8) *)
  0xf9000006;       (* arm_STR X6 X0 (Immediate_Offset (word 0)) *)
  0xaa0703e0;       (* arm_MOV X0 X7 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let LEMIRE_RANDOM_EXEC = ARM_MK_EXEC_RULE lemire_random_mc;;

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

(*** The threshold is computed as (2^64 - s) - ((2^64 - s) / s) * s ***)

let WORD_MSUB_UDIV = prove
 (`!a d:int64. word_sub a (word_mul (word_udiv a d) d) = word(val a MOD val d)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub a b = c <=> a = word_add b c`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_UDIV;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[DIVISION_SIMP] THEN
  MATCH_MP_TAC(GSYM MOD_LT) THEN REWRITE_TAC[VAL_BOUND_64]);;

let WORD_NEG_MOD_MSUB = prove
 (`!s:int64.
        ~(val s = 0)
        ==> word_sub (word_neg s) (word_mul (word_udiv (word_neg s) s) s) =
            word(2 EXP 64 MOD val s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_MSUB_UDIV] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[VAL_WORD_NEG_CASES; DIMINDEX_64] THEN
  MATCH_MP_TAC(MESON[MOD_MULT_ADD] `N = 1 * s + a ==> a MOD s = N MOD s`) THEN
  MP_TAC(ISPEC `s:int64` VAL_BOUND_64) THEN ARITH_TAC);;
let ARM_THRESHOLD = prove
 (`!s:int64.
        ~(val s = 0)
        ==> iword(ival(word_sub (word 0) s) -
                  ival(word_udiv (word_sub (word 0) s) s) * ival s):int64 =
            word(2 EXP 64 MOD val s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IWORD_INT_SUB; IWORD_INT_MUL; IWORD_IVAL] THEN
  REWRITE_TAC[WORD_SUB_LZERO] THEN ASM_SIMP_TAC[WORD_NEG_MOD_MSUB]);;

(* ------------------------------------------------------------------------- *)
(* The main loop, from the point where x6:x5 = x[k-1] * s and the words     *)
(* x[0],...,x[k-2] have all been rejected, by induction on d = n - k.       *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_LOOP = prove
 (`!z s n x (l:int64 list) z0 pc d k.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x60) (z,8) /\
    LENGTH l = val n /\ 1 <= k /\ k + d = val n /\
    (!j. j < k - 1 ==> ~lemire_accept (2 EXP 64) (val s) (val(EL j l)))
    ==> ensures arm
         (\st. aligned_bytes_loaded st (word pc) lemire_random_mc /\
               read PC st = word(pc + 0x28) /\
               read X0 st = z /\ read X1 st = s /\
               read X2 st = n /\ read X3 st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0 /\
               read X7 st = word k /\
               read X8 st = word(2 EXP 64 MOD val s) /\
               read X5 st = word(val(EL (k - 1) l) * val s) /\
               read X6 st = word((val(EL (k - 1) l) * val s) DIV 2 EXP 64))
         (\st. read PC st = word(pc + 0x5c) /\
               read X0 st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [PC; X0; X4; X5; X6; X7; X8; X9] ,,
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (1--2) THEN
    BRANCH_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (3--4) THEN
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (1--2) THEN
    BRANCH_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (3--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `a = 0 ==> (word 0:int64) = word a /\ (y:int64) = (if a = 0 then y else b)`) THEN
    MATCH_MP_TAC LEMIRE_DRAWS_NONE THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `j < val(n:int64) - 1` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `j = val(n:int64) - 1` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC [`j < val(n:int64)`; `~(j < val(n:int64) - 1)`] THEN
    ARITH_TAC;

    ACCEPT_TAC;

    SUBGOAL_THEN `k < val(n:int64)` ASSUME_TAC THENL
     [UNDISCH_TAC `k + SUC d = val(n:int64)` THEN ARITH_TAC; ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x28`
     `\st. read X0 st = z /\ read X1 st = s /\
           read X2 st = n /\ read X3 st = x /\
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
      ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (1--2) THEN
      BRANCH_TAC THEN
      SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        TRANS_TAC LT_TRANS `val(n:int64)` THEN ASM_REWRITE_TAC[VAL_BOUND_64];
        ALL_TAC] THEN
      ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (3--4) THEN
      TRY(FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
          ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC) THEN
      ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (5--9) THEN
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

let LEMIRE_RANDOM_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x60) (z,8)
    ==> ensures arm
         (\st. aligned_bytes_loaded st (word pc) lemire_random_mc /\
               read PC st = word pc /\
               C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read PC st = word(pc + 0x5c) /\
               C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [PC; X0; X4; X5; X6; X7; X8; X9] ,,
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
    ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (1--7) THEN
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
   [ARM_SIM_TAC LEMIRE_RANDOM_EXEC (1--4) THEN REWRITE_TAC[LEMIRE_DRAWS_0];
    ALL_TAC] THEN

  (*** The fast path, accepting x[0] since l >= s ***)

  ASM_CASES_TAC
   `val(s:int64) <= (val(EL 0 (l:int64 list)) * val s) MOD 2 EXP 64` THENL
   [PREFIX_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (8--9) THEN
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

  ENSURES_SEQUENCE_TAC `pc + 0x28`
   `\st. read X0 st = z /\ read X1 st = s /\
         read X2 st = n /\ read X3 st = x /\
         read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
         read (memory :> bytes64 z) st = z0 /\
         read X7 st = word 1 /\
         read X8 st = word(2 EXP 64 MOD val s) /\
         read X5 st = word(val(EL 0 (l:int64 list)) * val s) /\
         read X6 st = word((val(EL 0 l) * val s) DIV 2 EXP 64)` THEN
  CONJ_TAC THENL
   [PREFIX_TAC THEN
    ARM_STEPS_TAC LEMIRE_RANDOM_EXEC (8--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARM_THRESHOLD];
    MP_TAC(SPECL [`z:int64`; `s:int64`; `n:int64`; `x:int64`;
                  `l:int64 list`; `z0:int64`; `pc:num`;
                  `val(n:int64) - 1`; `1`]
      LEMIRE_RANDOM_LOOP) THEN
    REWRITE_TAC[SOME_FLAGS; SUB_REFL; LT; LE_REFL; NONOVERLAPPING_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(val(n:int64) = 0)` THEN ARITH_TAC; REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the subroutine.                                            *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc returnaddress.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x60) (z,8)
    ==> ensures arm
         (\st. aligned_bytes_loaded st (word pc) lemire_random_mc /\
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
  ARM_ADD_RETURN_NOSTACK_TAC LEMIRE_RANDOM_EXEC LEMIRE_RANDOM_CORRECT);;

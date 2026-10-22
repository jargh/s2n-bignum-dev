(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemire's "nearly divisionless" uniform random integer below a bound.     *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/lemire.ml";;

(**** print_literal_from_elf "x86/random/lemire_random_VARIABLE_TIME.o";;
 ****)

let lemire_random_mc = define_assert_from_elf "lemire_random_mc"
  "x86/random/lemire_random_VARIABLE_TIME.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x85; 0xc0;        (* TEST (% r8) (% r8) *)
  0x74; 0x4d;              (* JE (Imm8 (word 77)) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0xc7; 0xc2; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm32 (word 1)) *)
  0x48; 0x39; 0xf0;        (* CMP (% rax) (% rsi) *)
  0x73; 0x35;              (* JAE (Imm8 (word 53)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x48; 0x89; 0xf0;        (* MOV (% rax) (% rsi) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x48; 0xf7; 0xf6;        (* DIV2 (% rax,% rdx) (% rdx,% rax) (% rsi) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x4c; 0x89; 0xca;        (* MOV (% rdx) (% r9) *)
  0x4c; 0x39; 0xd8;        (* CMP (% rax) (% r11) *)
  0x73; 0x16;              (* JAE (Imm8 (word 22)) *)
  0x4d; 0x39; 0xc2;        (* CMP (% r10) (% r8) *)
  0x73; 0x0d;              (* JAE (Imm8 (word 13)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x49; 0x83; 0xc2; 0x01;  (* ADD (% r10) (Imm8 (word 1)) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0xeb; 0xe9;              (* JMP (Imm8 (word 233)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xeb; 0x06;              (* JMP (Imm8 (word 6)) *)
  0x48; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% rdx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0xc3                     (* RET *)
];;

let lemire_random_tmc = define_trimmed "lemire_random_tmc" lemire_random_mc;;

let LEMIRE_RANDOM_EXEC = X86_MK_CORE_EXEC_RULE lemire_random_tmc;;

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
  MP_TAC(ISPECL [`x:int64`; `LENGTH(l:int64 list)`; `k:num`; `s:x86state`]
    (INST_TYPE [`:8`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY; DIMINDEX_8] THEN
  REWRITE_TAC[WORDLIST_OF_NUM_OF_WORDLIST] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[bytes64; wbytes; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let MUL_WORD_PARTS = prove
 (`!(a:int64) (s:int64).
     word_zx (word (val a * val s):int128):int64 =
     word((val a * val s) MOD 2 EXP 64) /\
     word_zx (word_ushr (word (val a * val s):int128) 64):int64 =
     word((val a * val s) DIV 2 EXP 64)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `val(a:int64) * val(s:int64) < 2 EXP 128` ASSUME_TAC THENL
   [MP_TAC(ISPEC `a:int64` VAL_BOUND_64) THEN
    MP_TAC(ISPEC `s:int64` VAL_BOUND_64) THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 128 = 2 EXP 64 * 2 EXP 64`] THEN
    MESON_TAC[LT_MULT2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD;
              DIMINDEX_64; DIMINDEX_128] THEN
  ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL]);;

(*** The forms needed so the simulator sees the DIV cannot raise #DE ***)

let DIV_NODE_FACTS = prove
 (`!s:int64. ~(val s = 0)
      ==> ~(2 EXP 64 <= (2 EXP 64 * 0 + val(word_neg s:int64)) DIV val s) /\
          ~(18446744073709551616 <= (0 + val(word_neg s:int64)) DIV val s) /\
          ~(18446744073709551616 <= val(word_neg s:int64) DIV val s) /\
          ~(2 EXP 64 <= val(word_neg s:int64) DIV val s)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NOT_LE] THEN
  TRANS_TAC LET_TRANS `val(word_neg s:int64)` THEN REWRITE_TAC[DIV_LE] THEN
  MP_TAC(ISPEC `word_neg s:int64` VAL_BOUND_64) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** The computed threshold (2^64 - s) mod s is indeed 2^64 mod s ***)

let VAL_WORD_NEG_MOD = prove
 (`!s:int64. ~(val s = 0)
             ==> (0 + val(word_neg s)) MOD val s = 2 EXP 64 MOD val s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; VAL_WORD_NEG_CASES; DIMINDEX_64] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[MOD_MULT_ADD] `N = 1 * s + a ==> a MOD s = N MOD s`) THEN
  MP_TAC(ISPEC `s:int64` VAL_BOUND_64) THEN ARITH_TAC);;

let VAL_WORD_THRESHOLD = prove
 (`!s:int64. ~(val s = 0)
             ==> val(word(2 EXP 64 MOD val s):int64) = 2 EXP 64 MOD val s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `val(s:int64)` THEN
  ASM_SIMP_TAC[MOD_LT_EQ; LT_IMP_LE; VAL_BOUND_64]);;

(* ------------------------------------------------------------------------- *)
(* The main loop, from the point where rdx:rax = x[k-1] * s and the words   *)
(* x[0],...,x[k-2] have all been rejected, by induction on d = n - k.       *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_LOOP = prove
 (`!z s n x (l:int64 list) z0 pc d k.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x58) (z,8) /\
    LENGTH l = val n /\ 1 <= k /\ k + d = val n /\
    (!j. j < k - 1 ==> ~lemire_accept (2 EXP 64) (val s) (val(EL j l)))
    ==> ensures x86
         (\st. bytes_loaded st (word pc) (BUTLAST lemire_random_tmc) /\
               read RIP st = word(pc + 0x36) /\
               read RDI st = z /\ read RSI st = s /\
               read R8 st = n /\ read RCX st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0 /\
               read R10 st = word k /\
               read R11 st = word(2 EXP 64 MOD val s) /\
               read RAX st = word((val(EL (k - 1) l) * val s) MOD 2 EXP 64) /\
               read RDX st = word((val(EL (k - 1) l) * val s) DIV 2 EXP 64))
         (\st. read RIP st = word(pc + 0x57) /\
               read RAX st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RIP; RAX; RDX; R8; R9; R10; R11] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes64 z])`,
  let BRANCH_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE
     [MATCH_MP VAL_WORD_THRESHOLD (ASSUME `~(val(s:int64) = 0)`);
      VAL_WORD; DIMINDEX_64; MOD_MOD_REFL; GSYM lemire_accept]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC in
  let ACCEPT_TAC =
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC LEMIRE_RANDOM_EXEC (1--2) THEN
    BRANCH_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_EXEC (3--4) THEN
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
  (SUBGOAL_THEN `k - 1 < val(n:int64) /\ k - 1 + 1 = k /\ ~(k = 0)`
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
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC LEMIRE_RANDOM_EXEC (1--2) THEN
    BRANCH_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_EXEC (3--6) THEN
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
    ENSURES_SEQUENCE_TAC `pc + 0x36`
     `\st. read RDI st = z /\ read RSI st = s /\
           read R8 st = n /\ read RCX st = x /\
           read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
           read (memory :> bytes64 z) st = z0 /\
           read R10 st = word (k + 1) /\
           read R11 st = word(2 EXP 64 MOD val s) /\
           read RAX st =
           word((val(EL k (l:int64 list)) * val s) MOD 2 EXP 64) /\
           read RDX st = word((val(EL k l) * val s) DIV 2 EXP 64)` THEN
    CONJ_TAC THENL
     [ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes64 (word_add x (word(8 * k)))) s0 =
        EL k (l:int64 list)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC READ_WORDLIST_EL THEN EXISTS_TAC `val(n:int64)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X86_STEPS_TAC LEMIRE_RANDOM_EXEC (1--2) THEN
      BRANCH_TAC THEN
      SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        TRANS_TAC LT_TRANS `val(n:int64)` THEN ASM_REWRITE_TAC[VAL_BOUND_64];
        ALL_TAC] THEN
      X86_STEPS_TAC LEMIRE_RANDOM_EXEC (3--4) THEN
      TRY(FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
          ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC) THEN
      X86_STEPS_TAC LEMIRE_RANDOM_EXEC (5--8) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MUL_WORD_PARTS; GSYM WORD_ADD];
      FIRST_X_ASSUM(MP_TAC o SPEC `k + 1` o check (fun th ->
        can (find_term (fun t -> t = `x86`)) (concl th))) THEN
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
(* Correctness of the core.                                                  *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x58) (z,8)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) (BUTLAST lemire_random_tmc) /\
               read RIP st = word pc /\
               C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read RIP st = word(pc + 0x57) /\
               C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RIP; RAX; RDX; R8; R9; R10; R11] ,,
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
    X86_STEPS_TAC LEMIRE_RANDOM_EXEC (1--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MUL_WORD_PARTS; VAL_WORD; DIMINDEX_64;
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
   [X86_SIM_TAC LEMIRE_RANDOM_EXEC (1--4) THEN REWRITE_TAC[LEMIRE_DRAWS_0];
    ALL_TAC] THEN

  (*** The fast path, accepting x[0] since l >= s ***)

  ASM_CASES_TAC
   `val(s:int64) <= (val(EL 0 (l:int64 list)) * val s) MOD 2 EXP 64` THENL
   [PREFIX_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_EXEC (10--11) THEN
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

  ENSURES_SEQUENCE_TAC `pc + 0x36`
   `\st. read RDI st = z /\ read RSI st = s /\
         read R8 st = n /\ read RCX st = x /\
         read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
         read (memory :> bytes64 z) st = z0 /\
         read R10 st = word 1 /\
         read R11 st = word(2 EXP 64 MOD val s) /\
         read RAX st = word((val(EL 0 (l:int64 list)) * val s) MOD 2 EXP 64) /\
         read RDX st = word((val(EL 0 l) * val s) DIV 2 EXP 64)` THEN
  CONJ_TAC THENL
   [PREFIX_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_EXEC (10--14) THEN
    MP_TAC(SPEC `s:int64` DIV_NODE_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_EXEC (15--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[VAL_WORD_NEG_MOD];
    MP_TAC(SPECL [`z:int64`; `s:int64`; `n:int64`; `x:int64`;
                  `l:int64 list`; `z0:int64`; `pc:num`;
                  `val(n:int64) - 1`; `1`]
      LEMIRE_RANDOM_LOOP) THEN
    REWRITE_TAC[SOME_FLAGS; SUB_REFL; LT; LE_REFL; NONOVERLAPPING_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(val(n:int64) = 0)` THEN ARITH_TAC; REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the subroutine, with and without IBT.                     *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    nonoverlapping (word pc,LENGTH lemire_random_tmc) (z,8) /\
    nonoverlapping (z,8) (stackpointer,8)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_tmc /\
               read RIP st = word pc /\
               read RSP st = stackpointer /\
               read (memory :> bytes64 stackpointer) st = returnaddress /\
               C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read RIP st = returnaddress /\
               read RSP st = word_add stackpointer (word 8) /\
               C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes64 z])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC lemire_random_tmc LEMIRE_RANDOM_CORRECT);;

let LEMIRE_RANDOM_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    nonoverlapping (word pc,LENGTH lemire_random_mc) (z,8) /\
    nonoverlapping (z,8) (stackpointer,8)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_mc /\
               read RIP st = word pc /\
               read RSP st = stackpointer /\
               read (memory :> bytes64 stackpointer) st = returnaddress /\
               C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read RIP st = returnaddress /\
               read RSP st = word_add stackpointer (word 8) /\
               C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes64 z])`,
  let TWEAK_CONV = REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV LEMIRE_RANDOM_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let lemire_random_windows_mc = define_from_elf "lemire_random_windows_mc"
      "x86/random/lemire_random_VARIABLE_TIME.obj";;

let lemire_random_windows_tmc =
  define_trimmed "lemire_random_windows_tmc" lemire_random_windows_mc;;

let LEMIRE_RANDOM_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [(word pc,LENGTH lemire_random_windows_tmc); (x,8 * val n)] /\
    nonoverlapping (word pc,LENGTH lemire_random_windows_tmc) (z,8) /\
    nonoverlapping (z,8) (word_sub stackpointer (word 16),24)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_windows_tmc /\
               read RIP st = word pc /\
               read RSP st = stackpointer /\
               read (memory :> bytes64 stackpointer) st = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read RIP st = returnaddress /\
               read RSP st = word_add stackpointer (word 8) /\
               WINDOWS_C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes64 z] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  let TWEAK_CONV =
    REWRITE_CONV[wordlist_from_memory] THENC
    TOP_DEPTH_CONV DIMINDEX_CONV THENC
    REWRITE_CONV[ARITH_RULE `(64 * n + 7) DIV 8 = 8 * n`] in
  CONV_TAC TWEAK_CONV THEN
  WINDOWS_X86_WRAP_NOSTACK_TAC lemire_random_windows_tmc lemire_random_tmc
    (CONV_RULE TWEAK_CONV LEMIRE_RANDOM_CORRECT));;

let LEMIRE_RANDOM_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [(word pc,LENGTH lemire_random_windows_mc); (x,8 * val n)] /\
    nonoverlapping (word pc,LENGTH lemire_random_windows_mc) (z,8) /\
    nonoverlapping (z,8) (word_sub stackpointer (word 16),24)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_windows_mc /\
               read RIP st = word pc /\
               read RSP st = stackpointer /\
               read (memory :> bytes64 stackpointer) st = returnaddress /\
               WINDOWS_C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read RIP st = returnaddress /\
               read RSP st = word_add stackpointer (word 8) /\
               WINDOWS_C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes64 z] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  let TWEAK_CONV = REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV LEMIRE_RANDOM_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional addition of bignums.                                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_optadd.o";;
 ****)

let bignum_optadd_mc =
  define_assert_from_elf "bignum_optadd_mc" "x86/generic/bignum_optadd.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x2c;              (* JE (Imm8 (word 44)) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4e; 0x8b; 0x1c; 0xca;  (* MOV (% r11) (Memop Quadword (%%% (rdx,3,r9))) *)
  0x4f; 0x8b; 0x14; 0xc8;  (* MOV (% r10) (Memop Quadword (%%% (r8,3,r9))) *)
  0x49; 0x21; 0xca;        (* AND (% r10) (% rcx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x4d; 0x11; 0xd3;        (* ADC (% r11) (% r10) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x4e; 0x89; 0x1c; 0xce;  (* MOV (Memop Quadword (%%% (rsi,3,r9))) (% r11) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xe0;              (* JB (Imm8 (word 224)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0xc3                     (* RET *)
];;

let bignum_optadd_tmc = define_trimmed "bignum_optadd_tmc" bignum_optadd_mc;;

let BIGNUM_OPTADD_EXEC = X86_MK_CORE_EXEC_RULE bignum_optadd_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTADD_CORRECT = prove
 (`!k z x p y a b pc.
        nonoverlapping (word pc,0x35) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_optadd_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read RIP s = word(pc + 0x34) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (a + bitval(~(p = word 0)) * b) (val k) /\
                  C_RETURN s =
                  word(highdigits (a + bitval(~(p = word 0)) * b) (val k)))
             (MAYCHANGE [RIP; RAX; RCX; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `p:int64`; `y:int64`;
    `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`] THEN

  (*** The trivial k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN RULE_ASSUM_TAC
    (REWRITE_RULE[ARITH_RULE `a < 2 EXP (64 * 0) <=> a = 0`]) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTADD_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Main loop setup ***)

  ABBREV_TAC `m <=> ~(p:int64 = word 0)` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x11` `pc + 0x2c`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read RDX s = x /\
          read RCX s = word_neg(word(bitval m)) /\
          read R8 s = y /\
          read R9 s = word i /\
          bignum_from_memory (word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          bignum_from_memory (word_add y (word(8 * i)),k - i) s =
          highdigits b i /\
          val(word_neg(read RAX s)) <= 1 /\
          2 EXP (64 * i) * val(word_neg(read RAX s)) +
          bignum_from_memory(z,i) s =
          lowdigits a i + bitval m * lowdigits b i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTADD_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; ADD_CLAUSES; MULT_CLAUSES;
                WORD_NEG_0; VAL_WORD_0; SUB_0; BITVAL_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; LE_0];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTADD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `cin:int64` `read RAX` THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_OPTADD_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_THEN
     `2 EXP (64 * k) * val(word_neg cin:int64) +
      read (memory :> bytes (z,8 * k)) s3 =
      lowdigits a k + bitval m * lowdigits b k`
     (fun th -> MP_TAC(CONJ (AP_TERM `\x. lowdigits x k` th)
                            (AP_TERM `\x. highdigits x k` th))) THEN
    SIMP_TAC[lowdigits; highdigits; MOD_MULT_ADD; DIV_MULT_ADD;
             EXP_EQ_0; ARITH_EQ; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
    SIMP_TAC[VAL_WORD_GALOIS]] THEN

  (*** Proof of the main invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  GHOST_INTRO_TAC `cinn:num` `\s. val(word_neg(read RAX s))` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN
  REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC BIGNUM_OPTADD_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
  REWRITE_TAC[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0] THEN
  REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
  REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
   `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0; MULT_CLAUSES] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN ARITH_TAC);;

let BIGNUM_OPTADD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z x p y a b pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_optadd_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optadd_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (a + bitval(~(p = word 0)) * b) (val k) /\
                  C_RETURN s =
                  word(highdigits (a + bitval(~(p = word 0)) * b) (val k)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_optadd_tmc BIGNUM_OPTADD_CORRECT);;

let BIGNUM_OPTADD_SUBROUTINE_CORRECT = prove
 (`!k z x p y a b pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_optadd_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optadd_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (a + bitval(~(p = word 0)) * b) (val k) /\
                  C_RETURN s =
                  word(highdigits (a + bitval(~(p = word 0)) * b) (val k)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTADD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_optadd_windows_mc = define_from_elf
   "bignum_optadd_windows_mc" "x86/generic/bignum_optadd.obj";;

let bignum_optadd_windows_tmc = define_trimmed "bignum_optadd_windows_tmc" bignum_optadd_windows_mc;;

let BIGNUM_OPTADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x p y a b pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optadd_windows_tmc); (x,8 * val k); (y,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_optadd_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optadd_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (a + bitval(~(p = word 0)) * b) (val k) /\
                  WINDOWS_C_RETURN s =
                  word(highdigits (a + bitval(~(p = word 0)) * b) (val k)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_optadd_windows_tmc bignum_optadd_tmc
    BIGNUM_OPTADD_CORRECT);;

let BIGNUM_OPTADD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x p y a b pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optadd_windows_mc); (x,8 * val k); (y,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_optadd_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optadd_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;p;y] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory(z,val k) s =
                  lowdigits (a + bitval(~(p = word 0)) * b) (val k) /\
                  WINDOWS_C_RETURN s =
                  word(highdigits (a + bitval(~(p = word 0)) * b) (val k)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_optadd" subroutine_signatures)
    BIGNUM_OPTADD_CORRECT
    BIGNUM_OPTADD_EXEC;;

(* Containment of a word-indexed memory access buf[m] (8 bytes) within
   [buf, n * 8] when m < n.  Used for the loads x[i], y[i] and the store z[i]
   in the main loop. *)
let OPTADD_CONTAINED = prove
 (`!(a:int64) (n:num) (m:num).
      m < n /\ n < 2 EXP 64
      ==> contained_modulo (2 EXP 64)
            (val(word_add a (word(8 * m))),8) (val a, n * 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[contained_modulo] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN EXISTS_TAC `8 * m + d` THEN
  CONJ_TAC THENL
   [ ASM_ARITH_TAC;
     REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[CONG] THEN
     CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC ]);;

(* Recursive backtracking discharge of one memaccess containment leaf:
   close it directly via OPTADD_CONTAINED, or descend into whichever
   disjunct of the (multi-buffer) read/write range matches. *)
let rec OPTADD_CONTAIN_TAC g =
  (FIRST [ MATCH_MP_TAC OPTADD_CONTAINED THEN CONJ_TAC THEN SIMPLE_ARITH_TAC;
           DISJ1_TAC THEN OPTADD_CONTAIN_TAC;
           DISJ2_TAC THEN OPTADD_CONTAIN_TAC ]) g;;

let BIGNUM_OPTADD_SAFE = prove
 (`exists f_events.
       forall e k z x p y pc.
           nonoverlapping (word pc,53) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
           (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST bignum_optadd_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [k; z; x; p; y] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 52) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y z k pc /\
                         memaccess_inbounds e2
                         [x,val k * 8; y,val k * 8; z,val k * 8]
                         [z,val k * 8]))
               (MAYCHANGE [RIP; RAX; RCX; R9; R10; R11] ,,
                MAYCHANGE SOME_FLAGS ,,
                MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (z:int64) (k:int64) (pc:num). if val k = 0 then f_ev_k0 x y z k pc
      else APPEND (f_ev_post x y z k pc) (APPEND (ENUMERATEL (val k) (f_ev_loop x y z k pc)) (f_ev_pre x y z k pc)):(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `k:num` THEN MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `p:int64`; `y:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `k = 0` THENL
   [ ASM_REWRITE_TAC[] THEN X86_SIM_TAC BIGNUM_OPTADD_EXEC (1--3) THEN DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  ASM_REWRITE_TAC[ASSUME `val(word k:int64) = k`] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x11` `pc + 0x31`
   `\i s. read RDI s = word k /\ read RSI s = z /\ read RDX s = x /\ read R8 s = y /\ read R9 s = word i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ X86_SIM_TAC BIGNUM_OPTADD_EXEC (1--6) THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
     ALL_TAC;
     ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN X86_STEPS_TAC BIGNUM_OPTADD_EXEC (1--1) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC ] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC BIGNUM_OPTADD_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_add (word i) (word 1):int64 = word(i+1)` ASSUME_TAC THENL [ CONV_TAC WORD_RULE; ALL_TAC ] THEN
  SUBGOAL_THEN `val(word(i+1):int64) = i + 1` ASSUME_TAC THENL
   [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(val(word (i+1):int64) < k) <=> i + 1 < k` SUBST1_TAC THENL
   [ IMP_REWRITE_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `i < k` ASSUME_TAC THENL [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  W (fun (asl,w) -> (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ]) else ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THEN
  ((REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN REPEAT CONJ_TAC THEN OPTADD_CONTAIN_TAC)
   ORELSE
   (FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhs(concl th)) && name_of(lhs(concl th))="e2"
                            then MP_TAC(CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV BETA_CONV)) th) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `k:num` && (is_comb(lhs(concl th)) && name_of(rator(lhs(concl th)))="val")
                          then REWRITE_TAC[th] else NO_TAC) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC)));;

(* Has no "word_sub stackpointer (word ..)"; stackofs is None *)
let BIGNUM_OPTADD_NOIBT_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x p y pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_optadd_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_optadd_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [k; z; x; p; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z k pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; z,val k * 8; stackpointer,8]
                      [z,val k * 8; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_optadd_tmc BIGNUM_OPTADD_SAFE THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_OPTADD_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x p y pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_optadd_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_optadd_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [k; z; x; p; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z k pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; z,val k * 8; stackpointer,8]
                      [z,val k * 8; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTADD_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OPTADD_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x p y pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_optadd_windows_tmc; x,8 * val k; y,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_optadd_windows_tmc)
        (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_optadd_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [k; z; x; p; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x y z k pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; z,val k * 8;
                       word_add stackpointer (word 40),8;
                       word_sub stackpointer (word 16),24]
                      [z,val k * 8; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,val k);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_optadd_windows_tmc bignum_optadd_tmc BIGNUM_OPTADD_SAFE THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_OPTADD_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x p y pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_optadd_windows_mc; x,8 * val k; y,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_optadd_windows_mc)
        (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_optadd_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [k; z; x; p; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x y z k pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; z,val k * 8;
                       word_add stackpointer (word 40),8;
                       word_sub stackpointer (word 16),24]
                      [z,val k * 8; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,val k);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTADD_NOIBT_WINDOWS_SUBROUTINE_SAFE));;

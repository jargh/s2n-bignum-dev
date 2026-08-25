(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplexing for raw bignums with same length.                            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_mux.o";;
 ****)

let bignum_mux_mc =
  define_assert_from_elf "bignum_mux_mc" "x86/generic/bignum_mux.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x74; 0x1e;              (* JE (Imm8 (word 30)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0xf7; 0xdf;        (* NEG (% rdi) *)
  0x4a; 0x8b; 0x04; 0xc9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r9))) *)
  0x4b; 0x8b; 0x3c; 0xc8;  (* MOV (% rdi) (Memop Quadword (%%% (r8,3,r9))) *)
  0x48; 0x0f; 0x43; 0xc7;  (* CMOVAE (% rax) (% rdi) *)
  0x4a; 0x89; 0x04; 0xca;  (* MOV (Memop Quadword (%%% (rdx,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x75; 0xe8;              (* JNE (Imm8 (word 232)) *)
  0xc3                     (* RET *)
];;

let bignum_mux_tmc = define_trimmed "bignum_mux_tmc" bignum_mux_mc;;

let BIGNUM_MUX_EXEC = X86_MK_CORE_EXEC_RULE bignum_mux_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX_CORRECT = prove
 (`!b k x y z m n pc.
     nonoverlapping (word pc,0x24) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mux_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read RIP s =
                word (pc + 0x23) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [RIP; RAX; RDI; RSI; R9] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,val k)] ,, MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_MUX_EXEC] THEN
  MAP_EVERY W64_GEN_TAC [`b:num`; `k:num`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_RANGE_TAC "k") ["m"; "n"] THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; COND_ID] THEN
    X86_SIM_TAC BIGNUM_MUX_EXEC (1--2);
    ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0xb` `pc + 0x21`
   `\i s. (read RCX s = x /\
           read R8 s = y /\
           read RDX s = z /\
           (read CF s <=> ~(b = 0)) /\
           read RSI s = word(k - i) /\
           read R9 s = word i /\
           bignum_from_memory(z,i) s = lowdigits (if b = 0 then n else m) i /\
           bignum_from_memory(word_add x (word(8 * i)),k - i) s =
           highdigits m i /\
           bignum_from_memory(word_add y (word(8 * i)),k - i) s =
           highdigits n i) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_MUX_EXEC (1--4) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; LOWDIGITS_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; HIGHDIGITS_0] THEN
    ASM_REWRITE_TAC[WORD_ADD_0; BIGNUM_FROM_MEMORY_BYTES; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC BIGNUM_MUX_EXEC (1--6) THEN
    ASM_SIMP_TAC[WORD_SUB; VAL_WORD_SUB_CASES; LT_IMP_LE; VAL_WORD_1;
                 ARITH_RULE `i < k ==> i + 1 <= k`] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      CONV_TAC WORD_RULE;
      ALL_TAC;
      UNDISCH_TAC `i:num < k` THEN ARITH_TAC] THEN
    ASM_CASES_TAC `b = 0` THEN
    ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; VAL_WORD_BIGDIGIT] THEN ARITH_TAC;

    REPEAT STRIP_TAC THEN X86_SIM_TAC BIGNUM_MUX_EXEC [1];

    X86_SIM_TAC BIGNUM_MUX_EXEC [1] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF]]);;

let BIGNUM_MUX_NOIBT_SUBROUTINE_CORRECT = prove
 (`!b k x y z m n pc stackpointer returnaddress.
     nonoverlapping (word pc,LENGTH bignum_mux_tmc) (z,8 * val k) /\
     nonoverlapping (stackpointer,8) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mux_tmc BIGNUM_MUX_CORRECT);;

let BIGNUM_MUX_SUBROUTINE_CORRECT = prove
 (`!b k x y z m n pc stackpointer returnaddress.
     nonoverlapping (word pc,LENGTH bignum_mux_mc) (z,8 * val k) /\
     nonoverlapping (stackpointer,8) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUX_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mux_windows_mc = define_from_elf
   "bignum_mux_windows_mc" "x86/generic/bignum_mux.obj";;

let bignum_mux_windows_tmc = define_trimmed "bignum_mux_windows_tmc" bignum_mux_windows_mc;;

let BIGNUM_MUX_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!b k x y z m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mux_windows_tmc); (x,8 * val k); (y,8 * val k)] /\
     nonoverlapping (word pc,LENGTH bignum_mux_windows_tmc) (z,8 * val k) /\
     nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_mux_windows_tmc bignum_mux_tmc
    BIGNUM_MUX_CORRECT);;

let BIGNUM_MUX_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!b k x y z m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mux_windows_mc); (x,8 * val k); (y,8 * val k)] /\
     nonoverlapping (word pc,LENGTH bignum_mux_windows_mc) (z,8 * val k) /\
     nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
     (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
     ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mux_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [b; k; z; x; y] s /\
                bignum_from_memory (x,val k) s = m /\
                bignum_from_memory (y,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s =
                  if ~(b = word 0) then m else n)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUX_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_mux" subroutine_signatures)
    BIGNUM_MUX_CORRECT
    BIGNUM_MUX_EXEC;;

(* Containment of a word-indexed memory access buf[m] (8 bytes) within
   [buf, n * 8] when m < n.  Used for the loads x[i], y[i] and the store z[i]. *)
let MUX_CONTAINED = prove
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

let rec MUX_CONTAIN_TAC g =
  (FIRST [ MATCH_MP_TAC MUX_CONTAINED THEN CONJ_TAC THEN SIMPLE_ARITH_TAC;
           DISJ1_TAC THEN MUX_CONTAIN_TAC; DISJ2_TAC THEN MUX_CONTAIN_TAC ]) g;;

let BIGNUM_MUX_SAFE = prove
 (`exists f_events.
       forall e b k x y z pc.
           nonoverlapping (word pc,36) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
           (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST bignum_mux_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [b; k; z; x; y] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 35) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y z k pc /\
                         memaccess_inbounds e2
                         [x,val k * 8; y,val k * 8; z,val k * 8]
                         [z,val k * 8]))
               (MAYCHANGE [RIP; RAX; RDI; RSI; R9] ,,
                MAYCHANGE SOME_FLAGS ,,
                MAYCHANGE [memory :> bignum (z,val k)] ,,
                MAYCHANGE [events])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (z:int64) (k:int64) (pc:num). if val k = 0 then f_ev_k0 x y z k pc
      else APPEND (f_ev_post x y z k pc) (APPEND (ENUMERATEL (val k) (f_ev_loop x y z k pc)) (f_ev_pre x y z k pc)):(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `b:int64` THEN W64_GEN_TAC `k:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `y:int64`; `z:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `k = 0` THENL
   [ ASM_REWRITE_TAC[] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MUX_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `~(val(word k:int64) = 0)` ASSUME_TAC THENL [ ASM_REWRITE_TAC[]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[ASSUME `val(word k:int64) = k`] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0xb` `pc + 0x23`
   `\i s. read RCX s = x /\ read R8 s = y /\ read RDX s = z /\ read RSI s = word(k - i) /\ read R9 s = word i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MUX_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
     ALL_TAC;
     ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     DISCHARGE_SAFETY_PROPERTY_TAC ] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC BIGNUM_MUX_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word(k - i):int64) = k - i` ASSUME_TAC THENL
   [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `word_add (word i) (word 1):int64 = word(i+1)` ASSUME_TAC THENL [ CONV_TAC WORD_RULE; ALL_TAC ] THEN
  SUBGOAL_THEN `val(word(i+1):int64) = i + 1` ASSUME_TAC THENL
   [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `word_sub (word(k - i)) (word 1):int64 = word(k - (i+1))` SUBST_ALL_TAC THENL
   [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(~(val(word(k - (i+1)):int64) = 0)) <=> i + 1 < k` SUBST1_TAC THENL
   [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  SUBGOAL_THEN `i < k` ASSUME_TAC THENL [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
  CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  W (fun (asl,w) -> (if is_conj w then (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ]) else ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THEN
  ((REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN REPEAT CONJ_TAC THEN MUX_CONTAIN_TAC)
   ORELSE
   (FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhs(concl th)) && name_of(lhs(concl th))="e2"
                            then MP_TAC(CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV BETA_CONV)) th) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `k:num` && (is_comb(lhs(concl th)) && name_of(rator(lhs(concl th)))="val")
                          then REWRITE_TAC[th] else NO_TAC) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC)));;

(* Has no "word_sub stackpointer (word ..)"; stackofs is None *)
let BIGNUM_MUX_NOIBT_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e b k x y z pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_mux_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mux_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [b; k; z; x; y] s /\
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
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mux_tmc BIGNUM_MUX_SAFE THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MUX_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e b k x y z pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_mux_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mux_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [b; k; z; x; y] s /\
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
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUX_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e b k x y z pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_mux_windows_tmc; x,8 * val k; y,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_mux_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mux_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [b; k; z; x; y] s /\
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
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_mux_windows_tmc bignum_mux_tmc BIGNUM_MUX_SAFE THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MUX_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e b k x y z pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_mux_windows_mc; x,8 * val k; y,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_mux_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mux_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [b; k; z; x; y] s /\
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
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MUX_NOIBT_WINDOWS_SUBROUTINE_SAFE));;

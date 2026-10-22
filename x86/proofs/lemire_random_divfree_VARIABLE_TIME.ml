(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemire's uniform random integer below a bound, threshold without DIV.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/word_recip.ml";;
needs "common/lemire.ml";;

(**** print_literal_from_elf "x86/random/lemire_random_divfree_VARIABLE_TIME.o";;
 ****)

let lemire_random_divfree_mc = define_assert_from_elf
  "lemire_random_divfree_mc" "x86/random/lemire_random_divfree_VARIABLE_TIME.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x85; 0xc0;        (* TEST (% r8) (% r8) *)
  0x0f; 0x84; 0x49; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 329)) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0xc7; 0xc2; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm32 (word 1)) *)
  0x48; 0x39; 0xf0;        (* CMP (% rax) (% rsi) *)
  0x0f; 0x83; 0x2d; 0x01; 0x00; 0x00;
                           (* JAE (Imm32 (word 301)) *)
  0x49; 0x89; 0xc9;        (* MOV (% r9) (% rcx) *)
  0x49; 0x89; 0xfa;        (* MOV (% r10) (% rdi) *)
  0x49; 0x89; 0xf3;        (* MOV (% r11) (% rsi) *)
  0x48; 0x0f; 0xbd; 0xce;  (* BSR (% rcx) (% rsi) *)
  0x48; 0x83; 0xf1; 0x3f;  (* XOR (% rcx) (Imm8 (word 63)) *)
  0x48; 0x89; 0xf7;        (* MOV (% rdi) (% rsi) *)
  0x48; 0xd3; 0xe7;        (* SHL (% rdi) (% cl) *)
  0x48; 0x89; 0xfe;        (* MOV (% rsi) (% rdi) *)
  0x48; 0xb9; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x01; 0x00;
                           (* MOV (% rcx) (Imm64 (word 562949953421311)) *)
  0x48; 0xc1; 0xee; 0x10;  (* SHR (% rsi) (Imm8 (word 16)) *)
  0x48; 0x31; 0xf1;        (* XOR (% rcx) (% rsi) *)
  0x48; 0xff; 0xc6;        (* INC (% rsi) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xf2;        (* MOV (% rdx) (% rsi) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x31;  (* SHR (% rax) (Imm8 (word 49)) *)
  0x48; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% rax) *)
  0x48; 0xc1; 0xea; 0x22;  (* SHR (% rdx) (Imm8 (word 34)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x48; 0x0d; 0x00; 0x00; 0x00; 0x40;
                           (* OR (% rax) (Imm32 (word 1073741824)) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x1e;  (* SHR (% rax) (Imm8 (word 30)) *)
  0x48; 0x0f; 0xaf; 0xc1;  (* IMUL (% rax) (% rcx) *)
  0x48; 0xc1; 0xe1; 0x1e;  (* SHL (% rcx) (Imm8 (word 30)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0xc1; 0xe9; 0x1e;  (* SHR (% rcx) (Imm8 (word 30)) *)
  0x48; 0x89; 0xf2;        (* MOV (% rdx) (% rsi) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0xc1; 0xea; 0x18;  (* SHR (% rdx) (Imm8 (word 24)) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xc1; 0xe1; 0x10;  (* SHL (% rcx) (Imm8 (word 16)) *)
  0x48; 0xc1; 0xea; 0x18;  (* SHR (% rdx) (Imm8 (word 24)) *)
  0x48; 0x01; 0xd1;        (* ADD (% rcx) (% rdx) *)
  0x48; 0x89; 0xf2;        (* MOV (% rdx) (% rsi) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0xc1; 0xea; 0x20;  (* SHR (% rdx) (Imm8 (word 32)) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xc1; 0xe1; 0x1f;  (* SHL (% rcx) (Imm8 (word 31)) *)
  0x48; 0xc1; 0xea; 0x11;  (* SHR (% rdx) (Imm8 (word 17)) *)
  0x48; 0x01; 0xd1;        (* ADD (% rcx) (% rdx) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x0f; 0xac; 0xd0; 0x3c;
                           (* SHRD (% rax) (% rdx) (Imm8 (word 60)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x48; 0xc1; 0xea; 0x21;  (* SHR (% rdx) (Imm8 (word 33)) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0xd1; 0xe1;        (* SHL (% rcx) (Imm8 (word 1)) *)
  0x48; 0xc1; 0xe8; 0x21;  (* SHR (% rax) (Imm8 (word 33)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x83; 0xc1; 0x01;  (* ADD (% rcx) (Imm8 (word 1)) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x01; 0xfa;        (* ADD (% rdx) (% rdi) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x49; 0x0f; 0xbd; 0xcb;  (* BSR (% rcx) (% r11) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x0f; 0xac; 0xd0; 0x01;
                           (* SHRD (% rax) (% rdx) (Imm8 (word 1)) *)
  0x48; 0xd3; 0xe8;        (* SHR (% rax) (% cl) *)
  0x49; 0x0f; 0xaf; 0xc3;  (* IMUL (% rax) (% r11) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x89; 0xc6;        (* MOV (% rsi) (% rax) *)
  0x4c; 0x29; 0xde;        (* SUB (% rsi) (% r11) *)
  0x48; 0x0f; 0x42; 0xf0;  (* CMOVB (% rsi) (% rax) *)
  0x4c; 0x89; 0xd7;        (* MOV (% rdi) (% r10) *)
  0x49; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (r9,0))) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x49; 0xc7; 0xc2; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm32 (word 1)) *)
  0x48; 0x39; 0xf0;        (* CMP (% rax) (% rsi) *)
  0x73; 0x16;              (* JAE (Imm8 (word 22)) *)
  0x4d; 0x39; 0xc2;        (* CMP (% r10) (% r8) *)
  0x73; 0x0d;              (* JAE (Imm8 (word 13)) *)
  0x4b; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x49; 0x83; 0xc2; 0x01;  (* ADD (% r10) (Imm8 (word 1)) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0xeb; 0xe9;              (* JMP (Imm8 (word 233)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xeb; 0x06;              (* JMP (Imm8 (word 6)) *)
  0x48; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% rdx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0xc3                     (* RET *)
];;

let lemire_random_divfree_tmc =
  define_trimmed "lemire_random_divfree_tmc" lemire_random_divfree_mc;;

let LEMIRE_RANDOM_DIVFREE_EXEC =
  X86_MK_CORE_EXEC_RULE lemire_random_divfree_tmc;;

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

let VAL_WORD_THRESHOLD = prove
 (`!s:int64. ~(val s = 0)
             ==> val(word(2 EXP 64 MOD val s):int64) = 2 EXP 64 MOD val s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `val(s:int64)` THEN
  ASM_SIMP_TAC[MOD_LT_EQ; LT_IMP_LE; VAL_BOUND_64]);;

(*** The normalization of s, shifting it left by clz(s) places ***)

let CLZ_SHIFT_COUNT = prove
 (`!s:int64.
     ~(s = word 0)
     ==> val(word(val(word_xor (word(63 - word_clz s)) (word 63):int64)
                  MOD 256):byte) MOD 64 =
         word_clz s`,
  GEN_TAC THEN REWRITE_TAC[GSYM WORD_CLZ_LT_DIMINDEX; DIMINDEX_64] THEN
  SPEC_TAC(`word_clz(s:int64)`,`c:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

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
        ==> (if val(word_neg(word_mul q s)) < val s then word_neg(word_mul q s)
             else word_sub (word_neg(word_mul q s)) s) =
            word(2 EXP 64 MOD val s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word_neg(word_mul q s):int64) = 2 EXP 64 - val q * val s`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_NEG_CASES; VAL_WORD_MUL; DIMINDEX_64; MOD_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC `val(q:int64)` THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `word_neg(word_mul q s):int64 = s` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SUB_REFL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[MOD_EQ_0] THEN EXISTS_TAC `val(q:int64) + 1` THEN
    ASM_ARITH_TAC]);;

(*** The quotient approximation from the reciprocal and bsr result ***)

let LEMIRE_RECIP_Q = prove
 (`!s:int64 rcp:int64.
        ~(s = word 0)
        ==> val(word_ushr
                 (word_subword (word_join (word 1:int64) rcp:int128) (1,64))
                 (63 - word_clz s):int64) =
            (2 EXP 64 + val rcp) DIV 2 EXP (64 - word_clz s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM WORD_CLZ_LT_DIMINDEX; DIMINDEX_64] THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_SUBWORD; VAL_WORD_JOIN; VAL_WORD_1;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  MP_TAC(ISPEC `rcp:int64` VAL_BOUND_64) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(2 EXP 64 * 1 + val(rcp:int64)) MOD 2 EXP 128 =
                2 EXP 64 + val rcp`
  SUBST1_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(rcp:int64) < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((2 EXP 64 + val(rcp:int64)) DIV 2 EXP 1) MOD 2 EXP 64 =
                (2 EXP 64 + val rcp) DIV 2 EXP 1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC `val(rcp:int64) < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let LEMIRE_SHIFT_COUNT = prove
 (`!c. val(word(val(word(63 - c):int64) MOD 256):byte) MOD 64 = 63 - c`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIMINDEX_8] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `63 - c < 2 EXP 64`; ARITH_RULE `63 - c < 256`;
           ARITH_RULE `63 - c < 2 EXP 8`; ARITH_RULE `63 - c < 64`]);;

(*** Putting it together, in the form the simulation produces ***)

let LEMIRE_RECIP_THRESHOLD = prove
 (`!s:int64 rcp:int64.
     ~(s = word 0) /\
     &2 pow 64 + &(val rcp) < &2 pow 128 / &(2 EXP word_clz s * val s) /\
     &2 pow 128 / &(2 EXP word_clz s * val s) <= &2 pow 64 + &(val rcp) + &1
     ==> (if val(word_neg(word_mul
               (word_ushr (word_subword (word_join (word 1:int64) rcp:int128)
                                        (1,64))
                          (63 - word_clz s)) s)) < val s
          then word_neg(word_mul
               (word_ushr (word_subword (word_join (word 1:int64) rcp:int128)
                                        (1,64))
                          (63 - word_clz s)) s)
          else word_sub (word_neg(word_mul
               (word_ushr (word_subword (word_join (word 1:int64) rcp:int128)
                                        (1,64))
                          (63 - word_clz s)) s)) s) =
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
    ~(val s = 0) /\ nonoverlapping (word pc,0x158) (z,8) /\
    LENGTH l = val n /\ ~(val n = 0) /\
    ~(val s <= (val(EL 0 l) * val s) MOD 2 EXP 64)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) (BUTLAST lemire_random_divfree_tmc) /\
               read RIP st = word pc /\
               read RDI st = z /\ read RSI st = s /\
               read RDX st = n /\ read RCX st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0)
         (\st. bytes_loaded st (word pc) (BUTLAST lemire_random_divfree_tmc) /\
               read RIP st = word(pc + 0x136) /\
               read RDI st = z /\ read R11 st = s /\
               read R8 st = n /\ read R9 st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0 /\
               read R10 st = word 1 /\
               read RSI st = word(2 EXP 64 MOD val s) /\
               read RAX st = word((val(EL 0 l) * val s) MOD 2 EXP 64) /\
               read RDX st = word((val(EL 0 l) * val s) DIV 2 EXP 64))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
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

  X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MUL_WORD_PARTS; VAL_WORD; DIMINDEX_64;
                              MOD_MOD_REFL]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** Save registers and normalize s ***)

  X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (10--16) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP CLZ_SHIFT_COUNT (ASSUME `~(s:int64 = word 0)`)]) THEN

  (*** The reciprocal, using the existing proof of the word_recip code ***)

  X86_SUBROUTINE_SIM_TAC
   ((GEN_REWRITE_CONV RAND_CONV [lemire_random_divfree_tmc] THENC
     REWRITE_CONV[BUTLAST_CLAUSES])
    `BUTLAST lemire_random_divfree_tmc`,
    LEMIRE_RANDOM_DIVFREE_EXEC,
    0x3b,
    (GEN_REWRITE_CONV RAND_CONV [word_recip_tmc] THENC
     REWRITE_CONV[BUTLAST_CLAUSES])
    `BUTLAST word_recip_tmc`,
    WORD_RECIP_CORRECT)
   [`read RDI s`; `pc + 0x3b`] 17 THEN
  ABBREV_TAC `rcp = read RAX s17` THEN
  FIRST_X_ASSUM(MP_TAC o check
   (can (find_term ((=) `bit:num->int64->bool`)) o concl)) THEN
  REWRITE_TAC[ASSUME `read RAX s17 = rcp`] THEN
  ASM_SIMP_TAC[BIT63_WORD_SHL_CLZ; VAL_WORD_SHL_CLZ] THEN STRIP_TAC THEN

  (*** The quotient approximation, correction and setup for the loop ***)

  X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (18--30) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LEMIRE_SHIFT_COUNT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MUL_WORD_PARTS] THEN
  MATCH_MP_TAC LEMIRE_RECIP_THRESHOLD THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main loop, from the point where rdx:rax = x[k-1] * s and the words   *)
(* x[0],...,x[k-2] have all been rejected, by induction on d = n - k.       *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_DIVFREE_LOOP = prove
 (`!z s n x (l:int64 list) z0 pc d k.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x158) (z,8) /\
    LENGTH l = val n /\ 1 <= k /\ k + d = val n /\
    (!j. j < k - 1 ==> ~lemire_accept (2 EXP 64) (val s) (val(EL j l)))
    ==> ensures x86
         (\st. bytes_loaded st (word pc) (BUTLAST lemire_random_divfree_tmc) /\
               read RIP st = word(pc + 0x136) /\
               read RDI st = z /\ read R11 st = s /\
               read R8 st = n /\ read R9 st = x /\
               read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
               read (memory :> bytes64 z) st = z0 /\
               read R10 st = word k /\
               read RSI st = word(2 EXP 64 MOD val s) /\
               read RAX st = word((val(EL (k - 1) l) * val s) MOD 2 EXP 64) /\
               read RDX st = word((val(EL (k - 1) l) * val s) DIV 2 EXP 64))
         (\st. read RIP st = word(pc + 0x157) /\
               read RAX st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes64 z])`,
  let BRANCH_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE
     [MATCH_MP VAL_WORD_THRESHOLD (ASSUME `~(val(s:int64) = 0)`);
      VAL_WORD; DIMINDEX_64; MOD_MOD_REFL; GSYM lemire_accept]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC in
  let ACCEPT_TAC =
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--2) THEN
    BRANCH_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (3--4) THEN
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
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--2) THEN
    BRANCH_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (3--6) THEN
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
    ENSURES_SEQUENCE_TAC `pc + 0x136`
     `\st. read RDI st = z /\ read R11 st = s /\
           read R8 st = n /\ read R9 st = x /\
           read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
           read (memory :> bytes64 z) st = z0 /\
           read R10 st = word (k + 1) /\
           read RSI st = word(2 EXP 64 MOD val s) /\
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
      X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--2) THEN
      BRANCH_TAC THEN
      SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        TRANS_TAC LT_TRANS `val(n:int64)` THEN ASM_REWRITE_TAC[VAL_BOUND_64];
        ALL_TAC] THEN
      X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (3--4) THEN
      TRY(FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
          ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC) THEN
      X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (5--8) THEN
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

let LEMIRE_RANDOM_DIVFREE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc.
    ~(val s = 0) /\
    nonoverlapping (word pc,0x158) (z,8)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) (BUTLAST lemire_random_divfree_tmc) /\
               read RIP st = word pc /\
               C_ARGUMENTS [z; s; n; x] st /\
               wordlist_from_memory(x,val n) st = l /\
               read (memory :> bytes64 z) st = z0)
         (\st. read RIP st = word(pc + 0x157) /\
               C_RETURN st =
               word(lemire_draws (2 EXP 64) (val s) (val n)
                                 (\i. val(EL i l))) /\
               read (memory :> bytes64 z) st =
               if lemire_draws (2 EXP 64) (val s) (val n) (\i. val(EL i l)) = 0
               then z0
               else word(lemire_result (2 EXP 64) (val s) (\i. val(EL i l))))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes64 z])`,
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
   [X86_SIM_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--4) THEN
    REWRITE_TAC[LEMIRE_DRAWS_0];
    ALL_TAC] THEN

  (*** The fast path, accepting x[0] since l >= s ***)

  ASM_CASES_TAC
   `val(s:int64) <= (val(EL 0 (l:int64 list)) * val s) MOD 2 EXP 64` THENL
   [ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `read (memory :> bytes64 (word_add x (word(8 * 0)))) s0 =
                  EL 0 (l:int64 list)` MP_TAC THENL
     [MATCH_MP_TAC READ_WORDLIST_EL THEN EXISTS_TAC `val(n:int64)` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(val(n:int64) = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (1--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MUL_WORD_PARTS; VAL_WORD; DIMINDEX_64;
                                MOD_MOD_REFL]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o rhs o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC LEMIRE_RANDOM_DIVFREE_EXEC (10--11) THEN
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

  ENSURES_SEQUENCE_TAC `pc + 0x136`
   `\st. read RDI st = z /\ read R11 st = s /\
         read R8 st = n /\ read R9 st = x /\
         read (memory :> bytes(x,8 * val n)) st = num_of_wordlist l /\
         read (memory :> bytes64 z) st = z0 /\
         read R10 st = word 1 /\
         read RSI st = word(2 EXP 64 MOD val s) /\
         read RAX st = word((val(EL 0 (l:int64 list)) * val s) MOD 2 EXP 64) /\
         read RDX st = word((val(EL 0 l) * val s) DIV 2 EXP 64)` THEN
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
(* Correctness of the subroutine, with and without IBT.                     *)
(* ------------------------------------------------------------------------- *)

let LEMIRE_RANDOM_DIVFREE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    nonoverlapping (word pc,LENGTH lemire_random_divfree_tmc) (z,8) /\
    nonoverlapping (z,8) (stackpointer,8)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_divfree_tmc /\
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
  X86_PROMOTE_RETURN_NOSTACK_TAC lemire_random_divfree_tmc
    LEMIRE_RANDOM_DIVFREE_CORRECT);;

let LEMIRE_RANDOM_DIVFREE_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    nonoverlapping (word pc,LENGTH lemire_random_divfree_mc) (z,8) /\
    nonoverlapping (z,8) (stackpointer,8)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_divfree_mc /\
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
   (CONV_RULE TWEAK_CONV LEMIRE_RANDOM_DIVFREE_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let lemire_random_divfree_windows_mc = define_from_elf
  "lemire_random_divfree_windows_mc"
  "x86/random/lemire_random_divfree_VARIABLE_TIME.obj";;

let lemire_random_divfree_windows_tmc = define_trimmed
  "lemire_random_divfree_windows_tmc" lemire_random_divfree_windows_mc;;

let LEMIRE_RANDOM_DIVFREE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [(word pc,LENGTH lemire_random_divfree_windows_tmc); (x,8 * val n)] /\
    nonoverlapping (word pc,LENGTH lemire_random_divfree_windows_tmc) (z,8) /\
    nonoverlapping (z,8) (word_sub stackpointer (word 16),24)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_divfree_windows_tmc /\
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
         (MAYCHANGE [RSP] ,,
          WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes64 z] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  let TWEAK_CONV =
    REWRITE_CONV[wordlist_from_memory] THENC
    TOP_DEPTH_CONV DIMINDEX_CONV THENC
    REWRITE_CONV[ARITH_RULE `(64 * n + 7) DIV 8 = 8 * n`] in
  CONV_TAC TWEAK_CONV THEN
  WINDOWS_X86_WRAP_NOSTACK_TAC
    lemire_random_divfree_windows_tmc lemire_random_divfree_tmc
    (CONV_RULE TWEAK_CONV LEMIRE_RANDOM_DIVFREE_CORRECT));;

let LEMIRE_RANDOM_DIVFREE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!z s n x (l:int64 list) z0 pc stackpointer returnaddress.
    ~(val s = 0) /\
    ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [(word pc,LENGTH lemire_random_divfree_windows_mc); (x,8 * val n)] /\
    nonoverlapping (word pc,LENGTH lemire_random_divfree_windows_mc) (z,8) /\
    nonoverlapping (z,8) (word_sub stackpointer (word 16),24)
    ==> ensures x86
         (\st. bytes_loaded st (word pc) lemire_random_divfree_windows_mc /\
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
         (MAYCHANGE [RSP] ,,
          WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes64 z] ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  let TWEAK_CONV = REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV
     LEMIRE_RANDOM_DIVFREE_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;

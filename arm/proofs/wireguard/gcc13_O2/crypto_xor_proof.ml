(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of crypto_xor_spec.ml, with the byte arrays as       *)
(* functions (wg_bytes in arm/proofs/utils/wireguard.ml): fa and fb for the  *)
(* inputs and xf for the output. With n the size, the loop over the n DIV 8  *)
(* words (if n >= 8) reaches join1 with the xors of the first 8 * (n DIV 8)  *)
(* bytes at dst and the rest of the inputs unchanged, after which the        *)
(* n MOD 8 remaining bytes are done (by 4, 2 and 1 bytes) in each of the     *)
(* eight cases. The proof is the same when dst is the first input (in place) *)
(* as when they are disjoint, the source aa of the tactics being either.     *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/crypto_xor_spec.ml";;

let WIREGUARD_CRYPTO_XOR_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "__crypto_xor"];;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the shifted index, and the number of words and of the remaining   *)
(* bytes as the code computes them from the 32-bit size.                     *)
(* ------------------------------------------------------------------------- *)

let XOR_SHL3 = prove
 (`!i. word_shl (word i:int64) 3 = word(8 * i)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let XOR_WORDS_BOUND = prove
 (`!len:int64. 8 <= val len /\ val len < 2 EXP 32
     ==> word_zx (word_add (word_ushr (word_sub (word_subword len (0,32):int32)
                                                (word 8)) 3) (word 1)):int64 =
         word(val len DIV 8)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_SUB_CASES;
              VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  SUBGOAL_THEN `val(len:int64) MOD 4294967296 = val len` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `val(len:int64) < 2 EXP 32` THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(val(len:int64) - 8) DIV 8 + 1 = val len DIV 8` SUBST1_TAC THENL
   [UNDISCH_TAC `8 <= val(len:int64)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(len:int64) DIV 8 < 4294967296` ASSUME_TAC THENL
   [UNDISCH_TAC `val(len:int64) < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let XOR_TAIL_LENGTH = prove
 (`!len:int64. val len < 2 EXP 32
     ==> word_zx (word_and (word_subword len (0,32):int32) (word 7)):int64 =
         word(val len MOD 8)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`word_subword (len:int64) (0,32):int32`; `3`]
    (CONJUNCT1 WORD_AND_MASK_WORD)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  UNDISCH_TAC `val(len:int64) < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `val(len:int64) MOD 8 < 4294967296` ASSUME_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN
  SUBGOAL_THEN `val(len:int64) MOD 8 < 18446744073709551616` ASSUME_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* The setup: the arrays as functions, n the size; the size test.            *)
(* ------------------------------------------------------------------------- *)

let XOR_SETUP_TAC =
  MAP_EVERY X_GEN_TAC [`dst:int64`; `a:int64`; `b:int64`; `len:int64`;
     `la:byte list`; `lb:byte list`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_SEQ] THEN
  ASM_SIMP_TAC[WG_BYTES_OF_LIST] THEN
  ABBREV_TAC
   `xf = \i. word_xor (EL i (la:byte list)) (EL i (lb:byte list))` THEN
  ABBREV_TAC `fa = \i. EL i (la:byte list)` THEN
  ABBREV_TAC `fb = \i. EL i (lb:byte list)` THEN
  SUBGOAL_THEN `!i. (xf:num->byte) i = word_xor (fa i) (fb i)` ASSUME_TAC
  THENL [MAP_EVERY EXPAND_TAC ["xf"; "fa"; "fb"] THEN REWRITE_TAC[];
         ALL_TAC] THEN
  ABBREV_TAC `n = val(len:int64)`;;

let XOR_ZX_TAC =
  SUBGOAL_THEN `val(word_zx (len:int64):int32) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let XOR_LS7 = MP (SPECL [`word_zx (len:int64):int32`; `7`] WG_VAL_LS_COND32)
                 (ARITH_RULE `7 < 2 EXP 32`);;

(* ------------------------------------------------------------------------- *)
(* The state at join1 (after the words), the invariant of the loop over the  *)
(* words after i of them, and the loop from the entry to join1.              *)
(* ------------------------------------------------------------------------- *)

let xor_join_tm aa =
  subst [aa,`aa:int64`]
  `\s. read X30 s = returnaddress /\
       read X0 s = word_add (dst:int64) (word(8 * (n DIV 8))) /\
       read X1 s = word_add aa (word(8 * (n DIV 8))) /\
       read X2 s = word_add (b:int64) (word(8 * (n DIV 8))) /\
       read X3 s = word(n MOD 8) /\
       read (memory :> bytes(dst,8 * (n DIV 8))) s =
         wg_bytes (xf:num->byte) (8 * (n DIV 8)) /\
       read (memory :> bytes(word_add aa (word(8 * (n DIV 8))),n MOD 8)) s =
         wg_bytes (\i. (fa:num->byte)(8 * (n DIV 8) + i)) (n MOD 8) /\
       read (memory :> bytes(word_add b (word(8 * (n DIV 8))),n MOD 8)) s =
         wg_bytes (\i. (fb:num->byte)(8 * (n DIV 8) + i)) (n MOD 8)`;;

let xor_loop_tm aa =
  subst [aa,`aa:int64`]
  `\i s. (read X30 s = returnaddress /\
          read X0 s = dst /\ read X1 s = aa /\ read X2 s = b /\
          read X3 s = len /\
          read X4 s = word i /\ read X6 s = word(n DIV 8) /\
          read (memory :> bytes(dst,8 * i)) s =
            wg_bytes (xf:num->byte) (8 * i) /\
          read (memory :> bytes(word_add aa (word(8 * i)),n - 8 * i)) s =
            wg_bytes (\j. (fa:num->byte)(8 * i + j)) (n - 8 * i) /\
          read (memory :> bytes(word_add b (word(8 * i)),n - 8 * i)) s =
            wg_bytes (\j. (fb:num->byte)(8 * i + j)) (n - 8 * i)) /\
         (read ZF s <=> i = n DIV 8)`;;

(* Fewer than 8 bytes: straight to join1.                                    *)

let XOR_SHORT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC WIREGUARD_CRYPTO_XOR_GCC13_O2_EXEC (1--2) THEN XOR_ZX_TAC THEN
  WG_PC_REWRITE_TAC[XOR_LS7; ASSUME `val(word_zx (len:int64):int32) = n`;
                    ASSUME `n <= 7`] THEN
  SUBGOAL_THEN `n DIV 8 = 0 /\ n MOD 8 = n` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIV_LT; MOD_LT; ARITH_RULE `n <= 7 ==> n < 8`]; ALL_TAC] THEN
  SUBGOAL_THEN `word n:int64 = len` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `val(len:int64) = n`); WORD_VAL]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; ADD_CLAUSES; ETA_AX; wg_bytes;
                  READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE];;

(* In the loop body: the address in the form that the loads and stores use.  *)

let XOR_VI_TAC =
  SUBGOAL_THEN `word(8 * i):int64 = word(8 * val(word i:int64))` ASSUME_TAC
  THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `i < n DIV 8` THEN UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC];;

(* After the body: the stored word as the next 8 bytes of the output.        *)

let XOR_BODY_POST_TAC s =
  SUBGOAL_THEN
   (vsubst [s,`s:armstate`]
     `read (memory :> bytes(word_add (dst:int64) (word(8 * i)),8)) s =
      wg_bytes (\j. (xf:num->byte)(8 * i + j)) 8`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 WG_READ_BYTES_OF_WORDS) THEN CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `word(8 * i):int64 = word(8 * val(word i:int64))`] THEN
      ASM_REWRITE_TAC[CONJUNCT1 WG_XOR_BYTES_FUN];
      REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP (8 * 8)`; WG_BYTES_BOUND]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`dst:int64`; `xf:num->byte`; `8 * i`; `8`; s]
               WG_READ_BYTES_FUN_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* In the prologue: the number of words.                                     *)

let XOR_BOUND_TAC =
  SUBGOAL_THEN `8 <= val(len:int64) /\ val len < 2 EXP 32` (fun th ->
    ASSUME_TAC(REWRITE_RULE[ASSUME `val(len:int64) = n`]
      (MP (SPEC `len:int64` XOR_WORDS_BOUND) th))) THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (find_term (fun t -> t = `word_ushr:int32->num->int32`))
           (concl th) &&
       not(can (find_term (fun t -> type_of t = `:armstate`)) (concl th))
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)
    else failwith "XOR_BOUND_TAC");;

let XOR_LOOP_TAC aa =
  let EXEC = WIREGUARD_CRYPTO_XOR_GCC13_O2_EXEC in
  ENSURES_WHILE_PUP_TAC `n DIV 8` `pc + __crypto_xor_loop1`
    `pc + __crypto_xor_loop1_back` (xor_loop_tm aa) THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--2) THEN XOR_ZX_TAC THEN
    WG_PC_REWRITE_TAC[XOR_LS7; ASSUME `val(word_zx (len:int64):int32) = n`;
                      ASSUME `~(n <= 7)`] THEN
    WG_STEPS_TAC EXEC (3--6) THEN XOR_BOUND_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; ADD_CLAUSES; WORD_ADD_0; ETA_AX] THEN
    REWRITE_TAC[wg_bytes; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `8 * i + 8 <= n` ASSUME_TAC THENL
     [UNDISCH_TAC `i < n DIV 8` THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun (a,f) ->
      let a8 = mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                       `word(8 * i):int64`) in
      let g = mk_abs(`j:num`,mk_comb(f,`8 * i + j`)) in
      WG_BYTES_FUN_SUB_TAC a8 g `n - 8 * i` `s0:armstate` `0` `8` THEN
      WG_BYTES_FUN_SUB_TAC a8 g `n - 8 * i` `s0:armstate` `8`
                           `n - (8 * i + 8)` THEN
      WG_WORD_FACT_AT_TAC a8 `s0:armstate` 8)
     [aa,`fa:num->byte`; `b:int64`,`fb:num->byte`] THEN
    XOR_VI_TAC THEN
    MAP_EVERY (fun a ->
      let l = vsubst [a,`a:int64`]
                `read (memory :> bytes64 (word_add a (word(8 * i)))) s0` in
      FIRST_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) = l
        then ASSUME_TAC(REWRITE_RULE
               [ASSUME `word(8 * i):int64 = word(8 * val(word i:int64))`] th)
        else failwith "")) [aa; `b:int64`] THEN
    WG_STEPS_TAC EXEC (1--6) THEN
    XOR_BODY_POST_TAC `s6:armstate` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) WG_VAL_WORD_SUB_EQ_0 o
      lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `i < n DIV 8` THEN UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ARITH_TAC];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];

    ENSURES_INIT_TAC "s0" THEN WG_STEPS_TAC EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[XOR_SHL3; XOR_TAIL_LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `n MOD 8 = n - 8 * (n DIV 8)`] THEN
    ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* From join1: the r = n MOD 8 remaining bytes, as chunks (offset, size) of  *)
(* 4, 2 and 1 bytes, the number of steps, and the tactic for each r.         *)
(* ------------------------------------------------------------------------- *)

let xor_chunks r =
  let c4 = if r >= 4 then [0,4] else [] in
  let r1 = if r >= 4 then r - 4 else r in
  let o2 = if r >= 4 then 4 else 0 in
  let c2 = if r1 >= 2 then [o2,2] else [] in
  let r2 = if r1 >= 2 then r1 - 2 else r1 in
  let o1 = o2 + (if r1 >= 2 then 2 else 0) in
  let c1 = if r2 = 1 then [o1,1] else [] in
  c4 @ c2 @ c1;;

let xor_tail_steps r =
  let r1 = if r >= 4 then r - 4 else r in
  let r2 = if r1 >= 2 then r1 - 2 else r1 in
  2 + (if r >= 4 then 5 else 0) + 2 + (if r1 >= 2 then 5 else 0) + 1 +
  (if r2 = 1 then 4 else 0) + 1;;

let xor_base aa =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,aa),
          `word(8 * n DIV 8):int64`);;

let xor_fun f = mk_abs(`i:num`,mk_comb(f,`8 * n DIV 8 + i`));;

let xor_koff off =
  if off = 0 then `8 * n DIV 8` else
  mk_binop `(+):num->num->num` `8 * n DIV 8` (mk_small_numeral off);;

let xor_addr aa off =
  if off = 0 then xor_base aa else
  mk_comb(mk_comb(`word_add:int64->int64->int64`,aa),
          mk_comb(`word:num->int64`,xor_koff off));;

let xor_xf_fun off =
  mk_abs(`i:num`,mk_comb(`xf:num->byte`,
    if off = 0 then `8 * n DIV 8 + i` else
    mk_binop `(+):num->num->num` `8 * n DIV 8`
      (mk_binop `(+):num->num->num` (mk_small_numeral off) `i:num`)));;

let xor_width_th c =
  match c with
    8 -> CONJUNCT1 WG_READ_BYTES_OF_WORDS
  | 4 -> CONJUNCT1(CONJUNCT2 WG_READ_BYTES_OF_WORDS)
  | 2 -> CONJUNCT1(CONJUNCT2(CONJUNCT2 WG_READ_BYTES_OF_WORDS))
  | _ -> CONJUNCT2(CONJUNCT2(CONJUNCT2 WG_READ_BYTES_OF_WORDS));;

(* A stored chunk as bytes of the output, and its combination with the       *)
(* output so far.                                                            *)

let XOR_CHUNK_BYTES_TAC s (off,c) =
  let tm = vsubst [xor_addr `dst:int64` off,`x:int64`;
                   mk_small_numeral c,`c:num`;
                   s,`s:armstate`; xor_xf_fun off,`g:num->byte`]
             `read (memory :> bytes(x,c)) s = wg_bytes g c` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MATCH_MP_TAC(xor_width_th c) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[WG_XOR_ZX; WG_XOR_BYTES_FUN];
      REWRITE_TAC[ARITH_RULE `2 EXP 32 = 2 EXP (8 * 4) /\
                              2 EXP 16 = 2 EXP (8 * 2) /\
                              2 EXP 8 = 2 EXP (8 * 1) /\
                              2 EXP 64 = 2 EXP (8 * 8)`;
                  WG_BYTES_BOUND]];
    ALL_TAC];;

let XOR_COMBINE_TAC s (off,c) =
  MP_TAC(SPECL [`dst:int64`; `xf:num->byte`; xor_koff off; mk_small_numeral c;
                s] WG_READ_BYTES_FUN_COMBINE) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC];;

let XOR_TAIL_TAC aa r =
  let cs = xor_chunks r and ns = xor_tail_steps r in
  let sN = mk_var("s"^string_of_int ns,`:armstate`) in
  let rn = mk_small_numeral r in
  REWRITE_TAC[ASSUME (mk_eq(`n MOD 8`,rn))] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (a,f) -> MAP_EVERY (fun (off,c) ->
     WG_BYTES_FUN_SUB_TAC (xor_base a) (xor_fun f) rn `s0:armstate`
                 (mk_small_numeral off) (mk_small_numeral c) THEN
     WG_WORD_FACT_AT_TAC (xor_addr a off) `s0:armstate` c) cs)
   [aa,`fa:num->byte`; `b:int64`,`fb:num->byte`] THEN
  WG_STEPS_TAC WIREGUARD_CRYPTO_XOR_GCC13_O2_EXEC (1--ns) THEN
  MAP_EVERY (XOR_CHUNK_BYTES_TAC sN) cs THEN
  MAP_EVERY (XOR_COMBINE_TAC sN) cs THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   (mk_eq(`n:num`,if r = 0 then `8 * n DIV 8`
                  else mk_binop `(+):num->num->num` `8 * n DIV 8` rn))
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [MP_TAC(SPECL [`n:num`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let XOR_MAIN_TAC aa =
  ENSURES_SEQUENCE_TAC `pc + __crypto_xor_join1` (xor_join_tm aa) THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n <= 7` THENL [XOR_SHORT_TAC; XOR_LOOP_TAC aa];
    MP_TAC(ARITH_RULE `n MOD 8 = 0 \/ n MOD 8 = 1 \/ n MOD 8 = 2 \/
                       n MOD 8 = 3 \/ n MOD 8 = 4 \/ n MOD 8 = 5 \/
                       n MOD 8 = 6 \/ n MOD 8 = 7`) THEN
    STRIP_TAC THENL (map (XOR_TAIL_TAC aa) (0--7))];;

let WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  XOR_SETUP_TAC THEN ASM_CASES_TAC `dst:int64 = a` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                  check (fun th -> concl th = `dst:int64 = a`)) THEN
    XOR_MAIN_TAC `dst:int64`;
    UNDISCH_TAC
     `dst:int64 = a \/
      nonoverlapping_modulo (2 EXP 64) (val dst,n) (val(a:int64),n)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    XOR_MAIN_TAC `a:int64`]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function construct(h,length,n) of puff, at 0x6a0 in the image, which  *)
(* builds the decoding table h for the canonical Huffman code with the n     *)
(* code lengths in length[]. It counts the codes of each length, returns 0   *)
(* if there are none and otherwise checks, length by length, that the        *)
(* lengths are not over-subscribed, returning a negative number if they are. *)
(* Then it computes, on the stack, the offset of the symbols of each length  *)
(* in the table and places the symbols in the order of their codes. It       *)
(* returns 0 for a complete code and a positive number for an incomplete     *)
(* one.                                                                      *)
(*                                                                           *)
(* 0x06a0:  ldr    x5, [x0]            0x0720:  sub    sp, sp, #0x20         *)
(* 0x06a4:  mov    x9, x0              0x0724:  add    x5, x5, #0x2          *)
(* 0x06a8:  stp    xzr, xzr, [x5]      0x0728:  mov    x8, sp                *)
(* 0x06ac:  stp    xzr, xzr, [x5, #16] 0x072c:  mov    x4, #0x0              *)
(* 0x06b0:  cmp    w2, #0x0            0x0730:  mov    w3, #0x0              *)
(* 0x06b4:  b.le   0x6dc               0x0734:  strh   wzr, [sp, #2]         *)
(* 0x06b8:  mov    x6, x1              0x0738:  ldrh   w7, [x5, x4]          *)
(* 0x06bc:  add    x7, x1, w2, sxtw #1 0x073c:  add    x6, x8, x4            *)
(* 0x06c0:  ldrsh  x3, [x6], #2        0x0740:  add    x4, x4, #0x2          *)
(* 0x06c4:  lsl    x3, x3, #1          0x0744:  add    w3, w3, w7            *)
(* 0x06c8:  ldrh   w4, [x5, x3]        0x0748:  sxth   w3, w3                *)
(* 0x06cc:  add    w4, w4, #0x1        0x074c:  strh   w3, [x6, #4]          *)
(* 0x06d0:  strh   w4, [x5, x3]        0x0750:  cmp    x4, #0x1c             *)
(* 0x06d4:  cmp    x7, x6              0x0754:  b.ne   0x738                 *)
(* 0x06d8:  b.ne   0x6c0               0x0758:  cmp    w2, #0x0              *)
(* 0x06dc:  ldrsh  w3, [x5]            0x075c:  b.le   0x790                 *)
(* 0x06e0:  mov    w0, #0x0            0x0760:  sxtw   x4, w2                *)
(* 0x06e4:  cmp    w3, w2              0x0764:  mov    x2, #0x0              *)
(* 0x06e8:  b.eq   0x798               0x0768:  ldrsh  w3, [x1, x2, lsl #1]  *)
(* 0x06ec:  ldrsh  w0, [x5, #2]        0x076c:  cbz    w3, 0x784             *)
(* 0x06f0:  mov    w3, #0x2            0x0770:  ldr    x6, [x9, #8]          *)
(* 0x06f4:  subs   w0, w3, w0          0x0774:  ldrsh  w5, [x8, w3, sxtw #1] *)
(* 0x06f8:  b.mi   0x798               0x0778:  add    w7, w5, #0x1          *)
(* 0x06fc:  add    x4, x5, #0x4        0x077c:  strh   w7, [x8, w3, sxtw #1] *)
(* 0x0700:  add    x7, x5, #0x20       0x0780:  strh   w2, [x6, w5, sxtw #1] *)
(* 0x0704:  b      0x714               0x0784:  add    x2, x2, #0x1          *)
(* 0x0708:  ldrsh  w3, [x4], #2        0x0788:  cmp    x2, x4                *)
(* 0x070c:  subs   w0, w6, w3          0x078c:  b.ne   0x768                 *)
(* 0x0710:  b.mi   0x798               0x0790:  add    sp, sp, #0x20         *)
(* 0x0714:  lsl    w6, w0, #1          0x0794:  ret                          *)
(* 0x0718:  cmp    x4, x7              0x0798:  ret                          *)
(* 0x071c:  b.ne   0x708                                                     *)
(* ========================================================================= *)

needs "arm/proofs/utils/puff.ml";;

(* ------------------------------------------------------------------------- *)
(* The proof is in four parts. First the counts are zeroed and then          *)
(* accumulated by a loop over the symbols, which updates the count of the    *)
(* length of each symbol, an element of h->count at a symbolic index (see    *)
(* READ_MEMORY_WORDLIST16_SPLIT and _UPDATE). Then a loop with early exits   *)
(* checks the lengths, at length L with left = 2^L - (first + count), where  *)
(* first is the first code of length L. Then the offsets of the lengths in   *)
(* the table, which are the indices huffman_index, are computed (in full,    *)
(* there being 14 of them), and finally a loop over the symbols places each  *)
(* symbol of nonzero length at the next offset for its length, which is its  *)
(* rank in the order of the codes. The element offs[0] of the array of       *)
(* offsets on the stack is never written, so it keeps its initial value o0.  *)
(* ------------------------------------------------------------------------- *)

(*** The count of length k in h->count, before the state s, for numeral k ***)

let CNT_ELEMENT_TAC k s =
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
   (ISPECL [`cnt:int64`; `huffman_counts lens`; `16`; k; s]
           READ_MEMORY_BYTES16_NUM_OF_WORDLIST)) THEN
  ASM_REWRITE_TAC[LENGTH_HUFFMAN_COUNTS] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_LT_CONV) THEN REWRITE_TAC[] THEN
  SIMP_TAC[EL_HUFFMAN_COUNTS; ARITH] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  DISCH_TAC;;

(*** The same for a symbolic length k ***)

let CNT_ELEMENT_SYM_TAC k s =
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
   (ISPECL [`cnt:int64`; `huffman_counts lens`; `16`; k; s]
           READ_MEMORY_BYTES16_NUM_OF_WORDLIST)) THEN
  ASM_REWRITE_TAC[LENGTH_HUFFMAN_COUNTS] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`lens:num list`; k] EL_HUFFMAN_COUNTS) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC;;

(*** The count of length k is at most the number of symbols ***)

let COUNT_BOUND_TAC k =
  MP_TAC(SPECL [`lens:num list`; k] HUFFMAN_COUNT_LE_LENGTH) THEN
  DISCH_TAC;;

(*** Expand huffman_index lens k, for a numeral k, as a sum of counts ***)

let HUFFMAN_INDEX_NUM_CONV =
  let th = SPEC_ALL HUFFMAN_INDEX_CLAUSES in
  let th0 = CONJUNCT1 th and th1 = CONJUNCT1(CONJUNCT2 th)
  and th2 = SPEC_ALL(CONJUNCT2(CONJUNCT2 th)) in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("huffman_index",_),l),k) when is_numeral k ->
        let n = dest_small_numeral k in
        if n = 0 then PART_MATCH lhs th0 tm
        else if n = 1 then PART_MATCH lhs th1 tm
        else
          let km1 = mk_small_numeral(n - 1) in
          let tm' = mk_comb(rator tm,mk_binop `(+):num->num->num` km1 `1`) in
          let ith = PART_MATCH (lhs o rand) th2 tm' in
          let ith' = MP ith (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl ith)))) in
          let ith'' = CONV_RULE(LAND_CONV(RAND_CONV NUM_ADD_CONV)) ith' in
          CONV_RULE(RAND_CONV(LAND_CONV conv)) ith''
    | _ -> failwith "HUFFMAN_INDEX_NUM_CONV" in
  conv;;

(*** A step normalizing the pointers, for the straight-line part ***)

let CSTEP_TAC n = PUFF_STEP_TAC n THEN STATE_PTR_NORM_TAC;;
let CSTEPS_TAC ns = MAP_EVERY CSTEP_TAC ns;;

let CSTEPS_TAC ns = MAP_EVERY CSTEP_TAC ns;;

(*** The regions that construct reads and writes ***)

let construct_rr =
 `[h,16; len,2 * LENGTH(lens:num list); cnt,32;
   word_sub stackpointer (word 32),32]:(int64#num)list`
and construct_wr =
 `[cnt,32; sym,2 * LENGTH(lens:num list);
   word_sub stackpointer (word 32),32]:(int64#num)list`;;

(*** The state at 0x6dc, with the counts in h->count ***)

let construct_ab = with_memsafe construct_rr construct_wr `\s.
  read SP s = stackpointer /\ read X30 s = returnaddress /\
  read X1 s = len /\ read X2 s = word(LENGTH lens) /\
  read X5 s = cnt /\ read X9 s = h /\
  read (memory :> bytes64(word_add h (word 8))) s = sym /\
  read (memory :> bytes(len,2 * LENGTH lens)) s =
  num_of_wordlist(MAP (word:num->int16) lens) /\
  read (memory :> bytes(cnt,32)) s = num_of_wordlist(huffman_counts lens) /\
  read (memory :> bytes16(word_sub stackpointer (word 32))) s = o0`;;

(*** The invariant of the loop counting the lengths, at 0x6c0 ***)

let construct_hist =
  with_memsafe_loop construct_rr construct_wr `\i s.
  (read SP s = stackpointer /\ read X30 s = returnaddress /\
   read X1 s = len /\ read X2 s = word(LENGTH lens) /\
   read X5 s = cnt /\ read X9 s = h /\
   read X6 s = word_add len (word(2 * i)) /\
   read X7 s = word_add len (word(2 * LENGTH lens)) /\
   read (memory :> bytes64(word_add h (word 8))) s = sym /\
   read (memory :> bytes(len,2 * LENGTH lens)) s =
   num_of_wordlist(MAP (word:num->int16) lens) /\
   read (memory :> bytes(cnt,32)) s =
   num_of_wordlist(list_of_seq
     (\j. word(CARD {t | t < i /\ EL t lens = j}):int16) 16) /\
   read (memory :> bytes16(word_sub stackpointer (word 32))) s = o0) /\
  (read ZF s <=> i = LENGTH lens)`;;

(*** From the entry to 0x6dc ***)

let CONSTRUCT_PHASE_A_TAC =
  ASM_CASES_TAC `LENGTH(lens:num list) = 0` THENL
   [PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--6) THEN
    MP_TAC(SPECL [`cnt:int64`; `s6:armstate`] READ_MEMORY_BYTES32_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    PUFF_FINAL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(lens:num list) = 0`]) THEN
    ASM_REWRITE_TAC[huffman_counts; huffman_count; LT; EMPTY_GSPEC;
                    CARD_CLAUSES; NUM_OF_WORDLIST_LIST_OF_SEQ_0] THEN
    REWRITE_TAC[ASSUME `LENGTH(lens:num list) = 0`; LT; EMPTY_GSPEC;
                CARD_CLAUSES; NUM_OF_WORDLIST_LIST_OF_SEQ_0];
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `LENGTH(lens:num list)` `pc + 0x6c0` `pc + 0x6d8`
    construct_hist THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--8) THEN
    MP_TAC(SPECL [`cnt:int64`; `s8:armstate`] READ_MEMORY_BYTES32_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    PUFF_FINAL_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; LT; EMPTY_GSPEC; CARD_CLAUSES;
                NUM_OF_WORDLIST_LIST_OF_SEQ_0] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC `j0 = EL i (lens:num list)` THEN
    SUBGOAL_THEN `j0 <= 15` ASSUME_TAC THENL
     [EXPAND_TAC "j0" THEN
      UNDISCH_TAC `ALL (\x. x <= 15) lens` THEN REWRITE_TAC[GSYM ALL_EL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    PUFF_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`len:int64`; `MAP (word:num->int16) lens`;
                   `LENGTH(lens:num list)`; `i:num`; `s0:armstate`]
                  READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`cnt:int64`;
      `list_of_seq (\j. word(CARD {t | t < i /\ EL t lens = j}):int16) 16`;
      `j0:num`; `s0:armstate`] READ_MEMORY_WORDLIST16_SPLIT) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `j <= 15 ==> j < 16`] THEN
    ABBREV_TAC `c0 = CARD {t | t < i /\ EL t (lens:num list) = j0}` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `c0 <= i` ASSUME_TAC THENL
     [EXPAND_TAC "c0" THEN REWRITE_TAC[CARD_RESTRICT_LT_LE]; ALL_TAC] THEN
    PUFF_STEPS_TAC [1] THEN PTR_NORM_TAC `X6` THEN PUFF_STEPS_TAC (2--6) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    MP_TAC(ISPECL [`cnt:int64`;
      `list_of_seq (\j. word(CARD {t | t < i /\ EL t lens = j}):int16) 16`;
      `list_of_seq (\j. word(CARD {t | t < i + 1 /\ EL t lens = j}):int16)
                   16`;
      `j0:num`; `s6:armstate`] READ_MEMORY_WORDLIST16_UPDATE) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `j <= 15 ==> j < 16`] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CARD_RESTRICT_LT_ADD1] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[];
      DISCH_TAC] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN PUFF_INIT_TAC "s0" THEN
    PUFF_STEPS_TAC [1] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC [1] THEN
    PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[huffman_counts; huffman_count]];;

(*** The invariant of the loop checking the lengths, at 0x714, L = i + 1 ***)

let construct_left = with_memsafe construct_rr construct_wr `\i s.
  aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
  read PC s = word(pc + 0x714) /\
  read SP s = stackpointer /\ read X30 s = returnaddress /\
  read X0 s =
  word(2 EXP (i + 1) -
       (huffman_first lens (i + 1) + huffman_count lens (i + 1))) /\
  read X1 s = len /\ read X2 s = word(LENGTH lens) /\
  read X4 s = word_add cnt (word(2 * (i + 2))) /\
  read X5 s = cnt /\ read X7 s = word_add cnt (word 32) /\ read X9 s = h /\
  read (memory :> bytes64(word_add h (word 8))) s = sym /\
  read (memory :> bytes(len,2 * LENGTH lens)) s =
  num_of_wordlist(MAP (word:num->int16) lens) /\
  read (memory :> bytes(cnt,32)) s = num_of_wordlist(huffman_counts lens) /\
  read (memory :> bytes16(word_sub stackpointer (word 32))) s = o0 /\
  huffman_first lens (i + 1) + huffman_count lens (i + 1) <= 2 EXP (i + 1) /\
  ~(ALL (\x. x = 0) lens)`;;

let construct_left0 = rhs(concl(BETA_CONV(mk_comb(construct_left,`0`))));;

(*** The state at 0x758, with the offsets computed ***)

let construct_d = with_memsafe construct_rr construct_wr `\s.
  aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
  read PC s = word(pc + 0x758) /\
  read SP s = word_sub stackpointer (word 32) /\
  read X30 s = returnaddress /\
  read X0 s = word(2 EXP 15 - huffman_kraft lens) /\
  read X1 s = len /\ read X2 s = word(LENGTH lens) /\
  read X8 s = word_sub stackpointer (word 32) /\ read X9 s = h /\
  read (memory :> bytes64(word_add h (word 8))) s = sym /\
  read (memory :> bytes(len,2 * LENGTH lens)) s =
  num_of_wordlist(MAP (word:num->int16) lens) /\
  read (memory :> bytes(cnt,32)) s = num_of_wordlist(huffman_counts lens) /\
  read (memory :> bytes(word_sub stackpointer (word 32),32)) s =
  num_of_wordlist(list_of_seq
    (\j. if j = 0 then o0 else word(huffman_index lens j):int16) 16) /\
  huffman_kraft lens <= 2 EXP 15 /\ ~(ALL (\x. x = 0) lens)`;;

(*** From 0x6dc to 0x758, or to the return if the lengths are all 0 or     ***)
(*** the code is over-subscribed                                           ***)

let CONSTRUCT_PHASE_BC_TAC =
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC construct_left0 THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    PUFF_INIT_TAC "s0" THEN CNT_ELEMENT_TAC `0` `s0:armstate` THEN
    CNT_ELEMENT_TAC `1` `s0:armstate` THEN
    COUNT_BOUND_TAC `0` THEN COUNT_BOUND_TAC `1` THEN
    PUFF_STEPS_TAC (1--3) THEN
    ASM_CASES_TAC `ALL (\x. x = 0) lens` THENL
     [SUBGOAL_THEN `huffman_count lens 0 = LENGTH(lens:num list)` ASSUME_TAC
      THENL [ASM_REWRITE_TAC[HUFFMAN_COUNT_ALL_ZERO]; ALL_TAC] THEN
      PUFF_STEPS_TAC (4--5) THEN PUFF_FINAL_TAC THEN
      ASM_SIMP_TAC[HUFFMAN_KRAFT_ALL_ZERO; HUFFMAN_TABLE_ALL_ZERO; LE_0] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`sym:int64`; `LENGTH(lens:num list)`; `s5:armstate`]
                   WORDLIST16_FROM_MEMORY) THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(huffman_count lens 0 = LENGTH(lens:num list))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[HUFFMAN_COUNT_ALL_ZERO]; ALL_TAC] THEN
    PUFF_STEPS_TAC (4--7) THEN
    ASM_CASES_TAC `huffman_count lens 1 <= 2` THEN W32_DECIDE_FLAGS_TAC THENL
     [PUFF_STEPS_TAC (8--11) THEN PUFF_FINAL_TAC THEN
      DISJ1_TAC THEN ASM_REWRITE_TAC[HUFFMAN_FIRST_CLAUSES; ADD_CLAUSES];
      PUFF_STEPS_TAC (8--9) THEN PUFF_FINAL_TAC THEN
      DISJ2_TAC THEN DISJ2_TAC THEN
      SUBGOAL_THEN `32768 < huffman_kraft lens` ASSUME_TAC THENL
       [MP_TAC(SPECL [`lens:num list`; `1`] HUFFMAN_FIRST_COUNT_OVER) THEN
        REWRITE_TAC[HUFFMAN_FIRST_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM NOT_LT; WORD_ZX_ZX_32_64] THEN
      MATCH_MP_TAC IVAL_WORD_SUB_NEG THEN SIMPLE_ARITH_TAC];
    MATCH_MP_TAC(ISPECL [`14`; construct_left] ENSURES_LOOP_EXIT) THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
      MATCH_MP_TAC ENSURES_ALREADY THEN REWRITE_TAC[] THEN
      SUBSUMED_ID_MAYCHANGE_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `2 EXP (i + 1) <= 16384` ASSUME_TAC THENL
       [TRANS_TAC LE_TRANS `2 EXP 14` THEN REWRITE_TAC[LE_EXP] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      COUNT_BOUND_TAC `i + 1` THEN COUNT_BOUND_TAC `i + 2` THEN
      PUFF_INIT_TAC "s0" THEN
      CNT_ELEMENT_SYM_TAC `i + 2` `s0:armstate` THEN
      PUFF_STEPS_TAC (1--4) THEN PTR_NORM_TAC `X4` THEN PUFF_STEPS_TAC [5] THEN
      ASM_CASES_TAC
       `huffman_count lens (i + 2) <=
        2 * (2 EXP (i + 1) -
             (huffman_first lens (i + 1) + huffman_count lens (i + 1)))` THEN
      W32_DECIDE_FLAGS_TAC THENL
       [PUFF_STEPS_TAC [6] THEN PUFF_FINAL_TAC THEN
        DISJ1_TAC THEN
        REWRITE_TAC[MATCH_MP (CONJUNCT2(CONJUNCT2(SPEC `lens:num list`
                       HUFFMAN_FIRST_CLAUSES))) (ARITH_RULE `~(i + 1 = 0)`);
                    SPECL [`2`; `i + 1`; `1`] EXP_ADD; EXP_1] THEN
        REWRITE_TAC[ARITH_RULE `(i + 1) + 1 = i + 2`;
                    ARITH_RULE `2 * ((i + 1) + 2) = 2 * (i + 2) + 2`] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN
        FIRST [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
        PUFF_STEPS_TAC (6--7) THEN PUFF_FINAL_TAC THEN
        DISJ2_TAC THEN DISJ2_TAC THEN
        SUBGOAL_THEN `2 EXP 15 < huffman_kraft lens` ASSUME_TAC THENL
         [MATCH_MP_TAC HUFFMAN_FIRST_COUNT_OVER THEN EXISTS_TAC `i + 2` THEN
          SUBGOAL_THEN
           `huffman_first lens (i + 2) =
            2 * (huffman_first lens (i + 1) + huffman_count lens (i + 1))`
          SUBST1_TAC THENL
           [REWRITE_TAC[ARITH_RULE `i + 2 = (i + 1) + 1`] THEN
            MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `lens:num list`
                           HUFFMAN_FIRST_CLAUSES))) THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `2 EXP (i + 2) = 2 * 2 EXP (i + 1)` SUBST1_TAC THENL
           [REWRITE_TAC[ARITH_RULE `i + 2 = SUC(i + 1)`; EXP]; ALL_TAC] THEN
          SIMPLE_ARITH_TAC;
          ALL_TAC] THEN
        RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
        ASM_REWRITE_TAC[GSYM NOT_LT; WORD_ZX_ZX_32_64] THEN
        MATCH_MP_TAC IVAL_WORD_SUB_NEG THEN SIMPLE_ARITH_TAC];
      BETA_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      PUFF_INIT_TAC "s0" THEN
      MAP_EVERY (fun k -> CNT_ELEMENT_TAC (mk_small_numeral k) `s0:armstate`)
                (0--15) THEN
      MAP_EVERY (fun k -> COUNT_BOUND_TAC (mk_small_numeral k)) (0--15) THEN
      CSTEPS_TAC (1--121) THEN
      SUBGOAL_THEN
       `read (memory :> bytes(word_sub stackpointer (word 32),32)) s121 =
        num_of_wordlist(list_of_seq
         (\j. if j = 0 then o0 else word(huffman_index lens j):int16) 16)`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL
         [`list_of_seq
            (\j. if j = 0 then o0 else word(huffman_index lens j):int16) 16`;
          `word_sub stackpointer (word 32):int64`; `s121:armstate`]
         READ_MEMORY_WORDLIST16_ELEMENTS) THEN
        REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        SIMP_TAC[EL_LIST_OF_SEQ; ARITH] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        REWRITE_TAC[WORD_ADD_0] THEN
        CONV_TAC(DEPTH_CONV HUFFMAN_INDEX_NUM_CONV) THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
        ARITH_TAC;
        ALL_TAC] THEN
      PUFF_FINAL_TAC THEN DISJ1_TAC THEN
      ASM_SIMP_TAC[GSYM HUFFMAN_KRAFT_FIRST_COUNT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]]];;

(*** The invariant of the loop placing the symbols, at 0x768 for symbol i ***)

let construct_place =
  with_memsafe_loop construct_rr construct_wr `\i s.
  (read SP s = word_sub stackpointer (word 32) /\
   read X30 s = returnaddress /\
   read X0 s = word(2 EXP 15 - huffman_kraft lens) /\
   read X1 s = len /\ read X2 s = word i /\ read X4 s = word(LENGTH lens) /\
   read X8 s = word_sub stackpointer (word 32) /\ read X9 s = h /\
   read (memory :> bytes64(word_add h (word 8))) s = sym /\
   read (memory :> bytes(len,2 * LENGTH lens)) s =
   num_of_wordlist(MAP (word:num->int16) lens) /\
   read (memory :> bytes(cnt,32)) s = num_of_wordlist(huffman_counts lens) /\
   read (memory :> bytes(word_sub stackpointer (word 32),32)) s =
   num_of_wordlist(list_of_seq
     (\j. if j = 0 then o0
          else word(huffman_index lens j +
                    CARD {t | t < i /\ EL t lens = j}):int16) 16) /\
   (?syms. LENGTH syms = LENGTH lens /\
           read (memory :> bytes(sym,2 * LENGTH lens)) s =
           num_of_wordlist syms /\
           !t. t < i /\ ~(EL t lens = 0)
               ==> EL (huffman_rank lens t) (syms:int16 list) = word t)) /\
  (read ZF s <=> i = LENGTH lens)`;;

(*** Placing symbol i, at the next offset for its length if that is not 0 ***)

let CONSTRUCT_PLACE_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ENSURES_EXISTS_PRE_TAC `syms:int16 list` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  ABBREV_TAC `j0 = EL i (lens:num list)` THEN
  SUBGOAL_THEN `j0 <= 15` ASSUME_TAC THENL
   [EXPAND_TAC "j0" THEN
    UNDISCH_TAC `ALL (\x. x <= 15) lens` THEN REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  PUFF_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`len:int64`; `MAP (word:num->int16) lens`;
                 `LENGTH(lens:num list)`; `i:num`; `s0:armstate`]
                READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN DISCH_TAC THEN
  ADDR16_TAC `len:int64` `i:num` `val(word i:int64)` THEN
  PUFF_STEPS_TAC [1] THEN
  ASM_CASES_TAC `j0 = 0` THENL
   [PUFF_STEPS_TAC (2--4) THEN PTR_DECIDE_FLAGS_TAC THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[CARD_RESTRICT_LT_ADD1] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `~(j = 0) ==> ~(0 = j)`; ADD_CLAUSES];
      EXISTS_TAC `syms:int16 list` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `t:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `t:num = i` THENL [ASM_MESON_TAC[]; SIMPLE_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_sub stackpointer (word 32):int64`;
    `list_of_seq
      (\j. if j = 0 then o0
           else word(huffman_index lens j +
                     CARD {t | t < i /\ EL t lens = j}):int16) 16`;
    `j0:num`; `s1:armstate`] READ_MEMORY_WORDLIST16_SPLIT) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `j <= 15 ==> j < 16`] THEN
  ABBREV_TAC `c = CARD {t | t < i /\ EL t (lens:num list) = j0}` THEN
  ABBREV_TAC `r = huffman_rank lens i` THEN
  SUBGOAL_THEN `huffman_index lens j0 + c = r` (fun th -> REWRITE_TAC[th])
  THENL
   [MAP_EVERY EXPAND_TAC ["r"; "c"] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`lens:num list`; `i:num`] HUFFMAN_RANK) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `r < LENGTH(lens:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC HUFFMAN_RANK_LT_LENGTH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  PUFF_STEPS_TAC [2] THEN
  SXTW_ABBREV_TAC `X3` `w3v:int64` `j0:num` THEN
  PUFF_STEPS_TAC (3--6) THEN
  SXTW_ABBREV_TAC `X5` `w5v:int64` `r:num` THEN
  MP_TAC(ISPECL [`sym:int64`; `syms:int16 list`; `r:num`; `s6:armstate`]
                READ_MEMORY_WORDLIST16_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  PUFF_STEPS_TAC (7--9) THEN
  SUBGOAL_THEN `huffman_index lens j0 + c = r` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "c"] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`lens:num list`; `i:num`] HUFFMAN_RANK) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_sub stackpointer (word 32):int64`;
    `list_of_seq
      (\j. if j = 0 then o0
           else word(huffman_index lens j +
                     CARD {t | t < i /\ EL t lens = j}):int16) 16`;
    `list_of_seq
      (\j. if j = 0 then o0
           else word(huffman_index lens j +
                     CARD {t | t < i + 1 /\ EL t lens = j}):int16) 16`;
    `j0:num`; `s9:armstate`] READ_MEMORY_WORDLIST16_UPDATE) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `j <= 15 ==> j < 16`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CARD_RESTRICT_LT_ADD1] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `j0:num = m` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_MESON_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`sym:int64`; `syms:int16 list`;
    `list_of_seq (\m. if m = r then word i else EL m syms:int16)
                 (LENGTH(lens:num list))`;
    `r:num`; `s9:armstate`] READ_MEMORY_WORDLIST16_UPDATE) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN DISCH_TAC THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  EXISTS_TAC `list_of_seq (\m. if m = r then word i else EL m syms:int16)
                          (LENGTH(lens:num list))` THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `huffman_rank lens t < LENGTH(lens:num list)` ASSUME_TAC THENL
   [MATCH_MP_TAC HUFFMAN_RANK_LT_LENGTH THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  ASM_CASES_TAC `t:num = i` THENL
   [ASM_REWRITE_TAC[];
    COND_CASES_TAC THENL
     [MP_TAC(SPECL [`lens:num list`; `t:num`; `i:num`] HUFFMAN_RANK_INJ) THEN
      ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMPLE_ARITH_TAC]];;

(*** From 0x758, placing the symbols, to the return ***)

let CONSTRUCT_PHASE_D_TAC =
  GLOBALIZE_PRECONDITION_TAC THEN
  SUBGOAL_THEN `~(LENGTH(lens:num list) = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; ALL]; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `LENGTH(lens:num list)` `pc + 0x768` `pc + 0x78c`
    construct_place THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--4) THEN
    PUFF_FINAL_TAC THEN
    REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORDLIST16_FROM_MEMORY];
    CONSTRUCT_PLACE_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_EXISTS_PRE_TAC `syms:int16 list` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC [1] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    EXISTS_TAC `syms:int16 list` THEN ASM_REWRITE_TAC[];
    ENSURES_EXISTS_PRE_TAC `syms:int16 list` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--3) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[WORD_SUB_ADD; GSYM NOT_LE] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
    EXISTS_TAC `syms:int16 list` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[huffman_table; LENGTH_HUFFMAN_COUNTS] THEN
    SIMP_TAC[EL_HUFFMAN_COUNTS] THEN
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HUFFMAN_RANK_LT_LENGTH];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];;

(* ------------------------------------------------------------------------- *)
(* Given code lengths lens, all at most 15, in the array at len, and the     *)
(* table h, whose count array has room for 16 counts and whose symbol array  *)
(* has room for a symbol for each length, construct puts the counts of the   *)
(* lengths in the count array and, if the code is not over-subscribed,       *)
(* returns 0 if the code is complete or has no codes and 2^15 minus the      *)
(* Kraft sum otherwise, with the symbols in the order of their codes in the  *)
(* symbol array. If the code is over-subscribed it returns a negative        *)
(* number. It changes only x0 to x9 and the flags among the registers, which *)
(* puff relies on: gcc keeps a value in x10 across a call of construct. Its  *)
(* loads are from h, the code lengths, the count array and the array of      *)
(* offsets on the stack, and its stores are to the arrays of the table and   *)
(* the offsets.                                                              *)
(* ------------------------------------------------------------------------- *)

let PUFF_CONSTRUCT_CORRECT_MEMSAFE = prove
 (`!h cnt sym len lens pc returnaddress stackpointer e.
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     ALL (\x. x <= 15) lens /\ LENGTH lens <= 320 /\
     nonoverlapping (word pc,0x11d8) (cnt,32) /\
     nonoverlapping (word pc,0x11d8) (sym,2 * LENGTH lens) /\
     nonoverlapping (word pc,0x11d8) (word_sub stackpointer (word 32),32) /\
     nonoverlapping (cnt,32) (h,16) /\
     nonoverlapping (cnt,32) (len,2 * LENGTH lens) /\
     nonoverlapping (cnt,32) (sym,2 * LENGTH lens) /\
     nonoverlapping (cnt,32) (word_sub stackpointer (word 32),32) /\
     nonoverlapping (sym,2 * LENGTH lens) (h,16) /\
     nonoverlapping (sym,2 * LENGTH lens) (len,2 * LENGTH lens) /\
     nonoverlapping (sym,2 * LENGTH lens)
                    (word_sub stackpointer (word 32),32) /\
     nonoverlapping (word_sub stackpointer (word 32),32) (h,16) /\
     nonoverlapping (word_sub stackpointer (word 32),32)
                    (len,2 * LENGTH lens)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0x6a0) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [h; len; word(LENGTH lens)] s /\
               read (memory :> bytes64 h) s = cnt /\
               read (memory :> bytes64(word_add h (word 8))) s = sym /\
               read (memory :> bytes(len,2 * LENGTH lens)) s =
               num_of_wordlist(MAP (word:num->int16) lens) /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(cnt,32)) s =
               num_of_wordlist(huffman_counts lens) /\
               (huffman_kraft lens <= 2 EXP 15
                ==> read X0 s = word(if ALL (\x. x = 0) lens then 0
                                     else 2 EXP 15 - huffman_kraft lens) /\
                    ?syms. LENGTH syms = LENGTH lens /\
                           read (memory :> bytes(sym,2 * LENGTH lens)) s =
                           num_of_wordlist syms /\
                           huffman_table lens (huffman_counts lens) syms) /\
               (2 EXP 15 < huffman_kraft lens
                ==> ival(word_zx(read X0 s):int32) < &0) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [h,16; len,2 * LENGTH lens; cnt,32;
                       word_sub stackpointer (word 32),32]
                      [cnt,32; sym,2 * LENGTH lens;
                       word_sub stackpointer (word 32),32]))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(cnt,32);
                      memory :> bytes(sym,2 * LENGTH lens);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  GHOST_INTRO_TAC `o0:int16`
   `read (memory :> bytes16(word_sub stackpointer (word 32)))` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x6dc` construct_ab THEN CONJ_TAC THENL
   [CONSTRUCT_PHASE_A_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC construct_d THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
    CONSTRUCT_PHASE_BC_TAC; CONSTRUCT_PHASE_D_TAC]);;

(*** The same without the events ***)

let PUFF_CONSTRUCT_CORRECT = prove
 (`!h cnt sym len lens pc returnaddress stackpointer.
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     ALL (\x. x <= 15) lens /\ LENGTH lens <= 320 /\
     nonoverlapping (word pc,0x11d8) (cnt,32) /\
     nonoverlapping (word pc,0x11d8) (sym,2 * LENGTH lens) /\
     nonoverlapping (word pc,0x11d8) (word_sub stackpointer (word 32),32) /\
     nonoverlapping (cnt,32) (h,16) /\
     nonoverlapping (cnt,32) (len,2 * LENGTH lens) /\
     nonoverlapping (cnt,32) (sym,2 * LENGTH lens) /\
     nonoverlapping (cnt,32) (word_sub stackpointer (word 32),32) /\
     nonoverlapping (sym,2 * LENGTH lens) (h,16) /\
     nonoverlapping (sym,2 * LENGTH lens) (len,2 * LENGTH lens) /\
     nonoverlapping (sym,2 * LENGTH lens)
                    (word_sub stackpointer (word 32),32) /\
     nonoverlapping (word_sub stackpointer (word 32),32) (h,16) /\
     nonoverlapping (word_sub stackpointer (word 32),32)
                    (len,2 * LENGTH lens)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0x6a0) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [h; len; word(LENGTH lens)] s /\
               read (memory :> bytes64 h) s = cnt /\
               read (memory :> bytes64(word_add h (word 8))) s = sym /\
               read (memory :> bytes(len,2 * LENGTH lens)) s =
               num_of_wordlist(MAP (word:num->int16) lens))
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(cnt,32)) s =
               num_of_wordlist(huffman_counts lens) /\
               (huffman_kraft lens <= 2 EXP 15
                ==> read X0 s = word(if ALL (\x. x = 0) lens then 0
                                     else 2 EXP 15 - huffman_kraft lens) /\
                    ?syms. LENGTH syms = LENGTH lens /\
                           read (memory :> bytes(sym,2 * LENGTH lens)) s =
                           num_of_wordlist syms /\
                           huffman_table lens (huffman_counts lens) syms) /\
               (2 EXP 15 < huffman_kraft lens
                ==> ival(word_zx(read X0 s):int32) < &0))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(cnt,32);
                      memory :> bytes(sym,2 * LENGTH lens);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  EVENTS_FORGET_TAC PUFF_CONSTRUCT_CORRECT_MEMSAFE);;

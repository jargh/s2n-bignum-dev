(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function decode(s,h) of puff, at 0x830 in the image, which decodes a  *)
(* symbol from the stream with the canonical Huffman code given by the table *)
(* h. It tries the code lengths 1, 2, ..., 15 in turn, reading a bit at a    *)
(* time: the codes of length n are consecutive, from the first code of that  *)
(* length, so if the first n bits form one of them it returns its symbol,    *)
(* from the list of the symbols in the order of their codes. It returns -10  *)
(* if there is no code of length at most 15, and calls longjmp(s->env,1) if  *)
(* the input runs out first.                                                 *)
(*                                                                           *)
(* 0x0830:  ldr    x3, [x1]           0x0898:  ldrsh  w8, [x3], #2           *)
(* 0x0834:  mov    w10, #0x0          0x089c:  sub    w11, w4, w8            *)
(* 0x0838:  ldp    w6, w13, [x0, #48] 0x08a0:  cmp    w11, w5                *)
(* 0x083c:  add    x3, x3, #0x2       0x08a4:  b.lt   0x8cc                  *)
(* 0x0840:  mov    w5, #0x0           0x08a8:  add    w5, w5, w8             *)
(* 0x0844:  mov    w4, #0x0           0x08ac:  sub    w2, w2, #0x1           *)
(* 0x0848:  mov    w2, w13            0x08b0:  add    w10, w10, w8           *)
(* 0x084c:  mov    w7, #0x1           0x08b4:  lsl    w4, w4, #1             *)
(* 0x0850:  mov    w9, #0x10          0x08b8:  lsl    w5, w5, #1             *)
(* 0x0854:  mov    w12, #0x8          0x08bc:  add    w7, w7, #0x1           *)
(* 0x0858:  cbnz   w2, 0x88c          0x08c0:  b      0x858                  *)
(* 0x085c:  subs   w2, w9, w7         0x08c4:  mov    w0, #0xfffffff6        *)
(* 0x0860:  b.eq   0x8c4              0x08c8:  ret                           *)
(* 0x0864:  ldp    x8, x6, [x0, #32]  0x08cc:  ldr    x3, [x1, #8]           *)
(* 0x0868:  cmp    x6, x8             0x08d0:  sub    w1, w4, w5             *)
(* 0x086c:  b.eq   0x8ec              0x08d4:  add    w1, w1, w10            *)
(* 0x0870:  ldr    x8, [x0, #24]      0x08d8:  sub    w2, w13, w7            *)
(* 0x0874:  add    x11, x6, #0x1      0x08dc:  and    w2, w2, #0x7           *)
(* 0x0878:  str    x11, [x0, #40]     0x08e0:  stp    w6, w2, [x0, #48]      *)
(* 0x087c:  cmp    w2, #0x8           0x08e4:  ldrsh  w0, [x3, w1, sxtw #1]  *)
(* 0x0880:  csel   w2, w2, w12, le    0x08e8:  ret                           *)
(* 0x0884:  ldrb   w6, [x8, x6]       0x08ec:  stp    x29, x30, [sp, #-16]!  *)
(* 0x0888:  cbz    w2, 0x85c          0x08f0:  add    x0, x0, #0x38          *)
(* 0x088c:  and    w8, w6, #0x1       0x08f4:  mov    w1, #0x1               *)
(* 0x0890:  asr    w6, w6, #1         0x08f8:  mov    x29, sp                *)
(* 0x0894:  orr    w4, w8, w4         0x08fc:  bl     0x5a0 (longjmp)        *)
(* ========================================================================= *)

needs "arm/proofs/utils/puff.ml";;

(* ------------------------------------------------------------------------- *)
(* The proof is by a loop with early exits (ENSURES_LOOP_EXIT) whose         *)
(* invariant decode_inv i holds at 0x858 when trying the code length i + 1.  *)
(* Each iteration, for i < 15, gets a bit to read, loading a byte if the bit *)
(* buffer is empty, or calling longjmp if the input has run out, to reach    *)
(* decode_body at 0x88c, where it reads the bit and either finds a code of   *)
(* length i + 1 and returns its symbol or goes on to the next length. At     *)
(* length 16 it returns -10. The bit buffer holds the bits of the stream     *)
(* from position p + i to the end of the last byte read, of which w2 (left   *)
(* in the C code) are still to be used, at most 15 - i, and there is no code *)
(* of any length up to i at p.                                               *)
(* ------------------------------------------------------------------------- *)

let DECODE_INTRO_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x20018`] WORD_ADD; C_ARGUMENTS;
              puff_input; puff_table;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE_JMP_CONTEXT;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  MP_TAC(SPEC `p:num` PUFF_POS_BOUNDS) THEN
  ABBREV_TAC `ic0 = (p + 7) DIV 8` THEN
  ABBREV_TAC `bc0 = 8 * ic0 - p` THEN
  ABBREV_TAC `bb0 = deflate_bits l p bc0` THEN STRIP_TAC THEN
  SUBGOAL_THEN `bc0 < 8 /\ ic0 <= LENGTH(l:byte list) /\ bb0 < 2 EXP bc0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bb0"; "bc0"] THEN
    REWRITE_TAC[DEFLATE_BITS_BOUND] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP bc0 <= 2 EXP 7` MP_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC] THEN
  SUBGOAL_THEN `bb0 < 128` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  JMP_CONTEXT_INTRO_TAC;;

(*** The regions that decode reads and writes ***)

let decode_rr =
 `[st,368; inp,LENGTH(l:byte list); h,16; cnt,32;
   sym,2 * LENGTH(syms:int16 list); word pc,0x20320; ea,el]:(int64#num)list`
and decode_wr =
 `[word_add st (word 40),16;
   word_sub stackpointer (word 16),16]:(int64#num)list`;;

(*** The invariant at 0x858, for the code length i + 1 ***)

let decode_inv = with_memsafe decode_rr decode_wr `\i s.
  aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
  read PC s = word(pc + 0x858) /\
  read SP s = stackpointer /\ read X30 s = returnaddress /\
  read X19 s = ctx_x19 /\ read X20 s = ctx_x20 /\ read X21 s = ctx_x21 /\
  read X22 s = ctx_x22 /\ read X23 s = ctx_x23 /\ read X24 s = ctx_x24 /\
  read X25 s = ctx_x25 /\ read X26 s = ctx_x26 /\ read X27 s = ctx_x27 /\
  read X28 s = ctx_x28 /\ read X29 s = ctx_x29 /\
  read (Q8 :> bottomhalf) s = ctx_d8 /\ read (Q9 :> bottomhalf) s = ctx_d9 /\
  read (Q10 :> bottomhalf) s = ctx_d10 /\
  read (Q11 :> bottomhalf) s = ctx_d11 /\
  read (Q12 :> bottomhalf) s = ctx_d12 /\
  read (Q13 :> bottomhalf) s = ctx_d13 /\
  read (Q14 :> bottomhalf) s = ctx_d14 /\
  read (Q15 :> bottomhalf) s = ctx_d15 /\
  read X0 s = st /\ read X1 s = h /\
  read X3 s = word_add cnt (word(2 * (i + 1))) /\
  read X4 s = word(2 * deflate_codebits l p i) /\
  read X5 s = word(huffman_first lens (i + 1)) /\
  read X7 s = word(i + 1) /\ read X9 s = word 16 /\ read X12 s = word 8 /\
  read X10 s = word(huffman_index lens (i + 1)) /\
  read X13 s = word bc0 /\
  read X2 s = word(MIN (8 * (((p + i) + 7) DIV 8) - (p + i)) (15 - i)) /\
  read X6 s =
  word(deflate_bits l (p + i) (8 * (((p + i) + 7) DIV 8) - (p + i))) /\
  read (memory :> bytes64(word_add st (word 24))) s = inp /\
  read (memory :> bytes64(word_add st (word 32))) s = word(LENGTH l) /\
  read (memory :> bytes64(word_add st (word 40))) s =
  word(((p + i) + 7) DIV 8) /\
  read (memory :> bytes32(word_add st (word 48))) s = word bb0 /\
  read (memory :> bytes32(word_add st (word 52))) s = word bc0 /\
  read (memory :> bytes(inp,LENGTH l)) s = num_of_bytelist l /\
  read (memory :> bytes64 h) s = cnt /\
  read (memory :> bytes64(word_add h (word 8))) s = sym /\
  read (memory :> bytes(cnt,32)) s = num_of_wordlist(cnts:int16 list) /\
  read (memory :> bytes(sym,2 * LENGTH(syms:int16 list))) s =
  num_of_wordlist syms /\
  read (memory :> bytes(word_add st (word 56),312)) s =
  (enc:int64 list->num) ctx /\
  read (memory :> bytes64(word_add (word pc) (word 131096))) s = fl /\
  read (memory :> bytes(ea,el)) s = ev /\
  p + i <= 8 * LENGTH l /\
  (!m. 0 < m /\ m <= i
       ==> huffman_first lens m + huffman_count lens m <=
           deflate_codebits l p m) /\
  huffman_first lens (i + 1) <= 2 * deflate_codebits l p i`;;

(*** At 0x88c, with a bit to read for the code length i + 1 ***)

let decode_body = with_memsafe decode_rr decode_wr `\s.
  aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
  read PC s = word(pc + 0x88c) /\
  read SP s = stackpointer /\ read X30 s = returnaddress /\
  read X19 s = ctx_x19 /\ read X20 s = ctx_x20 /\ read X21 s = ctx_x21 /\
  read X22 s = ctx_x22 /\ read X23 s = ctx_x23 /\ read X24 s = ctx_x24 /\
  read X25 s = ctx_x25 /\ read X26 s = ctx_x26 /\ read X27 s = ctx_x27 /\
  read X28 s = ctx_x28 /\ read X29 s = ctx_x29 /\
  read (Q8 :> bottomhalf) s = ctx_d8 /\ read (Q9 :> bottomhalf) s = ctx_d9 /\
  read (Q10 :> bottomhalf) s = ctx_d10 /\
  read (Q11 :> bottomhalf) s = ctx_d11 /\
  read (Q12 :> bottomhalf) s = ctx_d12 /\
  read (Q13 :> bottomhalf) s = ctx_d13 /\
  read (Q14 :> bottomhalf) s = ctx_d14 /\
  read (Q15 :> bottomhalf) s = ctx_d15 /\
  read X0 s = st /\ read X1 s = h /\
  read X3 s = word_add cnt (word(2 * (i + 1))) /\
  read X4 s = word(2 * deflate_codebits l p i) /\
  read X5 s = word(huffman_first lens (i + 1)) /\
  read X7 s = word(i + 1) /\ read X9 s = word 16 /\ read X12 s = word 8 /\
  read X10 s = word(huffman_index lens (i + 1)) /\
  read X13 s = word bc0 /\
  read X2 s = word(MIN (8 * ((p + i) DIV 8 + 1) - (p + i)) (15 - i)) /\
  read X6 s =
  word(deflate_bits l (p + i) (8 * ((p + i) DIV 8 + 1) - (p + i))) /\
  read (memory :> bytes64(word_add st (word 24))) s = inp /\
  read (memory :> bytes64(word_add st (word 32))) s = word(LENGTH l) /\
  read (memory :> bytes64(word_add st (word 40))) s =
  word((p + i) DIV 8 + 1) /\
  read (memory :> bytes32(word_add st (word 48))) s = word bb0 /\
  read (memory :> bytes32(word_add st (word 52))) s = word bc0 /\
  read (memory :> bytes(inp,LENGTH l)) s = num_of_bytelist l /\
  read (memory :> bytes64 h) s = cnt /\
  read (memory :> bytes64(word_add h (word 8))) s = sym /\
  read (memory :> bytes(cnt,32)) s = num_of_wordlist(cnts:int16 list) /\
  read (memory :> bytes(sym,2 * LENGTH(syms:int16 list))) s =
  num_of_wordlist syms /\
  read (memory :> bytes(word_add st (word 56),312)) s =
  (enc:int64 list->num) ctx /\
  read (memory :> bytes64(word_add (word pc) (word 131096))) s = fl /\
  read (memory :> bytes(ea,el)) s = ev /\
  (p + i) DIV 8 + 1 <= LENGTH l /\
  (!m. 0 < m /\ m <= i
       ==> huffman_first lens m + huffman_count lens m <=
           deflate_codebits l p m) /\
  huffman_first lens (i + 1) <= 2 * deflate_codebits l p i`;;

(*** From the entry to the loop, with i = 0 ***)

let DECODE_ENTRY_TAC =
  PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--10) THEN
  PUFF_FINAL_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; deflate_codebits;
              HUFFMAN_FIRST_CLAUSES; HUFFMAN_INDEX_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `~(0 < m /\ m <= 0)`; LE_0] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MIN] THEN SIMPLE_ARITH_TAC;;

(*** From 0x858 to 0x88c, loading a byte if the bit buffer is empty ***)

let DECODE_HEAD_TAC =
  BETA_TAC THEN
  MP_TAC(SPEC `p + i:num` PUFF_POS_BOUNDS) THEN
  ABBREV_TAC `qq = p + i:num` THEN
  ABBREV_TAC `icq = (qq + 7) DIV 8` THEN
  ABBREV_TAC `nb = 8 * icq - qq` THEN
  ABBREV_TAC `bq = deflate_bits l qq nb` THEN STRIP_TAC THEN
  SUBGOAL_THEN `nb < 8 /\ bq < 2 EXP nb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bq"; "nb"] THEN
    REWRITE_TAC[DEFLATE_BITS_BOUND] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP nb <= 2 EXP 7` MP_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC] THEN
  SUBGOAL_THEN `bq < 128` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  PUFF_INIT_TAC "s0" THEN
  ASM_CASES_TAC `nb = 0` THENL
   [PUFF_STEPS_TAC (1--5) THEN
    ASM_CASES_TAC `icq = LENGTH(l:byte list)` THEN PTR_DECIDE_FLAGS_TAC THENL
     [PUFF_STEPS_TAC (6--12) THEN PUFF_ADRP_TAC THEN
      PUFF_STEPS_TAC (13--15) THEN
      PUFF_LONGJMP_TAC `word_add st (word 56):int64` `ctx:int64 list` 16 THEN
      PUFF_FINAL_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HUFFMAN_DECODE_NOT_FOUND THEN EXISTS_TAC `i + 1` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        SIMPLE_ARITH_TAC;
        DISJ2_TAC THEN SIMPLE_ARITH_TAC];
      PUFF_STEPS_TAC (6--11) THEN
      MP_TAC(SPECL [`inp:int64`; `l:byte list`; `icq:num`; `s11:armstate`]
                   READ_MEMORY_BYTES8_BYTELIST) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMPLE_ARITH_TAC];
        DISCH_TAC] THEN
      PUFF_STEPS_TAC (12--13) THEN
      PUFF_FINAL_TAC THEN DISJ1_TAC THEN
      MP_TAC(SPEC `qq:num` PUFF_POS_ZERO) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `8 * (icq + 1) - qq = 8` SUBST1_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `deflate_bits l qq 8 = val(EL icq (l:byte list))`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `qq = 8 * icq` SUBST1_TAC THENL
         [SIMPLE_ARITH_TAC; REWRITE_TAC[DEFLATE_BITS_BYTE]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[MIN] THEN SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC]];
    PUFF_STEPS_TAC [1] THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    MP_TAC(SPEC `qq:num` PUFF_POS_NONZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC];;

(*** From 0x88c, reading a bit: the code found, or back to 0x858 ***)

let DECODE_BODY_TAC =
  let is_b16 tm =
    can (find_term (fun u -> is_const u && fst(dest_const u) = "bytes16")) tm
  and rank_th = ASSUME
   `ix + (bt + 2 * cd) - fs =
    val(word_sx(word_zx(word((bt + 2 * cd) - fs + ix):int64):int32):int64)` in
  MP_TAC(SPEC `p + i:num` PUFF_POS_BOUNDS) THEN
  ABBREV_TAC `qq = p + i:num` THEN
  ABBREV_TAC `nb1 = 8 * (qq DIV 8 + 1) - qq` THEN
  ABBREV_TAC `bv = deflate_bits l qq nb1` THEN
  ABBREV_TAC `cd = deflate_codebits l p i` THEN
  ABBREV_TAC `fs = huffman_first lens (i + 1)` THEN
  ABBREV_TAC `cn = huffman_count lens (i + 1)` THEN
  ABBREV_TAC `ix = huffman_index lens (i + 1)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= nb1 /\ nb1 <= 8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "nb1" THEN MP_TAC(SPECL [`qq:num`; `8`] DIVISION) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `bv < 256` ASSUME_TAC THENL
   [EXPAND_TAC "bv" THEN TRANS_TAC LTE_TRANS `2 EXP nb1` THEN
    REWRITE_TAC[DEFLATE_BITS_BOUND; ARITH_RULE `256 = 2 EXP 8`; LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cd < 16384` ASSUME_TAC THENL
   [EXPAND_TAC "cd" THEN TRANS_TAC LTE_TRANS `2 EXP i` THEN
    REWRITE_TAC[DEFLATE_CODEBITS_BOUND; ARITH_RULE `16384 = 2 EXP 14`;
                LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fs + cn <= 32768` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fs"; "cn"] THEN
    TRANS_TAC LE_TRANS `2 EXP (i + 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HUFFMAN_FIRST_COUNT_BOUND THEN ASM_REWRITE_TAC[] THEN
      SIMPLE_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `32768 = 2 EXP 15`; LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cn <= 320 /\ ix <= 320` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cn"; "ix"] THEN
    MP_TAC(SPECL [`lens:num list`; `i + 1`] HUFFMAN_COUNT_LE_LENGTH) THEN
    MP_TAC(SPECL [`lens:num list`; `i + 1`] HUFFMAN_INDEX_LE_LENGTH) THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `qq:num`; `nb1:num`; `1`]
               DEFLATE_BITS_SPLIT) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `bt = deflate_bits l qq 1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `bt < 2` ASSUME_TAC THENL
   [EXPAND_TAC "bt" THEN
    MP_TAC(SPECL [`l:byte list`; `qq:num`; `1`] DEFLATE_BITS_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `deflate_codebits l p (i + 1) = bt + 2 * cd` ASSUME_TAC THENL
   [REWRITE_TAC[DEFLATE_CODEBITS_ADD; DEFLATE_CODEBITS_1] THEN
    ASM_REWRITE_TAC[EXP_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--3) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[huffman_table] o
    check (can (term_match [] `huffman_table a b c`) o concl)) THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
   (SPECL [`cnt:int64`; `cnts:int16 list`; `16`; `i + 1`; `s3:armstate`]
          READ_MEMORY_BYTES16_NUM_OF_WORDLIST)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
   [MATCH_MP th (UNDISCH(ARITH_RULE `i < 15 ==> i + 1 < 16`))]) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    REWRITE_RULE[ASSUME `huffman_count lens (i + 1) = cn`] o
    check (is_b16 o concl)) THEN
  PUFF_STEPS_TAC (4--6) THEN
  ASM_CASES_TAC `bt + 2 * cd < fs + cn` THEN W32_DECIDE_FLAGS_TAC THENL
   [PUFF_STEPS_TAC (7--13) THEN
    MP_TAC(SPECL [`l:byte list`; `lens:num list`; `p:num`; `i + 1`]
                 HUFFMAN_DECODE_FOUND) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN ANTS_TAC THENL
     [MP_TAC(SPECL [`qq:num`; `8`] DIVISION) THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `sv:num` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     `huffman_rank lens sv < LENGTH(syms:int16 list) /\
      EL (huffman_rank lens sv) syms = word sv`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match []
         `!t. t < LENGTH lens /\ ~(EL t lens = 0) ==> P t`) (concl th))) THEN
      UNDISCH_TAC `huffman_decode l lens p sv (p + i + 1)` THEN
      SIMP_TAC[huffman_decode];
      ALL_TAC] THEN
    MP_TAC(SPECL [`sym:int64`; `syms:int16 list`; `LENGTH(syms:int16 list)`;
                  `huffman_rank lens sv`; `s13:armstate`]
                 READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN (concl rank_th) ASSUME_TAC THENL
     [W(fun (asl,w) ->
        MP_TAC(PART_MATCH (lhand o rand) VAL_SXTW_SMALL (rand w))) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_b16 (concl th) && free_in `sym:int64` (concl th)
      then ASSUME_TAC(REWRITE_RULE[rank_th] th) else failwith "") THEN
    PUFF_STEPS_TAC (14--15) THEN SMALL_WORD_TAC THEN
    PUFF_FINAL_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`sv:num`; `p + i + 1`] THEN
    REWRITE_TAC[puff_input; jmp_context] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p + i + 1 = qq + 1` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[PUFF_POS_SUCC] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sv < 320` ASSUME_TAC THENL
     [UNDISCH_TAC `huffman_decode l lens p sv (p + i + 1)` THEN
      REWRITE_TAC[huffman_decode] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [W(fun (asl,w) -> CONV_TAC(SMALL_WORD_CONV asl));
      REPEAT AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      AP_TERM_TAC THEN
      MP_TAC(SPECL [`p:num`; `i:num`; `ic0:num`] PUFF_BITCNT_MOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMPLE_ARITH_TAC];
    PUFF_STEPS_TAC (7--14) THEN
    PUFF_FINAL_TAC THEN DISJ1_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `p + i + 1 = qq + 1` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[PUFF_POS_SUCC] THEN
    MAP_EVERY (fun th ->
      REWRITE_TAC[MATCH_MP (CONJUNCT2(CONJUNCT2(SPEC `lens:num list` th)))
                           (ARITH_RULE `~(i + 1 = 0)`)])
     [HUFFMAN_INDEX_CLAUSES; HUFFMAN_FIRST_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      REPEAT AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC;
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `m = i + 1` THENL
       [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC];
      SIMPLE_ARITH_TAC]];;

(*** At 0x858 for the code length 16, returning -10 ***)

let DECODE_LAST_TAC =
  PUFF_INIT_TAC "s0" THEN PUFF_STEPS_TAC (1--5) THEN
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN
  ASM_REWRITE_TAC[jmp_context] THEN CONV_TAC WORD_REDUCE_CONV THEN
  MATCH_MP_TAC HUFFMAN_DECODE_NOT_FOUND THEN EXISTS_TAC `16` THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Given the state of the input at st, with the stream read up to position   *)
(* p, and the table at h for a code with code lengths lens, all at most 15,  *)
(* whose Kraft sum is at most 2^15, either decode returns the symbol decoded *)
(* at p, and reads up to the end of its code, or there is no symbol at p and *)
(* it returns -10 or calls longjmp with the context ctx saved in the jmp_buf *)
(* of the state. Its loads are from the state, the input, the table (h and   *)
(* its arrays), the image and the region (ea,el) of longjmp, and its stores  *)
(* are to the fields incnt, bitbuf and bitcnt of the state and its stack     *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let PUFF_DECODE_CORRECT_MEMSAFE = prove
 (`!st h cnt sym lens cnts syms l inp p fl ea el ev enc ctx ctx0
    pc returnaddress stackpointer e.
     longjmp_contract fl ea el ev enc /\
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     p <= 8 * LENGTH l /\ LENGTH l < 2 EXP 60 /\
     ALL (\n. n <= 15) lens /\ LENGTH lens <= 320 /\
     huffman_kraft lens <= 2 EXP 15 /\ huffman_table lens cnts syms /\
     LENGTH syms <= 320 /\
     nonoverlapping (word pc,0x20320) (st,368) /\
     nonoverlapping (word pc,0x20320) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (st,368) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_add st (word 40),16) /\
     nonoverlapping (inp,LENGTH l) (word_add st (word 40),16) /\
     nonoverlapping (h,16) (word_add st (word 40),16) /\
     nonoverlapping (cnt,32) (word_add st (word 40),16) /\
     nonoverlapping (sym,2 * LENGTH syms) (word_add st (word 40),16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0x830) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               jmp_context s = ctx0 /\
               C_ARGUMENTS [st; h] s /\
               puff_input st inp l p s /\
               puff_table h cnt sym cnts syms s /\
               read (memory :> bytes(word_add st (word 56),312)) s = enc ctx /\
               read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. ((?c q. huffman_decode l lens p c q /\
                       read PC s = returnaddress /\ jmp_context s = ctx0 /\
                       read X0 s = word c /\ puff_input st inp l q s) \/
                ~(?c q. huffman_decode l lens p c q) /\
                (read PC s = returnaddress /\ jmp_context s = ctx0 /\
                 word_zx(read X0 s):int32 = word 4294967286 \/
                 read PC s = EL 11 ctx /\ jmp_context s = ctx /\
                 word_zx(read X0 s):int32 = word 1)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [st,368; inp,LENGTH l; h,16; cnt,32;
                       sym,2 * LENGTH syms; word pc,0x20320; ea,el]
                      [word_add st (word 40),16;
                       word_sub stackpointer (word 16),16]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE_JMP_CONTEXT ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16);
                      memory :> bytes(word_add st (word 40),16)])`,
  DECODE_INTRO_TAC THEN
  MATCH_MP_TAC(ISPECL [`15`; decode_inv] ENSURES_LOOP_EXIT) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    SUBSUMED_ID_MAYCHANGE_TAC;
    DECODE_ENTRY_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_SEQUENCE_EXIT THEN EXISTS_TAC decode_body THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC;
      DECODE_HEAD_TAC; DECODE_BODY_TAC];
    DECODE_LAST_TAC]);;

(*** The same without the events ***)

let PUFF_DECODE_CORRECT = prove
 (`!st h cnt sym lens cnts syms l inp p fl ea el ev enc ctx ctx0
    pc returnaddress stackpointer.
     longjmp_contract fl ea el ev enc /\
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     p <= 8 * LENGTH l /\ LENGTH l < 2 EXP 60 /\
     ALL (\n. n <= 15) lens /\ LENGTH lens <= 320 /\
     huffman_kraft lens <= 2 EXP 15 /\ huffman_table lens cnts syms /\
     LENGTH syms <= 320 /\
     nonoverlapping (word pc,0x20320) (st,368) /\
     nonoverlapping (word pc,0x20320) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (st,368) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_add st (word 40),16) /\
     nonoverlapping (inp,LENGTH l) (word_add st (word 40),16) /\
     nonoverlapping (h,16) (word_add st (word 40),16) /\
     nonoverlapping (cnt,32) (word_add st (word 40),16) /\
     nonoverlapping (sym,2 * LENGTH syms) (word_add st (word 40),16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0x830) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               jmp_context s = ctx0 /\
               C_ARGUMENTS [st; h] s /\
               puff_input st inp l p s /\
               puff_table h cnt sym cnts syms s /\
               read (memory :> bytes(word_add st (word 56),312)) s = enc ctx /\
               read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. (?c q. huffman_decode l lens p c q /\
                      read PC s = returnaddress /\ jmp_context s = ctx0 /\
                      read X0 s = word c /\ puff_input st inp l q s) \/
               ~(?c q. huffman_decode l lens p c q) /\
               (read PC s = returnaddress /\ jmp_context s = ctx0 /\
                word_zx(read X0 s):int32 = word 4294967286 \/
                read PC s = EL 11 ctx /\ jmp_context s = ctx /\
                word_zx(read X0 s):int32 = word 1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE_JMP_CONTEXT ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16);
                      memory :> bytes(word_add st (word 40),16)])`,
  EVENTS_FORGET_TAC PUFF_DECODE_CORRECT_MEMSAFE);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The function bits(s,need) of puff, at 0x7a0 in the image, which returns   *)
(* the next need bits of the stream as a number, read from the least         *)
(* significant bit of each byte, loading bytes into the bit buffer as needed *)
(* and calling longjmp(s->env,1) if the input runs out first.                *)
(*                                                                           *)
(* 0x07a0:  ldp     w3, w2, [x0, #48] 0x07e4:  orr     x5, x5, x3            *)
(* 0x07a4:  mov     x4, x0            0x07e8:  cmp     w2, w1                *)
(* 0x07a8:  sxtw    x5, w3            0x07ec:  b.lt    0x7bc                 *)
(* 0x07ac:  cmp     w1, w2            0x07f0:  mov     w3, w5                *)
(* 0x07b0:  b.le    0x7f4             0x07f4:  mov     x0, #0x1              *)
(* 0x07b4:  ldp     x7, x3, [x0, #32] 0x07f8:  sub     w2, w2, w1            *)
(* 0x07b8:  b       0x7c0             0x07fc:  lsl     x0, x0, x1            *)
(* 0x07bc:  mov     x3, x0            0x0800:  sub     w0, w0, #0x1          *)
(* 0x07c0:  cmp     x7, x3            0x0804:  asr     x5, x5, x1            *)
(* 0x07c4:  b.eq    0x814             0x0808:  and     w0, w0, w3            *)
(* 0x07c8:  ldr     x6, [x4, #24]     0x080c:  stp     w5, w2, [x4, #48]     *)
(* 0x07cc:  add     x0, x3, #0x1      0x0810:  ret                           *)
(* 0x07d0:  str     x0, [x4, #40]     0x0814:  stp     x29, x30, [sp, #-16]! *)
(* 0x07d4:  ldrb    w3, [x6, x3]      0x0818:  add     x0, x4, #0x38         *)
(* 0x07d8:  lsl     x3, x3, x2        0x081c:  mov     w1, #0x1              *)
(* 0x07dc:  add     w2, w2, #0x8      0x0820:  mov     x29, sp               *)
(* 0x07e0:  str     w2, [x4, #52]     0x0824:  bl      0x5a0 (longjmp)       *)
(* ========================================================================= *)

needs "arm/proofs/utils/puff.ml";;

(* ------------------------------------------------------------------------- *)
(* The proof is by cases on the number of bytes loaded (0, 1 or 2, as need   *)
(* is at most 16 and at least one bit of the last byte read is left) and on  *)
(* whether the input runs out first. The bit buffer holds bc bits, the value *)
(* bb, from position p, and ic bytes have been read.                         *)
(* ------------------------------------------------------------------------- *)

let BITS_INTRO_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x20018`] WORD_ADD; C_ARGUMENTS; puff_input;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE_JMP_CONTEXT;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  MP_TAC(SPEC `p:num` PUFF_POS_BOUNDS) THEN
  ABBREV_TAC `ic = (p + 7) DIV 8` THEN
  ABBREV_TAC `bc = 8 * ic - p` THEN
  ABBREV_TAC `bb = deflate_bits l p bc` THEN STRIP_TAC THEN
  SUBGOAL_THEN `bc < 8 /\ ic <= LENGTH(l:byte list) /\ bb < 2 EXP bc`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bb"; "bc"] THEN REWRITE_TAC[DEFLATE_BITS_BOUND] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP bc <= 2 EXP 7 /\ 2 EXP need <= 2 EXP 16 /\ 0 < 2 EXP need`
  MP_TAC THENL
   [REWRITE_TAC[LE_EXP; EXP_LT_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN STRIP_TAC] THEN
  SUBGOAL_THEN `bb < 128` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  JMP_CONTEXT_INTRO_TAC THEN PUFF_INIT_TAC "s0";;

(*** The byte at index i of the input, before the load at step n ***)

let BITS_BYTE_TAC i n =
  let s = mk_var("s"^string_of_int(n - 1),`:armstate`) in
  MP_TAC(SPECL [`inp:int64`; `l:byte list`; i; s]
                READ_MEMORY_BYTES8_BYTELIST) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMPLE_ARITH_TAC]; DISCH_TAC];;

(*** After an OR, the accumulated value as bits of the stream ***)

let BITS_ACC_TAC n i =
  let n8 = mk_binop `(+):num->num->num` n `8` in
  MP_TAC(SPECL [`l:byte list`; `p:num`; n; i] DEFLATE_BITS_EXTEND) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE
     [REWRITE_RULE[ASSUME `deflate_bits l p bc = bb`] th])) THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; n8] DEFLATE_BITS_BOUND) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
    (list_mk_comb(`deflate_bits`,[`l:byte list`; `p:num`; n8])) `16777216`)
  ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS (mk_comb(`(EXP) 2`,n8)) THEN
    REWRITE_TAC[DEFLATE_BITS_BOUND] THEN
    REWRITE_TAC[ARITH_RULE `16777216 = 2 EXP 24`; LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let BITS_EXIT_TAC m i =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  SUBGOAL_THEN (mk_eq(`((p + need) + 7) DIV 8`,i)) SUBST1_TAC THENL
   [MATCH_MP_TAC PUFF_POS_DIV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(mk_binop `(-):num->num->num`
           (mk_binop `( * ):num->num->num` `8` i) `p + need`,
          mk_binop `(-):num->num->num` m `need:num`))
  SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; m; `need:num`] DEFLATE_BITS_SPLIT) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN
   (ASSUME_TAC o REWRITE_RULE[ASSUME `deflate_bits l p bc = bb`])) THEN
  ASM_REWRITE_TAC[jmp_context] THEN SIMPLE_ARITH_TAC;;

let BITS_ESCAPE_TAC n =
  PUFF_STEPS_TAC (n--(n+6)) THEN PUFF_ADRP_TAC THEN
  PUFF_STEPS_TAC ((n+7)--(n+9)) THEN
  PUFF_LONGJMP_TAC `word_add st (word 56):int64` `ctx:int64 list` (n+10) THEN
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMPLE_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Given the state of the input at st, with the stream read up to position   *)
(* p, either there are need more bits in it, and bits returns them and reads *)
(* up to p + need, or it calls longjmp with the context ctx saved in the     *)
(* jmp_buf of the state. Either way, its loads are from the state, the       *)
(* input, the image (the GOT entry of longjmp) and the region (ea,el) of     *)
(* longjmp, and its stores are to the fields incnt, bitbuf and bitcnt of the *)
(* state and its stack frame.                                                *)
(* ------------------------------------------------------------------------- *)

let PUFF_BITS_CORRECT_MEMSAFE = prove
 (`!st need l inp p fl ea el ev enc ctx ctx0 pc returnaddress stackpointer
    e.
     longjmp_contract fl ea el ev enc /\
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     need <= 16 /\ p <= 8 * LENGTH l /\ LENGTH l < 2 EXP 60 /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc,0x20320) (st,368) /\
     nonoverlapping (word pc,0x20320) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (st,368) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_add st (word 40),16) /\
     nonoverlapping (inp,LENGTH l) (word_add st (word 40),16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0x7a0) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               jmp_context s = ctx0 /\
               C_ARGUMENTS [st; word need] s /\
               puff_input st inp l p s /\
               read (memory :> bytes(word_add st (word 56),312)) s = enc ctx /\
               read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. (p + need <= 8 * LENGTH l /\
                read PC s = returnaddress /\ jmp_context s = ctx0 /\
                read X0 s = word(deflate_bits l p need) /\
                puff_input st inp l (p + need) s \/
                8 * LENGTH l < p + need /\
                read PC s = EL 11 ctx /\ jmp_context s = ctx /\
                word_zx(read X0 s):int32 = word 1) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [st,368; inp,LENGTH l; word pc,0x20320; ea,el]
                      [word_add st (word 40),16;
                       word_sub stackpointer (word 16),16]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE_JMP_CONTEXT ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16);
                      memory :> bytes(word_add st (word 40),16)])`,
  BITS_INTRO_TAC THEN PUFF_STEPS_TAC (1--4) THEN
  ASM_CASES_TAC `need <= bc` THEN W32_DECIDE_FLAGS_TAC THENL
   [PUFF_STEPS_TAC (5--13) THEN BITS_EXIT_TAC `bc:num` `ic:num`; ALL_TAC] THEN
  PUFF_STEPS_TAC (5--8) THEN
  ASM_CASES_TAC `ic = LENGTH(l:byte list)` THEN PTR_DECIDE_FLAGS_TAC THENL
   [BITS_ESCAPE_TAC 9; ALL_TAC] THEN
  PUFF_STEPS_TAC (9--12) THEN BITS_BYTE_TAC `ic:num` 13 THEN
  PUFF_STEPS_TAC (13--17) THEN BITS_ACC_TAC `bc:num` `ic:num` THEN
  PUFF_STEPS_TAC [18] THEN
  ASM_CASES_TAC `bc + 8 < need` THEN W32_DECIDE_FLAGS_TAC THENL
   [ALL_TAC;
    PUFF_STEPS_TAC (19--28) THEN BITS_EXIT_TAC `bc + 8` `ic + 1`] THEN
  PUFF_STEPS_TAC (19--21) THEN
  ASM_CASES_TAC `ic + 1 = LENGTH(l:byte list)` THEN PTR_DECIDE_FLAGS_TAC THENL
   [BITS_ESCAPE_TAC 22; ALL_TAC] THEN
  PUFF_STEPS_TAC (22--25) THEN BITS_BYTE_TAC `ic + 1` 26 THEN
  PUFF_STEPS_TAC (26--30) THEN BITS_ACC_TAC `bc + 8` `ic + 1` THEN
  PUFF_STEPS_TAC (31--41) THEN BITS_EXIT_TAC `(bc + 8) + 8` `(ic + 1) + 1`);;

(*** The same without the events ***)

let PUFF_BITS_CORRECT = prove
 (`!st need l inp p fl ea el ev enc ctx ctx0 pc returnaddress stackpointer.
     longjmp_contract fl ea el ev enc /\
     aligned 4096 (word pc:int64) /\ pc + 0x20320 <= 2 EXP 64 /\
     need <= 16 /\ p <= 8 * LENGTH l /\ LENGTH l < 2 EXP 60 /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc,0x20320) (st,368) /\
     nonoverlapping (word pc,0x20320) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (st,368) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_sub stackpointer (word 16),16) /\
     nonoverlapping (ea,el) (word_add st (word 40),16) /\
     nonoverlapping (inp,LENGTH l) (word_add st (word 40),16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc /\
               read PC s = word(pc + 0x7a0) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               jmp_context s = ctx0 /\
               C_ARGUMENTS [st; word need] s /\
               puff_input st inp l p s /\
               read (memory :> bytes(word_add st (word 56),312)) s = enc ctx /\
               read (memory :> bytes64(word(pc + 0x20018))) s = fl /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. p + need <= 8 * LENGTH l /\
               read PC s = returnaddress /\ jmp_context s = ctx0 /\
               read X0 s = word(deflate_bits l p need) /\
               puff_input st inp l (p + need) s \/
               8 * LENGTH l < p + need /\
               read PC s = EL 11 ctx /\ jmp_context s = ctx /\
               word_zx(read X0 s):int32 = word 1)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE_JMP_CONTEXT ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16);
                      memory :> bytes(word_add st (word 40),16)])`,
  EVENTS_FORGET_TAC PUFF_BITS_CORRECT_MEMSAFE);;

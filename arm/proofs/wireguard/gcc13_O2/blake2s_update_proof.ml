(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of blake2s_update_spec.ml, by cases on the length of *)
(* the input: none, filling at most the buffer, filling it and then 1 to 64  *)
(* more bytes, and filling it and then more, with the transitions of the     *)
(* state given by BLAKE2S_UPDATE_SMALL and BLAKE2S_UPDATE_LARGE in           *)
(* common/wireguard_kernel.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;

let WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "blake2s_update"; layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* The two calls of blake2s_compress_generic: one block of the buffer, and   *)
(* nb blocks of the input, both with the increment 64.                       *)
(* ------------------------------------------------------------------------- *)

let BLAKE2S_COMPRESS_ONE_BLOCK =
  let th = SPECL [`st:int64`; `blk:int64`; `word 1:int64`; `word 64:int64`]
     WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT in
  GENL [`st:int64`; `blk:int64`]
   (CONV_RULE (DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
               DEPTH_CONV WORD_RED_CONV THENC
               DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
               REWRITE_CONV[MULT_CLAUSES; LE_REFL]) th);;

let BLAKE2S_COMPRESS_BLOCKS64 =
  let th = SPECL [`st:int64`; `blk:int64`; `nb:int64`; `word 64:int64`]
     WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT in
  GENL [`st:int64`; `blk:int64`; `nb:int64`]
   (CONV_RULE (DEPTH_CONV WORD_RED_CONV THENC
               DEPTH_CONV VAL_WORD_NUMERAL_CONV) th);;

let BLAKE2S_COMPRESS_ONE_BLOCK_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,BLAKE2S_COMPRESS_ONE_BLOCK);;

let BLAKE2S_COMPRESS_BLOCKS64_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,BLAKE2S_COMPRESS_BLOCKS64);;

(* The 8 facts for the state words h in state s from the fact with a         *)
(* quantifier, and conversely the fact with a quantifier from the 8 facts,   *)
(* for the words h i.                                                        *)

let BLAKE2S_H_EXPAND_TAC s =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && can (find_term ((=) s)) (concl th))) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

let BLAKE2S_H_COLLECT_TAC s h =
  SUBGOAL_THEN
   (subst [s,`s:armstate`; h,`h:num->int32`]
     `!i. i < 8 ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s =
                    (h:num->int32) i`)
  ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC];;

(* The final steps: the new state words agree with the specification, as     *)
(* given by the transition lemma, and the frame.                             *)

let BLAKE2S_UPDATE_FINAL_TAC =
  REWRITE_TAC[wg_agree] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `inp:int64`; `inlen:int64`; `h0:num->int32`;
    `d:byte list`; `m:byte list`; `outlen:num`; `mcpy:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 336 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "memcpy" o REWRITE_RULE[memcpy_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            (19--29) THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  REWRITE_TAC[blake2s_state_at] THEN
  MP_TAC(ISPEC `d:byte list` BLAKE2S_BUFLEN) THEN
  ABBREV_TAC `n = blake2s_nblocks d` THEN ABBREV_TAC `b = blake2s_buflen d` THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 272):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN BLAKE2S_H_EXPAND_TAC `s0:armstate` THEN
  ARM_STEPS_TAC EXEC (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `b:num` WG_FILL_WORD)
                                 (ASSUME `b <= 64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `b:num` WG_WORD_ZX_SMALL)
    (MP (ARITH_RULE `b <= 64 ==> b < 2 EXP 32`) (ASSUME `b <= 64`))]) THEN
  ASM_CASES_TAC `val(inlen:int64) = 0` THENL

   [(*** An empty input: nothing to do ***)

    SUBGOAL_THEN `m:byte list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    WG_PC_REWRITE_TAC[ASSUME `val(inlen:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (11--15) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[APPEND_NIL] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN

  WG_PC_REWRITE_TAC[ASSUME `~(val(inlen:int64) = 0)`] THEN
  ARM_STEPS_TAC EXEC (11--15) THEN
  WG_PC_REWRITE_TAC[MP (SPEC `64 - b` WG_VAL_WORD_SMALL)
                       (ARITH_RULE `64 - b < 2 EXP 64`)] THEN
  ASM_CASES_TAC `64 - b < val(inlen:int64)` THENL
   [ALL_TAC;

    (*** The input fits in the buffer: copy it there ***)

    WG_PC_REWRITE_TAC[ASSUME `~(64 - b < val(inlen:int64))`] THEN
    ARM_STEPS_TAC EXEC (16--17) THEN
    SUBGOAL_THEN
     `~(64 <= val(inlen:int64) /\ ~(val(word_sub inlen (word 64)) = 0))`
     (fun th -> WG_PC_REWRITE_TAC[th]) THENL
     [ASM_CASES_TAC `64 <= val(inlen:int64)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inlen:int64 = word 64` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC `64 <= val(inlen:int64)` THEN
        UNDISCH_TAC `~(64 - b < val(inlen:int64))` THEN ARITH_TAC;
        CONV_TAC WORD_REDUCE_CONV];
      ALL_TAC] THEN
    ARM_STEPS_TAC EXEC (18--22) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `b:num` WG_WORD_ZX_SMALL)
      (MP (ARITH_RULE `b <= 64 ==> b < 2 EXP 32`) (ASSUME `b <= 64`))]) THEN
    WG_PLT_TAC EXEC 22 THEN
    WG_CALL_TAC "memcpy" EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist m`;
      `read X30 s`] 27 THEN
    ARM_STEPS_TAC EXEC (28--35) THEN
    MP_TAC(SPECL [`h0:num->int32`; `d:byte list`; `m:byte list`]
      BLAKE2S_UPDATE_SMALL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(64 - b < val(inlen:int64))` THEN
      UNDISCH_TAC `b <= 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[wg_agree] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
    ABBREV_TAC `l = val(inlen:int64)` THEN CONJ_TAC THENL
     [ALL_TAC; REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `LENGTH(SUB_LIST(64 * n,b) (d:byte list)) = b`
      ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN
        UNDISCH_TAC `LENGTH(d:byte list) = 64 * n + b` THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`word_add st (word 48):int64`;
                     `SUB_LIST(64 * n,b) (d:byte list)`;
                     `m:byte list`; `l:num`; `s35:armstate`]
                    WG_READ_BYTES_APPEND) THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      EXPAND_TAC "l" THEN MATCH_MP_TAC WG_BUFLEN_ADD THEN
      UNDISCH_TAC `~(64 - b < l)` THEN UNDISCH_TAC `val(inlen:int64) = l` THEN
      UNDISCH_TAC `b <= 64` THEN ARITH_TAC]] THEN

  (*** The input fills the buffer: copy the bytes that fill it ***)

  WG_PC_REWRITE_TAC[ASSUME `64 - b < val(inlen:int64)`] THEN
  ARM_STEPS_TAC EXEC (16--18) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `b:num` WG_WORD_ZX_SMALL)
    (MP (ARITH_RULE `b <= 64 ==> b < 2 EXP 32`) (ASSUME `b <= 64`))]) THEN
  WG_PLT_TAC EXEC 18 THEN
  ASSUME_TAC(MP (SPEC `64 - b` WG_VAL_WORD_SMALL)
                (ARITH_RULE `64 - b < 2 EXP 64`)) THEN
  MP_TAC(ISPECL [`inp:int64`; `m:byte list`; `val(inlen:int64)`; `0`; `64 - b`;
                 `s22:armstate`] WG_READ_BYTES_SUBLIST) THEN
  ASM_REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `64 - b < val(inlen:int64)` THEN ARITH_TAC; DISCH_TAC] THEN
  WG_CALL_TAC "memcpy" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `num_of_bytelist(SUB_LIST(0,64 - b) m)`; `read X30 s`] 23 THEN

  (*** Compress the buffer ***)

  ARM_STEPS_TAC EXEC (24--29) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add st (word 48),64)) s29 =
    num_of_bytelist(APPEND (SUB_LIST(64 * n,b) d)
                           (SUB_LIST(0,64 - b) (m:byte list)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH(SUB_LIST(64 * n,b) (d:byte list)) = b`
    ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN
      UNDISCH_TAC `LENGTH(d:byte list) = 64 * n + b` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`word_add st (word 48):int64`;
                   `SUB_LIST(64 * n,b) (d:byte list)`;
                   `SUB_LIST(0,64 - b) (m:byte list)`; `64 - b`;
                   `s29:armstate`] WG_READ_BYTES_APPEND) THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `b <= 64 ==> b + (64 - b) = 64`];
    ALL_TAC] THEN
  BLAKE2S_H_COLLECT_TAC `s29:armstate` `blake2s_chain h0 d` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WG_BYTES64_SPLIT o check (fun th ->
    concl th =
    `read (memory :> bytes64 (word_add st (word 40))) s29 = word 0`)) THEN
  CONV_TAC(LAND_CONV(WG_ADDR_CONV THENC WORD_REDUCE_CONV)) THEN STRIP_TAC THEN
  BLAKE2S_COMPRESS_ONE_BLOCK_TAC
   [`st:int64`; `read X1 s`; `word(64 * n):int64`; `blake2s_chain h0 d`;
    `APPEND (SUB_LIST(64 * n,b) d) (SUB_LIST(0,64 - b) (m:byte list))`;
    `F`; `pc:num`; `read SP s`; `read X30 s`] 30 THEN
  BLAKE2S_H_EXPAND_TAC `s30:armstate` THEN
  ARM_STEPS_TAC EXEC (31--34) THEN

  (*** The rest r of the input, more than the bytes filling the buffer ***)

  SUBGOAL_THEN
   `word_sub inlen (word(64 - b)):int64 = word(val inlen - (64 - b))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WG_WORD_SUB_VAL THEN
    UNDISCH_TAC `64 - b < val(inlen:int64)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = val(inlen:int64) - (64 - b)` THEN
  SUBGOAL_THEN `r < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MP_TAC(ISPEC `inlen:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  WG_PC_REWRITE_TAC[MP (SPEC `r:num` WG_VAL_WORD_SMALL)
                       (ASSUME `r < 2 EXP 64`)] THEN
  ASSUME_TAC(MP (SPEC `r:num` WG_VAL_WORD_SMALL) (ASSUME `r < 2 EXP 64`)) THEN
  ASM_CASES_TAC `r <= 64` THENL

   [(*** At most 64 bytes left: copy them to the buffer ***)

    SUBGOAL_THEN `~(64 <= r /\ ~(val(word_sub (word r) (word 64):int64) = 0))`
     (fun th -> WG_PC_REWRITE_TAC[th]) THENL
     [ASM_CASES_TAC `64 <= r` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `r = 64` SUBST1_TAC THENL
       [UNDISCH_TAC `64 <= r` THEN UNDISCH_TAC `r <= 64` THEN ARITH_TAC;
        CONV_TAC WORD_REDUCE_CONV];
      ALL_TAC] THEN
    ARM_STEPS_TAC EXEC (35--39) THEN
    WG_PLT_TAC EXEC 39 THEN
    MP_TAC(ISPECL [`inp:int64`; `m:byte list`; `val(inlen:int64)`; `64 - b`;
                   `r:num`; `s43:armstate`] WG_READ_BYTES_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `val(inlen:int64) - (64 - b) = r` THEN
      UNDISCH_TAC `64 - b < val(inlen:int64)` THEN ARITH_TAC;
      DISCH_TAC] THEN
    WG_CALL_TAC "memcpy" EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`;
      `num_of_bytelist(SUB_LIST(64 - b,r) m)`; `read X30 s`] 44 THEN
    ARM_STEPS_TAC EXEC (45--52) THEN
    MP_TAC(SPECL [`h0:num->int32`; `d:byte list`; `m:byte list`; `0`]
      BLAKE2S_UPDATE_LARGE) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN ANTS_TAC THENL
     [UNDISCH_TAC `val(inlen:int64) - (64 - b) = r` THEN
      UNDISCH_TAC `64 - b < val(inlen:int64)` THEN UNDISCH_TAC `r <= 64` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[blake2s_compress_blocks] THEN ASM_REWRITE_TAC[] THEN
    BLAKE2S_UPDATE_FINAL_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; LEFT_ADD_DISTRIB; MULT_CLAUSES];
      MATCH_MP_TAC WG_BUFLEN_ZX THEN ASM_REWRITE_TAC[]];

    (*** More: compress all the complete blocks but the last, and copy the ***)
    (*** last 1 to 64 bytes to the buffer                                  ***)

    SUBGOAL_THEN `64 <= r /\ ~(val(word_sub (word r) (word 64):int64) = 0)`
     (fun th -> WG_PC_REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL [UNDISCH_TAC `~(r <= 64)` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word_sub (word r) (word 64):int64 = word(r - 64)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC WG_WORD_SUB_LE THEN UNDISCH_TAC `~(r <= 64)` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `r - 64 < 2 EXP 64`
       (fun th -> REWRITE_TAC[MATCH_MP WG_VAL_WORD_SMALL th]) THENL
       [UNDISCH_TAC `r < 2 EXP 64` THEN ARITH_TAC;
        UNDISCH_TAC `~(r <= 64)` THEN ARITH_TAC];
      ALL_TAC] THEN
    ARM_STEPS_TAC EXEC (35--42) THEN
    SUBGOAL_THEN `r + 63 < 2 EXP 64` ASSUME_TAC THENL
     [UNDISCH_TAC `val(inlen:int64) - (64 - b) = r` THEN
      UNDISCH_TAC `LENGTH(d:byte list) + val(inlen:int64) < 2 EXP 64` THEN
      UNDISCH_TAC `LENGTH(d:byte list) = 64 * n + b` THEN
      UNDISCH_TAC `~(val(inlen:int64) = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `r:num` WG_NBLOCKS_WORD)
      (CONJ (MP (ARITH_RULE `~(r <= 64) ==> 64 < r`) (ASSUME `~(r <= 64)`))
            (ASSUME `r + 63 < 2 EXP 64`))]) THEN
    ABBREV_TAC `k = (r + 63) DIV 64 - 1` THEN
    SUBGOAL_THEN `1 <= k /\ 64 * k < r /\ r <= 64 * k + 64 /\ 64 * k < 2 EXP 64`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN
      MP_TAC(SPECL [`r + 63`; `64`] DIVISION) THEN
      UNDISCH_TAC `~(r <= 64)` THEN UNDISCH_TAC `r < 2 EXP 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASSUME_TAC(MP (SPEC `k:num` WG_VAL_WORD_SMALL)
      (MP (ARITH_RULE `64 * k < 2 EXP 64 ==> k < 2 EXP 64`)
          (ASSUME `64 * k < 2 EXP 64`))) THEN
    MP_TAC(ISPECL [`inp:int64`; `m:byte list`; `val(inlen:int64)`; `64 - b`;
                   `64 * k`; `s42:armstate`] WG_READ_BYTES_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `val(inlen:int64) - (64 - b) = r` THEN
      UNDISCH_TAC `64 - b < val(inlen:int64)` THEN
      UNDISCH_TAC `64 * k < r` THEN ARITH_TAC;
      DISCH_TAC] THEN
    BLAKE2S_H_COLLECT_TAC `s42:armstate`
     `blake2s_compress_blocks (blake2s_chain h0 d)
        (APPEND (SUB_LIST(64 * n,b) d) (SUB_LIST(0,64 - b) m))
        (word(64 * n)) 64 F 1` THEN
    BLAKE2S_COMPRESS_BLOCKS64_TAC
     [`st:int64`; `read X1 s`; `read X2 s`;
      `word_add (word(64 * n)) (word 64):int64`;
      `blake2s_compress_blocks (blake2s_chain h0 d)
         (APPEND (SUB_LIST(64 * n,b) d) (SUB_LIST(0,64 - b) m))
         (word(64 * n)) 64 F 1`;
      `SUB_LIST(64 - b,64 * k) (m:byte list)`;
      `F`; `pc:num`; `read SP s`; `read X30 s`] 43 THEN
    BLAKE2S_H_EXPAND_TAC `s43:armstate` THEN
    ARM_STEPS_TAC EXEC (44--52) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `k:num` WG_WORD_SHL_6)
                                   (ASSUME `64 * k < 2 EXP 64`)]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`r:num`; `64 * k`] WG_WORD_SUB_LE)
      (MP (ARITH_RULE `64 * k < r ==> 64 * k <= r`)
          (ASSUME `64 * k < r`))]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    ABBREV_TAC `r2 = r - 64 * k` THEN
    SUBGOAL_THEN `1 <= r2 /\ r2 <= 64 /\ r2 < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r2" THEN UNDISCH_TAC `64 * k < r` THEN
      UNDISCH_TAC `r <= 64 * k + 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
    WG_PLT_TAC EXEC 52 THEN
    ASSUME_TAC(MP (SPEC `r2:num` WG_VAL_WORD_SMALL)
                  (ASSUME `r2 < 2 EXP 64`)) THEN
    MP_TAC(ISPECL [`inp:int64`; `m:byte list`; `val(inlen:int64)`;
                   `64 - b + 64 * k`; `r2:num`; `s56:armstate`]
                  WG_READ_BYTES_SUBLIST) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `val(inlen:int64) - (64 - b) = r` THEN
      UNDISCH_TAC `64 - b < val(inlen:int64)` THEN
      UNDISCH_TAC `r - 64 * k = r2` THEN UNDISCH_TAC `64 * k < r` THEN
      ARITH_TAC;
      DISCH_TAC] THEN
    WG_CALL_TAC "memcpy" EXEC
     [`read X0 s`; `read X1 s`; `read X2 s`;
      `num_of_bytelist(SUB_LIST(64 - b + 64 * k,r2) m)`; `read X30 s`] 57 THEN
    ARM_STEPS_TAC EXEC (58--65) THEN
    MP_TAC(SPECL [`h0:num->int32`; `d:byte list`; `m:byte list`; `k:num`]
      BLAKE2S_UPDATE_LARGE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`] THEN
    BLAKE2S_UPDATE_FINAL_TAC THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ARITH_TAC;
      MATCH_MP_TAC WG_BUFLEN_ZX THEN ASM_REWRITE_TAC[]]]);;

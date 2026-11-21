(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of blake2s_final_spec.ml: a straight-line            *)
(* simulation through the calls of memset, blake2s_compress_generic, memcpy  *)
(* and memset.                                                               *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

let WIREGUARD_BLAKE2S_FINAL_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "blake2s_final"; layout_range "plt_memcpy";
   layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* The first n bytes of the hash as a number, from the 8 state words.        *)

let BLAKE2S_BYTES_NUM = prove
 (`!(h:num->int32) n.
     n <= 32
     ==> num_of_bytelist(SUB_LIST(0,n) (blake2s_bytes h)) =
         num_of_wordlist [h 0; h 1; h 2; h 3; h 4; h 5; h 6; h 7] MOD
         2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[blake2s_bytes; WG_NUM_OF_BYTELIST_AS_WORDLIST;
              NUM_OF_WORDLIST_SUB_LIST_0; DIMINDEX_8] THEN
  REWRITE_TAC[GSYM WG_NUM_OF_BYTELIST_AS_WORDLIST; NUM_OF_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[ARITH_RULE `256 EXP 32 = 2 EXP (8 * 32)`; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `n <= 32 ==> MIN (8 * 32) (8 * n) = 8 * n`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_32] THEN ARITH_TAC);;

(* The increment of the last compression, the buffer length b.               *)

let WG_VAL_WORD_SUBWORD_SMALL = prove
 (`!b. b < 2 EXP 32 ==> val(word_subword (word b:int64) (0,32):int32) = b`,
  GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `b < 18446744073709551616` ASSUME_TAC THENL
   [UNDISCH_TAC `b < 4294967296` THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT; DIV_1]]);;

(* blake2s_compress_generic for the last block: one block, the final flag.   *)

let BLAKE2S_COMPRESS_LAST_BLOCK =
  let th = SPECL [`st:int64`; `blk:int64`; `word 1:int64`; `inc:int64`;
                  `tt:int64`; `h:num->int32`; `p:byte list`; `T`]
     WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT in
  GENL [`st:int64`; `blk:int64`; `inc:int64`; `tt:int64`; `h:num->int32`;
        `p:byte list`]
   (CONV_RULE (DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
               DEPTH_CONV WORD_RED_CONV THENC
               REWRITE_CONV[MULT_CLAUSES; LE_REFL]) th);;

let BLAKE2S_COMPRESS_LAST_BLOCK_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_BLAKE2S_FINAL_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,BLAKE2S_COMPRESS_LAST_BLOCK);;

(* The chained state after the last compression, the 8 words of it as a      *)
(* number, and the output, its first outlen bytes.                           *)

let blake2s_final_h_tm =
 `blake2s_compress_blocks (blake2s_chain h0 d)
    (APPEND (SUB_LIST (64 * n,b) d) (REPLICATE (64 - b) (word 0)))
    (word (64 * n)) b T 1`;;

let blake2s_final_num_tm =
  mk_comb(`num_of_wordlist:int32 list->num`,
          mk_list(map (fun i -> mk_comb(blake2s_final_h_tm,mk_small_numeral i))
                      (0--7),`:int32`));;

let blake2s_final_out_tm =
  mk_comb(mk_comb(`(MOD)`,blake2s_final_num_tm),`2 EXP (8 * outlen)`);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_BLAKE2S_FINAL_GCC13_O2_EXEC in
  let bth = ASSUME `b <= 64` in
  let zxth = MP (SPEC `b:num` WG_WORD_ZX_SMALL)
                (MP (ARITH_RULE `b <= 64 ==> b < 2 EXP 32`) bth) in
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `out:int64`; `h0:num->int32`; `d:byte list`; `outlen:num`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 320 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "memset" o REWRITE_RULE[memset_contract])
    (CONJUNCTS_THEN2
      (LABEL_TAC "memcpy" o REWRITE_RULE[memcpy_contract])
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
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
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `s0:armstate`)) (concl th))) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WG_BYTES64_SPLIT o check (fun th ->
    concl th =
    `read (memory :> bytes64 (word_add st (word 40))) s0 = word 0`)) THEN
  CONV_TAC(LAND_CONV(WG_ADDR_CONV THENC WORD_REDUCE_CONV)) THEN STRIP_TAC THEN

  (*** Pad the buffer with zeros ***)

  ARM_STEPS_TAC EXEC (1--15) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `b:num` WG_FILL_WORD) bth]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[zxth]) THEN
  WG_PLT_TAC EXEC 15 THEN
  ASSUME_TAC(MP (SPEC `64 - b` WG_VAL_WORD_SMALL)
                (ARITH_RULE `64 - b < 2 EXP 64`)) THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 20 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add st (word 48),64)) s20 =
    num_of_bytelist(APPEND (SUB_LIST(64 * n,b) d)
                           (REPLICATE (64 - b) (word 0)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH(SUB_LIST(64 * n,b) (d:byte list)) = b`
    ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN
      UNDISCH_TAC `LENGTH(d:byte list) = 64 * n + b` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`word_add st (word 48):int64`;
                   `SUB_LIST(64 * n,b) (d:byte list)`;
                   `REPLICATE (64 - b) (word 0):byte list`; `64 - b`;
                   `s20:armstate`] WG_READ_BYTES_APPEND) THEN
    ASM_REWRITE_TAC[NUM_OF_BYTELIST_REPLICATE_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `b <= 64 ==> b + (64 - b) = 64`];
    ALL_TAC] THEN

  (*** Compress the buffer as the last block ***)

  ARM_STEPS_TAC EXEC (21--25) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[zxth]) THEN
  SUBGOAL_THEN
   `!i. i < 8 ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s25 =
                  blake2s_chain h0 d i`
  ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  BLAKE2S_COMPRESS_LAST_BLOCK_TAC
   [`st:int64`; `read X1 s`; `read X3 s`; `word(64 * n):int64`;
    `blake2s_chain h0 d`;
    `APPEND (SUB_LIST(64 * n,b) d) (REPLICATE (64 - b) (word 0)):byte list`;
    `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `b:num` WG_VAL_WORD_SUBWORD_SMALL)
    (MP (ARITH_RULE `b <= 64 ==> b < 2 EXP 32`) bth)]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `s26:armstate`)) (concl th) &&
    can (find_term ((=) `blake2s_chain h0 d`)) (concl th))) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN

  (*** Copy the first outlen bytes of the new state words to the output ***)

  ARM_STEPS_TAC EXEC (27--30) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `outlen:num` WG_WORD_ZX_SMALL)
    (MP (ARITH_RULE `outlen <= 32 ==> outlen < 2 EXP 32`)
        (ASSUME `outlen <= 32`))]) THEN
  SUBGOAL_THEN
   (mk_eq(`read (memory :> bytes(st,32)) s30`,blake2s_final_num_tm))
  ASSUME_TAC THENL
   [CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
    REWRITE_TAC[GSYM BYTES32_WBYTES] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(`read (memory :> bytes(st,outlen)) s30`,blake2s_final_out_tm))
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if lhand(concl th) = `read (memory :> bytes(st,32)) s30`
      then REWRITE_TAC[GSYM th] else failwith "") THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE `outlen <= 32 ==> MIN 32 outlen = outlen`];
    ALL_TAC] THEN
  WG_PLT_TAC EXEC 30 THEN
  ASSUME_TAC(MP (SPEC `outlen:num` WG_VAL_WORD_SMALL)
    (MP (ARITH_RULE `outlen <= 32 ==> outlen < 2 EXP 64`)
        (ASSUME `outlen <= 32`))) THEN
  WG_CALL_TAC "memcpy" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; blake2s_final_out_tm;
    `read X30 s`] 35 THEN

  (*** Zero the state ***)

  ARM_STEPS_TAC EXEC (36--39) THEN
  WG_PLT_TAC EXEC 39 THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 44 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  ARM_STEPS_TAC EXEC (45--48) THEN

  (*** The output is the specified hash ***)

  SUBGOAL_THEN (mk_eq(`blake2s_final_hash h0 d`,blake2s_final_h_tm))
  SUBST1_TAC THENL
   [REWRITE_TAC[blake2s_final_hash; ONE; blake2s_compress_blocks] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM WORD_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `LENGTH(d:byte list) < 2 EXP 64` THEN
    UNDISCH_TAC `LENGTH(d:byte list) = 64 * n + b` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[BLAKE2S_BYTES_NUM] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

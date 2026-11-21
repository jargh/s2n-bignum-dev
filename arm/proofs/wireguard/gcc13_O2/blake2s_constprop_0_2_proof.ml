(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of blake2s_constprop_0_2_spec.ml: the state on the   *)
(* stack is zeroed with memset, the parameter words stored (h[0] with the    *)
(* key length, then 64 bits at a time from h[1], at an odd word, to the low  *)
(* half of t), the key copied into the buffer with memcpy and the rest of    *)
(* the buffer zeroed with memset, which gives the state of a keyed hash with *)
(* the padded key block buffered; then blake2s_update and blake2s_final are  *)
(* simulated with their theorems, and BLAKE2S_STREAM gives the hash.         *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/blake2s_constprop_0_2_spec.ml";;

let WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "blake2s_constprop_0_2"; layout_range "plt_memset";
    layout_range "plt_memcpy"];;

let BC_EXEC = WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_EXEC;;

let BC_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,BC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let BC_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,BC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the address and length of the padding of the key in the buffer   *)
(* (the state being at stackpointer + 408) and h[0].                         *)
(* ------------------------------------------------------------------------- *)

let BC_PAD_ADDR = prove
 (`!sp k:int64. word_add (word_add sp (word 408)) (word_add k (word 48)) =
                word_add sp (word(456 + val k))`,
  REWRITE_TAC[WORD_ADD; WORD_VAL] THEN CONV_TAC WORD_RULE);;

let BC_PAD_LEN_WORD = prove
 (`!k:int64. val k <= 64 ==> word_sub (word 64) k = word(64 - val k)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  ASM_SIMP_TAC[WG_WORD_SUB_LE]);;

let BC_H0_WORD0 = prove
 (`!k:int64.
     word_zx(word_zx(word_xor (word 1795745399) (word_shl (word_zx k) 8):int32)
             :int64):int32 =
     word_xor (word 1779033703)
       (word_xor (word 16842752) (word_xor (word_shl (word_zx k) 8) (word 16)))`,
  GEN_TAC THEN BITBLAST_TAC);;

(* The state, the padded key and the data hashed (kl being the key length).  *)

let bc_st = `word_add stackpointer (word 408):int64`;;

let bc_pk = `APPEND (kb:byte list) (REPLICATE (64 - kl) (word 0))`;;

let bc_d = mk_binop `APPEND:byte list->byte list->byte list` bc_pk
                    `m:byte list`;;

(* ------------------------------------------------------------------------- *)
(* The setup, the zeroing of the state and the parameter words.              *)
(* ------------------------------------------------------------------------- *)

let BC_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `inp:int64`; `key:int64`; `inlen:int64`; `keylen:int64`;
    `kb:byte list`; `m:byte list`; `mset:int64`; `ea1:int64`; `el1:num`;
    `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 528 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "memset" (REWRITE_RULE[memset_contract] th))
    (CONJUNCTS_THEN2
      (fun th -> ASSUME_TAC th THEN
                 LABEL_TAC "memcpy" (REWRITE_RULE[memcpy_contract] th))
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 336):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  GOT_ENTRY_TAC `got_memset:num` `s0:armstate` THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s0:armstate`;;

let BC_INIT_TAC =
  ARM_STEPS_TAC BC_EXEC (1--14) THEN WG_PLT_TAC BC_EXEC 14 THEN
  WG_CALL_TAC "memset" BC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 19 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC bc_st 120 [32; 40] `s19:armstate` THEN
  MP_TAC(SPECL [`word_add stackpointer (word 440):int64`; `s19:armstate`;
                `word 0:int64`] WG_BYTES64_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(WG_ADDR_CONV THENC WORD_REDUCE_CONV)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC BC_EXEC (20--47);;

(* ------------------------------------------------------------------------- *)
(* The key into the buffer and the padding with zeros, with the key length   *)
(* named kl (the simulation reasons about the address and length of the     *)
(* padding as stackpointer + 456 + kl and 64 - kl).                          *)
(* ------------------------------------------------------------------------- *)

let BC_KEY_TAC =
  WG_PLT_TAC BC_EXEC 47 THEN
  WG_CALL_TAC "memcpy" BC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist kb`;
    `read X30 s`] 52 THEN
  ARM_STEPS_TAC BC_EXEC (53--58) THEN WG_PLT_TAC BC_EXEC 58 THEN
  SUBGOAL_THEN `val(keylen:int64) <= 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BC_PAD_ADDR;
    MATCH_MP BC_PAD_LEN_WORD (ASSUME `val(keylen:int64) <= 64`)]) THEN
  ASSUME_TAC(MP (SPEC `64 - val(keylen:int64)` WG_VAL_WORD_SMALL)
                (ARITH_RULE `64 - val(keylen:int64) < 2 EXP 64`)) THEN
  ABBREV_TAC `kl = val(keylen:int64)` THEN
  WG_CALL_TAC "memset" BC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 63 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  SUBGOAL_THEN
   (mk_eq(`read (memory :> bytes(word_add stackpointer (word 456),64)) s63`,
          mk_comb(`num_of_bytelist`,bc_pk)))
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`word_add stackpointer (word 456):int64`; `kb:byte list`;
                   `REPLICATE (64 - kl) (word 0):byte list`; `64 - kl`;
                   `s63:armstate`] WG_READ_BYTES_APPEND) THEN
    ASM_REWRITE_TAC[NUM_OF_BYTELIST_REPLICATE_0; GSYM WORD_ADD_ASSOC;
                    GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `kl <= 32 ==> kl + 64 - kl = 64`];
    ALL_TAC] THEN
  ARM_STEPS_TAC BC_EXEC (64--68);;

(* ------------------------------------------------------------------------- *)
(* The state of the keyed hash, from the 32-bit words of h and the 64-bit   *)
(* zero of t, and the hash.                                                  *)
(* ------------------------------------------------------------------------- *)

let BC_STATE_TAC =
  MAP_EVERY (fun k ->
    let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,
                            `stackpointer:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral k)) in
    let l = list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
      [mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->
                             (int64->byte,int64)component->
                             (armstate,int64)component`,`memory`),
               mk_comb(`bytes64:int64->(int64->byte,int64)component`,a));
       `s68:armstate`]) in
    FIRST_ASSUM(MP_TAC o MATCH_MP WG_BYTES64_SPLIT o check (fun th ->
      is_eq(concl th) && lhand(concl th) = l)) THEN
    CONV_TAC(LAND_CONV(WG_ADDR_CONV THENC WORD_REDUCE_CONV)) THEN STRIP_TAC)
   [412; 420; 428; 436] THEN
  WG_JOIN_TAC `read (memory :> bytes64 (word_add stackpointer (word 440))) s68 =
               word_join (word 0:int32) (word 0:int32)` THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_JOIN_CONV ORELSEC ALL_CONV)) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,bc_pk),`64`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word kl:int32 = word_zx(keylen:int64)` ASSUME_TAC THENL
   [EXPAND_TAC "kl" THEN REWRITE_TAC[word_zx]; ALL_TAC] THEN
  SUBGOAL_THEN
   (list_mk_comb(`blake2s_state_at`,
      [bc_st; `blake2s_h0 kl 16`; bc_pk; `16`; `s68:armstate`]))
  ASSUME_TAC THENL
   [REWRITE_TAC[blake2s_state_at; blake2s_chain; blake2s_nblocks;
                blake2s_buflen] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[blake2s_compress_blocks; SUB_LIST_REFL; LE_REFL] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[BC_H0_WORD0] THEN
    REWRITE_TAC[blake2s_h0; blake2s_iv] THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

let BC_HASH_TAC =
  SUBGOAL_THEN `64 + val(inlen:int64) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  BC_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 kl 16`; bc_pk;
    `m:byte list`; `16`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 69 THEN
  BLAKE2S_STATE_EXPAND_TAC `s69:armstate` THEN
  ARM_STEPS_TAC BC_EXEC (70--72) THEN
  BLAKE2S_STATE_COLLECT_TAC
   (list_mk_comb(`blake2s_state_at`,
      [bc_st; `blake2s_h0 kl 16`; bc_d; `16`; `s72:armstate`])) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
     (mk_comb(`LENGTH:byte list->num`,bc_d)) `2 EXP 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC] THEN
  BC_FINAL_TAC
   [`read X0 s`; `read X1 s`; `blake2s_h0 kl 16`; bc_d;
    `16`; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 73 THEN
  ARM_STEPS_TAC BC_EXEC (74--78) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(kl = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`kb:byte list`; `16`; `m:byte list`] BLAKE2S_STREAM) THEN
  ASM_REWRITE_TAC[blake2s_input] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[LENGTH_APPEND]];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  BC_SETUP_TAC THEN BC_INIT_TAC THEN BC_KEY_TAC THEN BC_STATE_TAC THEN
  BC_HASH_TAC);;

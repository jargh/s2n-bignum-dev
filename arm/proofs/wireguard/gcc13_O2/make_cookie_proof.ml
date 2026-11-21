(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of make_cookie_spec.ml. After the zeroing of the     *)
(* state on the stack (as a stack variable) and the time, the secret is      *)
(* either kept or (if expired) replaced by the bytes that get_random_bytes   *)
(* gives (named sk), under down_write; then under down_read the stores of    *)
(* blake2s_init_key for the 32-byte secret give the state of the keyed hash  *)
(* with the padded key block buffered, the address for the protocol and the  *)
(* port are hashed with blake2s_update and blake2s_final, and BLAKE2S_STREAM  *)
(* gives the MAC: six paths, for the two secrets and the three kinds of      *)
(* protocol.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/make_cookie_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_MAKE_COOKIE_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "make_cookie"; layout_range "plt_memset";
    layout_range "plt_down_write"; layout_range "plt_up_write";
    layout_range "plt_down_read"; layout_range "plt_up_read";
    layout_range "plt_ktime_get_coarse_with_offset";
    layout_range "plt_get_random_bytes"];;

let MC_EXEC = WIREGUARD_MAKE_COOKIE_GCC13_O2_EXEC;;

let MC_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,MC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let MC_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,MC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let mc_got =
  [`got_memset:num`; `got_memcpy:num`; `got_down_write:num`;
   `got_up_write:num`; `got_down_read:num`; `got_up_read:num`;
   `got_ktime_get_coarse_with_offset:num`; `got_get_random_bytes:num`];;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the test of the protocol (a 16-bit field compared as 32 bits),    *)
(* the addresses in the headers, and the condition of the expiry.            *)
(* ------------------------------------------------------------------------- *)

let MC_PROTO_EQ = prove
 (`!p:int16 c.
     c < 65536
     ==> (val(word_sub (word_zx(word_zx(word_zx p:int32):int64):int32)
                       (word c)) = 0 <=> p = word c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WG_WORD_ZX_ZX] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16;
              DIMINDEX_32] THEN
  MP_TAC(ISPEC `p:int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `c < 65536` THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `c < 65536 ==> c < 4294967296`]);;

let MC_ZX16 = prove
 (`!x:int16. word_zx(word_zx x:int32):int64 = word(val x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16;
                           DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 65536 ==> x < 4294967296`;
           ARITH_RULE `x < 65536 ==> x < 18446744073709551616`]);;

let MC_HDR_ADDR = prove
 (`!(h:int64) (x:int16) k.
     word_add (word_add h (word_zx(word_zx x:int32):int64)) (word k) =
     word_add h (word(val x + k)) /\
     word_add h (word_zx(word_zx x:int32):int64) = word_add h (word(val x))`,
  REWRITE_TAC[MC_ZX16; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let mc_fresh = `ival(now:int64) < ival(word_add bd (word 120000000000):int64)`;;

(* ------------------------------------------------------------------------- *)
(* The state of the keyed hash (at stackpointer + 4168) for the secret sk:   *)
(* its words, from the stores in state s, and blake2s_state_at, and its      *)
(* facts again in a later state, before the first blake2s_update.            *)
(* ------------------------------------------------------------------------- *)

let mc_st = `word_add stackpointer (word 4168):int64`;;

let mc_pk sk = mk_binop `APPEND:byte list->byte list->byte list` sk
                 `REPLICATE 32 (word 0):byte list`;;

let mc_state_at d s =
  list_mk_comb(`blake2s_state_at`,[mc_st; `blake2s_h0 32 16`; d; `16`; s]);;

let MC_SPLIT_TAC s ks =
  MAP_EVERY (fun k ->
    let a = rhs(concl(WG_ADDR_CONV
      (mk_comb(mk_comb(`word_add:int64->int64->int64`,mc_st),
               mk_comb(`word:num->int64`,mk_small_numeral k))))) in
    let l = vsubst [a,`a:int64`; s,`s:armstate`]
                   `read (memory :> bytes64 a) s` in
    FIRST_ASSUM(MP_TAC o MATCH_MP WG_BYTES64_SPLIT o
                check (fun th -> is_eq(concl th) && lhand(concl th) = l)) THEN
    CONV_TAC(LAND_CONV(WG_ADDR_CONV THENC WORD_REDUCE_CONV)) THEN
    STRIP_TAC) ks;;

let MC_STATE_TAC sk s =
  let pk = mc_pk sk in
  let rd a n = list_mk_comb(`read:(armstate,num)component->armstate->num`,
    [mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->
                           (int64->byte,num)component->
                           (armstate,num)component`,`memory`),
             mk_comb(`bytes:int64#num->(int64->byte,num)component`,
                     mk_pair(a,mk_small_numeral n))); s]) in
  MC_SPLIT_TAC s [0; 8; 16; 24; 112] THEN
  SUBGOAL_THEN (mk_eq(rd `word_add stackpointer (word 4216):int64` 32,
                      mk_comb(`num_of_bytelist`,sk))) ASSUME_TAC THENL
   [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(rd `word_add stackpointer (word 4248):int64` 32,`0`))
  ASSUME_TAC THENL [WG_ZERO_BYTES_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(rd `word_add stackpointer (word 4216):int64` 64,
                      mk_comb(`num_of_bytelist`,pk))) ASSUME_TAC THENL
   [MP_TAC(ISPECL [`word_add stackpointer (word 4216):int64`; sk;
                   `REPLICATE 32 (word 0):byte list`; `32`; s]
                  WG_READ_BYTES_APPEND) THEN
    ASM_REWRITE_TAC[NUM_OF_BYTELIST_REPLICATE_0; GSYM WORD_ADD_ASSOC;
                    GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,pk),`64`))
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mc_state_at pk s) ASSUME_TAC THENL
   [REWRITE_TAC[blake2s_state_at; blake2s_chain; blake2s_nblocks;
                blake2s_buflen] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[blake2s_compress_blocks; SUB_LIST_REFL; LE_REFL] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[blake2s_h0; blake2s_iv] THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  BLAKE2S_STATE_EXPAND_TAC s;;

let MC_COLLECT_PK_TAC sk s =
  SUBGOAL_THEN (mc_state_at (mc_pk sk) s) ASSUME_TAC THENL
   [REWRITE_TAC[blake2s_state_at] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    REWRITE_TAC[blake2s_chain; blake2s_nblocks; blake2s_buflen] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[blake2s_compress_blocks; SUB_LIST_REFL; LE_REFL] THEN
    REWRITE_TAC[blake2s_h0; blake2s_iv] THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The hashing, from the data d (the padded key, perhaps with the address)  *)
(* at step p (the code for the port; coll gives the state before the first  *)
(* blake2s_update there), to the return; the MAC from BLAKE2S_STREAM; and    *)
(* the address (a, of k bytes) for a protocol, from step n.                  *)
(* ------------------------------------------------------------------------- *)

let MC_PORT_TAC coll p sk d =
  let sv i = mk_var("s"^string_of_int i,`:armstate`) in
  let d2 = mk_binop `APPEND:byte list->byte list->byte list` d
                    `port:byte list` in
  ARM_STEPS_TAC MC_EXEC (p--(p+5)) THEN
  WG_REG_REWRITE_TAC `X1` [MC_HDR_ADDR] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 2:int64)`) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
     (mk_binop `(+):num->num->num` (mk_comb(`LENGTH:byte list->num`,d)) `2`)
     `2 EXP 64`) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ARITH_TAC;
    ALL_TAC] THEN
  coll (sv(p+5)) THEN
  MC_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 32 16`; d;
    `port:byte list`; `16`; `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] (p+6) THEN
  BLAKE2S_STATE_EXPAND_TAC (sv(p+6)) THEN
  ARM_STEPS_TAC MC_EXEC ((p+7)--(p+9)) THEN
  BLAKE2S_STATE_COLLECT_TAC (mc_state_at d2 (sv(p+9))) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
     (mk_comb(`LENGTH:byte list->num`,d2)) `2 EXP 64`) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MC_FINAL_TAC
   [`read X0 s`; `read X1 s`; `blake2s_h0 32 16`; d2; `16`;
    `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
    `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] (p+10) THEN
  ARM_STEPS_TAC MC_EXEC ((p+11)--(p+12)) THEN WG_PLT_TAC MC_EXEC (p+12) THEN
  WG_CALL_TAC "up_read" MC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (p+17) THEN
  ARM_STEPS_TAC MC_EXEC ((p+18)--(p+22)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC sk THEN ASM_REWRITE_TAC[];;

let MC_MAC_TAC sk =
  REWRITE_TAC[wg_mac; wg_cookie_data] THEN CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[APPEND] THEN
  W(fun (asl,w) ->
    let m = rand(rand(rand w)) in
    MP_TAC(ISPECL [sk; `16`; m] BLAKE2S_STREAM)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[blake2s_input; LENGTH_APPEND; LENGTH_REPLICATE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[blake2s_input; APPEND_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[APPEND_ASSOC];;

let MC_ADDR_TAC n sk a k =
  let sv i = mk_var("s"^string_of_int i,`:armstate`) in
  ARM_STEPS_TAC MC_EXEC ((n+1)--(n+7)) THEN
  WG_REG_REWRITE_TAC `X1` [MC_HDR_ADDR] THEN
  ASSUME_TAC(WORD_REDUCE_CONV
    (mk_comb(`val:int64->num`,
             mk_comb(`word:num->int64`,mk_small_numeral k)))) THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool`
     (mk_binop `(+):num->num->num` (mk_comb(`LENGTH:byte list->num`,mc_pk sk))
               (mk_small_numeral k)) `2 EXP 64`) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MC_COLLECT_PK_TAC sk (sv(n+7)) THEN
  MC_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 32 16`;
    mc_pk sk; a; `16`; `mcpy:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] (n+8) THEN
  BLAKE2S_STATE_EXPAND_TAC (sv(n+8)) THEN
  ARM_STEPS_TAC MC_EXEC [n+9] THEN
  MC_PORT_TAC (BLAKE2S_STATE_COLLECT_TAC o
               mc_state_at (mk_binop `APPEND:byte list->byte list->byte list`
                                     (mc_pk sk) a))
    (n+10) sk (mk_binop `APPEND:byte list->byte list->byte list` (mc_pk sk) a)
  THEN MC_MAC_TAC sk;;

(* The three protocols, from the test at step n with the secret sk.          *)

let MC_PROTO_TAC sk n =
  ASM_CASES_TAC `proto:int16 = word 8` THENL
   [WG_PC_REWRITE_TAC [MATCH_MP MC_PROTO_EQ (ARITH_RULE `8 < 65536`);
                       ASSUME `proto:int16 = word 8`] THEN
    MC_ADDR_TAC n sk `a4:byte list` 4;
    WG_PC_REWRITE_TAC [MATCH_MP MC_PROTO_EQ (ARITH_RULE `8 < 65536`);
                       ASSUME `~(proto:int16 = word 8)`] THEN
    ARM_STEPS_TAC MC_EXEC ((n+1)--(n+3)) THEN
    ASM_CASES_TAC `proto:int16 = word 56710` THENL
     [WG_PC_REWRITE_TAC [MATCH_MP MC_PROTO_EQ (ARITH_RULE `56710 < 65536`);
                         ASSUME `proto:int16 = word 56710`] THEN
      MC_ADDR_TAC (n+3) sk `a6:byte list` 16;
      WG_PC_REWRITE_TAC [MATCH_MP MC_PROTO_EQ (ARITH_RULE `56710 < 65536`);
                         ASSUME `~(proto:int16 = word 56710)`] THEN
      MC_PORT_TAC (MC_COLLECT_PK_TAC sk) (n+4) sk (mc_pk sk) THEN
      MC_MAC_TAC sk]];;

(* ------------------------------------------------------------------------- *)
(* The setup, the time, and the two secrets.                                 *)
(* ------------------------------------------------------------------------- *)

let MC_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`cookie:int64`; `skb:int64`; `checker:int64`; `proto:int16`; `th:int16`;
    `nh:int16`; `head:int64`; `sec:byte list`; `bd:int64`; `a4:byte list`;
    `a6:byte list`; `port:byte list`; `mset:int64`; `mcpy:int64`;
    `dwr:int64`; `uwr:int64`; `drd:int64`; `urd:int64`; `ktc:int64`;
    `grb:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`memset_contract mset ea el ev`,"memset";
    `rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write";
    `rwsem_contract drd ea el ev`,"down_read";
    `rwsem_contract urd ea el ev`,"up_read";
    `ktime_get_coarse_with_offset_contract ktc ea el ev`,"ktime";
    `get_random_bytes_contract grb ea el ev`,"get_random_bytes"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) mc_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4096):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) mc_got;;

let MC_TIME_TAC =
  ARM_STEPS_TAC MC_EXEC (1--12) THEN WG_PLT_TAC MC_EXEC 12 THEN
  WG_CALL_TAC "memset" MC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 17 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC mc_st 120 [32; 40] `s17:armstate` THEN
  ARM_STEPS_TAC MC_EXEC (18--25) THEN WG_PLT_TAC MC_EXEC 25 THEN
  WG_CALL_TAC "ktime" MC_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 30 THEN
  ABBREV_TAC `now = read X0 s30` THEN
  ARM_STEPS_TAC MC_EXEC (31--32);;

let MC_KEEP_TAC =
  WG_PC_REWRITE_TAC [WG_IVAL_GT_FLAGS; ASSUME mc_fresh] THEN
  ARM_STEPS_TAC MC_EXEC (33--34) THEN WG_PLT_TAC MC_EXEC 34 THEN
  WG_CALL_TAC "down_read" MC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 39 THEN
  WG_BYTES32_WORDS_TAC `checker:int64` `s39:armstate` THEN
  ARM_STEPS_TAC MC_EXEC (40--68) THEN
  MC_STATE_TAC `sec:byte list` `s68:armstate` THEN
  ARM_STEPS_TAC MC_EXEC (69--70);;

let MC_RENEW_TAC =
  WG_PC_REWRITE_TAC [WG_IVAL_GT_FLAGS; ASSUME (mk_neg mc_fresh)] THEN
  ARM_STEPS_TAC MC_EXEC (33--34) THEN WG_PLT_TAC MC_EXEC 34 THEN
  WG_CALL_TAC "down_write" MC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC MC_EXEC (40--41) THEN WG_PLT_TAC MC_EXEC 41 THEN
  WG_CALL_TAC "ktime" MC_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 46 THEN
  ARM_STEPS_TAC MC_EXEC (47--50) THEN WG_PLT_TAC MC_EXEC 50 THEN
  WG_CALL_TAC "get_random_bytes" MC_EXEC
   [`read X0 s`; `read X1 s`; `read SP s`; `read X30 s`] 55 THEN
  WG_NAME_BYTES_TAC `checker:int64` `32` `sk:byte list` `s55:armstate` THEN
  ARM_STEPS_TAC MC_EXEC (56--57) THEN WG_PLT_TAC MC_EXEC 57 THEN
  WG_CALL_TAC "up_write" MC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 62 THEN
  ARM_STEPS_TAC MC_EXEC (63--65) THEN WG_PLT_TAC MC_EXEC 65 THEN
  WG_CALL_TAC "down_read" MC_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 70 THEN
  WG_BYTES32_WORDS_TAC `checker:int64` `s70:armstate` THEN
  ARM_STEPS_TAC MC_EXEC (71--99) THEN
  MC_STATE_TAC `sk:byte list` `s99:armstate` THEN
  ARM_STEPS_TAC MC_EXEC (100--101);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MC_SETUP_TAC THEN MC_TIME_TAC THEN
  ASM_CASES_TAC mc_fresh THENL
   [MC_KEEP_TAC THEN MC_PROTO_TAC `sec:byte list` 70;
    MC_RENEW_TAC THEN MC_PROTO_TAC `sk:byte list` 101]);;

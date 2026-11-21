(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of hmac_spec.ml: a straight-line simulation. The     *)
(* padded key block on the stack is zeroed with memset, the key is copied    *)
(* into it and xored with the inner pad 64 bits at a time; the inner hash is *)
(* computed with blake2s_update and blake2s_final (simulated with their      *)
(* theorems) on a state initialized as in mix_hash; the block is xored again *)
(* to the outer padded key and the outer hash computed in the same way, then *)
(* copied to the output, and the stack copies are zeroed.                    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/hmac_spec.ml";;

let WIREGUARD_HMAC_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "hmac"; layout_range "plt_memset"];;

let HMAC_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_HMAC_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let HMAC_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_HMAC_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* The xor of a 64-bit word of 8 bytes with 8 copies of the inner pad 0x36,  *)
(* and of 0x6a (the xor of the two pads, with which the code turns the inner *)
(* padded key into the outer one in place).                                  *)

let WG_XOR_CHUNK_54 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
    word_xor (word(num_of_bytelist [b0;b1;b2;b3;b4;b5;b6;b7]):int64)
             (word 0x3636363636363636) =
    word(num_of_bytelist
           (MAP (word_xor (word 0x36)) [b0;b1;b2;b3;b4;b5;b6;b7]))`,
  REWRITE_TAC[MAP; num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
  BITBLAST_TAC);;

let WG_XOR_CHUNK_106 = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7:byte.
    word_xor (word(num_of_bytelist [b0;b1;b2;b3;b4;b5;b6;b7]):int64)
             (word 0x6a6a6a6a6a6a6a6a) =
    word(num_of_bytelist
           (MAP (word_xor (word 0x6a)) [b0;b1;b2;b3;b4;b5;b6;b7]))`,
  REWRITE_TAC[MAP; num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The key as the explicit list of its bytes, and the padded key block (at   *)
(* stackpointer + 456) xored with the pad c.                                 *)
(* ------------------------------------------------------------------------- *)

let hmac_key_tm =
 `[EL 0 kb; EL 1 kb; EL 2 kb; EL 3 kb; EL 4 kb; EL 5 kb; EL 6 kb; EL 7 kb;
   EL 8 kb; EL 9 kb; EL 10 kb; EL 11 kb; EL 12 kb; EL 13 kb; EL 14 kb;
   EL 15 kb; EL 16 kb; EL 17 kb; EL 18 kb; EL 19 kb; EL 20 kb; EL 21 kb;
   EL 22 kb; EL 23 kb; EL 24 kb; EL 25 kb; EL 26 kb; EL 27 kb; EL 28 kb;
   EL 29 kb; EL 30 kb; EL 31 kb]:byte list`;;

let hmac_xor_tm c =
  mk_comb(`MAP:(byte->byte)->byte list->byte list`,
          mk_comb(`word_xor:byte->byte->byte`,
                  mk_comb(`word:num->byte`,mk_small_numeral c)));;

let hmac_pad_tm c =
  mk_comb(hmac_xor_tm c,
          mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,
                          hmac_key_tm),
                  `REPLICATE 32 (word 0):byte list`));;

(* The 64-bit words of the key from its bytes, in the initial state s0.      *)

let HMAC_KEY_WORDS_TAC (asl,w as gl) =
  let th = snd(find (fun (_,th) ->
    is_eq(concl th) &&
    lhand(concl th) = `read (memory :> bytes(key,32)) s0`) asl) in
  MAP_EVERY (fun j ->
    MP_TAC(MATCH_MP WG_READ_BYTES64_BYTELIST
            (CONJ th (EQT_ELIM(NUM_REDUCE_CONV
              (mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` (mk_small_numeral(8*j)) `8`)
                 `32`))))) THEN
    CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV SUB_LIST_CONV)))) THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC) (0--3) gl;;

(* Apply conv to the values of the 64-bit words of the block in state s.     *)

let HMAC_PAD_WORDS_CONV_TAC s conv =
  let ws = map (fun k ->
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
            mk_comb(`word:num->int64`,mk_small_numeral k)))
    [456; 464; 472; 480; 488; 496; 504; 512] in
  let isw th =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),Comb(Const("bytes64",_),a))),
        s')),_) -> s' = s && mem a ws
    | _ -> false in
  fun (asl,w as gl) ->
    let ths = filter (fun (_,th) -> isw th) asl in
    MAP_EVERY (fun (_,th0) ->
      FIRST_X_ASSUM(fun th -> if concl th = concl th0
                              then ASSUME_TAC(CONV_RULE(RAND_CONV conv) th)
                              else failwith "")) ths gl;;

(* The block as bytes in state s, from its 64-bit words: the key part xored  *)
(* with c, and the zero part as numerals.                                    *)

let HMAC_PAD_TAC c s =
  let chunk j =
    let els =
      if j < 4 then
        map (fun i -> mk_comb(mk_comb(`EL:num->byte list->byte`,
                                      mk_small_numeral(8 * j + i)),
                              `kb:byte list`)) (0--7)
      else replicate `word 0:byte` 8 in
    mk_comb(hmac_xor_tm c,mk_list(els,`:byte`)) in
  let th = ISPECL ([`word_add stackpointer (word 456):int64`] @
                   map chunk (0--7) @ [s]) WG_READ_BYTES_64_OF_CHUNKS in
  let target = mk_eq(lhand(rand(concl th)),
                     mk_comb(`num_of_bytelist`,hmac_pad_tm c)) in
  SUBGOAL_THEN target ASSUME_TAC THENL
   [MP_TAC th THEN
    REWRITE_TAC[LENGTH_MAP] THEN CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV WG_ADDR_CONV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(CONV_TAC(RAND_CONV(REWRITE_CONV[MAP])) THEN
          FIRST_ASSUM ACCEPT_TAC) THEN
      CONV_TAC(RAND_CONV(REWRITE_CONV[MAP; num_of_bytelist] THENC
                         WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV WG_REPLICATE_CONV)) THEN
      REWRITE_TAC[MAP; APPEND]];
    ALL_TAC];;

let HMAC_PAD_LENGTH_TAC =
  REWRITE_TAC[LENGTH_MAP; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN CONV_TAC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The bytes hashed (d1, d2 for the inner hash, e1, e2 for the outer one)    *)
(* and the hashes.                                                           *)
(* ------------------------------------------------------------------------- *)

let hmac_append_tm l1 l2 =
  mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,l1),l2);;

let hmac_hash_tm d =
  mk_comb(`SUB_LIST(0,32):byte list->byte list`,
          mk_comb(`blake2s_bytes`,
                  mk_comb(`blake2s_final_hash (blake2s_h0 0 32)`,d)));;

let hmac_d1_tm = hmac_append_tm `[]:byte list` (hmac_pad_tm 54);;
let hmac_d2_tm = hmac_append_tm hmac_d1_tm `m:byte list`;;
let hmac_inner_tm = hmac_hash_tm hmac_d2_tm;;
let hmac_e1_tm = hmac_append_tm `[]:byte list` (hmac_pad_tm 92);;
let hmac_e2_tm = hmac_append_tm hmac_e1_tm hmac_inner_tm;;
let hmac_outer_tm = hmac_hash_tm hmac_e2_tm;;

let hmac_state_tm d s =
  vsubst [d,`d:byte list`; s,`s:armstate`]
   `blake2s_state_at (word_add stackpointer (word 520)) (blake2s_h0 0 32)
                     d 32 s`;;

let hmac_length_lt_tm l =
  mk_binop `(<):num->num->bool` l `2 EXP 64`;;

let hmac_update_args d x =
  [`read X0 s`; `read X1 s`; `read X2 s`; `blake2s_h0 0 32`; d; x; `32`;
   `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`; `read SP s`;
   `read X30 s`];;

let hmac_final_args d =
  [`read X0 s`; `read X1 s`; `blake2s_h0 0 32`; d; `32`;
   `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
   `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
   `pc:num`; `read SP s`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_HMAC_GCC13_O2_EXEC in
  let length_tm l = mk_comb(`LENGTH:byte list->num`,l) in
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `inp:int64`; `key:int64`; `inlen:int64`; `kb:byte list`;
    `m:byte list`; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 640 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(LABEL_TAC "memset" o REWRITE_RULE[memset_contract] o
    check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "memset_contract"
      with Failure _ -> false)) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WG_LENGTH_32_EXPLICIT o
    check (fun th -> concl th = `LENGTH(kb:byte list) = 32`)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            (19--29) THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 336):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  HMAC_KEY_WORDS_TAC THEN

  (*** Zero the state at stackpointer + 520 and the block ***)

  ARM_STEPS_TAC EXEC (1--15) THEN
  WG_PLT_TAC EXEC 15 THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 20 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC `word_add stackpointer (word 520):int64` 120
    [32; 40] `s20:armstate` THEN
  ARM_STEPS_TAC EXEC (21--25) THEN
  WG_PLT_TAC EXEC 25 THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 30 THEN
  MEMSET_ZERO_ALL_TAC THEN
  MEMSET_ZERO_WORDS64_TAC `word_add stackpointer (word 456):int64` 64
    [32; 40; 48; 56] `s30:armstate` THEN

  (*** Copy the key to the block and xor it with the inner pad ***)

  ARM_STEPS_TAC EXEC (31--42) THEN
  WG_STEPS_TAC EXEC (43--82) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WG_XOR_CHUNK_54]) THEN
  HMAC_PAD_TAC 54 `s82:armstate` THEN

  (*** The inner hash ***)

  ARM_STEPS_TAC EXEC (83--108) THEN
  BLAKE2S_STATE_INIT_TAC `word_add stackpointer (word 520):int64`
    `s108:armstate` THEN
  ASSUME_TAC(INST_TYPE [`:byte`,`:A`] (CONJUNCT1 LENGTH)) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 64:int64)`) THEN
  SUBGOAL_THEN (mk_eq(length_tm(hmac_pad_tm 54),`64`)) ASSUME_TAC THENL
   [HMAC_PAD_LENGTH_TAC; ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s108:armstate` THEN
  HMAC_UPDATE_TAC (hmac_update_args `[]:byte list` (hmac_pad_tm 54)) 109 THEN

  BLAKE2S_STATE_EXPAND_TAC `s109:armstate` THEN
  ARM_STEPS_TAC EXEC (110--113) THEN
  BLAKE2S_STATE_COLLECT_TAC (hmac_state_tm hmac_d1_tm `s113:armstate`) THEN
  SUBGOAL_THEN
   (hmac_length_lt_tm
     (mk_binop `(+):num->num->num` (length_tm hmac_d1_tm) `val(inlen:int64)`))
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s113:armstate` THEN
  HMAC_UPDATE_TAC (hmac_update_args hmac_d1_tm `m:byte list`) 114 THEN

  BLAKE2S_STATE_EXPAND_TAC `s114:armstate` THEN
  ARM_STEPS_TAC EXEC (115--117) THEN
  BLAKE2S_STATE_COLLECT_TAC (hmac_state_tm hmac_d2_tm `s117:armstate`) THEN
  SUBGOAL_THEN (hmac_length_lt_tm (length_tm hmac_d2_tm)) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s117:armstate` THEN
  GOT_ENTRY_TAC `got_memset:num` `s117:armstate` THEN
  HMAC_FINAL_TAC (hmac_final_args hmac_d2_tm) 118 THEN

  (*** Turn the block into the outer padded key ***)

  ARM_STEPS_TAC EXEC (119--123) THEN
  HMAC_PAD_WORDS_CONV_TAC `s123:armstate` (REWRITE_CONV[MAP]) THEN
  WG_STEPS_TAC EXEC (124--163) THEN
  HMAC_PAD_WORDS_CONV_TAC `s163:armstate`
    (REWRITE_CONV[WG_XOR_CHUNK_106] THENC REWRITE_CONV[MAP] THENC
     REWRITE_CONV[WORD_XOR_ASSOC] THENC WORD_REDUCE_CONV) THEN
  HMAC_PAD_TAC 92 `s163:armstate` THEN

  (*** The outer hash ***)

  ARM_STEPS_TAC EXEC (164--188) THEN
  BLAKE2S_STATE_INIT_TAC `word_add stackpointer (word 520):int64`
    `s188:armstate` THEN
  SUBGOAL_THEN (mk_eq(length_tm(hmac_pad_tm 92),`64`)) ASSUME_TAC THENL
   [HMAC_PAD_LENGTH_TAC; ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s188:armstate` THEN
  HMAC_UPDATE_TAC (hmac_update_args `[]:byte list` (hmac_pad_tm 92)) 189 THEN

  BLAKE2S_STATE_EXPAND_TAC `s189:armstate` THEN
  ARM_STEPS_TAC EXEC (190--193) THEN
  BLAKE2S_STATE_COLLECT_TAC (hmac_state_tm hmac_e1_tm `s193:armstate`) THEN
  SUBGOAL_THEN (mk_eq(length_tm hmac_inner_tm,`32`)) ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; blake2s_bytes; LENGTH_BYTELIST_OF_NUM] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  SUBGOAL_THEN
   (hmac_length_lt_tm
     (mk_binop `(+):num->num->num` (length_tm hmac_e1_tm) `32`))
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s193:armstate` THEN
  HMAC_UPDATE_TAC (hmac_update_args hmac_e1_tm hmac_inner_tm) 194 THEN

  BLAKE2S_STATE_EXPAND_TAC `s194:armstate` THEN
  ARM_STEPS_TAC EXEC (195--197) THEN
  BLAKE2S_STATE_COLLECT_TAC (hmac_state_tm hmac_e2_tm `s197:armstate`) THEN
  SUBGOAL_THEN (hmac_length_lt_tm (length_tm hmac_e2_tm)) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s197:armstate` THEN
  GOT_ENTRY_TAC `got_memset:num` `s197:armstate` THEN
  HMAC_FINAL_TAC (hmac_final_args hmac_e2_tm) 198 THEN

  (*** Copy the hash to the output, zero the block and the hash ***)

  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 424):int64`
    `s198:armstate` THEN
  ARM_STEPS_TAC EXEC (199--206) THEN
  WG_PLT_TAC EXEC 206 THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 211 THEN
  ARM_STEPS_TAC EXEC (212--219) THEN

  (*** The output is HMAC ***)

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [hmac_key_tm; `m:byte list`] WG_HMAC_STREAM) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `64 + val(inlen:int64) < 2 EXP 64` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN (mk_eq(length_tm hmac_outer_tm,`32`)) ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; blake2s_bytes; LENGTH_BYTELIST_OF_NUM] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL ([`out:int64`] @
                 map (fun j ->
                   mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,
                                   mk_pair(mk_small_numeral(8 * j),`8`)),
                           hmac_outer_tm)) (0--3) @
                 [`s219:armstate`])
                WG_READ_BYTES_32_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[WG_SUB_LIST_CHUNKS32] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[APPEND]);;

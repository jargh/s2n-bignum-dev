(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of blake2s_compress_generic_spec.ml. Each block is   *)
(* simulated with the 32-bit values abbreviated after every step, and the    *)
(* final state words are identified with the compression of the block by     *)
(* the specification evaluated symbolically on tables of the abbreviations   *)
(* (common/wireguard_tables.ml), up to the reassociations by the compiler.   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/blake2s_compress_generic_spec.ml";;
needs "common/wireguard_tables.ml";;

let WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "blake2s_compress_generic"];;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* The 64-bit words of block i of a byte array in memory, as the code loads  *)
(* them, with the message words of the specification as their halves.        *)

let WG_READ_BLAKE2S_BLOCK64 = prove
 (`!a:int64 p n i q s:armstate.
        read (memory :> bytes(a,n)) s = num_of_bytelist p /\
        64 * i + 64 <= n /\ q < 8
        ==> read (memory :> bytes64(word_add (word_add a (word(64 * i)))
                                             (word(8 * q)))) s =
            word_join (blake2s_block p i (2 * q + 1))
                      (blake2s_block p i (2 * q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WG_BYTES64_JOIN THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; blake2s_block] THEN
  REWRITE_TAC[ARITH_RULE `64 * i + 4 * 2 * q = 64 * i + 8 * q`;
              ARITH_RULE `64 * i + 4 * (2 * q + 1) = 64 * i + 8 * q + 4`] THEN
  CONJ_TAC THEN MATCH_MP_TAC WG_READ_BYTES32_BYTELIST THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The values of the loop variables after one more block.                    *)

let WG_COUNTER_STEP = prove
 (`!(tt:int64) (x:int32) i.
     word_add tt (word(val x * (i + 1))) =
     word_add (word_add tt (word(val x * i))) (word_zx x)`,
  REWRITE_TAC[word_zx; LEFT_ADD_DISTRIB; MULT_CLAUSES; WORD_ADD;
              WORD_ADD_ASSOC]);;

let WG_BLK_STEP = prove
 (`!(blk:int64) i.
     word_add blk (word(64 * (i + 1))) =
     word_add (word_add blk (word(64 * i))) (word 64)`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; WORD_ADD; WORD_ADD_ASSOC]);;

let WG_NBLOCKS_STEP = prove
 (`!(nb:int64) i.
     i < val nb
     ==> word_sub (word(val nb - i)) (word 1):int64 = word(val nb - (i + 1)) /\
         (val(word_sub (word(val nb - i)) (word 1):int64) = 0 <=>
          i + 1 = val nb)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n - (i + 1) = (n - i) - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `nb:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
    DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o lhand o lhand o snd) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Tactics.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* The fact for the 8 words h i of the state in the precondition as 8 facts, *)
(* which the simulation then carries along.                                  *)

let BLAKE2S_EXPAND_H_TAC =
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

let BLAKE2S_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0];;

(* At the end of the simulation of block i: the code's new state words (the  *)
(* abbreviations of the simulation) are the compression of the block by the  *)
(* specification evaluated on tables (common/wireguard_tables.ml), and the   *)
(* other values are those of the invariant after i + 1 blocks.               *)

let BLAKE2S_COMPRESS_MATCH_TAC : tactic =
  fun (asl,w as gl) ->
    let defs = wg_defs_of asl in
    let canon = wg_canon_maker defs in
    let idx = wg_canon_index defs canon in
    let ident = WG_IDENTIFY defs canon idx in
    let vth = ISPECL [`hh:num->int32`; `ctr:int64`;
                      `word_subword (inc:int64) (0,32):int32`; `f:bool`]
                     BLAKE2S_WORKVEC_COUNTER in
    let rth = WG_SYM_ROUNDS_RULE ident 10 `m:num->int32` vth in
    let vfin = dest_list(rand(body(rand(concl rth)))) in
    let ats = map (WG_AGREE_AT rth) (0--15) in
    let ctm = `blake2s_compress hh m
                 (val(word_add (ctr:int64)
                   (word_zx (word_subword (inc:int64) (0,32):int32)))) f` in
    let outs = map (fun k ->
      let th = (RATOR_CONV(REWR_CONV blake2s_compress THENC let_CONV) THENC
                BETA_CONV THENC NUM_REDUCE_CONV THENC PURE_REWRITE_CONV ats)
               (mk_comb(ctm,mk_small_numeral k)) in
      TRANS th (ident (filter is_var vfin) (rand(concl th)))) (0--7) in
    let ith = MATCH_MP WG_NBLOCKS_STEP (ASSUME `i < val(nb:int64)`) in
    let zf = mk_comb(`read ZF`,rand w) in
    (ENSURES_FINAL_STATE_TAC THEN
     CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
     REWRITE_TAC outs THEN
     REWRITE_TAC[WG_COUNTER_ADD_LO; WG_COUNTER_ADD_HI;
                 GSYM(CONJUNCT1 ith)] THEN
     REPEAT CONJ_TAC THEN
     FIRST [FIRST_ASSUM ACCEPT_TAC;
            WG_ASM_EQ_TAC defs;
            MATCH_MP_TAC WG_BYTES64_FROM_HALVES THEN CONV_TAC WG_ADDR_CONV THEN
            REWRITE_TAC[WG_COUNTER_ADD_LO; WG_COUNTER_ADD_HI] THEN
            CONJ_TAC THEN WG_ASM_EQ_TAC defs;
            FIRST_ASSUM(fun th ->
              if is_iff(concl th) && lhand(concl th) = zf
              then REWRITE_TAC[th; CONJUNCT2 ith] else failwith "")]) gl;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `blk:int64`; `nb:int64`; `inc:int64`; `tt:int64`;
    `h:num->int32`; `p:byte list`; `f:bool`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            (19--29) THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  (*** The loop over the blocks, with the invariant after i blocks ***)

  ENSURES_WHILE_PUP_TAC `val(nb:int64)` `pc + blake2s_compress_generic_loop1`
   `pc + blake2s_compress_generic_loop1_back`
   `\i s.
     (read SP s = stackpointer /\ read X29 s = stackpointer /\
      read X17 s = word_add blk (word(64 * i)) /\
      read X21 s = word_add stackpointer (word 208) /\
      read(memory :> bytes64(word_add stackpointer (word 104))) s = st /\
      read(memory :> bytes64(word_add stackpointer (word 120))) s =
        word(val(nb:int64) - i) /\
      read(memory :> bytes32(word_add stackpointer (word 116))) s =
        word_subword (word_add tt
          (word(val(word_subword inc (0,32):int32) * i)):int64) (0,32) /\
      read(memory :> bytes32(word_add stackpointer (word 136))) s =
        word_subword (word_add tt
          (word(val(word_subword inc (0,32):int32) * i)):int64) (32,32) /\
      read(memory :> bytes32(word_add stackpointer (word 140))) s =
        word_subword (inc:int64) (0,32) /\
      read(memory :> bytes64 stackpointer) s = x29_init /\
      read(memory :> bytes64(word_add stackpointer (word 8))) s =
        returnaddress /\
      read(memory :> bytes64(word_add stackpointer (word 16))) s = x19_init /\
      read(memory :> bytes64(word_add stackpointer (word 24))) s = x20_init /\
      read(memory :> bytes64(word_add stackpointer (word 32))) s = x21_init /\
      read(memory :> bytes64(word_add stackpointer (word 40))) s = x22_init /\
      read(memory :> bytes64(word_add stackpointer (word 48))) s = x23_init /\
      read(memory :> bytes64(word_add stackpointer (word 56))) s = x24_init /\
      read(memory :> bytes64(word_add stackpointer (word 64))) s = x25_init /\
      read(memory :> bytes64(word_add stackpointer (word 72))) s = x26_init /\
      read(memory :> bytes64(word_add stackpointer (word 80))) s = x27_init /\
      read(memory :> bytes64(word_add stackpointer (word 88))) s = x28_init /\
      (!k. k < 8
           ==> read(memory :> bytes32(word_add st (word(4 * k)))) s =
               blake2s_compress_blocks h p tt
                 (val(word_subword inc (0,32):int32)) f i k) /\
      read(memory :> bytes64(word_add st (word 32))) s =
        word_add tt (word(val(word_subword inc (0,32):int32) * i)) /\
      read(memory :> bytes32(word_add st (word 40))) s =
        (if f then word_not(word 0) else word 0) /\
      read(memory :> bytes32(word_add st (word 44))) s = word 0 /\
      read(memory :> bytes(blk,64 * val nb)) s = num_of_bytelist p) /\
     (read ZF s <=> i = val nb)` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `1 <= val(nb:int64)` THEN ARITH_TAC;

    (*** The prologue ***)

    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; WORD_VAL;
                blake2s_compress_blocks] THEN
    ENSURES_INIT_TAC "s0" THEN BLAKE2S_EXPAND_H_TAC THEN
    WG_STEPS_TAC WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_EXEC (1--18) THEN
    BLAKE2S_FINAL_TAC;

    (*** One block: the values at its start as variables hh (the state),   ***)
    (*** m (the message words), ctr (the counter) and bi (its address)      ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[BLAKE2S_COMPRESS_BLOCKS_STEP; WG_COUNTER_STEP; WG_BLK_STEP] THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add blk (word(64 * i)),64) (stackpointer,272) /\
      nonoverlapping (word_add blk (word(64 * i)),64) (st:int64,48)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `64 * i + 64 <= 64 * val(nb:int64)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN BLAKE2S_EXPAND_H_TAC THEN
    MAP_EVERY (fun q ->
      MP_TAC(SPECL [`blk:int64`; `p:byte list`; `64 * val(nb:int64)`; `i:num`;
                    mk_small_numeral q; `s0:armstate`]
                   WG_READ_BLAKE2S_BLOCK64) THEN
      ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        CONV_TAC(LAND_CONV(NUM_REDUCE_CONV THENC REWRITE_CONV[WORD_ADD_0])) THEN
        DISCH_TAC]) (0--7) THEN
    ABBREV_TAC `hh = blake2s_compress_blocks h p (tt:int64)
                       (val(word_subword (inc:int64) (0,32):int32)) f i` THEN
    ABBREV_TAC `m = blake2s_block p i` THEN
    ABBREV_TAC `ctr = word_add (tt:int64)
                   (word(val(word_subword (inc:int64) (0,32):int32) * i))` THEN
    ABBREV_TAC `bi = word_add (blk:int64) (word(64 * i))` THEN
    MAP_EVERY (fun q ->
      let a = if q = 0 then `st:int64` else
              mk_comb(mk_comb(`word_add:int64->int64->int64`,`st:int64`),
                      mk_comb(`word:num->int64`,mk_small_numeral(8 * q))) in
      WG_JOIN_TAC (subst [a,`a:int64`; mk_small_numeral(2 * q + 1),`j:num`;
                          mk_small_numeral(2 * q),`k:num`]
        `read (memory :> bytes64 a) s0 = word_join ((hh:num->int32) j) (hh k)`))
      (0--3) THEN
    WG_RUN_TO_TAC WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_EXEC
      `word(pc + blake2s_compress_generic_loop1_back):int64` 2000 THEN
    BLAKE2S_COMPRESS_MATCH_TAC;

    (*** The branch back to the loop head ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN BLAKE2S_EXPAND_H_TAC THEN
    ARM_STEPS_TAC WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_EXEC [1] THEN
    BLAKE2S_FINAL_TAC;

    (*** The epilogue ***)

    REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN BLAKE2S_EXPAND_H_TAC THEN
    ARM_STEPS_TAC WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_EXEC (1--8) THEN
    BLAKE2S_FINAL_TAC]);;

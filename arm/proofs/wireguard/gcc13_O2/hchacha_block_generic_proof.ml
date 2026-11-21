(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of hchacha_block_generic_spec.ml: the state is       *)
(* copied to the stack 64 bits at a time and permuted by chacha_permute      *)
(* (simulated with its theorem, which keeps X0, the address of the copy, for *)
(* the memset after it); words 0..3 and 12..15 are stored 64 bits at a time, *)
(* and the copy zeroed with memset.                                          *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/hchacha_block_generic_spec.ml";;
needs "common/wireguard_kernel.ml";;

let WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "hchacha_block_generic"; layout_range "plt_memset"];;

let HCHACHA_BLOCK_GENERIC_PERMUTE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* The 64-bit words at a + 8 * k in s of the 32-bit words f(2 * k) and       *)
(* f(2 * k + 1), for k in ks, with the addresses in the form that the        *)
(* simulation uses.                                                          *)

let HCHACHA_JOIN_TAC a f s ks =
  MAP_EVERY (fun k ->
    let ak = if k = 0 then a else
             rand(concl(WG_ADDR_CONV
               (mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                        mk_comb(`word:num->int64`,
                                mk_small_numeral(8 * k)))))) in
    let fk i = mk_comb(f,mk_small_numeral i) in
    WG_JOIN_TAC (subst [ak,`a:int64`; s,`s:armstate`;
                        fk(2 * k + 1),`h:int32`; fk(2 * k),`l:int32`]
      `read (memory :> bytes64 a) s = word_join (h:int32) (l:int32)`)) ks;;

(* The 32 bytes of the result as four 64-bit words.                          *)

let HCHACHA_OUT_NUM = prove
 (`!f g:num->int32.
     num_of_bytelist (APPEND (chacha20_words 4 f) (chacha20_words 4 g)) =
     num_of_wordlist [word_join (f 1) (f 0):int64; word_join (f 3) (f 2);
                      word_join (g 1) (g 0); word_join (g 3) (g 2)]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_APPEND; chacha20_words;
              LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM;
              num_of_wordlist] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`(f:num->int32) 0`; `(f:num->int32) 1`; `(f:num->int32) 2`;
    `(f:num->int32) 3`; `(g:num->int32) 0`; `(g:num->int32) 1`;
    `(g:num->int32) 2`; `(g:num->int32) 3`] THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) ->
    let ms = find_terms (fun t -> is_binary "MOD" t) w in
    MAP_EVERY (fun t -> SUBGOAL_THEN (mk_eq(t,lhand t)) SUBST1_TAC THENL
      [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC]) ms) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `out:int64`; `xs:num->int32`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 96 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "memset" o REWRITE_RULE[memset_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN

  (*** Copy the state to stackpointer + 32 and permute the copy ***)

  HCHACHA_JOIN_TAC `st:int64` `xs:num->int32` `s0:armstate` (0--7) THEN
  WG_STEPS_TAC EXEC (1--17) THEN
  SUBGOAL_THEN
   `!i. i < 16
        ==> read (memory :> bytes32
                   (word_add stackpointer (word (32 + 4 * i)))) s17 = xs i`
  ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  HCHACHA_BLOCK_GENERIC_PERMUTE_TAC
   [`read X0 s`; `xs:num->int32`; `pc:num`; `read X30 s`] 18 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term ((=) `s18:armstate`)) (concl th))) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                     WG_ADDR_CONV)) THEN
  STRIP_TAC THEN

  (*** Words 0..3 and 12..15 into the output ***)

  HCHACHA_JOIN_TAC `word_add stackpointer (word 32):int64`
    `chacha20_rounds 10 xs` `s18:armstate` [0; 1; 6; 7] THEN
  WG_STEPS_TAC EXEC (19--25) THEN

  (*** The zeroing of the copy and the return ***)

  WG_PLT_TAC EXEC 25 THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 30 THEN
  ARM_STEPS_TAC EXEC (31--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HCHACHA_OUT_NUM] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN ASM_REWRITE_TAC[]);;

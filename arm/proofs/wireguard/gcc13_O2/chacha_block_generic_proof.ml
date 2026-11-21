(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of chacha_block_generic_spec.ml: the state is copied *)
(* to the stack 64 bits at a time and permuted by chacha_permute (simulated  *)
(* with its theorem); the loop of 16 additions is simulated through, and the *)
(* copy zeroed with memset.                                                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/chacha_block_generic_spec.ml";;
needs "common/wireguard_kernel.ml";;

let WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "chacha_block_generic"; layout_range "plt_memset"];;

let CHACHA_BLOCK_GENERIC_PERMUTE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* The 64-bit words of the state in s, for the copy.                         *)

let CHACHA_BLOCK_GENERIC_JOIN_TAC s =
  MAP_EVERY (fun k ->
    let a = if k = 0 then `st:int64` else
            mk_comb(mk_comb(`word_add:int64->int64->int64`,`st:int64`),
                    mk_comb(`word:num->int64`,mk_small_numeral(8 * k))) in
    WG_JOIN_TAC (subst [a,`a:int64`; s,`s:armstate`;
                        mk_small_numeral(2 * k + 1),`j:num`;
                        mk_small_numeral(2 * k),`k:num`]
      `read (memory :> bytes64 a) s = word_join ((xs:num->int32) j) (xs k)`))
   (0--7);;

(* The loop indexes the state and the output from st - 4 and out - 4 (with   *)
(* the index from 1): addresses word_add (word_sub v (word 4)) (word(4 * k)) *)
(* in the form that the simulation uses for its memory facts, and their      *)
(* values, word_add v (word(4 * k - 4)).                                     *)

let chacha_block_generic_minus4 v k =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,
                  mk_comb(mk_comb(`word_sub:int64->int64->int64`,v),
                          `word 4:int64`)),
          mk_comb(`word:num->int64`,mk_small_numeral(4 * k)));;

let CHACHA_BLOCK_GENERIC_MINUS4 v k =
  let r = if k = 1 then v else
          mk_comb(mk_comb(`word_add:int64->int64->int64`,v),
                  mk_comb(`word:num->int64`,mk_small_numeral(4 * k - 4))) in
  WORD_RULE (mk_eq(chacha_block_generic_minus4 v k,r));;

(* The 16 iterations, the k-th from step 25 + 8 * (k - 1), with the word of  *)
(* the state that it loads given at its address.                             *)

let CHACHA_BLOCK_GENERIC_LOOP_TAC =
  let EXEC = WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_EXEC in
  MAP_EVERY (fun k ->
    let s = mk_var("s"^string_of_int(24 + 8 * (k - 1)),`:armstate`) in
    let tm = vsubst [chacha_block_generic_minus4 `st:int64` k,`a:int64`;
                     s,`s:armstate`; mk_small_numeral(k - 1),`j:num`]
               `read (memory :> bytes32 a) s = (xs:num->int32) j` in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [REWRITE_TAC[CHACHA_BLOCK_GENERIC_MINUS4 `st:int64` k] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    WG_STEPS_TAC EXEC ((25 + 8 * (k - 1))--(32 + 8 * (k - 1)))) (1--16);;

let CHACHA20_ADD_SYM = prove
 (`!(xs:num->int32) i. word_add (chacha20_rounds 10 xs i) (xs i) =
                       word_add (xs i) (chacha20_rounds 10 xs i)`,
  REWRITE_TAC[WORD_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `out:int64`; `xs:num->int32`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 112 THEN
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
            [19; 20; 21; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN

  (*** Copy the state to stackpointer + 48 and permute the copy ***)

  CHACHA_BLOCK_GENERIC_JOIN_TAC `s0:armstate` THEN
  WG_STEPS_TAC EXEC (1--18) THEN
  SUBGOAL_THEN
   `!i. i < 16
        ==> read (memory :> bytes32
                   (word_add stackpointer (word (48 + 4 * i)))) s18 = xs i`
  ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CHACHA_BLOCK_GENERIC_PERMUTE_TAC
   [`read X0 s`; `xs:num->int32`; `pc:num`; `read X30 s`] 19 THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term ((=) `s19:armstate`)) (concl th))) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  STRIP_TAC THEN

  (*** The additions into the output ***)

  WG_STEPS_TAC EXEC (20--24) THEN
  CHACHA_BLOCK_GENERIC_LOOP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE
    (map (CHACHA_BLOCK_GENERIC_MINUS4 `out:int64`) (1--16))) THEN

  (*** The counter, the zeroing of the copy and the return ***)

  WG_STEPS_TAC EXEC (153--158) THEN
  WG_PLT_TAC EXEC 158 THEN
  WG_CALL_TAC "memset" EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 163 THEN
  ARM_STEPS_TAC EXEC (164--167) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[CHACHA20_WORDS_NUM] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[CHACHA20_ADD_SYM] THEN
    CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
    REWRITE_TAC[GSYM BYTES32_WBYTES] THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_0]]);;

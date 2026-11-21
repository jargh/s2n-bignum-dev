(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of chacha_permute_spec.ml: the loop of 10 double     *)
(* rounds, with the 16 words in W registers. The body is simulated from the  *)
(* abstract words y = chacha20_rounds i xs; the double round of the spec is  *)
(* evaluated on them explicitly (common/wireguard_tables.ml) and the values  *)
(* agree with those of the code modulo the associativity and commutativity   *)
(* of the additions and xors, once the rotations are written as the code     *)
(* does them, to the right.                                                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/chacha_permute_spec.ml";;
needs "common/wireguard_tables.ml";;

(* The code without the brk of the WARN at chacha_permute_ret1 + 4.          *)

let WIREGUARD_CHACHA_PERMUTE_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout "chacha_permute",layout "chacha_permute_ret1" + 4;
   layout "chacha_permute_ret1" + 8,
   layout "chacha_permute" + layout "chacha_permute_size"];;

(* ------------------------------------------------------------------------- *)
(* One double round on the words y 0, ..., y 15, as 16 explicit equations,   *)
(* and the left rotations by 16, 12, 8 and 7 as right rotations.             *)
(* ------------------------------------------------------------------------- *)

let CHACHA20_DOUBLE_ROUND_THS =
  let eq = REWRITE_CONV[chacha20_double_round] `chacha20_double_round y` in
  let tab = WG_NEST_EVAL CHACHA20_QROUND_STEP "chacha20_qround"
              (rand(concl eq)) in
  map (REWRITE_RULE[GSYM eq] o WG_AGREE_AT tab) (0--15);;

let CHACHA20_ROL_ROR_THS =
  map (fun n ->
    REWRITE_RULE[] (CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC
                               NUM_REDUCE_CONV)
      (ISPECL [`w:int32`; mk_small_numeral n] WORD_ROL_ROR)))
  [16; 12; 8; 7];;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop after i double rounds: word k of the state in   *)
(* the k-th of these registers, and the round counter (2 * i) in X8.         *)
(* ------------------------------------------------------------------------- *)

let chacha_permute_inv =
  let regs = [`X17`; `X16`; `X13`; `X10`; `X9`; `X7`; `X6`; `X5`;
              `X11`; `X15`; `X14`; `X12`; `X4`; `X3`; `X2`; `X1`] in
  let cs = map2 (fun r k ->
    mk_eq(list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
                       [r; `s:armstate`]),
          mk_comb(`word_zx:int32->int64`,
            list_mk_comb(`chacha20_rounds`,
                         [`i:num`; `xs:num->int32`; mk_small_numeral k]))))
    regs (0--15) in
  list_mk_abs([`i:num`; `s:armstate`],
    mk_conj(list_mk_conj(
      [`read X0 s = x`; `read X30 s = returnaddress`; `read X18 s = word 20`;
       `read X8 s = word(2 * i)`] @ cs),
      `~read ZF s /\ (read NF s <=> read VF s) <=> i < 10`));;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_CHACHA_PERMUTE_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`x:int64`; `xs:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ENSURES_WHILE_PUP_TAC `10` `pc + chacha_permute_loop1`
    `pc + chacha_permute_loop1_back` chacha_permute_inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Load the words into the registers ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    ARM_STEPS_TAC EXEC (1--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[chacha20_rounds] THEN
    CONV_TAC NUM_REDUCE_CONV;

    (*** A double round ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC `y = chacha20_rounds i xs` THEN
    ENSURES_INIT_TAC "s0" THEN
    WG_STEPS_TAC EXEC (1--98) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; chacha20_rounds] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC CHACHA20_DOUBLE_ROUND_THS THEN
    REWRITE_TAC CHACHA20_ROL_ROR_THS THEN
    REWRITE_TAC[WORD_ADD_AC; WG_WORD_XOR_AC] THEN
    UNDISCH_TAC `i < 10` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV;

    (*** The branch back ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];

    (*** Store the words ***)

    CONV_TAC NUM_REDUCE_CONV THEN ENSURES_INIT_TAC "s0" THEN
    WG_STEPS_TAC EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_0]]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of handshake_zero_spec.ml: the stores, and the zero  *)
(* regions from their 64-bit words (WG_ZERO_BYTES_TAC).                      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/handshake_zero_spec.ml";;

let WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "handshake_zero"];;

let HZ_EXEC = WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`hs:int64`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC HZ_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN WG_ZERO_BYTES_TAC);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The theorems of link.ml for the functions that use X25519, with           *)
(* s2n-bignum's curve25519_x25519_byte as curve25519_generic: the contract   *)
(* curve25519_generic_contract cfn ea el ev of a theorem is replaced by the  *)
(* hypotheses of CURVE25519_GENERIC_CONTRACT_S2N                             *)
(* (../curve25519_generic_s2n.ml) for cfn = word_add ea (word k), that the   *)
(* code is in the region (ea,el) of the kernel at the offset k. The theorems *)
(* are named with the suffix _S2N_X25519.                                    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/link.ml";;
needs "arm/proofs/wireguard/curve25519_generic_s2n.ml";;

(* ------------------------------------------------------------------------- *)
(* The rule, for a theorem !xs. A1 /\ ... /\ An ==> E with the contract as   *)
(* one of the Ai.                                                            *)
(* ------------------------------------------------------------------------- *)

let S2N_X25519_RULE =
  let is_contract t =
    try fst(dest_const(fst(strip_comb t))) = "curve25519_generic_contract"
    with Failure _ -> false in
  fun th ->
    let th1 = SPEC_ALL th in
    let ants,e = dest_imp(concl th1) in
    let c = find is_contract (conjuncts ants) in
    let cfn,ea,el,ev =
      match snd(strip_comb c) with
        [a;b;c;d] -> a,b,c,d | _ -> failwith "S2N_X25519_RULE" in
    let k = variant (frees(concl th1)) `k:num` in
    let f = list_mk_comb(`word_add:int64->int64->int64`,
                         [ea; mk_comb(`word:num->int64`,k)]) in
    let th2 = INST [f,cfn] th1 in
    let c' = vsubst [f,cfn] c in
    let hyp = vsubst [ea,`ea:int64`; el,`el:num`; ev,`ev:num`; k,`k:num`]
     `4 divides val(word_add ea (word k):int64) /\
      k + LENGTH curve25519_x25519_byte_mc <= el /\
      (ev DIV 2 EXP (8 * k)) MOD
      2 EXP (8 * LENGTH curve25519_x25519_byte_mc) =
      num_of_bytelist curve25519_x25519_byte_mc` in
    let ants2 = lhand(concl th2) in
    let ants' = list_mk_conj
      (map (fun a -> if a = c' then hyp else a) (conjuncts ants2)) in
    let imp = prove(mk_imp(ants',ants2),
      STRIP_TAC THEN
      SUBGOAL_THEN c' ASSUME_TAC THENL
       [MATCH_MP_TAC CURVE25519_GENERIC_CONTRACT_S2N THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]) in
    GEN_ALL(IMP_TRANS imp th2);;

(* ------------------------------------------------------------------------- *)
(* The theorems.                                                             *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_S2N_X25519 =
  S2N_X25519_RULE
   WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

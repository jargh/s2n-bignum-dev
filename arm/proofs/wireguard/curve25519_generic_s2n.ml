(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* s2n-bignum's curve25519_x25519_byte (X25519 of RFC 7748 on 32-byte        *)
(* arrays, proved in ../curve25519_x25519_byte.ml) satisfies                 *)
(* curve25519_generic_contract of contracts.ml when its code is in the       *)
(* kernel's region (ea,el) at the offset k (4-byte aligned): it can take the *)
(* place of the kernel's curve25519_generic (the HACL* code of               *)
(* lib/crypto/curve25519-hacl64.c), and then the theorems for the handshake  *)
(* need no assumption about X25519. It uses 384 bytes of stack, of the 1216  *)
(* that the contract allows.                                                 *)
(* ========================================================================= *)

needs "arm/proofs/curve25519_x25519_byte.ml";;
needs "arm/proofs/wireguard/contracts.ml";;

(* ------------------------------------------------------------------------- *)
(* A region at an offset in a larger one, the bytes of X25519, and a region  *)
(* that does not meet another region not meeting a part of it either.        *)
(* ------------------------------------------------------------------------- *)

let CONTAINED_MODULO_WORD_OFFSET = prove
 (`!a:int64 k l m.
     k + l <= m
     ==> contained_modulo (2 EXP 64) (val(word_add a (word k)),l) (val a,m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[contained_modulo] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXISTS_TAC `k + i` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_ASSOC]);;

let NUM_OF_BYTELIST_WG_DH = prove
 (`!sb pb. num_of_bytelist(wg_dh sb pb) =
           rfcx25519(num_of_bytelist sb,num_of_bytelist pb)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wg_dh; NUM_OF_BYTELIST_OF_NUM] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[rfcx25519] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p_25519` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PUREX25519_BOUND];
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV]);;

let NONOVERLAPPING_SUBREGION_RIGHT = prove
 (`!(a:int64) m b n (c:int64) l.
     nonoverlapping (a,m) (b,n) /\
     contained_modulo (2 EXP 64) (val c,l) (val b,n)
     ==> nonoverlapping (a,m) (c,l)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; DIMINDEX_64] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`val(a:int64)`; `m:num`; `val(b:int64)`; `n:num`] THEN
  ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL]);;

(* A theorem with ensures for a stronger precondition, a weaker              *)
(* postcondition and a larger frame.                                         *)

let ENSURES_MONO = prove
 (`!(step:A->A->bool) P Q C P' Q' C'.
     ensures step P Q C
     ==> (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ C subsumed C'
         ==> ensures step P' Q' C'`,
  MESON_TAC[ENSURES_PRECONDITION_THM; ENSURES_POSTCONDITION_THM;
            ENSURES_FRAME_SUBSUMED]);;

(* ------------------------------------------------------------------------- *)
(* The contract.                                                             *)
(* ------------------------------------------------------------------------- *)

let CURVE25519_GENERIC_CONTRACT_S2N = prove
 (`!ea el ev k.
     4 divides val(word_add ea (word k):int64) /\
     k + LENGTH curve25519_x25519_byte_mc <= el /\
     (ev DIV 2 EXP (8 * k)) MOD 2 EXP (8 * LENGTH curve25519_x25519_byte_mc) =
     num_of_bytelist curve25519_x25519_byte_mc
     ==> curve25519_generic_contract (word_add ea (word k)) ea el ev`,
  MAP_EVERY X_GEN_TAC [`ea:int64`; `el:num`; `ev:num`; `k:num`] THEN
  STRIP_TAC THEN REWRITE_TAC[curve25519_generic_contract] THEN
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `scalar:int64`; `point:int64`; `sb:byte list`;
    `pb:byte list`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ea:int64`; `k:num`; `LENGTH curve25519_x25519_byte_mc`;
                 `el:num`] CONTAINED_MODULO_WORD_OFFSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `f:int64 = word_add ea (word k)` THEN
  MP_TAC(SPECL
   [`out:int64`; `scalar:int64`; `num_of_bytelist sb`; `point:int64`;
    `num_of_bytelist pb`; `val(f:int64)`; `stackpointer:int64`;
    `returnaddress:int64`] CURVE25519_X25519_BYTE_SUBROUTINE_CORRECT) THEN
  REWRITE_TAC[WORD_VAL; ALL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM(fst CURVE25519_X25519_BYTE_EXEC)]
    THEN REPEAT CONJ_TAC THEN
    TRY(NONOVERLAPPING_TAC THEN NO_TAC) THEN
    MATCH_MP_TAC NONOVERLAPPING_SUBREGION_RIGHT THEN
    MAP_EVERY EXISTS_TAC [`ea:int64`; `el:num`] THEN
    ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_MONO) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[aligned_bytes_loaded; bytes_loaded;
                    READ_BYTELIST_EQ_BYTES] THEN
    MP_TAC(SPECL [`ea:int64`; `el:num`; `ev:num`; `k:num`;
                  `LENGTH curve25519_x25519_byte_mc`; `s:armstate`]
                 WG_READ_BYTES_OF_NUM) THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[NUM_OF_BYTELIST_WG_DH];
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `word_sub stackpointer (word 384):int64 =
                  word_add (word_sub stackpointer (word 1216)) (word 832)`
    SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SPEC_TAC(`word_sub stackpointer (word 1216):int64`,`b:int64`) THEN
    GEN_TAC THEN SUBSUMED_MAYCHANGE_TAC]);;

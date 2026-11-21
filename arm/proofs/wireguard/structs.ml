(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The kernel's data structures in the memory of an AArch64 state, in terms  *)
(* of the abstract values of common/wireguard_kernel.ml.                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/wireguard.ml";;
needs "common/wireguard_kernel.ml";;

(* ------------------------------------------------------------------------- *)
(* struct blake2s_state (120 bytes) at st, after the bytes d from the        *)
(* chained state h0, for the output length outlen: h[8] at 0 (the chained    *)
(* state), t[2] at 32 (the counter, the number of bytes compressed), f[2] at *)
(* 40 (zero), buf[64] at 48 (the bytes not compressed yet, then anything),   *)
(* buflen at 112 and outlen at 116.                                          *)
(* ------------------------------------------------------------------------- *)

let blake2s_state_at = new_definition
 `blake2s_state_at (st:int64) (h0:num->int32) (d:byte list) outlen
                   (s:armstate) <=>
    (!i. i < 8
         ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s =
             blake2s_chain h0 d i) /\
    read (memory :> bytes64 (word_add st (word 32))) s =
      word(64 * blake2s_nblocks d) /\
    read (memory :> bytes64 (word_add st (word 40))) s = word 0 /\
    read (memory :> bytes (word_add st (word 48),blake2s_buflen d)) s =
      num_of_bytelist(SUB_LIST(64 * blake2s_nblocks d,blake2s_buflen d) d) /\
    read (memory :> bytes32 (word_add st (word 112))) s =
      word(blake2s_buflen d) /\
    read (memory :> bytes32 (word_add st (word 116))) s = word outlen`;;

(* The facts of blake2s_state_at in state s as facts about the memory of     *)
(* s, which the simulation carries along, and conversely.                    *)

let BLAKE2S_STATE_EXPAND_TAC s =
  FIRST_ASSUM(MP_TAC o check (fun th ->
    match concl th with
      Comb(Comb(Comb(Comb(Comb(Const("blake2s_state_at",_),_),_),_),_),s')
        -> s' = s
    | _ -> false)) THEN
  REWRITE_TAC[blake2s_state_at] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
                     NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

let BLAKE2S_STATE_COLLECT_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[blake2s_state_at] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC];;

(* The state at st in s initialized (blake2s_init) for an unkeyed hash of 32 *)
(* bytes: zeroed (t and f facts as 64-bit words at st + 32 and st + 40),     *)
(* then h and buflen/outlen stored as 64-bit words. The facts for the        *)
(* 64-bit words of h and at st + 112 are split into their 32-bit halves and  *)
(* blake2s_state_at st (blake2s_h0 0 32) [] 32 s is added.                   *)

let BLAKE2S_STATE_INIT_TAC st s =
  let addr k =
    rhs(concl(WG_ADDR_CONV
      (mk_comb(mk_comb(`word_add:int64->int64->int64`,st),
               mk_comb(`word:num->int64`,mk_small_numeral k))))) in
  let split k =
    let l = vsubst [addr k,`a:int64`; s,`s:armstate`]
                   `read (memory :> bytes64 a) s` in
    FIRST_ASSUM(MP_TAC o MATCH_MP WG_BYTES64_SPLIT o
                check (fun th -> is_eq(concl th) && lhand(concl th) = l)) THEN
    CONV_TAC(LAND_CONV(WG_ADDR_CONV THENC WORD_REDUCE_CONV)) THEN
    STRIP_TAC in
  MAP_EVERY split [0; 8; 16; 24; 112] THEN
  SUBGOAL_THEN
   (vsubst [st,`st:int64`; s,`s:armstate`]
      `blake2s_state_at st (blake2s_h0 0 32) [] 32 s`)
  ASSUME_TAC THENL
   [REWRITE_TAC[blake2s_state_at; blake2s_chain; blake2s_nblocks;
                blake2s_buflen; LENGTH] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[blake2s_compress_blocks; blake2s_h0; blake2s_iv;
                SUB_LIST_CLAUSES; num_of_bytelist; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* struct poly1305_state (24 bytes, h64[3]) at st holding the accumulator a  *)
(* in the partly reduced form of poly1305-donna64: limbs of 44, 44 and 42    *)
(* bits (the middle one may have 45) congruent to a modulo 2^130 - 5.        *)
(* ------------------------------------------------------------------------- *)

let poly1305_h_at = new_definition
 `poly1305_h_at (st:int64) a (s:armstate) <=>
    val(read (memory :> bytes64 st) s) < 2 EXP 44 /\
    val(read (memory :> bytes64 (word_add st (word 8))) s) < 2 EXP 45 /\
    val(read (memory :> bytes64 (word_add st (word 16))) s) < 2 EXP 42 /\
    (val(read (memory :> bytes64 st) s) +
     2 EXP 44 * val(read (memory :> bytes64 (word_add st (word 8))) s) +
     2 EXP 88 * val(read (memory :> bytes64 (word_add st (word 16))) s))
    MOD (2 EXP 130 - 5) = a`;;

(* The limbs as (ghost) words, for the simulation, which only keeps facts    *)
(* read c s = v about the state; POLY1305_H_GHOST_TAC s does it for the      *)
(* assumption poly1305_h_at st a s.                                          *)

let POLY1305_H_AT_EXISTS = prove
 (`!st a s. poly1305_h_at st a s
     ==> ?h0 h1 h2:int64.
           read (memory :> bytes64 st) s = h0 /\
           read (memory :> bytes64 (word_add st (word 8))) s = h1 /\
           read (memory :> bytes64 (word_add st (word 16))) s = h2 /\
           val h0 < 2 EXP 44 /\ val h1 < 2 EXP 45 /\ val h2 < 2 EXP 42 /\
           (val h0 + 2 EXP 44 * val h1 + 2 EXP 88 * val h2) MOD
           (2 EXP 130 - 5) = a`,
  REWRITE_TAC[poly1305_h_at] THEN MESON_TAC[]);;

let POLY1305_H_GHOST_TAC s =
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `poly1305_h_at st a (s:armstate)`) (concl th) &&
       rand(concl th) = s
    then STRIP_ASSUME_TAC(MATCH_MP POLY1305_H_AT_EXISTS th)
    else failwith "POLY1305_H_GHOST_TAC");;

(* ------------------------------------------------------------------------- *)
(* struct poly1305_core_key (48 bytes) at k for the clamped r: the limbs of  *)
(* 44, 44 and 36 bits of r, then 20 times the last two (precomputed_s, whose *)
(* third word is not used).                                                  *)
(* ------------------------------------------------------------------------- *)

let poly1305_key_at = new_definition
 `poly1305_key_at (k:int64) r (s:armstate) <=>
    read (memory :> bytes64 k) s = word(r MOD 2 EXP 44) /\
    read (memory :> bytes64 (word_add k (word 8))) s =
      word((r DIV 2 EXP 44) MOD 2 EXP 44) /\
    read (memory :> bytes64 (word_add k (word 16))) s = word(r DIV 2 EXP 88) /\
    read (memory :> bytes64 (word_add k (word 24))) s =
      word(20 * (r DIV 2 EXP 44) MOD 2 EXP 44) /\
    read (memory :> bytes64 (word_add k (word 32))) s =
      word(20 * r DIV 2 EXP 88)`;;


(* ------------------------------------------------------------------------- *)
(* struct poly1305_desc_ctx (280 bytes) at desc for the 32-byte key k after  *)
(* the bytes d: buf[16] at 0 holding the bytes after the last whole block,   *)
(* buflen at 16, s[4] at 20 (the last 16 bytes of the key), the accumulator  *)
(* of the whole blocks at 40 (poly1305_h_at) and the key r at 64             *)
(* (poly1305_key_at, of the first 16 bytes of the key, clamped).             *)
(* ------------------------------------------------------------------------- *)

let poly1305_desc_at = new_definition
 `poly1305_desc_at (desc:int64) (k:byte list) (d:byte list) (s:armstate) <=>
    read (memory :> bytes(desc,LENGTH d MOD 16)) s =
      num_of_bytelist(SUB_LIST(16 * LENGTH d DIV 16,LENGTH d MOD 16) d) /\
    read (memory :> bytes32 (word_add desc (word 16))) s =
      word(LENGTH d MOD 16) /\
    read (memory :> bytes(word_add desc (word 20),16)) s =
      num_of_bytelist(SUB_LIST(16,16) k) /\
    poly1305_h_at (word_add desc (word 40))
      (poly1305_kacc (poly1305_r k) 0 d 1 (LENGTH d DIV 16)) s /\
    poly1305_key_at (word_add desc (word 64)) (poly1305_r k) s`;;

(* The facts that poly1305_desc_at stands for, with the limbs of the         *)
(* accumulator as (ghost) words, for the simulation.                         *)

let POLY1305_DESC_AT_EXPAND = prove
 (`!desc k (d:byte list) s.
     poly1305_desc_at desc k d s
     ==> ?h0 h1 h2:int64.
           read (memory :> bytes(desc,LENGTH d MOD 16)) s =
             num_of_bytelist
              (SUB_LIST(16 * LENGTH d DIV 16,LENGTH d MOD 16) d) /\
           read (memory :> bytes32 (word_add desc (word 16))) s =
             word(LENGTH d MOD 16) /\
           read (memory :> bytes(word_add desc (word 20),16)) s =
             num_of_bytelist(SUB_LIST(16,16) k) /\
           read (memory :> bytes64 (word_add desc (word 40))) s = h0 /\
           read (memory :> bytes64
                 (word_add (word_add desc (word 40)) (word 8))) s = h1 /\
           read (memory :> bytes64
                 (word_add (word_add desc (word 40)) (word 16))) s = h2 /\
           val h0 < 2 EXP 44 /\ val h1 < 2 EXP 45 /\ val h2 < 2 EXP 42 /\
           (val h0 + 2 EXP 44 * val h1 + 2 EXP 88 * val h2) MOD
           (2 EXP 130 - 5) =
             poly1305_kacc (poly1305_r k) 0 d 1 (LENGTH d DIV 16) /\
           read (memory :> bytes64 (word_add desc (word 64))) s =
             word(poly1305_r k MOD 2 EXP 44) /\
           read (memory :> bytes64
                 (word_add (word_add desc (word 64)) (word 8))) s =
             word((poly1305_r k DIV 2 EXP 44) MOD 2 EXP 44) /\
           read (memory :> bytes64
                 (word_add (word_add desc (word 64)) (word 16))) s =
             word(poly1305_r k DIV 2 EXP 88) /\
           read (memory :> bytes64
                 (word_add (word_add desc (word 64)) (word 24))) s =
             word(20 * (poly1305_r k DIV 2 EXP 44) MOD 2 EXP 44) /\
           read (memory :> bytes64
                 (word_add (word_add desc (word 64)) (word 32))) s =
             word(20 * poly1305_r k DIV 2 EXP 88)`,
  REWRITE_TAC[poly1305_desc_at; poly1305_h_at; poly1305_key_at] THEN
  MESON_TAC[]);;

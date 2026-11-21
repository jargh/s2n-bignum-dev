(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant data in the .rodata of the image that the code reads, as facts   *)
(* about the memory of any state where the image is loaded.                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;
needs "common/wireguard.ml";;

(* The zero point and the base point (u = 9) of include/crypto/curve25519.h, *)
(* 32 bytes each.                                                            *)

let wg_curve25519_null_point_data = new_definition
 `wg_curve25519_null_point_data:byte list =
   [word 0; word 0; word 0; word 0; word 0; word 0; word 0; word 0;
    word 0; word 0; word 0; word 0; word 0; word 0; word 0; word 0;
    word 0; word 0; word 0; word 0; word 0; word 0; word 0; word 0;
    word 0; word 0; word 0; word 0; word 0; word 0; word 0; word 0]`;;

let wg_curve25519_base_point_data = new_definition
 `wg_curve25519_base_point_data:byte list =
   [word 9; word 0; word 0; word 0; word 0; word 0; word 0; word 0;
    word 0; word 0; word 0; word 0; word 0; word 0; word 0; word 0;
    word 0; word 0; word 0; word 0; word 0; word 0; word 0; word 0;
    word 0; word 0; word 0; word 0; word 0; word 0; word 0; word 0]`;;

let WG_CURVE25519_NULL_POINT_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc
          ==> read (memory :> bytes(word(pc + rodata_curve25519_null_point),
                                    32)) s = 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
    wireguard_gcc13_O2_mc wg_curve25519_null_point_data
    (layout "rodata_curve25519_null_point"))) THEN
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[wg_curve25519_null_point_data; LENGTH; num_of_bytelist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN SIMP_TAC[]);;

let WG_CURVE25519_BASE_POINT_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc
          ==> read (memory :> bytes(word(pc + rodata_curve25519_base_point),
                                    32)) s = 9`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
    wireguard_gcc13_O2_mc wg_curve25519_base_point_data
    (layout "rodata_curve25519_base_point"))) THEN
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[wg_curve25519_base_point_data; LENGTH; num_of_bytelist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN SIMP_TAC[]);;

(* The labels of the keys of mac1 and of cookie replies in cookie.c,         *)
(* "mac1----" and "cookie--" (8 bytes each, without a terminating zero).     *)

let LENGTH_WG_LABEL_COOKIE = prove
 (`LENGTH wg_label_cookie = 8`,
  REWRITE_TAC[wg_label_cookie; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_WG_LABEL_MAC1 = prove
 (`LENGTH wg_label_mac1 = 8`,
  REWRITE_TAC[wg_label_mac1; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let WG_COOKIE_KEY_LABEL_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc
          ==> read (memory :> bytes(word(pc + rodata_cookie_key_label),8)) s =
              num_of_bytelist wg_label_cookie`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
    wireguard_gcc13_O2_mc wg_label_cookie
    (layout "rodata_cookie_key_label"))) THEN
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[wg_label_cookie; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

let WG_MAC1_KEY_LABEL_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc
          ==> read (memory :> bytes(word(pc + rodata_mac1_key_label),8)) s =
              num_of_bytelist wg_label_mac1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
    wireguard_gcc13_O2_mc wg_label_mac1
    (layout "rodata_mac1_key_label"))) THEN
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[wg_label_mac1; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

(* The strings of the construction and the identifier in noise.c,            *)
(* handshake_name (37 bytes) and identifier_name (34 bytes), without         *)
(* terminating zeros.                                                        *)

let LENGTH_WG_CONSTRUCTION = prove
 (`LENGTH wg_construction = 37`,
  REWRITE_TAC[wg_construction; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_WG_IDENTIFIER = prove
 (`LENGTH wg_identifier = 34`,
  REWRITE_TAC[wg_identifier; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let WG_HANDSHAKE_NAME_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc
          ==> read (memory :> bytes(word(pc + rodata_handshake_name),37)) s =
              num_of_bytelist wg_construction`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
    wireguard_gcc13_O2_mc wg_construction
    (layout "rodata_handshake_name"))) THEN
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[wg_construction; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

let WG_IDENTIFIER_NAME_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc
          ==> read (memory :> bytes(word(pc + rodata_identifier_name),34)) s =
              num_of_bytelist wg_identifier`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ALIGNED_BYTES_LOADED_SUBPROGRAM_RULE
    wireguard_gcc13_O2_mc wg_identifier
    (layout "rodata_identifier_name"))) THEN
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[wg_identifier; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

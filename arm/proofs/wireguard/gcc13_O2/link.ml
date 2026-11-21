(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* All the proofs about the gcc13_O2 image, in one session, callees first.   *)
(* Each proof file proves the theorems of its spec file relative to the      *)
(* contracts of its callees (see ../relative.ml); at the end, the theorems   *)
(* are closed: each assumption is discharged by the theorem proved for it,   *)
(* so the theorems below have no assumptions, except the assumed contracts   *)
(* (../relative_assumed.ml) of the functions that are not proved yet, which  *)
(* the theorems of their callers keep as assumptions.                        *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/relative_assumed.ml";;

needs "arm/proofs/wireguard/gcc13_O2/blake2s_compress_generic_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_constprop_0_2_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/precompute_key_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_hash_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/hmac_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/kdf_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/curve25519_fn_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/curve25519_generate_public_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_dh_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/message_ephemeral_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha_permute_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha_block_generic_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/hchacha_block_generic_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/hchacha_block_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_xor_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha_crypt_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_setkey_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_blocks_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_emit_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_init_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_update_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_final_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_encrypt_inner_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_decrypt_inner_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_encrypt_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_decrypt_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/xchacha_init_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/xchacha20poly1305_encrypt_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/xchacha20poly1305_decrypt_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_create_initiation_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_consume_initiation_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_create_response_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_consume_response_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_checker_precompute_device_keys_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_checker_precompute_peer_keys_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_add_mac_to_packet_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/make_cookie_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_validate_packet_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_message_create_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_message_consume_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_init_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/cookie_checker_init_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_constprop_0_1_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_init_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/handshake_zero_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/index_hashtable_remove_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_clear_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_set_static_identity_private_key_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_precompute_static_static_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_init_proof.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_expire_current_peer_keypairs_proof.ml";;

(* The contracts that are assumed: wg_index_hashtable_insert, whose code     *)
(* needs instructions that the model does not have (see its spec file).      *)

relative_assume
  WIREGUARD_INDEX_HASHTABLE_INSERT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* The contracts stated, proved and assumed, and those not proved, if any    *)

relative_report_assumed ();;

let WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_HCHACHA_BLOCK_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_HCHACHA_BLOCK_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CHACHA20POLY1305_ENCRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_CHACHA20POLY1305_ENCRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_CHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_XCHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_XCHACHA20POLY1305_ENCRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_XCHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_XCHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_PEER_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_PEER_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_COOKIE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_NOISE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

(* With the assumed contract for wg_index_hashtable_insert.                  *)

let WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close_assuming
    WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close
    WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

let WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  relative_close_assuming
    WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT;;

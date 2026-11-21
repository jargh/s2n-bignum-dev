(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ChaCha20, Poly1305 and the AEAD_CHACHA20_POLY1305 construction of        *)
(* RFC 8439, and XChaCha20-Poly1305 (HChaCha20 and the extended nonce) of    *)
(* draft-irtf-cfrg-xchacha-03, for byte-string inputs.                       *)
(*                                                                           *)
(* As in the RFC, the ChaCha20 state is 16 32-bit words (here a function     *)
(* from indices to words), keys and nonces are read as little-endian words   *)
(* (Section 2.3), the block counter is a 32-bit word, and Poly1305 works on  *)
(* numbers modulo 2^130 - 5 (Section 2.5). The AEAD encryption returns the   *)
(* ciphertext followed by the 16-byte tag, as WireGuard and the Linux kernel *)
(* use it, and the decryption returns NONE when the tag does not match.      *)
(* ========================================================================= *)

needs "Library/words.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Little-endian correspondence between byte lists and numbers (the same     *)
(* definitions as in common/words2.ml).                                      *)
(* ------------------------------------------------------------------------- *)

let num_of_bytelist = define
 `(num_of_bytelist [] = 0) /\
  (!h t. num_of_bytelist (CONS h t) = val(h:byte) + 256 * num_of_bytelist t)`;;

let bytelist_of_num = define
 `(bytelist_of_num 0 n = []) /\
  (bytelist_of_num (SUC k) n =
     CONS (word(n MOD 256):byte) (bytelist_of_num k (n DIV 256)))`;;

(* ------------------------------------------------------------------------- *)
(* The quarter round (Section 2.1) on x[a], x[b], x[c] and x[d], and two     *)
(* rounds: a column round and a diagonal round (Section 2.3).                *)
(* ------------------------------------------------------------------------- *)

let chacha20_qround = new_definition
 `chacha20_qround a b c d (x:num->int32) =
    let xa = word_add (x a) (x b) in
    let xd = word_rol (word_xor (x d) xa) 16 in
    let xc = word_add (x c) xd in
    let xb = word_rol (word_xor (x b) xc) 12 in
    let xa' = word_add xa xb in
    let xd' = word_rol (word_xor xd xa') 8 in
    let xc' = word_add xc xd' in
    let xb' = word_rol (word_xor xb xc') 7 in
    \i. if i = a then xa' else if i = b then xb'
        else if i = c then xc' else if i = d then xd' else x i`;;

let chacha20_double_round = new_definition
 `chacha20_double_round (x:num->int32) =
    chacha20_qround 3 4  9 14
     (chacha20_qround 2 7  8 13
       (chacha20_qround 1 6 11 12
         (chacha20_qround 0 5 10 15
           (chacha20_qround 3 7 11 15
             (chacha20_qround 2 6 10 14
               (chacha20_qround 1 5  9 13
                 (chacha20_qround 0 4  8 12 x)))))))`;;

let chacha20_rounds = define
 `chacha20_rounds 0 x = x /\
  chacha20_rounds (SUC n) x = chacha20_double_round (chacha20_rounds n x)`;;

(* ------------------------------------------------------------------------- *)
(* The state for a 32-byte key, a 32-bit block counter and a 12-byte nonce,  *)
(* and the block function (Section 2.3), giving 64 bytes of keystream.       *)
(* ------------------------------------------------------------------------- *)

let chacha20_le32 = new_definition
 `chacha20_le32 (b:byte list) k =
    word(num_of_bytelist(SUB_LIST(4 * k,4) b)):int32`;;

let chacha20_state = new_definition
 `chacha20_state (key:byte list) counter (nonce:byte list) =
    \i. if i = 0 then word 0x61707865
        else if i = 1 then word 0x3320646e
        else if i = 2 then word 0x79622d32
        else if i = 3 then word 0x6b206574
        else if i < 12 then chacha20_le32 key (i - 4)
        else if i = 12 then word counter
        else chacha20_le32 nonce (i - 13):int32`;;

let chacha20_words = new_definition
 `chacha20_words n (x:num->int32) =
    bytelist_of_num (4 * n) (nsum (0..n-1) (\i. val(x i) * 2 EXP (32 * i)))`;;

let chacha20_block = new_definition
 `chacha20_block key counter nonce =
    let x = chacha20_state key counter nonce in
    let y = chacha20_rounds 10 x in
    chacha20_words 16 (\i. word_add (y i) (x i))`;;

(* ------------------------------------------------------------------------- *)
(* Encryption (Section 2.4): the XOR of the input with the keystream of the  *)
(* blocks counter, counter + 1, ... (decryption is the same).                *)
(* ------------------------------------------------------------------------- *)

let chacha20_encrypt = new_definition
 `chacha20_encrypt key counter nonce (m:byte list) =
    list_of_seq
     (\i. word_xor (EL i m)
           (EL (i MOD 64) (chacha20_block key (counter + i DIV 64) nonce)))
     (LENGTH m)`;;

(* ------------------------------------------------------------------------- *)
(* Poly1305 (Section 2.5) with a 32-byte one-time key (r,s): the 16-byte     *)
(* blocks of the message, the last one possibly shorter, each with a one     *)
(* byte appended, are accumulated by acc := ((acc + n) * r) mod (2^130 - 5), *)
(* and the tag is the low 128 bits of acc + s, as 16 bytes.                  *)
(* ------------------------------------------------------------------------- *)

let poly1305_acc = define
 `poly1305_acc r (msg:byte list) 0 = 0 /\
  poly1305_acc r msg (SUC j) =
    let c = SUB_LIST(16 * j,16) msg in
    ((poly1305_acc r msg j + num_of_bytelist c + 2 EXP (8 * LENGTH c)) * r)
    MOD (2 EXP 130 - 5)`;;

let poly1305_r = new_definition
 `poly1305_r (key:byte list) =
    val(word_and (word(num_of_bytelist(SUB_LIST(0,16) key)):int128)
                 (word 0x0ffffffc0ffffffc0ffffffc0fffffff))`;;

let poly1305 = new_definition
 `poly1305 (key:byte list) (msg:byte list) =
    bytelist_of_num 16
     (poly1305_acc (poly1305_r key) msg ((LENGTH msg + 15) DIV 16) +
      num_of_bytelist(SUB_LIST(16,16) key))`;;

(* ------------------------------------------------------------------------- *)
(* AEAD_CHACHA20_POLY1305 (Sections 2.6 and 2.8). The one-time Poly1305 key *)
(* is the start of the keystream block 0, and the input is encrypted from    *)
(* block 1. The tag covers the AAD and the ciphertext, each padded with      *)
(* zeros to a multiple of 16 bytes, and their lengths as 8-byte numbers.     *)
(* ------------------------------------------------------------------------- *)

let poly1305_pad16 = new_definition
 `poly1305_pad16 n = REPLICATE ((16 - n MOD 16) MOD 16) (word 0:byte)`;;

let aead_chacha20_poly1305_tag = new_definition
 `aead_chacha20_poly1305_tag key nonce (aad:byte list) (c:byte list) =
    let otk = SUB_LIST(0,32) (chacha20_block key 0 nonce) in
    poly1305 otk
     (APPEND aad (APPEND (poly1305_pad16 (LENGTH aad))
       (APPEND c (APPEND (poly1305_pad16 (LENGTH c))
         (APPEND (bytelist_of_num 8 (LENGTH aad))
                 (bytelist_of_num 8 (LENGTH c)))))))`;;

let aead_chacha20_poly1305_encrypt = new_definition
 `aead_chacha20_poly1305_encrypt key nonce (plain:byte list) (aad:byte list) =
    let c = chacha20_encrypt key 1 nonce plain in
    APPEND c (aead_chacha20_poly1305_tag key nonce aad c)`;;

let aead_chacha20_poly1305_decrypt = new_definition
 `aead_chacha20_poly1305_decrypt key nonce (ct:byte list) (aad:byte list) =
    if LENGTH ct < 16 then NONE else
    let c = SUB_LIST(0,LENGTH ct - 16) ct in
    if aead_chacha20_poly1305_tag key nonce aad c =
       SUB_LIST(LENGTH ct - 16,16) ct
    then SOME(chacha20_encrypt key 1 nonce c)
    else NONE`;;

(* ------------------------------------------------------------------------- *)
(* HChaCha20 and XChaCha20-Poly1305 (draft-irtf-cfrg-xchacha-03 Sections     *)
(* 2.2 and 2.3): the subkey is words 0..3 and 12..15 of the 20 rounds of the *)
(* state with the first 16 bytes of the 24-byte nonce in words 12..15 (no    *)
(* feed-forward), and the 12-byte nonce for it is four zero bytes followed   *)
(* by the last 8 bytes of the nonce.                                         *)
(* ------------------------------------------------------------------------- *)

let hchacha20 = new_definition
 `hchacha20 (key:byte list) (nonce:byte list) =
    let x = chacha20_state key (val(chacha20_le32 nonce 0))
                           (SUB_LIST(4,12) nonce) in
    let y = chacha20_rounds 10 x in
    APPEND (chacha20_words 4 y) (chacha20_words 4 (\i. y(i + 12)))`;;

let xchacha20_nonce = new_definition
 `xchacha20_nonce (nonce:byte list) =
    APPEND (REPLICATE 4 (word 0:byte)) (SUB_LIST(16,8) nonce)`;;

let xchacha20_poly1305_encrypt = new_definition
 `xchacha20_poly1305_encrypt key nonce plain aad =
    aead_chacha20_poly1305_encrypt (hchacha20 key (SUB_LIST(0,16) nonce))
                                   (xchacha20_nonce nonce) plain aad`;;

let xchacha20_poly1305_decrypt = new_definition
 `xchacha20_poly1305_decrypt key nonce ct aad =
    aead_chacha20_poly1305_decrypt (hchacha20 key (SUB_LIST(0,16) nonce))
                                   (xchacha20_nonce nonce) ct aad`;;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;

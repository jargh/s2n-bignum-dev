(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The WireGuard handshake (Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s), for     *)
(* byte strings, following Section 5.4 of J. A. Donenfeld, "WireGuard: Next  *)
(* Generation Kernel Network Tunnel" (NDSS 2017), with the checks that the   *)
(* Linux implementation (drivers/net/wireguard/noise.c) adds: Diffie-Hellman *)
(* results and the precomputed static-static secret must not be all zero.    *)
(*                                                                           *)
(* The primitives are those of Section 5.4 (HASH, MAC, HMAC, KDF, DH, AEAD,  *)
(* XAEAD, TAI64N). Each step of the handshake is a function of its inputs,   *)
(* including the random ephemeral key, the timestamp and the indices, which  *)
(* the implementation gets from the kernel; it returns NONE where the        *)
(* implementation gives up. The MACs of the messages (mac1, mac2) are added  *)
(* or checked separately, as in cookie.c.                                    *)
(* ========================================================================= *)

needs "common/rfc7693.ml";;
needs "common/rfc8439.ml";;
needs "EC/x25519.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The ASCII strings of Section 5.4 as byte lists.                           *)
(* ------------------------------------------------------------------------- *)

let wg_string_term s =
  mk_list(List.init (String.length s)
           (fun i -> mk_comb(`word:num->byte`,
                             mk_small_numeral(Char.code s.[i]))),
          `:byte`);;

let wg_construction = new_definition(mk_eq(`wg_construction:byte list`,
  wg_string_term "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s"));;

let wg_identifier = new_definition(mk_eq(`wg_identifier:byte list`,
  wg_string_term "WireGuard v1 zx2c4 Jason@zx2c4.com"));;

let wg_label_mac1 = new_definition(mk_eq(`wg_label_mac1:byte list`,
  wg_string_term "mac1----"));;

let wg_label_cookie = new_definition(mk_eq(`wg_label_cookie:byte list`,
  wg_string_term "cookie--"));;

(* ------------------------------------------------------------------------- *)
(* The primitives. HMAC is RFC 2104 with BLAKE2s-256 (64-byte blocks), and   *)
(* KDF_n is HKDF (RFC 5869) with it: t0 = HMAC(key,input), t1 = HMAC(t0,1)   *)
(* and t_(i+1) = HMAC(t0, t_i || i + 1), returning t1, ..., tn.              *)
(* ------------------------------------------------------------------------- *)

let wg_hash = new_definition
 `wg_hash (x:byte list) = blake2s [] 32 x`;;

let wg_mac = new_definition
 `wg_mac (key:byte list) (x:byte list) = blake2s key 16 x`;;

let wg_hmac = new_definition
 `wg_hmac (key:byte list) (x:byte list) =
    let k = if LENGTH key > 64 then wg_hash key else key in
    let k0 = APPEND k (REPLICATE (64 - LENGTH k) (word 0)) in
    wg_hash (APPEND (MAP (word_xor (word 0x5c)) k0)
                    (wg_hash (APPEND (MAP (word_xor (word 0x36)) k0) x)))`;;

let wg_kdf_t = define
 `wg_kdf_t (t0:byte list) 0 = [] /\
  wg_kdf_t t0 (SUC i) =
    wg_hmac t0 (APPEND (wg_kdf_t t0 i) [word(i + 1)])`;;

let wg_kdf1 = new_definition
 `wg_kdf1 key x = let t0 = wg_hmac key x in wg_kdf_t t0 1`;;

let wg_kdf2 = new_definition
 `wg_kdf2 key x = let t0 = wg_hmac key x in (wg_kdf_t t0 1,wg_kdf_t t0 2)`;;

let wg_kdf3 = new_definition
 `wg_kdf3 key x =
    let t0 = wg_hmac key x in (wg_kdf_t t0 1,wg_kdf_t t0 2,wg_kdf_t t0 3)`;;

(* X25519 (RFC 7748, rfcx25519 of EC/x25519.ml) on 32-byte little-endian     *)
(* strings, and the public key for a private one (the base point u = 9).     *)

let wg_dh = new_definition
 `wg_dh (priv:byte list) (pub:byte list) =
    bytelist_of_num 32 (rfcx25519(num_of_bytelist priv,num_of_bytelist pub))`;;

let wg_dh_pubkey = new_definition
 `wg_dh_pubkey priv = wg_dh priv (bytelist_of_num 32 9)`;;

let wg_zero32 = new_definition
 `wg_zero32:byte list = REPLICATE 32 (word 0)`;;

(* The clamping that the kernel applies to random private keys (the same as  *)
(* X25519's own, so wg_dh (wg_clamp k) = wg_dh k).                           *)

let wg_clamp = new_definition
 `wg_clamp (k:byte list) =
    APPEND [word_and (EL 0 k) (word 248)]
     (APPEND (SUB_LIST(1,30) k)
       [word_or (word_and (EL 31 k) (word 127)) (word 64)])`;;

(* AEAD with the 96-bit nonce of 32 zero bits and the 64-bit little-endian   *)
(* counter, and its decryption; XAEAD with a 24-byte nonce.                  *)

let wg_aead_nonce = new_definition
 `wg_aead_nonce counter =
    APPEND (REPLICATE 4 (word 0:byte)) (bytelist_of_num 8 counter)`;;

let wg_aead = new_definition
 `wg_aead key counter plain auth =
    aead_chacha20_poly1305_encrypt key (wg_aead_nonce counter) plain auth`;;

let wg_aead_decrypt = new_definition
 `wg_aead_decrypt key counter ct auth =
    aead_chacha20_poly1305_decrypt key (wg_aead_nonce counter) ct auth`;;

let wg_xaead = new_definition
 `wg_xaead key nonce plain auth =
    xchacha20_poly1305_encrypt key nonce plain auth`;;

let wg_xaead_decrypt = new_definition
 `wg_xaead_decrypt key nonce ct auth =
    xchacha20_poly1305_decrypt key nonce ct auth`;;

(* TAI64N as the kernel computes it (noise.c, tai64n_now) from the real-time *)
(* clock (seconds, nanoseconds as 64-bit words): the TAI64 label 2^62 + 10   *)
(* plus the seconds, then the nanoseconds rounded down to a multiple of      *)
(* 2^24, both big-endian.                                                    *)

let wg_tai64n = new_definition
 `wg_tai64n (sec:int64) (nsec:int64) =
    APPEND (REVERSE(bytelist_of_num 8
                     (val(word_add (word 0x400000000000000a) sec))))
           (REVERSE(bytelist_of_num 4
                     (val(word_and nsec (word_not(word 0xffffff))))))`;;

(* ------------------------------------------------------------------------- *)
(* The handshake state (chaining key, hash) and the Noise steps.             *)
(* ------------------------------------------------------------------------- *)

let wg_ck0 = new_definition
 `wg_ck0 = wg_hash wg_construction`;;

let wg_h0 = new_definition
 `wg_h0 = wg_hash (APPEND wg_ck0 wg_identifier)`;;

let wg_mix_hash = new_definition
 `wg_mix_hash h (x:byte list) = wg_hash (APPEND h x)`;;

(* Handshake state for a peer with static public key spub.                   *)

let wg_handshake_init = new_definition
 `wg_handshake_init spub = (wg_ck0,wg_mix_hash wg_h0 spub)`;;

(* An ephemeral public key e mixed into (ck,h).                              *)

let wg_ephemeral = new_definition
 `wg_ephemeral (ck,h) e = (wg_kdf1 ck e,wg_mix_hash h e)`;;

(* Encryption of plain with key k, authenticating h, and the new hash.       *)

let wg_encrypt = new_definition
 `wg_encrypt k h plain =
    let c = wg_aead k 0 plain h in (c,wg_mix_hash h c)`;;

(* Decryption of c (with its tag), and the new hash, or NONE.                *)

let wg_decrypt = new_definition
 `wg_decrypt k h c =
    match wg_aead_decrypt k 0 c h with
      SOME p -> SOME(p,wg_mix_hash h c)
    | NONE -> NONE`;;

(* ------------------------------------------------------------------------- *)
(* The messages, without their MACs (the first 116 bytes of the 148-byte     *)
(* initiation and the first 60 bytes of the 92-byte response), as the        *)
(* fields of Sections 5.4.2 and 5.4.3, little-endian where they are numbers. *)
(* ------------------------------------------------------------------------- *)

let wg_le32 = new_definition
 `wg_le32 (x:int32) = bytelist_of_num 4 (val x)`;;

let wg_initiation_msg = new_definition
 `wg_initiation_msg (sender:int32) e es et =
    APPEND (wg_le32 (word 1))
     (APPEND (wg_le32 sender) (APPEND e (APPEND es et)))`;;

let wg_response_msg = new_definition
 `wg_response_msg (sender:int32) (receiver:int32) e empty =
    APPEND (wg_le32 (word 2))
     (APPEND (wg_le32 sender) (APPEND (wg_le32 receiver) (APPEND e empty)))`;;

(* ------------------------------------------------------------------------- *)
(* Creating an initiation (Section 5.4.2, noise.c's create_initiation): the  *)
(* initiator has the static key pair (spriv,spub), knows the responder's     *)
(* static public key rpub, has precomputed ss = DH(spriv,rpub), and uses the *)
(* ephemeral private key epriv, the timestamp and the sender index. The      *)
(* result is the message and the new (ck,h), or NONE if a public key or DH   *)
(* result is zero.                                                           *)
(* ------------------------------------------------------------------------- *)

let wg_create_initiation = new_definition
 `wg_create_initiation spub rpub ss epriv timestamp sender =
    let ck,h = wg_handshake_init rpub in
    let epub = wg_dh_pubkey epriv in
    let ck,h = wg_ephemeral (ck,h) epub in
    let dh1 = wg_dh epriv rpub in
    let ck,k = wg_kdf2 ck dh1 in
    let es,h = wg_encrypt k h spub in
    let ck,k = wg_kdf2 ck ss in
    let et,h = wg_encrypt k h timestamp in
    if epriv = wg_zero32 \/ epub = wg_zero32 \/ dh1 = wg_zero32 \/
       ss = wg_zero32
    then NONE
    else SOME(wg_initiation_msg sender epub es et,ck,h)`;;

(* ------------------------------------------------------------------------- *)
(* Consuming an initiation (noise.c's consume_initiation), in two stages, as *)
(* the static-static secret of the peer is found from the decrypted static   *)
(* key: first, with the responder's static key pair (spriv,spub), the        *)
(* initiator's ephemeral key e, its static public key s and the state; then  *)
(* with the precomputed ss for that peer, the timestamp and the state. The   *)
(* message msg is at least the first 116 bytes of the initiation.            *)
(* ------------------------------------------------------------------------- *)

let wg_consume_initiation_static = new_definition
 `wg_consume_initiation_static spriv spub (msg:byte list) =
    let e = SUB_LIST(8,32) msg in
    let ck,h = wg_handshake_init spub in
    let ck,h = wg_ephemeral (ck,h) e in
    let dh1 = wg_dh spriv e in
    let ck,k = wg_kdf2 ck dh1 in
    if dh1 = wg_zero32 then NONE else
    match wg_decrypt k h (SUB_LIST(40,48) msg) with
      SOME(s,h) -> SOME(e,s,ck,h)
    | NONE -> NONE`;;

let wg_consume_initiation_timestamp = new_definition
 `wg_consume_initiation_timestamp ss (ck,h) (msg:byte list) =
    let ck,k = wg_kdf2 ck ss in
    if ss = wg_zero32 then NONE else
    match wg_decrypt k h (SUB_LIST(88,28) msg) with
      SOME(t,h) -> SOME(t,ck,h)
    | NONE -> NONE`;;

(* ------------------------------------------------------------------------- *)
(* Creating a response (Section 5.4.3, noise.c's create_response) from the   *)
(* state (ck,h) after the initiation, the initiator's ephemeral and static   *)
(* public keys, the preshared key, the ephemeral private key and the         *)
(* indices; and consuming it (consume_response) with the state after the     *)
(* initiation, the initiator's ephemeral and static private keys and the     *)
(* preshared key, returning the responder's ephemeral key and the new state. *)
(* ------------------------------------------------------------------------- *)

let wg_create_response = new_definition
 `wg_create_response (ck,h) repub rspub psk epriv sender receiver =
    let epub = wg_dh_pubkey epriv in
    let ck,h = wg_ephemeral (ck,h) epub in
    let dh1 = wg_dh epriv repub in
    let ck = wg_kdf1 ck dh1 in
    let dh2 = wg_dh epriv rspub in
    let ck = wg_kdf1 ck dh2 in
    let ck,tau,k = wg_kdf3 ck psk in
    let h = wg_mix_hash h tau in
    let empty,h = wg_encrypt k h [] in
    if epriv = wg_zero32 \/ epub = wg_zero32 \/ dh1 = wg_zero32 \/
       dh2 = wg_zero32
    then NONE
    else SOME(wg_response_msg sender receiver epub empty,ck,h)`;;

let wg_consume_response = new_definition
 `wg_consume_response (ck,h) epriv spriv psk (msg:byte list) =
    let e = SUB_LIST(12,32) msg in
    let ck,h = wg_ephemeral (ck,h) e in
    let dh1 = wg_dh epriv e in
    let ck = wg_kdf1 ck dh1 in
    let dh2 = wg_dh spriv e in
    let ck = wg_kdf1 ck dh2 in
    let ck,tau,k = wg_kdf3 ck psk in
    let h = wg_mix_hash h tau in
    if dh1 = wg_zero32 \/ dh2 = wg_zero32 then NONE else
    match wg_decrypt k h (SUB_LIST(44,16) msg) with
      SOME(p,h) -> SOME(e,ck,h)
    | NONE -> NONE`;;

(* ------------------------------------------------------------------------- *)
(* The transport keys (Section 5.4.5): the initiator sends with the first    *)
(* and receives with the second, the responder the other way round.          *)
(* ------------------------------------------------------------------------- *)

let wg_transport_keys = new_definition
 `wg_transport_keys ck = wg_kdf2 ck []`;;

(* ------------------------------------------------------------------------- *)
(* The MACs of a message (Section 5.4.4, cookie.c): mac1 is keyed with the  *)
(* hash of the label and the receiver's static public key and covers the     *)
(* message before it; mac2 is keyed with a cookie and covers the message up  *)
(* to it, or is zero.                                                        *)
(* ------------------------------------------------------------------------- *)

let wg_mac1_key = new_definition
 `wg_mac1_key rpub = wg_hash (APPEND wg_label_mac1 rpub)`;;

let wg_mac1 = new_definition
 `wg_mac1 rpub (msg:byte list) = wg_mac (wg_mac1_key rpub) msg`;;

let wg_cookie_key = new_definition
 `wg_cookie_key rpub = wg_hash (APPEND wg_label_cookie rpub)`;;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;

(* ------------------------------------------------------------------------- *)
(* EC/x25519.ml (through Library/primitive.ml) leaves the real numbers as    *)
(* the default for overloaded arithmetic; restore the natural numbers, as    *)
(* the proofs loaded later assume.                                           *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

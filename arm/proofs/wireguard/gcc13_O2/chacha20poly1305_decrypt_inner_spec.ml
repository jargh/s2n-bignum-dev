(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* __chacha20poly1305_decrypt(dst, src, src_len, ad, ad_len, chacha_state)   *)
(* of the kernel's lib/crypto/chacha20poly1305.c in the image (named         *)
(* chacha20poly1305_decrypt_inner here, apart from the exported              *)
(* chacha20poly1305_decrypt that calls it): with the ChaCha20 state at st    *)
(* for the key and the 12-byte nonce with counter 0, the result is whether   *)
(* the RFC 8439 AEAD decryption of the src_len bytes at src with the         *)
(* additional data at ad (common/rfc8439.ml) succeeds, in which case the     *)
(* plaintext is written to dst. If src_len < 16 it fails at once; otherwise  *)
(* the tag of the first src_len - 16 bytes is computed as for encryption     *)
(* and compared with the last 16 by __crypto_memneq, and only if they are    *)
(* the same is the ciphertext decrypted by chacha_crypt. The state is not    *)
(* zeroed (the counter is left advanced). The sizes are truncated to 32      *)
(* bits for chacha_crypt and poly1305_update, so they are bounded here.      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha_crypt_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_init_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_final_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy and *)
(* the data for the zero page (wg_zero_page_va in ../contracts.ml). The code *)
(* and its callees use 656 bytes of stack, which must not contain the        *)
(* address 0 (the poly1305_desc_ctx being on the stack). dst may be src;     *)
(* only its first src_len - 16 bytes are written, so they are all that must  *)
(* be separate from the other objects (and dst may be NULL if src_len is     *)
(* 16).                                                                      *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst src len ad adlen st key nonce ct al kv ms mset ea1 el1 ev1
   mcpy ea2 el2 ev2 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH key = 32 /\ LENGTH nonce = 12 /\
     LENGTH ct = val(len:int64) /\ LENGTH al = val(adlen:int64) /\
     val len + 16 < 2 EXP 32 /\ val adlen + 16 < 2 EXP 32 /\
     nonoverlapping (word_sub stackpointer (word 656),656) (word 0,1) /\
     (dst = src \/ nonoverlapping (dst,val len - 16) (src,val len)) /\
     ALL (nonoverlapping (word_sub stackpointer (word 656),656))
         [(word pc,wireguard_size); (word(pc + data_kimage_voffset),8);
          (word(pc + data_memstart_addr),8);
          (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
          (st,64); (dst,val len - 16); (src,val len); (ad,val adlen);
          (ea1,el1); (ea2,el2); (word(pc + got_memset),8);
          (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (st,64))
         [(word pc,wireguard_size);
          (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
          (dst,val len - 16); (src,val len); (ad,val adlen);
          (ea1,el1); (ea2,el2); (word(pc + got_memset),8);
          (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (dst,val len - 16))
         [(word pc,wireguard_size); (ea1,el1); (word(pc + got_memset),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + __chacha20poly1305_decrypt) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [dst; src; len; ad; adlen; st] s /\
               (!i. i < 16
                    ==> read (memory :> bytes32(word_add st (word(4 * i)))) s =
                        chacha20_state key 0 nonce i) /\
               read (memory :> bytes(src,val len)) s = num_of_bytelist ct /\
               read (memory :> bytes(ad,val adlen)) s = num_of_bytelist al /\
               read (memory :> bytes64(word(pc + data_kimage_voffset))) s =
                 kv /\
               read (memory :> bytes64(word(pc + data_memstart_addr))) s =
                 ms /\
               read (memory :>
                     bytes(wg_zero_page_va (word(pc + data_empty_zero_page))
                                           kv ms,32)) s = 0 /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
                 (if aead_chacha20_poly1305_decrypt key nonce ct al = NONE
                  then word 0 else word 1) /\
               (!p. aead_chacha20_poly1305_decrypt key nonce ct al = SOME p
                    ==> read (memory :> bytes(dst,LENGTH p)) s =
                        num_of_bytelist p))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,val len - 16);
                      memory :> bytes(st,64);
                      memory :> bytes(word_sub stackpointer (word 656),656)])`;;

let WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

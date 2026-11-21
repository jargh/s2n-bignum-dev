(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* chacha20poly1305_decrypt(dst, src, src_len, ad, ad_len, nonce, key) of    *)
(* the kernel's lib/crypto/chacha20poly1305.c in the image: the result is    *)
(* whether the WireGuard AEAD decryption (wg_aead_decrypt of                 *)
(* common/wireguard.ml) of the src_len bytes at src with the ad at ad and    *)
(* the 32-byte key at key succeeds, in which case the plaintext is written   *)
(* to dst. The ChaCha20 state is built on the stack and                      *)
(* __chacha20poly1305_decrypt (chacha20poly1305_decrypt_inner here) called;  *)
(* the state is then zeroed with memset (memzero_explicit), and so are the   *)
(* copies of the key and nonce. The sizes are bounded as for it.             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_decrypt_inner_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy and *)
(* the data for the zero page. The code and its callees use 800 bytes of     *)
(* stack, which must not contain the address 0. dst may be src; only its     *)
(* first src_len - 16 bytes are written, so they are all that must be        *)
(* separate from the other objects (and dst may be NULL if src_len is 16).   *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst src len ad adlen nonce key kb ct al kv ms mset ea1 el1 ev1
   mcpy ea2 el2 ev2 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH kb = 32 /\
     LENGTH ct = val(len:int64) /\ LENGTH al = val(adlen:int64) /\
     val len + 16 < 2 EXP 32 /\ val adlen + 16 < 2 EXP 32 /\
     nonoverlapping (word_sub stackpointer (word 800),800) (word 0,1) /\
     (dst = src \/ nonoverlapping (dst,val len - 16) (src,val len)) /\
     ALL (nonoverlapping (word_sub stackpointer (word 800),800))
         [(word pc,wireguard_size); (word(pc + data_kimage_voffset),8);
          (word(pc + data_memstart_addr),8);
          (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
          (key,32); (dst,val len - 16); (src,val len); (ad,val adlen);
          (ea1,el1); (ea2,el2); (word(pc + got_memset),8);
          (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (dst,val len - 16))
         [(word pc,wireguard_size); (ea1,el1); (word(pc + got_memset),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + chacha20poly1305_decrypt) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [dst; src; len; ad; adlen; nonce; key] s /\
               read (memory :> bytes(key,32)) s = num_of_bytelist kb /\
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
                 (if wg_aead_decrypt kb (val nonce) ct al = NONE
                  then word 0 else word 1) /\
               (!p. wg_aead_decrypt kb (val nonce) ct al = SOME p
                    ==> read (memory :> bytes(dst,LENGTH p)) s =
                        num_of_bytelist p))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,val len - 16);
                      memory :> bytes(word_sub stackpointer (word 800),800)])`;;

let WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_CHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_checker_precompute_peer_keys(peer) of the kernel's              *)
(* drivers/net/wireguard/cookie.c in the image: the key for decrypting       *)
(* cookie replies (at 722) and the key of mac1 (at 754) of the latest cookie *)
(* of the peer (a struct wg_peer, whose struct cookie is at 680) become      *)
(* those of the remote static public key of its handshake (at 328):          *)
(* wg_cookie_key and wg_mac1_key of common/wireguard.ml, by precompute_key   *)
(* with the labels of cookie.c.                                              *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/rodata.ml";;
needs "arm/proofs/wireguard/gcc13_O2/precompute_key_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy.    *)
(* The code and its callees use 560 bytes of stack.                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_PEER_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!peer rspub mset ea1 el1 ev1 mcpy ea2 el2 ev2
   pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH rspub = 32 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 560),560); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (ea1,el1); (ea2,el2); (word_add peer (word 328),32);
       (word_add peer (word 722),64)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s =
                 word(pc + wg_cookie_checker_precompute_peer_keys) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [peer] s /\
               read (memory :> bytes(word_add peer (word 328),32)) s =
                 num_of_bytelist rspub /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(word_add peer (word 722),32)) s =
                 num_of_bytelist(wg_cookie_key rspub) /\
               read (memory :> bytes(word_add peer (word 754),32)) s =
                 num_of_bytelist(wg_mac1_key rspub))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add peer (word 722),64);
                      memory :> bytes(word_sub stackpointer (word 560),
                                      560)])`;;

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_PEER_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_PEER_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

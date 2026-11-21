(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_checker_precompute_device_keys(checker) of the kernel's         *)
(* drivers/net/wireguard/cookie.c in the image: if the device of the cookie  *)
(* checker (a struct cookie_checker at checker, with the device at 144) has  *)
(* a static identity, the key of cookie replies (at 32) and the key of mac1  *)
(* (at 64) become those of its static public key (wg_cookie_key and          *)
(* wg_mac1_key of common/wireguard.ml, by precompute_key with the labels of  *)
(* cookie.c); otherwise both become zero. The device has the static public   *)
(* key at 856 and has_identity at 960; the caller holds the lock of the      *)
(* static identity.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/rodata.ml";;
needs "arm/proofs/wireguard/gcc13_O2/precompute_key_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy.    *)
(* The code and its callees use 544 bytes of stack.                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!checker wg spub hid mset ea1 el1 ev1 mcpy ea2 el2 ev2
   pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH spub = 32 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 544),544); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (ea1,el1); (ea2,el2); (checker,152); (word_add wg (word 856),105)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s =
                 word(pc + wg_cookie_checker_precompute_device_keys) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [checker] s /\
               read (memory :> bytes64(word_add checker (word 144))) s = wg /\
               read (memory :> bytes8(word_add wg (word 960))) s =
                 (if hid then word 1 else word 0) /\
               read (memory :> bytes(word_add wg (word 856),32)) s =
                 num_of_bytelist spub /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(word_add checker (word 32),32)) s =
                 (if hid then num_of_bytelist(wg_cookie_key spub) else 0) /\
               read (memory :> bytes(word_add checker (word 64),32)) s =
                 (if hid then num_of_bytelist(wg_mac1_key spub) else 0))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add checker (word 32),64);
                      memory :> bytes(word_sub stackpointer (word 544),
                                      544)])`;;

let WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_COOKIE_CHECKER_PRECOMPUTE_DEVICE_KEYS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

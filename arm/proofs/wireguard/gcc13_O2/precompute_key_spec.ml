(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* precompute_key(key, pubkey, label) of the kernel's                        *)
(* drivers/net/wireguard/cookie.c in the image (a static function): the 32   *)
(* bytes at key become the hash (wg_hash of common/wireguard.ml, unkeyed     *)
(* BLAKE2s-256) of the 8-byte label at label followed by the 32-byte public  *)
(* key at pubkey, as for the keys of mac1 and of cookie replies (wg_mac1_key *)
(* and wg_cookie_key) with the labels of cookie.c. blake2s_init is inlined;  *)
(* the state on the stack is zeroed at entry (as a stack variable) and by    *)
(* blake2s_final.                                                            *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy.    *)
(* The code and its callees use 512 bytes of stack.                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!key pub label pb lb mset ea1 el1 ev1 mcpy ea2 el2 ev2
   pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH pb = 32 /\ LENGTH lb = 8 /\
     ALL (nonoverlapping (word_sub stackpointer (word 512),512))
         [(word pc,wireguard_size); (key,32); (pub,32); (label,8);
          (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (key,32))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + precompute_key) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [key; pub; label] s /\
               read (memory :> bytes(pub,32)) s = num_of_bytelist pb /\
               read (memory :> bytes(label,8)) s = num_of_bytelist lb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(key,32)) s =
                 num_of_bytelist(wg_hash(APPEND lb pb)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(key,32);
                      memory :> bytes(word_sub stackpointer (word 512),
                                      512)])`;;

let WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_PRECOMPUTE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

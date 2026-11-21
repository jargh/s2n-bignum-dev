(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The copy of blake2s(out, in, key, outlen, inlen, keylen) (the inline      *)
(* function of the kernel's include/crypto/blake2s.h) that gcc made for      *)
(* drivers/net/wireguard/noise.c, blake2s.constprop.0 (the label             *)
(* blake2s_constprop_0_1 here), for its only call, in wg_noise_init, with    *)
(* all the arguments constant: the 32 bytes of handshake_init_chaining_key   *)
(* in the data of the image become the unkeyed BLAKE2s-256 (wg_hash of       *)
(* common/wireguard.ml) of the 37 bytes of handshake_name in its .rodata,    *)
(* the string of the construction of Section 5.4 of the WireGuard paper,     *)
(* that is, wg_ck0. The state is on the stack, zeroed at entry (as a stack   *)
(* variable) and by blake2s_final.                                           *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy.    *)
(* The code and its callees use 480 bytes of stack.                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mset ea1 el1 ev1 mcpy ea2 el2 ev2 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 480),480))
         [(word pc,wireguard_size);
          (word(pc + wireguard_data),wireguard_data_size);
          (ea1,el1); (ea2,el2)] /\
     ALL (nonoverlapping
           (word(pc + data_handshake_init_chaining_key):int64,32))
         [(ea1,el1); (ea2,el2)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + blake2s_constprop_0_1) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :>
                     bytes(word(pc + data_handshake_init_chaining_key),32)) s =
                 num_of_bytelist wg_ck0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :>
                        bytes(word(pc + data_handshake_init_chaining_key),32);
                      memory :> bytes(word_sub stackpointer (word 480),
                                      480)])`;;

let WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_BLAKE2S_CONSTPROP_0_1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_init() of the kernel's drivers/net/wireguard/noise.c in the      *)
(* image, run once when the module is loaded: it computes the initial        *)
(* chaining key and hash of the handshake into handshake_init_chaining_key   *)
(* and handshake_init_hash in the data of the image, which are wg_ck0 and    *)
(* wg_h0 of common/wireguard.ml (the hash of the construction, and the hash  *)
(* of that and the identifier), as the theorems for the handshake messages   *)
(* assume. The first is by blake2s.constprop.0 (blake2s_constprop_0_1), the  *)
(* second by blake2s_init (inlined), blake2s_update and blake2s_final, with  *)
(* the state on the stack (zeroed at entry, as a stack variable, and by      *)
(* blake2s_final).                                                           *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_constprop_0_1_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy     *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 640 bytes of stack.                                           *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mset mcpy ea el ev pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 640),640); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_init) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :>
                     bytes(word(pc + data_handshake_init_chaining_key),32)) s =
                 num_of_bytelist wg_ck0 /\
               read (memory :>
                     bytes(word(pc + data_handshake_init_hash),32)) s =
                 num_of_bytelist wg_h0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :>
                        bytes(word(pc + data_handshake_init_chaining_key),32);
                      memory :> bytes(word(pc + data_handshake_init_hash),32);
                      memory :> bytes(word_sub stackpointer (word 640),
                                      640)])`;;

let WIREGUARD_NOISE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_NOISE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

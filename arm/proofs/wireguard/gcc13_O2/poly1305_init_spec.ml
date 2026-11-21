(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* poly1305_init(desc, key) of the kernel's lib/crypto/poly1305.c in the     *)
(* image: the struct poly1305_desc_ctx at desc becomes the state for the     *)
(* 32-byte key k with no input (poly1305_desc_at in ../structs.ml): s is the *)
(* last 16 bytes of the key, buflen and the accumulator are zero, and the    *)
(* key r is set by poly1305_core_setkey. Only the first 104 bytes of the     *)
(* struct are written.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_setkey_spec.ml";;

let WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!desc key k pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH k = 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,wireguard_size); (desc,104); (key,32)] /\
     ALL (nonoverlapping (desc,104)) [(word pc,wireguard_size); (key,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + poly1305_init) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [desc; key] s /\
               read (memory :> bytes(key,32)) s = num_of_bytelist k)
          (\s. read PC s = returnaddress /\ poly1305_desc_at desc k [] s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(desc,104);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

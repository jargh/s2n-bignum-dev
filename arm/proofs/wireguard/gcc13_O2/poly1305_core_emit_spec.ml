(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* poly1305_core_emit(state, nonce, dst) of the kernel's                     *)
(* lib/crypto/poly1305-donna64.c in the image, for a non-NULL nonce: the 16  *)
(* bytes at dst become the low 128 bits of the accumulator a of the state    *)
(* (poly1305_h_at in ../structs.ml, so a < 2^130 - 5) plus the 16 bytes sb  *)
(* at nonce. The limbs are fully carried, p = 2^130 - 5 is subtracted if     *)
(* they are at least p (selected with masks, without branches), and the     *)
(* nonce is added.                                                           *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;

let WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!state nonce dst a sb pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     LENGTH sb = 16 /\ ~(nonce = word 0) /\
     nonoverlapping (word pc,wireguard_size) (dst,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + poly1305_core_emit) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [state; nonce; dst] s /\
               poly1305_h_at state a s /\
               read (memory :> bytes(nonce,16)) s = num_of_bytelist sb)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(dst,16)) s =
                 (a + num_of_bytelist sb) MOD 2 EXP 128)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(dst,16)])`;;

let WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* poly1305_core_setkey(key, raw_key) of the kernel's                        *)
(* lib/crypto/poly1305-donna64.c in the image: the 16 bytes kb at raw_key,   *)
(* clamped as r (poly1305_r of common/rfc8439.ml), are stored in the struct  *)
(* poly1305_core_key at key as three limbs and 20 times the last two         *)
(* (poly1305_key_at in ../structs.ml).                                       *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;
needs "common/rfc8439.ml";;

let WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!key raw kb pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     LENGTH kb = 16 /\
     nonoverlapping (word pc,wireguard_size) (key,40)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + poly1305_core_setkey) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [key; raw] s /\
               read (memory :> bytes(raw,16)) s = num_of_bytelist kb)
          (\s. read PC s = returnaddress /\
               poly1305_key_at key (poly1305_r kb) s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(key,40)])`;;

let WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    WIREGUARD_POLY1305_CORE_SETKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

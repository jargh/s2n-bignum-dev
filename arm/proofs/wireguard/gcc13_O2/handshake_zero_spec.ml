(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* handshake_zero(handshake) of the kernel's drivers/net/wireguard/noise.c   *)
(* in the image (a static function): for the struct noise_handshake at hs    *)
(* (see noise_handshake_create_initiation_spec.ml), the state (at 32)        *)
(* becomes HANDSHAKE_ZEROED (0), and the ephemeral private key (at 56), the  *)
(* remote ephemeral key (at 120), the hash and the chaining key (64 bytes at *)
(* 216) and the remote index (at 292) zero. Its memsets are inlined, and it  *)
(* uses no stack.                                                            *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!hs pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     nonoverlapping (hs,336) (word pc,wireguard_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + handshake_zero) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [hs] s)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes32(word_add hs (word 32))) s = word 0 /\
               read (memory :> bytes(word_add hs (word 56),32)) s = 0 /\
               read (memory :> bytes(word_add hs (word 120),32)) s = 0 /\
               read (memory :> bytes(word_add hs (word 216),64)) s = 0 /\
               read (memory :> bytes32(word_add hs (word 292))) s = word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_add hs (word 32),4);
                      memory :> bytes(word_add hs (word 56),32);
                      memory :> bytes(word_add hs (word 120),32);
                      memory :> bytes(word_add hs (word 216),64);
                      memory :> bytes(word_add hs (word 292),4)])`;;

let WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_HANDSHAKE_ZERO_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

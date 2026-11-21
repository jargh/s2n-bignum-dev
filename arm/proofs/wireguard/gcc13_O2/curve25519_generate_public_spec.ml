(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* curve25519_generate_public(pub, secret) of the kernel's                   *)
(* lib/crypto/curve25519.c in the image: if the 32-byte secret is zero       *)
(* (compared by __crypto_memneq with the zero point in .rodata) the result   *)
(* is false and nothing is written; otherwise the 32 bytes at pub become the *)
(* public key of the secret (X25519 with the base point 9, by                *)
(* curve25519_generic through the PLT), and the result is whether that is    *)
(* not zero.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contract for curve25519_generic.    *)
(* The code and curve25519_generic use 1264 bytes of stack.                  *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!pub secret sb cfn ea3 el3 ev3 pc stackpointer returnaddress.
     curve25519_generic_contract cfn ea3 el3 ev3 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH sb = 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 1264),1264))
         [(word pc,wireguard_size); (pub,32); (secret,32); (ea3,el3);
          (word(pc + got_curve25519_generic),8)] /\
     ALL (nonoverlapping (pub,32))
         [(word pc,wireguard_size); (secret,32); (ea3,el3);
          (word(pc + got_curve25519_generic),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + curve25519_generate_public) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [pub; secret] s /\
               read (memory :> bytes(secret,32)) s = num_of_bytelist sb /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes(ea3,el3)) s = ev3)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
                 (if sb = wg_zero32 \/ wg_dh_pubkey sb = wg_zero32
                  then word 0 else word 1) /\
               (~(sb = wg_zero32)
                ==> read (memory :> bytes(pub,32)) s =
                    num_of_bytelist(wg_dh_pubkey sb)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(pub,32);
                      memory :> bytes(word_sub stackpointer (word 1264),
                                      1264)])`;;

let WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_CURVE25519_GENERATE_PUBLIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_set_static_identity_private_key(static_identity, private_key) of *)
(* the kernel's drivers/net/wireguard/noise.c in the image: for the struct   *)
(* noise_static_identity at si (see                                          *)
(* noise_handshake_create_initiation_spec.ml, with the private key at 32),   *)
(* the private key becomes the 32 bytes at pk clamped (wg_clamp of           *)
(* common/wireguard.ml), the public key that of the bytes (if they are not   *)
(* zero) by curve25519_generate_public, and has_identity whether that        *)
(* worked (the bytes and the public key are not zero). The copy and the      *)
(* clamping are inlined.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/curve25519_generate_public_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contract for curve25519_generic.    *)
(* The code and its callees use 1296 bytes of stack.                         *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!si pk sk cfn ea el ev pc stackpointer returnaddress.
     curve25519_generic_contract cfn ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH sk = 32 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 1296),1296); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el); (si,112);
       (pk,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s =
                 word(pc + wg_noise_set_static_identity_private_key) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [si; pk] s /\
               read (memory :> bytes(pk,32)) s = num_of_bytelist sk /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(word_add si (word 32),32)) s =
                 num_of_bytelist(wg_clamp sk) /\
               read (memory :> bytes8(word_add si (word 104))) s =
                 (if sk = wg_zero32 \/ wg_dh_pubkey sk = wg_zero32
                  then word 0 else word 1) /\
               (~(sk = wg_zero32)
                ==> read (memory :> bytes(si,32)) s =
                    num_of_bytelist(wg_dh_pubkey sk)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(si,64);
                      memory :> bytes(word_add si (word 104),1);
                      memory :> bytes(word_sub stackpointer (word 1296),
                                      1296)])`;;

let WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_SET_STATIC_IDENTITY_PRIVATE_KEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

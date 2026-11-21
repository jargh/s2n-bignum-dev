(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_precompute_static_static(peer) of the kernel's                   *)
(* drivers/net/wireguard/noise.c in the image: with the lock of the peer's   *)
(* handshake held for writing, its precomputed static-static secret becomes  *)
(* X25519 (wg_dh) of the private key of its static identity and its remote   *)
(* static key if the identity has a key, and zero otherwise (and also if the *)
(* result of X25519 is zero, when it is that result). The handshake is the   *)
(* struct noise_handshake at 240 in the struct wg_peer (see                  *)
(* noise_handshake_create_initiation_spec.ml): its pointer to the static     *)
(* identity at 48, the remote static key at 88, the precomputed secret at    *)
(* 152 and the lock at 296; the static identity has its private key at 32   *)
(* and has_identity at 104.                                                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/curve25519_fn_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4144 bytes of stack.                                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!peer si hid spriv rpub cfn dwr uwr ea el ev pc stackpointer returnaddress.
     curve25519_generic_contract cfn ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH spriv = 32 /\ LENGTH rpub = 32 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4144),4144); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (word_add peer (word 240),336); (si,112)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_precompute_static_static) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [peer] s /\
               read (memory :> bytes64(word_add peer (word 288))) s = si /\
               read (memory :> bytes8(word_add si (word 104))) s =
                 (if hid then word 1 else word 0) /\
               read (memory :> bytes(word_add si (word 32),32)) s =
                 num_of_bytelist spriv /\
               read (memory :> bytes(word_add peer (word 328),32)) s =
                 num_of_bytelist rpub /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(word_add peer (word 392),32)) s =
                 num_of_bytelist(if hid then wg_dh spriv rpub else wg_zero32))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add peer (word 392),32);
                      memory :> bytes(word_add peer (word 536),40);
                      memory :> bytes(word_sub stackpointer (word 4144),
                                      4144)])`;;

let WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

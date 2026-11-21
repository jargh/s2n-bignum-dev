(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_handshake_init(handshake, static_identity, peer_public_key,      *)
(* peer_preshared_key, peer) of the kernel's drivers/net/wireguard/noise.c   *)
(* in the image, for the handshake of the peer (at 240 in the struct         *)
(* wg_peer, as in its only call, in peer.c; the code relies on that through  *)
(* wg_noise_precompute_static_static): the struct noise_handshake at hs (see *)
(* noise_handshake_create_initiation_spec.ml) is zeroed (by memset), its     *)
(* lock initialized (by __init_rwsem), and its entry gets the type           *)
(* INDEX_HASHTABLE_HANDSHAKE (1, at 24) and the peer (at 0); its remote      *)
(* static key (at 88) is the public key, its preshared key (at 184) the      *)
(* preshared key if that is not NULL, its pointer to the static identity (at *)
(* 48) the static identity, and its precomputed secret (at 152) that of      *)
(* wg_noise_precompute_static_static. The other fields are zero: the hash    *)
(* list node of the entry (at 8, so not in a list), the index (at 28), the   *)
(* state (at 32, HANDSHAKE_ZEROED), the time of the last initiation (at 40), *)
(* the ephemeral keys (at 56 and 120), and the hash, chaining key, latest    *)
(* timestamp and remote index (80 bytes at 216).                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_precompute_static_static_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4208 bytes of stack. The preshared key is the 32 bytes pskb   *)
(* at psk unless psk is NULL.                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!hs si pub psk peer hid spriv rpub pskb mset irw cfn dwr uwr ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ init_rwsem_contract irw ea el ev /\
     curve25519_generic_contract cfn ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH spriv = 32 /\ LENGTH rpub = 32 /\ LENGTH pskb = 32 /\
     hs = word_add peer (word 240) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4208),4208); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el); (hs,336);
       (si,112); (pub,32); (psk,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_handshake_init) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [hs; si; pub; psk; peer] s /\
               read (memory :> bytes8(word_add si (word 104))) s =
                 (if hid then word 1 else word 0) /\
               read (memory :> bytes(word_add si (word 32),32)) s =
                 num_of_bytelist spriv /\
               read (memory :> bytes(pub,32)) s = num_of_bytelist rpub /\
               (~(psk = word 0)
                ==> read (memory :> bytes(psk,32)) s = num_of_bytelist pskb) /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_init_rwsem))) s = irw /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes64 hs) s = peer /\
               read (memory :> bytes(word_add hs (word 8),16)) s = 0 /\
               read (memory :> bytes32(word_add hs (word 24))) s = word 1 /\
               read (memory :> bytes32(word_add hs (word 28))) s = word 0 /\
               read (memory :> bytes32(word_add hs (word 32))) s = word 0 /\
               read (memory :> bytes64(word_add hs (word 40))) s = word 0 /\
               read (memory :> bytes64(word_add hs (word 48))) s = si /\
               read (memory :> bytes(word_add hs (word 56),32)) s = 0 /\
               read (memory :> bytes(word_add hs (word 88),32)) s =
                 num_of_bytelist rpub /\
               read (memory :> bytes(word_add hs (word 120),32)) s = 0 /\
               read (memory :> bytes(word_add hs (word 152),32)) s =
                 num_of_bytelist(if hid then wg_dh spriv rpub else wg_zero32) /\
               read (memory :> bytes(word_add hs (word 184),32)) s =
                 (if psk = word 0 then 0 else num_of_bytelist pskb) /\
               read (memory :> bytes(word_add hs (word 216),80)) s = 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(hs,336);
                      memory :> bytes(word_sub stackpointer (word 4208),
                                      4208)])`;;

let WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

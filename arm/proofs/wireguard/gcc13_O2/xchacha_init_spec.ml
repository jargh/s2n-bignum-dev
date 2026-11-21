(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* xchacha_init(chacha_state, key, nonce) of the kernel's                    *)
(* lib/crypto/chacha20poly1305.c in the image (a static function): the 16    *)
(* words at chacha_state become the ChaCha20 state (chacha20_state of        *)
(* common/rfc8439.ml) for the HChaCha20 subkey of the 32-byte key kb and the *)
(* first 16 bytes of the 24-byte nonce nb, the counter 0 and the 12-byte     *)
(* nonce of XChaCha20 (four zero bytes and the last 8 bytes of nb), as in    *)
(* xchacha20_poly1305_encrypt of common/rfc8439.ml. The state is first built *)
(* for the key and the first 16 bytes of the nonce and hchacha_block gives   *)
(* the subkey into a buffer on the stack, which is zeroed at the end, as is  *)
(* the buffer of the 16-byte nonce.                                          *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/hchacha_block_spec.ml";;

let WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st key nonce kb nb mset ea1 el1 ev1 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH kb = 32 /\ LENGTH nb = 24 /\
     ALL (nonoverlapping (word_sub stackpointer (word 224),224))
         [(word pc,wireguard_size); (st,64); (key,32); (nonce,24);
          (ea1,el1); (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (st,64))
         [(word pc,wireguard_size); (key,32); (nonce,24); (ea1,el1);
          (word(pc + got_memset),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + xchacha_init) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [st; key; nonce] s /\
               read (memory :> bytes(key,32)) s = num_of_bytelist kb /\
               read (memory :> bytes(nonce,24)) s = num_of_bytelist nb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes(ea1,el1)) s = ev1)
          (\s. read PC s = returnaddress /\
               !i. i < 16
                   ==> read (memory :> bytes32(word_add st (word(4 * i)))) s =
                       chacha20_state (hchacha20 kb (SUB_LIST(0,16) nb)) 0
                                      (xchacha20_nonce nb) i)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(st,64);
                      memory :> bytes(word_sub stackpointer (word 224),
                                      224)])`;;

let WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

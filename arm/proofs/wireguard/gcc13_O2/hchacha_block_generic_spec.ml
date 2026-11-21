(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* hchacha_block_generic(state, out, nrounds) of the kernel's                *)
(* lib/crypto/chacha-block-generic.c in the image, for nrounds = 20: the 32  *)
(* bytes at out become words 0..3 and 12..15 of the 20 rounds of the 16-word *)
(* state xs at state, without the feed-forward of the block function         *)
(* (HChaCha20, as in hchacha20 of common/rfc8439.ml, little-endian). The     *)
(* copy of the state on the stack that is permuted is zeroed with memset.    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha_permute_spec.ml";;

let WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st out (xs:num->int32) mset ea1 el1 ev1 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 96),96))
         [(word pc,wireguard_size); (st,64); (out,32); (ea1,el1);
          (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (out,32))
         [(word pc,wireguard_size); (ea1,el1); (word(pc + got_memset),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + hchacha_block_generic) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [st; out; word 20] s /\
               (!i. i < 16
                    ==> read (memory :> bytes32(word_add st (word(4 * i)))) s =
                        xs i) /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes(ea1,el1)) s = ev1)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(out,32)) s =
               num_of_bytelist
                (APPEND (chacha20_words 4 (chacha20_rounds 10 xs))
                        (chacha20_words 4
                           (\i. chacha20_rounds 10 xs (i + 12)))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(out,32);
                      memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    WIREGUARD_HCHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

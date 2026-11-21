(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* chacha_block_generic(state, out, nrounds) of the kernel's lib/crypto/     *)
(* chacha-block-generic.c in the image, for nrounds = 20: the 64 bytes at    *)
(* out become the ChaCha20 block of the 16-word state xs at state (as in     *)
(* chacha20_block of common/rfc8439.ml: the 20 rounds of xs added to xs,     *)
(* little-endian), and the block counter (word 12) is incremented. The copy  *)
(* of the state on the stack that is permuted is zeroed with memset.         *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha_permute_spec.ml";;

let WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st out (xs:num->int32) mset ea1 el1 ev1 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     ALL (nonoverlapping (word_sub stackpointer (word 112),112))
         [(word pc,wireguard_size); (st,64); (out,64); (ea1,el1);
          (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (st,64))
         [(word pc,wireguard_size); (out,64); (ea1,el1);
          (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (out,64))
         [(word pc,wireguard_size); (ea1,el1); (word(pc + got_memset),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + chacha_block_generic) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [st; out; word 20] s /\
               (!i. i < 16
                    ==> read (memory :> bytes32(word_add st (word(4 * i)))) s =
                        xs i) /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes(ea1,el1)) s = ev1)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(out,64)) s =
               num_of_bytelist
                (chacha20_words 16
                  (\i. word_add (chacha20_rounds 10 xs i) (xs i))) /\
               (!i. i < 16
                    ==> read (memory :> bytes32(word_add st (word(4 * i)))) s =
                        if i = 12 then word_add (xs 12) (word 1) else xs i))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(out,64); memory :> bytes(st,64);
                      memory :> bytes(word_sub stackpointer (word 112),112)])`;;

let WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

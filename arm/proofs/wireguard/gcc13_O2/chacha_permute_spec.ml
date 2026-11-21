(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* chacha_permute(x, nrounds) of the kernel's lib/crypto/chacha-block-       *)
(* generic.c in the image, for nrounds = 20 (ChaCha20): the 16 words at x    *)
(* become the result of the 10 double rounds of RFC 8439 on them             *)
(* (chacha20_rounds 10 in common/rfc8439.ml). Other numbers of rounds than   *)
(* 12 and 20 would reach the WARN (brk) at chacha_permute_ret1. X0 keeps x,  *)
(* although the AAPCS does not require it: gcc's interprocedural register    *)
(* allocation (-fipa-ra) lets hchacha_block_generic rely on that.            *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;
needs "common/rfc8439.ml";;

let WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!x (xs:num->int32) pc returnaddress.
     nonoverlapping (word pc,wireguard_size) (x,64)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
           read PC s = word(pc + chacha_permute) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [x; word 20] s /\
           (!i. i < 16
                ==> read (memory :> bytes32(word_add x (word(4 * i)))) s =
                    xs i))
      (\s. read PC s = returnaddress /\ read X0 s = x /\
           (!i. i < 16
                ==> read (memory :> bytes32(word_add x (word(4 * i)))) s =
                    chacha20_rounds 10 xs i))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(x,64)])`;;

let WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_CHACHA_PERMUTE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

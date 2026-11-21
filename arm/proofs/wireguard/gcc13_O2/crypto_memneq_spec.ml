(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* __crypto_memneq(a, b, size) of the kernel's lib/crypto/memneq.c in the    *)
(* image: zero exactly when the size bytes at a and at b are equal. It ors   *)
(* together the xors of the 64-bit words and then of the remaining bytes (a  *)
(* size of 16 has its own unrolled code), so that its time does not depend   *)
(* on the data.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;

let WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a b size x y pc returnaddress.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
           read PC s = word(pc + __crypto_memneq) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a; b; size] s /\
           read (memory :> bytes(a,val size)) s = x /\
           read (memory :> bytes(b,val size)) s = y)
      (\s. read PC s = returnaddress /\
           (C_RETURN s = word 0 <=> x = y))
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

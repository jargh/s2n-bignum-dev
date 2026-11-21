(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* __crypto_xor(dst, src1, src2, size) of the kernel's lib/crypto/utils.c in *)
(* the image: the size bytes at dst become the xors of those at src1 and     *)
(* src2 (64 bits at a time, then 4, 2 and 1 bytes). The output may be the    *)
(* first input (in place), since each part is read before it is written.     *)
(* The size is an unsigned int, of which the code only uses the low 32 bits. *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;

let WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst a b len la lb pc returnaddress.
     LENGTH la = val len /\ LENGTH lb = val len /\ val(len:int64) < 2 EXP 32 /\
     (dst = a \/ nonoverlapping (dst,val len) (a,val len)) /\
     nonoverlapping (dst,val len) (b,val len) /\
     nonoverlapping (word pc,wireguard_size) (dst,val len)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + __crypto_xor) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; a; b; len] s /\
               read (memory :> bytes(a,val len)) s = num_of_bytelist la /\
               read (memory :> bytes(b,val len)) s = num_of_bytelist lb)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(dst,val len)) s =
               num_of_bytelist
                (list_of_seq (\i. word_xor (EL i la) (EL i lb)) (val len)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(dst,val len)])`;;

let WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

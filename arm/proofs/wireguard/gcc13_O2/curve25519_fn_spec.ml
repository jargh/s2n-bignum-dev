(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* curve25519(mypublic, secret, basepoint) of the kernel's                   *)
(* include/crypto/curve25519.h, of which gcc has made a function in the      *)
(* image (curve25519_fn in the layout): X25519 by curve25519_generic         *)
(* (through the PLT), and the result true exactly when the output is not the *)
(* zero point, compared by __crypto_memneq with the 32 zero bytes in         *)
(* .rodata.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contract for curve25519_generic.    *)
(* The code and its callees use 1248 bytes of stack.                         *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out scalar point sb pb cfn ea3 el3 ev3 pc stackpointer returnaddress.
     curve25519_generic_contract cfn ea3 el3 ev3 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH sb = 32 /\ LENGTH pb = 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 1248),1248))
         [(word pc,wireguard_size); (out,32); (scalar,32); (point,32);
          (ea3,el3); (word(pc + got_curve25519_generic),8)] /\
     ALL (nonoverlapping (out,32))
         [(word pc,wireguard_size); (scalar,32); (point,32); (ea3,el3);
          (word(pc + got_curve25519_generic),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + curve25519_fn) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [out; scalar; point] s /\
               read (memory :> bytes(scalar,32)) s = num_of_bytelist sb /\
               read (memory :> bytes(point,32)) s = num_of_bytelist pb /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes(ea3,el3)) s = ev3)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(out,32)) s =
                 num_of_bytelist(wg_dh sb pb) /\
               C_RETURN s = (if wg_dh sb pb = wg_zero32 then word 0
                             else word 1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(out,32);
                      memory :> bytes(word_sub stackpointer (word 1248),
                                      1248)])`;;

let WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_CURVE25519_FN_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

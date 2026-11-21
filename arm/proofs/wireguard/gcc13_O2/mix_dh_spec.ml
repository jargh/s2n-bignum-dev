(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* mix_dh(chaining_key, key, private, public) of the kernel's                *)
(* drivers/net/wireguard/noise.c in the image: the DH of private and public  *)
(* (wg_dh) by curve25519 (curve25519_fn) into a buffer on the stack; if it   *)
(* is the zero point, the result is false and nothing else is done, and      *)
(* otherwise the result is true and the chaining key and key become the two  *)
(* outputs of the KDF of the DH result with the chaining key (wg_kdf2), the  *)
(* buffer being zeroed.                                                      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/curve25519_fn_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/kdf_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset, memcpy and    *)
(* curve25519_generic. The code and its callees use 1328 bytes of stack.     *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ck key priv pub ckb privb pubb mset ea1 el1 ev1 mcpy ea2 el2 ev2
   cfn ea3 el3 ev3 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     curve25519_generic_contract cfn ea3 el3 ev3 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     ~(ck = word 0) /\ ~(key = word 0) /\
     LENGTH ckb = 32 /\ LENGTH privb = 32 /\ LENGTH pubb = 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 1328),1328))
         [(word pc,wireguard_size); (ck,32); (key,32); (priv,32); (pub,32);
          (ea1,el1); (ea2,el2); (ea3,el3); (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (word(pc + got_curve25519_generic),8)] /\
     ALL (nonoverlapping (ck,32))
         [(word pc,wireguard_size); (key,32); (ea1,el1); (ea2,el2);
          (ea3,el3); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (word(pc + got_curve25519_generic),8)] /\
     ALL (nonoverlapping (key,32))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2); (ea3,el3);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (word(pc + got_curve25519_generic),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + mix_dh) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [ck; key; priv; pub] s /\
               read (memory :> bytes(ck,32)) s = num_of_bytelist ckb /\
               read (memory :> bytes(priv,32)) s = num_of_bytelist privb /\
               read (memory :> bytes(pub,32)) s = num_of_bytelist pubb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2 /\
               read (memory :> bytes(ea3,el3)) s = ev3)
          (\s. read PC s = returnaddress /\
               C_RETURN s = (if wg_dh privb pubb = wg_zero32 then word 0
                             else word 1) /\
               (~(wg_dh privb pubb = wg_zero32)
                ==> read (memory :> bytes(ck,32)) s =
                    num_of_bytelist(FST(wg_kdf2 ckb (wg_dh privb pubb))) /\
                    read (memory :> bytes(key,32)) s =
                    num_of_bytelist(SND(wg_kdf2 ckb (wg_dh privb pubb)))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(ck,32); memory :> bytes(key,32);
                      memory :> bytes(word_sub stackpointer (word 1328),
                                      1328)])`;;

let WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_MIX_DH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same with a NULL key (as create_response and consume_response call    *)
(* it): only the chaining key is changed, to the first output of KDF.        *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ck priv pub ckb privb pubb mset ea1 el1 ev1 mcpy ea2 el2 ev2
   cfn ea3 el3 ev3 pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     curve25519_generic_contract cfn ea3 el3 ev3 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ ~(ck = word 0) /\
     LENGTH ckb = 32 /\ LENGTH privb = 32 /\ LENGTH pubb = 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 1328),1328))
         [(word pc,wireguard_size); (ck,32); (priv,32); (pub,32);
          (ea1,el1); (ea2,el2); (ea3,el3); (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (word(pc + got_curve25519_generic),8)] /\
     ALL (nonoverlapping (ck,32))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (ea3,el3); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (word(pc + got_curve25519_generic),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + mix_dh) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [ck; word 0; priv; pub] s /\
               read (memory :> bytes(ck,32)) s = num_of_bytelist ckb /\
               read (memory :> bytes(priv,32)) s = num_of_bytelist privb /\
               read (memory :> bytes(pub,32)) s = num_of_bytelist pubb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2 /\
               read (memory :> bytes(ea3,el3)) s = ev3)
          (\s. read PC s = returnaddress /\
               C_RETURN s = (if wg_dh privb pubb = wg_zero32 then word 0
                             else word 1) /\
               (~(wg_dh privb pubb = wg_zero32)
                ==> read (memory :> bytes(ck,32)) s =
                    num_of_bytelist(wg_kdf1 ckb (wg_dh privb pubb))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(ck,32);
                      memory :> bytes(word_sub stackpointer (word 1328),
                                      1328)])`;;

let WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_MIX_DH_NOKEY_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

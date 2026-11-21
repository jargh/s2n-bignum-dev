(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* hmac(out, in, key, inlen, keylen) of the kernel's drivers/net/wireguard/  *)
(* noise.c in the image: the 32 bytes at out become HMAC-BLAKE2s (wg_hmac in *)
(* common/wireguard.ml) with the key of 32 bytes at key of the inlen bytes   *)
(* at in. All the calls in noise.c have keylen = 32, so gcc has specialized  *)
(* the function to that (and dropped the argument): the key is copied to the *)
(* padded key block without the case of a key longer than a block. The two   *)
(* hashes are computed with blake2s_update and blake2s_final, on a state on   *)
(* the stack initialized with memset and stores, and the stack copies of the  *)
(* key and the inner hash are zeroed (memzero_explicit) at the end, the first *)
(* with memset. The output may be the input, as in kdf, since it is only      *)
(* written at the end.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "common/wireguard.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy as  *)
(* for blake2s_final. The code and its callees use 640 bytes of stack.       *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out inp key inlen kb m mset ea1 el1 ev1 mcpy ea2 el2 ev2 pc stackpointer
   returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH kb = 32 /\ LENGTH m = val(inlen:int64) /\
     64 + val inlen < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub stackpointer (word 640),640))
         [(word pc,wireguard_size); (out,32); (inp,val inlen); (key,32);
          (ea1,el1); (ea2,el2); (word(pc + got_memset),8);
          (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (out,32))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + hmac) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [out; inp; key; inlen] s /\
               read (memory :> bytes(key,32)) s = num_of_bytelist kb /\
               read (memory :> bytes(inp,val inlen)) s = num_of_bytelist m /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(out,32)) s = num_of_bytelist(wg_hmac kb m))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(out,32);
                      memory :> bytes(word_sub stackpointer (word 640),640)])`;;

let WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

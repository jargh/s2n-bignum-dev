(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* mix_hash(hash, src, src_len) of the kernel's drivers/net/wireguard/       *)
(* noise.c in the image: the 32 bytes at hash become the BLAKE2s hash of     *)
(* them followed by the src_len bytes at src (wg_mix_hash in                 *)
(* common/wireguard.ml). It initializes a blake2s_state on the stack (with   *)
(* memset and stores) and calls blake2s_update twice and blake2s_final.      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "common/wireguard.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy as  *)
(* for blake2s_final. The code and its callees use 512 bytes of stack.       *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!hash src srclen hb sb mset ea1 el1 ev1 mcpy ea2 el2 ev2 pc stackpointer
   returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH hb = 32 /\ LENGTH sb = val(srclen:int64) /\
     32 + val srclen < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub stackpointer (word 512),512))
         [(word pc,wireguard_size); (hash,32); (src,val srclen); (ea1,el1);
          (ea2,el2); (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (hash,32))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + mix_hash) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [hash; src; srclen] s /\
               read (memory :> bytes(hash,32)) s = num_of_bytelist hb /\
               read (memory :> bytes(src,val srclen)) s = num_of_bytelist sb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(hash,32)) s =
                 num_of_bytelist(wg_mix_hash hb sb))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(hash,32);
                      memory :> bytes(word_sub stackpointer (word 512),512)])`;;

let WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_MIX_HASH_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

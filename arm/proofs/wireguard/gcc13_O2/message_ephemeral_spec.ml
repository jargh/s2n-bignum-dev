(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* message_ephemeral(ephemeral_dst, ephemeral_src, chaining_key, hash) of    *)
(* the kernel's drivers/net/wireguard/noise.c in the image: the ephemeral    *)
(* public key at src is copied to dst (unless they are the same) and mixed   *)
(* into the chaining key and the hash (wg_ephemeral in common/wireguard.ml)  *)
(* by kdf (with one output) and mix_hash.                                    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_hash_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/kdf_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy.    *)
(* The code and its callees use 832 bytes of stack.                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst src ck hash eb ckb hb mset ea1 el1 ev1 mcpy ea2 el2 ev2
   pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ ~(ck = word 0) /\
     LENGTH eb = 32 /\ LENGTH ckb = 32 /\ LENGTH hb = 32 /\
     (dst = src \/ nonoverlapping (dst,32) (src,32)) /\
     ALL (nonoverlapping (word_sub stackpointer (word 832),832))
         [(word pc,wireguard_size); (dst,32); (src,32); (ck,32); (hash,32);
          (ea1,el1); (ea2,el2); (word(pc + got_memset),8);
          (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (dst,32))
         [(word pc,wireguard_size); (ck,32); (hash,32); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (src,32)) [(ck,32); (hash,32)] /\
     ALL (nonoverlapping (ck,32))
         [(word pc,wireguard_size); (hash,32); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (hash,32))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + message_ephemeral) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [dst; src; ck; hash] s /\
               read (memory :> bytes(src,32)) s = num_of_bytelist eb /\
               read (memory :> bytes(ck,32)) s = num_of_bytelist ckb /\
               read (memory :> bytes(hash,32)) s = num_of_bytelist hb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(dst,32)) s = num_of_bytelist eb /\
               read (memory :> bytes(ck,32)) s =
                 num_of_bytelist(FST(wg_ephemeral (ckb,hb) eb)) /\
               read (memory :> bytes(hash,32)) s =
                 num_of_bytelist(SND(wg_ephemeral (ckb,hb) eb)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,32); memory :> bytes(ck,32);
                      memory :> bytes(hash,32);
                      memory :> bytes(word_sub stackpointer (word 832),832)])`;;

let WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    WIREGUARD_MESSAGE_EPHEMERAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

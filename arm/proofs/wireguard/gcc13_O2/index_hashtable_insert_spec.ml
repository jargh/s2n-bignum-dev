(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_index_hashtable_insert(table, entry) of the kernel's                   *)
(* drivers/net/wireguard/peerlookup.c in the image: the entry (a struct      *)
(* index_hashtable_entry, at the start of a handshake or a keypair) is taken *)
(* out of any bucket of the table it is in, gets a random index that no      *)
(* other entry of the table has, which it returns, and is put at the head of *)
(* the bucket for that index.                                                *)
(*                                                                           *)
(* This theorem is ASSUMED, not proved: the code needs instructions that the *)
(* model does not have (mrs of SP_EL0, to raise the preempt count of the     *)
(* current task as rcu_read_lock_bh does, and the stlr of                    *)
(* rcu_assign_pointer), it calls kernel functions for the lock of the table, *)
(* random numbers and softirqs, and its search for an unused index ends only *)
(* with probability 1 (get_random_u32 could keep returning indices in use).  *)
(* It states only what its callers rely on: the result is the index stored   *)
(* in the entry, and only the hash node and index of the entry, the table    *)
(* (its buckets and lock) and 4144 bytes of stack change. It also changes    *)
(* the links of the entries next to the entry in the buckets, which are      *)
(* left outside the model, as the kernel's own state is for the kernel       *)
(* functions of ../contracts.ml.                                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;

let WIREGUARD_INDEX_HASHTABLE_INSERT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!table entry pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4144),4144); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (table,65544);
       (entry,32)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_index_hashtable_insert) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [table; entry] s)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
                 word_zx(read (memory :> bytes32(word_add entry (word 28))) s))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add entry (word 8),16);
                      memory :> bytes(word_add entry (word 28),4);
                      memory :> bytes(table,65544);
                      memory :> bytes(word_sub stackpointer (word 4144),
                                      4144)])`;;

let WIREGUARD_INDEX_HASHTABLE_INSERT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_INDEX_HASHTABLE_INSERT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

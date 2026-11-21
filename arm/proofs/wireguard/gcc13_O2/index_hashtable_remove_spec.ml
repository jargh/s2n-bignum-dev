(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_index_hashtable_remove(table, entry) of the kernel's                   *)
(* drivers/net/wireguard/peerlookup.c in the image: with the lock of the     *)
(* table of indices at table (a spinlock_t at 65536) held, the hash list     *)
(* node of the struct index_hashtable_entry at ent (at 8: the pointers next  *)
(* and pprev) is unlinked by hlist_del_init_rcu, if it is in a list (pprev   *)
(* is not NULL): *pprev becomes next, the pprev field of the next node (if   *)
(* any) becomes pprev, and pprev becomes NULL.                               *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4128 bytes of stack.                                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!table ent nx pp lk ulk ea el ev pc stackpointer returnaddress.
     spinlock_bh_contract lk ea el ev /\ spinlock_bh_contract ulk ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4128),4128); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (word_add table (word 65536),4); (word_add ent (word 8),16);
       (pp,8); (word_add nx (word 8),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_index_hashtable_remove) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [table; ent] s /\
               read (memory :> bytes64(word_add ent (word 8))) s = nx /\
               read (memory :> bytes64(word_add ent (word 16))) s = pp /\
               read (memory :> bytes64(word(pc + got_raw_spin_lock_bh))) s =
                 lk /\
               read (memory :> bytes64(word(pc + got_raw_spin_unlock_bh))) s =
                 ulk /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes64(word_add ent (word 16))) s = word 0 /\
               (~(pp = word 0)
                ==> read (memory :> bytes64 pp) s = nx /\
                    (~(nx = word 0)
                     ==> read (memory :> bytes64(word_add nx (word 8))) s =
                         pp)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add ent (word 16),8);
                      memory :> bytes(pp,8);
                      memory :> bytes(word_add nx (word 8),8);
                      memory :> bytes(word_add table (word 65536),4);
                      memory :> bytes(word_sub stackpointer (word 4128),
                                      4128)])`;;

let WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_INDEX_HASHTABLE_REMOVE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

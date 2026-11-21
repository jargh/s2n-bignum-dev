(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_index_hashtable_replace(table, old, new) of the kernel's               *)
(* drivers/net/wireguard/peerlookup.c in the image: with the lock of the     *)
(* table of indices at table (a spinlock_t at 65536) held, if the hash list  *)
(* node of the struct index_hashtable_entry at old (at 8: the pointers next  *)
(* and pprev) is in a list (pprev is not NULL), the entry at new takes its   *)
(* place there (hlist_replace_rcu, with the store of *pprev a release) and   *)
(* its index (at 28), and the node of old becomes unlinked (both pointers    *)
(* NULL, by INIT_HLIST_NODE after the poisoning of hlist_replace_rcu). The   *)
(* result is whether old was in a list.                                      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4144 bytes of stack. nx and pp are the pointers of the hash   *)
(* list node of old, and idx its index.                                      *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_INDEX_HASHTABLE_REPLACE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!table old new nx pp idx lk ulk ea el ev pc stackpointer returnaddress.
     spinlock_bh_contract lk ea el ev /\ spinlock_bh_contract ulk ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4144),4144); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (word_add table (word 65536),4); (word_add old (word 8),24);
       (word_add new (word 8),24); (pp,8); (word_add nx (word 8),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_index_hashtable_replace) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [table; old; new] s /\
               read (memory :> bytes64(word_add old (word 8))) s = nx /\
               read (memory :> bytes64(word_add old (word 16))) s = pp /\
               read (memory :> bytes32(word_add old (word 28))) s = idx /\
               read (memory :> bytes64(word(pc + got_raw_spin_lock_bh))) s =
                 lk /\
               read (memory :> bytes64(word(pc + got_raw_spin_unlock_bh))) s =
                 ulk /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               C_RETURN s = (if pp = word 0 then word 0 else word 1) /\
               (~(pp = word 0)
                ==> read (memory :> bytes32(word_add new (word 28))) s = idx /\
                    read (memory :> bytes64(word_add new (word 8))) s = nx /\
                    read (memory :> bytes64(word_add new (word 16))) s = pp /\
                    read (memory :> bytes64 pp) s = word_add new (word 8) /\
                    (~(nx = word 0)
                     ==> read (memory :> bytes64(word_add nx (word 8))) s =
                         word_add new (word 8)) /\
                    read (memory :> bytes64(word_add old (word 8))) s =
                      word 0 /\
                    read (memory :> bytes64(word_add old (word 16))) s =
                      word 0))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add old (word 8),16);
                      memory :> bytes(word_add new (word 8),16);
                      memory :> bytes(word_add new (word 28),4);
                      memory :> bytes(pp,8);
                      memory :> bytes(word_add nx (word 8),8);
                      memory :> bytes(word_add table (word 65536),4);
                      memory :> bytes(word_sub stackpointer (word 4144),
                                      4144)])`;;

let WIREGUARD_INDEX_HASHTABLE_REPLACE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_INDEX_HASHTABLE_REPLACE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

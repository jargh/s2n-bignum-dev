(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_keypair_put(keypair, unreference_now) of the kernel's            *)
(* drivers/net/wireguard/noise.c in the image: for the struct noise_keypair  *)
(* at kp (see noise_keypair_get_spec.ml), unless kp is NULL, its entry (at   *)
(* 0, as for the handshake's) is first removed from the table of indices of  *)
(* the device of the entry's peer if unreference_now (bit 0 of un) is set,   *)
(* and then its reference count is decremented (kref_put, by the LL/SC loop  *)
(* of the image as built). When that was the last reference (the count was   *)
(* 1), the entry is removed (again, which does nothing if it already was)    *)
(* and the keypair given to call_rcu (its rcu_head at 1192) to be freed      *)
(* later; when the count was not positive, refcount_warn_saturate is called. *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts_session.ml";;
needs "arm/proofs/wireguard/gcc13_O2/index_hashtable_remove_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4160 bytes of stack. peer, dev and table lead to the table of *)
(* indices, nx and pp are the pointers of the hash list node of the entry,   *)
(* and rc is the count.                                                      *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_KEYPAIR_PUT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!kp un peer dev table nx pp rc ws crcu lk ulk ea el ev
   pc stackpointer returnaddress.
     refcount_warn_saturate_contract ws ea el ev /\
     call_rcu_contract crcu ea el ev /\
     spinlock_bh_contract lk ea el ev /\ spinlock_bh_contract ulk ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4160),4160); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (kp,1216); (peer,8); (word_add dev (word 1152),8);
       (word_add table (word 65536),4); (pp,8); (word_add nx (word 8),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_keypair_put) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [kp; un] s /\
               (~(kp = word 0)
                ==> read (memory :> bytes64 kp) s = peer /\
                    read (memory :> bytes64 peer) s = dev /\
                    read (memory :> bytes64(word_add dev (word 1152))) s =
                      table /\
                    read (memory :> bytes64(word_add kp (word 8))) s = nx /\
                    read (memory :> bytes64(word_add kp (word 16))) s = pp /\
                    read (memory :> bytes32(word_add kp (word 1184))) s =
                      rc) /\
               read (memory :> bytes64(word(pc + got_refcount_warn_saturate)))
                 s = ws /\
               read (memory :> bytes64(word(pc + got_call_rcu))) s = crcu /\
               read (memory :> bytes64(word(pc + got_raw_spin_lock_bh))) s =
                 lk /\
               read (memory :> bytes64(word(pc + got_raw_spin_unlock_bh))) s =
                 ulk /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               (~(kp = word 0) /\ (bit 0 (un:int64) \/ rc = word 1)
                ==> read (memory :> bytes64(word_add kp (word 16))) s =
                      word 0 /\
                    (~(pp = word 0)
                     ==> read (memory :> bytes64 pp) s = nx /\
                         (~(nx = word 0)
                          ==> read (memory :> bytes64(word_add nx (word 8)))
                                s = pp))) /\
               (~(kp = word 0) /\ &0 < ival(rc:int32)
                ==> read (memory :> bytes32(word_add kp (word 1184))) s =
                    word_sub rc (word 1)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add kp (word 16),8);
                      memory :> bytes(word_add kp (word 1184),24);
                      memory :> bytes(pp,8);
                      memory :> bytes(word_add nx (word 8),8);
                      memory :> bytes(word_add table (word 65536),4);
                      memory :> bytes(word_sub stackpointer (word 4160),
                                      4160)])`;;

let WIREGUARD_NOISE_KEYPAIR_PUT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_KEYPAIR_PUT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

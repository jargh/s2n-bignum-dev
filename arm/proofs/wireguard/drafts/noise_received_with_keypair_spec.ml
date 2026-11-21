(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_received_with_keypair(keypairs, received_keypair) of the         *)
(* kernel's drivers/net/wireguard/noise.c in the image: for the struct       *)
(* noise_keypairs at ks (the current, previous and next keypairs at 0, 8 and *)
(* 16, and the lock keypair_update_lock, a spinlock_t, at 24), if the        *)
(* keypair at kp is the next one (checked again with the lock held), it      *)
(* becomes the current one, the current one becomes the previous one and the *)
(* next one NULL, with the stores of the pointers that readers follow being  *)
(* releases, and the old previous one is put (wg_noise_keypair_put with      *)
(* unreference_now set); the result is whether that happened.                *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts_session.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_keypair_put_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4224 bytes of stack. cur, prv and nxt are the keypairs of ks; *)
(* for the previous one, peer, dev and table lead to its table of indices,   *)
(* nx and pp are the pointers of the hash list node of its entry, and rc is  *)
(* its reference count.                                                      *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_RECEIVED_WITH_KEYPAIR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ks kp cur prv nxt peer dev table nx pp rc ws crcu lk ulk ea el ev
   pc stackpointer returnaddress.
     refcount_warn_saturate_contract ws ea el ev /\
     call_rcu_contract crcu ea el ev /\
     spinlock_bh_contract lk ea el ev /\ spinlock_bh_contract ulk ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4224),4224); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el); (ks,28);
       (prv,1216); (peer,8); (word_add dev (word 1152),8);
       (word_add table (word 65536),4); (pp,8); (word_add nx (word 8),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_received_with_keypair) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [ks; kp] s /\
               read (memory :> bytes64 ks) s = cur /\
               read (memory :> bytes64(word_add ks (word 8))) s = prv /\
               read (memory :> bytes64(word_add ks (word 16))) s = nxt /\
               (~(prv = word 0)
                ==> read (memory :> bytes64 prv) s = peer /\
                    read (memory :> bytes64 peer) s = dev /\
                    read (memory :> bytes64(word_add dev (word 1152))) s =
                      table /\
                    read (memory :> bytes64(word_add prv (word 8))) s = nx /\
                    read (memory :> bytes64(word_add prv (word 16))) s = pp /\
                    read (memory :> bytes32(word_add prv (word 1184))) s =
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
               C_RETURN s = (if kp = nxt then word 1 else word 0) /\
               (kp = nxt
                ==> read (memory :> bytes64 ks) s = kp /\
                    read (memory :> bytes64(word_add ks (word 8))) s = cur /\
                    read (memory :> bytes64(word_add ks (word 16))) s =
                      word 0 /\
                    (~(prv = word 0)
                     ==> read (memory :> bytes64(word_add prv (word 16))) s =
                           word 0 /\
                         (~(pp = word 0)
                          ==> read (memory :> bytes64 pp) s = nx /\
                              (~(nx = word 0)
                               ==> read (memory :>
                                         bytes64(word_add nx (word 8))) s =
                                   pp)) /\
                         (&0 < ival(rc:int32)
                          ==> read (memory :>
                                    bytes32(word_add prv (word 1184))) s =
                              word_sub rc (word 1)))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(ks,28);
                      memory :> bytes(word_add prv (word 16),8);
                      memory :> bytes(word_add prv (word 1184),24);
                      memory :> bytes(pp,8);
                      memory :> bytes(word_add nx (word 8),8);
                      memory :> bytes(word_add table (word 65536),4);
                      memory :> bytes(word_sub stackpointer (word 4224),
                                      4224)])`;;

let WIREGUARD_NOISE_RECEIVED_WITH_KEYPAIR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_RECEIVED_WITH_KEYPAIR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

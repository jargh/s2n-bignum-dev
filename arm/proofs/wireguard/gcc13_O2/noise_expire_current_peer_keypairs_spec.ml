(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_expire_current_peer_keypairs(peer) of the kernel's               *)
(* drivers/net/wireguard/noise.c in the image: for the struct wg_peer at     *)
(* peer, with the lock of its handshake (at 240, see                         *)
(* noise_handshake_create_initiation_spec.ml) held for writing, the entry of *)
(* the handshake is removed from the table of indices of the device of the   *)
(* entry's peer, the peer itself (as wg_noise_handshake_init makes it), by   *)
(* wg_index_hashtable_remove, and the handshake zeroed (handshake_zero); the *)
(* time of the last handshake sent (at 576) becomes the time less            *)
(* REKEY_TIMEOUT + 1 seconds (so that a new one is not held back); and with  *)
(* the lock of its keypairs (a spinlock_t at 160) held, the next and current *)
(* keypairs (pointers at 152 and 136), if not NULL, are made invalid for     *)
(* sending (is_valid of their struct noise_symmetric_key for sending, at 72, *)
(* becomes false).                                                           *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/index_hashtable_remove_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/handshake_zero_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4176 bytes of stack. nx and pp are the pointers of the hash   *)
(* list node of the handshake's entry, nk and ck the next and current        *)
(* keypairs.                                                                 *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!peer dev table nx pp nk ck dwr uwr ktc lk ulk ea el ev
   pc stackpointer returnaddress.
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     spinlock_bh_contract lk ea el ev /\ spinlock_bh_contract ulk ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4176),4176); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (peer,1648); (word_add dev (word 1152),8);
       (word_add table (word 65536),4); (pp,8); (word_add nx (word 8),8)] /\
     ALL (\k. ALL (nonoverlapping (word_add k (word 72),1))
                  [(word_sub stackpointer (word 4176),4176);
                   (word pc,wireguard_size);
                   (word(pc + wireguard_data),wireguard_data_size); (ea,el);
                   (peer,1648); (word_add table (word 65536),4); (pp,8);
                   (word_add nx (word 8),8)])
         [nk; ck]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_expire_current_peer_keypairs) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [peer] s /\
               read (memory :> bytes64(word_add peer (word 240))) s = peer /\
               read (memory :> bytes64 peer) s = dev /\
               read (memory :> bytes64(word_add dev (word 1152))) s = table /\
               read (memory :> bytes64(word_add peer (word 248))) s = nx /\
               read (memory :> bytes64(word_add peer (word 256))) s = pp /\
               read (memory :> bytes64(word_add peer (word 152))) s = nk /\
               read (memory :> bytes64(word_add peer (word 136))) s = ck /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :>
                     bytes64(word(pc + got_ktime_get_coarse_with_offset))) s =
                 ktc /\
               read (memory :> bytes64(word(pc + got_raw_spin_lock_bh))) s =
                 lk /\
               read (memory :> bytes64(word(pc + got_raw_spin_unlock_bh))) s =
                 ulk /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes64(word_add peer (word 256))) s = word 0 /\
               (~(pp = word 0)
                ==> read (memory :> bytes64 pp) s = nx /\
                    (~(nx = word 0)
                     ==> read (memory :> bytes64(word_add nx (word 8))) s =
                         pp)) /\
               read (memory :> bytes32(word_add peer (word 272))) s = word 0 /\
               read (memory :> bytes(word_add peer (word 296),32)) s = 0 /\
               read (memory :> bytes(word_add peer (word 360),32)) s = 0 /\
               read (memory :> bytes(word_add peer (word 456),64)) s = 0 /\
               read (memory :> bytes32(word_add peer (word 532))) s = word 0 /\
               (~(nk = word 0)
                ==> read (memory :> bytes8(word_add nk (word 72))) s =
                    word 0) /\
               (~(ck = word 0)
                ==> read (memory :> bytes8(word_add ck (word 72))) s =
                    word 0))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add peer (word 160),4);
                      memory :> bytes(word_add peer (word 256),8);
                      memory :> bytes(word_add peer (word 272),4);
                      memory :> bytes(word_add peer (word 296),32);
                      memory :> bytes(word_add peer (word 360),32);
                      memory :> bytes(word_add peer (word 456),64);
                      memory :> bytes(word_add peer (word 532),44);
                      memory :> bytes(word_add peer (word 576),8);
                      memory :> bytes(pp,8);
                      memory :> bytes(word_add nx (word 8),8);
                      memory :> bytes(word_add table (word 65536),4);
                      memory :> bytes(word_add nk (word 72),1);
                      memory :> bytes(word_add ck (word 72),1);
                      memory :> bytes(word_sub stackpointer (word 4176),
                                      4176)])`;;

let WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_EXPIRE_CURRENT_PEER_KEYPAIRS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

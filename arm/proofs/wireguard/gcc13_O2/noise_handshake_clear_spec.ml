(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_handshake_clear(handshake) of the kernel's                       *)
(* drivers/net/wireguard/noise.c in the image: with the lock of the struct   *)
(* noise_handshake at hs (see noise_handshake_create_initiation_spec.ml)     *)
(* held for writing, its entry is removed from the table of indices of the   *)
(* device of its peer (wg_index_hashtable_remove) and it is zeroed           *)
(* (handshake_zero).                                                         *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/index_hashtable_remove_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/handshake_zero_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4160 bytes of stack. nx and pp are the pointers of the hash   *)
(* list node of the entry.                                                   *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!hs peer dev table nx pp dwr uwr lk ulk ea el ev
   pc stackpointer returnaddress.
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     spinlock_bh_contract lk ea el ev /\ spinlock_bh_contract ulk ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4160),4160); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el); (hs,336);
       (peer,8); (word_add dev (word 1152),8);
       (word_add table (word 65536),4); (pp,8); (word_add nx (word 8),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_handshake_clear) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [hs] s /\
               read (memory :> bytes64 hs) s = peer /\
               read (memory :> bytes64 peer) s = dev /\
               read (memory :> bytes64(word_add dev (word 1152))) s = table /\
               read (memory :> bytes64(word_add hs (word 8))) s = nx /\
               read (memory :> bytes64(word_add hs (word 16))) s = pp /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes64(word(pc + got_raw_spin_lock_bh))) s =
                 lk /\
               read (memory :> bytes64(word(pc + got_raw_spin_unlock_bh))) s =
                 ulk /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes64(word_add hs (word 16))) s = word 0 /\
               (~(pp = word 0)
                ==> read (memory :> bytes64 pp) s = nx /\
                    (~(nx = word 0)
                     ==> read (memory :> bytes64(word_add nx (word 8))) s =
                         pp)) /\
               read (memory :> bytes32(word_add hs (word 32))) s = word 0 /\
               read (memory :> bytes(word_add hs (word 56),32)) s = 0 /\
               read (memory :> bytes(word_add hs (word 120),32)) s = 0 /\
               read (memory :> bytes(word_add hs (word 216),64)) s = 0 /\
               read (memory :> bytes32(word_add hs (word 292))) s = word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add hs (word 16),8);
                      memory :> bytes(pp,8);
                      memory :> bytes(word_add nx (word 8),8);
                      memory :> bytes(word_add table (word 65536),4);
                      memory :> bytes(word_add hs (word 32),4);
                      memory :> bytes(word_add hs (word 56),32);
                      memory :> bytes(word_add hs (word 120),32);
                      memory :> bytes(word_add hs (word 216),64);
                      memory :> bytes(word_add hs (word 292),4);
                      memory :> bytes(word_add hs (word 296),40);
                      memory :> bytes(word_sub stackpointer (word 4160),
                                      4160)])`;;

let WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_HANDSHAKE_CLEAR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

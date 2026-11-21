(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_keypair_get(keypair) of the kernel's                             *)
(* drivers/net/wireguard/noise.c in the image: for the struct noise_keypair  *)
(* at kp (1216 bytes, with its reference count, a refcount_t, at 1184), the  *)
(* result is NULL if kp is NULL or the count is zero, and otherwise kp,      *)
(* with the count incremented (kref_get_unless_zero, by the LL/SC loop of    *)
(* the image as built). If the increment reaches the sign bit the count      *)
(* saturates, by refcount_warn_saturate.                                     *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts_session.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contract for                        *)
(* refcount_warn_saturate. The code and its callee use 4128 bytes of stack.  *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_KEYPAIR_GET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!kp rc ws ea el ev pc stackpointer returnaddress.
     refcount_warn_saturate_contract ws ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4128),4128); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (word_add kp (word 1184),4)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_keypair_get) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [kp] s /\
               (~(kp = word 0)
                ==> read (memory :> bytes32(word_add kp (word 1184))) s =
                    rc) /\
               read (memory :> bytes64(word(pc + got_refcount_warn_saturate)))
                 s = ws /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
                 (if kp = word 0 \/ rc = word 0 then word 0 else kp) /\
               (~(kp = word 0) /\ ~(rc = word 0) /\ val rc + 1 < 2 EXP 31
                ==> read (memory :> bytes32(word_add kp (word 1184))) s =
                    word_add rc (word 1)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add kp (word 1184),4);
                      memory :> bytes(word_sub stackpointer (word 4128),
                                      4128)])`;;

let WIREGUARD_NOISE_KEYPAIR_GET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_KEYPAIR_GET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

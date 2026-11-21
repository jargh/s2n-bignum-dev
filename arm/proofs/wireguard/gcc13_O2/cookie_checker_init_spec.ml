(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_checker_init(checker, wg) of the kernel's                       *)
(* drivers/net/wireguard/cookie.c in the image: for the struct               *)
(* cookie_checker at checker (see cookie_validate_packet_spec.ml), the lock  *)
(* of the secret (at 104) is initialized (by __init_rwsem), the birthdate of *)
(* the secret (at 96) becomes the time (ktime_get_coarse_with_offset), the   *)
(* secret (at 0) 32 bytes from get_random_bytes, and the device (at 144) wg. *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4128 bytes of stack.                                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!checker wg irw ktc grb ea el ev pc stackpointer returnaddress.
     init_rwsem_contract irw ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     get_random_bytes_contract grb ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4128),4128); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (checker,152)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_cookie_checker_init) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [checker; wg] s /\
               read (memory :> bytes64(word(pc + got_init_rwsem))) s = irw /\
               read (memory :>
                     bytes64(word(pc + got_ktime_get_coarse_with_offset))) s =
                 ktc /\
               read (memory :> bytes64(word(pc + got_get_random_bytes))) s =
                 grb /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes64(word_add checker (word 144))) s = wg)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(checker,32);
                      memory :> bytes(word_add checker (word 96),56);
                      memory :> bytes(word_sub stackpointer (word 4128),
                                      4128)])`;;

let WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_COOKIE_CHECKER_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

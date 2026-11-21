(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_init(cookie) of the kernel's drivers/net/wireguard/cookie.c in  *)
(* the image: the struct cookie (152 bytes) at cookie (see                   *)
(* cookie_message_consume_spec.ml) is zeroed (by memset) and its lock (at    *)
(* 112) initialized (by __init_rwsem), so its fields before the lock are     *)
(* zero.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4128 bytes of stack.                                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cookie mset irw ea el ev pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ init_rwsem_contract irw ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4128),4128); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (cookie,152)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_cookie_init) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [cookie] s /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_init_rwsem))) s = irw /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(cookie,112)) s = 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(cookie,152);
                      memory :> bytes(word_sub stackpointer (word 4128),
                                      4128)])`;;

let WIREGUARD_COOKIE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_COOKIE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

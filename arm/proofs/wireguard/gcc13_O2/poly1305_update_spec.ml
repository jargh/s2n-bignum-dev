(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* poly1305_update(desc, src, nbytes) of the kernel's lib/crypto/poly1305.c  *)
(* in the image: the state for the key k after the bytes d (poly1305_desc_at *)
(* in ../structs.ml) becomes that after d followed by the nbytes bytes m at  *)
(* src. A partial block in the buffer is completed first (memcpy) and        *)
(* absorbed, then the whole blocks of the rest are absorbed from src, and    *)
(* the remaining bytes are copied to the buffer. nbytes is an unsigned int,  *)
(* zero-extended here, and buflen + nbytes must not wrap around.             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_blocks_spec.ml";;

let WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!desc src nbytes k d m mcpy ea2 el2 ev2 pc stackpointer returnaddress.
     memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH k = 32 /\ LENGTH m = val(nbytes:int64) /\
     val nbytes + 16 < 2 EXP 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 64),64))
         [(word pc,wireguard_size); (desc,104); (src,val nbytes); (ea2,el2);
          (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (desc,104))
         [(word pc,wireguard_size); (src,val nbytes); (ea2,el2);
          (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + poly1305_update) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [desc; src; nbytes] s /\
               poly1305_desc_at desc k d s /\
               read (memory :> bytes(src,val nbytes)) s = num_of_bytelist m /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               poly1305_desc_at desc k (APPEND d m) s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(desc,64);
                      memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

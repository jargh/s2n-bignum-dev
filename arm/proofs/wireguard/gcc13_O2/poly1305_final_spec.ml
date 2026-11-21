(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* poly1305_final(desc, dst) of the kernel's lib/crypto/poly1305.c in the    *)
(* image: from the state for the key k after the bytes d (poly1305_desc_at   *)
(* in ../structs.ml), the 16 bytes at dst become the RFC 8439 tag poly1305 k *)
(* d (common/rfc8439.ml), and the whole struct (280 bytes) is zeroed. A      *)
(* partial block in the buffer is padded (a one byte, then zeros by memset)  *)
(* and absorbed without the 2^128 bit, the tag is computed by                *)
(* poly1305_core_emit with the nonce s at desc + 20 (tested against NULL, so *)
(* the struct must not contain the address 0) and the struct is zeroed with  *)
(* memset.                                                                   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_blocks_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_emit_spec.ml";;

let WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!desc dst k d mset ea el ev pc stackpointer returnaddress.
     memset_contract mset ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH k = 32 /\
     nonoverlapping (desc,280) (word 0,1) /\
     ALL (nonoverlapping (word_sub stackpointer (word 48),48))
         [(word pc,wireguard_size); (desc,280); (dst,16); (ea,el);
          (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (desc,280))
         [(word pc,wireguard_size); (dst,16); (ea,el);
          (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (dst,16))
         [(word pc,wireguard_size); (ea,el); (word(pc + got_memset),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + poly1305_final) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [desc; dst] s /\
               poly1305_desc_at desc k d s /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(dst,16)) s =
                 num_of_bytelist(poly1305 k d) /\
               read (memory :> bytes(desc,280)) s = 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(desc,280); memory :> bytes(dst,16);
                      memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

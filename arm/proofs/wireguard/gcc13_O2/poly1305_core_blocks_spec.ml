(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* poly1305_core_blocks(state, key, src, nblocks, hibit) of the kernel's     *)
(* lib/crypto/poly1305-donna64.c in the image: the accumulator in the state  *)
(* (poly1305_h_at in ../structs.ml) absorbs the nblocks blocks of 16 bytes   *)
(* at src with the key r (poly1305_key_at, as poly1305_core_setkey stores    *)
(* it), each block with 2^128 * hibit added: poly1305_kacc of                *)
(* common/wireguard_kernel.ml. The limbs are multiplied with 128-bit         *)
(* products and only partly reduced. nblocks is an unsigned int and hibit a  *)
(* u32, both zero-extended here, and the state is only written at the end.  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;

let WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!state key src nb hbw m a r pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     r < 2 EXP 124 /\ val(hbw:int64) <= 1 /\ val(nb:int64) < 2 EXP 32 /\
     LENGTH m = 16 * val nb /\
     nonoverlapping (word pc,wireguard_size) (state,24)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + poly1305_core_blocks) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [state; key; src; nb; hbw] s /\
               poly1305_h_at state a s /\ poly1305_key_at key r s /\
               read (memory :> bytes(src,16 * val nb)) s = num_of_bytelist m)
          (\s. read PC s = returnaddress /\
               poly1305_h_at state (poly1305_kacc r a m (val hbw) (val nb)) s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(state,24)])`;;

let WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

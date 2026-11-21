(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* blake2s_compress_generic(state, block, nblocks, inc) of the kernel's      *)
(* lib/crypto/blake2s.c in the image: nblocks >= 1 compressions (RFC 7693)   *)
(* of consecutive 64-byte blocks, the 64-bit counter of the state being      *)
(* incremented by inc before each.                                           *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "common/wireguard_kernel.ml";;
needs "arm/proofs/wireguard/gcc13_O2/wireguard.ml";;

(* The code: a prologue that saves registers in a frame of 272 bytes and     *)
(* copies the counter t and the increment to it; at the loop head, the       *)
(* counter update and the copy of h and of the 64-byte block (as 64-bit      *)
(* words) to the frame, the ten rounds unrolled, an 8-iteration loop for the *)
(* new state words h[i] ^= v[i] ^ v[i + 8], and the count of the blocks; the *)
(* epilogue restores the registers.                                          *)

(* ------------------------------------------------------------------------- *)
(* The correctness theorem. The kernel's struct blake2s_state starts with    *)
(* h[8], t[2] and f[2]: the chained state h, the counter tt (t[0] its low    *)
(* half) and the finalization flags, f[0] all ones or zero (the flag f of    *)
(* the specification) and f[1] zero. Only the low 32 bits of inc are used.   *)
(* The code writes only h and t of the state, and the stack frame of 272     *)
(* bytes below the stack pointer, and uses x18 as a temporary.               *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st blk nb inc tt (h:num->int32) (p:byte list) f pc stackpointer
   returnaddress.
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ 1 <= val(nb:int64) /\ 64 * val nb < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub stackpointer (word 272),272))
         [(word pc,wireguard_size); (st,48); (blk,64 * val nb)] /\
     nonoverlapping (st,48) (word pc,wireguard_size) /\
     nonoverlapping (st,48) (blk,64 * val nb)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + blake2s_compress_generic) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [st; blk; nb; inc] s /\
               (!i. i < 8
                    ==> read(memory :> bytes32(word_add st (word(4 * i)))) s =
                        h i) /\
               read(memory :> bytes64(word_add st (word 32))) s = tt /\
               read(memory :> bytes32(word_add st (word 40))) s =
                 (if f then word_not(word 0) else word 0) /\
               read(memory :> bytes32(word_add st (word 44))) s = word 0 /\
               read(memory :> bytes(blk,64 * val nb)) s = num_of_bytelist p)
          (\s. read PC s = returnaddress /\
               (!i. i < 8
                    ==> read(memory :> bytes32(word_add st (word(4 * i)))) s =
                        blake2s_compress_blocks h p tt
                          (val(word_subword inc (0,32):int32)) f (val nb) i) /\
               read(memory :> bytes64(word_add st (word 32))) s =
                 word_add tt
                   (word(val(word_subword inc (0,32):int32) * val nb)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(st,40);
                      memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_BLAKE2S_COMPRESS_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

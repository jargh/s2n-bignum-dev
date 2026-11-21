(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* blake2s_final(state, out) of the kernel's lib/crypto/blake2s.c in the     *)
(* image: from the state after the bytes d, the first outlen bytes of the    *)
(* hash (blake2s_final_hash in common/wireguard_kernel.ml), and the state    *)
(* zeroed. It pads the buffer with memset, compresses it as the last block   *)
(* with blake2s_compress_generic, copies the output with memcpy and zeroes   *)
(* the state with memset (for memzero_explicit), the C library functions     *)
(* being called through the PLT.                                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_compress_generic_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset at the address *)
(* mset and memcpy at mcpy in the GOT entries, with their code and data in   *)
(* the regions (ea1,el1) and (ea2,el2). The code and                         *)
(* blake2s_compress_generic use 320 bytes of stack.                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st out h0 d outlen mset ea1 el1 ev1 mcpy ea2 el2 ev2 pc stackpointer
   returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ outlen <= 32 /\ LENGTH d < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub stackpointer (word 320),320))
         [(word pc,wireguard_size); (st,120); (out,outlen); (ea1,el1);
          (ea2,el2); (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (st,120))
         [(word pc,wireguard_size); (out,outlen); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (out,outlen))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + blake2s_final) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [st; out] s /\
               blake2s_state_at st h0 d outlen s /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(out,outlen)) s =
                 num_of_bytelist(SUB_LIST(0,outlen)
                   (blake2s_bytes(blake2s_final_hash h0 d))) /\
               read (memory :> bytes(st,120)) s = 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(st,120); memory :> bytes(out,outlen);
                      memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_BLAKE2S_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

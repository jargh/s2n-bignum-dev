(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* blake2s_update(state, in, inlen) of the kernel's lib/crypto/blake2s.c in  *)
(* the image: the state after the bytes d becomes the state after d followed *)
(* by the inlen bytes at in. It copies bytes to the buffer of the state with *)
(* memcpy, called through the PLT, and compresses blocks with                *)
(* blake2s_compress_generic.                                                 *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_compress_generic_spec.ml";;

(* The code: after saving registers in a frame of 64 bytes, nothing for an   *)
(* empty input; otherwise, if the input does not fill the buffer, a copy of  *)
(* it to the buffer after the bytes there; if it does, a copy of the bytes   *)
(* that fill it, a compression of the buffer, a compression of all the       *)
(* complete blocks of the rest but the last, if any, directly from the       *)
(* input, and a copy of the remaining 1 to 64 bytes to the buffer.           *)

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contract for memcpy at the address  *)
(* mcpy in the GOT entry, with its code and data in the region (ea,el). The  *)
(* code and blake2s_compress_generic use 336 bytes of stack.                 *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st inp inlen h0 d m outlen mcpy ea el ev pc stackpointer returnaddress.
     memcpy_contract mcpy ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH m = val(inlen:int64) /\ LENGTH d + val inlen < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub stackpointer (word 336),336))
         [(word pc,wireguard_size); (st,120); (inp,val inlen); (ea,el);
          (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (st,120))
         [(word pc,wireguard_size); (inp,val inlen); (ea,el);
          (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + blake2s_update) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [st; inp; inlen] s /\
               blake2s_state_at st h0 d outlen s /\
               read (memory :> bytes(inp,val inlen)) s = num_of_bytelist m /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               blake2s_state_at st h0 (APPEND d m) outlen s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(st,120);
                      memory :> bytes(word_sub stackpointer (word 336),336)])`;;

let WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_BLAKE2S_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

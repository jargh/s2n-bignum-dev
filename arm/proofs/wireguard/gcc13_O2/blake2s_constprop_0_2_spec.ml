(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The copy of blake2s(out, in, key, outlen, inlen, keylen) (the inline      *)
(* function of the kernel's include/crypto/blake2s.h) that gcc made for      *)
(* drivers/net/wireguard/cookie.c, blake2s.constprop.0 (the label            *)
(* blake2s_constprop_0_2 here), with outlen = 16 and the arguments (out, in, *)
(* key, inlen, keylen): the 16 bytes at out become the keyed BLAKE2s of RFC  *)
(* 7693 (blake2s in common/rfc7693.ml) of the inlen bytes at in with the     *)
(* keylen bytes at key. The state is on the stack, zeroed at entry (as a     *)
(* stack variable) and by blake2s_final.                                     *)
(*                                                                           *)
(* Both callers (compute_mac1 and compute_mac2) pass a nonzero keylen (32 or *)
(* 16), and gcc has dropped the test of keylen in __blake2s_init: the copy   *)
(* always treats the key as nonempty, so the theorem needs 0 < keylen. It    *)
(* also needs keylen <= 32, for which the or of the parameter block is the   *)
(* xor of RFC 7693.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy.    *)
(* The code and its callees use 528 bytes of stack.                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out inp key inlen keylen kb m mset ea1 el1 ev1 mcpy ea2 el2 ev2
   pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH kb = val(keylen:int64) /\ 0 < val keylen /\ val keylen <= 32 /\
     LENGTH m = val(inlen:int64) /\ val inlen + 64 < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub stackpointer (word 528),528))
         [(word pc,wireguard_size); (out,16); (inp,val inlen);
          (key,val keylen); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (out,16))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + blake2s_constprop_0_2) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [out; inp; key; inlen; keylen] s /\
               read (memory :> bytes(key,val keylen)) s = num_of_bytelist kb /\
               read (memory :> bytes(inp,val inlen)) s = num_of_bytelist m /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(out,16)) s =
                 num_of_bytelist(blake2s kb 16 m))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(out,16);
                      memory :> bytes(word_sub stackpointer (word 528),
                                      528)])`;;

let WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

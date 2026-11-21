(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* kdf of the kernel's drivers/net/wireguard/noise.c in the image (the HKDF  *)
(* of the Noise protocol, wg_kdf1/2/3 in common/wireguard.ml). gcc has       *)
(* specialized it (kdf.constprop.0) to first_len = 32, dropping the          *)
(* argument, so the arguments are first_dst, second_dst, third_dst, data,    *)
(* second_len, third_len, data_len and chaining_key, and the other lengths   *)
(* are only compared with zero: a nonzero one copies 32 bytes, which is      *)
(* right since the callers pass 0 or 32. The secret is the HMAC of the data  *)
(* with the chaining key; the outputs, each copied only if its destination   *)
(* is not NULL and its length not zero and all the previous ones were, are   *)
(* the HMACs with the secret of 0x1, of the first output and 0x2, and of the *)
(* second output and 0x3 (wg_kdf_t). The secret and the output buffer on the *)
(* stack are zeroed at the end (and, as stack variables, at the start). A    *)
(* destination may be the chaining key or the data, which are only read by   *)
(* the first HMAC, as when the chaining key is updated in place.             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/hmac_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for memset and memcpy as  *)
(* for hmac. The code and its callees use 800 bytes of stack.                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!d1 d2 d3 data len2 len3 datalen ck db ckb mset ea1 el1 ev1 mcpy ea2 el2 ev2
   pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH ckb = 32 /\ LENGTH db = val(datalen:int64) /\
     64 + val datalen < 2 EXP 64 /\
     (val(len2:int64) = 0 \/ val len2 = 32) /\
     (val(len3:int64) = 0 \/ val len3 = 32) /\
     ALL (nonoverlapping (word_sub stackpointer (word 800),800))
         [(word pc,wireguard_size); (data,val datalen); (ck,32); (d1,32);
          (d2,val len2); (d3,val len3); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (d1,32))
         [(word pc,wireguard_size); (d2,val len2); (d3,val len3);
          (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (d2,val len2))
         [(word pc,wireguard_size); (d3,val len3); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (d3,val len3))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + kdf) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [d1; d2; d3; data; len2; len3; datalen; ck] s /\
               read (memory :> bytes(data,val datalen)) s =
                 num_of_bytelist db /\
               read (memory :> bytes(ck,32)) s = num_of_bytelist ckb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               (~(d1 = word 0)
                ==> read (memory :> bytes(d1,32)) s =
                    num_of_bytelist(wg_kdf_t (wg_hmac ckb db) 1)) /\
               (~(d1 = word 0) /\ ~(d2 = word 0) /\ val len2 = 32
                ==> read (memory :> bytes(d2,32)) s =
                    num_of_bytelist(wg_kdf_t (wg_hmac ckb db) 2)) /\
               (~(d1 = word 0) /\ ~(d2 = word 0) /\ val len2 = 32 /\
                ~(d3 = word 0) /\ val len3 = 32
                ==> read (memory :> bytes(d3,32)) s =
                    num_of_bytelist(wg_kdf_t (wg_hmac ckb db) 3)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(d1,32); memory :> bytes(d2,val len2);
                      memory :> bytes(d3,val len3);
                      memory :> bytes(word_sub stackpointer (word 800),800)])`;;

let WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The theorem for particular values of the first seven arguments (d1, d2,   *)
(* d3, data, len2, len3, datalen), such as a NULL destination with length 0, *)
(* with the conditions and frame regions that become trivial removed and     *)
(* the variables among them quantified again.                                *)
(* ------------------------------------------------------------------------- *)

let KDF_SPECIALIZE_RULE th args =
  let th1 = SPECL args th in
  GENL (filter is_var args)
   (CONV_RULE (DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
               REWRITE_CONV[ALL; ARITH_EQ] THENC
               SIMP_CONV[NONOVERLAPPING_TRIVIAL] THENC
               ONCE_DEPTH_CONV WG_MAYCHANGE_DROP_EMPTY_CONV) th1);;

(* ------------------------------------------------------------------------- *)
(* The same with no second output (d2 NULL, as mix_dh with a NULL key calls  *)
(* it): only the first output is written, whatever len2, d3 and len3 are.    *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!d1 d3 data len2 len3 datalen ck db ckb mset ea1 el1 ev1 mcpy ea2 el2 ev2
   pc stackpointer returnaddress.
     memset_contract mset ea1 el1 ev1 /\ memcpy_contract mcpy ea2 el2 ev2 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH ckb = 32 /\ LENGTH db = val(datalen:int64) /\
     64 + val datalen < 2 EXP 64 /\
     ALL (nonoverlapping (word_sub stackpointer (word 800),800))
         [(word pc,wireguard_size); (data,val datalen); (ck,32); (d1,32);
          (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)] /\
     ALL (nonoverlapping (d1,32))
         [(word pc,wireguard_size); (ea1,el1); (ea2,el2);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + kdf) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [d1; word 0; d3; data; len2; len3; datalen; ck] s /\
               read (memory :> bytes(data,val datalen)) s =
                 num_of_bytelist db /\
               read (memory :> bytes(ck,32)) s = num_of_bytelist ckb /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes(ea1,el1)) s = ev1 /\
               read (memory :> bytes(ea2,el2)) s = ev2)
          (\s. read PC s = returnaddress /\
               (~(d1 = word 0)
                ==> read (memory :> bytes(d1,32)) s =
                    num_of_bytelist(wg_kdf_t (wg_hmac ckb db) 1)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(d1,32);
                      memory :> bytes(word_sub stackpointer (word 800),
                                      800)])`;;

let WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

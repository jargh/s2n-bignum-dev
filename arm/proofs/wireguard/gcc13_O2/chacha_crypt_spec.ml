(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* chacha_crypt(state, dst, src, bytes, nrounds) of the kernel's             *)
(* lib/crypto/chacha.c in the image, for nrounds = 20: the bytes at dst      *)
(* become the xor of those at src (which may be dst) with the ChaCha20       *)
(* keystream of the 16-word state xs, block j of it being that of the state  *)
(* with the counter (word 12) advanced by j (chacha20_kblock of              *)
(* common/wireguard_kernel.ml), and the counter of the state is advanced by  *)
(* the number of blocks used. Whole blocks are xored 64 bits at a time, the  *)
(* rest with __crypto_xor; the block buffer on the stack is zeroed at entry  *)
(* (as a stack variable) but not at the end. The size is an unsigned int.    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha_block_generic_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_xor_spec.ml";;
needs "common/wireguard_kernel.ml";;

let WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st dst src len (xs:num->int32) sl mset ea1 el1 ev1 pc stackpointer
   returnaddress.
     memset_contract mset ea1 el1 ev1 /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH sl = val len /\ val(len:int64) < 2 EXP 32 /\
     (dst = src \/ nonoverlapping (dst,val len) (src,val len)) /\
     ALL (nonoverlapping (word_sub stackpointer (word 256),256))
         [(word pc,wireguard_size); (st,64); (dst,val len); (src,val len);
          (ea1,el1); (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (st,64))
         [(word pc,wireguard_size); (dst,val len); (src,val len); (ea1,el1);
          (word(pc + got_memset),8)] /\
     ALL (nonoverlapping (dst,val len))
         [(word pc,wireguard_size); (ea1,el1); (word(pc + got_memset),8)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + chacha_crypt) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [st; dst; src; len; word 20] s /\
               (!i. i < 16
                    ==> read (memory :> bytes32(word_add st (word(4 * i)))) s =
                        xs i) /\
               read (memory :> bytes(src,val len)) s = num_of_bytelist sl /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes(ea1,el1)) s = ev1)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(dst,val len)) s =
               num_of_bytelist
                (list_of_seq
                  (\i. word_xor (EL i sl)
                                (EL (i MOD 64) (chacha20_kblock xs (i DIV 64))))
                  (val len)) /\
               (!i. i < 16
                    ==> read (memory :> bytes32(word_add st (word(4 * i)))) s =
                        chacha20_ctr xs ((val len + 63) DIV 64) i))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,val len); memory :> bytes(st,64);
                      memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_handshake_create_initiation(dst, handshake) of the kernel's      *)
(* drivers/net/wireguard/noise.c in the image: with the locks of the static  *)
(* identity (for reading) and of the handshake (for writing) held, if the    *)
(* device has a static identity, the first 116 bytes of the initiation       *)
(* message at dst (all but the MACs) and the new chaining key and hash of    *)
(* the handshake are those of wg_create_initiation (../../../../common/      *)
(* wireguard.ml), for the static public key of the identity, the remote      *)
(* static key and precomputed static-static secret of the handshake, the     *)
(* ephemeral private key from 32 random bytes (clamped, and kept in the      *)
(* handshake), the TAI64N timestamp of the time from the kernel and the      *)
(* sender index that wg_index_hashtable_insert gives the handshake's entry.  *)
(* The state of the handshake becomes HANDSHAKE_CREATED_INITIATION, and the  *)
(* result is whether all that worked.                                        *)
(*                                                                           *)
(* The handshake is the struct noise_handshake (336 bytes) at hs: the entry  *)
(* for the table of indices (whose peer field is at 0), the state at 32, a   *)
(* pointer to the static identity at 48, the ephemeral private key at 56,    *)
(* the remote static key at 88, the precomputed secret at 152, the hash at   *)
(* 216, the chaining key at 248 and the lock (a struct rw_semaphore of 40    *)
(* bytes) at 296. The static identity is a struct noise_static_identity      *)
(* (112 bytes) at si, with the public key at 0, the lock at 64 and the flag  *)
(* has_identity at 104. The table of indices of the device is found from the *)
(* peer of the entry (its device at 0, and the device's table at 1152).      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_hash_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/kdf_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_dh_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/message_ephemeral_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_encrypt_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/curve25519_generate_public_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/index_hashtable_insert_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (all with their code and data in one region (ea,el)), the data that       *)
(* wg_noise_init computes (the initial chaining key and hash), and the zero  *)
(* page (wg_zero_page_va in ../contracts.ml). The code and its callees use   *)
(* 4304 bytes of stack, which must not contain the address 0, nor must the   *)
(* handshake. The random bytes r and the time (sec, nsec) are those that     *)
(* the kernel gives, and the sender index is the one in the entry at the     *)
(* end; on success the message is the one of wg_create_initiation.           *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst hs si spub hid rpub ss peer dev table kv ms
   mset mcpy cfn wfrb grb ktm drd urd dwr uwr ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     curve25519_generic_contract cfn ea el ev /\
     wait_for_random_bytes_contract wfrb ea el ev /\
     get_random_bytes_contract grb ea el ev /\
     ktime_get_real_ts64_contract ktm ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH spub = 32 /\ LENGTH rpub = 32 /\ LENGTH ss = 32 /\
     nonoverlapping (word_sub stackpointer (word 4304),4304) (word 0,1) /\
     nonoverlapping (hs,336) (word 0,1) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4304),4304); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
       (ea,el); (dst,116); (hs,336); (si,112); (peer,8);
       (word_add dev (word 1152),8); (table,65544)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_handshake_create_initiation) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [dst; hs] s /\
               read (memory :> bytes64(word_add hs (word 48))) s = si /\
               read (memory :> bytes(si,32)) s = num_of_bytelist spub /\
               read (memory :> bytes8(word_add si (word 104))) s =
                 (if hid then word 1 else word 0) /\
               read (memory :> bytes(word_add hs (word 88),32)) s =
                 num_of_bytelist rpub /\
               read (memory :> bytes(word_add hs (word 152),32)) s =
                 num_of_bytelist ss /\
               read (memory :> bytes64 hs) s = peer /\
               read (memory :> bytes64 peer) s = dev /\
               read (memory :> bytes64(word_add dev (word 1152))) s = table /\
               read (memory :>
                     bytes(word(pc + data_handshake_init_chaining_key),32)) s =
                 num_of_bytelist wg_ck0 /\
               read (memory :>
                     bytes(word(pc + data_handshake_init_hash),32)) s =
                 num_of_bytelist wg_h0 /\
               read (memory :> bytes(word(pc + data_zero_point),32)) s = 0 /\
               read (memory :> bytes64(word(pc + data_kimage_voffset))) s =
                 kv /\
               read (memory :> bytes64(word(pc + data_memstart_addr))) s =
                 ms /\
               read (memory :>
                     bytes(wg_zero_page_va (word(pc + data_empty_zero_page))
                                           kv ms,32)) s = 0 /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes64(word(pc + got_curve25519_generic))) s =
                 cfn /\
               read (memory :> bytes64(word(pc + got_wait_for_random_bytes)))
                 s = wfrb /\
               read (memory :> bytes64(word(pc + got_get_random_bytes))) s =
                 grb /\
               read (memory :> bytes64(word(pc + got_ktime_get_real_ts64))) s =
                 ktm /\
               read (memory :> bytes64(word(pc + got_down_read))) s = drd /\
               read (memory :> bytes64(word(pc + got_up_read))) s = urd /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               ?r sec nsec.
                 LENGTH r = 32 /\
                 (hid
                  ==> read (memory :> bytes(word_add hs (word 56),32)) s =
                      num_of_bytelist(wg_clamp r)) /\
                 C_RETURN s =
                   (if hid /\
                       ~(wg_create_initiation spub rpub ss (wg_clamp r)
                          (wg_tai64n sec nsec)
                          (read (memory :> bytes32(word_add hs (word 28))) s) =
                         NONE)
                    then word 1 else word 0) /\
                 (!msg ck h.
                    hid /\
                    wg_create_initiation spub rpub ss (wg_clamp r)
                      (wg_tai64n sec nsec)
                      (read (memory :> bytes32(word_add hs (word 28))) s) =
                    SOME(msg,ck,h)
                    ==> read (memory :> bytes(dst,116)) s =
                        num_of_bytelist msg /\
                        read (memory :> bytes(word_add hs (word 248),32)) s =
                        num_of_bytelist ck /\
                        read (memory :> bytes(word_add hs (word 216),32)) s =
                        num_of_bytelist h /\
                        read (memory :> bytes32(word_add hs (word 32))) s =
                        word 1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,116);
                      memory :> bytes(word_add hs (word 8),16);
                      memory :> bytes(word_add hs (word 28),8);
                      memory :> bytes(word_add hs (word 56),32);
                      memory :> bytes(word_add hs (word 216),64);
                      memory :> bytes(word_add hs (word 296),40);
                      memory :> bytes(word_add si (word 64),40);
                      memory :> bytes(table,65544);
                      memory :> bytes(word_sub stackpointer (word 4304),
                                      4304)])`;;

let WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_HANDSHAKE_CREATE_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_handshake_create_response(dst, handshake) of the kernel's        *)
(* drivers/net/wireguard/noise.c in the image: with the locks of the static  *)
(* identity (for reading) and of the handshake (for writing) held, if the    *)
(* handshake is in the state HANDSHAKE_CONSUMED_INITIATION (2), the first 60 *)
(* bytes of the response message at dst (all but the MACs) and the new       *)
(* chaining key and hash of the handshake are those of wg_create_response    *)
(* (../../../../common/wireguard.ml), for the chaining key and hash of the   *)
(* handshake, its remote ephemeral and static keys and preshared key, the    *)
(* ephemeral private key from 32 random bytes (clamped, and kept in the      *)
(* handshake), the sender index that wg_index_hashtable_insert gives the     *)
(* handshake's entry and the remote index as the receiver index. The state   *)
(* of the handshake becomes HANDSHAKE_CREATED_RESPONSE (3), and the result   *)
(* is whether all that worked.                                               *)
(*                                                                           *)
(* The handshake (struct noise_handshake, 336 bytes, at hs) has the fields   *)
(* of noise_handshake_create_initiation_spec.ml, and also the remote         *)
(* ephemeral key at 120, the preshared key at 184 and the remote index at    *)
(* 292.                                                                      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_hash_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/kdf_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_dh_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/message_ephemeral_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_encrypt_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/curve25519_generate_public_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/index_hashtable_insert_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)) and the zero page. The   *)
(* code and its callees use 4288 bytes of stack, which must not contain the  *)
(* address 0, nor must the handshake. The random bytes r are those that the  *)
(* kernel gives, and the sender index is the one in the entry at the end; on *)
(* success the message is the one of wg_create_response.                     *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst hs si stw ckb hb repub rspub psk rindex peer dev table kv ms
   mset mcpy cfn wfrb grb drd urd dwr uwr ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     curve25519_generic_contract cfn ea el ev /\
     wait_for_random_bytes_contract wfrb ea el ev /\
     get_random_bytes_contract grb ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH ckb = 32 /\ LENGTH hb = 32 /\ LENGTH repub = 32 /\
     LENGTH rspub = 32 /\ LENGTH psk = 32 /\
     nonoverlapping (word_sub stackpointer (word 4288),4288) (word 0,1) /\
     nonoverlapping (hs,336) (word 0,1) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4288),4288); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
       (ea,el); (dst,60); (hs,336); (si,112); (peer,8);
       (word_add dev (word 1152),8); (table,65544)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_handshake_create_response) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [dst; hs] s /\
               read (memory :> bytes64(word_add hs (word 48))) s = si /\
               read (memory :> bytes32(word_add hs (word 32))) s = stw /\
               read (memory :> bytes(word_add hs (word 248),32)) s =
                 num_of_bytelist ckb /\
               read (memory :> bytes(word_add hs (word 216),32)) s =
                 num_of_bytelist hb /\
               read (memory :> bytes(word_add hs (word 120),32)) s =
                 num_of_bytelist repub /\
               read (memory :> bytes(word_add hs (word 88),32)) s =
                 num_of_bytelist rspub /\
               read (memory :> bytes(word_add hs (word 184),32)) s =
                 num_of_bytelist psk /\
               read (memory :> bytes32(word_add hs (word 292))) s = rindex /\
               read (memory :> bytes64 hs) s = peer /\
               read (memory :> bytes64 peer) s = dev /\
               read (memory :> bytes64(word_add dev (word 1152))) s = table /\
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
               read (memory :> bytes64(word(pc + got_down_read))) s = drd /\
               read (memory :> bytes64(word(pc + got_up_read))) s = urd /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               ?r. LENGTH r = 32 /\
                   (stw = word 2
                    ==> read (memory :> bytes(word_add hs (word 56),32)) s =
                        num_of_bytelist(wg_clamp r)) /\
                   C_RETURN s =
                     (if stw = word 2 /\
                         ~(wg_create_response (ckb,hb) repub rspub psk
                            (wg_clamp r)
                            (read (memory :> bytes32(word_add hs (word 28))) s)
                            rindex = NONE)
                      then word 1 else word 0) /\
                   (!msg ck h.
                      stw = word 2 /\
                      wg_create_response (ckb,hb) repub rspub psk (wg_clamp r)
                        (read (memory :> bytes32(word_add hs (word 28))) s)
                        rindex = SOME(msg,ck,h)
                      ==> read (memory :> bytes(dst,60)) s =
                          num_of_bytelist msg /\
                          read (memory :> bytes(word_add hs (word 248),32)) s =
                          num_of_bytelist ck /\
                          read (memory :> bytes(word_add hs (word 216),32)) s =
                          num_of_bytelist h /\
                          read (memory :> bytes32(word_add hs (word 32))) s =
                          word 3))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,60);
                      memory :> bytes(word_add hs (word 8),16);
                      memory :> bytes(word_add hs (word 28),8);
                      memory :> bytes(word_add hs (word 56),32);
                      memory :> bytes(word_add hs (word 216),64);
                      memory :> bytes(word_add hs (word 296),40);
                      memory :> bytes(word_add si (word 64),40);
                      memory :> bytes(table,65544);
                      memory :> bytes(word_sub stackpointer (word 4288),
                                      4288)])`;;

let WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_HANDSHAKE_CREATE_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

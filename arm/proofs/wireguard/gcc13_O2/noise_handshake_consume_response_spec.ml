(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_handshake_consume_response(src, wg) of the kernel's              *)
(* drivers/net/wireguard/noise.c in the image: with the lock of the device's *)
(* static identity held (for reading), if the device has a static identity,  *)
(* the handshake with the receiver index of the response message at src      *)
(* (its first 60 bytes, without the MACs) is looked up, and if it is in the  *)
(* state HANDSHAKE_CREATED_INITIATION (1), its chaining key, hash, ephemeral *)
(* private key and preshared key are copied (under the lock of the           *)
(* handshake, for reading) and the message is consumed as                    *)
(* wg_consume_response (../../../../common/wireguard.ml) does it, with the   *)
(* static private key of the device. If that gives the responder's           *)
(* ephemeral key and the new chaining key and hash, and (under the lock of   *)
(* the handshake, for writing) the state and ephemeral private key of the    *)
(* handshake are still the same, the handshake gets them and the sender      *)
(* index of the message, its state becomes HANDSHAKE_CONSUMED_RESPONSE (4)   *)
(* and the result is the peer, with the reference that the lookup took.      *)
(* Otherwise the result is NULL, and the reference to the peer, if any, is   *)
(* dropped (wg_peer_put).                                                    *)
(*                                                                           *)
(* The device has the fields of noise_handshake_consume_initiation_spec.ml   *)
(* and the pointer to its table of indices at 1152. The peer is a struct     *)
(* wg_peer (1648 bytes) whose handshake is at 240, so that the handshake's   *)
(* state is at 272, its ephemeral private key at 296, its remote ephemeral   *)
(* key at 360, its preshared key at 424, its hash at 456, its chaining key   *)
(* at 488, its remote index at 532 and its lock at 536.                      *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/kdf_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/mix_dh_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/message_ephemeral_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_decrypt_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The lookup of the handshake with the index idx by                         *)
(* wg_index_hashtable_lookup (in drivers/net/wireguard/peerlookup.c in the   *)
(* image), for the type INDEX_HASHTABLE_HANDSHAKE (1), in the table of       *)
(* indices at tbl: if found, the result is the handshake of the peer, with a *)
(* reference taken to the peer (the entry's peer at 240 and the reference    *)
(* count at 1088 may change), and the peer is stored at out; otherwise the   *)
(* result is NULL. As for the lookup of peers in consume_initiation, the     *)
(* theorem has this behaviour, for the receiver index of the message, as an  *)
(* assumption. It uses 4128 bytes of stack.                                  *)
(* ------------------------------------------------------------------------- *)

let wg_index_lookup_contract = new_definition
 `wg_index_lookup_contract (pc:num) (tbl:int64) (idx:int32) (found:bool)
                           (peer:int64) <=>
    !out stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(word_sub stackpointer (word 4128),4128); (word pc,wireguard_size);
          (word(pc + wireguard_data),wireguard_data_size); (out,8);
          (peer,1648)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
                  read PC s = word(pc + wg_index_hashtable_lookup) /\
                  read SP s = stackpointer /\ read X30 s = returnaddress /\
                  C_ARGUMENTS [tbl; word 1; word_zx idx; out] s)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                    (if found then word_add peer (word 240) else word 0) /\
                  (found ==> read (memory :> bytes64 out) s = peer))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(out,8);
                         memory :> bytes(word_add peer (word 240),8);
                         memory :> bytes(word_add peer (word 1088),4);
                         memory :> bytes(word_sub stackpointer (word 4128),
                                         4128)])`;;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)), the behaviour of the    *)
(* lookup for the receiver index of the message and the zero page. The code  *)
(* and its callees use 4656 bytes of stack, which must not contain the       *)
(* address 0, nor must the peer.                                             *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src wg msg spriv hid itbl found peer st ckb hb epriv psk kv ms
   mset mcpy cfn drd urd dwr uwr wpp ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     curve25519_generic_contract cfn ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     wg_peer_put_contract wpp ea el ev /\
     wg_index_lookup_contract pc itbl
       (word(num_of_bytelist(SUB_LIST(8,4) msg))) found peer /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH msg = 60 /\ LENGTH spriv = 32 /\ LENGTH ckb = 32 /\
     LENGTH hb = 32 /\ LENGTH epriv = 32 /\ LENGTH psk = 32 /\
     nonoverlapping (peer,1648) (word 0,1) /\
     nonoverlapping (word_sub stackpointer (word 4656),4656) (word 0,1) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4656),4656); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
       (ea,el); (src,60); (wg,1344); (peer,1648)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_handshake_consume_response) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [src; wg] s /\
               read (memory :> bytes(src,60)) s = num_of_bytelist msg /\
               read (memory :> bytes(word_add wg (word 888),32)) s =
                 num_of_bytelist spriv /\
               read (memory :> bytes8(word_add wg (word 960))) s =
                 (if hid then word 1 else word 0) /\
               read (memory :> bytes64(word_add wg (word 1152))) s = itbl /\
               read (memory :> bytes32(word_add peer (word 272))) s = st /\
               read (memory :> bytes(word_add peer (word 488),32)) s =
                 num_of_bytelist ckb /\
               read (memory :> bytes(word_add peer (word 456),32)) s =
                 num_of_bytelist hb /\
               read (memory :> bytes(word_add peer (word 296),32)) s =
                 num_of_bytelist epriv /\
               read (memory :> bytes(word_add peer (word 424),32)) s =
                 num_of_bytelist psk /\
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
               read (memory :> bytes64(word(pc + got_down_read))) s = drd /\
               read (memory :> bytes64(word(pc + got_up_read))) s = urd /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes64(word(pc + got_wg_peer_put))) s = wpp /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               C_RETURN s =
                 (if hid /\ found /\ st = word 1 /\
                     ~(wg_consume_response (ckb,hb) epriv spriv psk msg = NONE)
                  then peer else word 0) /\
               (!e ck h.
                  hid /\ found /\ st = word 1 /\
                  wg_consume_response (ckb,hb) epriv spriv psk msg =
                  SOME(e,ck,h)
                  ==> read (memory :> bytes(word_add peer (word 360),32)) s =
                      num_of_bytelist e /\
                      read (memory :> bytes(word_add peer (word 456),32)) s =
                      num_of_bytelist h /\
                      read (memory :> bytes(word_add peer (word 488),32)) s =
                      num_of_bytelist ck /\
                      read (memory :> bytes32(word_add peer (word 532))) s =
                      word(num_of_bytelist(SUB_LIST(4,4) msg)) /\
                      read (memory :> bytes32(word_add peer (word 272))) s =
                      word 4))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add wg (word 920),40);
                      memory :> bytes(peer,1648);
                      memory :> bytes(word_sub stackpointer (word 4656),
                                      4656)])`;;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_HANDSHAKE_CONSUME_RESPONSE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

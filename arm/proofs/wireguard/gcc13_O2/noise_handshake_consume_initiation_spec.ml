(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_noise_handshake_consume_initiation(src, wg) of the kernel's            *)
(* drivers/net/wireguard/noise.c in the image: with the lock of the device's *)
(* static identity held (for reading), if the device has a static identity,  *)
(* the initiation message at src (its first 116 bytes, without the MACs) is  *)
(* consumed as wg_consume_initiation_static and                              *)
(* wg_consume_initiation_timestamp (../../../../common/wireguard.ml) do it:  *)
(* the ephemeral key e and the static key s of the initiator are found,      *)
(* then the peer with the static key s is looked up in the device's table of *)
(* peers, and with the precomputed static-static secret of that peer the     *)
(* timestamp t is found. It is accepted, unless it is not later than the     *)
(* latest timestamp of the handshake (a replay) or the last initiation was   *)
(* consumed less than 20 ms before (a flood, by the coarse boot-time clock), *)
(* and then the handshake of the peer gets the new chaining key and hash,    *)
(* e, t, the sender index of the message and the time, its state becomes     *)
(* HANDSHAKE_CONSUMED_INITIATION and the result is the peer, with the        *)
(* reference that the lookup took. Otherwise the result is NULL, and the     *)
(* reference to the peer, if any, is dropped (wg_peer_put).                  *)
(*                                                                           *)
(* The device is the struct wg_device (1344 bytes) at wg, with its static    *)
(* identity at 856 (public key at 856, private key at 888, lock at 920 and   *)
(* has_identity at 960) and the pointer to its table of peers at 1144. The   *)
(* peer is a struct wg_peer (1648 bytes), whose handshake is at 240, so that *)
(* the handshake's state is at 272, its last initiation consumption at 280,  *)
(* its remote ephemeral key at 360, its precomputed secret at 392, its hash  *)
(* at 456, its chaining key at 488, its latest timestamp at 520, its remote  *)
(* index at 532 and its lock at 536.                                         *)
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
(* The lookup of the peer with the static public key k by                    *)
(* wg_pubkey_hashtable_lookup (in drivers/net/wireguard/peerlookup.c in the  *)
(* image), in the table of peers at tbl: the result is peer, with a          *)
(* reference taken (which may change the reference count of the struct       *)
(* wg_peer, at 1088). Its result depends on the table, which is outside the  *)
(* model, so the theorem for consume_initiation has the behaviour of the     *)
(* lookup, for the static key of the message, as an assumption, with the     *)
(* result peer. It uses 4128 bytes of stack (its frame of 32 bytes and the   *)
(* kernel functions it calls).                                               *)
(* ------------------------------------------------------------------------- *)

let wg_pubkey_lookup_contract = new_definition
 `wg_pubkey_lookup_contract (pc:num) (tbl:int64) (k:byte list) (peer:int64) <=>
    !key stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(word_sub stackpointer (word 4128),4128); (word pc,wireguard_size);
          (word(pc + wireguard_data),wireguard_data_size); (key,32);
          (peer,1648)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
                  read PC s = word(pc + wg_pubkey_hashtable_lookup) /\
                  read SP s = stackpointer /\ read X30 s = returnaddress /\
                  C_ARGUMENTS [tbl; key] s /\
                  read (memory :> bytes(key,32)) s = num_of_bytelist k)
             (\s. read PC s = returnaddress /\ C_RETURN s = peer)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(word_add peer (word 1088),4);
                         memory :> bytes(word_sub stackpointer (word 4128),
                                         4128)])`;;

(* ------------------------------------------------------------------------- *)
(* The handshake functions consuming an initiation, for the peer that the    *)
(* lookup gives (NULL if none), with the precomputed secret ss, the latest   *)
(* timestamp lts and the last initiation consumption lic of its handshake,   *)
(* and the time now of the flood check: the ephemeral key, the timestamp and *)
(* the new chaining key and hash, or NONE. The time check is as the code     *)
(* does it: an unsigned comparison of 64-bit words (the (s64) casts in the   *)
(* source are undone by the type of INITIATIONS_PER_SECOND, a member of an   *)
(* enumeration with members of 64 bits).                                     *)
(* ------------------------------------------------------------------------- *)

let wg_consume_initiation_kernel = new_definition
 `wg_consume_initiation_kernel spriv spub (msg:byte list) (peer:int64) ss lts
                               (lic:int64) (now:int64) =
    match wg_consume_initiation_static spriv spub msg with
      NONE -> NONE
    | SOME(e,s,ck,h) ->
        if peer = word 0 then NONE else
        match wg_consume_initiation_timestamp ss (ck,h) msg with
          NONE -> NONE
        | SOME(t,ck1,h1) ->
            if wg_bytes_lt lts t /\
               val(word_add lic (word 20000000)) <= val now
            then SOME(e,t,ck1,h1) else NONE`;;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (all with their code and data in one region (ea,el)), the behaviour of    *)
(* the lookup for the static key of the message, the data that wg_noise_init *)
(* computes and the zero page. The code and its callees use 4544 bytes of    *)
(* stack, which must not contain the address 0. The times now1 and now2 are  *)
(* those that the kernel gives for the flood check and for the new last      *)
(* consumption, which is the later one of it and the old one.                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src wg msg spub spriv hid tbl peer ss lts lic kv ms
   mset mcpy cfn drd urd dwr uwr mcmp ktc wpp ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     curve25519_generic_contract cfn ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     memcmp_contract mcmp ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     wg_peer_put_contract wpp ea el ev /\
     (!e sk ck h.
        wg_consume_initiation_static spriv spub msg = SOME(e,sk,ck,h)
        ==> wg_pubkey_lookup_contract pc tbl sk peer) /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH msg = 116 /\ LENGTH spub = 32 /\ LENGTH spriv = 32 /\
     LENGTH ss = 32 /\ LENGTH lts = 12 /\
     nonoverlapping (word_sub stackpointer (word 4544),4544) (word 0,1) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4544),4544); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
       (ea,el); (src,116); (wg,1344); (peer,1648)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_noise_handshake_consume_initiation) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [src; wg] s /\
               read (memory :> bytes(src,116)) s = num_of_bytelist msg /\
               read (memory :> bytes(word_add wg (word 856),32)) s =
                 num_of_bytelist spub /\
               read (memory :> bytes(word_add wg (word 888),32)) s =
                 num_of_bytelist spriv /\
               read (memory :> bytes8(word_add wg (word 960))) s =
                 (if hid then word 1 else word 0) /\
               read (memory :> bytes64(word_add wg (word 1144))) s = tbl /\
               read (memory :> bytes(word_add peer (word 392),32)) s =
                 num_of_bytelist ss /\
               read (memory :> bytes(word_add peer (word 520),12)) s =
                 num_of_bytelist lts /\
               read (memory :> bytes64(word_add peer (word 280))) s = lic /\
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
               read (memory :> bytes64(word(pc + got_down_read))) s = drd /\
               read (memory :> bytes64(word(pc + got_up_read))) s = urd /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes64(word(pc + got_memcmp))) s = mcmp /\
               read (memory :>
                     bytes64(word(pc + got_ktime_get_coarse_with_offset))) s =
                 ktc /\
               read (memory :> bytes64(word(pc + got_wg_peer_put))) s = wpp /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               ?now1 now2.
                 C_RETURN s =
                   (if hid /\
                       ~(wg_consume_initiation_kernel spriv spub msg peer ss
                           lts lic now1 = NONE)
                    then peer else word 0) /\
                 (!e t ck h.
                    hid /\
                    wg_consume_initiation_kernel spriv spub msg peer ss
                      lts lic now1 = SOME(e,t,ck,h)
                    ==> read (memory :> bytes(word_add peer (word 360),32)) s =
                        num_of_bytelist e /\
                        read (memory :> bytes(word_add peer (word 520),12)) s =
                        num_of_bytelist t /\
                        read (memory :> bytes(word_add peer (word 456),32)) s =
                        num_of_bytelist h /\
                        read (memory :> bytes(word_add peer (word 488),32)) s =
                        num_of_bytelist ck /\
                        read (memory :> bytes32(word_add peer (word 532))) s =
                        word(num_of_bytelist(SUB_LIST(4,4) msg)) /\
                        read (memory :> bytes64(word_add peer (word 280))) s =
                        (if ival(word_sub lic now2) < &0 then now2 else lic) /\
                        read (memory :> bytes32(word_add peer (word 272))) s =
                        word 2))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add wg (word 920),40);
                      memory :> bytes(peer,1648);
                      memory :> bytes(word_sub stackpointer (word 4544),
                                      4544)])`;;

let WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_NOISE_HANDSHAKE_CONSUME_INITIATION_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

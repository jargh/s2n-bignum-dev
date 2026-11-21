(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_message_consume(src, wg) of the kernel's                        *)
(* drivers/net/wireguard/cookie.c in the image, for the 64-byte cookie reply *)
(* at src (its receiver index at 4, nonce at 8 and encrypted cookie at 32):  *)
(* the entry (of a handshake or a keypair) with the receiver index is looked *)
(* up, with a reference taken to its peer; if found and the peer's latest    *)
(* cookie (a struct cookie at 680 in the struct wg_peer, its lock at 112)    *)
(* has a mac1 sent (have_sent_mac1 at 25), the encrypted cookie is decrypted *)
(* (wg_xaead_decrypt of common/wireguard.ml) with the cookie's decryption    *)
(* key (at 42) and the last mac1 sent (at 26) as associated data, under the  *)
(* lock held for reading. If that succeeds the cookie (at 9) becomes the     *)
(* plaintext, its birthdate the time, is_valid (at 8) 1 and have_sent_mac1   *)
(* 0, under the lock held for writing; otherwise the cookie is unchanged.    *)
(* The reference to the peer is then dropped (wg_peer_put). The decrypted    *)
(* cookie on the stack is not zeroed at the end.                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/xchacha20poly1305_decrypt_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The lookup of the entry with the index idx by wg_index_hashtable_lookup,  *)
(* for the types ty, in the table at tbl, as in                              *)
(* noise_handshake_consume_response_spec.ml but for any entry ent: if found, *)
(* the result is ent (its peer field, at 0, may change) with a reference     *)
(* taken to the peer, which is stored at out.                                *)
(* ------------------------------------------------------------------------- *)

let wg_index_lookup_entry_contract = new_definition
 `wg_index_lookup_entry_contract (pc:num) (tbl:int64) (ty:num) (idx:int32)
                                 (found:bool) (ent:int64) (peer:int64) <=>
    !out stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(word_sub stackpointer (word 4128),4128); (word pc,wireguard_size);
          (word(pc + wireguard_data),wireguard_data_size); (out,8);
          (ent,8); (word_add peer (word 1088),4)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
                  read PC s = word(pc + wg_index_hashtable_lookup) /\
                  read SP s = stackpointer /\ read X30 s = returnaddress /\
                  C_ARGUMENTS [tbl; word ty; word_zx idx; out] s)
             (\s. read PC s = returnaddress /\
                  C_RETURN s = (if found then ent else word 0) /\
                  (found ==> read (memory :> bytes64 out) s = peer))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(out,8); memory :> bytes(ent,8);
                         memory :> bytes(word_add peer (word 1088),4);
                         memory :> bytes(word_sub stackpointer (word 4128),
                                         4128)])`;;

(* ------------------------------------------------------------------------- *)
(* wg_peer_put(peer) (drivers/net/wireguard/peer.c, not in the image) for a  *)
(* peer that is not NULL, finer than wg_peer_put_contract of contracts.ml:   *)
(* it drops the reference (the refcount at 1088) and, for the last one,      *)
(* removes the handshake's entry from the table of indices, purges the       *)
(* staged packets and queues the peer to be freed after an RCU grace period  *)
(* (its rcu_head), none of which is in the latest cookie (152 bytes at 680), *)
(* which is the only part of the peer that it keeps. It uses 4096 bytes of   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let wg_peer_put_cookie_contract = new_definition
 `wg_peer_put_cookie_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !peer stackpointer returnaddress.
        aligned 16 stackpointer /\ ~(peer = word 0) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el) /\
        nonoverlapping (peer,1648) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [peer] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(peer,680);
                         memory :> bytes(word_add peer (word 832),816);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)), the behaviour of the    *)
(* lookup for the receiver index of the message and the zero page. The code  *)
(* and its callees use 4864 bytes of stack, which must not contain the       *)
(* address 0. cb is the latest cookie's birthdate, is_valid, cookie and      *)
(* have_sent_mac1, kept on failure. The peer changes apart from the rest of  *)
(* its latest cookie (as wg_peer_put may change it).                         *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src wg itbl msg found ent peer sent dk lm cb kv ms
   mset mcpy dwr uwr drd urd ktc wpp ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     wg_peer_put_cookie_contract wpp ea el ev /\
     wg_index_lookup_entry_contract pc itbl 3
       (word(num_of_bytelist(SUB_LIST(4,4) msg))) found ent peer /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH msg = 64 /\ LENGTH dk = 32 /\ LENGTH lm = 16 /\
     ~(ent = word 0) /\ nonoverlapping (peer,1648) (word 0,1) /\
     nonoverlapping (word_sub stackpointer (word 4864),4864) (word 0,1) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4864),4864); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
       (ea,el); (src,64); (word_add wg (word 1152),8); (ent,8);
       (peer,1648)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_cookie_message_consume) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [src; wg] s /\
               read (memory :> bytes(src,64)) s = num_of_bytelist msg /\
               read (memory :> bytes64(word_add wg (word 1152))) s = itbl /\
               read (memory :> bytes8(word_add peer (word 705))) s =
                 (if sent then word 1 else word 0) /\
               read (memory :> bytes(word_add peer (word 722),32)) s =
                 num_of_bytelist dk /\
               read (memory :> bytes(word_add peer (word 706),16)) s =
                 num_of_bytelist lm /\
               read (memory :> bytes(word_add peer (word 680),26)) s = cb /\
               read (memory :> bytes64(word(pc + data_kimage_voffset))) s =
                 kv /\
               read (memory :> bytes64(word(pc + data_memstart_addr))) s =
                 ms /\
               read (memory :>
                     bytes(wg_zero_page_va (word(pc + data_empty_zero_page))
                                           kv ms,32)) s = 0 /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes64(word(pc + got_down_read))) s = drd /\
               read (memory :> bytes64(word(pc + got_up_read))) s = urd /\
               read (memory :>
                     bytes64(word(pc + got_ktime_get_coarse_with_offset))) s =
                 ktc /\
               read (memory :> bytes64(word(pc + got_wg_peer_put))) s = wpp /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               (!c. found /\ sent /\
                    wg_xaead_decrypt dk (SUB_LIST(8,24) msg)
                      (SUB_LIST(32,32) msg) lm = SOME c
                    ==> read (memory :> bytes(word_add peer (word 689),16)) s =
                        num_of_bytelist c /\
                        read (memory :> bytes8(word_add peer (word 688))) s =
                        word 1 /\
                        read (memory :> bytes8(word_add peer (word 705))) s =
                        word 0) /\
               (~(found /\ sent /\
                  ~(wg_xaead_decrypt dk (SUB_LIST(8,24) msg)
                      (SUB_LIST(32,32) msg) lm = NONE))
                ==> read (memory :> bytes(word_add peer (word 680),26)) s =
                    cb))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(ent,8);
                      memory :> bytes(peer,706);
                      memory :> bytes(word_add peer (word 792),856);
                      memory :> bytes(word_sub stackpointer (word 4864),
                                      4864)])`;;

let WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_COOKIE_MESSAGE_CONSUME_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

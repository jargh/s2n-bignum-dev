(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_add_mac_to_packet(message, len, peer) of the kernel's           *)
(* drivers/net/wireguard/cookie.c in the image: the last 32 bytes of the len *)
(* bytes of the handshake message at message are its MACs. With the lock of  *)
(* the peer's latest cookie (a struct cookie at 680 in the struct wg_peer,   *)
(* its lock at 112) held for writing, mac1 becomes the MAC (wg_mac of        *)
(* common/wireguard.ml, keyed BLAKE2s-128) of the message before the MACs    *)
(* with the cookie's mac1 key (at 74), and it is kept in the cookie as the   *)
(* last mac1 sent (at 26, have_sent_mac1 at 25 becoming 1). Then, with the  *)
(* lock held for reading, mac2 becomes the MAC of the message up to mac2     *)
(* with the cookie (at 9) if the cookie is valid (is_valid at 8) and not     *)
(* older than 115 seconds (its birthdate at 0, against the boot time that    *)
(* ktime_get_coarse_with_offset gives, now here, compared as signed 64-bit   *)
(* numbers), and zero otherwise.                                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_constprop_0_2_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4160 bytes of stack.                                          *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!msg len peer mb mk ck valid bd mset mcpy dwr uwr drd urd ktc ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     32 <= val(len:int64) /\ val len + 64 < 2 EXP 64 /\
     LENGTH mb = val len - 32 /\ LENGTH mk = 32 /\ LENGTH ck = 16 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4160),4160); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (msg,val len); (word_add peer (word 680),152)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_cookie_add_mac_to_packet) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [msg; len; peer] s /\
               read (memory :> bytes(msg,val len - 32)) s = num_of_bytelist mb /\
               read (memory :> bytes(word_add peer (word 754),32)) s =
                 num_of_bytelist mk /\
               read (memory :> bytes(word_add peer (word 689),16)) s =
                 num_of_bytelist ck /\
               read (memory :> bytes8(word_add peer (word 688))) s =
                 (if valid then word 1 else word 0) /\
               read (memory :> bytes64(word_add peer (word 680))) s = bd /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes64(word(pc + got_down_read))) s = drd /\
               read (memory :> bytes64(word(pc + got_up_read))) s = urd /\
               read (memory :>
                     bytes64(word(pc + got_ktime_get_coarse_with_offset))) s =
                 ktc /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes(word_add msg (word(val len - 32)),16)) s =
                 num_of_bytelist(wg_mac mk mb) /\
               read (memory :> bytes(word_add peer (word 706),16)) s =
                 num_of_bytelist(wg_mac mk mb) /\
               read (memory :> bytes8(word_add peer (word 705))) s = word 1 /\
               ?now:int64.
                 read (memory :> bytes(word_add msg (word(val len - 16)),16))
                   s =
                 (if valid /\
                     ival now < ival(word_add bd (word 115000000000):int64)
                  then num_of_bytelist(wg_mac ck (APPEND mb (wg_mac mk mb)))
                  else 0))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(word_add msg (word(val len - 32)),32);
                      memory :> bytes(word_add peer (word 705),17);
                      memory :> bytes(word_add peer (word 792),40);
                      memory :> bytes(word_sub stackpointer (word 4160),
                                      4160)])`;;

let WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

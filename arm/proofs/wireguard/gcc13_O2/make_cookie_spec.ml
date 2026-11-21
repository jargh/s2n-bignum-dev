(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* make_cookie(cookie, skb, checker) of the kernel's                         *)
(* drivers/net/wireguard/cookie.c in the image (a static function): the 16   *)
(* bytes at cookie become the MAC (wg_mac of common/wireguard.ml, keyed      *)
(* BLAKE2s-128) with the secret of the cookie checker of the source address  *)
(* of the packet (4 bytes for IPv4, 16 for IPv6, none for another protocol)  *)
(* followed by its UDP source port. If the secret is at least 120 seconds    *)
(* old (its birthdate against the boot time that                             *)
(* ktime_get_coarse_with_offset gives, as signed 64-bit numbers), it is      *)
(* first replaced, under the lock of the secret held for writing, by 32      *)
(* bytes from get_random_bytes and its birthdate by the time; the MAC is     *)
(* computed under the lock held for reading, with the secret in the checker  *)
(* at the end. blake2s_init_key is inlined.                                  *)
(*                                                                           *)
(* The struct sk_buff at skb has the protocol at 176 (big-endian, so 0x0008  *)
(* for IPv4 and 0xdd86 for IPv6 as read), the offsets of the transport and   *)
(* network headers at 178 and 180, and head at 192; the source address is    *)
(* at 12 of the IPv4 header and at 8 of the IPv6 header, and the source port *)
(* at 0 of the UDP header. The struct cookie_checker at checker has the      *)
(* secret at 0, its birthdate at 96 and its lock at 104.                     *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/structs.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_update_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_final_spec.ml";;

(* The data that the cookie is the MAC of: the address for the protocol and  *)
(* the port.                                                                 *)

let wg_cookie_data = new_definition
 `wg_cookie_data (proto:int16) (a4:byte list) (a6:byte list) port =
    APPEND (if proto = word 0x0008 then a4
            else if proto = word 0xdd86 then a6 else []) port`;;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4288 bytes of stack. The bytes at the places of both kinds of *)
(* address are given, as a4 and a6; the one for the protocol is used.        *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cookie skb checker proto th nh head sec bd a4 a6 port
   mset mcpy dwr uwr drd urd ktc grb ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     get_random_bytes_contract grb ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     LENGTH sec = 32 /\ LENGTH a4 = 4 /\ LENGTH a6 = 16 /\ LENGTH port = 2 /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4288),4288); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (cookie,16); (checker,144); (word_add skb (word 176),24)] /\
     ALL (\r. ALL (nonoverlapping r)
                  [(word_sub stackpointer (word 4288),4288); (cookie,16);
                   (checker,144)])
         [(word_add head (word(val nh + 12)),4);
          (word_add head (word(val nh + 8)),16);
          (word_add head (word(val th)),2)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + make_cookie) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [cookie; skb; checker] s /\
               read (memory :> bytes16(word_add skb (word 176))) s = proto /\
               read (memory :> bytes16(word_add skb (word 178))) s = th /\
               read (memory :> bytes16(word_add skb (word 180))) s = nh /\
               read (memory :> bytes64(word_add skb (word 192))) s = head /\
               read (memory :> bytes(word_add head (word(val nh + 12)),4)) s =
                 num_of_bytelist a4 /\
               read (memory :> bytes(word_add head (word(val nh + 8)),16)) s =
                 num_of_bytelist a6 /\
               read (memory :> bytes(word_add head (word(val th)),2)) s =
                 num_of_bytelist port /\
               read (memory :> bytes(checker,32)) s = num_of_bytelist sec /\
               read (memory :> bytes64(word_add checker (word 96))) s = bd /\
               read (memory :> bytes64(word(pc + got_memset))) s = mset /\
               read (memory :> bytes64(word(pc + got_memcpy))) s = mcpy /\
               read (memory :> bytes64(word(pc + got_down_write))) s = dwr /\
               read (memory :> bytes64(word(pc + got_up_write))) s = uwr /\
               read (memory :> bytes64(word(pc + got_down_read))) s = drd /\
               read (memory :> bytes64(word(pc + got_up_read))) s = urd /\
               read (memory :>
                     bytes64(word(pc + got_ktime_get_coarse_with_offset))) s =
                 ktc /\
               read (memory :> bytes64(word(pc + got_get_random_bytes))) s =
                 grb /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               ?sec'. LENGTH sec' = 32 /\
                      read (memory :> bytes(checker,32)) s =
                        num_of_bytelist sec' /\
                      read (memory :> bytes(cookie,16)) s =
                        num_of_bytelist
                         (wg_mac sec' (wg_cookie_data proto a4 a6 port)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(cookie,16);
                      memory :> bytes(checker,32);
                      memory :> bytes(word_add checker (word 96),48);
                      memory :> bytes(word_sub stackpointer (word 4288),
                                      4288)])`;;

let WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_message_create(dst, skb, index, checker) of the kernel's        *)
(* drivers/net/wireguard/cookie.c in the image: the 64-byte cookie reply at  *)
(* dst gets the type 3 (MESSAGE_HANDSHAKE_COOKIE) and the receiver index     *)
(* ridx, 24 bytes of nonce from get_random_bytes (after                      *)
(* wait_for_random_bytes) at 8, and at 32 the XAEAD encryption (wg_xaead of  *)
(* common/wireguard.ml) with the checker's key for cookie replies (at 32)    *)
(* and the nonce of the cookie that make_cookie gives for the packet (with   *)
(* the checker's secret at the end, sec'), with the mac1 of the packet (the  *)
(* 16 bytes 32 before the end of the len bytes at data) as associated data.  *)
(* The skb and the data of the cookie are as for make_cookie and             *)
(* wg_cookie_validate_packet; the local copy of the cookie on the stack is   *)
(* not zeroed at the end.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/make_cookie_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/xchacha20poly1305_encrypt_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)) and the zero page. The   *)
(* code and its callees use 4368 bytes of stack, which must not contain the  *)
(* address 0.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!dst skb ridx checker len data m1 ck proto th nh head sec bd a4 a6 port
   kv ms mset mcpy dwr uwr drd urd ktc grb wfrb ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     get_random_bytes_contract grb ea el ev /\
     wait_for_random_bytes_contract wfrb ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     32 <= val(len:int32) /\ LENGTH m1 = 16 /\ LENGTH ck = 32 /\
     LENGTH sec = 32 /\ LENGTH a4 = 4 /\ LENGTH a6 = 16 /\ LENGTH port = 2 /\
     nonoverlapping (word_sub stackpointer (word 4368),4368) (word 0,1) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4368),4368); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size);
       (wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms,32);
       (ea,el); (dst,64); (checker,144); (word_add skb (word 112),96);
       (word_add data (word(val len - 32)),16)] /\
     ALL (\r. ALL (nonoverlapping r)
                  [(word_sub stackpointer (word 4368),4368); (dst,64);
                   (checker,144)])
         [(word_add head (word(val nh + 12)),4);
          (word_add head (word(val nh + 8)),16);
          (word_add head (word(val th)),2)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_cookie_message_create) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [dst; skb; word_zx(ridx:int32); checker] s /\
               read (memory :> bytes32(word_add skb (word 112))) s = len /\
               read (memory :> bytes64(word_add skb (word 200))) s = data /\
               read (memory :> bytes(word_add data (word(val len - 32)),16))
                 s = num_of_bytelist m1 /\
               read (memory :> bytes(word_add checker (word 32),32)) s =
                 num_of_bytelist ck /\
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
               read (memory :> bytes64(word(pc + got_get_random_bytes))) s =
                 grb /\
               read (memory :> bytes64(word(pc + got_wait_for_random_bytes)))
                 s = wfrb /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes32 dst) s = word 3 /\
               read (memory :> bytes32(word_add dst (word 4))) s = ridx /\
               ?nonce sec'.
                 LENGTH nonce = 24 /\
                 read (memory :> bytes(word_add dst (word 8),24)) s =
                   num_of_bytelist nonce /\
                 read (memory :> bytes(word_add dst (word 32),32)) s =
                   num_of_bytelist
                    (wg_xaead ck nonce
                       (wg_mac sec' (wg_cookie_data proto a4 a6 port)) m1))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,64);
                      memory :> bytes(checker,32);
                      memory :> bytes(word_add checker (word 96),48);
                      memory :> bytes(word_sub stackpointer (word 4368),
                                      4368)])`;;

let WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_COOKIE_MESSAGE_CREATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

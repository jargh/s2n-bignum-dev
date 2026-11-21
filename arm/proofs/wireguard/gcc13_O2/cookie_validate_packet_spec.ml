(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* wg_cookie_validate_packet(checker, skb, check_cookie) of the kernel's     *)
(* drivers/net/wireguard/cookie.c in the image, for the handshake message of *)
(* len bytes msg at data in the struct sk_buff at skb (its len at 112 and    *)
(* data at 200), whose last 32 bytes are its MACs: the result is 0           *)
(* (INVALID_MAC) unless mac1 is the MAC (wg_mac of common/wireguard.ml,      *)
(* keyed BLAKE2s-128) of the message before the MACs with the checker's mac1 *)
(* key (at 64); otherwise 1 (VALID_MAC_BUT_NO_COOKIE) if check_cookie is     *)
(* false or mac2 is not the MAC of the message up to mac2 with the cookie    *)
(* that make_cookie gives for the packet (with the checker's secret at the   *)
(* end, sec'); otherwise 2 or 3 (VALID_MAC_WITH_COOKIE_BUT_RATELIMITED or    *)
(* VALID_MAC_WITH_COOKIE) as wg_ratelimiter_allow refuses or allows the      *)
(* packet. The rate limiter is outside the image; the theorem has a contract *)
(* for it in which the result (a bool in the low byte of W0) is arbitrary.   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/relative.ml";;
needs "arm/proofs/wireguard/contracts.ml";;
needs "arm/proofs/wireguard/gcc13_O2/blake2s_constprop_0_2_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/crypto_memneq_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/make_cookie_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* wg_ratelimiter_allow(skb, net) (drivers/net/wireguard/ratelimiter.c, not  *)
(* in the image): it returns a bool and changes nothing visible here (its    *)
(* state is private to the kernel); it uses 4096 bytes of stack.             *)
(* ------------------------------------------------------------------------- *)

let wg_ratelimiter_allow_contract = new_definition
 `wg_ratelimiter_allow_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !skb net stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [skb; net] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  ?b. word_and (read X0 s) (word 255) =
                      (if b then word 1 else word 0))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem, assuming the contracts for the kernel functions  *)
(* (with their code and data in one region (ea,el)). The code and its        *)
(* callees use 4368 bytes of stack. check_cookie is the low byte of cc; the  *)
(* data of the cookie are as for make_cookie.                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!checker skb cc check len data msg mk proto th nh head sec bd a4 a6 port
   mset mcpy dwr uwr drd urd ktc grb rla ea el ev
   pc stackpointer returnaddress.
     memset_contract mset ea el ev /\ memcpy_contract mcpy ea el ev /\
     rwsem_contract dwr ea el ev /\ rwsem_contract uwr ea el ev /\
     rwsem_contract drd ea el ev /\ rwsem_contract urd ea el ev /\
     ktime_get_coarse_with_offset_contract ktc ea el ev /\
     get_random_bytes_contract grb ea el ev /\
     wg_ratelimiter_allow_contract rla ea el ev /\
     aligned 4096 (word pc:int64) /\ pc + wireguard_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     32 <= val(len:int32) /\ LENGTH msg = val len /\ LENGTH mk = 32 /\
     LENGTH sec = 32 /\ LENGTH a4 = 4 /\ LENGTH a6 = 16 /\ LENGTH port = 2 /\
     word_and cc (word 255) = (if check then word 1 else word 0) /\
     PAIRWISE nonoverlapping
      [(word_sub stackpointer (word 4368),4368); (word pc,wireguard_size);
       (word(pc + wireguard_data),wireguard_data_size); (ea,el);
       (checker,144); (word_add skb (word 112),96); (data,val len)] /\
     ALL (\r. ALL (nonoverlapping r)
                  [(word_sub stackpointer (word 4368),4368); (checker,144)])
         [(word_add head (word(val nh + 12)),4);
          (word_add head (word(val nh + 8)),16);
          (word_add head (word(val th)),2)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) wireguard_gcc13_O2_mc /\
               read PC s = word(pc + wg_cookie_validate_packet) /\
               read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [checker; skb; cc] s /\
               read (memory :> bytes32(word_add skb (word 112))) s = len /\
               read (memory :> bytes64(word_add skb (word 200))) s = data /\
               read (memory :> bytes(data,val len)) s = num_of_bytelist msg /\
               read (memory :> bytes(word_add checker (word 64),32)) s =
                 num_of_bytelist mk /\
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
               read (memory :> bytes64(word(pc + got_wg_ratelimiter_allow)))
                 s = rla /\
               read (memory :> bytes(ea,el)) s = ev)
          (\s. read PC s = returnaddress /\
               ?sec' allowed.
                 C_RETURN s =
                 (if ~(wg_mac mk (SUB_LIST(0,val len - 32) msg) =
                       SUB_LIST(val len - 32,16) msg)
                  then word 0
                  else if ~check then word 1
                  else if ~(wg_mac (wg_mac sec'
                                         (wg_cookie_data proto a4 a6 port))
                                   (SUB_LIST(0,val len - 16) msg) =
                            SUB_LIST(val len - 16,16) msg)
                  then word 1
                  else if allowed then word 3 else word 2))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(checker,32);
                      memory :> bytes(word_add checker (word 96),48);
                      memory :> bytes(word_sub stackpointer (word 4368),
                                      4368)])`;;

let WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

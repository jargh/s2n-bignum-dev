(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Contracts for the kernel functions that the code for sessions (the        *)
(* keypairs of noise.c and the tables of peerlookup.c) calls, in the         *)
(* sequential model of contracts.ml: each may change only what it says and   *)
(* the 4096 bytes of stack below the stack pointer, which must be 16-byte    *)
(* aligned.                                                                  *)
(*                                                                           *)
(*  - kmalloc_cache_noprof(cache, flags, size), as kzalloc for an object of  *)
(*    n bytes (kzalloc_contract, for the address p that it gives): the       *)
(*    result is NULL or p, and in the second case the n bytes at p are zero; *)
(*                                                                           *)
(*  - kfree_sensitive(p) of the object of n bytes at p (it zeroes and frees  *)
(*    it) may change those n bytes;                                          *)
(*                                                                           *)
(*  - call_rcu(head, func) may change the struct rcu_head (16 bytes) at      *)
(*    head; it calls func later, which is outside the model;                 *)
(*                                                                           *)
(*  - local_bh_enable_ip(ip, cnt), with the current task at t (SP_EL0), may  *)
(*    change the 4 bytes at t + 8 (the preempt count);                       *)
(*                                                                           *)
(*  - refcount_warn_saturate(r, t) may change the 4 bytes of the refcount_t  *)
(*    at r.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/contracts.ml";;

let kzalloc_contract = new_definition
 `kzalloc_contract (f:int64) (ea:int64) (el:num) (ev:num) (p:int64) (n:num) <=>
    !cache flags size stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [cache; flags; size] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  (C_RETURN s = word 0 \/
                   C_RETURN s = p /\ read (memory :> bytes(p,n)) s = 0))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(p,n);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let kfree_sensitive_contract = new_definition
 `kfree_sensitive_contract (f:int64) (ea:int64) (el:num) (ev:num) (n:num) <=>
    !p stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (p,n) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(p,n);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let call_rcu_contract = new_definition
 `call_rcu_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !head func stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (head,16) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [head; func] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(head,16);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let local_bh_enable_ip_contract = new_definition
 `local_bh_enable_ip_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !ip cnt t stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word_add t (word 8),4) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ip; cnt] s /\
                  read SP_EL0 s = t /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(word_add t (word 8),4);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let refcount_warn_saturate_contract = new_definition
 `refcount_warn_saturate_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !r t stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (r,4) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; t] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(r,4);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Contracts for the kernel functions that the image calls through its PLT   *)
(* and GOT (see wireguard/README.md), and tactics for calls of them.         *)
(*                                                                           *)
(* Their code is not part of the image, so their behaviour is assumed, as a  *)
(* high-level contract for each of them, in the same way as for the C        *)
(* library functions called by the mlkem-native binaries (the contracts for  *)
(* memset and memcpy are those of arm/proofs/utils/mlkem_native_libc.ml on   *)
(* the mlkem-arm branch). A contract states the behaviour of the function at *)
(* an address f (which a caller reads from the GOT) in any state where some  *)
(* region (ea,el) of memory, containing its code and any data it uses, has   *)
(* fixed contents ev; the callers require that region not to overlap         *)
(* anything they write, so that it is unchanged when they call the function. *)
(* The functions may change the registers that the ABI allows them to, as    *)
(* well as X18 and X30, but no memory except their outputs and, for those    *)
(* that use it, a stated amount of stack below the stack pointer (memset     *)
(* and memcpy, in assembly in the kernel, do not use the stack). memset      *)
(* sets each of the len bytes at dst to the low byte of c and memcpy copies  *)
(* the len bytes at src to dst, which must not overlap.                      *)
(* ========================================================================= *)

needs "arm/proofs/utils/wireguard.ml";;
needs "common/wireguard.ml";;

(* ------------------------------------------------------------------------- *)
(* The contracts for correctness.                                            *)
(* ------------------------------------------------------------------------- *)

let memset_contract = new_definition
 `memset_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !dst c len returnaddress.
        nonoverlapping (dst,val len) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; c; len] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  !i. i < val len
                      ==> read (memory :> bytes8(word_add dst (word i))) s =
                          word_zx c)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

let memcpy_contract = new_definition
 `memcpy_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !dst src len x returnaddress.
        nonoverlapping (dst,val len) (ea,el) /\
        nonoverlapping (dst,val len) (src,val len)
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [dst; src; len] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(src,val len)) s = x)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(dst,val len)) s = x)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(dst,val len)])`;;

(* curve25519_generic(out, scalar, point), the kernel's HACL* code of        *)
(* lib/crypto/curve25519-hacl64.c, which is not part of the image (to be     *)
(* proved later): X25519 (wg_dh) of the 32-byte scalar and u-coordinate at   *)
(* scalar and point, written to the 32 bytes at out, which must not overlap  *)
(* them. Unlike memset and memcpy it uses the stack, 1216 bytes below the    *)
(* stack pointer (its own frame of 592 bytes and the 624 of ladder_cmult in  *)
(* the arm64 build), and needs it 16-byte aligned.                           *)

let curve25519_generic_contract = new_definition
 `curve25519_generic_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !out scalar point sb pb stackpointer returnaddress.
        aligned 16 stackpointer /\ LENGTH sb = 32 /\ LENGTH pb = 32 /\
        ALL (nonoverlapping (word_sub stackpointer (word 1216),1216))
            [(ea,el); (out,32); (scalar,32); (point,32)] /\
        ALL (nonoverlapping (out,32)) [(ea,el); (scalar,32); (point,32)]
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; scalar; point] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(scalar,32)) s = num_of_bytelist sb /\
                  read (memory :> bytes(point,32)) s = num_of_bytelist pb)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,32)) s =
                  num_of_bytelist(wg_dh sb pb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(out,32);
                         memory :> bytes(word_sub stackpointer (word 1216),
                                         1216)])`;;

(* ------------------------------------------------------------------------- *)
(* The other kernel functions that the handshake calls (noise.c). They are   *)
(* modelled sequentially: what they do to the kernel's own state (the        *)
(* random number generator, the scheduler, other tasks) is outside the       *)
(* memory of the model, as for randombytes in the contracts of the           *)
(* mlkem-native binaries, and while one of them sleeps nothing else writes   *)
(* the memory of the caller (which the locks of the handshake are for).      *)
(* Each may change only its outputs and the 4096 bytes of stack below the    *)
(* stack pointer, an assumed bound on the stack that the kernel uses for it, *)
(* which must be 16-byte aligned:                                            *)
(*                                                                           *)
(*  - wait_for_random_bytes(), waiting until the random number generator is  *)
(*    ready, changes nothing else;                                           *)
(*                                                                           *)
(*  - get_random_bytes(buf, len) writes any len bytes at buf;                *)
(*                                                                           *)
(*  - ktime_get_real_ts64(ts) writes any time to the struct timespec64 (two  *)
(*    64-bit words, the seconds and nanoseconds) at ts;                      *)
(*                                                                           *)
(*  - down_read, up_read, down_write and up_write, of a struct rw_semaphore  *)
(*    sem (rwsem_contract), may change the 40 bytes at sem.                  *)
(* ------------------------------------------------------------------------- *)

let wait_for_random_bytes_contract = new_definition
 `wait_for_random_bytes_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let get_random_bytes_contract = new_definition
 `get_random_bytes_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !buf len stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (buf,val len) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [buf; len] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(buf,val len);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let ktime_get_real_ts64_contract = new_definition
 `ktime_get_real_ts64_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !ts stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (ts,16) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ts] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(ts,16);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let rwsem_contract = new_definition
 `rwsem_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !sem stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (sem,40) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sem] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(sem,40);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

(* ------------------------------------------------------------------------- *)
(* More kernel functions, for consuming a message:                           *)
(*                                                                           *)
(*  - memcmp(a, b, n) (in assembly in the kernel, using no stack): the       *)
(*    32-bit result is negative, zero or positive as the n bytes at a are    *)
(*    less than, equal to or greater than those at b, in the lexicographic   *)
(*    order wg_bytes_lt of byte strings (the bytes as unsigned numbers);     *)
(*                                                                           *)
(*  - ktime_get_coarse_with_offset(offs) returns any time;                   *)
(*                                                                           *)
(*  - wg_peer_put(peer) of drivers/net/wireguard/peer.c, which is not in the *)
(*    image, does nothing for NULL and otherwise drops a reference to the    *)
(*    struct wg_peer (1648 bytes) at peer, which it may change. When that is *)
(*    the last reference, what it does to the other structures the peer is   *)
(*    in, and the freeing of the peer later, are outside the model.          *)
(* ------------------------------------------------------------------------- *)

let wg_bytes_lt = define
 `(wg_bytes_lt [] (l2:byte list) <=> ~(l2 = [])) /\
  (wg_bytes_lt (CONS (a:byte) l1) [] <=> F) /\
  (wg_bytes_lt (CONS a l1) (CONS b l2) <=>
     val a < val b \/ a = b /\ wg_bytes_lt l1 l2)`;;

let memcmp_contract = new_definition
 `memcmp_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !a b n l1 l2 returnaddress.
        LENGTH l1 = val n /\ LENGTH l2 = val n
        ==> ensures arm
             (\s. read PC s = f /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; b; n] s /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(a,val n)) s = num_of_bytelist l1 /\
                  read (memory :> bytes(b,val n)) s = num_of_bytelist l2)
             (\s. read PC s = returnaddress /\
                  (ival(word_zx(read X0 s):int32) < &0 <=>
                   wg_bytes_lt l1 l2) /\
                  (word_zx(read X0 s):int32 = word 0 <=> l1 = l2) /\
                  (&0 < ival(word_zx(read X0 s):int32) <=>
                   wg_bytes_lt l2 l1))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30])`;;

let ktime_get_coarse_with_offset_contract = new_definition
 `ktime_get_coarse_with_offset_contract
     (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !offs stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [offs] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let wg_peer_put_contract = new_definition
 `wg_peer_put_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    (!stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [word 0] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])) /\
    (!peer stackpointer returnaddress.
        ~(peer = word 0) /\ aligned 16 stackpointer /\
        nonoverlapping (peer,1648) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [peer] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(peer,1648);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)]))`;;

(* ------------------------------------------------------------------------- *)
(* More kernel functions, for setting up handshakes and their tables:        *)
(*                                                                           *)
(*  - __init_rwsem(sem, name, key) initializes the struct rw_semaphore (40   *)
(*    bytes) at sem; the name and the lock class key are for lockdep, which  *)
(*    is not configured;                                                     *)
(*                                                                           *)
(*  - _raw_spin_lock_bh(lock) and _raw_spin_unlock_bh(lock), of a spinlock_t *)
(*    (4 bytes) at lock (spinlock_bh_contract), may change those 4 bytes;    *)
(*    what they do to the count of disabled bottom halves of the task is     *)
(*    outside the model.                                                     *)
(* ------------------------------------------------------------------------- *)

let init_rwsem_contract = new_definition
 `init_rwsem_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !sem name key stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (sem,40) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sem; name; key] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(sem,40);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

let spinlock_bh_contract = new_definition
 `spinlock_bh_contract (f:int64) (ea:int64) (el:num) (ev:num) <=>
    !lock stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (lock,4) (ea,el) /\
        nonoverlapping (word_sub stackpointer (word 4096),4096) (ea,el)
        ==> ensures arm
             (\s. read PC s = f /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [lock] s /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(lock,4);
                         memory :> bytes(word_sub stackpointer (word 4096),
                                         4096)])`;;

(* ------------------------------------------------------------------------- *)
(* Kernel data. The AEAD code reads zeros for its padding from the zero page *)
(* at page_address(ZERO_PAGE(0)), which it computes as the address in the    *)
(* linear map (at 0xfff0000000000000 for the 52-bit virtual addresses of     *)
(* the arm64 build) of the page frame of empty_zero_page, at zp in the       *)
(* image's data: its physical address is zp - kimage_voffset, and the        *)
(* first page frame of the linear map is memstart_addr >> 12, both being     *)
(* variables in the image's data (see wireguard/wg_env.S). The callers       *)
(* require zeros at that address, as the kernel's zero page has, rather than *)
(* relating it to the copy in the image.                                     *)
(* ------------------------------------------------------------------------- *)

let wg_zero_page_va = new_definition
 `wg_zero_page_va (zp:int64) (kv:int64) (ms:int64) =
    word_add (word 0xfff0000000000000)
             (word_shl (word_sub (word_ushr (word_sub zp kv) 12)
                                 (word_ishr ms 12)) 12)`;;

(* ------------------------------------------------------------------------- *)
(* Zeroing by memset: the region is zero, from the postcondition of the      *)
(* contract for each byte, in which the address of byte i for a destination  *)
(* word_add a (word k) may have been normalized to word_add a (word(k + i))  *)
(* by the simulation.                                                        *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_OF_BYTES8 = prove
 (`!a:int64 n x s:armstate.
        (!j. j < n
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word((x DIV 2 EXP (8 * j)) MOD 256))
        ==> read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:armstate`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN ARITH_TAC);;

let MEMSET_ZERO_BYTES = prove
 (`!a n s:armstate.
        (!i. i < n
             ==> read (memory :> bytes8(word_add a (word i))) s =
                 word_zx(word 0:int64))
        ==> read (memory :> bytes(a,n)) s = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `0`; `s:armstate`]
               READ_MEMORY_BYTES_OF_BYTES8) THEN
  ASM_SIMP_TAC[DIV_0; MOD_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC WORD_REDUCE_CONV);;

let MEMSET_ZERO_BYTES_OFFSET = prove
 (`!a k n s:armstate.
        (!i. i < n
             ==> read (memory :> bytes8(word_add a (word(k + i)))) s =
                 word_zx(word 0:int64))
        ==> read (memory :> bytes(word_add a (word k),n)) s = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEMSET_ZERO_BYTES THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_SIMP_TAC[]);;

let MEMSET_ZERO_BYTES_TAC =
  FIRST_ASSUM(fun th ->
    ASSUME_TAC(try MATCH_MP MEMSET_ZERO_BYTES_OFFSET th
               with Failure _ -> MATCH_MP MEMSET_ZERO_BYTES th));;

let NUM_OF_BYTELIST_REPLICATE_0 = prove
 (`!k. num_of_bytelist(REPLICATE k (word 0:byte)) = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; num_of_bytelist; VAL_WORD_0] THEN
  ARITH_TAC);;

(* The zero facts for all the regions that memset has set to zero in the     *)
(* current state, from the postconditions of the contract.                   *)

let MEMSET_ZERO_ALL_TAC : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let ths = mapfilter (fun (_,th) ->
      if is_forall(concl th) && can (find_term ((=) s)) (concl th) then
        (try MATCH_MP MEMSET_ZERO_BYTES_OFFSET th
         with Failure _ -> MATCH_MP MEMSET_ZERO_BYTES th)
      else failwith "") asl in
    MAP_EVERY ASSUME_TAC ths);;

(* The 64-bit words at the offsets ks of the region (a,n), zero in state s,  *)
(* as separate facts, which the simulation keeps when other parts of the     *)
(* region are written.                                                       *)

let MEMSET_ZERO_WORDS64_TAC a n ks s =
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [a; mk_small_numeral n; mk_small_numeral k; s]
                 WG_READ_BYTES64_ZERO) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV WG_ADDR_CONV) THEN DISCH_TAC) ks;;

(* The GOT entry for a function g in the state s, with the address in the    *)
(* form word(pc + got_g) of the preconditions of the theorems for callees,   *)
(* from the fact with the form word_add (word pc) (word got_g) that the      *)
(* simulation of the PLT stubs uses.                                         *)

let GOT_ENTRY_TAC got s =
  let eqth = SPECL [`pc:num`; got] (INST_TYPE [`:64`,`:N`] WORD_ADD) in
  let l = list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
            [mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->
                                   (int64->byte,int64)component->
                                   (armstate,int64)component`,`memory`),
                     mk_comb(`bytes64:int64->(int64->byte,int64)component`,
                             rhs(concl eqth))); s]) in
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = l
    then ASSUME_TAC(REWRITE_RULE[GSYM eqth] th)
    else failwith "GOT_ENTRY_TAC");;

(* ------------------------------------------------------------------------- *)
(* Simulating a call. WG_PLT_TAC execth k does the four steps of the PLT     *)
(* stub after the "bl" at step k, after which the PC is the address read     *)
(* from the GOT, which must be in the form                                   *)
(* read (memory :> bytes64 (word_add (word pc) (word n))) s = f in the       *)
(* assumptions, as normalized by WG_ADRP_TAC. Then                           *)
(* WG_CALL_TAC name execth ilist (k + 5) uses the contract, which must be    *)
(* an assumption with that label, unfolded to |- !args. P ==> ensures ...,   *)
(* with the arguments ilist, to reach the state at step k + 5, where the     *)
(* call has returned, also proving the equations between the addresses that  *)
(* the contract and the simulation give. (As LIBC_PLT_TAC and LIBC_CALL_TAC  *)
(* on the mlkem-arm branch.)                                                 *)
(* ------------------------------------------------------------------------- *)

let WG_PLT_TAC execth k =
  ARM_STEPS_TAC execth [k + 1] THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC execth ((k + 2)--(k + 4));;

let VAL_WORD_NUMERAL_CONV tm =
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
      WORD_REDUCE_CONV tm
  | _ -> failwith "VAL_WORD_NUMERAL_CONV";;

let WG_CONTRACT_SIM_TAC execth contract_th =
  fun ilist0 n ->
    let sname' = "s"^string_of_int n in
    let svar = mk_var("s"^string_of_int(n-1),`:armstate`)
    and svar0 = mk_var("s",`:armstate`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    MP_TAC(SPECL ilist contract_th) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS; fst execth] THEN
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV VAL_WORD_NUMERAL_CONV) THEN
    TRY(ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REPEAT CONJ_TAC THEN
      TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
      NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    ARM_BIGSTEP_TAC execth sname' THEN
    TRY(ASM_REWRITE_TAC[C_ARGUMENTS] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN NO_TAC);;

let WG_CALL_TAC name execth ilist n =
  REMOVE_THEN name (fun th ->
    WG_CONTRACT_SIM_TAC execth th ilist n THEN LABEL_TAC name th);;

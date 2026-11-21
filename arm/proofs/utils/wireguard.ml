(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs about the AArch64 image of the WireGuard handshake   *)
(* (see arm/wireguard/README.md), loaded at an address pc that is a multiple *)
(* of 4096 and not wrapping around the end of the address space.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* Decoding all the code in the image would take several minutes, and the    *)
(* header and the data in it are not instructions, so the decoding theorems  *)
(* for the simulation are only made for the given ranges of addresses        *)
(* [lo,hi), which are those of the code being simulated. Otherwise this is   *)
(* the same as ARM_MK_EXEC_RULE. (This is the rule of the same name in       *)
(* arm/proofs/utils/mlkem_native_image.ml on the mlkem-arm branch.)          *)
(* ------------------------------------------------------------------------- *)

let ARM_MK_EXEC_RANGES_RULE =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc) l ==>
     read_int32 l = SOME (a, l') ==> decode a = SOME i ==>
     arm_decode s (word pc) i' /\
     aligned_bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC ARM_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + 4 = p ==> (pc + n) + 4 = pc + p`
  and r32,dec,n4 = `read_int32`,`decode`,`4`
  and ei,ei' = `i:armstate->armstate->bool`,`i':armstate->armstate->bool`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and ea,en,ep,epc,epc' = `a:int32`,`n:num`,`p:num`,`pc:num`,`pc':num`
  and len_tm = `LENGTH:byte list->num` in
  let rec go k th =
    if k <= 0 then [] else
    let pc,l = (rand o rand F_F I) (dest_comb (concl th)) in
    let th1 = READ_WORD_CONV (mk_comb (r32, l)) in
    let a,l' = dest_pair (rand (rhs (concl th1))) in
    let th2 = DECODE_CONV (mk_comb (dec, a)) in
    let i = rand (rhs (concl th2)) in
    let th3 = REWRITE_CONV (invert_condition :: ARM_INSTRUCTION_ALIASES) i in
    let i' = rhs (concl th3) in
    let th4,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n4)) in
      PROVE_HYP th (INST [pc,epc; a,en; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n4)),`0` in
    let pc' = rhs (concl th4) in
    let th' = itlist PROVE_HYP [th3; th4; th; th1; th2]
      (INST [i,ei; i',ei'; pc,epc; pc',epc'; l,el; a,ea; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ -> let dth,bth = CONJ_PAIR th' in (dth,pcofs)::(go (k - 1) bth) in
  fun mc_def ranges ->
    let lenth = TRANS (AP_TERM len_tm mc_def)
                      (LENGTH_CONV (mk_comb(len_tm,rhs(concl mc_def)))) in
    let dth = AP_TERM `aligned_bytes_loaded s (word pc)` mc_def in
    let th0 = EQ_MP dth (ASSUME (lhs (concl dth))) in
    let decodes = itlist (fun (lo,hi) acc ->
      go ((hi - lo) / 4) (ALIGNED_BYTES_LOADED_OFFSET_RULE lo th0) @ acc)
      ranges [] in
    let arr = Array.make (dest_small_numeral (rhs (concl lenth))) None in
    List.iter (fun (th,pcofs) ->
        arr.(dest_small_numeral pcofs) <-
          Some ((GENL [`s:armstate`; `pc:num`] o DISCH_ALL) th))
      decodes;
    lenth,arr;;

(* ------------------------------------------------------------------------- *)
(* Addresses in the image when it is at a multiple of 4096: WG_ADRP_TAC puts *)
(* the page computed by ADRP, word_and (word(pc + k)) (word 0xFFF...F000),   *)
(* in the form word_add (word pc) (word p). (As MLKEM_NATIVE_ADRP_TAC and    *)
(* its lemmas in arm/proofs/utils/mlkem_native_image.ml on the mlkem-arm     *)
(* branch.)                                                                  *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_4096_WORD_AND = prove
 (`!x:int64. aligned 4096 x <=> word_and x (word 4095) = word 0`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:int64`; `12`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 4096 < 4096`; ARITH_RULE
    `x < 4096 ==> x < 2 EXP 64`]);;

let PAGE_ADD_ALIGNED = prove
 (`!x y:int64.
        word_and x (word 4095) = word 0
        ==> word_and (word_add x y) (word 0xFFFFFFFFFFFFF000) =
            word_add x (word_and y (word 0xFFFFFFFFFFFFF000)) /\
            word_subword (word_add x y) (0,12):(12)word =
            word_subword y (0,12) /\
            word_subword (word_add x y) (4,8):(12)word =
            word_subword y (4,8)`,
  BITBLAST_TAC);;

let WG_ADRP_TAC =
  let mask = `word 0xFFFFFFFFFFFFF000:int64` in
  let is_page t =
    match t with
      Comb(Comb(Const("word_and",_),
                Comb(Const("word",_),
                     Comb(Comb(Const("+",_),Var("pc",_)),k))),m)
        -> m = mask && is_numeral k
    | _ -> false in
  W(fun (asl,w) ->
    let ath = snd(find (fun (_,th) ->
                concl th = `aligned 4096 (word pc:int64)`) asl) in
    let pth = GEN_ALL(CONJUNCT1(SPEC_ALL(MATCH_MP PAGE_ADD_ALIGNED
                (REWRITE_RULE[ALIGNED_4096_WORD_AND] ath)))) in
    let conv t =
      if is_page t then
        (LAND_CONV(REWR_CONV WORD_ADD) THENC REWR_CONV pth THENC
         RAND_CONV WORD_REDUCE_CONV) t
      else failwith "WG_ADRP_TAC" in
    let rule th =
      if can (find_term is_page) (concl th) then
        CONV_RULE(ONCE_DEPTH_CONV conv THENC
                  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
      else th in
    RULE_ASSUM_TAC rule);;

(* ------------------------------------------------------------------------- *)
(* Small values: words of numbers below the word size and their extensions.  *)
(* ------------------------------------------------------------------------- *)

let WG_VAL_WORD_SMALL = prove
 (`!n. n < 2 EXP 64 ==> val(word n:int64) = n`,
  SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

let WG_WORD_SUB_LE = prove
 (`!x y. y <= x ==> word_sub (word x) (word y):N word = word(x - y)`,
  SIMP_TAC[WORD_SUB]);;

let WG_WORD_SUB_VAL = prove
 (`!(x:int64) y. y <= val x ==> word_sub x (word y) = word(val x - y)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  ASM_SIMP_TAC[WG_WORD_SUB_LE]);;

let WG_WORD_ZX_SMALL = prove
 (`!n. n < 2 EXP 32
       ==> word_zx (word n:int32):int64 = word n /\
           word_zx (word_zx (word n:int32):int64):int32 = word n /\
           word_zx (word_zx (word n:int64):int32):int64 = word n`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* The lengths that the BLAKE2s code computes, from a buffer length b and    *)
(* input lengths.                                                            *)
(* ------------------------------------------------------------------------- *)

(* The number of bytes that fill the buffer, from the 32-bit buffer length.  *)

let WG_FILL_WORD = prove
 (`!b. b <= 64
       ==> word_zx (word_sub (word 64) (word_zx (word_zx (word b:int32):int64))
                    :int32):int64 = word(64 - b)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WG_WORD_ZX_SMALL; ARITH_RULE `b <= 64 ==> b < 2 EXP 32`] THEN
  ASM_SIMP_TAC[WG_WORD_SUB_LE] THEN
  ASM_SIMP_TAC[WG_WORD_ZX_SMALL; ARITH_RULE `b <= 64 ==> 64 - b < 2 EXP 32`]);;

(* The new buffer length, as a 32-bit sum or after zero-extensions.          *)

let WG_BUFLEN_ADD = prove
 (`!b (x:int64).
     b + val x <= 64
     ==> word_zx (word_zx (word_add
                 (word_zx (word_zx (word b:int32):int64):int32)
                 (word_zx x:int32)):int64):int32 =
         word(b + val x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `b < 2 EXP 32 /\ val(x:int64) < 2 EXP 32 /\
                b + val x < 2 EXP 32 /\ b < 2 EXP 64 /\ b + val x < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `b + val(x:int64) <= 64` THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let WG_BUFLEN_ZX = prove
 (`!r. r <= 64
       ==> word_zx (word_zx (word_zx (word r:int64):int32):int64):int32 =
           word r`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  SUBGOAL_THEN `r < 2 EXP 32 /\ r < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r <= 64` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(* The number of complete blocks compressed from the input, all but the      *)
(* last of the rest r > 64 of the input after the buffer is filled.          *)

let WG_NBLOCKS_WORD = prove
 (`!r. 64 < r /\ r + 63 < 2 EXP 64
       ==> word_sub (word_ushr (word_add (word r) (word 63)) 6) (word 1):int64 =
           word((r + 63) DIV 64 - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  SUBGOAL_THEN `word_ushr (word(r + 63):int64) 6 = word((r + 63) DIV 64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LET_TRANS `r + 63` THEN
    CONJ_TAC THENL [REWRITE_TAC[DIV_LE];
      UNDISCH_TAC `r + 63 < 2 EXP 64` THEN CONV_TAC NUM_REDUCE_CONV THEN
      ARITH_TAC];
    MATCH_MP_TAC WG_WORD_SUB_LE THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `64 < r` THEN ARITH_TAC]);;

let WG_WORD_SHL_6 = prove
 (`!k. 64 * k < 2 EXP 64 ==> word_shl (word k:int64) 6 = word(64 * k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_shl] THEN
  SUBGOAL_THEN `val(word k:int64) = k` SUBST1_TAC THENL
   [MATCH_MP_TAC WG_VAL_WORD_SMALL THEN
    UNDISCH_TAC `64 * k < 2 EXP 64` THEN ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Normalization of the values in a simulation of 32-bit code: W-register    *)
(* reads and writes, halves of 64-bit loads, and the two 32-bit views of a   *)
(* 64-bit memory word (the code copies some 32-bit arrays with 64-bit loads  *)
(* and stores).                                                              *)
(* ------------------------------------------------------------------------- *)

let WG_WORD_ZX_ZX = prove
 (`(!x:int32. word_zx (word_zx x:int64):int32 = x) /\
   (!x:int64. word_zx (word_zx x:int32):int32 = word_zx x) /\
   (!x:int32. word_zx (word_zx x:int32):int64 = word_zx x) /\
   (!x:int32. word_zx x:int32 = x) /\
   (!x:int64. word_zx x:int64 = x)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_32; DIMINDEX_64; ARITH]);;

let WG_WORD_HALVES = prove
 (`(!x:int64. word_zx x:int32 = word_subword x (0,32)) /\
   (!x:int64. word_zx (word_ushr x 32):int32 = word_subword x (32,32)) /\
   (!h l:int32. word_subword (word_join h l:int64) (0,32):int32 = l) /\
   (!h l:int32. word_subword (word_join h l:int64) (32,32):int32 = h)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* ROR (immediate) is EXTR with both sources the same register.              *)

let WG_WORD_ROR_JOIN = prove
 (`!x:int32 n.
     n < 32 ==> word_subword (word_join x x:int64) (n,32) = word_ror x n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_32] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_ROR; DIMINDEX_32;
              DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> i < MIN 32 32`;
               ARITH_RULE `n < 32 /\ i < 32 ==> n + i < 64`] THEN
  REWRITE_TAC[ARITH_RULE `i + n:num = n + i`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let WG_ROR_CONV tm =
  match tm with
    Comb(Comb(Const("word_subword",_),Comb(Comb(Const("word_join",_),x),x')),
         Comb(Comb(Const(",",_),n),k))
      when x = x' && is_numeral n && type_of x = `:int32` ->
      let th = SPECL [x;n] WG_WORD_ROR_JOIN in
      MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))
  | _ -> failwith "WG_ROR_CONV";;

let WG_WORD_XOR_0 = prove
 (`(!x:int32. word_xor x (word 0) = x) /\ (!x:int32. word_xor (word 0) x = x)`,
  REWRITE_TAC[WORD_XOR_0]);;

let WG_NORM_CONV =
  PURE_REWRITE_CONV[WG_WORD_ZX_ZX] THENC PURE_REWRITE_CONV[WG_WORD_HALVES] THENC
  DEPTH_CONV WG_ROR_CONV THENC PURE_REWRITE_CONV[WG_WORD_XOR_0] THENC
  WORD_REDUCE_CONV;;

(* Whether a value may need WG_NORM_CONV (a cheap syntactic check, so that   *)
(* the facts carried over unchanged from the previous state are skipped).    *)

let wg_needs_norm =
  let w0 = `word 0:int32` in
  let rec chk t =
    match t with
      Comb(Const("word_zx",_),_) -> true
    | Comb(Comb(Const("word_subword",_),Comb(Comb(Const("word_join",_),_),_)),_)
        -> true
    | Comb(Comb(Const("word_xor",_),a),b) when a = w0 || b = w0 -> true
    | Comb(Comb(Const("word_subword",_),Comb(Const("word",_),n)),_)
        when is_numeral n -> true
    | Comb(f,x) -> chk f || chk x
    | _ -> false in
  let int32_ty = `:int32` in
  fun t -> match t with
             Comb(Const("word_zx",_),v) when type_of v = int32_ty -> chk v
           | _ -> chk t;;

(* The 64-bit view of two 32-bit memory words and the converse.              *)

let WG_BYTES64_JOIN = prove
 (`!a s (h:int32) (l:int32).
        read (memory :> bytes32 a) s = l /\
        read (memory :> bytes32 (word_add a (word 4))) s = h
        ==> read (memory :> bytes64 a) s = word_join h l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
  ASM_REWRITE_TAC[WG_WORD_HALVES]);;

let WG_BYTES64_SPLIT = prove
 (`!a s d. read (memory :> bytes64 a) s = d
           ==> read (memory :> bytes32 a) s = word_subword d (0,32) /\
               read (memory :> bytes32 (word_add a (word 4))) s =
               word_subword d (32,32)`,
  REWRITE_TAC[GSYM(el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT))]);;

let WG_BYTES64_FROM_HALVES = prove
 (`!a s (x:int64).
        read (memory :> bytes32 a) s = word_subword x (0,32) /\
        read (memory :> bytes32 (word_add a (word 4))) s =
        word_subword x (32,32)
        ==> read (memory :> bytes64 a) s = x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WG_BYTES64_JOIN o CONJ
    (ASSUME `read (memory :> bytes32 a) s =
             word_subword (x:int64) (0,32)`)) THEN
  DISCH_THEN SUBST1_TAC THEN BITBLAST_TAC);;

(* Addresses in the form the simulator uses: base + numeral.                 *)

let WG_ADDR_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; WORD_ADD_0] THENC
  REWRITE_CONV[GSYM WORD_ADD] THENC NUM_REDUCE_CONV;;

(* A 64-bit memory fact from the facts for its two 32-bit halves.            *)

let WG_JOIN_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MATCH_MP_TAC WG_BYTES64_JOIN THEN CONV_TAC WG_ADDR_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

(* The 32-bit words of a byte array in memory, given as a list of bytes:     *)
(* read (memory :> bytes(a,n)) s = num_of_bytelist l.                        *)

let WG_NUM_OF_BYTELIST_AS_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN
  ARITH_TAC);;

let WG_READ_BYTES32_BYTELIST = prove
 (`!a:int64 (l:byte list) n k s:armstate.
        read (memory :> bytes(a,n)) s = num_of_bytelist l /\ k + 4 <= n
        ==> read (memory :> bytes32(word_add a (word k))) s =
            word(num_of_bytelist(SUB_LIST(k,4) l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_AS_WORDLIST; NUM_OF_WORDLIST_SUB_LIST;
              DIMINDEX_8] THEN
  ASM_REWRITE_TAC[GSYM WG_NUM_OF_BYTELIST_AS_WORDLIST] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  REWRITE_TAC[BYTES32_WBYTES; wbytes; READ_COMPONENT_COMPOSE; asword;
              through; read; DIMINDEX_32] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(* The bytes of a byte array as a number from i to i + k, e.g. of a region   *)
(* that memset has zeroed.                                                   *)

let WG_READ_BYTES_OF_NUM = prove
 (`!a:int64 n x k m s:armstate.
        read (memory :> bytes(a,n)) s = x /\ k + m <= n
        ==> read (memory :> bytes(word_add a (word k),m)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let WG_READ_BYTES64_ZERO = prove
 (`!a:int64 n k s:armstate.
        read (memory :> bytes(a,n)) s = 0 /\ k + 8 <= n
        ==> read (memory :> bytes64(word_add a (word k))) s = word 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `0`; `k:num`; `8`; `s:armstate`]
    WG_READ_BYTES_OF_NUM) THEN
  ASM_REWRITE_TAC[DIV_0; MOD_0] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_64; VAL_WORD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[]);;

(* The bytes of a byte array from i to i + k, and a byte array from two.     *)

let WG_NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2:byte list.
        num_of_bytelist(APPEND l1 l2) =
        num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_bytelist; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let WG_NUM_OF_BYTELIST_EQ_0 = prove
 (`!l:byte list. num_of_bytelist l = 0 <=> l = REPLICATE (LENGTH l) (word 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; LENGTH; REPLICATE; CONS_11] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  ARITH_TAC);;

let WG_READ_BYTES_SUBLIST = prove
 (`!a:int64 (l:byte list) n i k s:armstate.
        read (memory :> bytes(a,n)) s = num_of_bytelist l /\ i + k <= n
        ==> read (memory :> bytes(word_add a (word i),k)) s =
            num_of_bytelist(SUB_LIST(i,k) l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_AS_WORDLIST; NUM_OF_WORDLIST_SUB_LIST;
              DIMINDEX_8] THEN
  ASM_REWRITE_TAC[GSYM WG_NUM_OF_BYTELIST_AS_WORDLIST] THEN
  REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let WG_READ_BYTES_APPEND = prove
 (`!a:int64 (l1:byte list) l2 c s:armstate.
        read (memory :> bytes(a,LENGTH l1)) s = num_of_bytelist l1 /\
        read (memory :> bytes(word_add a (word(LENGTH l1)),c)) s =
        num_of_bytelist l2
        ==> read (memory :> bytes(a,LENGTH l1 + c)) s =
            num_of_bytelist(APPEND l1 l2)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              WG_NUM_OF_BYTELIST_APPEND] THEN
  SIMP_TAC[]);;

(* The 64-bit words of a byte array, and byte arrays of 32 and 64 bytes      *)
(* from their 64-bit words.                                                  *)

let WG_READ_BYTES_8 = prove
 (`!(x:int64) (m:int64->byte). read (bytes(x,8)) m = val(read (bytes64 x) m)`,
  REWRITE_TAC[BYTES64_WBYTES; VAL_READ_WBYTES; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WG_READ_BYTES64_BYTELIST = prove
 (`!a:int64 (l:byte list) n k s:armstate.
        read (memory :> bytes(a,n)) s = num_of_bytelist l /\ k + 8 <= n
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word(num_of_bytelist(SUB_LIST(k,8) l))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `l:byte list`; `n:num`; `k:num`; `8`; `s:armstate`]
    WG_READ_BYTES_SUBLIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; wbytes; asword;
              through; read; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WG_VAL_WORD_BYTES8 = prove
 (`!l:byte list.
     LENGTH l = 8 ==> val(word(num_of_bytelist l):int64) = num_of_bytelist l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `l:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WG_READ_BYTES_32_OF_CHUNKS = prove
 (`!a:int64 l0 l1 l2 l3 s:armstate.
     LENGTH l0 = 8 /\ LENGTH l1 = 8 /\ LENGTH l2 = 8 /\ LENGTH l3 = 8 /\
     read (memory :> bytes64 a) s = word(num_of_bytelist l0) /\
     read (memory :> bytes64 (word_add a (word 8))) s =
     word(num_of_bytelist l1) /\
     read (memory :> bytes64 (word_add a (word 16))) s =
     word(num_of_bytelist l2) /\
     read (memory :> bytes64 (word_add a (word 24))) s =
     word(num_of_bytelist l3)
     ==> read (memory :> bytes(a,32)) s =
         num_of_bytelist(APPEND l0 (APPEND l1 (APPEND l2 l3)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `32 = 8 + 8 + 8 + 8`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WG_READ_BYTES_8; GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_SIMP_TAC[WG_VAL_WORD_BYTES8; WG_NUM_OF_BYTELIST_APPEND;
               LENGTH_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* A list of 32 elements as the list of its four chunks of 8.                *)

let WG_SUB_LIST_CHUNKS32 = prove
 (`!l:A list.
     LENGTH l = 32
     ==> APPEND (SUB_LIST(0,8) l) (APPEND (SUB_LIST(8,8) l)
           (APPEND (SUB_LIST(16,8) l) (SUB_LIST(24,8) l))) = l`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP SUB_LIST_REFL
    (MATCH_MP (ARITH_RULE `n = 32 ==> n <= 32`)
              (ASSUME `LENGTH(l:A list) = 32`)))] THEN
  REWRITE_TAC[ARITH_RULE `32 = 8 + 8 + 8 + 8`; SUB_LIST_SPLIT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* A sub-list of 16 elements as its two halves.                             *)

let WG_SUB_LIST_16 = prove
 (`!(l:A list) p.
     SUB_LIST(p,16) l = APPEND (SUB_LIST(p,8) l) (SUB_LIST(p + 8,8) l)`,
  REWRITE_TAC[ARITH_RULE `16 = 8 + 8`; SUB_LIST_SPLIT]);;

(* The value of 4 bytes, and 16 bytes as four 32-bit words.                *)

let WG_VAL_WORD_BYTES4 = prove
 (`!l:byte list.
     LENGTH l = 4 ==> val(word(num_of_bytelist l):int32) = num_of_bytelist l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `l:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WG_BYTES16_SPLIT32 = prove
 (`!a:int64 s:armstate.
     read (memory :> bytes(a,16)) s =
     val(read (memory :> bytes32 a) s) +
     2 EXP 32 * val(read (memory :> bytes32 (word_add a (word 4))) s) +
     2 EXP 64 * val(read (memory :> bytes32 (word_add a (word 8))) s) +
     2 EXP 96 * val(read (memory :> bytes32 (word_add a (word 12))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `16 = 4 + 4 + 4 + 4`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BYTES32_WBYTES; VAL_READ_WBYTES; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let WG_NUM_OF_BYTELIST_SUB16 = prove
 (`!(l:byte list) k.
     k + 16 <= LENGTH l
     ==> num_of_bytelist(SUB_LIST(k,16) l) =
         num_of_bytelist(SUB_LIST(k,4) l) +
         2 EXP 32 * num_of_bytelist(SUB_LIST(k + 4,4) l) +
         2 EXP 64 * num_of_bytelist(SUB_LIST(k + 8,4) l) +
         2 EXP 96 * num_of_bytelist(SUB_LIST(k + 12,4) l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 = 4 + 4 + 4 + 4`; SUB_LIST_SPLIT;
              WG_NUM_OF_BYTELIST_APPEND; LENGTH_APPEND; LENGTH_SUB_LIST] THEN
  SUBGOAL_THEN `MIN 4 (LENGTH(l:byte list) - k) = 4 /\
                MIN 4 (LENGTH(l:byte list) - (k + 4)) = 4 /\
                MIN 4 (LENGTH(l:byte list) - ((k + 4) + 4)) = 4`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `k + 16 <= LENGTH(l:byte list)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let WG_READ_BYTES_64_OF_CHUNKS = prove
 (`!a:int64 l0 l1 l2 l3 l4 l5 l6 l7 s:armstate.
     LENGTH l0 = 8 /\ LENGTH l1 = 8 /\ LENGTH l2 = 8 /\ LENGTH l3 = 8 /\
     LENGTH l4 = 8 /\ LENGTH l5 = 8 /\ LENGTH l6 = 8 /\ LENGTH l7 = 8 /\
     read (memory :> bytes64 a) s = word(num_of_bytelist l0) /\
     read (memory :> bytes64 (word_add a (word 8))) s =
     word(num_of_bytelist l1) /\
     read (memory :> bytes64 (word_add a (word 16))) s =
     word(num_of_bytelist l2) /\
     read (memory :> bytes64 (word_add a (word 24))) s =
     word(num_of_bytelist l3) /\
     read (memory :> bytes64 (word_add a (word 32))) s =
     word(num_of_bytelist l4) /\
     read (memory :> bytes64 (word_add a (word 40))) s =
     word(num_of_bytelist l5) /\
     read (memory :> bytes64 (word_add a (word 48))) s =
     word(num_of_bytelist l6) /\
     read (memory :> bytes64 (word_add a (word 56))) s =
     word(num_of_bytelist l7)
     ==> read (memory :> bytes(a,64)) s =
         num_of_bytelist(APPEND l0 (APPEND l1 (APPEND l2 (APPEND l3
           (APPEND l4 (APPEND l5 (APPEND l6 l7)))))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `64 = 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WG_READ_BYTES_8; GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_SIMP_TAC[WG_VAL_WORD_BYTES8; WG_NUM_OF_BYTELIST_APPEND;
               LENGTH_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Single bytes and 64-bit words of a byte array given as a number.          *)

let WG_READ_BYTES64_OF_NUM = prove
 (`!a:int64 n x k s:armstate.
     read (memory :> bytes(a,n)) s = x /\ k + 8 <= n
     ==> read (memory :> bytes64(word_add a (word k))) s =
         word((x DIV 2 EXP (8 * k)) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `x:num`; `k:num`; `8`; `s:armstate`]
    WG_READ_BYTES_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 8 = 64`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; WG_READ_BYTES_8] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]);;

let WG_READ_BYTES8_OF_NUM = prove
 (`!a:int64 n x k s:armstate.
     read (memory :> bytes(a,n)) s = x /\ k < n
     ==> read (memory :> bytes8(word_add a (word k))) s =
         word((x DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `x:num`; `k:num`; `1`; `s:armstate`]
    WG_READ_BYTES_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k + 1 <= n <=> k < n`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]);;

(* Equality of the low bits of two numbers, split at e bits.                 *)

let WG_MOD_EXP_ADD_EQ = prove
 (`!x y e d.
     x MOD 2 EXP (e + d) = y MOD 2 EXP (e + d) <=>
     x MOD 2 EXP e = y MOD 2 EXP e /\
     (x DIV 2 EXP e) MOD 2 EXP d = (y DIV 2 EXP e) MOD 2 EXP d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP_ADD] THEN EQ_TAC THENL
   [MESON_TAC[MOD_MOD; DIV_MOD];
    SIMP_TAC[MOD_MULT_MOD]]);;

let WG_WORD_EQ_MOD64 = prove
 (`!p q. (word(p MOD 2 EXP 64):int64) = word(q MOD 2 EXP 64) <=>
         p MOD 2 EXP 64 = q MOD 2 EXP 64`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_MOD_REFL]);;

let WG_WORD_EQ_MOD256 = prove
 (`!p q. (word(p MOD 256):byte) = word(q MOD 256) <=> p MOD 256 = q MOD 256`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* The flag conditions of comparisons with small numbers, as the simulation  *)
(* gives them: for equality (b.eq, b.ne) and unsigned lower or same (b.ls).  *)

let WG_VAL_WORD_SUB_EQ_0 = prove
 (`!p q. p < 2 EXP 64 /\ q < 2 EXP 64
         ==> (val(word_sub (word p) (word q):int64) = 0 <=> p = q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

let WG_VAL_LS_COND = prove
 (`!x:int64 n. n < 2 EXP 64
     ==> (~(n <= val x /\ ~(val(word_sub x (word n)) = 0)) <=> val x <= n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ARITH_TAC);;

(* The four 64-bit words of the 32-byte array at a in state s, from the fact *)
(* read (memory :> bytes(a,32)) s = num_of_bytelist l, and the converse for  *)
(* a goal of that form (with LENGTH l = 32 among the assumptions).           *)

let WG_BYTES32_WORDS_TAC a s (asl,w as gl) =
  let l = vsubst [a,`a:int64`; s,`s:armstate`]
                 `read (memory :> bytes(a,32)) s` in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhand(concl th) = l)
                    asl) in
  MAP_EVERY (fun j ->
    MP_TAC(MATCH_MP WG_READ_BYTES64_BYTELIST
            (CONJ th (EQT_ELIM(NUM_REDUCE_CONV
              (mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` (mk_small_numeral(8*j)) `8`)
                 `32`))))) THEN
    CONV_TAC(LAND_CONV(LAND_CONV WG_ADDR_CONV)) THEN DISCH_TAC) (0--3) gl;;

let WG_BYTES32_OF_WORDS_TAC ths (asl,w as gl) =
  let c = lhand(lhand w) and s = rand(lhand w) and l = rand(rand w) in
  let a = fst(dest_pair(rand(rand c))) in
  (MP_TAC(ISPECL ([a] @
                  map (fun j ->
                    mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,
                                    mk_pair(mk_small_numeral(8 * j),`8`)),l))
                      (0--3) @ [s])
                 WG_READ_BYTES_32_OF_CHUNKS) THEN
   CONV_TAC(LAND_CONV WG_ADDR_CONV) THEN
   ASM_REWRITE_TAC(LENGTH_SUB_LIST :: ths) THEN CONV_TAC NUM_REDUCE_CONV THEN
   ASM_SIMP_TAC(WG_SUB_LIST_CHUNKS32 :: ths)) gl;;

(* The nonoverlapping assumptions rewritten with ths, for example with the   *)
(* length of a region in a case where it is known.                           *)

let WG_NONOVERLAP_RULE_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    try if fst(dest_const(fst(strip_comb(concl th)))) = "nonoverlapping"
        then REWRITE_RULE ths th else th
    with Failure _ -> th);;

(* ------------------------------------------------------------------------- *)
(* Byte arrays as functions: wg_bytes f n is the number of the n bytes       *)
(* f 0, ..., f(n-1) (little-endian), as read (bytes(a,n)) is of those in     *)
(* memory. Sub-arrays and concatenations are then about the functions        *)
(* shifted, \i. f(k + i), which the specs give as \i. EL i l or with         *)
(* list_of_seq.                                                              *)
(* ------------------------------------------------------------------------- *)

let wg_bytes = define
 `wg_bytes (f:num->byte) 0 = 0 /\
  wg_bytes f (SUC n) = wg_bytes f n + 2 EXP (8 * n) * val(f n)`;;

let WG_BYTES_ADD = prove
 (`!(f:num->byte) m n.
     wg_bytes f (m + n) =
     wg_bytes f m + 2 EXP (8 * m) * wg_bytes (\i. f(m + i)) n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[wg_bytes; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; ADD_ASSOC] THEN ARITH_TAC);;

let WG_BYTES_BOUND = prove
 (`!(f:num->byte) n. wg_bytes f n < 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[wg_bytes; MULT_CLAUSES; EXP; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`; EXP_ADD] THEN
  MP_TAC(ISPEC `(f:num->byte) n` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * n) * val((f:num->byte) n) <= 2 EXP (8 * n) * 255`
  MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let WG_NUM_OF_BYTELIST_SEQ = prove
 (`!(f:num->byte) n. num_of_bytelist(list_of_seq f n) = wg_bytes f n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; wg_bytes; num_of_bytelist;
                  WG_NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  ARITH_TAC);;

let WG_NUM_OF_BYTELIST_EL = prove
 (`!l:byte list. num_of_bytelist l = wg_bytes (\i. EL i l) (LENGTH l)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_SEQ]);;

let WG_BYTES_OF_LIST = prove
 (`!l:byte list n.
     LENGTH l = n ==> num_of_bytelist l = wg_bytes (\i. EL i l) n`,
  MESON_TAC[WG_NUM_OF_BYTELIST_EL]);;

let WG_BYTES_EQ = prove
 (`!(f:num->byte) g n.
     (!i. i < n ==> f i = g i) ==> wg_bytes f n = wg_bytes g n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[wg_bytes] THEN
  DISCH_TAC THEN BINOP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`];
    AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ARITH_TAC]);;

(* wg_bytes f n for a numeral n as the explicit sum.                         *)

let rec WG_BYTES_CONV tm =
  match tm with
    Comb(Comb(Const("wg_bytes",_),f),n) when is_numeral n ->
      if dest_small_numeral n = 0 then REWR_CONV (CONJUNCT1 wg_bytes) tm else
      (RAND_CONV num_CONV THENC REWR_CONV (CONJUNCT2 wg_bytes) THENC
       LAND_CONV WG_BYTES_CONV) tm
  | _ -> failwith "WG_BYTES_CONV";;

(* Sub-arrays and concatenations in memory.                                  *)

let WG_DIV_ADD_MUL = prove
 (`!x p y. x < p ==> (x + p * y) DIV p = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `x:num` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WG_MOD_ADD_MUL = prove
 (`!x p y. x < p ==> (x + p * y) MOD p = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `y:num` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WG_READ_BYTES_FUN_SUB = prove
 (`!a:int64 f n k m s:armstate.
     read (memory :> bytes(a,n)) s = wg_bytes f n /\ k + m <= n
     ==> read (memory :> bytes(word_add a (word k),m)) s =
         wg_bytes (\i. f(k + i)) m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `wg_bytes f n`; `k:num`; `m:num`;
                `s:armstate`] WG_READ_BYTES_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`f:num->byte`; `k:num`; `m + (n - k - m):num`]
                WG_BYTES_ADD) THEN
  ASM_SIMP_TAC[ARITH_RULE `k + m <= n:num ==> k + (m + (n - k - m)) = n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[WG_DIV_ADD_MUL; WG_BYTES_BOUND] THEN
  REWRITE_TAC[WG_BYTES_ADD] THEN SIMP_TAC[WG_MOD_ADD_MUL; WG_BYTES_BOUND]);;

let WG_READ_BYTES_FUN_COMBINE = prove
 (`!a:int64 f k m s:armstate.
     read (memory :> bytes(a,k)) s = wg_bytes f k /\
     read (memory :> bytes(word_add a (word k),m)) s =
     wg_bytes (\i. f(k + i)) m
     ==> read (memory :> bytes(a,k + m)) s = wg_bytes f (k + m)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; WG_BYTES_ADD] THEN
  SIMP_TAC[]);;

(* Memory words and byte arrays of their size, both ways.                    *)

let WG_READ_WORDS_BYTES =
  let tac n =
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES64_WBYTES; BYTES32_WBYTES;
                BYTES16_WBYTES; BYTES8_WBYTES] THEN
    REPEAT GEN_TAC THEN
    W(fun (asl,w) ->
      let t = lhand w in
      let x = rand(rand(rator t)) and m = rand t in
      MP_TAC(ISPECL [x; m] (INST_TYPE [mk_finty(Num.num_of_int n),`:N`]
                                      VAL_READ_WBYTES))) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL] in
  end_itlist CONJ
   [prove(`!x:int64 s:armstate.
      read (memory :> bytes64 x) s = word(read (memory :> bytes(x,8)) s)`,
      tac 64);
    prove(`!x:int64 s:armstate.
      read (memory :> bytes32 x) s = word(read (memory :> bytes(x,4)) s)`,
      tac 32);
    prove(`!x:int64 s:armstate.
      read (memory :> bytes16 x) s = word(read (memory :> bytes(x,2)) s)`,
      tac 16);
    prove(`!x:int64 s:armstate.
      read (memory :> bytes8 x) s = word(read (memory :> bytes(x,1)) s)`,
      tac 8)];;

let WG_READ_BYTES_OF_WORDS = prove
 (`(!x:int64 v s:armstate.
      read (memory :> bytes64 x) s = word v /\ v < 2 EXP 64
      ==> read (memory :> bytes(x,8)) s = v) /\
   (!x:int64 v s:armstate.
      read (memory :> bytes32 x) s = word v /\ v < 2 EXP 32
      ==> read (memory :> bytes(x,4)) s = v) /\
   (!x:int64 v s:armstate.
      read (memory :> bytes16 x) s = word v /\ v < 2 EXP 16
      ==> read (memory :> bytes(x,2)) s = v) /\
   (!x:int64 v s:armstate.
      read (memory :> bytes8 x) s = word v /\ v < 2 EXP 8
      ==> read (memory :> bytes(x,1)) s = v)`,
  REWRITE_TAC[WG_READ_WORDS_BYTES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; DIMINDEX_32; DIMINDEX_16;
              DIMINDEX_8] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH lhand READ_BYTES_BOUND
                            (lhand(lhand(lhand w))))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT]);;

(* Facts about arrays in memory as functions: the sub-array at offset k, of *)
(* size m, of the array of size m0 at a of the function f, with its address  *)
(* and function in normalized forms; and the memory word (of 8, 4, 2 or 1    *)
(* bytes) of an array of that size at x.                                     *)

let WG_BYTES_FUN_SUB_TAC a f m0 s k m =
  MP_TAC(SPECL [a; f; m0; k; m; s] WG_READ_BYTES_FUN_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV WG_ADDR_CONV THENC
                     ONCE_DEPTH_CONV BETA_CONV THENC
                     REWRITE_CONV[ADD_CLAUSES; ETA_AX; GSYM ADD_ASSOC])) THEN
  DISCH_TAC;;

let WG_WORD_FACT_AT_TAC x s m =
  let ty = match m with 8 -> `:64` | 4 -> `:32` | 2 -> `:16` | _ -> `:8` in
  let l = vsubst [x,`x:int64`; s,`s:armstate`; mk_small_numeral m,`m:num`]
            `read (memory :> bytes(x,m)) s` in
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) = l then
    ASSUME_TAC(REWRITE_RULE[GSYM WG_READ_WORDS_BYTES]
                 (AP_TERM (mk_const("word",[ty,`:N`])) th))
    else failwith "WG_WORD_FACT_AT_TAC");;

(* Xors of byte arrays of word size, and of zero-extended halfwords and      *)
(* bytes as 32-bit registers hold them.                                      *)

let WG_XOR_BYTES_FUN = prove
 (`(!f g:num->byte.
     word_xor (word(wg_bytes f 8):int64) (word(wg_bytes g 8)) =
     word(wg_bytes (\i. word_xor (f i) (g i)) 8)) /\
   (!f g:num->byte.
     word_xor (word(wg_bytes f 4):int32) (word(wg_bytes g 4)) =
     word(wg_bytes (\i. word_xor (f i) (g i)) 4)) /\
   (!f g:num->byte.
     word_xor (word(wg_bytes f 2):int16) (word(wg_bytes g 2)) =
     word(wg_bytes (\i. word_xor (f i) (g i)) 2)) /\
   (!f g:num->byte.
     word_xor (word(wg_bytes f 1):byte) (word(wg_bytes g 1)) =
     word(wg_bytes (\i. word_xor (f i) (g i)) 1))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC(DEPTH_CONV WG_BYTES_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let WG_XOR_ZX = prove
 (`(!x y:int16. word_zx (word_xor (word_zx x:int32) (word_zx y)) =
                word_xor x y) /\
   (!x y:byte. word_zx (word_xor (word_zx x:int32) (word_zx y)) =
               word_xor x y)`,
  CONJ_TAC THEN BITBLAST_TAC);;

(* The condition of b.ls after a 32-bit cmp with a small number.             *)

let WG_VAL_LS_COND32 = prove
 (`!x:int32 k. k < 2 EXP 32
     ==> (~(&(val x) - &k:int = &(val(word_sub x (word k))) /\
          ~(val(word_sub x (word k)) = 0)) <=> val x <= k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THENL
   [ASM_ARITH_TAC;
    MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LE; GSYM INT_OF_NUM_LT] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; ARITH_RULE
      `~(k <= x) /\ k < 2 EXP 32 ==> k <= 2 EXP 32 + x`] THEN
    INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Frames and assumptions for callees with optional outputs: an empty region *)
(* of memory followed by another one in a MAYCHANGE list adds nothing to it  *)
(* (WG_MAYCHANGE_DROP_EMPTY_CONV removes such regions, for theorems about    *)
(* callees with a NULL destination and zero length), and the implications    *)
(* in the postconditions of such callees resolved with ths.                  *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_MEMORY_BYTES_0_SEQ = prove
 (`!a:int64 (d:(int64->byte,V)component).
     ASSIGNS (memory :> bytes(a,0)) ,, ASSIGNS (memory :> d) =
     ASSIGNS ((memory:(armstate,int64->byte)component) :> d)`,
  REPEAT GEN_TAC THEN
  MP_TAC(VALID_COMPONENT_CONV `valid_component memory`) THEN
  REWRITE_TAC[valid_component] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; seq; ASSIGNS_THM; WRITE_COMPONENT_COMPOSE;
              READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 bytes))] THEN
  REWRITE_TAC[UNWIND_THM1] THEN ASM_REWRITE_TAC[]);;

let WG_MAYCHANGE_DROP_EMPTY_CONV tm =
  match tm with
    Comb(Const("MAYCHANGE",_) as mc,l) ->
      let els = dest_list l in
      let empty c =
        match c with
          Comb(Comb(Const(":>",_),Const("memory",_)),Comb(Const("bytes",_),p))
            -> (try snd(dest_pair p) = `0` with Failure _ -> false)
        | _ -> false in
      let els' = filter (not o empty) els in
      if length els' = length els || els' = [] ||
         empty(last els) then failwith "WG_MAYCHANGE_DROP_EMPTY_CONV" else
      let tm' = mk_comb(mc,mk_list(els',type_of(hd els))) in
      prove(mk_eq(tm,tm'),
            REWRITE_TAC[MAYCHANGE; SEQ_ID; ASSIGNS_MEMORY_BYTES_0_SEQ])
  | _ -> failwith "WG_MAYCHANGE_DROP_EMPTY_CONV";;

let WG_IMP_ASSUM_REWRITE_TAC ths =
  RULE_ASSUM_TAC(fun th ->
    if is_imp(concl th) then REWRITE_RULE ths th else th);;

(* After a step: normalize the values of the facts about the current state,  *)
(* and add the 32-bit halves of each 64-bit memory word that has no fact     *)
(* for them yet.                                                             *)

(* The components that the normalization and abbreviation leave alone (as a  *)
(* constant: quotations inside the per-assumption functions would be parsed  *)
(* at every call).                                                           *)

let wg_flag_components = [`NF`; `ZF`; `CF`; `VF`; `PC`; `events`];;

(* The address a + 4 in the form of WG_ADDR_CONV, for each address a of a    *)
(* 64-bit memory fact (memoized).                                            *)

let wg_addr_plus4 =
  let tbl = (Hashtbl.create 1024 : (term,term) Hashtbl.t)
  and add_tm = `word_add:int64->int64->int64` and four_tm = `word 4:int64` in
  fun a ->
    try Hashtbl.find tbl a with Not_found ->
    let a4 = rand(concl(WG_ADDR_CONV(mk_comb(mk_comb(add_tm,a),four_tm)))) in
    Hashtbl.add tbl a a4; a4;;

let WG_STATE_NORM_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let isread c t = match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) ->
          s' = s && c c'
      | _ -> false in
    let nonflag c = not(mem c wg_flag_components) in
    let tac1 (asl,w as gl) =
      let targets = filter (fun (_,th) ->
        isread nonflag (concl th) && wg_needs_norm(rand(concl th))) asl in
      MAP_EVERY (fun (_,th0) ->
        FIRST_X_ASSUM(fun th ->
          if concl th = concl th0
          then ASSUME_TAC(CONV_RULE(RAND_CONV WG_NORM_CONV) th)
          else failwith "")) targets gl in
    let memaddr sz t = match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
          Comb(Comb(Const(":>",_),Const("memory",_)),Comb(Const(sz',_),a))),
          s')),_) when s' = s && sz' = sz -> a
      | _ -> failwith "memaddr" in
    let tac2 (asl,w as gl) =
      let have = Hashtbl.create 256 in
      List.iter (fun (_,th) ->
        try Hashtbl.replace have (memaddr "bytes32" (concl th)) ()
        with Failure _ -> ()) asl;
      let b64 = filter (fun (_,th) ->
        try let a = memaddr "bytes64" (concl th) in
            not(Hashtbl.mem have a && Hashtbl.mem have (wg_addr_plus4 a))
        with Failure _ -> false) asl in
      let news = List.concat (map (fun (_,th) ->
        let th1,th2 = CONJ_PAIR(MATCH_MP WG_BYTES64_SPLIT th) in
        let th2 = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV
                    WG_ADDR_CONV)))) th2 in
        let norm = CONV_RULE(RAND_CONV WG_NORM_CONV) in
        filter (fun th -> not(Hashtbl.mem have (memaddr "bytes32" (concl th))))
               [norm th1; norm th2]) b64) in
      MAP_EVERY ASSUME_TAC news gl in
    (tac1 THEN tac2) gl;;

(* A conditional PC after a branch on a comparison of two addresses with the *)
(* same base: reduce the difference to a numeral and decide the condition.   *)

let WG_WORD_SUB_ADD_ADD = WORD_RULE
 `!a x y:int64. word_sub (word_add a x) (word_add a y) = word_sub x y`;;

let WG_PC_COND_TAC : tactic =
  let conv = RATOR_CONV(RATOR_CONV(RAND_CONV
               (PURE_REWRITE_CONV[WG_WORD_SUB_ADD_ADD] THENC
                WORD_REDUCE_CONV THENC NUM_REDUCE_CONV))) THENC
             REWRITE_CONV[] in
  fun (asl,w as gl) ->
    let s = rand w in
    let pcfact (_,th) = match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),v)
          -> s' = s && is_cond v
      | _ -> false in
    if exists pcfact asl then
      FIRST_X_ASSUM(fun th -> if pcfact ("",th)
                              then ASSUME_TAC(CONV_RULE(RAND_CONV conv) th)
                              else failwith "") gl
    else ALL_TAC gl;;

(* Rewrite the PC fact of the current state with the given theorems, e.g. to *)
(* decide a conditional branch from facts about the inputs.                  *)

let WG_PC_REWRITE_TAC ths : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let pcfact th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),v)
        -> s' = s
    | _ -> false in
  FIRST_X_ASSUM(fun th -> if pcfact th
                          then ASSUME_TAC(REWRITE_RULE ths th)
                          else failwith "") gl;;

let WG_STEP_TAC execth n =
  ARM_STEPS_TAC execth [n] THEN WG_PC_COND_TAC THEN WG_STATE_NORM_TAC;;

let WG_STEPS_TAC execth ns = MAP_EVERY (WG_STEP_TAC execth) ns;;

(* ------------------------------------------------------------------------- *)
(* Abbreviation of the 32-bit data values after each step, so that the       *)
(* terms stay small in long straight-line code: a register holding           *)
(* word_zx e or a 32-bit memory word holding e, for a compound e:int32, is   *)
(* given a fresh variable c<n> with the assumption e = c<n> (as ABBREV_TAC   *)
(* does). Pointers and flags are left alone.                                 *)
(* ------------------------------------------------------------------------- *)

let wg_abbrev_counter = ref 0;;

(* The abbreviation equations are kept as wg_abbrev(e = c<n>), so that the   *)
(* simulator and rewriting with the assumptions do not use them.             *)

let wg_abbrev = new_definition `wg_abbrev (p:bool) <=> p`;;

let WG_ABBREV_TAC : tactic =
  let int32_ty = `:int32` in
  let simple e =
    is_var e || (try let f,args = strip_comb e in
                     match f with
                       Const("word",_) -> is_numeral(hd args)
                     | Const("word_subword",_) ->
                         is_var(hd args) || is_comb(hd args) &&
                         is_var(rator(hd args))
                     | _ -> is_var f
                 with Failure _ -> false) in
  let value_of s th =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
        when s' = s && not(mem c wg_flag_components) ->
        (match v with
           Comb(Const("word_zx",_),e) when type_of e = int32_ty -> e
         | _ when type_of v = int32_ty -> v
         | _ -> failwith "")
    | _ -> failwith "" in
  fun (asl,w as gl) ->
    let s = rand w in
    let cands = setify(filter (fun e -> not(simple e))
                         (mapfilter (value_of s o snd) asl)) in
    let one e (asl,w as gl) =
      incr wg_abbrev_counter;
      let c = mk_var("c" ^ string_of_int !wg_abbrev_counter,int32_ty) in
      let eq = mk_eq(e,c) in
      let exth = EXISTS (mk_exists(c,eq),e) (REFL e) in
      let users = filter (fun (_,th) ->
        try value_of s th = e with Failure _ -> false) asl in
      CHOOSE_THEN (fun eqth ->
        ASSUME_TAC(EQ_MP (SYM(SPEC eq wg_abbrev)) eqth) THEN
        MAP_EVERY (fun (_,th0) ->
          FIRST_X_ASSUM(fun th ->
            if concl th = concl th0
            then ASSUME_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV
                   (fun t -> if t = e then eqth else failwith ""))) th)
            else failwith "")) users) exth gl in
    MAP_EVERY one cands gl;;

let WG_ASTEP_TAC execth n =
  ARM_STEPS_TAC execth [n] THEN WG_PC_COND_TAC THEN WG_STATE_NORM_TAC THEN
  WG_ABBREV_TAC;;

let WG_ASTEPS_TAC execth ns = MAP_EVERY (WG_ASTEP_TAC execth) ns;;

(* Steps (as WG_ASTEP_TAC) until the PC is the given value, at most n steps. *)
(* The states are s0, s1, ... as in ARM_STEPS_TAC.                           *)

let wg_at_pc target (asl,w) =
  let s = rand w in
  exists (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),v)
        -> s' = s && v = target
    | _ -> false) asl;;

let wg_state_num (asl,w) =
  let s = rand w in
  try int_of_string(String.sub (fst(dest_var s)) 1
        (String.length(fst(dest_var s)) - 1)) with Failure _ -> 0;;

let WG_RUN_TO_TAC execth target n =
  let rec run k gl =
    if wg_at_pc target gl then ALL_TAC gl
    else if k > n then failwith "WG_RUN_TO_TAC: too many steps" else
    (WG_ASTEP_TAC execth (wg_state_num gl + 1) THEN run (k + 1)) gl in
  run 1;;

(* ------------------------------------------------------------------------- *)
(* Matching terms with the abbreviations c<n> of a simulation: canonical     *)
(* forms modulo AC of word_add and word_xor find the abbreviation for a term *)
(* (gcc reassociates both), and expanding both down to given stop variables  *)
(* and normalizing modulo AC proves them equal.                              *)
(* ------------------------------------------------------------------------- *)

let WG_WORD_XOR_AC = prove
 (`word_xor x y:N word = word_xor y x /\
   word_xor (word_xor x y) z:N word = word_xor x (word_xor y z) /\
   word_xor x (word_xor y z):N word = word_xor y (word_xor x z)`,
  MESON_TAC[WORD_XOR_SYM; WORD_XOR_ASSOC]);;

let WG_ACNORM_CONV = REWRITE_CONV[WORD_ADD_AC; WG_WORD_XOR_AC];;

(* The abbreviations of the goal: c |-> |- e = c.                            *)

let wg_defs_of (asl:(string*thm) list) =
  let tbl = Hashtbl.create 4096 in
  List.iter (fun (_,th) -> match concl th with
      Comb(Const("wg_abbrev",_),(Comb(Comb(Const("=",_),e),c) as p))
        when is_var c -> Hashtbl.replace tbl c (EQ_MP (SPEC p wg_abbrev) th)
    | _ -> ()) asl;
  tbl;;

(* |- t = t' expanding the abbreviations in t, except those in stops.        *)

let WG_EXPAND_CONV defs stops =
  let memo = Hashtbl.create 1024 in
  let rec conv t =
    try Hashtbl.find memo t with Not_found ->
    let th =
      match t with
        Var(_,_) when Hashtbl.mem defs t && not(mem t stops) ->
          let eqth = SYM(Hashtbl.find defs t) in
          TRANS eqth (conv(rhs(concl eqth)))
      | Comb(f,x) -> MK_COMB(conv f,conv x)
      | _ -> REFL t in
    Hashtbl.add memo t th; th in
  conv;;

(* Canonical forms modulo AC of word_add and word_xor, through all the       *)
(* abbreviations, as integers (hash-consed).                                 *)

type wgcanon =
    Wg_atom of term
  | Wg_sum of int list
  | Wg_xor of int list
  | Wg_ror of int * int
  | Wg_op of term * int list;;

let wg_canon_maker defs =
  let ids = Hashtbl.create 8192 and memo = Hashtbl.create 8192 in
  let id c = try Hashtbl.find ids c with Not_found ->
    let n = Hashtbl.length ids in Hashtbl.add ids c n; n in
  let rec canon t =
    try Hashtbl.find memo t with Not_found ->
    let r =
      match t with
        Comb(Comb(Const("word_add",_),_),_) ->
          id(Wg_sum(List.sort compare (flat "word_add" t)))
      | Comb(Comb(Const("word_xor",_),_),_) ->
          id(Wg_xor(List.sort compare (flat "word_xor" t)))
      | Comb(Comb(Const("word_ror",_),x),n) when is_numeral n ->
          id(Wg_ror(canon x,dest_small_numeral n))
      | Var(_,_) when Hashtbl.mem defs t ->
          canon(lhand(concl(Hashtbl.find defs t)))
      | _ -> id(Wg_atom t) in
    Hashtbl.add memo t r; r
  and flat op t =
    match t with
      Comb(Comb(Const(op',_),a),b) when op' = op -> flat op a @ flat op b
    | Var(_,_) when Hashtbl.mem defs t ->
        let e = lhand(concl(Hashtbl.find defs t)) in
        (match e with
           Comb(Comb(Const(op',_),_),_) when op' = op -> flat op e
         | _ -> [canon t])
    | _ -> [canon t] in
  canon;;

(* A map from canonical forms to the first abbreviation with that form.      *)

let wg_canon_index defs canon =
  let vars = Hashtbl.fold (fun c _ acc -> c::acc) defs [] in
  let num v = int_of_string(String.sub (fst(dest_var v)) 1
                                       (String.length(fst(dest_var v)) - 1)) in
  let vars = sort (fun a b -> num a < num b) vars in
  let idx = Hashtbl.create 8192 in
  List.iter (fun c -> let k = canon c in
                      if not(Hashtbl.mem idx k) then Hashtbl.add idx k c) vars;
  idx;;

(* |- e = c for the abbreviation c with the canonical form of e, proved by   *)
(* expanding both sides down to the stops and normalizing modulo AC.         *)

let WG_IDENTIFY defs canon idx stops e =
  let c = try Hashtbl.find idx (canon e)
          with Not_found -> failwith "WG_IDENTIFY: no abbreviation" in
  let exp = WG_EXPAND_CONV defs stops in
  let th1 = CONV_RULE(RAND_CONV WG_ACNORM_CONV) (exp e)
  and th2 = CONV_RULE(RAND_CONV WG_ACNORM_CONV) (exp c) in
  if aconv (rand(concl th1)) (rand(concl th2)) then TRANS th1 (SYM th2)
  else (print_term (rand(concl th1)); print_newline();
        print_term (rand(concl th2)); print_newline();
        failwith "WG_IDENTIFY: different normal forms");;

(* |- e1 = e2 by expanding all the abbreviations in both and normalizing     *)
(* modulo AC (for terms of small depth only).                                *)

let WG_EQ defs e1 e2 =
  let exp = WG_EXPAND_CONV defs [] in
  let th1 = CONV_RULE(RAND_CONV WG_ACNORM_CONV) (exp e1)
  and th2 = CONV_RULE(RAND_CONV WG_ACNORM_CONV) (exp e2) in
  if aconv (rand(concl th1)) (rand(concl th2)) then TRANS th1 (SYM th2)
  else failwith "WG_EQ";;

(* A goal read c s = e from an assumption read c s = v, with e = v by WG_EQ. *)

let WG_ASM_EQ_TAC defs (asl,w as gl) =
  let l,e = dest_eq w in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l) asl) in
  let eq = WG_EQ defs e (rhs(concl th)) in
  (CONV_TAC(RAND_CONV(K eq)) THEN ACCEPT_TAC th) gl;;

(* ------------------------------------------------------------------------- *)
(* A 32-bit length zero-extended and less a constant, the equality of byte   *)
(* lists of the same length by their numbers, the two halves of 16 bytes,    *)
(* 32 bytes as their first byte, 30 more and the last, and single bytes at   *)
(* the same offset from different bases.                                     *)
(* ------------------------------------------------------------------------- *)

let WG_VAL_ZX32 = prove
 (`!x:int32. val(word_zx x:int64) = val x`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

let WG_LEN32_SUB = prove
 (`!len:int32 k.
     k <= val len
     ==> word_sub ((word_zx:int32->int64) len) (word k) = word(val len - k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(word_zx:int32->int64) len`; `k:num`] WG_WORD_SUB_VAL) THEN
  ASM_REWRITE_TAC[WG_VAL_ZX32]);;

let WG_NUM_OF_BYTELIST_EQ = prove
 (`!l1 l2:byte list.
     LENGTH l1 = LENGTH l2
     ==> (num_of_bytelist l1 = num_of_bytelist l2 <=> l1 = l2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_AS_WORDLIST] THEN
  ONCE_REWRITE_TAC[MESON[] `(a <=> l1 = l2) <=> (a <=> (l1:byte list) = l2)`]
  THEN REWRITE_TAC[ISPECL [`l1:byte list`; `l2:byte list`]
                    LISTS_NUM_OF_WORDLIST_EQ] THEN
  ASM_REWRITE_TAC[]);;

let WG_SUB_LIST_HALVES_16 = prove
 (`!l:byte list.
     LENGTH l = 16 ==> APPEND (SUB_LIST(0,8) l) (SUB_LIST(8,8) l) = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `8`; `8`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[SUB_LIST_LENGTH]);;

let WG_BYTES32_CONS = prove
 (`!a:int64 b0 rmid b31 s.
     read (memory :> bytes8 a) s = b0 /\
     read (memory :> bytes(word_add a (word 1),30)) s = rmid /\
     read (memory :> bytes8 (word_add a (word 31))) s = b31
     ==> read (memory :> bytes(a,32)) s =
         num_of_bytelist(CONS b0 (APPEND (bytelist_of_num 30 rmid) [b31]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rmid < 256 EXP 30` ASSUME_TAC THENL
   [EXPAND_TAC "rmid" THEN
    MATCH_MP_TAC(ARITH_RULE `x < 2 EXP (8 * 30) ==> x < 256 EXP 30`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  REWRITE_TAC[num_of_bytelist; WG_NUM_OF_BYTELIST_APPEND;
              LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `32 = 1 + 30 + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WG_NONOVERLAPPING_BYTE_OFFSET = prove
 (`!a b:int64 k.
     ~(a = b)
     ==> nonoverlapping (word_add a (word k),1) (word_add b (word k),1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo; CONG;
              ARITH_RULE `i < 1 <=> i = 0`; DIMINDEX_64] THEN
  REWRITE_TAC[UNWIND_THM2; ADD_CLAUSES; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  SIMP_TAC[MOD_LT; REWRITE_RULE[DIMINDEX_64]
                     (INST_TYPE [`:64`,`:N`] VAL_BOUND)] THEN
  REWRITE_TAC[VAL_EQ] THEN
  REWRITE_TAC[WORD_RULE `word_add (a:int64) c = word_add b c <=> a = b`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The n bytes at a in state s (such as those that get_random_bytes gives)   *)
(* named as a byte list v, with its length; and a goal                       *)
(* read (memory :> bytes(a,8 * k)) s = 0 from the facts that its k 64-bit    *)
(* words are zero.                                                           *)
(* ------------------------------------------------------------------------- *)

let WG_READ_BYTES_BYTELIST_OF_NUM = prove
 (`!a:int64 n s:armstate.
     read (memory :> bytes(a,n)) s =
     num_of_bytelist(bytelist_of_num n (read (memory :> bytes(a,n)) s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `256 EXP n = 2 EXP (8 * n)` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]]);;

let WG_NAME_BYTES_TAC a n v s =
  let rd = vsubst [a,`a:int64`; n,`n:num`; s,`s:armstate`]
             `read (memory :> bytes(a,n)) s` in
  ASSUME_TAC(ISPECL [a; n; s] WG_READ_BYTES_BYTELIST_OF_NUM) THEN
  ABBREV_TAC (mk_eq(v,mk_comb(mk_comb(`bytelist_of_num`,n),rd))) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,v),n)) ASSUME_TAC
  THENL
   [EXPAND_TAC (fst(dest_var v)) THEN REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    ALL_TAC];;

let WG_ZERO_BYTES_TAC : tactic =
  W(fun (asl,w) ->
    let n = dest_small_numeral(snd(dest_pair(rand(rand(lhand(lhand w)))))) in
    let ws = mk_list(replicate `word 0:int64` (n / 8),`:int64`) in
    SUBGOAL_THEN (mk_eq(lhand w,mk_comb(`num_of_wordlist:int64 list->num`,ws)))
    SUBST1_TAC THENL
     [CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
      REWRITE_TAC[GSYM BYTES64_WBYTES; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                  GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[num_of_wordlist; VAL_WORD_0] THEN ARITH_TAC]);;

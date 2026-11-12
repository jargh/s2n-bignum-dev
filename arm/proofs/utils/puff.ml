(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of libpuff.so, zlib's contrib/puff/puff.c     *)
(* compiled by gcc 12 with -O2 (see arm/puff/README.md), as one image, and   *)
(* tools for the proofs about the functions in it. All the theorems about    *)
(* the image assume that it is loaded at an address pc that is a multiple of *)
(* 4096, as the dynamic loader does, and that the image and its writable     *)
(* data do not wrap around the end of the address space. The functions are   *)
(* then at pc + <address>, where <address> is that in the binary.            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/rfc1951_theory.ml";;

let puff_gcc12_O2_mc = define_from_elf
  "puff_gcc12_O2_mc" "arm/puff/puff_gcc12_O2.o";;

let LENGTH_PUFF_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` puff_gcc12_O2_mc);;

(* ------------------------------------------------------------------------- *)
(* Decoding all the code in the image would take longer than needed, and the *)
(* header and the data in it are not instructions, so the decoding theorems  *)
(* for the simulation are only made for the given ranges of addresses        *)
(* [lo,hi), which are those of the code being simulated. Otherwise this is   *)
(* the same as ARM_MK_EXEC_RULE. This and the tools for ADRP below are those *)
(* for the image of mlkem-native in the mlkem branch.                        *)
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
(* The code: the stubs of the procedure linkage table for _setjmp and        *)
(* longjmp, and the functions construct, bits, decode, codes and puff.       *)
(* ------------------------------------------------------------------------- *)

let PUFF_EXEC = ARM_MK_EXEC_RANGES_RULE puff_gcc12_O2_mc
  [0x570,0x580; 0x5a0,0x5b0; 0x6a0,0x1098];;

(* ------------------------------------------------------------------------- *)
(* Addresses in the image when it is at a multiple of 4096.                  *)
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

(*** The page and the offset within it computed by ADRP and ADD or LDR ***)

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

(*** The range check for ADRP holds within an image without wraparound ***)

let ADRP_WITHIN_BOUNDS_ALIGNED = prove
 (`!pc a b.
        aligned 4096 (word pc:int64) /\
        pc + a < 2 EXP 64 /\ pc + b < 2 EXP 64 /\
        a < 2 EXP 32 /\ b < 2 EXP 32
        ==> adrp_within_bounds (word (pc + b)) (word (pc + a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pc MOD 18446744073709551616 = pc` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[divides]) THEN
  REWRITE_TAC[adrp_within_bounds] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[word_uge; word_ult; word_ule; relational2; VAL_WORD_SUB_CASES;
              VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE `(4096 * x + b) DIV 4096 = x + b DIV 4096`] THEN
  MP_TAC(SPECL [`4096`; `a:num`] DIV_MUL_LE) THEN
  MP_TAC(SPECL [`4096`; `b:num`] DIV_MUL_LE) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(x + a DIV 4096) MOD 18014398509481984 = x + a DIV 4096 /\
                (x + b DIV 4096) MOD 18014398509481984 = x + b DIV 4096`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;


let PUFF_ADRP_TAC =
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
      else failwith "PUFF_ADRP_TAC" in
    let rule th =
      if can (find_term is_page) (concl th) then
        CONV_RULE(ONCE_DEPTH_CONV conv THENC
                  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
      else th in
    RULE_ASSUM_TAC rule);;

(* ------------------------------------------------------------------------- *)
(* Byte arrays, as lists of bytes l with                                     *)
(* read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l.                 *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_BYTELIST_BYTE = prove
 (`!l i. i < LENGTH l
         ==> (num_of_bytelist l DIV 2 EXP (8 * i)) MOD 256 = val(EL i l:byte)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[num_of_bytelist; EL; HD; TL; LT_SUC] THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT];
    DISCH_TAC THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `i < LENGTH(t:byte list)`))]) THEN
    REWRITE_TAC[MULT_CLAUSES; EXP_ADD; GSYM DIV_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]]);;

let READ_MEMORY_BYTES8_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k < m
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES8_BYTELIST = prove
 (`!a:int64 l i s:armstate.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        i < LENGTH l
        ==> read (memory :> bytes8(word_add a (word i))) s = EL i l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES8_OF_NUM o
    C CONJ (ASSUME `i < LENGTH(l:byte list)`)) THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[NUM_OF_BYTELIST_BYTE; WORD_VAL]);;

(* Writing a byte after the end of an array extends it.                      *)

let NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2:byte list.
        num_of_bytelist(APPEND l1 l2) =
        num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_bytelist; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let VAL_READ_MEMORY_BYTES8 = prove
 (`!x s:armstate.
        read (bytes(x,1)) (read memory s) = val(read (memory :> bytes8 x) s)`,
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_BYTELIST_SNOC = prove
 (`!a:int64 (l:byte list) b s:armstate.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        read (memory :> bytes8(word_add a (word(LENGTH l)))) s = b
        ==> read (memory :> bytes(a,LENGTH l + 1)) s =
            num_of_bytelist(APPEND l [b])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[VAL_READ_MEMORY_BYTES8; NUM_OF_BYTELIST_APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[num_of_bytelist] THEN ARITH_TAC);;

let READ_MEMORY_BYTES16_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int16 list) n j s:armstate.
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int16 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `16 * j = 8 * (2 * j)`;
              ARITH_RULE `65536 = 2 EXP (8 * 2)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arrays of 16-bit words, as lists l of words with read (memory :>          *)
(* bytes(a,2 * LENGTH l)) s = num_of_wordlist l. To update an element at a   *)
(* symbolic index j, the array is split around it, the element is written,   *)
(* and the array is put back together from the parts, whose facts the        *)
(* simulation keeps since they do not overlap the element.                   *)
(* ------------------------------------------------------------------------- *)

let EL_SUB_LIST = prove
 (`!(l:A list) m n i.
        i < n /\ m + n <= LENGTH l ==> EL i (SUB_LIST(m,n) l) = EL (m + i) l`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH] THEN
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT; SUB_LIST_CLAUSES] THENL
   [INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `n:num`; `i:num`]) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[ADD_CLAUSES; EL; TL] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `SUC n`; `i:num`]) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

let SUB_LIST_EQ_EL = prove
 (`!(l:A list) l' m n.
        LENGTH l' = LENGTH l /\ m + n <= LENGTH l /\
        (!i. m <= i /\ i < m + n ==> EL i l' = EL i l)
        ==> SUB_LIST(m,n) l' = SUB_LIST(m,n) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_SUB_LIST] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_SPLIT3 = prove
 (`!(l:(N word)list) j.
        j < LENGTH l
        ==> num_of_wordlist l =
            num_of_wordlist(SUB_LIST(0,j) l) +
            2 EXP (dimindex(:N) * j) *
            (val(EL j l) +
             2 EXP dimindex(:N) *
             num_of_wordlist(SUB_LIST(j + 1,LENGTH l - (j + 1)) l))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = LENGTH(l:(N word)list) - (j + 1)` THEN
  SUBGOAL_THEN `SUB_LIST(0,j + 1 + r) l:(N word)list = l` MP_TAC THENL
   [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_ARITH_TAC;
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th])] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; NUM_OF_WORDLIST_APPEND; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_LIST_1; NUM_OF_WORDLIST_SING] THEN
  ASM_SIMP_TAC[ARITH_RULE `j < l ==> MIN j (l - 0) = j`;
               ARITH_RULE `j < l ==> MIN 1 (l - j) = 1`] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_ASSOC]);;

let NUM_OF_WORDLIST_LIST_OF_SEQ_0 = prove
 (`!n. num_of_wordlist(list_of_seq (\j. word 0:N word) n) = 0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; num_of_wordlist; NUM_OF_WORDLIST_APPEND;
                  NUM_OF_WORDLIST_SING; VAL_WORD_0] THEN
  ARITH_TAC);;

let VAL_READ_MEMORY_BYTES16 = prove
 (`!x s:armstate.
        read (bytes(x,2)) (read memory s) = val(read (memory :> bytes16 x) s)`,
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV);;

let VAL_READ_MEMORY_BYTES64 = prove
 (`!x s:armstate.
        read (bytes(x,8)) (read memory s) = val(read (memory :> bytes64 x) s)`,
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_WORDLIST16_SPLIT = prove
 (`!a:int64 (l:int16 list) j s:armstate.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l /\
        j < LENGTH l
        ==> read (memory :> bytes(a,2 * j)) s =
            num_of_wordlist(SUB_LIST(0,j) l) /\
            read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l /\
            read (memory :> bytes(word_add a (word(2 * j + 2)),
                                  2 * (LENGTH l - (j + 1)))) s =
            num_of_wordlist(SUB_LIST(j + 1,LENGTH l - (j + 1)) l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; DIMINDEX_16] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE;
                ARITH_RULE `16 * j = 8 * (2 * j)`; READ_BYTES_MOD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC READ_MEMORY_BYTES16_NUM_OF_WORDLIST THEN
    EXISTS_TAC `LENGTH(l:int16 list)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_16] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE;
                ARITH_RULE `16 * (j + 1) = 8 * (2 * j + 2)`] THEN
    REWRITE_TAC[READ_BYTES_DIV] THEN
    REWRITE_TAC[ARITH_RULE `16 * n = 8 * (2 * n)`; READ_BYTES_MOD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC]);;

let READ_MEMORY_WORDLIST16_UPDATE = prove
 (`!a:int64 (l:int16 list) l' j s:armstate.
        read (memory :> bytes(a,2 * j)) s =
        num_of_wordlist(SUB_LIST(0,j) l) /\
        read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l' /\
        read (memory :> bytes(word_add a (word(2 * j + 2)),
                              2 * (LENGTH l - (j + 1)))) s =
        num_of_wordlist(SUB_LIST(j + 1,LENGTH l - (j + 1)) l) /\
        j < LENGTH l /\ LENGTH l' = LENGTH l /\
        (!i. i < LENGTH l /\ ~(i = j) ==> EL i l' = EL i l)
        ==> read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l':int16 list`; `j:num`] NUM_OF_WORDLIST_SPLIT3) THEN
  ASM_REWRITE_TAC[DIMINDEX_16] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `SUB_LIST(0,j) l':int16 list = SUB_LIST(0,j) l /\
    SUB_LIST(j + 1,LENGTH l - (j + 1)) l' =
    SUB_LIST(j + 1,LENGTH l - (j + 1)) l`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUB_LIST_EQ_EL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN TRY(REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 * LENGTH(l:int16 list) = 2 * j + 2 + 2 * (LENGTH l - (j + 1))`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; VAL_READ_MEMORY_BYTES16] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * j = 16 * j`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let READ_MEMORY_WORDLIST16_ELEMENTS = prove
 (`!(l:int16 list) a s:armstate.
        (!j. j < LENGTH l
             ==> read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l)
        ==> read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; num_of_wordlist; MULT_CLAUSES; CONJUNCT1 LT] THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 + 2 * n`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[VAL_READ_MEMORY_BYTES16; DIMINDEX_16] THEN
  BINOP_TAC THENL
   [AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LT_0; MULT_CLAUSES; WORD_ADD_0; EL; HD];
    CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN
    ASM_REWRITE_TAC[LT_SUC; EL; TL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ARITH_TAC]);;

let READ_MEMORY_BYTES32_ZERO = prove
 (`!a s:armstate.
        read (memory :> bytes64 a) s = word 0 /\
        read (memory :> bytes64(word_add a (word 8))) s = word 0 /\
        read (memory :> bytes64(word_add a (word 16))) s = word 0 /\
        read (memory :> bytes64(word_add a (word 24))) s = word 0
        ==> read (memory :> bytes(a,32)) s = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `32 = 8 + 8 + 8 + 8`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; VAL_READ_MEMORY_BYTES64] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC);;

let WORDLIST16_FROM_MEMORY = prove
 (`!a n s:armstate. ?l:int16 list.
        LENGTH l = n /\ read (memory :> bytes(a,2 * n)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `wordlist_from_memory(a,n) s:int16 list` THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `2 * n`;
                 `wordlist_from_memory(a,n) s:int16 list`; `s:armstate`]
                WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16] THEN ANTS_TAC THENL [ARITH_TAC; MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The tables of the base lengths and distances and their extra bits, of     *)
(* 16-bit words in the read-only data at 0x10b0, 0x10f0, 0x1130 and 0x1170.  *)
(* ------------------------------------------------------------------------- *)

let PUFF_TABLE_BYTES = prove
 (`num_of_bytelist(SUB_LIST(4272,58) puff_gcc12_O2_mc) =
   num_of_wordlist(MAP (word:num->int16) deflate_length_base) /\
   num_of_bytelist(SUB_LIST(4336,58) puff_gcc12_O2_mc) =
   num_of_wordlist(MAP (word:num->int16) deflate_length_extra) /\
   num_of_bytelist(SUB_LIST(4400,60) puff_gcc12_O2_mc) =
   num_of_wordlist(MAP (word:num->int16) deflate_dist_base) /\
   num_of_bytelist(SUB_LIST(4464,60) puff_gcc12_O2_mc) =
   num_of_wordlist(MAP (word:num->int16) deflate_dist_extra)`,
  REWRITE_TAC[puff_gcc12_O2_mc; deflate_length_base; deflate_length_extra;
              deflate_dist_base; deflate_dist_extra] THEN
  CONV_TAC(ONCE_DEPTH_CONV SUB_LIST_CONV) THEN
  REWRITE_TAC[MAP; num_of_bytelist; num_of_wordlist; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let PUFF_TABLES_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) puff_gcc12_O2_mc
          ==> read (memory :> bytes(word_add (word pc) (word 4272),58)) s =
              num_of_wordlist(MAP (word:num->int16) deflate_length_base) /\
              read (memory :> bytes(word_add (word pc) (word 4336),58)) s =
              num_of_wordlist(MAP (word:num->int16) deflate_length_extra) /\
              read (memory :> bytes(word_add (word pc) (word 4400),60)) s =
              num_of_wordlist(MAP (word:num->int16) deflate_dist_base) /\
              read (memory :> bytes(word_add (word pc) (word 4464),60)) s =
              num_of_wordlist(MAP (word:num->int16) deflate_dist_extra)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_bytes_loaded] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM PUFF_TABLE_BYTES] THEN
  MAP_EVERY (fun (m,n) ->
    MP_TAC(ISPECL [`s:armstate`; `word pc:int64`; `puff_gcc12_O2_mc`;
                   mk_small_numeral m; mk_small_numeral n]
                  BYTES_LOADED_SUB_LIST))
   [4272,58; 4336,58; 4400,60; 4464,60] THEN
  ASM_REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_SUB_LIST;
                  LENGTH_PUFF_GCC12_O2_MC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let WORD_ADD_ASSOC_NUM = WORD_RULE
 `word_add (word_add (x:int64) (word a)) (word b) = word_add x (word(a + b))`;;

(*** The element idx of the table tbl, of n words at pc + off, in state s, ***)
(*** as the fact read (memory :> bytes16(word_add (word pc)                ***)
(*** (word(off + 2 * idx)))) s = word(EL idx tbl), the form of the address ***)
(*** that the simulation gives                                             ***)

let TABLE_ELEMENT_TAC off n tbl idx s =
  let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,`word pc:int64`),
                  mk_comb(`word:num->int64`,mk_small_numeral off)) in
  let lth = ASSUME(list_mk_comb
    (`aligned_bytes_loaded:armstate->int64->byte list->bool`,
     [s; `word pc:int64`; `puff_gcc12_O2_mc`])) in
  let tth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
              (MATCH_MP PUFF_TABLES_LOADED lth) in
  MP_TAC(ISPECL [a; mk_comb(`MAP (word:num->int16)`,tbl); mk_small_numeral n;
                 idx; s] READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[tth; LENGTH_MAP; DEFLATE_TABLE_BOUNDS] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word:num->int16`; idx; tbl] EL_MAP) THEN
  REWRITE_TAC[DEFLATE_TABLE_BOUNDS] THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN DISCH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Reasoning about the 32-bit operations on small numbers that the compiled  *)
(* code uses, and about the flags set when they are compared. These are as   *)
(* in the mlkem branch (arm/proofs/utils/mlkem_native.ml and the proof for   *)
(* rej_uniform).                                                             *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_ZX_32_64 = prove
 (`!x:int32. word_zx(word_zx x:int64) = x`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH]);;

let WORD_ZX_64_32_SMALL = prove
 (`!n. n < 4294967296 ==> word_zx(word n:int64):int32 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_64] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let WORD_CMP_32_FLAGS = prove
 (`!x y. x < 4294967296 /\ y < 4294967296
         ==> ((&(val(word x:int32)) - &(val(word y:int32)):int =
               &(val(word_sub (word x) (word y):int32)) <=> y <= x) /\
              (&(val(word x:int32)) - &y:int =
               &(val(word_sub (word x) (word y):int32)) <=> y <= x) /\
              (val(word_sub (word x) (word y):int32) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:int32) = x /\ val(word y:int32) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

let WORD_CMP_32_SFLAGS = prove
 (`!x y. x < 2147483648 /\ y < 2147483648
         ==> (ival(word_sub (word x) (word y):int32) < &0 <=> x < y) /\
             (ival(word x:int32) - &y =
              ival(word_sub (word x) (word y):int32)) /\
             (ival(word x:int32) - ival(word y:int32) =
              ival(word_sub (word x) (word y):int32))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word x:int32) = &x /\ ival(word y:int32) = &y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word_sub (word x) (word y):int32) = &x - &y`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word x) (word y):int32 =
                           iword(&x - &y)`] THEN
    MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC;
    ASM_REWRITE_TAC[INT_LT_SUB_RADD; INT_ADD_LID; INT_OF_NUM_LT] THEN
    INT_ARITH_TAC]);;

let WORD_CMP_32_SUB_SFLAGS = prove
 (`!a b c. a < 2 EXP 30 /\ b < 2 EXP 30 /\ c < 2 EXP 30
           ==> (ival(word_sub (word_sub (word a) (word b)) (word c):int32) <
                &0 <=> a < b + c) /\
               (ival(word_sub (word a) (word b):int32) - ival(word c:int32) =
                ival(word_sub (word_sub (word a) (word b)) (word c):int32)) /\
               (val(word_sub (word_sub (word a) (word b)) (word c):int32) =
                0 <=> a = b + c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ival(word_sub (word a) (word b):int32) = &a - &b /\
    ival(word c:int32) = &c /\
    ival(word_sub (word_sub (word a) (word b)) (word c):int32) =
    &a - &b - &c`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word x) (word y):int32 = iword(&x - &y)`;
                WORD_RULE `word_sub (iword x) (iword y):int32 = iword(x - y)`;
                WORD_IWORD] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC(NUM_REDUCE_CONV THENC
      INT_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT]) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `x - y - z:int < &0 <=> x < y + z`;
              INT_ARITH `x - y - z:int = &0 <=> x = y + z`;
              INT_ARITH `x - y - z:int = x - y - z`;
              INT_OF_NUM_ADD; INT_OF_NUM_LT; INT_OF_NUM_EQ]);;

let WORD_CMP_64_FLAGS = prove
 (`!x y. x < 18446744073709551616 /\ y < 18446744073709551616
         ==> ((&(val(word x:int64)) - &(val(word y:int64)):int =
               &(val(word_sub (word x) (word y):int64)) <=> y <= x) /\
              (val(word_sub (word x) (word y):int64) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word y:int64) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

let IVAL_WORD_SUB_NEG = prove
 (`!a b. a < b /\ b < 2 EXP 31
         ==> ival(word_sub (word a) (word b):int32) < &0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word a) (word b):int32 = iword(&a - &b)`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT]) THEN
  ANTS_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN INT_ARITH_TAC]);;

(*** Replace 32-bit views of small numbers in assumptions and goal ***)

let W32_SMALL_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (can (term_match [] `word_zx(word n:int64):int32`))
      (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_64_32_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                             REWRITE_TAC[th])]) tms);;

(*** The PC in the current state ***)

let current_pc (asl,w) =
  let s = rand w in
  let th = snd(find (fun (_,th) -> try let l,_ = dest_eq(concl th) in
                                       l = mk_comb(`read PC`,s)
                                   with Failure _ -> false) asl) in
  rhs(concl th);;

(*** Decide a condition by arithmetic, keeping it as an assumption. An     ***)
(*** equation is only added if it, or its symmetric form, is not already   ***)
(*** an assumption, so that rewriting with the assumptions cannot loop.    ***)

let DECIDE_PROP_TAC c =
  let rule th th' = if aconv (concl th') (concl th) then th'
                    else REWRITE_RULE[EQT_INTRO th] th' in
  let keep th (asl,w as gl) =
    let c = concl th in
    if is_eq c &&
       exists (fun (_,a) -> aconv (concl a) c ||
                            aconv (concl a) (mk_eq(rhs c,lhs c))) asl
    then ALL_TAC gl else ASSUME_TAC th gl in
  (SUBGOAL_THEN c
    (fun th -> RULE_ASSUM_TAC(rule th) THEN keep th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

(*** Express the flags in terms of the numbers compared and decide them ***)

let CMP_FLAGS_TAC pat th =
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y] th) THEN
          ANTS_TAC THENL
           [CONJ_TAC THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])) tms);;

let DECIDE_FLAGS_TAC =
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`;`NF`;`VF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(DECIDE_PROP_TAC p)) ps);;

let CMP3_FLAGS_TAC pat th =
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand(lhand t)) and y = rand(rand(lhand t))
      and z = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y;z] th) THEN
          ANTS_TAC THENL
           [REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])) tms);;

let W32_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64]) THEN
  CMP3_FLAGS_TAC `word_sub (word_sub (word x) (word y)) (word z):int32`
    (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) WORD_CMP_32_SUB_SFLAGS) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_SFLAGS THEN
  DECIDE_FLAGS_TAC;;

let PTR_DECIDE_FLAGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`]) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int64` WORD_CMP_64_FLAGS THEN
  DECIDE_FLAGS_TAC;;

(*** Decide the conditions of values conditional on the flags ***)

let DECIDE_IFS_TAC =
  W(fun (asl,w) ->
    let s = rand w in
    let conds = setify(List.concat(mapfilter (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `PC`) ->
            map (lhand o rator) (find_terms is_cond t)
      | _ -> failwith "") asl)) in
    MAP_EVERY (fun c -> TRY(DECIDE_PROP_TAC c)) conds);;

(* ------------------------------------------------------------------------- *)
(* Words formed from small numbers. The simulation gives the values of       *)
(* registers and memory as words built by zero and sign extension, shifts,   *)
(* masks and so on from words of numbers, which are normalized here to a     *)
(* word of a number by conditional rewriting, the conditions (that the       *)
(* numbers are small enough) being proved by arithmetic from the             *)
(* assumptions.                                                              *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_WORD_SMALL = prove
 (`!n. n < 2 EXP dimindex(:M) /\ n < 2 EXP dimindex(:N)
       ==> word_zx(word n:M word):N word = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[VAL_WORD; MOD_LT]);;

let WORD_ZX_BYTE = prove
 (`!x:byte. word_zx x:N word = word(val x)`,
  REWRITE_TAC[word_zx]);;

let WORD_SUB_WORD_SMALL = prove
 (`!a b. b <= a ==> word_sub (word a) (word b):N word = word(a - b)`,
  SIMP_TAC[WORD_SUB]);;

let WORD_JSHL_WORD_SMALL = prove
 (`!a k. k < dimindex(:N)
         ==> word_jshl (word a:N word) (word k) = word(2 EXP k * a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jshl; WORD_SHL_WORD] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `k < 2 EXP dimindex(:N)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[LT_POW2_REFL; LT_IMP_LE];
    ASM_SIMP_TAC[VAL_WORD; MOD_LT]]);;

let WORD_ISHR_WORD_SMALL = prove
 (`!a k. a < 2 EXP (dimindex(:N) - 1)
         ==> word_ishr (word a:N word) k = word(a DIV 2 EXP k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  SUBGOAL_THEN `ival(word a:N word) = &a` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN MATCH_MP_TAC IVAL_IWORD THEN
    ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN INT_ARITH_TAC;
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_DIV; GSYM WORD_IWORD]]);;

let WORD_JSHR_WORD_SMALL = prove
 (`!a k. a < 2 EXP (dimindex(:N) - 1) /\ k < dimindex(:N)
         ==> word_jshr (word a:N word) (word k) = word(a DIV 2 EXP k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[word_jshr; WORD_ISHR_WORD_SMALL] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `k < 2 EXP dimindex(:N)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[LT_POW2_REFL; LT_IMP_LE];
    ASM_SIMP_TAC[VAL_WORD; MOD_LT]]);;

let WORD_AND_MASK_SMALL = prove
 (`!a k. a < 2 EXP dimindex(:N)
         ==> word_and (word(2 EXP k - 1)) (word a):N word =
             word(a MOD 2 EXP k) /\
             word_and (word a) (word(2 EXP k - 1)):N word =
             word(a MOD 2 EXP k)`,
  SIMP_TAC[WORD_AND_MASK_WORD; VAL_WORD; MOD_LT]);;

let WORD_OR_DISJOINT_SMALL = prove
 (`!a b k. a < 2 EXP k
           ==> word_or (word a) (word(2 EXP k * b)):N word =
               word(a + 2 EXP k * b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < k` THENL
   [SUBGOAL_THEN `(2 EXP k * b) DIV 2 EXP i = 2 EXP (k - i) * b`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `2 EXP k = 2 EXP i * 2 EXP (k - i)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[GSYM MULT_ASSOC] THEN
        SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]];
      REWRITE_TAC[ODD_MULT; ODD_EXP; ARITH] THEN ASM_ARITH_TAC];
    SUBGOAL_THEN `a DIV 2 EXP i = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP k` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ODD]]]);;

let WORD_SUBWORD_WORD_SMALL = prove
 (`!a n. a < 2 EXP n /\ a < 2 EXP dimindex(:M)
         ==> word_subword (word a:M word) (0,n):N word = word a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; EXP; DIV_1] THEN
  ASM_SIMP_TAC[VAL_WORD; MOD_LT]);;

let WORD_SXFROM_WORD_SMALL = prove
 (`!a n. a < 2 EXP n ==> word_sxfrom n (word a:N word) = word a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SXFROM; BIT_WORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i <= n` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i <= n ==> MIN n i = i`] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(i <= n) ==> MIN n i = n`]] THEN
  SUBGOAL_THEN `a DIV 2 EXP n = 0 /\ a DIV 2 EXP i = 0`
   (fun th -> REWRITE_TAC[th; ODD]) THEN
  CONJ_TAC THEN MATCH_MP_TAC DIV_LT THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LTE_TRANS `2 EXP n` THEN ASM_REWRITE_TAC[LE_EXP] THEN
  ASM_ARITH_TAC);;

let WORD_ADD_WORD = prove
 (`!a b. word_add (word a) (word b):N word = word(a + b)`,
  REWRITE_TAC[WORD_ADD]);;

let WORD_OR_0_SMALL = prove
 (`!x:N word. word_or x (word 0) = x /\ word_or (word 0) x = x`,
  REWRITE_TAC[WORD_OR_0]);;

let WORD_OR_BIT_DOUBLE = prove
 (`!a b. a < 2
         ==> word_or (word a) (word(2 * b)):N word = word(a + 2 * b) /\
             word_or (word(2 * b)) (word a):N word = word(a + 2 * b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num`; `b:num`; `1`] WORD_OR_DISJOINT_SMALL) THEN
  ASM_REWRITE_TAC[EXP_1; ARITH] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[WORD_OR_SYM] THEN
  ASM_REWRITE_TAC[]);;

let WORD_AND_1_SMALL = prove
 (`!a. a < 2 EXP dimindex(:N)
       ==> word_and (word a) (word 1):N word = word(a MOD 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num`; `1`] WORD_AND_MASK_SMALL) THEN
  ASM_REWRITE_TAC[EXP_1; ARITH] THEN SIMP_TAC[]);;

let WORD_SX_WORD_SMALL = prove
 (`!a. a < 2 EXP (dimindex(:M) - 1) /\ a < 2 EXP dimindex(:N)
       ==> word_sx(word a:M word):N word = word a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  SUBGOAL_THEN `ival(word a:M word) = &a` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN MATCH_MP_TAC IVAL_IWORD THEN
    ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM WORD_IWORD]]);;

let WORD_AND_SUB_7 = prove
 (`!a b. word_and (word_sub (word a) (word b)) (word 7):int32 =
         word((a + 7 * b) MOD 8)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_sub (word a) (word b):int32 = word(a + 4294967295 * b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word x) (word y):int32 = iword(&x - &y)`;
                WORD_IWORD; IWORD_EQ; DIMINDEX_32] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    REWRITE_TAC[int_congruent] THEN EXISTS_TAC `-- &b:int` THEN
    CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [ARITH_RULE `7 = 2 EXP 3 - 1`] THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_32] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 32 = 2 EXP 3 * 536870912`; MOD_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE
   `a + 4294967295 * b = (a + 7 * b) + 8 * (536870911 * b)`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let WORD_COND_SMALL = prove
 (`!c a b. (if c then word a else word b):N word = word(if c then a else b)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let VAL_WORD_SMALL = prove
 (`!n. n < 2 EXP dimindex(:N) ==> val(word n:N word) = n`,
  SIMP_TAC[VAL_WORD; MOD_LT]);;

let SMALL_WORD_RULES =
  let split th =
    let th' = SPEC_ALL th in
    if is_imp(concl th') then
      let c = lhand(concl th') in
      map (GEN_ALL o DISCH c) (CONJUNCTS(UNDISCH th'))
    else map GEN_ALL (CONJUNCTS th') in
  List.concat (map split
   [WORD_ZX_ZX_32_64; WORD_ZX_BYTE; WORD_SHL_WORD; WORD_ADD_WORD;
    ARITH_RULE `!x. x * 1 = x /\ 1 * x = x`;
    WORD_ZX_WORD_SMALL; WORD_SUB_WORD_SMALL; WORD_JSHL_WORD_SMALL;
    WORD_ISHR_WORD_SMALL; WORD_JSHR_WORD_SMALL; WORD_AND_MASK_SMALL;
    WORD_OR_DISJOINT_SMALL; WORD_SUBWORD_WORD_SMALL;
    WORD_SXFROM_WORD_SMALL; VAL_WORD_SMALL; WORD_OR_0_SMALL;
    WORD_OR_BIT_DOUBLE; WORD_AND_1_SMALL; WORD_SX_WORD_SMALL;
    WORD_AND_SUB_7; WORD_COND_SMALL]);;

(*** The index in a load with an SXTW register offset of a small number ***)

let VAL_SXTW_SMALL = prove
 (`!n. n < 2 EXP 31 ==> val(word_sx(word_zx(word n:int64):int32):int64) = n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_zx(word n:int64):int32 = word n` SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_ZX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_sx(word n:int32):int64 = word n` SUBST1_TAC THENL
   [MATCH_MP_TAC WORD_SX_WORD_SMALL THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC VAL_WORD_SMALL THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* Normalize words built from small numbers, proving the conditions by       *)
(* arithmetic from the assumptions. Terms involving pc, the address of the   *)
(* image, are left alone, so that addresses keep the form of the code.       *)

let SMALL_WORD_CONV asl =
  let pc_tm = `pc:num` in
  let prove_cond c =
    let th1 = (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) c in
    let c' = rhs(concl th1) in
    let th2 =
      if c' = `T` then TRUTH else
      let divs = find_terms (is_binary "DIV") c'
      and mods = find_terms (is_binary "MOD") c' in
      let vals =
        find_terms (fun t -> is_comb t && rator t = `val:byte->num`) c' in
      let facts = map (fun t -> SPECL [lhand t; rand t] DIV_LE) divs @
                  map (fun t -> SPECL [lhand t; rand t] MOD_LE) mods @
                  map (fun t -> CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC
                                           NUM_REDUCE_CONV)
                                (ISPEC (rand t) VAL_BOUND)) vals in
      TAC_PROOF((asl,c'),MAP_EVERY MP_TAC facts THEN SIMPLE_ARITH_TAC) in
    EQ_MP (SYM th1) th2 in
  let rule_conv th =
    let th' = SPEC_ALL th in
    if is_imp(concl th') then
      let pm = PART_MATCH (lhs o rand) th in
      fun tm -> if free_in pc_tm tm then failwith "SMALL_WORD_CONV" else
                let ith = pm tm in MP ith (prove_cond(lhand(concl ith)))
    else
      let pm = PART_MATCH lhs th in
      fun tm -> if free_in pc_tm tm then failwith "SMALL_WORD_CONV" else
                pm tm in
  let conv = FIRST_CONV (map rule_conv SMALL_WORD_RULES) in
  TOP_DEPTH_CONV conv THENC NUM_REDUCE_CONV;;

(* Normalize the values in the assumptions about the current state, except   *)
(* the flags, whose comparisons are recognized by CMP_FLAGS_TAC, and the PC, *)
(* which may depend on them.                                                 *)

let SMALL_WORD_TAC:tactic =
  let flags = [`NF`; `ZF`; `CF`; `VF`; `PC`] in
  fun (asl,w as gl) ->
    let s = try rand w with Failure _ -> w in
    let conv = SMALL_WORD_CONV asl in
    let rule th =
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),_)
          when s' = s && not(mem c flags) -> CONV_RULE (RAND_CONV conv) th
      | _ -> th in
    RULE_ASSUM_TAC rule gl;;

(* ------------------------------------------------------------------------- *)
(* The position in the stream as puff keeps it (see puff_input below).       *)
(* ------------------------------------------------------------------------- *)

let PUFF_POS_BOUNDS = prove
 (`!p. p <= 8 * ((p + 7) DIV 8) /\ 8 * ((p + 7) DIV 8) <= p + 7`,
  GEN_TAC THEN MP_TAC(SPECL [`p + 7`; `8`] DIVISION) THEN ARITH_TAC);;

let PUFF_POS_DIV = prove
 (`!q i. q <= 8 * i /\ 8 * i <= q + 7 ==> (q + 7) DIV 8 = i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(q + 7) - 8 * i` THEN ASM_ARITH_TAC);;

let PUFF_POS_NONZERO = prove
 (`!q. ~(8 * ((q + 7) DIV 8) - q = 0) ==> q DIV 8 + 1 = (q + 7) DIV 8`,
  GEN_TAC THEN MP_TAC(SPECL [`q:num`; `8`] DIVISION) THEN
  MP_TAC(SPECL [`q + 7`; `8`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let PUFF_POS_ZERO = prove
 (`!q. 8 * ((q + 7) DIV 8) - q = 0
       ==> q DIV 8 = (q + 7) DIV 8 /\ 8 * (q DIV 8) = q`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `q:num` PUFF_POS_BOUNDS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * ((q + 7) DIV 8) = q` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q DIV 8 = (q + 7) DIV 8` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ];
    ASM_REWRITE_TAC[]]);;

let PUFF_POS_SUCC = prove
 (`!q. ((q + 1) + 7) DIV 8 = q DIV 8 + 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `(q + 1) + 7 = q + 1 * 8`] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ]);;

let PUFF_BITCNT_MOD = prove
 (`!p i ic0.
        p <= 8 * ic0 /\ 8 * ic0 <= p + 7
        ==> ((8 * ic0 - p) + 7 * (i + 1)) MOD 8 =
            (8 * ((p + i) DIV 8 + 1) - (p + i)) - 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `(ic0 + i) - (p + i) DIV 8` THEN
  MP_TAC(SPECL [`p + i`; `8`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(p + i) DIV 8 <= ic0 + i` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `8 * a <= 8 * b ==> a <= b`) THEN
    MP_TAC(SPECL [`p + i`; `8`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Contracts for _setjmp and longjmp. The code calls them through its PLT,   *)
(* which reads their addresses fs and fl from the GOT. Their code is not     *)
(* part of the image, so their behaviour is assumed, as a notional           *)
(* high-level contract in the style of those for memset and memcpy in the    *)
(* mlkem branch, in any state where some region (ea,el) of memory,           *)
(* containing their code and any data they use, has fixed contents ev, and   *)
(* they are assumed not to use the stack. The context that _setjmp saves in  *)
(* the jmp_buf env, and longjmp restores, is that of glibc on AArch64: the   *)
(* registers X19-X29, X30 (the return address of _setjmp), SP and the low    *)
(* halves of Q8-Q15. It is saved in the 312 bytes of the jmp_buf in an       *)
(* unspecified encoding enc, the same for both, and longjmp(env,v) returns   *)
(* as if from the call of _setjmp that saved it, with the 32-bit result v,   *)
(* or 1 if v is 0, and no memory changed.                                    *)
(* ------------------------------------------------------------------------- *)

let jmp_context = new_definition
 `jmp_context (s:armstate) =
    [read X19 s; read X20 s; read X21 s; read X22 s; read X23 s;
     read X24 s; read X25 s; read X26 s; read X27 s; read X28 s;
     read X29 s; read X30 s; read SP s;
     read (Q8 :> bottomhalf) s; read (Q9 :> bottomhalf) s;
     read (Q10 :> bottomhalf) s; read (Q11 :> bottomhalf) s;
     read (Q12 :> bottomhalf) s; read (Q13 :> bottomhalf) s;
     read (Q14 :> bottomhalf) s; read (Q15 :> bottomhalf) s]`;;

let MAYCHANGE_JMP_CONTEXT = new_definition
 `MAYCHANGE_JMP_CONTEXT =
    MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
               SP] ,,
    MAYCHANGE [Q8 :> bottomhalf; Q9 :> bottomhalf; Q10 :> bottomhalf;
               Q11 :> bottomhalf; Q12 :> bottomhalf; Q13 :> bottomhalf;
               Q14 :> bottomhalf; Q15 :> bottomhalf]`;;

let setjmp_contract = new_definition
 `setjmp_contract (fs:int64) (ea:int64) (el:num) (ev:num)
                  (enc:int64 list->num) <=>
    !env returnaddress ctx.
        nonoverlapping (env,312) (ea,el)
        ==> ensures arm
             (\s. read PC s = fs /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [env] s /\
                  jmp_context s = ctx /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  word_zx(read X0 s):int32 = word 0 /\
                  read (memory :> bytes(env,312)) s = enc ctx)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18; X30] ,,
              MAYCHANGE [memory :> bytes(env,312)])`;;

let longjmp_contract = new_definition
 `longjmp_contract (fl:int64) (ea:int64) (el:num) (ev:num)
                   (enc:int64 list->num) <=>
    !env v ctx.
        ensures arm
         (\s. read PC s = fl /\
              C_ARGUMENTS [env; v] s /\
              read (memory :> bytes(env,312)) s = enc ctx /\
              read (memory :> bytes(ea,el)) s = ev)
         (\s. read PC s = EL 11 ctx /\
              jmp_context s = ctx /\
              word_zx(read X0 s):int32 =
              (if word_zx v:int32 = word 0 then word 1 else word_zx v))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [X18] ,, MAYCHANGE_JMP_CONTEXT)`;;

let setjmp_longjmp_contract = new_definition
 `setjmp_longjmp_contract (fs:int64) (fl:int64) (ea:int64) (el:num)
                          (ev:num) <=>
    ?enc. setjmp_contract fs ea el ev enc /\
          longjmp_contract fl ea el ev enc`;;

(* ------------------------------------------------------------------------- *)
(* A Huffman decoding table (struct huffman) at address h, for the code with *)
(* code lengths lens: pointers to the counts of the codes of each length, at *)
(* cnt, and to the symbols in the order of their codes, at sym, both arrays  *)
(* of shorts, with contents the lists cnts and syms.                         *)
(* ------------------------------------------------------------------------- *)

let puff_table = new_definition
 `puff_table (h:int64) (cnt:int64) (sym:int64) (cnts:int16 list)
             (syms:int16 list) (s:armstate) <=>
    read (memory :> bytes64 h) s = cnt /\
    read (memory :> bytes64(word_add h (word 8))) s = sym /\
    read (memory :> bytes(cnt,32)) s = num_of_wordlist cnts /\
    read (memory :> bytes(sym,2 * LENGTH syms)) s = num_of_wordlist syms`;;

let huffman_table = new_definition
 `huffman_table (lens:num list) (cnts:int16 list) (syms:int16 list) <=>
    LENGTH cnts = 16 /\
    (!n. n < 16 ==> EL n cnts = word(huffman_count lens n)) /\
    (!t. t < LENGTH lens /\ ~(EL t lens = 0)
         ==> huffman_rank lens t < LENGTH syms /\
             EL (huffman_rank lens t) syms = word t)`;;

(*** The counts of the code lengths 0, 1, ..., 15, as built by construct ***)

let huffman_counts = new_definition
 `huffman_counts (lens:num list) =
    list_of_seq (\n. word(huffman_count lens n):int16) 16`;;

let LENGTH_HUFFMAN_COUNTS = prove
 (`!lens. LENGTH(huffman_counts lens) = 16`,
  REWRITE_TAC[huffman_counts; LENGTH_LIST_OF_SEQ]);;

let EL_HUFFMAN_COUNTS = prove
 (`!lens n.
        n < 16 ==> EL n (huffman_counts lens) = word(huffman_count lens n)`,
  SIMP_TAC[huffman_counts; EL_LIST_OF_SEQ]);;

let HUFFMAN_TABLE_ALL_ZERO = prove
 (`!lens syms.
        ALL (\x. x = 0) lens
        ==> huffman_table lens (huffman_counts lens) syms`,
  REWRITE_TAC[huffman_table; GSYM ALL_EL; LENGTH_HUFFMAN_COUNTS] THEN
  SIMP_TAC[EL_HUFFMAN_COUNTS] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* For an "ensures" goal whose precondition has jmp_context s = ctx with ctx *)
(* a variable, and read X30 s = returnaddress and read SP s = stackpointer,  *)
(* introduce variables ctx_x19, ..., ctx_d15 for the other registers of the  *)
(* context, so that the simulation keeps track of them, and replace ctx by   *)
(* the list of them all.                                                     *)
(* ------------------------------------------------------------------------- *)

let JMP_CONTEXT_INTRO_TAC =
  let regs =
   ["X19"; "X20"; "X21"; "X22"; "X23"; "X24"; "X25"; "X26"; "X27"; "X28";
    "X29"; "Q8 :> bottomhalf"; "Q9 :> bottomhalf"; "Q10 :> bottomhalf";
    "Q11 :> bottomhalf"; "Q12 :> bottomhalf"; "Q13 :> bottomhalf";
    "Q14 :> bottomhalf"; "Q15 :> bottomhalf"]
  and names =
   ["ctx_x19"; "ctx_x20"; "ctx_x21"; "ctx_x22"; "ctx_x23"; "ctx_x24";
    "ctx_x25"; "ctx_x26"; "ctx_x27"; "ctx_x28"; "ctx_x29"; "ctx_d8";
    "ctx_d9"; "ctx_d10"; "ctx_d11"; "ctx_d12"; "ctx_d13"; "ctx_d14";
    "ctx_d15"]
  and lst = `[ctx_x19:int64; ctx_x20; ctx_x21; ctx_x22; ctx_x23; ctx_x24;
              ctx_x25; ctx_x26; ctx_x27; ctx_x28; ctx_x29; returnaddress;
              stackpointer; ctx_d8; ctx_d9; ctx_d10; ctx_d11; ctx_d12;
              ctx_d13; ctx_d14; ctx_d15]` in
  let is_jc t = is_eq t &&
    (match lhs t with Comb(Const("jmp_context",_),_) -> true | _ -> false) in
  MAP_EVERY (fun (n,r) ->
    GHOST_INTRO_TAC (mk_var(n,`:int64`)) (parse_term("read ("^r^")")))
   (zip names regs) THEN
  W(fun (asl,w) ->
    let pre = rand(rator(rator w)) in
    let sv,bod = dest_abs pre in
    let jc = find is_jc (conjuncts bod) in
    let bod' = subst [mk_eq(rhs jc,lst),jc] bod in
    ENSURES_PRECONDITION_TAC (mk_abs(sv,bod')) THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_jc o concl)) THEN
      ASM_REWRITE_TAC[jmp_context];
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check
       (fun th -> is_eq(concl th) && rhs(concl th) = lst))]);;


(* ------------------------------------------------------------------------- *)
(* The state of puff (struct state) at address st, of 368 bytes:             *)
(*                                                                           *)
(*   0: unsigned char *out                32: unsigned long inlen            *)
(*   8: unsigned long outlen              40: unsigned long incnt            *)
(*  16: unsigned long outcnt              48: int bitbuf                     *)
(*  24: const unsigned char *in           52: int bitcnt                     *)
(*                                        56: jmp_buf env                    *)
(*                                                                           *)
(* puff_input st inp l p s says that the input is the list of bytes l at     *)
(* address inp and that the bits of the stream up to position p have been    *)
(* read, in the form that puff keeps: the bytes read are those containing    *)
(* the bits before p, and the rest of the last of them, the bits from p to a *)
(* multiple of 8, are in bitbuf.                                             *)
(* ------------------------------------------------------------------------- *)

let puff_input = new_definition
 `puff_input (st:int64) (inp:int64) (l:byte list) p (s:armstate) <=>
    read (memory :> bytes64(word_add st (word 24))) s = inp /\
    read (memory :> bytes64(word_add st (word 32))) s = word(LENGTH l) /\
    read (memory :> bytes64(word_add st (word 40))) s = word((p + 7) DIV 8) /\
    read (memory :> bytes32(word_add st (word 48))) s =
    word(deflate_bits l p (8 * ((p + 7) DIV 8) - p)) /\
    read (memory :> bytes32(word_add st (word 52))) s =
    word(8 * ((p + 7) DIV 8) - p) /\
    read (memory :> bytes(inp,LENGTH l)) s = num_of_bytelist l`;;

(* puff_output st outp outlen out s says that the output buffer is at outp,  *)
(* of size outlen, and that the output so far is the list of bytes out.      *)

let puff_output = new_definition
 `puff_output (st:int64) (outp:int64) outlen (out:byte list) (s:armstate) <=>
    read (memory :> bytes64 st) s = outp /\
    read (memory :> bytes64(word_add st (word 8))) s = word outlen /\
    read (memory :> bytes64(word_add st (word 16))) s = word(LENGTH out) /\
    read (memory :> bytes(outp,LENGTH out)) s = num_of_bytelist out`;;

(* ------------------------------------------------------------------------- *)
(* A loop that runs at most k times, with the invariant lp i at the start of *)
(* iteration i, whose iterations may exit early with the postcondition Q.    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_LOOP_EXIT = prove
 (`!k (lp:num->A->bool) P Q C.
        C ,, C = C /\ (=) subsumed C /\
        ensures step P (lp 0) C /\
        (!i. i < k ==> ensures step (lp i) (\s. lp (i + 1) s \/ Q s) C) /\
        ensures step (lp k) Q C
        ==> ensures step P Q C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. j <= k ==> ensures step ((lp:num->A->bool) (k - j)) Q C`
   (MP_TAC o SPEC `k:num`) THENL
   [ALL_TAC;
    REWRITE_TAC[SUB_REFL] THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `(lp:num->A->bool) 0` THEN ASM_REWRITE_TAC[]] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `\s. (lp:num->A->bool) (k - j) s \/ Q s` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k - SUC j` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC j <= k ==> k - SUC j + 1 = k - j`];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ensures] THEN DISCH_TAC THEN X_GEN_TAC `s:A` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((=):A->A->bool) subsumed C` THEN
    REWRITE_TAC[subsumed] THEN MESON_TAC[]]);;

(* A sequence through a point at which M holds, from which R is reached,     *)
(* where the first part may instead reach R directly.                        *)

let ENSURES_SEQUENCE_EXIT = prove
 (`!(M:A->bool) P R C.
        C ,, C = C /\ (=) subsumed C /\
        ensures step P (\s. M s \/ R s) C /\ ensures step M R C
        ==> ensures step P R C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `\s. (M:A->bool) s \/ R s` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ensures step (M:A->bool) R C` THEN
  REWRITE_TAC[ensures] THEN DISCH_TAC THEN X_GEN_TAC `s:A` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `((=):A->A->bool) subsumed C` THEN
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;

(* A loop with the invariant lp n, for a measure n that each iteration       *)
(* decreases, unless it exits with the postcondition Q.                      *)

let ENSURES_WHILE_MEASURE = prove
 (`!(lp:num->A->bool) P Q C.
        C ,, C = C /\ (=) subsumed C /\
        ensures step P (\s. (?n. lp n s) \/ Q s) C /\
        (!n. ensures step (lp n) (\s. (?m. m < n /\ lp m s) \/ Q s) C)
        ==> ensures step P Q C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. ensures step ((lp:num->A->bool) n) Q C` ASSUME_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `\s. (?m. m < n /\ (lp:num->A->bool) m s) \/ Q s` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ensures] THEN X_GEN_TAC `s:A` THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[ensures] THEN
      DISCH_THEN(MP_TAC o SPEC `s:A`) THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `((=):A->A->bool) subsumed C` THEN
      REWRITE_TAC[subsumed] THEN MESON_TAC[]];
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `\s. (?n. (lp:num->A->bool) n s) \/ Q s` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ensures] THEN X_GEN_TAC `s:A` THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[ensures] THEN
      DISCH_THEN(MP_TAC o SPEC `s:A`) THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `((=):A->A->bool) subsumed C` THEN
      REWRITE_TAC[subsumed] THEN MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* An existential in the precondition, which is pulled out of the conjuncts  *)
(* and generalized over, with the given name, by ENSURES_EXISTS_PRE_TAC.     *)
(* ------------------------------------------------------------------------- *)

let ENSURES_EXISTS_PRECONDITION = prove
 (`!step (P:B->A->bool) Q C.
        (!x. ensures step (\s. P x s) Q C)
        ==> ensures step (\s. ?x. P x s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let ENSURES_EXISTS_PRE_TAC v =
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV(ABS_CONV
   (TOP_DEPTH_CONV(REWR_CONV LEFT_AND_EXISTS_THM ORELSEC
                   REWR_CONV RIGHT_AND_EXISTS_THM)))))) THEN
  MATCH_MP_TAC ENSURES_EXISTS_PRECONDITION THEN X_GEN_TAC v THEN BETA_TAC;;

(* ------------------------------------------------------------------------- *)
(* Simulating the code. PUFF_STEP_TAC n does step n and normalizes the       *)
(* values, and when the step is a conditional branch or computes a value     *)
(* conditional on the flags, decides the flags where the comparison is of    *)
(* small numbers or of pointers with the same base, and the branch.          *)
(* ------------------------------------------------------------------------- *)

(*** Normalize the condition of a conditional branch ***)

let PC_COND_NORM_TAC =
  W(fun (asl,w) ->
    let conv = SMALL_WORD_CONV asl in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),
             r) when is_cond r ->
          CONV_RULE (RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV conv)))) th
      | _ -> th));;

(*** Decide the condition of a conditional branch ***)

let DECIDE_BRANCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not (is_cond r) || not(can (term_match [] `read PC s`) l)
    then failwith "DECIDE_BRANCH_TAC" else
    DECIDE_PROP_TAC (lhand(rator r)));;

let PUFF_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),t)
          when s' = s -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC PUFF_EXEC [n] THEN SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let PUFF_STEPS_TAC ns = MAP_EVERY PUFF_STEP_TAC ns;;

(*** Normalize a pointer in register r, as word_add a (word n) ***)

let PTR_NORM_TAC r =
  W(fun (asl,w) ->
    let s = rand w in
    let tm = mk_comb(mk_comb
      (`read:((armstate,int64)component)->armstate->int64`,r),s) in
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = tm
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] th)
      else failwith "PTR_NORM_TAC"));;

(*** The same for all the registers and addresses of the current state ***)

let STATE_PTR_NORM_TAC =
  let conv = REWRITE_CONV[GSYM WORD_ADD_ASSOC; WORD_ADD_0] THENC
             REWRITE_CONV[GSYM WORD_ADD] THENC NUM_REDUCE_CONV in
  let flags = [`NF`; `ZF`; `CF`; `VF`; `PC`] in
  fun (asl,w as gl) ->
    let s = try rand w with Failure _ -> w in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),_)
          when s' = s && not(mem c flags) -> CONV_RULE conv th
      | _ -> th) gl;;

(*** Replace the value tm of register r by the variable v ***)

let REG_ABBREV_TAC r v tm =
  ABBREV_TAC (mk_eq(v,tm)) THEN
  W(fun (asl,w) ->
    let s = rand w in
    let rd = mk_comb(mk_comb
      (`read:((armstate,int64)component)->armstate->int64`,r),s) in
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = rd
      then ASSUME_TAC(REWRITE_RULE[ASSUME (mk_eq(tm,v))] th)
      else failwith "REG_ABBREV_TAC"));;

(* ------------------------------------------------------------------------- *)
(* A register r holding word k, for a small number k, used as an index with  *)
(* SXTW extension. The simulation gives the address of the access with       *)
(* val(word_sx(word_zx ...)) for the index, which it rewrites with the       *)
(* equations here, and which the reasoning about non-overlapping regions     *)
(* understands only once the value of r is replaced by a variable v, since   *)
(* it ignores the assumptions that involve words of numbers.                 *)
(* ------------------------------------------------------------------------- *)

let SXTW_ABBREV_TAC r v k =
  let wk = mk_comb(`word:num->int64`,k) in
  let e1 = mk_eq(mk_comb(`val:int64->num`,
             mk_comb(`word_sx:int32->int64`,
               mk_comb(`word_zx:int64->int32`,v))),k)
  and e2 = mk_eq(mk_comb(`val:int64->num`,
             mk_comb(`word_sx:int32->int64`,
               mk_comb(`word_zx:int32->int32`,
                 mk_comb(`word_zx:int64->int32`,v)))),k) in
  REG_ABBREV_TAC r v wk THEN
  MAP_EVERY (fun e ->
    SUBGOAL_THEN e ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME(mk_eq(wk,v)))) THEN
      W(fun (asl,w) -> CONV_TAC(LAND_CONV(SMALL_WORD_CONV asl))) THEN
      REFL_TAC;
      ALL_TAC]) [e1; e2];;

(*** Rewrite the index 2 * k in the address of a 16-bit read at base to    ***)
(*** 2 * e, the form that the simulation gives, where val e = k            ***)

let ADDR16_TAC base k e =
  let is_b16 tm =
    can (find_term (fun u ->
      is_const u && fst(dest_const u) = "bytes16")) tm in
  let eq = mk_eq(mk_binop `( * ):num->num->num` `2` k,
                 mk_binop `( * ):num->num->num` `2` e) in
  SUBGOAL_THEN eq ASSUME_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST [MATCH_MP_TAC VAL_SXTW_SMALL; MATCH_MP_TAC VAL_WORD_SMALL] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_b16 (lhs c) && free_in base (lhs c) &&
       free_in (mk_binop `( * ):num->num->num` `2` k) (lhs c)
    then ASSUME_TAC(GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV)
                     [ASSUME eq] th)
    else failwith "ADDR16_TAC");;

(* ------------------------------------------------------------------------- *)
(* A call of longjmp(env,1), at step n, at which the PC is the address of    *)
(* longjmp read from the GOT by the PLT stub, using the contract (which must *)
(* be an assumption) with the context ctx that env holds.                    *)
(* ------------------------------------------------------------------------- *)

let PUFF_LONGJMP_TAC env ctx n =
  let sname = "s"^string_of_int n in
  FIRST_ASSUM(fun th ->
    match strip_comb(concl th) with
      Const("longjmp_contract",_),[_;_;_;_;_] ->
        MP_TAC(SPECL [env; `word 1:int64`; ctx]
                 (REWRITE_RULE[longjmp_contract] th))
    | _ -> NO_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MAYCHANGE_JMP_CONTEXT; MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC PUFF_EXEC sname THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV));;

(* ------------------------------------------------------------------------- *)
(* A call of one of the functions of puff from another, at step n, at which  *)
(* the PC is the address of the callee, using its correctness theorem th     *)
(* specialized at the terms vars. In these, `ctx0:int64 list`, for the       *)
(* context of the caller that the callee preserves, is replaced by the       *)
(* values of the components of jmp_context in the current state, for which   *)
(* variables are introduced where they are not known.                        *)
(* ------------------------------------------------------------------------- *)

let jmp_components =
  [`X19`; `X20`; `X21`; `X22`; `X23`; `X24`; `X25`; `X26`; `X27`; `X28`;
   `X29`; `X30`; `SP`; `Q8 :> bottomhalf`; `Q9 :> bottomhalf`;
   `Q10 :> bottomhalf`; `Q11 :> bottomhalf`; `Q12 :> bottomhalf`;
   `Q13 :> bottomhalf`; `Q14 :> bottomhalf`; `Q15 :> bottomhalf`];;

let jmp_values (asl,w) =
  let s = rand w in
  let value c =
    let rd = list_mk_icomb "read" [c; s] in
    try rhs(concl(snd(find (fun (_,th) ->
              let t = concl th in is_eq t && lhs t = rd) asl)))
    with Failure _ -> failwith("jmp_values: " ^ string_of_term c) in
  mk_list(map value jmp_components,`:int64`);;

let JMP_VALUES_GHOST_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let missing = filter (fun c ->
      let rd = list_mk_icomb "read" [c; s] in
      not (exists (fun (_,th) -> let t = concl th in is_eq t && lhs t = rd)
                  asl)) jmp_components in
    MAP_EVERY (fun c ->
      let rd = list_mk_icomb "read" [c; s] in
      let v = genvar `:int64` in
      ABBREV_TAC (mk_eq(v,rd))) missing gl;;

(*** The hypotheses of the callee theorem, from the assumptions ***)

let CALLEE_HYPS_TAC =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         ALIGNED_WORD_TAC THEN NO_TAC;
         NONOVERLAPPING_TAC;
         SIMPLE_ARITH_TAC];;

(*** The stack frame of the callee as one region below the caller's ***)

let WORD_SUB_SUB_NUM = WORD_RULE
 `word_sub (word_sub (x:int64) (word a)) (word b) = word_sub x (word(a + b))`;;

let PUFF_CALL_TAC th vars n =
  JMP_VALUES_GHOST_TAC THEN
  W(fun gl ->
    let ctx0 = jmp_values gl in
    let vars' = map (fun v -> if v = `ctx0:int64 list` then ctx0 else v)
                    vars in
    MP_TAC(ISPECL vars' th)) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; puff_input; puff_table; jmp_context; CONS_11;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE_JMP_CONTEXT;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  ARM_BIGSTEP_TAC PUFF_EXEC ("s"^string_of_int n) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC);;

(*** After a call of decode at position p, that its symbol is in range and ***)
(*** its code ends after p and within the input                            ***)

let DECODE_FACTS_TAC p =
  FIRST_ASSUM(fun th ->
    match strip_comb(concl th) with
      Const("huffman_decode",_),[_;_;p';_;_] when p' = p ->
        ASSUME_TAC(MATCH_MP HUFFMAN_DECODE_SYMBOL th) THEN
        STRIP_ASSUME_TAC(MATCH_MP HUFFMAN_DECODE_POS th)
    | _ -> failwith "DECODE_FACTS_TAC");;

(*** Decide the test of bit 31 of a register holding word n, for n small ***)

let BIT_WORD_LT = prove
 (`!n k. n < 2 EXP k ==> ~bit k (word n:N word)`,
  SIMP_TAC[BIT_WORD; DIV_LT; ODD]);;

let BIT31_DECIDE_TAC =
  W(fun (asl,w) ->
    let s = rand w in
    let pcth = snd(find (fun (_,th) -> let t = concl th in
      is_eq t && lhs t = list_mk_icomb "read" [`PC`; s] && is_cond(rhs t))
      asl) in
    let c0 = lhand(rator(rhs(concl pcth))) in
    let c = if is_neg c0 then rand c0 else c0 in
    let ith = PART_MATCH (rand o rand) BIT_WORD_LT c in
    let bth = TAC_PROOF((asl,lhand(concl ith)),
                CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC) in
    RULE_ASSUM_TAC(REWRITE_RULE[MP ith bth]));;

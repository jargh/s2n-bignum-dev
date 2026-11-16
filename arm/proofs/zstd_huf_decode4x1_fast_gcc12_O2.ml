(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The fast decoding of Huffman-coded literals in four streams with          *)
(* single-symbol tables in zstd, compiled by gcc 12 at -O2 for AArch64:      *)
(* HUF_decompress4X1_usingDTable_internal_fast_c_loop, which decodes 5       *)
(* symbols of each stream per iteration, and HUF_DecompressFastArgs_init,    *)
(* which sets up its arguments.                                              *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode1x1_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress4X1_usingDTable_internal_fast_c_loop at 0x24a4 takes, in    *)
(* the arguments at args, for each of the four streams k of the block blk at *)
(* ilowest a pointer ip[k] = ilowest + u_k to the 8 bytes that end its       *)
(* unread bits, a pointer op[k] to its output, and a bit container bits[k],  *)
(* those 8 bytes with bit 0 set as a sentinel, shifted left by the s_k bits  *)
(* already used, so that the stream is at position p_k = 8 * u_k + 64 - s_k  *)
(* in blk; and the table dt of 2^11 entries for the code of the weights ws.  *)
(* Each iteration decodes 5 symbols of each stream and then reloads each     *)
(* container, for as many iterations as the first stream has 7 bytes before  *)
(* ilowest and the last 5 bytes of output before oend for, and then again as *)
(* long as the pointers are in order (ip[0] <= ip[1] <= ip[2] <= ip[3]).     *)
(* Each lookup has at least 12 bits in its container, so the decoding is     *)
(* that of huf_decode ws ml blk p_k on all of blk, whatever the input, with  *)
(* no code needing more bits than are left. The function returns the         *)
(* arguments after j symbols of each stream, for some j, with args still in  *)
(* X0, as its caller expects (HUF_DECOMPRESS4X1_FAST_C_LOOP_CORRECT).        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The containers and the table. The arguments are copied to the stack and   *)
(* back with 128-bit loads and stores of q registers. The index of a lookup  *)
(* is the top 11 bits of a container, which are the 11 bits of blk below the *)
(* position of the stream, and the 16-bit entry of the table gives its       *)
(* number of bits nb in its low byte and its symbol sym in its high byte.    *)
(* After 5 symbols, a stream moves back by the whole bytes used, and the     *)
(* container is the 8 bytes from there with the bits used of the next byte,  *)
(* by counting the trailing zeros up to the sentinel.                        *)
(* ------------------------------------------------------------------------- *)

(*** Memory: 128-bit reads as two 64-bit ones and back ***)

let READ_BYTES128_JOIN = prove
 (`!(a:int64) x y s.
        read (memory :> bytes64 a) s = x /\
        read (memory :> bytes64 (word_add a (word 8))) s = y
        ==> read (memory :> bytes128 a) s = word_join y x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  ASM_REWRITE_TAC[]);;

let READ_BYTES128_SPLIT = prove
 (`!(a:int64) d s.
        read (memory :> bytes128 a) s = d
        ==> read (memory :> bytes64 a) s = word_subword d (0,64) /\
            read (memory :> bytes64 (word_add a (word 8))) s =
            word_subword d (64,64)`,
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)]);;

let WORD_SUBWORD_JOIN_64 = prove
 (`!x y:int64. word_subword (word_join y x:int128) (0,64):int64 = x /\
               word_subword (word_join y x:int128) (64,64):int64 = y`,
  CONV_TAC WORD_BLAST);;

(*** The bit container of the fast loop, with its sentinel bit: the 8     ***)
(*** bytes w from the pointer, with bit 0 set, shifted left by the number ***)
(*** x of bits used                                                       ***)

let FAST_CTZ = prove
 (`!(w:int64) x. x < 64 ==> word_ctz(word_shl (word_or w (word 1)) x) = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_shl (word_or w (word 1)) x:int64`; `x:num`]
    WORD_CTZ_UNIQUE) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_OR; DIMINDEX_64; LE_REFL; SUB_REFL] THEN
  ASM_REWRITE_TAC[BIT_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NOT_LT] THEN MESON_TAC[]);;

let FAST_TOP = prove
 (`!(w:int64) x.
        x <= 52
        ==> word_ushr (word_shl (word_or w (word 1)) x) 53 =
            word_ushr (word_shl w x) 53`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD_OR; DIMINDEX_64;
              BIT_WORD_1] THEN
  ASM_CASES_TAC `i + 53 < 64` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((i + 53) - x = 0) /\ (i + 53) - x < 64 /\ x <= i + 53`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(*** The index into the table: the top 11 bits, which are the bits of the ***)
(*** bytes blk below the position 8 * u + 64 - x                          ***)

let FAST_INDEX = prove
 (`!(blk:byte list) u x.
        x <= 52
        ==> word_ushr (word_shl (word_or
              (word ((num_of_bytelist blk DIV 2 EXP (8 * u)) MOD 2 EXP 64))
              (word 1)) x) 53:int64 =
            word (zstd_back blk (8 * u + 64 - x) 11)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FAST_TOP] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_SHL; VAL_WORD;
              DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  SUBGOAL_THEN
   `2 EXP x * (num_of_bytelist (blk:byte list) DIV 2 EXP (8 * u)) MOD
              2 EXP 64 =
    ((num_of_bytelist blk DIV 2 EXP (8 * u)) MOD 2 EXP 64) * 2 EXP x`
  SUBST1_TAC THENL [REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  SUBST1_TAC(ARITH_RULE `53 = 64 - 11`) THEN
  MP_TAC(ISPECL [`blk:byte list`; `u:num`; `x:num`; `11`] ZSTD_WINDOW) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`blk:byte list`; `8 * u + 64 - x`; `11`] ZSTD_BACK_BOUND) THEN
  ARITH_TAC);;

(*** The 16-bit entry of the table for the index x ***)

let WORD_JOIN_BYTES = prove
 (`!a b. a < 256 /\ b < 256
         ==> word_join (word b:byte) (word a:byte):int16 = word(a + 256 * b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_8; DIMINDEX_16; ARITH] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `a + 256 * b < 65536` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC]);;

let HUF_DTABLE_READ16 = prove
 (`!ws ml tl (tbl:int64) x s.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\ tl <= 12 /\
        x < 2 EXP tl /\
        read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
        num_of_bytelist (huf_dtable ws ml tl)
        ==> read (memory :> bytes16 (word_add tbl (word (2 * x)))) s =
            word(((ml + 1) - EL (huf_symbol ws (x DIV 2 EXP (tl - ml))) ws) +
                 256 * huf_symbol ws (x DIV 2 EXP (tl - ml)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; `x:num`;
                `s:armstate`] HUF_DTABLE_READ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x DIV 2 EXP (tl - ml) < 2 EXP ml` ASSUME_TAC THENL
   [MATCH_MP_TAC DIV_EXP_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC WORD_JOIN_BYTES THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (tl - ml)`]
    HUF_SYMBOL_BOUND) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (tl - ml)`]
    HUF_NBITS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`ml <= tl`; `tl <= 12`] THEN ARITH_TAC);;

(*** The symbol and the number of bits of an entry nb + 256 * sym, as the ***)
(*** fast loop takes them                                                 ***)

let FAST_SYM = prove
 (`!nb sym.
        nb < 256 /\ sym < 256
        ==> word_zx (word_ishr (word_zx (word (nb + 256 * sym):int16):int32)
                               8):byte = word sym`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM WORD_JOIN_BYTES] THEN
  SPEC_TAC(`word sym:byte`,`y:byte`) THEN
  SPEC_TAC(`word nb:byte`,`x:byte`) THEN
  CONV_TAC WORD_BLAST);;

let FAST_JSHL = prove
 (`!(c:int64) nb sym.
        nb < 64 /\ sym < 256
        ==> word_jshl c
              (word_zx (word_zx (word (nb + 256 * sym):int16):int32)) =
            word_shl c nb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jshl] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `nb + 256 * sym < 65536` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 65536 ==> x < 4294967296`;
               ARITH_RULE `x < 65536 ==> x < 18446744073709551616`] THEN
  REWRITE_TAC[ARITH_RULE `nb + 256 * sym = nb + (4 * sym) * 64`] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let FAST_JSHL64 = prove
 (`!(c:int64) nb sym.
        nb < 64 /\ sym < 256
        ==> word_jshl c (word (nb + 256 * sym)) = word_shl c nb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_jshl] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `nb + 256 * sym < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN
  REWRITE_TAC[ARITH_RULE `nb + 256 * sym = nb + (4 * sym) * 64`] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let FAST_SYM_DIV = prove
 (`!nb sym. nb < 256 ==> (nb + 256 * sym) DIV 256 = sym`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `nb:num` THEN
  ASM_ARITH_TAC);;

(*** The reload of the fast loop: the number of whole bytes used and the ***)
(*** bits used of the next byte                                          ***)

let FAST_RELOAD_CTZ = prove
 (`!(w:int64) x.
        x < 64
        ==> word(word_clz(word_reversefields 1 (word_shl (word_or w (word 1))
                                                  x))):int64 = word x`,
  SIMP_TAC[WORD_CLZ_REVERSEFIELDS; FAST_CTZ]);;

let FAST_RELOAD_USHR = prove
 (`!x. x < 64 ==> word_ushr (word x:int64) 3 = word (x DIV 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD;
                                    DIMINDEX_64] THEN
  SUBGOAL_THEN `x < 2 EXP 64 /\ x DIV 8 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `x:num` THEN
      REWRITE_TAC[DIV_LE] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV]);;

let FAST_RELOAD_SUB = prove
 (`!(a:int64) u d. d <= u ==> word_sub (word_add a (word u)) (word d) =
                              word_add a (word (u - d))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let FAST_RELOAD_AND = prove
 (`!x. x < 64
       ==> word_zx (word_and (word_zx (word x:int64):int32) (word 7)):int64 =
           word (x MOD 8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `x MOD 2 EXP 64 = x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `7 = 2 EXP 3 - 1`; WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD; WORD_ZX_WORD; DIMINDEX_32] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `x MOD 4294967296 = x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`x:num`; `8`] MOD_LT_EQ) THEN ARITH_TAC);;

let FAST_RELOAD_JSHL = prove
 (`!(w:int64) x.
        word_jshl (word_or w (word 1)) (word (x MOD 8)) =
        word_shl (word_or w (word 1)) (x MOD 8)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_jshl] THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `x MOD 8 < 8` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x MOD 8 < 2 EXP 64 /\ x MOD 8 < 64` STRIP_ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(*** One more symbol decoded by a lookup of the fast loop ***)

let HUF_DECODE_FAST_STEP = prove
 (`!ws ml (blk:byte list) p0 j u x sym nb.
     FST(SND(huf_decode ws ml blk p0 j)) = 8 * u + 64 - x /\
     SND(SND(huf_decode ws ml blk p0 j)) /\ x <= 52 /\
     huf_symbol ws (zstd_back blk (8 * u + 64 - x) ml) = sym /\
     (ml + 1) - EL sym ws = nb /\ nb <= ml /\ ml <= 11
     ==> FST(huf_decode ws ml blk p0 (j + 1)) =
         APPEND (FST(huf_decode ws ml blk p0 j)) [word sym] /\
         FST(SND(huf_decode ws ml blk p0 (j + 1))) = 8 * u + 64 - (x + nb) /\
         SND(SND(huf_decode ws ml blk p0 (j + 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[HUF_DECODE_SUC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let fl_win u = subst [u,`u:num`]
  `word((num_of_bytelist (blk:byte list) DIV 2 EXP (8 * u)) MOD
         2 EXP 64):int64`;;

let fl_cont u x = subst [fl_win u,`w:int64`; x,`x:num`]
  `word_shl (word_or w (word 1)) x:int64`;;

(* ------------------------------------------------------------------------- *)
(* The simulation of an iteration, of 132 instructions with 20 lookups, is   *)
(* made practical by normalizing the facts after each step (FL_NORM_TAC):    *)
(* the indices as bits of blk, with the table entries, symbols and numbers   *)
(* of bits abbreviated as idxN, symN and nbN; the stores of the symbols      *)
(* merged into one fact for the bytes decoded of each stream; the reloads;   *)
(* and the numeric facts about the lookups hidden in one conjunction. The    *)
(* postcondition is abbreviated during the simulation (FL_ABBREV_POST_TAC),  *)
(* which makes each step much faster.                                        *)
(* ------------------------------------------------------------------------- *)

(*** Normalization in the simulation of the fast loop, after each step ***)

let FAST_INDEX' = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) FAST_INDEX;;

let fl_counter = ref 0;;

let fl_index_pat =
  `word_ushr (word_shl (word_or (word ((num_of_bytelist (blk:byte list) DIV
       2 EXP (8 * u)) MOD 18446744073709551616)) (word 1)) x) 53:int64`;;

(*** A bound x <= c for a sum x, from the bounds of its summands and ***)
(*** ml <= 11                                                        ***)

let FL_LE_TAC : tactic =
  fun (asl,w as gl) ->
    let atoms = striplist (dest_binop `(+):num->num->num`) (lhand w) in
    let facts = mapfilter (fun th ->
      let t = concl th in
      if is_binop `(<=):num->num->bool` t &&
         mem (lhand t) (`ml:num`::atoms) then th else fail())
      (itlist (fun (_,th) acc -> CONJUNCTS th @ acc) asl []) in
    (MAP_EVERY MP_TAC facts THEN ARITH_TAC) gl;;

(*** Arithmetic side conditions, from the numeric facts (also in the      ***)
(*** conjunctions of hidden facts) about the variables of the goal and ml ***)

let FL_ARITH_TAC : tactic =
  fun (asl,w as gl) ->
    let vs = `ml:num` :: frees w in
    let numty = `:num` in
    let ok t =
      exists (fun op -> is_binary op t && type_of(lhand t) = numty)
             ["="; "<"; "<="] &&
      not(exists (fun v -> type_of v = `:armstate`) (frees t)) &&
      subset (frees t) vs in
    let facts = filter (ok o concl)
      (itlist (fun (_,th) acc -> CONJUNCTS th @ acc) asl []) in
    (MAP_EVERY MP_TAC facts THEN ARITH_TAC) gl;;

(*** The index read from the container of a stream as bits of blk,     ***)
(*** with the entry of the table for it, its symbol and number of bits ***)

let FL_INDEX_ONE_TAC (th:thm) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let _,tmi,_ = term_match [] fl_index_pat (rhs(concl th)) in
    let inst v = try rev_assoc v tmi with Failure _ -> v in
    let blk = inst `blk:byte list` and u = inst `u:num` and x = inst `x:num` in
    incr fl_counter;
    let k = string_of_int !fl_counter in
    let idx = mk_var("idx"^k,`:num`) and sym = mk_var("sym"^k,`:num`)
    and nb = mk_var("nb"^k,`:num`) in
    let pos = subst [u,`u:num`; x,`x:num`] `8 * u + 64 - x` in
    let back n = list_mk_icomb "zstd_back" [blk; pos; n] in
    let lt a b = mk_binop `(<):num->num->bool` a b
    and le a b = mk_binop `(<=):num->num->bool` a b in
    let xle = le x `52` in
    let symt = list_mk_icomb "huf_symbol" [`ws:num list`; back `ml:num`] in
    let nbt = subst [symt,`t:num`] `(ml + 1) - EL t ws` in
    let divth = MP (SPECL [blk; pos; `11`; `ml:num`] ZSTD_BACK_DIV)
                   (ASSUME `ml <= 11`) in
    (SUBGOAL_THEN xle (fun xth ->
       RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [blk; u; x] FAST_INDEX') xth]))
     THENL [FL_LE_TAC; ALL_TAC] THEN
     SUBGOAL_THEN (lt (back `11`) `2048`) ASSUME_TAC THENL
      [MP_TAC(SPECL [blk; pos; `11`] ZSTD_BACK_BOUND) THEN
       CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
       ALL_TAC] THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; back `11`; s]
       HUF_DTABLE_READ16) THEN
     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) divth] THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     MP_TAC(SPECL [blk; pos; `ml:num`] ZSTD_BACK_BOUND) THEN DISCH_TAC THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; back `ml:num`]
       HUF_SYMBOL_BOUND) THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; back `ml:num`]
       HUF_NBITS_BOUND) THEN
     ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
     ABBREV_TAC (mk_eq(idx,back `11`)) THEN
     ABBREV_TAC (mk_eq(sym,symt)) THEN
     ABBREV_TAC (mk_eq(nb,subst [sym,`t:num`] `(ml + 1) - EL t ws`)) THEN
     SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                                 mk_comb(`word:num->int64`,idx)),idx))
     ASSUME_TAC THENL
      [MATCH_MP_TAC VAL_WORD_LT64 THEN UNDISCH_TAC (lt idx `2048`) THEN
       ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN (list_mk_conj [lt nb `256`; lt nb `64`])
       STRIP_ASSUME_TAC THENL
      [MAP_EVERY UNDISCH_TAC [le nb `ml:num`; `ml <= 11`] THEN ARITH_TAC;
       ALL_TAC] THEN
     ASSUME_TAC(MP (SPECL [nb; sym] FAST_SYM)
                  (CONJ (ASSUME(lt nb `256`)) (ASSUME(lt sym `256`)))) THEN
     ASSUME_TAC(GEN `c:int64` (MP (SPECL [`c:int64`; nb; sym] FAST_JSHL)
                  (CONJ (ASSUME(lt nb `64`)) (ASSUME(lt sym `256`))))) THEN
     ASSUME_TAC(GEN `c:int64` (MP (SPECL [`c:int64`; nb; sym] FAST_JSHL64)
                  (CONJ (ASSUME(lt nb `64`)) (ASSUME(lt sym `256`))))) THEN
     ASSUME_TAC(MP (SPECL [nb; sym] FAST_SYM_DIV) (ASSUME(lt nb `256`)))
    ) gl;;

let FL_INDEX_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let ths = mapfilter (fun (_,th) ->
      let t = concl th in
      if is_eq t && is_comb(lhs t) && rand(lhs t) = s &&
         can (term_match [] fl_index_pat) (rhs t) then th else fail()) asl in
    MAP_EVERY FL_INDEX_ONE_TAC ths gl;;

(*** The symbols stored and the containers shifted ***)

let fl_inst_pats =
  [`word_zx (word_ishr (word_zx (word (nb + 256 * sym):int16):int32)
                       8):byte = word sym`;
   `!c. word_jshl c (word_zx (word_zx (word (nb + 256 * sym):int16):int32)) =
        word_shl c nb`;
   `!c. word_jshl c (word (nb + 256 * sym):int64) = word_shl c nb`;
   `(nb + 256 * sym) DIV 256 = sym`];;

let FL_SHIFT_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let ths = mapfilter (fun (_,th) ->
      if exists (fun p -> can (term_match [] p) (concl th)) fl_inst_pats
      then th else fail()) asl in
    let rule = REWRITE_RULE(WORD_SHL_COMPOSE :: ths) in
    RULE_ASSUM_TAC(fun th ->
      if free_in s (concl th) then rule th else th) gl;;

(*** The table entries already loaded, and the facts with             ***)
(*** subtractions, put out of the way of the simulation of the stores ***)

let FL_DROP_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let loaded = mapfilter (fun (_,th) ->
      let t = concl th in
      if is_eq t &&
         (match lhs t with
            Comb(Comb(Const("read",_),Const(_,_)),s') -> s' = s
          | _ -> false) &&
         (let rec strip t = match t with
            Comb(Const("word_zx",_),x) -> strip x | _ -> t in
          match strip(rhs t) with
            Comb(Const("word",_),Comb(Comb(Const("+",_),nb),_)) -> true
          | _ -> false)
      then (let rec strip t = match t with
              Comb(Const("word_zx",_),x) -> strip x | _ -> t in
            strip(rhs t))
      else fail()) asl in
    let is_entry th =
      let t = concl th in
      is_eq t &&
      (match lhs t with
         Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
              Comb(Const("bytes16",_),_))),_) -> mem (rhs t) loaded
       | _ -> false) in
    DISCARD_ASSUMPTIONS_TAC is_entry gl;;

let FL_HIDE_SUB_TAC = HUF_HIDE_SUB_TAC;;

(*** The numeric facts about the variables of the lookups, put ***)
(*** together as one conjunction, except val(word idx) = idx   ***)

let fl_is_lookup_var v =
  is_var v &&
  (let n = fst(dest_var v) in
   exists (fun p -> String.length n > String.length p &&
                    String.sub n 0 (String.length p) = p)
          ["idx"; "sym"; "nb"]);;

let FL_HIDE_TAC : tactic =
  let numty = `:num` in
  let is_hidden tm =
    exists (fun op -> is_binary op tm && type_of(lhand tm) = numty)
           ["="; "<"; "<="] &&
    exists fl_is_lookup_var (frees tm) &&
    not(exists (fun v -> type_of v = `:armstate`) (frees tm)) &&
    not(is_eq tm && is_comb(lhs tm) &&
        fst(strip_comb(lhs tm)) = `val:int64->num`) &&
    not(is_binary "<" tm && is_var(lhand tm) &&
        String.sub (fst(dest_var(lhand tm))) 0 3 = "idx") in
  fun (asl,w) ->
    let ths,others = partition (fun (_,th) -> is_hidden(concl th)) asl in
    if ths = [] then ALL_TAC (asl,w) else
    ASSUME_TAC (end_itlist CONJ (map snd ths)) (others,w);;

(*** The reloads, ctz of the container, the pointer moved back by    ***)
(*** the whole bytes used, the bits used of the next byte, the new 8 ***)
(*** bytes and the new container                                     ***)

let fl_ctz_pat = `word(word_clz(word_reversefields 1
                    (word_shl (word_or (w:int64) (word 1)) x))):int64`
and fl_ushr_pat = `word_ushr (word x:int64) 3`
and fl_sub_pat = `word_sub (word_add (a:int64) (word u)) (word (x DIV 8))`
and fl_and_pat = `word_zx (word_and (word_zx (word x:int64):int32)
                                    (word 7)):int64`
and fl_jshl_pat = `word_jshl (word_or (w:int64) (word 1)) (word (x MOD 8))`;;

let FL_RELOAD_ONE_TAC (pat,mk) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let cands = mapfilter (fun (_,th) ->
      let t = concl th in
      if is_eq t && is_comb(lhs t) && rand(lhs t) = s then
        find_term (can (term_match [] pat)) (rhs t) else fail()) asl in
    match cands with
      [] -> failwith "FL_RELOAD_ONE_TAC"
    | t::_ ->
        let _,tmi,_ = term_match [] pat t in
        let inst v = try rev_assoc v tmi with Failure _ -> v in
        let cond,eqn = mk inst in
        (SUBGOAL_THEN cond (fun cth ->
           let eth = MP eqn cth in
           RULE_ASSUM_TAC(fun th ->
             if free_in s (concl th) then REWRITE_RULE[eth] th else th))
         THENL [FL_ARITH_TAC; ALL_TAC]) gl;;

let fl_reload_rules =
  [fl_ctz_pat,
   (fun inst -> let w = inst `w:int64` and x = inst `x:num` in
      mk_binop `(<):num->num->bool` x `64`, SPECL [w; x] FAST_RELOAD_CTZ);
   fl_ushr_pat,
   (fun inst -> let x = inst `x:num` in
      mk_binop `(<):num->num->bool` x `64`, SPEC x FAST_RELOAD_USHR);
   fl_sub_pat,
   (fun inst -> let a = inst `a:int64` and u = inst `u:num`
                and x = inst `x:num` in
      let d = mk_binop `(DIV):num->num->num` x `8` in
      mk_binop `(<=):num->num->bool` d u, SPECL [a; u; d] FAST_RELOAD_SUB);
   fl_and_pat,
   (fun inst -> let x = inst `x:num` in
      mk_binop `(<):num->num->bool` x `64`, SPEC x FAST_RELOAD_AND);
   fl_jshl_pat,
   (fun inst -> let w = inst `w:int64` and x = inst `x:num` in
      `T`, DISCH `T` (SPECL [w; x] FAST_RELOAD_JSHL))];;

let FL_RELOAD_TAC = REPEAT(FIRST(map FL_RELOAD_ONE_TAC fl_reload_rules));;

(*** The 8 bytes of blk at a new pointer, for the reload ***)

let FL_WINDOW_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let pat = `word_add (ilowest:int64) (word (u - d))` in
    let ptrs = mapfilter (fun (_,th) ->
      let t = concl th in
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(_,_)),s')),p)
          when s' = s && can (term_match [] pat) p -> p
      | _ -> fail()) asl in
    let have p = exists (fun (_,th) ->
      let t = concl th in
      is_eq t && (match lhs t with
        Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
             Comb(Const("bytes64",_),p'))),s') -> p' = p && s' = s
      | _ -> false)) asl in
    match filter (not o have) ptrs with
      [] -> failwith "FL_WINDOW_TAC"
    | p::_ ->
        let off = rand(rand p) and base = lhand p in
        let bth = find (fun (_,th) -> let t = concl th in
          is_eq t && (match lhs t with
            Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
                 Comb(Const("bytes",_),ar))),s') ->
                 s' = s && fst(dest_pair ar) = base &&
                 (match rhs t with
                    Comb(Const("num_of_bytelist",_),l) -> is_var l
                  | _ -> false)
          | _ -> false)) asl in
        let th = snd bth in
        let a,n = dest_pair(rand(rand(lhand(lhs(concl th))))) in
        (MP_TAC(ISPECL [a; n; rhs(concl th); off; s] READ_MEMORY_BYTES64_SLICE)
         THEN ANTS_TAC THENL [CONJ_TAC THENL [ACCEPT_TAC th; FL_ARITH_TAC];
                              DISCH_TAC]) gl;;

(*** A byte stored after the bytes l already stored from a, merged ***)
(*** into one fact for the bytes from a                            ***)

let fl_len_conv =
  REWRITE_CONV[LENGTH; LENGTH_APPEND; HUF_DECODE_LENGTH; GSYM ADD_ASSOC] THENC
  NUM_REDUCE_CONV;;

let fl_num_norm t =
  rhs(concl((REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV) t));;

let FL_MERGE_TAC : tactic =
  let pat8 = `read (memory :> bytes8 a) (s:armstate) = (b:byte)`
  and patl = `read (memory :> bytes(a,n)) (s:armstate) = num_of_bytelist l` in
  fun (asl,w as gl) ->
    let s = rand w in
    let b8s = mapfilter (fun (_,th) ->
      let _ = term_match [] (subst [s,`s:armstate`] pat8) (concl th) in
      th) asl
    and lists = mapfilter (fun (_,th) ->
      let _ = term_match [] (subst [s,`s:armstate`] patl) (concl th) in
      th) asl in
    let base_len th = dest_pair(rand(rand(lhand(lhs(concl th))))) in
    let addr th8 = rand(rand(lhand(lhs(concl th8)))) in
    let ends_at thl a =
      let base,n = base_len thl in
      let n' = fl_num_norm n in
      if n' = `0` then a = base else
      (match a with
         Comb(Comb(Const("word_add",_),b),Comb(Const("word",_),k)) ->
           b = base && fl_num_norm k = n'
       | _ -> false) in
    let pairs = mapfilter (fun th8 ->
       let a = addr th8 in
       try let thl = find (fun thl -> ends_at thl a) lists in (th8,thl)
       with Failure _ ->
         if is_var a then
           let th0 = TRANS (ISPECL [a; s] READ_MEMORY_BYTES_0)
                           (SYM(CONJUNCT1 num_of_bytelist)) in
           (th8,th0)
         else fail()) b8s in
    match pairs with
      [] -> failwith "FL_MERGE_TAC"
    | (th8,thl)::_ ->
        let base,n = base_len thl in
        let l = rand(rhs(concl thl)) in
        let b = rhs(concl th8) in
        let lth = fl_len_conv (mk_comb(`LENGTH:byte list->num`,l)) in
        let lemma = ISPECL [base; l; b; s] READ_MEMORY_BYTELIST_SNOC in
        let lemma' = CONV_RULE(ONCE_DEPTH_CONV fl_len_conv) lemma in
        let ant1,ant2 = dest_conj(lhand(concl lemma')) in
        let prove_ant ant th =
          if aconv ant (concl th) then th else
          let eq = (REWRITE_CONV[WORD_ADD_0] THENC
                    ONCE_DEPTH_CONV fl_len_conv) ant in
          let eq' = (REWRITE_CONV[WORD_ADD_0] THENC
                     ONCE_DEPTH_CONV fl_len_conv) (concl th) in
          EQ_MP (SYM eq) (EQ_MP eq' th) in
        let th = MP lemma' (CONJ (prove_ant ant1 thl) (prove_ant ant2 th8)) in
        let th' = CONV_RULE (ONCE_DEPTH_CONV fl_len_conv) th in
        (DISCARD_ASSUMPTIONS_TAC (fun t -> concl t = concl th8 ||
                                           concl t = concl thl) THEN
         ASSUME_TAC th') gl;;

let FL_NORM_TAC = FL_INDEX_TAC THEN FL_SHIFT_TAC THEN FL_DROP_TAC THEN
                  REPEAT FL_MERGE_TAC THEN FL_RELOAD_TAC THEN
                  REPEAT FL_WINDOW_TAC THEN FL_HIDE_TAC;;

let FL_STEPS_TAC ns =
  MAP_EVERY (fun n -> ZSTD_STEP_TAC n THEN FL_NORM_TAC) ns;;

let FL_TIMED_STEPS_TAC ns =
  MAP_EVERY (fun n gl ->
    let t0 = Unix.gettimeofday() in
    let r = (ZSTD_STEP_TAC n THEN FL_NORM_TAC) gl in
    Printf.printf "STEP %d %.2f\n%!" n (Unix.gettimeofday() -. t0); r) ns;;

(*** The postcondition as an abbreviation during the simulation, which is ***)
(*** much faster with a small goal                                        ***)

let FL_ABBREV_POST_TAC : tactic =
  fun (asl,w as gl) ->
    let p = rand(rator w) in
    ABBREV_TAC (mk_eq(mk_var("fl_post",type_of p),p)) gl;;

let FL_EXPAND_POST_TAC =
  FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_eq t && is_var(rhs t) && fst(dest_var(rhs t)) = "fl_post"
    then SUBST1_TAC(SYM th) else NO_TAC) THEN BETA_TAC;;

(*** The hidden facts back as separate assumptions ***)

let FL_UNHIDE_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) &&
       not(exists (fun v -> type_of v = `:armstate`) (frees(concl th)))
    then STRIP_ASSUME_TAC th else NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* The states of the loop. The arguments are at args (the pointers at +0,    *)
(* +32 and +64, the table at +96, ilowest at +104 and oend at +112), and the *)
(* function keeps copies of the pointers in its frame of 192 bytes, where it *)
(* also saves x19 to x27, x29 and x30. In the loop, stream k is in the       *)
(* registers given by fl_streams (pointer, output pointer and container),    *)
(* with j symbols decoded and m iterations left before the number of         *)
(* iterations is worked out again, D is the size of the output of the last   *)
(* stream, oend - op[3], and the output of each stream has room for D bytes. *)
(* ------------------------------------------------------------------------- *)

(*** The fast loop: regions, hypotheses and frame ***)

let fl_rr =
 `[ilowest,LENGTH(blk:byte list); dt,4096; args,120;
   word_sub stackpointer (word 192),192]:(int64#num)list`
and fl_wr =
 `[op0,D; op1,D; op2,D; op3,D; args,96;
   word_sub stackpointer (word 192),192]:(int64#num)list`;;

let fl_regions =
 [`ilowest:int64`,`LENGTH(blk:byte list)`; `dt:int64`,`4096`;
  `args:int64`,`152`; `word_sub stackpointer (word 192):int64`,`192`;
  `word pc:int64`,`32000`];;

let fl_nonover =
  let ops = map (fun k -> mk_var("op"^string_of_int k,`:int64`),`D:num`)
                [0;1;2;3] in
  let mk (a,n) (b,m) =
    list_mk_icomb "nonoverlapping" [mk_pair(a,n); mk_pair(b,m)] in
  let rec pairs l = match l with
      [] -> [] | x::t -> map (fun y -> (x,y)) t @ pairs t in
  map (fun (x,y) -> mk x y) (pairs (ops @ fl_regions));;

let fl_hyps = list_mk_conj
 ([`aligned 4096 (word pc:int64)`; `pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml`; `LENGTH(ws:num list) <= 256`; `1 <= ml`;
   `ml <= 11`; `val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`;
   `oend:int64 = word_add op3 (word D)`; `val(op3:int64) + D < 2 EXP 64`] @
  fl_nonover);;

let fl_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `args:int64`;
  `blk:byte list`; `ilowest:int64`; `dt:int64`; `oend:int64`; `D:num`;
  `op0:int64`; `op1:int64`; `op2:int64`; `op3:int64`;
  `p0:num`; `p1:num`; `p2:num`; `p3:num`; `ws:num list`; `ml:num`;
  `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`; `x23:int64`;
  `x24:int64`; `x25:int64`; `x26:int64`; `x27:int64`; `x29:int64`;
  `e:uarch_event list`];;


(*** The state of stream k: its pointer, output pointer and container in ***)
(*** the registers given, the bytes decoded, and the position            ***)

let fl_stream k (ipr,opr,cr) =
  let n = string_of_int k in
  let u = mk_var("u"^n,`:num`) and sk = mk_var("s"^n,`:num`)
  and op = mk_var("op"^n,`:int64`) and p = mk_var("p"^n,`:num`) in
  let dec = list_mk_icomb "huf_decode"
              [`ws:num list`; `ml:num`; `blk:byte list`; p; `j:num`] in
  let t = subst [u,`u:num`; sk,`sk:num`; op,`op:int64`;
                 dec,`dec:byte list#num#bool`; fl_cont u sk,`c:int64`]
   `read IPR s = word_add (ilowest:int64) (word u) /\
    read OPR s = word_add (op:int64) (word j) /\
    read CR s = (c:int64) /\
    read (memory :> bytes(op,j)) s = num_of_bytelist(FST dec) /\
    FST(SND dec) = 8 * u + 64 - sk /\ SND(SND dec) /\
    sk <= 8 /\ u + 8 <= LENGTH(blk:byte list) /\ 7 * m <= u` in
  subst [ipr,`IPR:(armstate,int64)component`;
         opr,`OPR:(armstate,int64)component`;
         cr,`CR:(armstate,int64)component`] t;;

let fl_streams =
  [`X10`,`X9`,`X25`; `X11`,`X8`,`X3`; `X12`,`X7`,`X2`; `X13`,`X6`,`X1`];;

(*** The fast loop with its frame of 192 bytes on the stack: the saved ***)
(*** registers and the pointers to the copies of the arguments         ***)

let fl_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X29; X30; SP] ,,
  MAYCHANGE [memory :> bytes(op0,D); memory :> bytes(op1,D);
             memory :> bytes(op2,D); memory :> bytes(op3,D);
             memory :> bytes(args,96);
             memory :> bytes(word_sub stackpointer (word 192),192)]`;;

let mk_fl_goal_hyps hyps extra pre post =
  let tm = mk_imp(list_mk_conj(fl_hyps :: hyps),
                  list_mk_icomb "ensures" [`arm`; pre; post; fl_frame]) in
  let vs = fl_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fl_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let mk_fl_goal = mk_fl_goal_hyps [];;

(*** The frame of 192 bytes from 0x24a4: the copies of the arguments in ***)
(*** registers, and the registers saved, the second ones at 0x2544      ***)

let fl_spk k =
  let sp = `word_sub stackpointer (word 192):int64` in
  if k = 0 then sp
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,sp),
               mk_comb(`word:num->int64`,mk_small_numeral k));;

let fl_saved1 =
  [0,`x29:int64`; 8,`returnaddress:int64`; 16,`x19:int64`; 24,`x20:int64`;
   32,`x21:int64`; 40,`x22:int64`]
and fl_saved2 =
  [48,`x23:int64`; 56,`x24:int64`; 64,`x25:int64`; 72,`x26:int64`;
   80,`x27:int64`];;

let fl_stack_fact (k,v) =
  subst [fl_spk k,`a:int64`; v,`v:int64`]
    `read (memory :> bytes64 a) s = (v:int64)`;;

let fl_frame_facts = list_mk_conj
 ([`read SP s = word_sub stackpointer (word 192)`;
   mk_eq(`read X15 s`,fl_spk 160); mk_eq(`read X16 s`,fl_spk 128);
   mk_eq(`read X17 s`,fl_spk 96);
   `read X21 s = word_add args (word 32)`;
   `read X22 s = word_add args (word 64)`] @
  map fl_stack_fact fl_saved1);;

let fl_saved2_facts = list_mk_conj(map fl_stack_fact fl_saved2);;

(*** The loop, at 0x2588 and 0x2798, with the stack ***)

let fl_common = list_mk_conj
 [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
   read X5 s = dt /\ read X30 s = ilowest /\ read X18 s = oend /\
   read X19 s = word 0x2492492492492493 /\
   read X20 s = word 0xcccccccccccccccd /\
   read X14 s = word_add op3 (word (j + 5 * m)) /\ j + 5 * m <= D /\
   read X0 s = args /\
   read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
   num_of_bytelist blk /\
   read (memory :> bytes(dt,4096)) s = num_of_bytelist(huf_dtable ws ml 11)`;
  fl_frame_facts; fl_saved2_facts];;

let mk_fl_state pcoff =
  let pct = subst [mk_small_numeral pcoff,`k:num`]
                  `read PC s = word(pc + k)` in
  let body = list_mk_conj
    (pct :: fl_common ::
     map2 fl_stream [0;1;2;3] fl_streams) in
  let ex = list_mk_exists
    ([`u0:num`; `u1:num`; `u2:num`; `u3:num`;
      `s0:num`; `s1:num`; `s2:num`; `s3:num`],body) in
  with_memsafe fl_rr fl_wr (list_mk_abs([`j:num`; `m:num`; `s:armstate`],ex));;

let fl_body_pre = mk_fl_state 0x2588 and fl_body_post = mk_fl_state 0x2798;;

let fl_body_goal = mk_fl_goal_hyps [`1 <= m`] [`j:num`; `m:num`]
  (mk_abs(`s:armstate`,
      list_mk_comb(fl_body_pre,[`j:num`; `m:num`; `s:armstate`])))
  (mk_abs(`s:armstate`,
      list_mk_comb(fl_body_post,[`j + 5`; `m - 1`; `s:armstate`])));;

(*** The entry at 0x24a4 ***)

let fl_args_in =
 `read (memory :> bytes64 (word_add args (word 32))) s = op0 /\
  read (memory :> bytes64 (word_add args (word 40))) s = op1 /\
  read (memory :> bytes64 (word_add args (word 48))) s = op2 /\
  read (memory :> bytes64 (word_add args (word 56))) s = op3 /\
  read (memory :> bytes64 (word_add args (word 96))) s = dt /\
  read (memory :> bytes64 (word_add args (word 104))) s = ilowest /\
  read (memory :> bytes64 (word_add args (word 112))) s = oend`;;

let fl_field n =
  if n = 0 then `args:int64`
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,`args:int64`),
               mk_comb(`word:num->int64`,mk_small_numeral n));;

let fl_args_streams =
  let ip k = mk_var("u"^string_of_int k,`:num`)
  and sh k = mk_var("s"^string_of_int k,`:num`) in
  let one k =
    let p = mk_var("p"^string_of_int k,`:num`) in
    subst [fl_field(8 * k),`a8:int64`; fl_field(64 + 8 * k),`a64:int64`;
           ip k,`u:num`; sh k,`x:num`;
           fl_cont (ip k) (sh k),`c:int64`; p,`p:num`]
     `read (memory :> bytes64 a8) s = word_add (ilowest:int64) (word u) /\
      read (memory :> bytes64 a64) s = (c:int64) /\
      p = 8 * u + 64 - x /\ x <= 8 /\ u + 8 <= LENGTH(blk:byte list)` in
  list_mk_conj(map one [0;1;2;3]);;

let fl_top_pre =
  let body = list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x24a4) /\ read SP s = stackpointer /\
     read X30 s = returnaddress /\ read X0 s = args /\
     read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
     read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
     read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
     read X29 s = x29 /\
     read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
     num_of_bytelist blk /\
     read (memory :> bytes(dt,4096)) s =
     num_of_bytelist(huf_dtable ws ml 11)`;
    fl_args_in;
    list_mk_exists
     ([`u0:num`; `u1:num`; `u2:num`; `u3:num`;
       `s0:num`; `s1:num`; `s2:num`; `s3:num`],fl_args_streams);
    `read events s = e`] in
  mk_abs(`s:armstate`,body);;

(*** The return: the registers restored, and for each stream its pointer, ***)
(*** output pointer and container in the arguments, after the j bytes     ***)
(*** decoded                                                              ***)

let fl_out_stream k =
  let n = string_of_int k in
  let u = mk_var("u"^n,`:num`) and sk = mk_var("s"^n,`:num`)
  and op = mk_var("op"^n,`:int64`) and p = mk_var("p"^n,`:num`) in
  let dec = list_mk_icomb "huf_decode"
              [`ws:num list`; `ml:num`; `blk:byte list`; p; `j:num`] in
  subst [fl_field(8 * k),`aip:int64`; fl_field(32 + 8 * k),`aop:int64`;
         fl_field(64 + 8 * k),`abits:int64`;
         u,`u:num`; sk,`sk:num`; op,`op:int64`;
         dec,`dec:byte list#num#bool`; fl_cont u sk,`c:int64`]
   `read (memory :> bytes64 aip) s = word_add (ilowest:int64) (word u) /\
    read (memory :> bytes64 aop) s = word_add (op:int64) (word j) /\
    read (memory :> bytes64 abits) s = (c:int64) /\
    read (memory :> bytes(op,j)) s = num_of_bytelist(FST dec) /\
    FST(SND dec) = 8 * u + 64 - sk /\ SND(SND dec) /\
    sk <= 8 /\ u + 8 <= LENGTH(blk:byte list)`;;

let fl_top_post =
  let ex = list_mk_exists
    ([`j:num`; `u0:num`; `u1:num`; `u2:num`; `u3:num`;
      `s0:num`; `s1:num`; `s2:num`; `s3:num`],
     list_mk_conj(`j <= D` :: map fl_out_stream [0;1;2;3])) in
  with_memsafe fl_rr fl_wr (mk_abs(`s:armstate`,list_mk_conj
   [`read PC s = returnaddress /\ read SP s = stackpointer /\
     read X0 s = args /\
     read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
     read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
     read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
     read X29 s = x29 /\ read X30 s = returnaddress`; ex]));;

let fl_top_goal = mk_fl_goal [] fl_top_pre fl_top_post;;

(*** The 128-bit reads of the ldp of q registers, from the 64-bit facts ***)

let FL_JOIN128_TAC (addrs:term list) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let r64 = filter (fun (_,th) -> let t = concl th in
      is_eq t && (match lhs t with
        Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
             Comb(Const("bytes64",_),_))),s') -> s' = s
      | _ -> false)) asl in
    let ths = map snd r64 in
    let one a =
      let t = subst [a,`a:int64`; s,`s:armstate`]
                `read (memory :> bytes128 a) s` in
      CONV_RULE(RAND_CONV(REWRITE_CONV ths)) (READ_MEMORY_MERGE_CONV 1 t) in
    MAP_EVERY (ASSUME_TAC o one) addrs gl;;

(*** The 64-bit reads of what a stp of q registers stored ***)

let FL_SPLIT128_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let r128 = mapfilter (fun (_,th) -> let t = concl th in
      if is_eq t && (match lhs t with
        Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
             Comb(Const("bytes128",_),_))),s') -> s' = s
      | _ -> false) then th else fail()) asl in
    let one th =
      CONV_RULE(BINOP_CONV(BINOP2_CONV
        (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
        (REWRITE_CONV[WORD_SUBWORD_JOIN_64])))
       (GEN_REWRITE_RULE I
          [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] th) in
    MAP_EVERY (STRIP_ASSUME_TAC o one) r128 gl;;

(*** The streams without the bound of the iterations, for the exit ***)

let fl_stream_x k regs =
  let t = fl_stream k regs in
  list_mk_conj(butlast(conjuncts t));;

(*** The exit at 0x27dc, with the streams in registers ***)

let fl_exit_pre =
  let body = list_mk_conj
   ([`read PC s = word(pc + 0x27dc)`;
     `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read X0 s = args /\ j <= D`;
     fl_frame_facts; fl_saved2_facts] @
    map2 fl_stream_x [0;1;2;3] fl_streams) in
  let ex = list_mk_exists
    ([`u0:num`; `u1:num`; `u2:num`; `u3:num`;
      `s0:num`; `s1:num`; `s2:num`; `s3:num`],body) in
  with_memsafe fl_rr fl_wr (list_mk_abs([`s:armstate`],ex));;

(*** The exit at 0x280c, with the streams in the copies on the stack ***)

let fl_local_stream k =
  let n = string_of_int k in
  let u = mk_var("u"^n,`:num`) and sk = mk_var("s"^n,`:num`)
  and op = mk_var("op"^n,`:int64`) and p = mk_var("p"^n,`:num`) in
  let dec = list_mk_icomb "huf_decode"
              [`ws:num list`; `ml:num`; `blk:byte list`; p; `j:num`] in
  subst [fl_spk(128 + 8 * k),`aip:int64`; fl_spk(160 + 8 * k),`aop:int64`;
         fl_spk(96 + 8 * k),`abits:int64`;
         u,`u:num`; sk,`sk:num`; op,`op:int64`;
         dec,`dec:byte list#num#bool`; fl_cont u sk,`c:int64`]
   `read (memory :> bytes64 aip) s = word_add (ilowest:int64) (word u) /\
    read (memory :> bytes64 aop) s = word_add (op:int64) (word j) /\
    read (memory :> bytes64 abits) s = (c:int64) /\
    read (memory :> bytes(op,j)) s = num_of_bytelist(FST dec) /\
    FST(SND dec) = 8 * u + 64 - sk /\ SND(SND dec) /\
    sk <= 8 /\ u + 8 <= LENGTH(blk:byte list)`;;

let fl_exit0_pre =
  let body = list_mk_conj
   ([`read PC s = word(pc + 0x280c)`;
     `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read X0 s = args /\ j <= D /\
      read X23 s = x23 /\ read X24 s = x24 /\ read X25 s = x25 /\
      read X26 s = x26 /\ read X27 s = x27`;
     fl_frame_facts] @
    map fl_local_stream [0;1;2;3]) in
  let ex = list_mk_exists
    ([`u0:num`; `u1:num`; `u2:num`; `u3:num`;
      `s0:num`; `s1:num`; `s2:num`; `s3:num`],body) in
  with_memsafe fl_rr fl_wr (list_mk_abs([`s:armstate`],ex));;

let fl_exit0_goal = mk_fl_goal [`j:num`] fl_exit0_pre fl_top_post;;
let fl_exit_goal = mk_fl_goal [`j:num`] fl_exit_pre fl_top_post;;

(* ------------------------------------------------------------------------- *)
(* The body of the loop, from 0x2588 to 0x2798: 5 symbols of each stream and *)
(* the reloads (FL_BODY).                                                    *)
(* ------------------------------------------------------------------------- *)

(*** After the body: the five symbols of each stream decoded, as steps of ***)
(*** huf_decode, from the facts of the lookups                            ***)

let fl_all_facts asl =
  itlist (fun (_,th) acc -> CONJUNCTS th @ acc) asl [];;

let FL_DECODE5_TAC (u:term) (p:term) : tactic =
  fun (asl,w as gl) ->
    let facts = fl_all_facts asl in
    let sympat =
      `huf_symbol ws (zstd_back (blk:byte list) (8 * u + 64 - x) ml) = sym` in
    let syms = mapfilter (fun th ->
      let _,tmi,_ = term_match [] sympat (concl th) in
      let inst v = try rev_assoc v tmi with Failure _ -> v in
      if inst `u:num` = u then (inst `x:num`,inst `sym:num`,th) else fail())
      facts in
    let size x = length(striplist (dest_binop `(+):num->num->num`) x) in
    let syms = sort (fun (x,_,_) (y,_,_) -> size x < size y) syms in
    let nbth sym = find (fun th -> let t = concl th in
      is_eq t && lhs t = subst [sym,`t:num`] `(ml + 1) - EL t ws`) facts in
    let nbleth nb = find (fun th -> concl th =
      mk_binop `(<=):num->num->bool` nb `ml:num`) facts in
    let jnorm t = rhs(concl((REWRITE_CONV[GSYM ADD_ASSOC] THENC
                             NUM_REDUCE_CONV) t)) in
    let step (jt,tac) (x,sym,sth) =
      let nbe = nbth sym in
      let nb = rhs(concl nbe) in
      let jt' = jnorm(mk_binop `(+):num->num->num` jt `1`) in
      let dec j = list_mk_icomb "huf_decode"
                    [`ws:num list`; `ml:num`; `blk:byte list`; p; j] in
      let posth = mk_eq(mk_icomb(`FST:num#bool->num`,
                          mk_icomb(`SND:byte list#num#bool->num#bool`,dec jt)),
                        subst [u,`u:num`; x,`x:num`] `8 * u + 64 - x`) in
      let okth = mk_icomb(`SND:num#bool->bool`,
                   mk_icomb(`SND:byte list#num#bool->num#bool`,dec jt)) in
      let xle = mk_binop `(<=):num->num->bool` x `52` in
      let tac' =
        tac THEN
        SUBGOAL_THEN xle ASSUME_TAC THENL [FL_LE_TAC; ALL_TAC] THEN
        MP_TAC(SPECL [`ws:num list`; `ml:num`; `blk:byte list`; p; jt; u; x;
                      sym; nb] HUF_DECODE_FAST_STEP) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN
          FIRST [FIRST_ASSUM ACCEPT_TAC; ACCEPT_TAC sth; ACCEPT_TAC nbe;
                 ACCEPT_TAC(nbleth nb)];
          ALL_TAC] THEN
        CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV
          (fun t -> if t = mk_binop `(+):num->num->num` jt `1`
                    then (REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV) t
                    else failwith ""))) THEN
        STRIP_TAC in
      ignore posth; ignore okth;
      (jt',tac') in
    let _,tac =
      itlist (fun s acc -> step acc s) (rev syms) (`j:num`,ALL_TAC) in
    tac gl;;

(*** The post of the body: the new u and s of each stream from its ***)
(*** pointer register, and the conjuncts                           ***)

let FL_BODY_POST_TAC (s:term) =
  let ipregs = [`X10`; `X11`; `X12`; `X13`] in
  W(fun (asl,w) ->
    let ipval r = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
        is_eq t && lhs t = list_mk_icomb "read" [r; s]) asl))) in
    let offs = map (fun r -> rand(rand(ipval r))) ipregs in
    let ts = map (fun o' -> lhand(rand o')) offs in
    let us = [`u0:num`; `u1:num`; `u2:num`; `u3:num`]
    and ps = [`p0:num`; `p1:num`; `p2:num`; `p3:num`] in
    MAP_EVERY (fun (u,p) -> FL_DECODE5_TAC u p) (zip us ps) THEN
    (fun (asl,w as gl) ->
       if is_conj w then (CONJ_TAC THENL [ALL_TAC; MONOTONE_MAYCHANGE_TAC]) gl
       else ALL_TAC gl) THEN
    MAP_EVERY EXISTS_TAC offs THEN
    MAP_EVERY (fun t -> EXISTS_TAC (mk_binop `(MOD):num->num->num` t `8`))
      ts THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV));;

(*** The conjuncts of the post of the body ***)

let FL_BODY_CONJ_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         AP_TERM_TAC THEN AP_TERM_TAC THEN FL_ARITH_TAC;
         ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN NO_TAC;
         ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
           FL_ARITH_TAC;
         FL_ARITH_TAC];;

let FL_BODY_SIM_TAC =
  ZSTD_INTRO_TAC THEN
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v)
    [`u0:num`; `u1:num`; `u2:num`; `u3:num`;
     `s0:num`; `s1:num`; `s2:num`; `s3:num`] THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `7 <= u0 /\ 7 <= u1 /\ 7 <= u2 /\ 7 <= u3 /\ j + 5 <= D`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`7 * m <= u0`; `7 * m <= u1`; `7 * m <= u2`;
                           `7 * m <= u3`; `1 <= m`; `j + 5 * m <= D`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (fun gl -> fl_counter := 0; ALL_TAC gl) THEN
  FL_STEPS_TAC (1--132) THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC;;

(*** The body ***)

let FL_BODY = prove
 (fl_body_goal,
  FL_BODY_SIM_TAC THEN FL_BODY_POST_TAC `s132:armstate` THEN
  FL_BODY_CONJ_TAC);;

(* ------------------------------------------------------------------------- *)
(* The exits: at 0x27dc the registers are copied to the copies in the frame, *)
(* and at 0x280c the copies are copied back to the arguments, the registers  *)
(* restored, and the function returns (FL_EXIT, FL_EXIT0).                   *)
(* ------------------------------------------------------------------------- *)

(*** The exits of the fast loop ***)

let FL_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 192)) (word 192):int64 =
  stackpointer`;;

let fl_uvars =
  [`u0:num`; `u1:num`; `u2:num`; `u3:num`;
   `s0:num`; `s1:num`; `s2:num`; `s3:num`];;

let FL_STREAMS_PRE_TAC =
  MAP_EVERY (fun v -> ENSURES_EXISTS_PRE_TAC v) fl_uvars;;

let FL_POST_TAC =
  ASM_REWRITE_TAC[FL_SP_RESTORE] THEN
  MAP_EVERY EXISTS_TAC (`j:num` :: fl_uvars) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN REWRITE_TAC[];;

(*** 0x280c: the copies on the stack to the arguments, the registers ***)
(*** restored, the return                                            ***)

let FL_EXIT0 = prove
 (fl_exit0_goal,
  ZSTD_INTRO_TAC THEN FL_STREAMS_PRE_TAC THEN PUFF_INIT_TAC "s0" THEN
  FL_JOIN128_TAC (map fl_spk [96; 112; 128; 144; 160; 176]) THEN
  ZSTD_STEPS_TAC (1--6) THEN FL_SPLIT128_TAC THEN
  ZSTD_STEPS_TAC (7--10) THEN PUFF_FINAL_TAC THEN FL_POST_TAC);;

(*** 0x27dc: the streams copied from the registers to the stack, the ***)
(*** second registers saved restored, and on to 0x280c               ***)

let FL_PRE_TAC =
  MAP_EVERY EXISTS_TAC fl_uvars THEN MEMSAFE_ELIM_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[];;

let FL_EXIT = prove
 (fl_exit_goal,
  ZSTD_INTRO_TAC THEN FL_STREAMS_PRE_TAC THEN PUFF_INIT_TAC "s0" THEN
  ZSTD_STEPS_TAC (1--12) THEN ZSTD_CONTINUE_TAC FL_EXIT0 [] THEN
  FL_PRE_TAC);;

(* ------------------------------------------------------------------------- *)
(* After the body (0x2798, FL_NEXT): the loop goes on if m > 0; otherwise    *)
(* the number of iterations is worked out again, as the minimum of (ip[0] -  *)
(* ilowest) / 7 and (oend - op[3]) / 5, the divisions being by               *)
(* multiplication (umulh) and shifts, and if it is not 0 and the pointers    *)
(* are in order, the loop goes on, and otherwise the function exits.         *)
(* ------------------------------------------------------------------------- *)

(*** The divisions by 7 and by 5 of the fast loop, by multiplication ***)

let DIV7_MAGIC = prove
 (`!a. a < 2 EXP 64
       ==> ((a - (a * 2635249153387078803) DIV 2 EXP 64) DIV 2 +
             (a * 2635249153387078803) DIV 2 EXP 64) DIV 4 = a DIV 7`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = (a * 2635249153387078803) DIV 2 EXP 64` THEN
  MP_TAC(SPECL [`a * 2635249153387078803`; `2 EXP 64`] DIVISION) THEN
  ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `7`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `q = a DIV 7` THEN ABBREV_TAC `r = a MOD 7` THEN STRIP_TAC THEN
  SUBGOAL_THEN `t = q \/ t = q + 1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `a < 2 EXP 64` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let DIV5_MAGIC = prove
 (`!b. b < 2 EXP 64
       ==> ((b * 14757395258967641293) DIV 2 EXP 64) DIV 4 = b DIV 5`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = (b * 14757395258967641293) DIV 2 EXP 64` THEN
  MP_TAC(SPECL [`b * 14757395258967641293`; `2 EXP 64`] DIVISION) THEN
  ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:num`; `5`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `q = b DIV 5` THEN ABBREV_TAC `r = b MOD 5` THEN STRIP_TAC THEN
  UNDISCH_TAC `b < 2 EXP 64` THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** The number of iterations: the divisions by 7 and by 5 of the code ***)

let FL_DIV7 = prove
 (`!u. u < 2 EXP 64
       ==> word_ushr
            (word_add
              (word ((val(word u:int64) * 2635249153387078803) DIV
                     18446744073709551616))
              (word_ushr
                (word_sub (word u)
                  (word ((val(word u:int64) * 2635249153387078803) DIV
                         18446744073709551616))) 1)) 2 =
           word(u DIV 7):int64`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_LT64] THEN
  ABBREV_TAC `t = (u * 2635249153387078803) DIV 18446744073709551616` THEN
  SUBGOAL_THEN `t <= u` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN SIMP_TAC[LE_LDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `u < 2 EXP 64` THEN UNDISCH_TAC `t <= u` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `t + (u - t) DIV 2 < 18446744073709551616 /\
                u DIV 7 < 18446744073709551616`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`u < 2 EXP 64`; `t <= u`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]] THEN
  MP_TAC(SPEC `u:num` DIV7_MAGIC) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let FL_DIV5 = prove
 (`!d. d < 2 EXP 64
       ==> word_ushr
            (word ((val(word d:int64) * 14757395258967641293) DIV
                   18446744073709551616)) 2 =
           word(d DIV 5):int64`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_LT64] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(d * 14757395258967641293) DIV 18446744073709551616 <
                18446744073709551616 /\ d DIV 5 < 18446744073709551616`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN UNDISCH_TAC `d < 2 EXP 64` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]] THEN
  MP_TAC(SPEC `d:num` DIV5_MAGIC) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(*** After the body: the loop goes on, or the number of iterations is ***)
(*** worked out again, and the loop goes on after the checks or ends  ***)

let fl_beta t = rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

let fl_st pre j m =
  fl_beta(list_mk_comb(pre,[j; m; `s:armstate`]));;

let fl_next_goal = fl_beta(mk_fl_goal [`j:num`; `m:num`]
  (mk_abs(`s:armstate`,fl_st fl_body_post `j:num` `m:num`))
  (mk_abs(`s:armstate`,
     mk_disj(mk_exists(`m':num`,
               mk_conj(`1 <= m'`,fl_st fl_body_pre `j:num` `m':num`)),
             fl_beta(mk_comb(fl_top_post,`s:armstate`))))));;

let fl_loop_goal = fl_beta(mk_fl_goal_hyps [`1 <= m`] [`j:num`; `m:num`]
  (mk_abs(`s:armstate`,fl_st fl_body_pre `j:num` `m:num`))
  fl_top_post);;

(*** Simple rules for ensures ***)

let ENSURES_PRE_FACT = prove
 (`!(P:A->bool) Q C p.
        (!s. P s ==> p) /\ (p ==> ensures step P Q C)
        ==> ensures step P Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let ENSURES_DISJ_DONE = prove
 (`!(P:num->A->bool) Q C.
        (=) subsumed C /\ (!m. ensures step (P m) Q C)
        ==> ensures step (\s. (?m. P m s) \/ Q s) Q C`,
  REWRITE_TAC[ensures; subsumed] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    GEN_REWRITE_TAC I [eventually_CASES] THEN ASM_MESON_TAC[]]);;

let ENSURES_PRE_PURE = prove
 (`!(P:A->bool) Q C p.
        (p ==> ensures step P Q C) ==> ensures step (\s. p /\ P s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

(*** The smaller of the two numbers of iterations, by the csel with ls ***)

let FL_CSEL_MIN = prove
 (`!a b. a < 2 EXP 64 /\ b < 2 EXP 64
         ==> (if ~(val(word b:int64) <= val(word a:int64) /\
                   ~(val(word_sub (word a) (word b):int64) = 0))
              then word a else word b) = word(MIN a b):int64`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_LT64; VAL_EQ_0; WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `(word a:int64 = word b) <=> a = b` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD_LT64]; ALL_TAC] THEN
  REWRITE_TAC[MIN] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC);;

let FL_TIMES5 = prove
 (`!m. word_add (word m) (word_shl (word m) 2):int64 = word(5 * m)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD;
              DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** The step after the body: FL_NEXT ***)

let FL_SUB_OP = prove
 (`!(a:int64) d j. j <= d
     ==> word_sub (word_add a (word d)) (word_add a (word j)) = word(d - j)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let FL_X14_TAC =
  let r1 = ARITH_RULE `!a b. a + b + 4 * b = a + 5 * b`
  and r2 = ARITH_RULE `!b. b + 4 * b = 5 * b` in
  W(fun (asl,w) ->
    let s = rand w in
    let rd = list_mk_icomb "read" [`X14`; s] in
    FIRST_X_ASSUM(fun th ->
      let t = concl th in
      if is_eq t && lhs t = rd then
        ASSUME_TAC(REWRITE_RULE[FL_TIMES5; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                                r1; r2] th)
      else NO_TAC));;

let FL_IPVAL_TAC =
  MAP_EVERY (fun u ->
    let th = SPECL [`ilowest:int64`; u] VAL_WORD_ADD_NOWRAP in
    MP_TAC th THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [subst [u,`u:num`] `u + 8 <= LENGTH(blk:byte list)`;
        `val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`] THEN
      ARITH_TAC;
      DISCH_TAC])
  [`u0:num`; `u1:num`; `u2:num`; `u3:num`];;

let FL_NEXT_EXIT_TAC =
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN
                          ASM_REWRITE_TAC[]) FL_EXIT [] THEN
  FL_PRE_TAC;;

let FL_SUBST_ZERO_TAC v =
  FIRST_X_ASSUM(fun th -> if concl th = mk_eq(v,`0`) then SUBST_ALL_TAC th
                          else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]);;

(*** The new number of iterations m' from u0 / 7 and (D - j) / 5 ***)

let FL_NEXT_ITERS_TAC =
  SUBGOAL_THEN `u0 < 2 EXP 64 /\ D - j < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`u0 + 8 <= LENGTH(blk:byte list)`;
      `val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`;
      `val(op3:int64) + D < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `u0:num` FL_DIV7) (ASSUME `u0 < 2 EXP 64`);
    MP (SPEC `D - j:num` FL_DIV5) (ASSUME `D - j < 2 EXP 64`)]) THEN
  SUBGOAL_THEN `u0 DIV 7 < 2 EXP 64 /\ (D - j) DIV 5 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`u0 < 2 EXP 64`; `D - j < 2 EXP 64`] THEN
    MP_TAC(SPECL [`u0:num`; `7`] DIV_LE) THEN
    MP_TAC(SPECL [`D - j:num`; `5`] DIV_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`(D - j) DIV 5`; `u0 DIV 7`] FL_CSEL_MIN)
       (CONJ (ASSUME `(D - j) DIV 5 < 2 EXP 64`)
             (ASSUME `u0 DIV 7 < 2 EXP 64`))]) THEN
  ABBREV_TAC `m' = MIN ((D - j) DIV 5) (u0 DIV 7)` THEN
  SUBGOAL_THEN `7 * m' <= u0 /\ j + 5 * m' <= D` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m'" THEN
    MP_TAC(SPECL [`u0:num`; `7`] DIV_MUL_LE) THEN
    MP_TAC(SPECL [`D - j:num`; `5`] DIV_MUL_LE) THEN
    MP_TAC(ARITH_RULE `MIN ((D - j) DIV 5) (u0 DIV 7) <= (D - j) DIV 5 /\
                       MIN ((D - j) DIV 5) (u0 DIV 7) <= u0 DIV 7`) THEN
    UNDISCH_TAC `j <= D` THEN ARITH_TAC;
    ALL_TAC];;

(*** The checks of the order of the pointers of the streams at 0x2570, ***)
(*** from step k, after which the loop goes on or ends                 ***)

let FL_CHECKS_TAC k pass_tac fail_tac =
  FL_IPVAL_TAC THEN
  ASM_CASES_TAC `u0 <= u1` THENL
   [ASM_CASES_TAC `u1 <= u2` THENL
     [ASM_CASES_TAC `u2 <= u3` THENL
       [ZSTD_STEPS_TAC (k--(k+5)) THEN pass_tac;
        ZSTD_STEPS_TAC (k--(k+6)) THEN fail_tac];
      ZSTD_STEPS_TAC (k--(k+4)) THEN fail_tac];
    ZSTD_STEPS_TAC (k--(k+2)) THEN fail_tac];;

let FL_NEXT_PASS_TAC =
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `m':num` THEN
  CONJ_TAC THENL [UNDISCH_TAC `~(m' = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC fl_uvars THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`7 * m' <= u0`; `u0 <= u1`; `u1 <= u2`; `u2 <= u3`] THEN
  ARITH_TAC;;

let FL_NEXT = prove
 (fl_next_goal,
  ZSTD_INTRO_TAC THEN FL_STREAMS_PRE_TAC THEN PUFF_INIT_TAC "s0" THEN
  ASM_CASES_TAC `m = 0` THENL
   [FL_SUBST_ZERO_TAC `m:num` THEN ZSTD_STEPS_TAC (1--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`op3:int64`; `D:num`; `j:num`]
      FL_SUB_OP) (ASSUME `j <= D`)]) THEN
    ZSTD_STEPS_TAC (5--13) THEN FL_NEXT_ITERS_TAC THEN
    ZSTD_STEPS_TAC [14] THEN FL_X14_TAC THEN
    ZSTD_STEPS_TAC [15] THEN FL_X14_TAC THEN
    ASM_CASES_TAC `m' = 0` THENL
     [FL_SUBST_ZERO_TAC `m':num` THEN ZSTD_STEPS_TAC (16--17) THEN
      FL_NEXT_EXIT_TAC;
      ZSTD_STEPS_TAC (16--17) THEN
      FL_CHECKS_TAC 18 FL_NEXT_PASS_TAC FL_NEXT_EXIT_TAC];
    ZSTD_STEPS_TAC (1--2) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `m:num` THEN
    CONJ_TAC THENL [UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC fl_uvars THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The loop from 0x2588 to the return, by induction on D - j (FL_LOOP), and  *)
(* the entry at 0x24a4, which copies the arguments, works out the first      *)
(* number of iterations and checks the order of the pointers (FL_TOP).       *)
(* ------------------------------------------------------------------------- *)

(*** The loop from 0x2588 to the return, by induction on D - j ***)

let FL_FRAME_RULE =
  REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
               MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS];;

let FL_ACCEPT_TAC th =
  MP_TAC(FL_FRAME_RULE(CONV_RULE(TOP_DEPTH_CONV BETA_CONV) th)) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[];;

let FL_LOOP = prove
 (fl_loop_goal,
  ZSTD_INTRO_TAC THEN
  W(fun (asl,w) ->
    let gen = list_mk_forall([`n:num`; `j:num`; `m:num`],
                mk_imp(`D - j = n /\ 1 <= m`,w)) in
    SUBGOAL_THEN gen (fun th -> MATCH_MP_TAC th THEN
                                EXISTS_TAC `D - j:num` THEN
                                ASM_REWRITE_TAC[])) THEN
  UNDISCH_TAC `1 <= m` THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `m:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRE_FACT THEN EXISTS_TAC `j + 5 * m <= D` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (mk_abs(`s:armstate`,fl_st fl_body_post `j + 5` `m - 1`)) THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; FL_ACCEPT_TAC(SPEC_ALL FL_BODY); ALL_TAC] THEN
  W(fun (asl,w) ->
    let th = INST [`j + 5`,`j:num`; `m - 1`,`m:num`] (SPEC_ALL FL_NEXT) in
    let q = rand(rator(rand(concl th))) in
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q THEN
    REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC; FL_ACCEPT_TAC th; ALL_TAC]) THEN
  MATCH_MP_TAC ENSURES_DISJ_DONE THEN
  CONJ_TAC THENL [SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m':num` THEN BETA_TAC THEN
  MATCH_MP_TAC ENSURES_PRE_PURE THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `D - (j + 5)`) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`D - j = n`; `1 <= m`; `j + 5 * m <= D`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`j + 5`; `m':num`]) THEN
  ASM_REWRITE_TAC[]);;

(*** The entry at 0x24a4: the copies of the arguments, the number of ***)
(*** iterations and the checks, then the loop                        ***)

let FL_PINSTS =
  map (fun k -> let n = string_of_int k in
         subst [mk_var("u"^n,`:num`),`u:num`; mk_var("s"^n,`:num`),`x:num`]
           `8 * u + 64 - x`, mk_var("p"^n,`:num`)) [0;1;2;3];;

let FL_PRE0_TAC =
  MAP_EVERY EXISTS_TAC fl_uvars THEN MEMSAFE_ELIM_TAC THEN
  REWRITE_TAC[huf_decode; FST; SND; WORD_ADD_0; ADD_CLAUSES; MULT_CLAUSES;
              READ_MEMORY_BYTES_0; num_of_bytelist; LE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[];;

let FL_TOP_ITERS_TAC =
  SUBGOAL_THEN `u0 < 2 EXP 64 /\ D < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`u0 + 8 <= LENGTH(blk:byte list)`;
      `val(ilowest:int64) + LENGTH(blk:byte list) < 2 EXP 64`;
      `val(op3:int64) + D < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `u0:num` FL_DIV7) (ASSUME `u0 < 2 EXP 64`);
    MP (SPEC `D:num` FL_DIV5) (ASSUME `D < 2 EXP 64`)]) THEN
  SUBGOAL_THEN `u0 DIV 7 < 2 EXP 64 /\ D DIV 5 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`u0 < 2 EXP 64`; `D < 2 EXP 64`] THEN
    MP_TAC(SPECL [`u0:num`; `7`] DIV_LE) THEN
    MP_TAC(SPECL [`D:num`; `5`] DIV_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPECL [`u0 DIV 7`; `D DIV 5`] FL_CSEL_MIN)
       (CONJ (ASSUME `u0 DIV 7 < 2 EXP 64`)
             (ASSUME `D DIV 5 < 2 EXP 64`))]) THEN
  ABBREV_TAC `m = MIN (u0 DIV 7) (D DIV 5)` THEN
  SUBGOAL_THEN `7 * m <= u0 /\ 5 * m <= D` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    MP_TAC(SPECL [`u0:num`; `7`] DIV_MUL_LE) THEN
    MP_TAC(SPECL [`D:num`; `5`] DIV_MUL_LE) THEN
    MP_TAC(ARITH_RULE `MIN (u0 DIV 7) (D DIV 5) <= u0 DIV 7 /\
                       MIN (u0 DIV 7) (D DIV 5) <= D DIV 5`) THEN
    ARITH_TAC;
    ALL_TAC];;

let FL_CHECKS_X_TAC k extra pass_tac fail_tac =
  FL_IPVAL_TAC THEN
  ASM_CASES_TAC `u0 <= u1` THENL
   [ASM_CASES_TAC `u1 <= u2` THENL
     [ASM_CASES_TAC `u2 <= u3` THENL
       [ZSTD_STEPS_TAC (k--(k+5)) THEN pass_tac;
        ZSTD_STEPS_TAC (k--(k+6+extra)) THEN fail_tac];
      ZSTD_STEPS_TAC (k--(k+4+extra)) THEN fail_tac];
    ZSTD_STEPS_TAC (k--(k+2+extra)) THEN fail_tac];;

let FL_TOP_PASS_TAC =
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL
   [UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  ZSTD_CONTINUE_TAC FL_LOOP ((`0`,`j:num`) :: FL_PINSTS) THEN
  FL_PRE0_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`7 * m <= u0`; `u0 <= u1`; `u1 <= u2`; `u2 <= u3`] THEN
  ARITH_TAC;;

let FL_TOP_FAIL_TAC =
  ZSTD_CONTINUE_TAC FL_EXIT0 ((`0`,`j:num`) :: FL_PINSTS) THEN FL_PRE0_TAC;;

let FL_TOP = prove
 (fl_top_goal,
  ZSTD_INTRO_TAC THEN FL_STREAMS_PRE_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FL_JOIN128_TAC (map fl_field [0; 16; 32; 48; 64; 80]) THEN
  ZSTD_STEPS_TAC (1--12) THEN FL_SPLIT128_TAC THEN
  ZSTD_STEPS_TAC (13--18) THEN FL_SPLIT128_TAC THEN
  ZSTD_STEPS_TAC (19--34) THEN FL_TOP_ITERS_TAC THEN
  ZSTD_STEPS_TAC [35] THEN FL_SPLIT128_TAC THEN
  ZSTD_STEPS_TAC [36] THEN FL_X14_TAC THEN
  ZSTD_STEPS_TAC [37] THEN FL_X14_TAC THEN
  ASM_CASES_TAC `m = 0` THENL
   [FL_SUBST_ZERO_TAC `m:num` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    ZSTD_STEPS_TAC (38--39) THEN FL_TOP_FAIL_TAC;
    ZSTD_STEPS_TAC (38--51) THEN
    FL_CHECKS_X_TAC 52 4 FL_TOP_PASS_TAC FL_TOP_FAIL_TAC]);;

(*** The fast loop as a subroutine ***)

let fl_std_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [memory :> bytes(op0,D); memory :> bytes(op1,D);
             memory :> bytes(op2,D); memory :> bytes(op3,D);
             memory :> bytes(args,96);
             memory :> bytes(word_sub stackpointer (word 192),192)]`;;

let fl_std_pre =
  let body = list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x24a4) /\ read SP s = stackpointer /\
     read X30 s = returnaddress /\ read X0 s = args /\
     read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
     num_of_bytelist blk /\
     read (memory :> bytes(dt,4096)) s =
     num_of_bytelist(huf_dtable ws ml 11)`;
    fl_args_in;
    list_mk_exists(fl_uvars,fl_args_streams);
    `read events s = e`] in
  mk_abs(`s:armstate`,body);;

let fl_std_post =
  let ex = list_mk_exists
    (`j:num` :: fl_uvars,
     list_mk_conj(`j <= D` :: map fl_out_stream [0;1;2;3])) in
  let ms = subst [fl_rr,`rr:(int64#num)list`; fl_wr,`wr:(int64#num)list`]
   `?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 rr wr` in
  mk_abs(`s:armstate`,
         list_mk_conj [`read PC s = returnaddress /\ read X0 s = args`;
                       ex; ms]);;

let fl_goal =
  let tm = mk_imp(fl_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; fl_std_pre; fl_std_post; fl_std_frame]) in
  let fvs = frees tm in
  list_mk_forall(filter (fun v -> mem v fvs) fl_vars,tm);;

let HUF_DECOMPRESS4X1_FAST_C_LOOP_CORRECT = prove
 (fl_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
              SOME_FLAGS] THEN
  ENSURES_PRESERVED_TAC "x19" `X19` THEN
  ENSURES_PRESERVED_TAC "x20" `X20` THEN
  ENSURES_PRESERVED_TAC "x21" `X21` THEN
  ENSURES_PRESERVED_TAC "x22" `X22` THEN
  ENSURES_PRESERVED_TAC "x23" `X23` THEN
  ENSURES_PRESERVED_TAC "x24" `X24` THEN
  ENSURES_PRESERVED_TAC "x25" `X25` THEN
  ENSURES_PRESERVED_TAC "x26" `X26` THEN
  ENSURES_PRESERVED_TAC "x27" `X27` THEN
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  W(fun (asl,w) ->
    let th0 = FL_FRAME_RULE(SPEC_ALL FL_TOP) in
    let hth = TAC_PROOF((asl,lhand(concl th0)),
                REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
    let th = MP th0 hth in
    let [_;p0;q0;c0] = snd(strip_comb(concl th)) in
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c0 THEN
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC p0 THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC q0 THEN
      CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]]) THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC fl_uvars;
    MAP_EVERY EXISTS_TAC (`j:num` :: fl_uvars)] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* HUF_DecompressFastArgs_init at 0x1de0 sets up the arguments args of the   *)
(* fast loop for the block blk of four streams at src, the n bytes of output *)
(* at dst and the decoding table at dtable, whose header dh has the table    *)
(* log tl in its byte 2. It returns 1 if the fast loop applies: n > 0, a     *)
(* table log of 11, streams of at least 8 bytes, and some output for the     *)
(* last stream (3q < n for q = (n + 3) DIV 4). Then each stream k ends 8     *)
(* bytes after its pointer, with the shift huf_lastshift of its last byte in *)
(* its container, its output is at dst + k * q, and the start of each stream *)
(* is in the arguments at +120. It returns 0 if the fast loop does not       *)
(* apply, and the error -20 for a block of fewer than 10 bytes or a jump     *)
(* table that runs past its end (HUF_DECOMPRESSFASTARGS_INIT_CORRECT). A     *)
(* stream cannot end with a byte 0, but then the shift is 0, and the fast    *)
(* loop decodes from the end of the stream. The output must end 3 bytes      *)
(* below the top of the address space, since the code compares dst + 3q,     *)
(* which can be dst + n + 2, with dst + n.                                   *)
(* ------------------------------------------------------------------------- *)

(*** The starts of the four streams after the jump table, and the shift ***)
(*** of the initial container of a stream from its last byte            ***)

let fa_a1 = `6 + huf_jump blk 0`
and fa_a2 = `6 + huf_jump blk 0 + huf_jump blk 1`
and fa_a3 = `6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2`;;

let huf_lastshift = new_definition
 `huf_lastshift (b:byte) = if b = word 0 then 0 else word_clz b + 1`;;

let fa_ends = [fa_a1; fa_a2; fa_a3; `LENGTH(blk:byte list)`];;
let fa_starts = [`6`; fa_a1; fa_a2; fa_a3];;

let fa_stream k =
  let e = el k fa_ends in
  let u = subst [e,`e:num`] `e - 8` in
  let sh = subst [e,`e:num`] `huf_lastshift (EL (e - 1) (blk:byte list))` in
  subst [fl_field(8 * k),`aip:int64`; fl_field(32 + 8 * k),`aop:int64`;
         fl_field(64 + 8 * k),`abits:int64`;
         fl_field(120 + 8 * k),`aend:int64`;
         u,`u:num`; sh,`x:num`; fl_cont u sh,`c:int64`;
         el k fa_starts,`a:num`;
         (if k = 0 then `0` else if k = 1 then `(n + 3) DIV 4` else
          subst [mk_small_numeral k,`k:num`] `k * ((n + 3) DIV 4)`),
         `ofs:num`]
   `read (memory :> bytes64 aip) s = word_add src (word u) /\
    read (memory :> bytes64 aop) s = word_add dst (word ofs) /\
    read (memory :> bytes64 abits) s = (c:int64) /\
    read (memory :> bytes64 aend) s = word_add src (word a)`;;

let fa_rr = `[src,LENGTH(blk:byte list); dtable,4]:(int64#num)list`
and fa_wr = `[args,152]:(int64#num)list`;;

let fa_goal =
  let ok = list_mk_conj
   ([`tl = 11`; `~(n = 0)`; `3 * ((n + 3) DIV 4) < n`;
     `8 <= huf_jump blk 0`; `8 <= huf_jump blk 1`; `8 <= huf_jump blk 2`;
     subst [fa_a3,`a3:num`] `a3 + 8 <= LENGTH(blk:byte list)`] @
    map fa_stream [0;1;2;3] @
    [`read (memory :> bytes64 (word_add args (word 96))) s =
      word_add dtable (word 4)`;
     `read (memory :> bytes64 (word_add args (word 104))) s = src`;
     `read (memory :> bytes64 (word_add args (word 112))) s =
      word_add dst (word n)`]) in
  let post = list_mk_conj
   [`read PC s = returnaddress`;
    `read X0 s = word 0 \/ read X0 s = word 1 \/
     read X0 s = word 18446744073709551596`;
    subst [fa_a3,`a3:num`]
     `read X0 s = word 18446744073709551596
      ==> LENGTH(blk:byte list) < 10 \/ LENGTH blk < a3`;
    mk_imp(`read X0 s = word 1`,ok);
    subst [fa_rr,`rr:(int64#num)list`; fa_wr,`wr:(int64#num)list`]
     `?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 rr wr`] in
  let tm = subst [mk_abs(`s:armstate`,post),`Q:armstate->bool`]
   `aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
    n < 2 EXP 28 /\ val(src:int64) + LENGTH(blk:byte list) < 2 EXP 64 /\
    val(dst:int64) + n + 3 < 2 EXP 64 /\
    nonoverlapping (args:int64,152) (src,LENGTH blk) /\
    nonoverlapping (args,152) (dtable:int64,4) /\
    nonoverlapping (args,152) (word pc,32000)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
              read PC s = word(pc + 0x1de0) /\ read X30 s = returnaddress /\
              C_ARGUMENTS [args; dst; word n; src; word(LENGTH blk); dtable]
                          s /\
              read (memory :> bytes(src,LENGTH blk)) s = num_of_bytelist blk /\
              read (memory :> bytes32 dtable) s = dh /\
              val(word_subword dh (16,8):byte) = tl /\
              read events s = e)
         Q
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(args,152)])` in
  list_mk_forall(
    [`pc:num`; `returnaddress:int64`; `args:int64`; `dst:int64`; `n:num`;
     `src:int64`; `blk:byte list`; `dtable:int64`; `dh:int32`; `tl:num`;
     `e:uarch_event list`],tm);;

(*** Reads of the jump table and of the streams ***)

let READ_MEMORY_BYTES16_SLICE = prove
 (`!a n x ofs s.
        read (memory :> bytes(a,n)) s = x /\ ofs + 2 <= n
        ==> read (memory :> bytes16 (word_add a (word ofs))) s =
            word((x DIV 2 EXP (8 * ofs)) MOD 2 EXP 16)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 16 = 2 EXP (8 * 2)`; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `ofs + 2 <= n ==> MIN (n - ofs) 2 = 2`] THEN
  REWRITE_TAC[BYTES16_WBYTES; wbytes; READ_COMPONENT_COMPOSE; asword;
              through; read; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let HUF_JUMP_NUM = prove
 (`!(blk:byte list) k.
        2 * k + 2 <= LENGTH blk
        ==> (num_of_bytelist blk DIV 2 EXP (8 * (2 * k))) MOD 2 EXP 16 =
            huf_jump blk k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_jump] THEN
  MP_TAC(SPECL [`blk:byte list`; `2 * k`] NUM_OF_BYTELIST_BYTE) THEN
  MP_TAC(SPECL [`blk:byte list`; `2 * k + 1`] NUM_OF_BYTELIST_BYTE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[ARITH_RULE `8 * (2 * k + 1) = 8 * (2 * k) + 8`; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  SPEC_TAC(`num_of_bytelist blk DIV 2 EXP (8 * (2 * k))`,`x:num`) THEN
  GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `65536 = 256 * 256`; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let HUF_JUMP_BOUND = prove
 (`!(blk:byte list) k. huf_jump blk k < 65536`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_jump] THEN
  MP_TAC(ISPEC `EL (2 * k) (blk:byte list)` VAL_BOUND) THEN
  MP_TAC(ISPEC `EL (2 * k + 1) (blk:byte list)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(*** HUF_DecompressFastArgs_init: lemmas and tactics ***)


(*** The table log, byte 2 of the header, by ubfx ***)

let FA_UBFX = prove
 (`!dh:int32. word_subword (word_zx dh:int64) (16,8):int64 =
              word(val(word_subword dh (16,8):byte))`,
  GEN_TAC THEN REWRITE_TAC[GSYM word_zx] THEN CONV_TAC WORD_BLAST);;

(*** Arithmetic from the facts whose variables are those of the goal and ***)
(*** extra ones, with negations, conjunctions and disjunctions of them   ***)

let FA_ARITHV_TAC (extra:term list) : tactic =
  fun (asl,w as gl) ->
    let vs = union extra (frees w) in
    let numty = `:num` in
    let rec is_rel t =
      (is_neg t && is_rel (rand t)) ||
      (is_disj t && is_rel (lhand t) && is_rel (rand t)) ||
      (is_conj t && is_rel (lhand t) && is_rel (rand t)) ||
      exists (fun op -> is_binary op t && type_of(lhand t) = numty)
             ["="; "<"; "<="] in
    let ok t = is_rel t &&
               not(exists (fun v -> type_of v = `:armstate`) (frees t)) &&
               subset (frees t) vs in
    let facts = filter (ok o concl) (map snd asl) in
    (MAP_EVERY MP_TAC facts THEN ARITH_TAC) gl;;

let FA_ARITH_TAC = FA_ARITHV_TAC [];;

let fa_jvars = [`j0:num`; `j1:num`; `j2:num`; `l4:num`; `blk:byte list`];;

(*** Rewriting the register and memory facts of the current state ***)

let FA_STATE_REWRITE_TAC ths =
  W(fun (asl,w) ->
    let s = rand w in
    RULE_ASSUM_TAC(fun th ->
      let t = concl th in
      if free_in s t &&
         (match t with
            Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),_)
              -> s' = s && not(c = `events`)
          | _ -> not(is_eq t) && not(maychange_term t) &&
                 not(can (find_term ((=) `events`)) t))
      then REWRITE_RULE ths th else th));;

let FA_DECIDE_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL [FA_ARITHV_TAC fa_jvars; ALL_TAC] THEN
  FA_STATE_REWRITE_TAC[ASSUME t];;

(*** The three 16-bit sizes of the jump table ***)

let FA_JUMP_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let bpat = subst [s,`s:armstate`]
      `read (memory :> bytes(src,LENGTH(blk:byte list))) s` in
    let bth = snd(find (fun (_,th) -> let t = concl th in
                          is_eq t && lhs t = bpat) asl) in
    let lth = snd(find (fun (_,th) -> concl th =
                          `~(LENGTH(blk:byte list) <= 9)`) asl) in
    let arith t = MP (INST [`LENGTH(blk:byte list)`,`n:num`] (ARITH_RULE t))
                     lth in
    let one k =
      let ofs = mk_small_numeral(2 * k) and kk = mk_small_numeral k in
      let c1 = arith(subst [ofs,`o2:num`] `~(n <= 9) ==> o2 + 2 <= n`) in
      let r = MP (SPECL [`src:int64`; `LENGTH(blk:byte list)`;
                         `num_of_bytelist blk`; ofs; s]
                    READ_MEMORY_BYTES16_SLICE) (CONJ bth c1) in
      let c2 = arith(subst [kk,`k:num`] `~(n <= 9) ==> 2 * k + 2 <= n`) in
      let j = MP (SPECL [`blk:byte list`; kk] HUF_JUMP_NUM) c2 in
      let r' = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) r
      and j' = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) j in
      REWRITE_RULE[j'; WORD_ADD_0] r' in
    MAP_EVERY (ASSUME_TAC o one) [0;1;2] gl;;

(*** The flags of the ccmp of the sizes with 7 ***)

let FA_SUB7_FLAG = prove
 (`!b. b < 2 EXP 64
       ==> ((&b:int) - &7 = &(val(word_sub (word b) (word 7):int64)) <=>
            7 <= b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `7 < 2 EXP 64`] THEN
  ASM_CASES_TAC `7 <= b` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB];
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

let FA_CCMP7 = prove
 (`!a b. a < 2 EXP 64 /\ b < 2 EXP 64
         ==> (~((if 7 <= a /\ ~(a = 7)
                 then (&b:int) - &7 = &(val(word_sub (word b) (word 7):int64))
                 else F) /\
                ~(if 7 <= a /\ ~(a = 7) then b = 7 else F)) <=>
              a <= 7 \/ b <= 7)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FA_SUB7_FLAG] THEN
  ASM_CASES_TAC `7 <= a /\ ~(a = 7)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let FA_CCMP_TAC a b =
  MP_TAC(SPECL [a; b] FA_CCMP7) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(fun th ->
      if is_binop `(<):num->num->bool` (concl th) &&
         (lhand(concl th) = a || lhand(concl th) = b)
      then MP_TAC th THEN ARITH_TAC else NO_TAC);
    DISCH_THEN(fun th -> FA_STATE_REWRITE_TAC[th])];;

(*** The size of the fourth stream, with or without wrapping ***)

let FA_SUB_SUB = prove
 (`!x y z. y + z <= x
           ==> word_sub (word_sub (word x) (word y)) (word z):int64 =
               word(x - (y + z))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let WORD_2EXP64 =
  CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV THENC WORD_REDUCE_CONV))
    (REFL `word(2 EXP 64):int64`);;

let FA_SUB_SUB_WRAP = prove
 (`!x y z. y + z <= x + 2 EXP 64
           ==> word_sub (word_sub (word x) (word y)) (word z):int64 =
               word((x + 2 EXP 64) - (y + z))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN
  REWRITE_TAC[WORD_ADD; WORD_2EXP64] THEN CONV_TAC WORD_RULE);;

(*** Pointers 8 bytes before the end of a stream, and the addresses of ***)
(*** the last byte and the last 8 bytes                                ***)

let FA_SUB8 = prove
 (`!(p:int64) a. 8 <= a ==> word_sub (word_add p (word a)) (word 8) =
                            word_add p (word (a - 8))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let FA_SUB8_TAC =
  MAP_EVERY (fun a ->
    let c = mk_binop `(<=):num->num->bool` `8` a in
    SUBGOAL_THEN c ASSUME_TAC THENL [FA_ARITHV_TAC fa_jvars; ALL_TAC] THEN
    FA_STATE_REWRITE_TAC[MP (SPECL [`src:int64`; a] FA_SUB8) (ASSUME c)])
  [`6 + j0`; `6 + j0 + j1`; `6 + j0 + j1 + j2`];;

let FA_ADDR_NEG = prove
 (`!(p:int64) a k. k <= a /\ k <= 2 EXP 64
                   ==> word_add (word_add p (word a)) (word (2 EXP 64 - k)) =
                       word_add p (word (a - k))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN
  REWRITE_TAC[WORD_2EXP64] THEN CONV_TAC WORD_RULE);;

let FA_WORD_NEG = prove
 (`!a k. k <= a /\ k <= 2 EXP 64
         ==> word(a + (2 EXP 64 - k)):int64 = word(a - k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a + (2 EXP 64 - k) = (a - k) + 2 EXP 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD; WORD_2EXP64; WORD_ADD_0]]);;

(*** The last byte and the last 8 bytes of a stream ending at a, before ***)
(*** the loads, at the addresses as the simulator puts them             ***)

let FA_LOAD_FACTS_TAC (a:term) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let bpat = subst [s,`s:armstate`]
      `read (memory :> bytes(src,LENGTH(blk:byte list))) s` in
    let bth = snd(find (fun (_,th) -> let t = concl th in
                          is_eq t && lhs t = bpat) asl) in
    let am1 = mk_binop `(-):num->num->num` a `1`
    and am8 = mk_binop `(-):num->num->num` a `8` in
    let c1 = mk_binop `(<):num->num->bool` am1 `LENGTH(blk:byte list)`
    and c8 = mk_binop `(<=):num->num->bool`
               (mk_binop `(+):num->num->num` am8 `8`) `LENGTH(blk:byte list)`
    and k1 = mk_binop `(<=):num->num->bool` `1` a
    and k8 = mk_binop `(<=):num->num->bool` `8` a in
    let neg k = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THENC
                          LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV))
                 (SPECL [a; k] FA_WORD_NEG) in
    (SUBGOAL_THEN (list_mk_conj [c1; c8; k1; k8]) STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THEN FA_ARITHV_TAC fa_jvars; ALL_TAC] THEN
     W(fun (asl,w) ->
       let th8 = MP (ISPECL [`src:int64`; `blk:byte list`; am1; s]
                       READ_MEMORY_BYTES8_BYTELIST) (CONJ bth (ASSUME c1)) in
       let th64 = MP (ISPECL [`src:int64`; `LENGTH(blk:byte list)`;
                              `num_of_bytelist blk`; am8; s]
                       READ_MEMORY_BYTES64_SLICE) (CONJ bth (ASSUME c8)) in
       let e1 = REWRITE_RULE[ASSUME k1] (neg `1`)
       and e8 = REWRITE_RULE[ASSUME k8] (neg `8`) in
       ASSUME_TAC(GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV)
                    [GSYM e1] th8) THEN
       ASSUME_TAC(GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV)
                    [GSYM e8] th64))) gl;;

(*** The same for the last stream, loaded from its start src + L - 8 ***)

let FA_LOAD3_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let bpat = subst [s,`s:armstate`]
      `read (memory :> bytes(src,LENGTH(blk:byte list))) s` in
    let bth = snd(find (fun (_,th) -> let t = concl th in
                          is_eq t && lhs t = bpat) asl) in
    (SUBGOAL_THEN `8 <= LENGTH(blk:byte list)` ASSUME_TAC THENL
      [FA_ARITHV_TAC fa_jvars; ALL_TAC] THEN
     W(fun (asl,w) ->
       let c1 = ARITH_RULE `8 <= n ==> n - 8 + 7 < n /\ n - 8 + 7 = n - 1 /\
                                       (n - 8) + 8 <= n` in
       let cc = MP (INST [`LENGTH(blk:byte list)`,`n:num`] c1)
                   (ASSUME `8 <= LENGTH(blk:byte list)`) in
       let [ca; cb; cc'] = CONJUNCTS cc in
       let th8 = MP (ISPECL [`src:int64`; `blk:byte list`;
                             `LENGTH(blk:byte list) - 8 + 7`; s]
                       READ_MEMORY_BYTES8_BYTELIST) (CONJ bth ca) in
       let th8' = CONV_RULE(RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV cb))))
                    th8 in
       let th64 = MP (ISPECL [`src:int64`; `LENGTH(blk:byte list)`;
                              `num_of_bytelist blk`;
                              `LENGTH(blk:byte list) - 8`; s]
                       READ_MEMORY_BYTES64_SLICE) (CONJ bth cc') in
       ASSUME_TAC th8' THEN ASSUME_TAC th64)) gl;;

let FA_DROP_LOADS_TAC =
  let bad t = can (find_term (fun x -> x = `18446744073709551615` ||
                                       x = `18446744073709551608`)) t in
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let t = concl th in
    is_eq t && is_comb(lhs t) &&
    (match lhs t with
       Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),_)),_) -> bad t
     | _ -> false));;

(*** The shift of the initial container, from the last byte ***)

let HUF_LASTSHIFT_BOUND = prove
 (`!b:byte. huf_lastshift b <= 9`,
  GEN_TAC THEN REWRITE_TAC[huf_lastshift; WORD_CLZ_BITSIZE; DIMINDEX_8] THEN
  COND_CASES_TAC THEN ARITH_TAC);;

let FA_SHIFT_REG = prove
 (`!b:byte.
     word_zx (if ~(val b - 0 = 0)
              then word_sub (word (32 - bitsize (val b))) (word 23):int32
              else word 0):int64 =
     word(huf_lastshift b)`,
  GEN_TAC THEN
  REWRITE_TAC[huf_lastshift; WORD_CLZ_BITSIZE; DIMINDEX_8; GSYM VAL_EQ_0;
              SUB_0] THEN
  ASM_CASES_TAC `val(b:byte) = 0` THEN ASM_REWRITE_TAC[WORD_ZX_0] THEN
  SUBGOAL_THEN `bitsize(val(b:byte)) <= 8` ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE] THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `(32 - bitsize(val(b:byte))) MOD 2 EXP 32 =
                32 - bitsize(val b)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `b <= 8 ==> 23 <= 32 - b`] THEN
  SUBGOAL_THEN `(32 - bitsize(val(b:byte))) - 23 < 64 /\
                (8 - bitsize(val b)) + 1 < 64` STRIP_ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 64 ==> x < 4294967296`;
               ARITH_RULE `x < 64 ==> x < 18446744073709551616`] THEN
  UNDISCH_TAC `bitsize(val(b:byte)) <= 8` THEN ARITH_TAC);;

let FA_JSHL_SHIFT = prove
 (`!(c:int64) b. word_jshl c (word (huf_lastshift b)) =
                 word_shl c (huf_lastshift b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_jshl; DIMINDEX_64; VAL_WORD] THEN
  MP_TAC(SPEC `b:byte` HUF_LASTSHIFT_BOUND) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x <= 9 ==> x < 64`;
               ARITH_RULE `x <= 9 ==> x < 2 EXP 64`]);;

(*** One stream, from the step k of the load of its last byte; the csel ***)
(*** is stepped without the deciders of branches                        ***)

let FA_CONTAINER_TAC k =
  ZSTD_STEPS_TAC ((k+2)--(k+4)) THEN
  ARM_STEPS_TAC ZSTD_EXEC [k+5] THEN ZSTD_SMALL_WORD_TAC THEN
  FA_STATE_REWRITE_TAC[FA_SHIFT_REG] THEN ZSTD_STEPS_TAC ((k+6)--(k+8)) THEN
  FA_STATE_REWRITE_TAC[FA_JSHL_SHIFT];;

let FA_STREAM_TAC a k =
  FA_LOAD_FACTS_TAC a THEN ZSTD_STEPS_TAC (k--(k+1)) THEN
  FA_DROP_LOADS_TAC THEN FA_CONTAINER_TAC k;;

(*** The addresses of the loads in the events ***)

let FA_EVENTS_ADDR_TAC =
  let eqs = List.concat (map (fun a ->
    map (fun k ->
      let c = mk_binop `(<=):num->num->bool` k a in
      (c, CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THENC
                    LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV))
            (SPECL [`src:int64`; a; k] FA_ADDR_NEG))) [`1`; `8`])
    [`6 + j0`; `6 + j0 + j1`; `6 + j0 + j1 + j2`]) in
  MAP_EVERY (fun (c,th) ->
    SUBGOAL_THEN c ASSUME_TAC THENL [FA_ARITHV_TAC fa_jvars; ALL_TAC] THEN
    W(fun (asl,w) ->
      let th' = REWRITE_RULE[ASSUME c] th in
      RULE_ASSUM_TAC(fun t ->
        if is_eq(concl t) && is_read_events(lhs(concl t))
        then REWRITE_RULE[th'] t else t))) eqs;;

(*** The returns ***)

let FA_ZERO_TAC n =
  ZSTD_STEPS_TAC (n--(n+1)) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV;;

let FA_RESULT_TAC =
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
  TRY(FA_ARITHV_TAC fa_jvars);;

(*** The proof of HUF_DecompressFastArgs_init ***)

let FA_NOWRAP_TAC =
  MP_TAC(SPECL [`LENGTH(blk:byte list) - 6`; `j0 + j1:num`; `j2:num`]
    FA_SUB_SUB) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `6 + j0 + j1 + j2 <= LENGTH(blk:byte list)` THEN ARITH_TAC;
    DISCH_THEN(fun th -> FA_STATE_REWRITE_TAC[th])] THEN
  ABBREV_TAC `l4 = (LENGTH(blk:byte list) - 6) - ((j0 + j1) + j2)` THEN
  SUBGOAL_THEN `l4 < 2 EXP 64 /\ l4 <= LENGTH(blk:byte list)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l4" THEN
    UNDISCH_TAC `val(src:int64) + LENGTH(blk:byte list) < 2 EXP 64` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (28--29) THEN FA_CCMP_TAC `j2:num` `l4:num` THEN
  ASM_CASES_TAC `j2 <= 7 \/ l4 <= 7` THENL
   [FA_STATE_REWRITE_TAC[ASSUME `j2 <= 7 \/ l4 <= 7`] THEN FA_ZERO_TAC 30;
    ALL_TAC] THEN
  FA_STATE_REWRITE_TAC[ASSUME `~(j2 <= 7 \/ l4 <= 7)`] THEN
  ZSTD_STEPS_TAC (30--46) THEN
  ABBREV_TAC `q = (n + 3) DIV 4` THEN
  FA_STATE_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
    ARITH_RULE `q + q = 2 * q`; ARITH_RULE `q + 2 * q = 3 * q`] THEN
  FA_SUB8_TAC THEN
  SUBGOAL_THEN `3 * q <= n + 2` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`dst:int64`; `3 * q`] VAL_WORD_ADD_NOWRAP) THEN
  MP_TAC(SPECL [`dst:int64`; `n:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `val(dst:int64) + n + 3 < 2 EXP 64` THEN ARITH_TAC;
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`val(dst:int64) + n + 3 < 2 EXP 64`; `3 * q <= n + 2`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  ASM_CASES_TAC `3 * q < n` THENL
   [ALL_TAC; ZSTD_STEPS_TAC (47--49) THEN FA_RESULT_TAC] THEN
  ZSTD_STEPS_TAC [47] THEN
  FA_LOAD_FACTS_TAC `6 + j0` THEN ZSTD_STEPS_TAC (48--50) THEN
  FA_DROP_LOADS_TAC THEN ZSTD_STEPS_TAC (51--53) THEN
  ARM_STEPS_TAC ZSTD_EXEC [54] THEN ZSTD_SMALL_WORD_TAC THEN
  FA_STATE_REWRITE_TAC[FA_SHIFT_REG] THEN ZSTD_STEPS_TAC (55--58) THEN
  FA_STATE_REWRITE_TAC[FA_JSHL_SHIFT] THEN
  FA_STREAM_TAC `6 + j0 + j1` 59 THEN
  FA_STREAM_TAC `6 + j0 + j1 + j2` 68 THEN
  FA_LOAD3_TAC THEN ZSTD_STEPS_TAC (77--81) THEN
  ARM_STEPS_TAC ZSTD_EXEC [82] THEN ZSTD_SMALL_WORD_TAC THEN
  FA_STATE_REWRITE_TAC[FA_SHIFT_REG] THEN ZSTD_STEPS_TAC (83--85) THEN
  FA_STATE_REWRITE_TAC[FA_JSHL_SHIFT] THEN ZSTD_STEPS_TAC (86--87) THEN
  FA_EVENTS_ADDR_TAC THEN PUFF_FINAL_TAC THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  FA_ARITHV_TAC fa_jvars;;

let FA_WRAP_TAC =
  MP_TAC(SPECL [`LENGTH(blk:byte list) - 6`; `j0 + j1:num`; `j2:num`]
    FA_SUB_SUB_WRAP) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`j0 < 65536`; `j1 < 65536`; `j2 < 65536`] THEN
    ARITH_TAC;
    DISCH_THEN(fun th -> FA_STATE_REWRITE_TAC[th])] THEN
  ABBREV_TAC
   `w4 = ((LENGTH(blk:byte list) - 6) + 2 EXP 64) - ((j0 + j1) + j2)` THEN
  SUBGOAL_THEN `w4 < 2 EXP 64 /\ LENGTH(blk:byte list) < w4 /\ ~(w4 <= 7)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w4" THEN
    MAP_EVERY UNDISCH_TAC
     [`~(6 + j0 + j1 + j2 <= LENGTH(blk:byte list))`;
      `~(LENGTH(blk:byte list) <= 9)`;
      `val(src:int64) + LENGTH(blk:byte list) < 2 EXP 64`;
      `j0 < 65536`; `j1 < 65536`; `j2 < 65536`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (28--29) THEN FA_CCMP_TAC `j2:num` `w4:num` THEN
  FA_STATE_REWRITE_TAC[ASSUME `~(w4 <= 7)`] THEN
  ASM_CASES_TAC `j2 <= 7` THENL
   [FA_DECIDE_TAC `~(7 <= j2 /\ ~(j2 = 7))` THEN FA_ZERO_TAC 30;
    FA_DECIDE_TAC `7 <= j2 /\ ~(j2 = 7)` THEN
    FA_STATE_REWRITE_TAC[MP (SPECL [`7`; `w4:num`] INT_OF_NUM_SUB)
      (MP (ARITH_RULE `~(w4 <= 7) ==> 7 <= w4`) (ASSUME `~(w4 <= 7)`))] THEN
    ZSTD_STEPS_TAC (30--33) THEN FA_RESULT_TAC];;

let HUF_DECOMPRESSFASTARGS_INIT_CORRECT = prove
 (fa_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `n = 0` then SUBST_ALL_TAC th
                            else NO_TAC) THEN
    ZSTD_STEPS_TAC (1--8) THEN FA_RESULT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(blk:byte list) <= 9` THENL
   [ZSTD_STEPS_TAC (1--9) THEN FA_RESULT_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--8) THEN
  SUBGOAL_THEN `tl < 256` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `tl:num`)) THEN
    MP_TAC(ISPEC `word_subword (dh:int32) (16,8):byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FA_UBFX]) THEN
  FA_STATE_REWRITE_TAC
    [ASSUME `val(word_subword (dh:int32) (16,8):byte) = tl`] THEN
  ASM_CASES_TAC `tl = 11` THENL
   [ALL_TAC; ZSTD_STEPS_TAC (9--12) THEN FA_RESULT_TAC] THEN
  FA_JUMP_TAC THEN
  MAP_EVERY (fun k ->
    let kk = mk_small_numeral k in
    let j = mk_var("j"^string_of_int k,`:num`) in
    ASSUME_TAC(SPECL [`blk:byte list`; kk] HUF_JUMP_BOUND) THEN
    ABBREV_TAC (mk_eq(j,list_mk_icomb "huf_jump" [`blk:byte list`; kk])))
   [0;1;2] THEN
  ZSTD_STEPS_TAC (9--19) THEN
  FA_STATE_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ZSTD_STEPS_TAC (20--22) THEN FA_CCMP_TAC `j0:num` `j1:num` THEN
  ASM_CASES_TAC `j0 <= 7 \/ j1 <= 7` THENL
   [FA_STATE_REWRITE_TAC[ASSUME `j0 <= 7 \/ j1 <= 7`] THEN FA_ZERO_TAC 23;
    ALL_TAC] THEN
  FA_STATE_REWRITE_TAC[ASSUME `~(j0 <= 7 \/ j1 <= 7)`] THEN
  ZSTD_STEPS_TAC (23--27) THEN
  ASM_CASES_TAC `6 + j0 + j1 + j2 <= LENGTH(blk:byte list)` THENL
   [FA_NOWRAP_TAC; FA_WRAP_TAC]);;

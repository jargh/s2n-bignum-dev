(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* zstd's HUF_decompress4X2_usingDTable_internal, the decoding of            *)
(* Huffman-coded literals in four streams with double-symbol tables,         *)
(* compiled by gcc 12 at -O2 for AArch64                                     *)
(* (HUF_DECOMPRESS4X2_USINGDTABLE_CORRECT). For a valid block the result is  *)
(* the size n of the output, with the output at dst; and the result is       *)
(* always n or an error code. The fast path sets up its arguments with       *)
(* HUF_DecompressFastArgs_init, decodes with                                 *)
(* HUF_decompress4X2_usingDTable_internal_fast_c_loop and finishes each      *)
(* stream at 0x3140. Neither path rejects every block that is not valid: the *)
(* slow path accepts a stream whose last entry of two symbols is cut off at  *)
(* its start, and the fast path does not check that each stream ends exactly *)
(* at its start; so for such a block the theorem says only that the result   *)
(* is n or an error code. The output must not be at address 0, for the       *)
(* comparisons of the output pointers with the end of a segment less 9.      *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode4x2_slow_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* The finish of a stream after the fast loop, at 0x3140: the lookups of 11  *)
(* bits in the double-symbol table (4 bytes an entry), the last byte         *)
(* (FIN2_LAST), the loop of one lookup without reloads (FIN2_L0) and with    *)
(* them (FIN2_L1), the body of five lookups (FIN2_B5) and its loop           *)
(* (FIN2_L5), and the head (FIN2_HEAD): the segment of the stream decoded to *)
(* its end, the bytes those of the decoding when it uses no bits beyond the  *)
(* stream, or the error -20 when the stream has not reached 8 bytes before   *)
(* its end.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*** The finish of a stream after the fast loop, at 0x3140: the lookups ***)
(*** of 11 bits of the double-symbol table at dt (4 bytes an entry)     ***)

let FIN2_INDEX_ANY = prove
 (`!(y:int64). word_shl (word_ushr y 53) 2 = word (4 * val(word_ushr y 53)) /\
               val(word_ushr y 53) < 2048`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD_USHR] THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  MP_TAC(ISPEC `y:int64` VAL_BOUND_64) THEN ARITH_TAC);;

let FIN2_INDEX2W = prove
 (`!(blk:byte list) ofs bc.
     bc < 64 /\ (11 + bc <= 64 \/ ofs = 0)
     ==> word_shl (word_ushr
           (word (2 EXP bc * (num_of_bytelist blk DIV 2 EXP (8 * ofs)) MOD
                  18446744073709551616):int64) 53) 2 =
         word (4 * zstd_back blk (8 * ofs + 64 - bc) 11)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[CONJUNCT1(SPEC_ALL FIN2_INDEX_ANY)] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`blk:byte list`; `ofs:num`; `bc:num`; `11`] ZSTD_WINDOW) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC MULT_SYM);;

let FIN2_INDEX2 = prove
 (`!(blk:byte list) ofs bc.
     bc < 64 /\ (11 + bc <= 64 \/ ofs = 0)
     ==> word_shl (word_ushr
           (word_jshl (word((num_of_bytelist blk DIV 2 EXP (8 * ofs)) MOD
                            18446744073709551616):int64) (word bc)) 53) 2 =
         word (4 * zstd_back blk (8 * ofs + 64 - bc) 11)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FIN2_INDEX2W th)]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FAST2_JSHL (CONJUNCT1 th)]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_SHL_WORD; WORD_EQ; DIMINDEX_64; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

(*** The index at the start of the block (ofs = 0) ***)

let FIN2_INDEX0W = prove
 (`!(blk:byte list) bc.
     bc < 64
     ==> word_shl (word_ushr
           (word (2 EXP bc * (num_of_bytelist blk DIV 1) MOD
                  18446744073709551616):int64) 53) 2 =
         word (4 * zstd_back blk (64 - bc) 11)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`blk:byte list`; `0`; `bc:num`] FIN2_INDEX2W) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP]);;

(*** The first symbol of an entry as the next symbol of the decoding, ***)
(*** and no next symbol once the bits ran out                         ***)

let FIN2_FIRST_SYM = prove
 (`!ws ml (blk:byte list) p jj pos.
        huf_complete ws ml /\ ml <= 11 /\
        FST(SND(huf_decode ws ml blk p jj)) = pos
        ==> FST(huf_decode ws ml blk p (jj + 1)) =
            APPEND (FST(huf_decode ws ml blk p jj))
                   [word(EL 0 (huf_dentry2 ws ml 11 (zstd_back blk pos 11)))]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HUF_DECODE_SUC] THEN
  ASM_SIMP_TAC[HUF_DENTRY2_BACK] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[EL; HD]);;

let FIN2_NOBITS = prove
 (`!ws ml (blk:byte list) p jj.
        huf_complete ws ml /\ FST(SND(huf_decode ws ml blk p jj)) = 0
        ==> ~SND(SND(huf_decode ws ml blk p (jj + 1)))`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_REWRITE_TAC[HUF_DECODE_SUC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`;
                `zstd_back (blk:byte list) 0 ml`] HUF_NBITS_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN ARITH_TAC);;

let FIN2_NOTOK_MONO = prove
 (`!ws ml (blk:byte list) p jj k.
        ~SND(SND(huf_decode ws ml blk p jj))
        ==> ~SND(SND(huf_decode ws ml blk p (jj + k)))`,
  MESON_TAC[HUF_DECODE_OK_MONO; LE_ADD]);;

let FIN2_NOTOK_LE = prove
 (`!ws ml (blk:byte list) p a b.
        ~SND(SND(huf_decode ws ml blk p a)) /\ a <= b
        ==> ~SND(SND(huf_decode ws ml blk p b))`,
  MESON_TAC[HUF_DECODE_OK_MONO]);;

(*** The finish of stream k after the fast loop, at 0x3140: the segment  ***)
(*** of L bytes at op (the outputs at op up to oend = op + rest, L = MIN ***)
(*** q rest), of which j0 were decoded by the fast loop, decoded to its  ***)
(*** end with the bit stream from the start ilowest of the block, the    ***)
(*** stream at position p in blk (positions from ilowest), with the      ***)
(*** table of 2^11 entries at dt (as FIN of the 4X1 proof)               ***)

let fin2_rr =
 `[ilowest,LENGTH(blk:byte list); dt,8192; argk,128;
   word_add (word_sub stackpointer (word 496)) (word 448),8]:(int64#num)list`
and fin2_wr =
 `[op,L; word_add argk (word 32),8]:(int64#num)list`;;

let fin2_hyps = list_mk_conj
 [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
  `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\ 1 <= ml /\ ml <= 11`;
  `8 <= val(ilowest:int64) /\
   val ilowest + LENGTH(blk:byte list) < 2 EXP 64`;
  `MIN q rest = L /\ q < 2 EXP 28 /\ val(op:int64) + rest < 2 EXP 64 /\
   ~(val op = 0)`;
  `nonoverlapping (op:int64,L) (ilowest,LENGTH(blk:byte list)) /\
   nonoverlapping (op,L) (dt:int64,8192) /\
   nonoverlapping (op,L) (argk:int64,128) /\
   nonoverlapping (op,L)
     (word_add (word_sub stackpointer (word 496)) (word 448),8) /\
   nonoverlapping (op,L) (word pc,32000) /\
   nonoverlapping (word_add argk (word 32),8)
     (word_add (word_sub stackpointer (word 496)) (word 448),8) /\
   nonoverlapping (word_add argk (word 32),8)
     (ilowest,LENGTH(blk:byte list)) /\
   nonoverlapping (word_add argk (word 32),8) (dt,8192) /\
   nonoverlapping (word_add argk (word 32),8) (word pc,32000)`];;

let fin2_frame =
 `MAYCHANGE [PC; X1; X2; X3; X4; X6; X7; X8; X11; X12; X13; X14; X15;
             X16; X17; X19] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op,L);
             memory :> bytes(word_add argk (word 32),8)]`;;

let fin2_vars =
 [`pc:num`; `stackpointer:int64`; `argk:int64`; `op:int64`; `rest:num`;
  `q:num`; `L:num`; `blk:byte list`; `ilowest:int64`; `dt:int64`;
  `ws:num list`; `ml:num`; `p:num`; `j0:num`; `e:uarch_event list`];;

let mk_fin2_goal extra pre post =
  let tm = mk_imp(fin2_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; fin2_frame]) in
  let vs = fin2_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fin2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** The facts that hold all through ***)

let fin2_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read X0 s = argk /\ read X5 s = dt /\ read X7 s = word_add op (word L) /\
  read X8 s = word_add op (word j0) /\
  read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
  num_of_bytelist blk /\
  read (memory :> bytes(dt,8192)) s = num_of_bytelist(huf_dtable2 ws ml 11) /\
  read (memory :> bytes64 (word_add argk (word 32))) s =
  word_add op (word j0) /\ j0 <= L`;;

(*** The decoding ok for the L bytes of the segment ***)

let fin2_ok = `SND(SND(huf_decode ws ml (blk:byte list) p L))`;;

let fin2_bytes = subst [fin2_ok,`ok:bool`]
 `ok ==> read (memory :> bytes(op,L)) s =
         num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p L))`;;

(*** At 0x344c, the segment done and op[k] at its end ***)

let fin2_post = with_memsafe fin2_rr fin2_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x344c) /\ read X19 s = word_add op (word L) /\
   read (memory :> bytes64 (word_add argk (word 32))) s =
   word_add op (word L)`; fin2_bytes]));;

(*** At 0x3434, after the last byte ***)

let fin2_done = with_memsafe fin2_rr fin2_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x3434)`; fin2_common;
  `read X2 s = word_add op (word L)`; fin2_bytes]));;

let FIN2_STEPS_TAC ns = MAP_EVERY ZSTD2_STEP_TAC ns;;

let FIN2_DONE = prove
 (mk_fin2_goal [] fin2_done fin2_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  FIN2_STEPS_TAC (1--2) THEN
  FA_STATE_REWRITE_TAC[WORD_RULE
    `word_sub (word_add (op:int64) (word L)) (word_add op (word j0)) =
     word_sub (word L) (word j0)`] THEN
  FA_STATE_REWRITE_TAC[SYM(REWRITE_RULE[ASSUME `j0 <= L`]
    (SPECL [`L:num`; `j0:num`] WORD_SUB))] THEN
  FIN2_STEPS_TAC [3] THEN
  FA_STATE_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
    MP (ARITH_RULE `j0 <= L ==> j0 + L - j0 = L`) (ASSUME `j0 <= L`)] THEN
  FIN2_STEPS_TAC (4--6) THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

(*** The container at ofs ***)

let fin2_win = `word((num_of_bytelist (blk:byte list) DIV 2 EXP (8 * ofs)) MOD
                     2 EXP 64):int64`;;

(*** The state of the decoding after jj bytes, at ofs with bc bits used: ***)
(*** good, or the bits ran out (then nothing about the bytes)            ***)

let fin2_good = `SND(SND(huf_decode ws ml blk p jj)) /\
  FST(SND(huf_decode ws ml blk p jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
  read (memory :> bytes(op,jj)) s =
  num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p jj))`;;

let fin2_bad = `~SND(SND(huf_decode ws ml (blk:byte list) p jj)) /\
  bc <= 64 + 11 * jj`;;

(*** At 0x3418, at most one byte left: the first symbol of the entry ***)

let fin2_lastbody = list_mk_conj
 [`read PC s = word(pc + 0x3418)`; fin2_common;
  `read X2 s = word_add op (word jj)`; mk_eq(`read X4 s`,fin2_win);
  `read X1 s = word bc /\ ofs + 8 <= LENGTH(blk:byte list) /\
   jj <= L /\ L <= jj + 1`;
  mk_disj(mk_conj(fin2_good,`ofs = 0 \/ bc <= 53`),fin2_bad)];;

let fin2_last = with_memsafe fin2_rr fin2_wr
  (mk_abs(`s:armstate`,fin2_lastbody));;

let fin2_last_ex = with_memsafe fin2_rr fin2_wr
  (mk_abs(`s:armstate`,list_mk_exists([`jj:num`; `bc:num`],fin2_lastbody)));;

(*** The values of op + k for the comparisons of the output pointer ***)

let FIN2_OPVAL_TAC ks =
  MAP_EVERY (fun k ->
    let th = SPECL [`op:int64`; k] VAL_WORD_ADD_NOWRAP in
    MP_TAC th THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(op:int64) + rest < 2 EXP 64`; `MIN q rest = L`] THEN
      REWRITE_TAC[MIN; DIMINDEX_64] THEN
      FA_ARITHV_TAC [`jj:num`; `L:num`; `rest:num`; `q:num`; `op:int64`];
      DISCH_TAC]) ks;;

(*** A lookup at a good state at position pos of the decoding after jj   ***)
(*** bytes, under the condition cnd of the lemmas idx for the index: the ***)
(*** index as the 11 bits below pos, and the entry e of the table with   ***)
(*** its bytes                                                           ***)

let FIN2_LOOKUP_GEN_TAC (s:term) (pos:term) (cnd:term) (idx:thm list) =
  let x = list_mk_icomb "zstd_back" [`blk:byte list`; pos; `11`] in
  SUBGOAL_THEN cnd ASSUME_TAC THENL
   [FA_ARITHV_TAC [`ofs:num`; `bc:num`; `L:num`; `jj:num`]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = cnd
    then FA_STATE_REWRITE_TAC (map (fun l -> MATCH_MP l th) idx)
    else NO_TAC) THEN
  MP_TAC(ISPECL [`blk:byte list`; pos; `11`] ZSTD_BACK_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
   (ISPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; x; s]
     HUF_DTABLE2_READ)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
   (ISPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; x; s]
     HUF_DTABLE2_READ16)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; x] HUF_DENTRY2_BOUNDS) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))];;

(*** The lookup at position 8 * ofs + 64 - bc ***)

let FIN2_LOOKUP_TAC (s:term) (ofs:term) (bc:term) =
  let pos = subst [ofs,`ofs:num`; bc,`bc:num`] `8 * ofs + 64 - bc` in
  let cnd = subst [ofs,`ofs:num`; bc,`bc:num`]
              `bc < 64 /\ (11 + bc <= 64 \/ ofs = 0)` in
  FIN2_LOOKUP_GEN_TAC s pos cnd
   [SPECL [`blk:byte list`; ofs; bc] FIN2_INDEX2;
    SPECL [`blk:byte list`; ofs; bc] FIN2_INDEX2W];;

(*** A lookup with any index (once the bits ran out): the index below ***)
(*** 2^11, as x, and the entry of the table with its bytes            ***)

let FIN2_LOOKUP_ANY_TAC (s:term) : tactic =
  W(fun (asl,w) ->
    let pat = `word_shl (word_ushr y 53) 2:int64` in
    let t = tryfind (fun (_,th) ->
      find_term (fun u -> can (term_match [] pat) u) (concl th)) asl in
    let _,tmi,_ = term_match [] pat t in
    let y = rev_assoc `y:int64` tmi in
    let th = ISPEC y FIN2_INDEX_ANY in
    let vt = lhand(concl(CONJUNCT2 th)) in
    FA_STATE_REWRITE_TAC[CONJUNCT1 th] THEN
    ASSUME_TAC(CONJUNCT2 th) THEN
    ABBREV_TAC (mk_eq(`x:num`,vt))) THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
   (ISPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; `x:num`; s]
     HUF_DTABLE2_READ)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
   (ISPECL [`ws:num list`; `ml:num`; `11`; `dt:int64`; `x:num`; s]
     HUF_DTABLE2_READ16)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; `x:num`]
    HUF_DENTRY2_BOUNDS) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))];;

(*** 0x3418: the last byte if one is left, the first symbol of the entry ***)

let FIN2_NOTOK_TAC : tactic =
  FIRST [MATCH_MP_TAC FIN2_NOTOK_MONO THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC FIN2_NOBITS THEN ASM_REWRITE_TAC[] THEN
         FA_ARITHV_TAC [`ofs:num`; `bc:num`]];;

let FIN2_LAST_END_TAC good : tactic =
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  if good then
    DISCH_TAC THEN MATCH_MP_TAC HUF_MEM_STEP THEN
    W(fun (asl,w) ->
      let e = `EL 0 (huf_dentry2 ws ml 11
                 (zstd_back (blk:byte list) (8 * ofs + 64 - bc) 11))` in
      MAP_EVERY EXISTS_TAC [`jj:num`; e]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FIN2_FIRST_SYM THEN
    ASM_REWRITE_TAC[]
  else
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN FIN2_NOTOK_TAC;;

let FIN2_LAST = prove
 (mk_fin2_goal [`jj:num`; `ofs:num`; `bc:num`] fin2_last fin2_done,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  FIN2_OPVAL_TAC [`jj:num`; `L:num`] THEN
  ASM_CASES_TAC `jj:num = L` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `jj:num = L`))
    THEN FIN2_STEPS_TAC (1--2) THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
      check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `L = jj + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (is_disj o concl)) THENL
   [ASM_CASES_TAC `bc < 64` THENL
     [FIN2_STEPS_TAC (1--5) THEN
      FIN2_LOOKUP_TAC `s5:armstate` `ofs:num` `bc:num` THEN
      FIN2_STEPS_TAC (6--7) THEN FIN2_LAST_END_TAC true;
      FIN2_STEPS_TAC (1--5) THEN FIN2_LOOKUP_ANY_TAC `s5:armstate` THEN
      FIN2_STEPS_TAC (6--7) THEN FIN2_LAST_END_TAC false];
    FIN2_STEPS_TAC (1--5) THEN FIN2_LOOKUP_ANY_TAC `s5:armstate` THEN
    FIN2_STEPS_TAC (6--7) THEN FIN2_LAST_END_TAC false]);;

(*** 0x3410, the loop of one lookup without reloads while two bytes are ***)
(*** left, for the measure m = L - jj, the container at ofs fixed; good ***)
(*** only at the start of the block (ofs = 0) unless it stops at once   ***)

let fin2_l0body = list_mk_conj
 [`read PC s = word(pc + 0x3410)`; fin2_common;
  `read X2 s = word_add op (word jj)`; mk_eq(`read X4 s`,fin2_win);
  `read X1 s = word bc /\
   read X15 s = word_add op (word (L - 2)) /\ 2 <= L /\
   ofs + 8 <= LENGTH(blk:byte list) /\ jj <= L`;
  mk_disj(list_mk_conj [fin2_good; `ofs = 0 \/ bc <= 53`;
                        `ofs = 0 \/ L < jj + 2`],fin2_bad)];;

let fin2_l0inv = with_memsafe fin2_rr fin2_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `bc:num`],
    mk_conj(`m = L - jj`,fin2_l0body))));;

let fin2_l0_goal = mk_fin2_goal [`ofs:num`]
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(fin2_l0inv,[`m:num`; `s:armstate`]))))
  fin2_last_ex;;

(*** The decoding after a lookup of a good state after j bytes at     ***)
(*** position pos: the bytes, position and state of the decoding of   ***)
(*** j + len bytes, with the store of the two symbols merged into the ***)
(*** bytes before                                                     ***)

let FIN2_STEP_FACTS_GEN_TAC (s:term) (j:term) (pos:term) : tactic =
  let x = list_mk_icomb "zstd_back" [`blk:byte list`; pos; `11`] in
  let e = list_mk_icomb "huf_dentry2" [`ws:num list`; `ml:num`; `11`; x] in
  let el k = mk_icomb(mk_icomb(`EL:num->num list->num`,mk_small_numeral k),
                      e) in
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `11`; `blk:byte list`; `p:num`;
                j] HUF_DECODE_X2_STEP) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`op:int64`;
                 subst [j,`j:num`] `FST(huf_decode ws ml (blk:byte list) p j)`;
                 el 0; el 1; el 3; s] READ_MEMORY_X2_STORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HUF_DECODE_LENGTH];
    REWRITE_TAC[HUF_DECODE_LENGTH] THEN DISCH_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,
                         mk_comb(`word:num->byte`,el 3)),el 3))
  (fun th -> FA_STATE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(fun th -> if is_disj(concl th) && lhand(lhand(concl th)) = el 3
                          then MP_TAC th else NO_TAC) THEN
    ARITH_TAC;
    ALL_TAC];;

let FIN2_STEP_FACTS_POS_TAC (s:term) (pos:term) : tactic =
  FIN2_STEP_FACTS_GEN_TAC s `jj:num` pos;;

let FIN2_STEP_FACTS_TAC (s:term) (ofs:term) (bc:term) : tactic =
  FIN2_STEP_FACTS_POS_TAC s
   (subst [ofs,`ofs:num`; bc,`bc:num`] `8 * ofs + 64 - bc`);;

(*** The arithmetic of the loops: the facts about the variables of the ***)
(*** stream only                                                       ***)

let FIN2_ARITH_TAC =
  FA_ARITHV_TAC [`ofs:num`; `bc:num`; `jj:num`; `L:num`; `m:num`; `ml:num`];;

(*** On to the next iteration of a loop with jj' bytes and bc' bits used: ***)
(*** the measure and the conjuncts of the invariant                       ***)

let FIN2_NEXT_TAC jj' bc' : tactic =
  DISJ1_TAC THEN EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jj') THEN
  CONJ_TAC THENL [FIN2_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [jj'; bc'] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];;

(*** The good state after a lookup, or the bad one when the bits ran out ***)

let FIN2_GOOD_OR_BAD_TAC (ofs:term) (bc:term) : tactic =
  let pos = subst [ofs,`ofs:num`; bc,`bc:num`] `8 * ofs + 64 - bc` in
  let x = list_mk_icomb "zstd_back" [`blk:byte list`; pos; `11`] in
  let e = list_mk_icomb "huf_dentry2" [`ws:num list`; `ml:num`; `11`; x] in
  let nb = mk_icomb(mk_icomb(`EL:num->num list->num`,`2`),e) in
  ASM_CASES_TAC (mk_binop `(<=):num->num->bool` nb pos) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIN2_ARITH_TAC;;

(*** After a lookup with any index x: the number of symbols as a value ***)

let FIN2_ANY_FACTS_TAC : tactic =
  let e = `huf_dentry2 ws ml 11 x` in
  let el k = mk_icomb(mk_icomb(`EL:num->num list->num`,mk_small_numeral k),
                      e) in
  SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,
                         mk_comb(`word:num->byte`,el 3)),el 3))
  (fun th -> FA_STATE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(fun th -> if is_disj(concl th) && lhand(lhand(concl th)) = el 3
                          then MP_TAC th else NO_TAC) THEN
    ARITH_TAC;
    ALL_TAC];;

(*** The bad state after a lookup with any index: from a bad one, or from ***)
(*** a good one with the bits used up (bc = 64 at the start)              ***)

let FIN2_BAD_NEXT_TAC : tactic =
  let jj' = `jj + EL 3 (huf_dentry2 ws ml 11 x)`
  and bc' = `bc + EL 2 (huf_dentry2 ws ml 11 x)` in
  PUFF_FINAL_TAC THEN FIN2_NEXT_TAC jj' bc' THEN
  REPEAT CONJ_TAC THEN TRY FIN2_ARITH_TAC THEN
  W(fun (asl,w) ->
    if is_disj w then DISJ2_TAC else ALL_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FIN2_NOTOK_LE THEN
    FIRST [EXISTS_TAC `jj:num` THEN ASM_REWRITE_TAC[] THEN FIN2_ARITH_TAC;
           EXISTS_TAC `jj + 1` THEN CONJ_TAC THENL
            [MATCH_MP_TAC FIN2_NOBITS THEN ASM_REWRITE_TAC[] THEN
             FIN2_ARITH_TAC;
             FIN2_ARITH_TAC]];
    FIN2_ARITH_TAC];;

(*** The exit to the last byte, the state as it is ***)

let FIN2_TO_LAST_TAC : tactic =
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`jj:num`; `bc:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY FIN2_ARITH_TAC THEN
  FIRST [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN FIN2_ARITH_TAC;
         DISJ2_TAC THEN ASM_REWRITE_TAC[]];;

let FIN2_L0_TAC =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  PUFF_INIT_TAC "s0" THEN FIN2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
             can (find_term ((=) `huf_decode`)) (concl th))) THEN
  ASM_CASES_TAC `jj + 2 <= L` THEN
  TRY(FIN2_STEPS_TAC (1--2) THEN FIN2_TO_LAST_TAC THEN NO_TAC) THENL
   [ASM_CASES_TAC `bc < 64` THENL
     [FIN2_STEPS_TAC (1--5) THEN
      FIN2_LOOKUP_TAC `s5:armstate` `ofs:num` `bc:num` THEN
      FIN2_STEPS_TAC (6--12) THEN FIN2_STEP_FACTS_TAC `s12:armstate` `ofs:num`
        `bc:num`
      THEN PUFF_FINAL_TAC THEN
      FIN2_NEXT_TAC
       `jj + EL 3 (huf_dentry2 ws ml 11 (zstd_back blk (8 * ofs + 64 - bc)
                                          11))`
       `bc + EL 2 (huf_dentry2 ws ml 11 (zstd_back blk (8 * ofs + 64 - bc)
                                          11))` THEN
      CONJ_TAC THENL [FIN2_ARITH_TAC; FIN2_GOOD_OR_BAD_TAC `ofs:num` `bc:num`];
      FIN2_STEPS_TAC (1--5) THEN FIN2_LOOKUP_ANY_TAC `s5:armstate` THEN
      FIN2_STEPS_TAC (6--12) THEN FIN2_ANY_FACTS_TAC THEN FIN2_BAD_NEXT_TAC];
    FIN2_STEPS_TAC (1--5) THEN FIN2_LOOKUP_ANY_TAC `s5:armstate` THEN
    FIN2_STEPS_TAC (6--12) THEN FIN2_ANY_FACTS_TAC THEN FIN2_BAD_NEXT_TAC];;

let FIN2_L0 = prove(fin2_l0_goal, FIN2_L0_TAC);;

(*** The pieces put together: the last byte from its state, and the loop ***)
(*** without reloads, on to the end of the segment                       ***)

let FIN2_TRANS_TAC mid th1 th2 =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC mid THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC(SPEC_ALL th1) THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(SPEC_ALL th2) THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];;

let FIN2_LASTEX = prove
 (mk_fin2_goal [`ofs:num`] fin2_last_ex fin2_done,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  MATCH_MP_TAC(SPEC_ALL FIN2_LAST) THEN ASM_REWRITE_TAC[]);;

let FIN2_LASTPOST = prove
 (mk_fin2_goal [`ofs:num`] fin2_last_ex fin2_post,
  FIN2_TRANS_TAC fin2_done FIN2_LASTEX FIN2_DONE);;

let FIN2_L0POST = prove
 (mk_fin2_goal [`ofs:num`]
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      list_mk_comb(fin2_l0inv,[`m:num`; `s:armstate`]))))
   fin2_post,
  FIN2_TRANS_TAC fin2_last_ex FIN2_L0 FIN2_LASTPOST);;

(*** 0x33ac, the loop of a reload and one lookup while two bytes are left, ***)
(*** for the measure m = L - jj; good all through (after a reload at least ***)
(*** 57 bits are left), the bits used at most 7 after a reload, 18 after   ***)
(*** a lookup, unless at the start of the block                            ***)

let fin2_l1body = list_mk_conj
 [`read PC s = word(pc + 0x33ac)`; fin2_common;
  `read X2 s = word_add op (word jj) /\
   read X3 s = word_add ilowest (word ofs)`;
  mk_eq(`read X4 s`,fin2_win);
  `read X1 s = word bc /\ read X11 s = ilowest /\
   read X12 s = word_add ilowest (word 8) /\
   read X15 s = word_add op (word (L - 2)) /\ 2 <= L /\
   ofs + 8 <= LENGTH(blk:byte list) /\ jj <= L`;
  fin2_good; `ofs = 0 \/ bc <= 18`];;

let fin2_l1inv = with_memsafe fin2_rr fin2_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],
    mk_conj(`m = L - jj`,fin2_l1body))));;

let fin2_l1_goal = mk_fin2_goal []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(fin2_l1inv,[`m:num`; `s:armstate`]))))
  fin2_post;;

(*** Going on with a later piece th from the state, its postcondition to ***)
(*** that of the goal by wtac, with the instantiation insts and the      ***)
(*** witnesses ws of its precondition, the arithmetic by arith; for a    ***)
(*** piece to the end of the segment, the second disjunct of the         ***)
(*** postcondition of a loop                                             ***)

let FIN2_GOON_ARITH_TAC arith wtac th insts (ws:term list) : tactic =
  ZSTD_CONTINUE_WITH_TAC wtac th insts THEN
  MEMSAFE_ELIM_TAC THEN MAP_EVERY EXISTS_TAC ws THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY arith THEN
  FIRST [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
         TRY(FIRST_ASSUM ACCEPT_TAC) THEN arith;
         ALL_TAC];;

let FIN2_GOON_GEN_TAC = FIN2_GOON_ARITH_TAC FIN2_ARITH_TAC;;

let FIN2_GOON_TAC =
  FIN2_GOON_GEN_TAC
   (GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(*** The container after a reload to ofs' ***)

let FIN2_SLICE_TAC ofs' : tactic =
  W(fun (asl,w) ->
    MP_TAC(SPECL [`ilowest:int64`; `LENGTH(blk:byte list)`;
                  `num_of_bytelist(blk:byte list)`; ofs'; rand w]
       READ_MEMORY_BYTES64_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIN2_ARITH_TAC;
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC]);;

(*** The position of the decoding as pos after a reload (the fact with ***)
(*** the old one replaced), and at the new ofs' and bc'                ***)

let FIN2_POS_TAC pos : tactic =
  let t = mk_eq(`FST(SND(huf_decode ws ml (blk:byte list) p jj))`,pos) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && lhs c = lhs t && not(c = t)
      then REWRITE_TAC[th] else NO_TAC) THEN
    FIN2_ARITH_TAC;
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && lhs c = lhs t && not(c = t)
      then ALL_TAC else NO_TAC)];;

let FIN2_RELOAD_POS_TAC ofs' bc' : tactic =
  FIN2_POS_TAC (subst [ofs',`ofs':num`; bc',`bc':num`] `8 * ofs' + 64 - bc'`);;

(*** On to the next iteration of a loop with jj' bytes, ofs' and bc' ***)

let FIN2_NEXT3_TAC jj' ofs' bc' : tactic =
  DISJ1_TAC THEN EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jj') THEN
  CONJ_TAC THENL [FIN2_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [jj'; ofs'; bc'] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];;

(*** At 0x3388 after a reload to ofs - bc DIV 8 with bc MOD 8 bits used, ***)
(*** two bytes left: the lookup, on to the next iteration at 0x33ac      ***)

let FIN2_L1_LOOKUP_TAC : tactic =
  let ofs' = `ofs - bc DIV 8` and bc' = `bc MOD 8` in
  let e = `huf_dentry2 ws ml 11
             (zstd_back blk (8 * (ofs - bc DIV 8) + 64 - bc MOD 8) 11)` in
  FIN2_RELOAD_POS_TAC ofs' bc' THEN
  W(fun (_,w) -> FIN2_LOOKUP_TAC (rand w) ofs' bc') THEN
  ZSTD2_SIM_UNTIL_TAC [0x33ac] THEN
  W(fun (_,w) -> FIN2_STEP_FACTS_TAC (rand w) ofs' bc') THEN
  PUFF_FINAL_TAC THEN
  FIN2_NEXT3_TAC (subst [e,`e:num list`] `jj + EL 3 e`) ofs'
                 (subst [e,`e:num list`] `bc MOD 8 + EL 2 e`) THEN
  REPEAT CONJ_TAC THEN FIN2_ARITH_TAC;;

(*** After a full reload (normal, or partial when the old bits used are ***)
(*** not a multiple of 8 of them): the lookup if two bytes are left,    ***)
(*** else the loop without reloads                                      ***)

let FIN2_L1_RELOADED_TAC (partial:bool) : tactic =
  let fix =
    if partial then
      SUBGOAL_THEN `bc - 8 * bc DIV 8 = bc MOD 8`
        (fun th -> FA_STATE_REWRITE_TAC[th]) THENL
       [FIN2_ARITH_TAC; ALL_TAC]
    else ALL_TAC in
  FIN2_SLICE_TAC `ofs - bc DIV 8` THEN
  ASM_CASES_TAC `jj + 2 <= L` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x3388] THEN fix THEN FIN2_L1_LOOKUP_TAC;
    ZSTD2_SIM_UNTIL_TAC [0x3410] THEN fix THEN
    FIN2_GOON_TAC FIN2_L0POST [`ofs - bc DIV 8`,`ofs:num`]
      [`L - jj:num`; `jj:num`; `bc MOD 8`]];;

(*** After a reload clipped at the start of the block: one lookup and the ***)
(*** loop without reloads if two bytes are left, else the last byte       ***)

let FIN2_L1_CLIPPED_TAC : tactic =
  let pos = `64 - (bc - 8 * ofs)` in
  let e = `huf_dentry2 ws ml 11 (zstd_back blk (64 - (bc - 8 * ofs)) 11)` in
  let sub t = subst [e,`e:num list`] t in
  FIN2_SLICE_TAC `0` THEN
  ASM_CASES_TAC `jj + 2 <= L` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x33f4] THEN FIN2_POS_TAC pos THEN
    W(fun (_,w) ->
      FIN2_LOOKUP_GEN_TAC (rand w) pos `bc - 8 * ofs < 64`
        [SPECL [`blk:byte list`; `bc - 8 * ofs`] FIN2_INDEX0W]) THEN
    ZSTD2_SIM_UNTIL_TAC [0x3410] THEN
    W(fun (_,w) -> FIN2_STEP_FACTS_POS_TAC (rand w) pos) THEN
    FIN2_GOON_TAC FIN2_L0POST [`0`,`ofs:num`]
     [sub `L - (jj + EL 3 e)`; sub `jj + EL 3 e`;
      sub `(bc - 8 * ofs) + EL 2 e`];
    ZSTD2_SIM_UNTIL_TAC [0x3418] THEN FIN2_POS_TAC pos THEN
    FIN2_GOON_TAC FIN2_LASTPOST [`0`,`ofs:num`] [`jj:num`; `bc - 8 * ofs`]];;

let FIN2_L1_TAC : tactic =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FIN2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [FIN2_L1_RELOADED_TAC false;
    ASM_CASES_TAC `ofs = 0` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ofs = 0`))
      THEN ZSTD2_SIM_UNTIL_TAC [0x3410] THEN
      FIN2_GOON_TAC FIN2_L0POST [`0`,`ofs:num`]
        [`L - jj:num`; `jj:num`; `bc:num`];
      ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
       [FIN2_L1_RELOADED_TAC true; FIN2_L1_CLIPPED_TAC]]];;

let FIN2_L1 = prove(fin2_l1_goal, FIN2_L1_TAC);;

(*** 0x328c, the loop of a reload and five lookups while more than nine   ***)
(*** bytes are left (op + jj below the end less 9, computed as a number), ***)
(*** for the measure m = L - jj; good all through                         ***)

let fin2_end9 = `word((val(op:int64) + L) - 9):int64`;;

let fin2_l5body = list_mk_conj
 [`read PC s = word(pc + 0x328c)`; fin2_common;
  `read X2 s = word_add op (word jj) /\
   read X3 s = word_add ilowest (word ofs)`;
  mk_eq(`read X4 s`,fin2_win);
  `read X1 s = word bc /\ read X11 s = ilowest /\
   read X12 s = word_add ilowest (word 8)`;
  mk_eq(`read X13 s`,fin2_end9);
  `ofs + 8 <= LENGTH(blk:byte list) /\ jj <= L`;
  fin2_good];;

let fin2_l5inv = with_memsafe fin2_rr fin2_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],
    mk_conj(`m = L - jj`,fin2_l5body))));;

let fin2_l5_goal = mk_fin2_goal []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(fin2_l5inv,[`m:num`; `s:armstate`]))))
  fin2_post;;

(*** 0x31b8, the body of five lookups after a reload (at most 7 bits ***)
(*** used), with at least ten bytes left                             ***)

let fin2_b5body = list_mk_conj
 [`read PC s = word(pc + 0x31b8)`; fin2_common;
  `read X2 s = word_add op (word jj) /\
   read X3 s = word_add ilowest (word ofs)`;
  mk_eq(`read X4 s`,fin2_win);
  `read X1 s = word bc /\ read X11 s = ilowest /\
   read X12 s = word_add ilowest (word 8) /\ read X14 s = word 1`;
  mk_eq(`read X13 s`,fin2_end9);
  `ofs + 8 <= LENGTH(blk:byte list) /\ jj + 10 <= L /\ bc <= 7`;
  fin2_good];;

let fin2_b5 = with_memsafe fin2_rr fin2_wr
  (mk_abs(`s:armstate`,fin2_b5body));;

let fin2_b5_goal = mk_fin2_goal [`jj:num`; `ofs:num`; `bc:num`] fin2_b5
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     mk_conj(`m < L - jj`,
             list_mk_comb(fin2_l5inv,[`m:num`; `s:armstate`])))));;

(*** The lookups of the body: the entry e at the position after the bits ***)
(*** bp used, the lookup after jp bytes and bp bits, and the facts after ***)
(*** lookup i with the bytes and bits after it abbreviated as ji and bi  ***)
(*** (bounded by those of the body); the stores of the symbols merged    ***)
(*** into the bytes, at addresses op + j with the sums of the registers  ***)
(*** folded (with the abbreviation of the bytes before)                  ***)

let fin2_b5_entry bp =
  let pos = subst [bp,`bc:num`] `8 * ofs + 64 - bc` in
  pos,list_mk_icomb "huf_dentry2"
        [`ws:num list`; `ml:num`; `11`;
         list_mk_icomb "zstd_back" [`blk:byte list`; pos; `11`]];;

let FIN2_B5_LOOKUP_TAC bp : tactic =
  let pos,_ = fin2_b5_entry bp in
  let cnd = subst [bp,`bc:num`] `bc < 64 /\ (11 + bc <= 64 \/ ofs = 0)` in
  W(fun (_,w) ->
    FIN2_LOOKUP_GEN_TAC (rand w) pos cnd
     [SPECL [`blk:byte list`; `ofs:num`; bp] FIN2_INDEX2;
      SPECL [`blk:byte list`; `ofs:num`; bp] FIN2_INDEX2W]) THEN
  DISCARD_ASSUMPTIONS_TAC(fun th -> concl th = cnd);;

let FIN2_DROP_TABLE_TAC : tactic =
  let pat1 = `read (memory :> bytes8 (word_add dt a)) s = x`
  and pat2 = `read (memory :> bytes16 (word_add dt a)) s = x` in
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> can (term_match [`dt:int64`] pat1) (concl th) ||
              can (term_match [`dt:int64`] pat2) (concl th));;

let FIN2_B5_STEP_TAC i jp bp (prev:term option) : tactic =
  let pos,e = fin2_b5_entry bp in
  let el k = mk_icomb(mk_icomb(`EL:num->num list->num`,mk_small_numeral k),
                      e) in
  let n = string_of_int i in
  let ji = mk_var("j"^n,`:num`) and bi = mk_var("b"^n,`:num`) in
  let jt = mk_binop `(+):num->num->num` jp (el 3)
  and bt = mk_binop `(+):num->num->num` (el 2) bp in
  let dec j = list_mk_icomb "huf_decode"
    [`ws:num list`; `ml:num`; `blk:byte list`; `p:num`; j] in
  let fsts j = mk_icomb(`FST:num#bool->num`,
                 mk_icomb(`SND:byte list#num#bool->num#bool`,dec j))
  and snds j = mk_icomb(`SND:num#bool->bool`,
                 mk_icomb(`SND:byte list#num#bool->num#bool`,dec j))
  and fstd j = mk_icomb(`FST:byte list#num#bool->byte list`,dec j) in
  let posi = subst [bi,`bc:num`] `8 * ofs + 64 - bc` in
  let num k = mk_small_numeral k in
  let bnds = subst [ji,`j:num`; bi,`b:num`; num i,`i:num`;
                    num(2 * i),`i2:num`; num(11 * i),`i11:num`]
    `jj + i <= j /\ j <= jj + i2 /\ b <= bc + i11` in
  let pbnds = if i = 1 then [] else
    conjuncts(subst [jp,`j:num`; bp,`b:num`; num(i - 1),`i:num`;
                     num(2 * (i - 1)),`i2:num`; num(11 * (i - 1)),`i11:num`]
      `jj + i <= j /\ j <= jj + i2 /\ b <= bc + i11`) in
  let len12 = mk_disj(mk_eq(el 3,`1`),mk_eq(el 3,`2`))
  and nb11 = mk_binop `(<=):num->num->bool` (el 2) `11` in
  let facts = [mk_eq(jt,ji); mk_eq(bt,bi); len12; nb11; `bc <= 7`] @ pbnds in
  let USE_TAC = MAP_EVERY (fun t -> MP_TAC(ASSUME t)) facts THEN ARITH_TAC in
  FA_STATE_REWRITE_TAC
   ([GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] @
    (match prev with Some t -> [ASSUME t] | None -> [])) THEN
  W(fun (_,w) -> FIN2_STEP_FACTS_GEN_TAC (rand w) jp pos) THEN
  FA_STATE_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ABBREV_TAC (mk_eq(ji,jt)) THEN ABBREV_TAC (mk_eq(bi,bt)) THEN
  SUBGOAL_THEN bnds STRIP_ASSUME_TAC THENL [USE_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(fsts ji,posi)) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> let c = concl th in
      if is_eq c && lhs c = fsts ji && not(rhs c = posi)
      then REWRITE_TAC[th] else NO_TAC) THEN
    USE_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && lhs c = fsts ji && not(rhs c = posi)
    then ALL_TAC else NO_TAC) THEN
  SUBGOAL_THEN (snds ji) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_iff c && lhs c = snds ji then REWRITE_TAC[th] else NO_TAC) THEN
    USE_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && lhs c = fstd ji then FA_STATE_REWRITE_TAC[GSYM th]
    else NO_TAC) THEN
  FIN2_DROP_TABLE_TAC THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (el 3) `2`) ASSUME_TAC THENL
   [MP_TAC(ASSUME len12) THEN ARITH_TAC; ALL_TAC] THEN
  let fixed = [`op:int64`; jp] in
  DISCARD_ASSUMPTIONS_TAC(fun th -> let c = concl th in
    c = len12 ||
    is_iff c && lhs c = snds ji ||
    is_eq c && (lhs c = fsts jp || lhs c = fstd ji) || c = snds jp ||
    can (term_match fixed
          (subst [jp,`j:num`] `read (memory :> bytes(op,j)) s = x`)) c ||
    can (term_match fixed
          (subst [jp,`j:num`]
            `read (memory :> bytes16(word_add op (word j))) s = x`)) c);;

(*** The body from 0x31b8: the five lookups, the second to fifth with the ***)
(*** bytes and bits after the one before                                  ***)

let FIN2_B5_TAC : tactic =
  let e_of b = subst [b,`bc:num`]
    `huf_dentry2 ws ml 11 (zstd_back blk (8 * ofs + 64 - bc) 11)` in
  let prev j b j' =
    Some(mk_eq(subst [j,`j:num`; e_of b,`e:num list`] `j + EL 3 e`,j')) in
  let js = [`jj:num`; `j1:num`; `j2:num`; `j3:num`; `j4:num`]
  and bs = [`bc:num`; `b1:num`; `b2:num`; `b3:num`; `b4:num`]
  and pcs = [0x31f0; 0x3218; 0x3240; 0x3268; 0x328c] in
  let step i =
    let jp = el (i - 1) js and bp = el (i - 1) bs in
    FIN2_B5_LOOKUP_TAC bp THEN ZSTD2_SIM_UNTIL_TAC [el (i - 1) pcs] THEN
    FIN2_B5_STEP_TAC i jp bp
      (if i = 1 then None else prev (el (i - 2) js) (el (i - 2) bs) jp) in
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FIN2_OPVAL_TAC [`jj:num`] THEN
  ZSTD2_SIM_UNTIL_TAC [0x31c8] THEN MAP_EVERY step (1--5) THEN
  PUFF_FINAL_TAC THEN
  EXISTS_TAC `L - j5:num` THEN CONJ_TAC THENL [FIN2_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`j5:num`; `ofs:num`; `b5:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIN2_ARITH_TAC;;

let FIN2_B5 = prove(fin2_b5_goal, FIN2_B5_TAC);;

(*** The loop: the body to a later iteration, the X13 of the comparisons ***)
(*** with op + jj as a number, and the bits used after a partial reload  ***)

let FIN2_B5_WTAC : tactic =
  GEN_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ASSUME `j0 <= L`];;

let FIN2_END9_TAC : tactic =
  SUBGOAL_THEN `val(word((val(op:int64) + L) - 9):int64) = (val op + L) - 9`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MAP_EVERY UNDISCH_TAC
     [`val(op:int64) + rest < 2 EXP 64`; `MIN q rest = L`] THEN
    REWRITE_TAC[MIN] THEN ARITH_TAC;
    ALL_TAC];;

let FIN2_MOD8_TAC : tactic =
  SUBGOAL_THEN `bc - 8 * bc DIV 8 = bc MOD 8`
    (fun th -> FA_STATE_REWRITE_TAC[th]) THENL
   [FIN2_ARITH_TAC; ALL_TAC];;

(*** After a full reload (normal, or partial): the body if more than ***)
(*** nine bytes are left, else the loop of one lookup if two are,    ***)
(*** else the last byte                                              ***)

let FIN2_L5_RELOADED_TAC (partial:bool) : tactic =
  let fix = if partial then FIN2_MOD8_TAC else ALL_TAC in
  let ofs' = `ofs - bc DIV 8` and bc' = `bc MOD 8` in
  FIN2_SLICE_TAC ofs' THEN
  ASM_CASES_TAC `jj + 10 <= L` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x31b8] THEN fix THEN
    FIN2_GOON_GEN_TAC FIN2_B5_WTAC FIN2_B5 [ofs',`ofs:num`; bc',`bc:num`] [];
    ASM_CASES_TAC `jj + 2 <= L` THENL
     [ZSTD2_SIM_UNTIL_TAC [0x33ac] THEN fix THEN
      FIN2_GOON_TAC FIN2_L1 [] [`L - jj:num`; `jj:num`; ofs'; bc'];
      ZSTD2_SIM_UNTIL_TAC [0x3418] THEN fix THEN
      FIN2_GOON_TAC FIN2_LASTPOST [ofs',`ofs:num`] [`jj:num`; bc']]];;

(*** At the start of the block, or after a reload clipped at it: with ***)
(*** bc' bits used at ofs = 0 (position pos), the loop of one lookup  ***)
(*** if two bytes are left, else the last byte                        ***)

let FIN2_L5_START_TAC bc' (pos:term option) : tactic =
  let postac = match pos with Some t -> FIN2_POS_TAC t | None -> ALL_TAC in
  ASM_CASES_TAC `jj + 2 <= L` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x33ac] THEN postac THEN
    FIN2_GOON_TAC FIN2_L1 [] [`L - jj:num`; `jj:num`; `0`; bc'];
    ZSTD2_SIM_UNTIL_TAC [0x3418] THEN postac THEN
    FIN2_GOON_TAC FIN2_LASTPOST [`0`,`ofs:num`] [`jj:num`; bc']];;

let FIN2_L5_TAC : tactic =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FIN2_OPVAL_TAC [`jj:num`] THEN FIN2_END9_TAC THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [FIN2_L5_RELOADED_TAC false;
    ASM_CASES_TAC `ofs = 0` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ofs = 0`))
      THEN FIN2_L5_START_TAC `bc:num` None;
      ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
       [FIN2_L5_RELOADED_TAC true;
        FIN2_SLICE_TAC `0` THEN
        FIN2_L5_START_TAC `bc - 8 * ofs` (Some `64 - (bc - 8 * ofs)`)]]];;

let FIN2_L5 = prove(fin2_l5_goal, FIN2_L5_TAC);;

(*** 0x3140, the start of the finish of a stream: the end of the segment, ***)
(*** the error -20 at 0x3338 when the stream has not reached 8 bytes      ***)
(*** before its end (u + 8 < a, as 4X1), else the container and the bits  ***)
(*** used, and the loop of five lookups, or for at most 7 bytes left a    ***)
(*** reload and the loop of one lookup or the last byte                   ***)

let fin2_head = with_memsafe fin2_rr fin2_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x3140)`;
  `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
   read X0 s = argk /\ read X5 s = dt /\ read X9 s = word q /\
   read X19 s = op /\ read X21 s = word_add op (word rest) /\
   read SP s = word_sub stackpointer (word 496) /\
   aligned 16 (stackpointer:int64) /\
   read (memory :> bytes64
          (word_add (word_sub stackpointer (word 496)) (word 448))) s =
   ilowest /\
   read (memory :> bytes(ilowest,LENGTH(blk:byte list))) s =
   num_of_bytelist blk /\
   read (memory :> bytes(dt,8192)) s = num_of_bytelist(huf_dtable2 ws ml 11)`;
  subst [fl_cont `u:num` `sh:num`,`c:int64`]
  `read (memory :> bytes64 argk) s = word_add ilowest (word u) /\
   read (memory :> bytes64 (word_add argk (word 32))) s =
   word_add op (word j0) /\
   read (memory :> bytes64 (word_add argk (word 64))) s = (c:int64) /\
   read (memory :> bytes64 (word_add argk (word 120))) s =
   word_add ilowest (word a)`;
  `read (memory :> bytes(op,j0)) s =
   num_of_bytelist(FST(huf_decode ws ml blk p j0)) /\
   FST(SND(huf_decode ws ml blk p j0)) = 8 * u + 64 - sh /\
   SND(SND(huf_decode ws ml (blk:byte list) p j0)) /\
   sh <= 8 /\ u + 8 <= LENGTH(blk:byte list) /\ j0 <= L /\
   a <= LENGTH(blk:byte list)`]));;

let fin2_hpost = with_memsafe fin2_rr fin2_wr `\s.
  read PC s = word(pc + 0x344c) /\ read X19 s = word_add op (word L) /\
  read (memory :> bytes64 (word_add argk (word 32))) s =
  word_add op (word L) /\
  (SND(SND(huf_decode ws ml blk p L))
   ==> read (memory :> bytes(op,L)) s =
       num_of_bytelist(FST(huf_decode ws ml (blk:byte list) p L))) \/
  read PC s = word(pc + 0x3338) /\ u + 8 < a`;;

let fin2_head_goal =
  mk_fin2_goal [`u:num`; `sh:num`; `a:num`] fin2_head fin2_hpost;;

(*** The end of the segment less 9 for the comparisons of the loop ***)

let FIN2_END9 = prove
 (`!(op:int64) L.
     9 <= val op + L /\ val op + L < 2 EXP 64
     ==> word_sub (word_add op (word L)) (word 9):int64 =
         word((val op + L) - 9)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add (op:int64) (word L) = word(((val op + L) - 9) + 9)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `9 <= x ==> (x - 9) + 9 = x`] THEN
    REWRITE_TAC[WORD_ADD; WORD_VAL];
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(*** The arithmetic and the pieces to go on with, from the variables of ***)
(*** the head                                                           ***)

let FIN2_HEAD_ARITH_TAC =
  FA_ARITHV_TAC [`u:num`; `sh:num`; `j0:num`; `L:num`; `ml:num`;
                 `blk:byte list`];;

let FIN2_HEAD_GOON_TAC =
  FIN2_GOON_ARITH_TAC FIN2_HEAD_ARITH_TAC FIN_HEAD_WTAC;;

let FIN2_SHMOD8_TAC : tactic =
  SUBGOAL_THEN `sh - 8 * sh DIV 8 = sh MOD 8`
    (fun th -> FA_STATE_REWRITE_TAC[th]) THENL
   [FIN2_HEAD_ARITH_TAC; ALL_TAC];;

(*** At most 7 bytes left, after the reload to ofs' with bc' bits used ***)
(*** (fix for the form of the bits): the loop of one lookup if two     ***)
(*** bytes are left, else the last byte                                ***)

let FIN2_HEAD_SHORT_TAC ofs' bc' fix : tactic =
  ASM_CASES_TAC `j0 + 2 <= L` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x33ac] THEN fix THEN
    FIN2_HEAD_GOON_TAC FIN2_L1 [] [`L - j0:num`; `j0:num`; ofs'; bc'];
    ZSTD2_SIM_UNTIL_TAC [0x3418] THEN fix THEN
    FIN2_HEAD_GOON_TAC FIN2_LASTPOST [ofs',`ofs:num`] [`j0:num`; bc']];;

let FIN2_HEAD_TAC : tactic =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ZSTD2_SIM_UNTIL_TAC [0x3154] THEN
  SUBGOAL_THEN `q < 2 EXP 64 /\ rest < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`q < 2 EXP 28`; `val(op:int64) + rest < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FA_STATE_REWRITE_TAC[MP (SPECL [`op:int64`; `q:num`; `rest:num`] FIN_CSEL)
    (CONJ (ASSUME `q < 2 EXP 64`) (ASSUME `rest < 2 EXP 64`))] THEN
  FA_STATE_REWRITE_TAC[ASSUME `MIN q rest = L`] THEN
  FIN_HEAD_VAL_TAC THEN ZSTD2_SIM_UNTIL_TAC [0x315c] THEN
  ASM_CASES_TAC `u + 8 < a` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x3338] THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIN2_SLICE_TAC `u:num` THEN ZSTD2_SIM_UNTIL_TAC [0x3190] THEN
  FIN_SETUP_TAC THEN
  MP_TAC(SPECL [`sh:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `7 < L - j0` THENL
   [SUBGOAL_THEN `9 <= val(op:int64) + L /\ val op + L < 2 EXP 64`
     STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`~(val(op:int64) = 0)`; `7 < L - j0`;
        `val(op:int64) + rest < 2 EXP 64`; `MIN q rest = L`] THEN
      REWRITE_TAC[MIN] THEN ARITH_TAC;
      ALL_TAC] THEN
    ZSTD2_SIM_UNTIL_TAC [0x328c] THEN
    FA_STATE_REWRITE_TAC[MP (SPECL [`op:int64`; `L:num`] FIN2_END9)
     (CONJ (ASSUME `9 <= val(op:int64) + L`)
           (ASSUME `val(op:int64) + L < 2 EXP 64`))] THEN
    FIN2_HEAD_GOON_TAC FIN2_L5 [] [`L - j0:num`; `j0:num`; `u:num`; `sh:num`];
    ALL_TAC] THEN
  ASM_CASES_TAC `8 <= u` THENL
   [FIN2_SLICE_TAC `u - sh DIV 8` THEN
    FIN2_HEAD_SHORT_TAC `u - sh DIV 8` `sh MOD 8` ALL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `u = 0` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `u = 0`)) THEN
    FIN2_HEAD_SHORT_TAC `0` `sh:num` ALL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sh DIV 8 <= u` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`sh <= 8`; `~(u = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIN2_SLICE_TAC `u - sh DIV 8` THEN
  FIN2_HEAD_SHORT_TAC `u - sh DIV 8` `sh MOD 8` FIN2_SHMOD8_TAC;;

let FIN2_HEAD = prove(fin2_head_goal, FIN2_HEAD_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole function (HUF_DECOMPRESS4X2_USINGDTABLE_CORRECT): the prologue, *)
(* the slow path (SP2ALL_CORRECT) when bit 5 of the flags is set or the fast *)
(* path does not apply, else HUF_DecompressFastArgs_init, the fast loop and  *)
(* the finishes of the four streams.                                         *)
(* ------------------------------------------------------------------------- *)

(*** The whole of HUF_decompress4X2_usingDTable_internal at 0x30c0, as  ***)
(*** the TOP_* proof of 4X1 (the same shape of code): the slow path     ***)
(*** (SP2ALL_CORRECT) when bit 5 of the flags is set or the fast        ***)
(*** arguments do not apply, else the fast loop and the finishes of the ***)
(*** four streams; the frame of 496 bytes and the 320 of the fast loop  ***)
(*** below it                                                           ***)

(*** The steps and the run to the return in the code of the function ***)

let TOP2_STEPS_TAC k : tactic =
  W(fun gl -> let n = top_state_num gl in
              MAP_EVERY ZSTD2_STEP_TAC ((n+1)--(n+k)));;

let ZSTD2_RUN_TAC =
  let num_of_state s =
    let n = fst(dest_var s) in
    int_of_string(String.sub n 1 (String.length n - 1)) in
  let rec run k n (asl,w as gl) =
    let pc = current_pc gl in
    if pc = `returnaddress:int64` then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "ZSTD2_RUN_TAC"
    else (ZSTD2_STEP_TAC n THEN run (k - 1) (n + 1)) gl in
  fun (asl,w as gl) -> run 40 (num_of_state(rand w) + 1) gl;;

(*** The derived facts about the regions ***)

let TOP2_REGIONS_TAC =
  SUBGOAL_THEN
   `nonoverlapping (dst:int64,n) (word_add dtable (word 4),4 * 2 EXP tl) /\
    nonoverlapping (word_sub stackpointer (word 816),816)
                   (word_add dtable (word 4),4 * 2 EXP tl) /\
    nonoverlapping (word_sub stackpointer (word 816),816) (dtable,4) /\
    nonoverlapping (word_add dtable (word 4),4 * 2 EXP tl) (word pc,32000) /\
    nonoverlapping (src:int64,LENGTH(blk:byte list))
                   (word_add dtable (word 4),4 * 2 EXP tl) /\
    nonoverlapping (dst:int64,n) (word_sub stackpointer (word 496),496) /\
    nonoverlapping (word_sub stackpointer (word 496),496)
                   (src,LENGTH(blk:byte list)) /\
    nonoverlapping (word_sub stackpointer (word 496),496)
                   (word_add dtable (word 4),4 * 2 EXP tl) /\
    nonoverlapping (word_sub stackpointer (word 496),496) (dtable,4) /\
    nonoverlapping (word_sub stackpointer (word 496),496) (word pc,32000)`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `tt = 2 EXP tl` THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(src:int64) + LENGTH(blk:byte list) < 2 EXP 64 /\
    val(dst:int64) + n < 2 EXP 64 /\ 1 <= tl`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`;
      `val(dst:int64) + n + 3 < 2 EXP 64`; `1 <= ml`; `ml <= tl`] THEN
    ARITH_TAC;
    ALL_TAC];;

(*** The final state: the postcondition, with the frame proved from the ***)
(*** few facts that its subsumption needs, its stack addresses rebased  ***)
(*** on the region of 816 bytes                                         ***)

let TOP2_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 496):int64 =
  word_add (word_sub stackpointer (word 816)) (word 320)`;;

let TOP2_FRAME_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE[TOP2_STACK_REBASE; WORD_ADD_ASSOC_NUM] th)
    else th) THEN
  W(fun (asl,w) ->
    let sasl = filter (fun (_,th) -> let t = concl th in
                 maychange_term t || mem t top_frame_facts) asl in
    ACCEPT_TAC(TAC_PROOF((sasl,w),
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC)));;

let TOP2_FINAL_TAC : tactic =
  GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
  GEN_REWRITE_TAC TRY_CONV [BETA_THM] THEN
  W(fun (asl,w) ->
    let mcs,ocs = partition maychange_term (conjuncts w) in
    let w' = mk_conj(list_mk_conj ocs,list_mk_conj mcs) in
    GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))]) THEN
  CONJ_TAC THENL [MEMSAFE_ELIM_TAC; TOP2_FRAME_TAC];;

(*** The slow path at 0x32d0 (SP2ALL_CORRECT), to the return ***)

let TOP2_SLOW_TAC : tactic =
  BK2_BIGSTEP_TAC SP2ALL_CORRECT top_sp_alist THEN
  TOP_RESULT_ABBREV_TAC THEN ZSTD2_RUN_TAC THEN TOP2_FINAL_TAC THEN
  ASM_REWRITE_TAC[TOP_SP_RESTORE] THEN TOP_RESULT_TAC;;

(*** The prologue, to the test of bit 5 of the flags at 0x30e8 ***)

let TOP2_PROLOGUE_TAC : tactic =
  TOP2_REGIONS_TAC THEN MAP_EVERY ZSTD2_STEP_TAC (1--11) THEN
  ASM_CASES_TAC `bit 5 (flags':int64)` THEN
  W(fun (asl,w) ->
    let c = snd(hd asl) and s = rand w in
    RULE_ASSUM_TAC(fun th ->
      if free_in s (concl th) then REWRITE_RULE[TOP_BIT5; c] th else th));;

(*** The calls of HUF_DecompressFastArgs_init at 0x3114 and of the fast ***)
(*** loop at 0x3128, with the arguments at sp + 344 in the frame        ***)

let TOP2_CALL_TAC : tactic =
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  W(fun gl -> ARM_BIGSTEP_TAC SLOW2_EXEC
                ("s"^string_of_int(top_state_num gl + 1))) THEN
  EVENTS_UNABBREV_TAC;;

let TOP2_FA_CALL_TAC : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(CONV_RULE TOP_ADDR_CONV (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x3118):int64`; top_args;
    `dst:int64`; `n:num`; `src:int64`; `blk:byte list`; `dtable:int64`;
    `dh:int32`; `tl:num`] HUF_DECOMPRESSFASTARGS_INIT_CORRECT)))) THEN
  TOP2_CALL_TAC;;

let TOP2_FA_TAC : tactic = TOP2_STEPS_TAC 11 THEN TOP2_FA_CALL_TAC;;

(*** The error -20 of HUF_DecompressFastArgs_init: no valid block ***)

let TOP2_ERROR_END_TAC : tactic =
  ZSTD2_RUN_TAC THEN TOP2_FINAL_TAC THEN
  ASM_REWRITE_TAC[TOP_SP_RESTORE; zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (asl,w) ->
    let th = snd(find (fun (_,th) -> concl th =
      `!out. ~(LENGTH out = n /\ huf_streams4 T ws ml blk out)`) asl) in
    MESON_TAC[th]);;

let TOP2_FA20_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_eq(lhand(concl th)) &&
    rand(lhand(concl th)) = `word 18446744073709551596:int64`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TOP_NOVALID_TAC
   (FIRST_ASSUM(MP_TAC o MATCH_MP HUF_STREAMS4_NECESSARY) THEN
    UNDISCH_TAC `LENGTH(blk:byte list) < 10 \/
                 LENGTH blk <
                 6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2` THEN
    ARITH_TAC) THEN
  TOP2_ERROR_END_TAC;;

(*** The fast path: HUF_DecompressFastArgs_init returned 1, so tl = 11 ***)
(*** and the table is of 8192 bytes                                    ***)

let TOP2_FA1_SETUP_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_eq(lhand(concl th)) &&
    rand(lhand(concl th)) = `word 1:int64`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_imp(concl th) && is_eq(lhand(concl th)) &&
    rand(lhand(concl th)) = `word 18446744073709551596:int64`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `tl = 11`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * 2 EXP 11 = 8192`]) THEN
  ABBREV_TAC `q = (n + 3) DIV 4` THEN
  SUBGOAL_THEN
   `3 * q <= n /\ n <= 4 * q /\ n - 3 * q <= q /\ q < 2 EXP 28 /\
    2 * q <= n /\ q <= n /\ ~(n - 3 * q = 0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(n + 3) DIV 4 = q`; `3 * q < n`; `n < 2 EXP 28`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`dst:int64`; top_o k] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(dst:int64) + n + 3 < 2 EXP 64`; `3 * q <= n`] THEN ARITH_TAC;
      DISCH_TAC])
   [1;2;3] THEN
  SUBGOAL_THEN `val(word_add dst (word (3 * q)):int64) + n - 3 * q < 2 EXP 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(dst:int64) + n + 3 < 2 EXP 64`; `3 * q <= n`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add dst (word n):int64 =
    word_add (word_add dst (word (3 * q))) (word (n - 3 * q))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `3 * q <= n` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FA_STATE_REWRITE_TAC[MP (SPECL [`dst:int64`; `n:num`] TOP_X21_LEMMA)
    (CONJ (ASSUME `~(n = 0)`) (ASSUME `n < 2 EXP 28`))];;

(*** The call of the fast loop at 0x3128: the facts for its hypotheses ***)
(*** about the outputs                                                 ***)

let TOP2_FL_FACTS_TAC : tactic =
  SUBGOAL_THEN
   `word_add (word_add (dst:int64) (word q)) (word q) =
    word_add dst (word (2 * q)) /\
    word_add (word_add (dst:int64) (word (2 * q))) (word q) =
    word_add dst (word (3 * q)) /\
    val(dst:int64) + q + q + q + n - 3 * q < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`val(dst:int64) + n + 3 < 2 EXP 64`; `3 * q <= n`] THEN ARITH_TAC];
    ALL_TAC];;

let top2_fl_alist =
  [("returnaddress",`word(pc + 0x312c):int64`);
   ("stackpointer",`word_sub stackpointer (word 496):int64`);
   ("args",top_args); ("ilowest",`src:int64`);
   ("dt",`word_add dtable (word 4):int64`);
   ("oend",`word_add dst (word n):int64`)] @
  map (fun k -> ("op"^string_of_int k,top_op k)) [0;1;2;3] @
  map (fun k -> ("sz"^string_of_int k,top_L k)) [0;1;2;3] @
  map (fun k -> ("p"^string_of_int k,top_p k)) [0;1;2;3];;

let TOP2_FL_CALL_TAC : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun gl ->
    let th = ml_inst_thm HUF_DECOMPRESS4X2_FAST_C_LOOP_CORRECT
               (("e",current_events gl)::top2_fl_alist) in
    MP_TAC(CONV_RULE(TOP_ADDR_CONV THENC ONCE_DEPTH_CONV NUM_ADD_CONV)
             (REWRITE_RULE[WORD_SUB_SUB_NUM] th))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  W(fun gl -> ARM_BIGSTEP_TAC SLOW2_EXEC
                ("s"^string_of_int(top_state_num gl + 1))) THEN
  W(fun (_,w) ->
    if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                     with Failure _ -> false)
    then EVENTS_UNABBREV_TAC else TOP_FL_PRE_TAC);;

let TOP2_FL_TAC : tactic = TOP2_STEPS_TAC 5 THEN TOP2_FL_CALL_TAC;;

(*** A big step with a theorem th instantiated by names, its addresses ***)
(*** normalized, its hypotheses from the assumptions                   ***)

let TOP2_BIGSTEP_TAC th alist : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun gl ->
    let th' = CONV_RULE TOP_ADDR_CONV
                (ml_inst_thm th (("e",current_events gl)::alist)) in
    let n = top_state_num gl in
    MP_TAC th' THEN ANTS_TAC THENL [ML_HYP_TAC; ALL_TAC] THEN
    ARM_BIGSTEP_TAC SLOW2_EXEC ("s"^string_of_int(n + 1)) THEN
    W(fun (_,w) ->
      if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                       with Failure _ -> false)
      then EVENTS_UNABBREV_TAC THEN MEMSAFE_STRIP_TAC
      else REPEAT CONJ_TAC THEN
           FIRST [ML_PRE_MEMSAFE_TAC; ML_FACT_TAC; T4_CONJ_TAC]));;

(*** The finish of stream k at 0x3140 (FIN2_HEAD), with the bytes jk ***)
(*** that the fast loop decoded                                      ***)

let top2_j k = mk_var("j"^string_of_int k,`:num`);;

let top2_fin_alist k gl =
  map (fun (v,t) -> if v = "j0" then (v,top2_j k) else (v,t))
      (top_fin_alist k gl);;

let TOP2_FIN_TAC k : tactic =
  TOP_FIN_PREP_TAC k THEN
  W(fun gl -> TOP2_BIGSTEP_TAC FIN2_HEAD (top2_fin_alist k gl));;

(*** The error of the finish of stream k: its pointer below its start, ***)
(*** which no valid block can give                                     ***)

let TOP2_FINERR_TAC k : tactic =
  W(fun gl ->
  let u,sh = top_fin_vars k gl in
  TOP_NOVALID_TAC
   (MP_TAC(SPECL [`ws:num list`; `ml:num`; `blk:byte list`; `out:byte list`;
                  `n:num`; `q:num`] HUF_STREAMS4_FAST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ws:num list`; `ml:num`; `blk:byte list`; top_p k;
                   top2_j k; top_L k; list_mk_icomb "zstd_sublist"
                     [`out:byte list`; top_o k; top_L k];
                   top_a k; u; sh] HUF_DECODE_START_LE) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [mk_binop `(<=):num->num->bool` (top2_j k) (top_L k);
      mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` u `8`)
               (top_a k)] THEN
    ARITH_TAC) THEN
  TOP2_ERROR_END_TAC);;

(*** After the finish of stream k, at 0x344c: the bytes of its segment ***)
(*** as mk, then on to the next stream                                 ***)

let TOP2_NEXT_TAC k : tactic =
  let m = mk_var("m"^string_of_int k,`:num`) in
  W(fun (asl,w) ->
    let s = rand w in
    ABBREV_TAC (mk_eq(m,subst [top_op k,`a:int64`; top_L k,`l:num`;
                               s,`s:armstate`]
                          `read (memory :> bytes(a,l)) s`))) THEN
  TOP2_STEPS_TAC 3;;

(*** The end of the fast path: n, and the bytes of the four segments ***)

let TOP2_FAST_END_TAC : tactic =
  ZSTD2_RUN_TAC THEN TOP2_FINAL_TAC THEN
  ASM_REWRITE_TAC[TOP_SP_RESTORE] THEN
  REWRITE_TAC[MATCH_MP SP_BYTES4 (ASSUME `3 * q <= n`)] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HUF_STREAMS4_FAST_RESULT THEN
  REPEAT CONJ_TAC THEN ML_FACT_TAC;;

(*** The four streams, from 0x3140 ***)

let rec TOP2_PASSES_TAC k : tactic =
  TOP2_FIN_TAC k THENL
   [TOP2_NEXT_TAC k THEN
    (if k = 3 then TOP2_FAST_END_TAC else TOP2_PASSES_TAC (k + 1));
    TOP2_FINERR_TAC k];;

(*** The arithmetic facts that the preconditions of the finishes need: ***)
(*** the ends of the streams in the block, the outputs not at 0        ***)

let TOP2_FIN_FACTS_TAC : tactic =
  let one t =
    SUBGOAL_THEN t ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC top_fa_ok THEN ARITH_TAC; ALL_TAC] in
  let nz k =
    let v = mk_comb(`val:int64->num`,top_op k) in
    let eq = mk_eq(v,mk_binop `(+):num->num->num` `val(dst:int64)`
                              (top_o k)) in
    SUBGOAL_THEN (mk_neg(mk_eq(v,`0`))) ASSUME_TAC THENL
     [MP_TAC(ASSUME eq) THEN UNDISCH_TAC `~(val(dst:int64) = 0)` THEN
      ARITH_TAC;
      ALL_TAC] in
  MAP_EVERY one
   (map (fun k -> mk_binop `(<=):num->num->bool` (top_a k)
                    `LENGTH(blk:byte list)`) [0;1;2;3]) THEN
  MAP_EVERY nz [1;2;3];;

(*** The paths after HUF_DecompressFastArgs_init: 0, the slow path; 1, the ***)
(*** fast loop and the finishes of the four streams                        ***)

let TOP2_FA0_TAC = TOP2_STEPS_TAC 3 THEN TOP2_SLOW_TAC;;

let TOP2_FAST_SETUP_TAC : tactic =
  TOP2_FA1_SETUP_TAC THEN TOP2_FL_FACTS_TAC THEN TOP2_FL_TAC THEN
  TOP_HIDE_TAC THEN
  TOP2_STEPS_TAC 5 THEN FA_STATE_REWRITE_TAC[ASSUME `(n + 3) DIV 4 = q`] THEN
  TOP2_FIN_FACTS_TAC;;

let TOP2_FA1_TAC : tactic =
  TOP2_FAST_SETUP_TAC THEN TOP2_PASSES_TAC 0;;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For the block blk of four streams at src, the decoding  *)
(* table (built by HUF_readDTableX2_wksp) for the weights ws, with codes of  *)
(* at most ml bits and a table of tl bits, at DTable + 4, its header holding *)
(* tl at DTable + 2, and the n bytes at dst (not at address 0): if blk is    *)
(* the four streams of the n bytes out (huf_streams4 T), the result is n,    *)
(* with out at dst; and the result is always n or an error code. The loads   *)
(* are from the block, the table and its header and the stack, the stores   *)
(* to the n bytes at dst and the stack, whose region of 816 bytes is the     *)
(* frame of 496 bytes and the 320 bytes of the fast loop below it.           *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS4X2_USINGDTABLE_CORRECT = prove
 (`!pc returnaddress stackpointer dst n src (blk:byte list) dtable flags
    ws ml tl e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\
     huf_complete ws ml /\ LENGTH ws <= 256 /\
     1 <= ml /\ ml <= tl /\ tl <= 12 /\
     n < 2 EXP 28 /\ val(dst:int64) + n + 3 < 2 EXP 64 /\ ~(val dst = 0) /\
     8 <= val(src:int64) /\ val src + LENGTH blk + 8 < 2 EXP 64 /\
     LENGTH blk < 2 EXP 32 /\
     nonoverlapping (dst,n) (src,LENGTH blk) /\
     nonoverlapping (dst,n) (dtable,4 + 4 * 2 EXP tl) /\
     nonoverlapping (dst,n) (word_sub stackpointer (word 816),816) /\
     nonoverlapping (dst,n) (word pc,32000) /\
     nonoverlapping (word_sub stackpointer (word 816),816) (src,LENGTH blk) /\
     nonoverlapping (word_sub stackpointer (word 816),816)
                    (dtable,4 + 4 * 2 EXP tl) /\
     nonoverlapping (word_sub stackpointer (word 816),816) (word pc,32000) /\
     nonoverlapping (src,LENGTH blk) (dtable,4 + 4 * 2 EXP tl) /\
     nonoverlapping (src,LENGTH blk) (word pc,32000) /\
     nonoverlapping (dtable,4 + 4 * 2 EXP tl) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x30c0) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; word n; src; word(LENGTH blk); dtable;
                            flags] s /\
               read (memory :> bytes(src,LENGTH blk)) s =
               num_of_bytelist blk /\
               read (memory :> bytes8(word_add dtable (word 2))) s = word tl /\
               read (memory :> bytes(word_add dtable (word 4),4 * 2 EXP tl))
                    s =
               num_of_bytelist(huf_dtable2 ws ml tl) /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!out. LENGTH out = n /\ huf_streams4 T ws ml blk out
                      ==> read X0 s = word n /\
                          read (memory :> bytes(dst,n)) s =
                          num_of_bytelist out) /\
               (read X0 s = word n \/ zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH blk; dtable,4 + 4 * 2 EXP tl;
                       word_sub stackpointer (word 816),816]
                      [dst,n; word_sub stackpointer (word 816),816]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,n);
                      memory :> bytes(word_sub stackpointer (word 816),816)])`,
  TOP_START_TAC THEN TOP2_PROLOGUE_TAC THENL
   [TOP2_SLOW_TAC;
    TOP2_FA_TAC THENL [TOP2_FA0_TAC; TOP2_FA1_TAC; TOP2_FA20_TAC]]);;

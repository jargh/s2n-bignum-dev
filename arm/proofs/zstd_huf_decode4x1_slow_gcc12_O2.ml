(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The slow path of HUF_decompress4X1_usingDTable_internal, zstd's decoding  *)
(* of Huffman-coded literals in four streams with single-symbol tables,      *)
(* compiled by gcc 12 at -O2 for AArch64: from 0x5458, where the function    *)
(* goes when its fast path does not apply, to 0x5444, where it restores its  *)
(* callee-saved registers and returns, with the result n and the output for  *)
(* a valid block and an error code otherwise (SP_CORRECT). The pieces, each  *)
(* proved in its own small context and composed by big steps, are the entry  *)
(* checks (0x5458), the initializations of the four BIT_DStreams (0x54c0),   *)
(* the setup (0x55e0) and body (0x56fc) of the main loop with the reloads of *)
(* the streams, its exits, the check of the order of the outputs (0x5ce4),   *)
(* the tails of the four streams (0x5d00, 0x5e64, 0x5fcc, 0x6134) and the    *)
(* end checks (0x6294).                                                      *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode4x1_fast_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* The tail of the fourth stream at 0x6134 (and the reloads of a stream by   *)
(* BIT_reloadDStream_internal at 0x1c20): the bytes after the main loop,     *)
(* four at a time and then one at a time, from a good state of the decoding  *)
(* (all bits of each lookup in the container) or a bad one (the stream has   *)
(* run out).                                                                 *)
(* ------------------------------------------------------------------------- *)

(*** The slow path, the tail of the fourth stream at 0x6134: the stream st ***)
(*** of LENGTH st bytes at src, from position r, decoded to the L bytes at ***)
(*** op, with BIT_DStream at sp + 344 and the table of 2^tl entries at tbl ***)

let t4_sp = `word_sub stackpointer (word 496):int64`;;

let t4_spk k = mk_comb(mk_comb(`word_add:int64->int64->int64`,t4_sp),
                       mk_comb(`word:num->int64`,mk_small_numeral k));;

let t4_rr =
 `[src,LENGTH(st:byte list); tbl,2 * 2 EXP tl;
   word_sub stackpointer (word 496),496]:(int64#num)list`
and t4_wr =
 `[op,L; word_add (word_sub stackpointer (word 496)) (word 344),24]
  :(int64#num)list`;;

let t4_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\
  huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
  ml <= tl /\ 1 <= tl /\ tl <= 12 /\ L < 2 EXP 28 /\
  8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64 /\
  val(op:int64) + L < 2 EXP 64 /\
  nonoverlapping (op,L) (src,LENGTH st) /\
  nonoverlapping (op,L) (tbl:int64,2 * 2 EXP tl) /\
  nonoverlapping (op,L) (word_sub stackpointer (word 496),496) /\
  nonoverlapping (op,L) (word pc,32000) /\
  nonoverlapping (word_sub stackpointer (word 496),496) (src,LENGTH st) /\
  nonoverlapping (word_sub stackpointer (word 496),496)
                 (tbl,2 * 2 EXP tl) /\
  nonoverlapping (word_sub stackpointer (word 496),496) (word pc,32000)`;;

let t4_frame =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X6; X12; X13; X14; X16; X17; X18;
             X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op,L);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 344),24)]`;;

let t4_vars =
 [`pc:num`; `stackpointer:int64`; `src:int64`; `st:byte list`; `op:int64`;
  `L:num`; `tbl:int64`; `tl:num`; `ws:num list`; `ml:num`; `r:num`;
  `e:uarch_event list`];;

let mk_t4_goal extra pre post =
  let tm = mk_imp(t4_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; t4_frame]) in
  let vs = t4_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_t4_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** The facts that hold all through: the code, the table, the stream and ***)
(*** the end of the output in x9, its start in x27, tl in w23             ***)

let t4_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read SP s = word_sub stackpointer (word 496) /\
  read X5 s = tbl /\ read X9 s = word_add op (word L) /\ read X27 s = src /\
  read X23 s = word tl /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl)`;;

let t4_win = `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                   2 EXP 64):int64`;;

(*** The good and the bad state of the decoding of jj bytes, at ofs with  ***)
(*** bc bits used, and the bytes stored                                    ***)

let t4_good jj =
  subst [jj,`jj:num`]
  `SND(SND(huf_decode ws ml st r jj)) /\
   FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   read (memory :> bytes(op,jj)) s =
   num_of_bytelist(FST(huf_decode ws ml (st:byte list) r jj))`;;

let t4_bad jj =
  subst [jj,`jj:num`]
  `~SND(SND(huf_decode ws ml (st:byte list) r jj)) /\ ofs = 0 /\
   64 < bc /\ bc <= 64 + 12 * jj`;;

(*** The loop for the last bytes of stream 4, at 0x6268 ***)

let T4_LOOKUP_TAC =
  ZSTD_STEPS_TAC (1--3) THEN
  MP_TAC(ISPECL [`st:byte list`; `ofs:num`; `bc:num`; `tl:num`; `c:num`;
                 `ws:num list`; `ml:num`; `tbl:int64`; `s3:armstate`]
    HUF_LOOKUP_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`st:byte list`; `8 * ofs + 64 - bc`; `tl:num`]
    ZSTD_BACK_BOUND) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back st (8 * ofs + 64 - bc) ml`] HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back st (8 * ofs + 64 - bc) ml`] HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `x = zstd_back st (8 * ofs + 64 - bc) tl` THEN
  ABBREV_TAC `y = zstd_back st (8 * ofs + 64 - bc) ml` THEN
  ABBREV_TAC `sym = huf_symbol ws y` THEN
  ABBREV_TAC `nb = (ml + 1) - EL sym ws`;;

let T4_ANY_TAC =
  ZSTD_STEPS_TAC (1--3) THEN
  MP_TAC(ISPECL [`word_jshl (word c) (word bc):int64`; `tl:num`]
    HUF_INDEX_ANY) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x = val(word_jushr (word_jshl (word c) (word bc):int64)
                                 (word (64 - tl)))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; `x:num`;
                 `s3:armstate`] HUF_DTABLE_READ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `tl:num`; `ml:num`] DIV_EXP_LT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (tl - ml)`]
    HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (tl - ml)`]
    HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `sym = huf_symbol ws (x DIV 2 EXP (tl - ml))` THEN
  ABBREV_TAC `nb = (ml + 1) - EL sym ws`;;

let T4_STEP_TAC =
  ZSTD_STEPS_TAC (4--8) THEN STATE_PTR_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_VAL]) THEN
  ASM_CASES_TAC `jj + 1 = L` THENL
   [ZSTD_STEPS_TAC (9--11); ZSTD_STEPS_TAC (9--10)];;

let T4_SUBST_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `jj + 1 = L`));;

let T4_MEM_SNOC_TAC s =
  MP_TAC(ISPECL [`op:int64`; `FST(huf_decode ws ml (st:byte list) r jj)`;
                 `word sym:byte`; s] READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[HUF_DECODE_LENGTH];;

let T4_GOOD_END_TAC,T4_GOOD_LOOP_TAC =
  let fin s =
    ASM_CASES_TAC `nb <= 8 * ofs + 64 - bc` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [T4_MEM_SNOC_TAC s THEN NO_TAC; ZSTD_ARITH_TAC] in
  (PUFF_FINAL_TAC THEN DISJ2_TAC THEN T4_SUBST_TAC THEN
   MAP_EVERY EXISTS_TAC [`ofs:num`; `bc + nb:num`] THEN
   ASM_REWRITE_TAC[HUF_DECODE_SUC] THEN fin `s11:armstate`),
  (PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `L - (jj + 1)` THEN
   CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`jj + 1`; `bc + nb:num`] THEN
   ASM_REWRITE_TAC[HUF_DECODE_SUC] THEN
   CONJ_TAC THENL [SIMPLE_ARITH_TAC; fin `s10:armstate`]);;

let T4_BAD_FACT_TAC =
  SUBGOAL_THEN `~SND(SND(huf_decode ws ml (st:byte list) r (jj + 1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[HUF_DECODE_SUC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                   `zstd_back (st:byte list) (8 * ofs + 64 - bc) ml`]
      HUF_NBITS_BOUND) THEN
    ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN ZSTD_ARITH_TAC;
    ALL_TAC];;

let T4_BAD_END_TAC,T4_BAD_LOOP_TAC =
  (T4_BAD_FACT_TAC THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN T4_SUBST_TAC THEN
   MAP_EVERY EXISTS_TAC [`ofs:num`; `bc + nb:num`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC),
  (T4_BAD_FACT_TAC THEN
   PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `L - (jj + 1)` THEN
   CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`jj + 1`; `bc + nb:num`] THEN
   ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC);;

(*** 0x6250: the check before the loop for the last bytes ***)

let T4_SHIFT_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HUF_SHIFT_WORD
    (CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`))]);;

(*** The main loop: 0x6210 (reload) and 0x6180 (4 bytes), with the flag ***)
(*** w18 of the body, BIT_DStream in memory being up to date when it is ***)
(*** 0, and the end of the output less 3 in x13                         ***)

let t4_loopregs =
 `read X12 s = word_add op (word jj) /\
  read X3 s = word_add src (word ofs) /\ read X4 s = word(64 - tl) /\
  read X13 s = word_add op (word (L - 3)) /\
  read X14 s = word_add src (word 8) /\ 3 < L /\ jj <= L`;;

let t4_rinv = with_memsafe t4_rr t4_wr (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + 0x6210)`; t4_common; t4_loopregs;
    mk_eq(`read X2 s`,t4_win);
    `read X0 s = word bc`;
    mk_disj(list_mk_conj
      [`read X18 s = word 0 /\ read X1 s = word_add src (word ofs)`;
       subst [t4_spk 344,`a:int64`; t4_win,`w:int64`]
        `read (memory :> bytes64 a) s = w`;
       subst [t4_spk 352,`a:int64`] `read (memory :> bytes32 a) s = word bc`],
      `read X18 s = word 1`);
    `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
    t4_good `jj:num`])));;

let t4_body = with_memsafe t4_rr t4_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x6180)`; t4_common; t4_loopregs;
  mk_eq(`read X2 s`,t4_win);
  `read X0 s = word bc /\ read X18 s = word 1 /\ jj + 4 <= L /\ bc <= 7`;
  `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
  t4_good `jj:num`]));;

(*** Lookup jn of the body at state sn with bcv bits used, and the state ***)
(*** of the specification after it                                      ***)

let T4_SYM_TAC sn jn bcv =
  let s = mk_var("s"^string_of_int sn,`:armstate`) in
  let n = string_of_int jn in
  let jt = if jn = 0 then `jj:num` else
           mk_binop `(+):num->num->num` `jj:num` (mk_small_numeral jn)
  and jt' = mk_binop `(+):num->num->num` `jj:num` (mk_small_numeral(jn+1)) in
  let pos = mk_binop `(+):num->num->num` `8 * ofs`
              (mk_binop `(-):num->num->num` `64` bcv) in
  let xv = mk_var("x"^n,`:num`) and yv = mk_var("y"^n,`:num`)
  and symv = mk_var("sym"^n,`:num`) and nbv = mk_var("nb"^n,`:num`) in
  let back k = list_mk_icomb "zstd_back" [`st:byte list`; pos; k] in
  let dec t = list_mk_icomb "huf_decode"
                [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; t] in
  let fsts t = mk_icomb(`FST:num#bool->num`,
                        mk_icomb(`SND:byte list#num#bool->num#bool`,dec t))
  and snds t = mk_icomb(`SND:num#bool->bool`,
                        mk_icomb(`SND:byte list#num#bool->num#bool`,dec t))
  and fst t = mk_icomb(`FST:byte list#num#bool->byte list`,dec t) in
  let goal = list_mk_conj
   [mk_eq(fsts jt',mk_binop `(+):num->num->num` `8 * ofs`
      (mk_binop `(-):num->num->num` `64`
         (mk_binop `(+):num->num->num` nbv bcv)));
    snds jt';
    mk_eq(fst jt',list_mk_icomb "APPEND"
      [fst jt; mk_list([mk_comb(`word:num->byte`,symv)],`:byte`)])] in
  let split = if jn = 0 then ALL_TAC else
    REWRITE_TAC[ARITH_RULE(mk_eq(jt',mk_binop `(+):num->num->num` jt `1`))] in
  MP_TAC(ISPECL [`st:byte list`; `ofs:num`; bcv; `tl:num`; `c:num`;
                 `ws:num list`; `ml:num`; `tbl:int64`; s]
    HUF_LOOKUP_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FA_ARITHV_TAC [`ml:num`; `tl:num`]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`st:byte list`; pos; `tl:num`] ZSTD_BACK_BOUND) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; back `ml:num`] HUF_SYMBOL_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC (mk_eq(xv,back `tl:num`)) THEN
  ABBREV_TAC (mk_eq(yv,back `ml:num`)) THEN
  ABBREV_TAC (mk_eq(symv,list_mk_icomb "huf_symbol" [`ws:num list`; yv])) THEN
  ABBREV_TAC (mk_eq(nbv,mk_binop `(-):num->num->num` `ml + 1`
                    (list_mk_icomb "EL" [symv; `ws:num list`]))) THEN
  SUBGOAL_THEN goal STRIP_ASSUME_TAC THENL
   [split THEN ONCE_REWRITE_TAC[HUF_DECODE_SUC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FA_ARITHV_TAC [`ml:num`; `tl:num`];
    ALL_TAC];;

let T4_DROP_TABLE_TAC =
  let pat = `read (memory :> bytes8 (word_add tbl a)) s = x` in
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> can (term_match [`tbl:int64`] pat) (concl th));;

let T4_BODY_MEM_TAC s =
  let jtm j = if j = 0 then `jj:num` else
    mk_binop `(+):num->num->num` `jj:num` (mk_small_numeral j) in
  let step j =
    MP_TAC(ISPECL [`op:int64`; `ws:num list`; `ml:num`; `st:byte list`;
                   `r:num`; jtm j; jtm(j + 1);
                   mk_var("sym"^string_of_int j,`:num`); s] HUF_MEM_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] in
  step 0 THEN step 1 THEN step 2 THEN step 3;;

let t4_body_goal = mk_t4_goal [`jj:num`; `ofs:num`; `bc:num`] t4_body
  (mk_abs(`s:armstate`,list_mk_comb(t4_rinv,[`L - (jj + 4)`; `s:armstate`])));;

let T4_BODY = prove
 (t4_body_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--5) THEN T4_SYM_TAC 5 0 `bc:num` THEN HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (6--8) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (9--13) THEN T4_SYM_TAC 13 1 `nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (14--16) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (17--21) THEN T4_SYM_TAC 21 2 `nb1 + nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (22--24) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (25--29) THEN T4_SYM_TAC 29 3 `nb2 + nb1 + nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (30--32) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (33--36) THEN
  PUFF_FINAL_TAC THEN T4_BODY_MEM_TAC `s36:armstate` THEN
  MAP_EVERY EXISTS_TAC
   [`jj + 4`; `ofs:num`; `nb3 + nb2 + nb1 + nb0 + bc:num`] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC);;

(*** 0x6210: the main loop of stream 4, the reload and then the body or ***)
(*** the tail                                                            ***)

let T4_OPVAL_TAC =
  MAP_EVERY (fun k ->
    let th = SPECL [`op:int64`; k] VAL_WORD_ADD_NOWRAP in
    MP_TAC th THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`val(op:int64) + L < 2 EXP 64`; `jj <= L`] THEN
      ARITH_TAC;
      DISCH_TAC])
  [`jj:num`; `L - 3`];;

let T4_SLICE_TAC ofs' s =
  MP_TAC(SPECL [`src:int64`; `LENGTH(st:byte list)`;
                `num_of_bytelist(st:byte list)`; ofs'; s]
     READ_MEMORY_BYTES64_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC;;

let T4_RELOAD_WEAKEN_TAC =
  GEN_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN
  EXISTS_TAC `L - (jj + 4)` THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; POP_ASSUM MP_TAC THEN REWRITE_TAC[]];;

let T4_CONJ_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
    NO_TAC) ORELSE
   ZSTD_ARITH_TAC);;

(*** BIT_reloadDStream_internal at 0x1c20, for a stream not in its last 8  ***)
(*** bytes: the pointer bc DIV 8 bytes back and bc MOD 8 bits used         ***)

let BITR_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc [0x1c20,0x1c50];;

let bitr_goal =
 `!pc returnaddress (bd:int64) (c:int64) bc (ptr:int64) (w:int64) e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     bc < 2 EXP 32 /\
     nonoverlapping (bd,24) (word pc,32000) /\
     nonoverlapping (bd,24) (word_sub ptr (word (bc DIV 8)),8)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x1c20) /\ read X30 s = returnaddress /\
               read X0 s = bd /\
               read (memory :> bytes64 bd) s = c /\
               read (memory :> bytes32 (word_add bd (word 8))) s = word bc /\
               read (memory :> bytes64 (word_add bd (word 16))) s = ptr /\
               read (memory :> bytes64 (word_sub ptr (word (bc DIV 8)))) s =
               w /\
               read events s = e)
          (\s. read PC s = returnaddress /\ read X0 s = word 0 /\
               read (memory :> bytes64 bd) s = w /\
               read (memory :> bytes32 (word_add bd (word 8))) s =
               word (bc MOD 8) /\
               read (memory :> bytes64 (word_add bd (word 16))) s =
               word_sub ptr (word (bc DIV 8)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [bd,24; word_sub ptr (word (bc DIV 8)),8] [bd,24]))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(bd,24)])`;;

let BITR_DIV8 = prove
 (`!bc. bc < 2 EXP 32
        ==> word_zx (word_ushr (word_zx (word_zx (word bc:int32):int64):int32)
                               3):int64 = word (bc DIV 8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `bc DIV 8 < 4294967296 /\ bc < 4294967296`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `bc < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT;
               ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`;
               ARITH_RULE
                `x < 4294967296 ==> x DIV 8 < 18446744073709551616`]);;

let BITR_MOD8 = prove
 (`!bc. bc < 2 EXP 32
        ==> word_zx (word_and (word_zx (word_zx (word bc:int32):int64):int32)
                              (word 7)):int64 = word (bc MOD 8) /\
            word_zx (word_zx (word_and (word_zx (word_zx (word bc:int32):int64)
                                                :int32) (word 7)):int64)
                    :int32 = word (bc MOD 8)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `bc < 4294967296 /\ bc MOD 8 < 8` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `bc < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `7 = 2 EXP 3 - 1`; WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
               ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`;
               ARITH_RULE `x < 8 ==> x < 4294967296`;
               ARITH_RULE `x < 8 ==> x < 18446744073709551616`]);;

let BITR_CORRECT = prove
 (bitr_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BITR_EXEC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `bc:num` BITR_DIV8) (ASSUME `bc < 2 EXP 32`);
    MP (SPEC `bc:num` BITR_MOD8) (ASSUME `bc < 2 EXP 32`)]) THEN
  ARM_STEPS_TAC BITR_EXEC (7--12) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`bc:num`; `8`] MOD_LT_EQ) THEN ARITH_TAC);;

(*** The signed comparison of L - jj with 3 ***)

let T4_IVAL_SMALL = prove
 (`!x. x < 2 EXP 62 ==> ival(word x:int64) = &x`,
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_IWORD] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  INT_ARITH_TAC);;

let T4_SGT3 = prove
 (`!d. 3 < d /\ d < 2 EXP 62
       ==> (ival(word(d - 3):int64) < &0 <=> F) /\
           (ival(word d:int64) - &3 = ival(word(d - 3):int64) <=> T)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `d - 3 < 2 EXP 62` ASSUME_TAC THENL
   [UNDISCH_TAC `d < 2 EXP 62` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[T4_IVAL_SMALL; INT_OF_NUM_LT; LT; GSYM INT_OF_NUM_SUB;
               LT_IMP_LE] THEN
  UNDISCH_TAC `3 < d` THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  INT_ARITH_TAC);;

let T4_SGT3_TAC =
  W(fun (asl,w) ->
    let pat = `ival(word(d - 3):int64)` in
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let d = lhand(rand(rand t)) in
      TRY(MP_TAC(SPEC d T4_SGT3) THEN
          ANTS_TAC THENL
           [CONJ_TAC THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])) tms);;

let T4_LE3_TAC =
  CMP_FLAGS_TAC `word_sub (word x) (word y):int64` WORD_CMP_64_SFLAGS THEN
  T4_SGT3_TAC THEN
  PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN TRY DECIDE_IFS_TAC THEN
  ZSTD_SMALL_WORD_TAC;;

let T4_ENTRY_INIT_TAC =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs <= LENGTH(st:byte list)`] THEN
    ARITH_TAC;
    DISCH_TAC];;

(*** The call of BIT_reloadDStream_internal at state sn, with the pointer  ***)
(*** bc DIV 8 bytes back                                                   ***)

let T4_SUB_ADDR = prove
 (`!(p:int64) a k. k <= a ==> word_sub (word_add p (word a)) (word k) =
                             word_add p (word (a - k))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

(*** ofs + 8 <= LENGTH st from ofs <> 0, given by the fact t ***)

let T4_OFS8_TAC t =
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`) THEN
    MP_TAC(ASSUME t) THEN ARITH_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The tails of the four streams, by tactics generic in the registers, the   *)
(* offset of the BIT_DStream in the frame and the addresses of the code (the *)
(* body of the fourth being the one above).                                  *)
(* ------------------------------------------------------------------------- *)

(*** The tails of the four streams in the slow path, after the main loop:  ***)
(*** the definitions of the tail of stream 4 generic in the registers,     ***)
(*** the offset of BIT_DStream in the frame and the addresses of the code  ***)

type tailspec =
 {tk : int;                     (* the stream                          *)
  sofs : int;                   (* BIT_DStream at sp - 496 + sofs      *)
  fregs : term;                 (* the registers in the frame          *)
  op : term; oend : term;       (* output pointer and its end          *)
  start : term; ptr : term;     (* start of the stream and the pointer *)
  t_cont : term; t_bc : term; t_shift : term;    (* the last bytes     *)
  r_cont : term; r_bc : term; r_flag : term;     (* the reload         *)
  r_copy : term; r_shift : term; olim : term; lim : term;
  b_cont : term; b_bc : term; b_flag : bool;     (* the body           *)
  a_post : int; a_tinv : int; a_tail : int;      (* addresses          *)
  a_rinv : int; a_body : int; a_entry : int; a_ret : int;
  e_regs : term;                (* facts of the entry about registers  *)
  e_mems : term list};;         (* and the frame                       *)

new_type_abbrev("tailreg",`:(armstate,int64)component`);;

let tail_regv s = mk_var(s,`:(armstate,int64)component`)
and tail_numv s = mk_var(s,`:num`);;

let tail_inst spec tm =
  let num = mk_small_numeral in
  vsubst
   [spec.fregs,`r_regs:((armstate,int64)component)list`;
    spec.op,tail_regv "r_op"; spec.oend,tail_regv "r_oend";
    spec.start,tail_regv "r_start"; spec.ptr,tail_regv "r_ptr";
    spec.t_cont,tail_regv "r_tcont"; spec.t_bc,tail_regv "r_tbc";
    spec.t_shift,tail_regv "r_tshift"; spec.r_cont,tail_regv "r_rcont";
    spec.r_bc,tail_regv "r_rbc"; spec.r_flag,tail_regv "r_rflag";
    spec.r_copy,tail_regv "r_rcopy"; spec.r_shift,tail_regv "r_rshift";
    spec.olim,tail_regv "r_olim"; spec.lim,tail_regv "r_lim";
    spec.b_cont,tail_regv "r_bcont"; spec.b_bc,tail_regv "r_bbc";
    num spec.a_post,tail_numv "a_post"; num spec.a_tinv,tail_numv "a_tinv";
    num spec.a_tail,tail_numv "a_tail"; num spec.a_rinv,tail_numv "a_rinv";
    num spec.a_body,tail_numv "a_body";
    num spec.a_entry,tail_numv "a_entry";
    num spec.sofs,tail_numv "s_c"; num(spec.sofs + 8),tail_numv "s_b";
    num(spec.sofs + 16),tail_numv "s_p"] tm;;

let tail_spv v =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,
                  `word_sub stackpointer (word 496):int64`),
          mk_comb(`word:num->int64`,v));;

let tail_rr = t4_rr
and tail_wr =
 `[op,L; word_add (word_sub stackpointer (word 496)) (word s_c),24]
  :(int64#num)list`;;

let tail_frame =
 `MAYCHANGE (r_regs:((armstate,int64)component)list) ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op,L);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word s_c),24)]`;;

let mk_tail_goal spec extra pre post =
  let pre' = tail_inst spec pre and post' = tail_inst spec post
  and frame = tail_inst spec tail_frame in
  let tm = mk_imp(t4_hyps,
                  list_mk_icomb "ensures" [`arm`; pre'; post'; frame]) in
  let vs = t4_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_tail_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** The facts that hold all through ***)

let tail_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read SP s = word_sub stackpointer (word 496) /\
  read X5 s = tbl /\ read (r_oend:tailreg) s = word_add op (word L) /\
  read (r_start:tailreg) s = src /\ read X23 s = word tl /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl)`;;

let tail_cont_mem =
  subst [tail_spv `s_c:num`,`a:int64`; t4_win,`w:int64`]
   `read (memory :> bytes64 a) s = w`
and tail_bc_mem =
  subst [tail_spv `s_b:num`,`a:int64`]
   `read (memory :> bytes32 a) s = word bc`
and tail_ptr_mem =
  subst [tail_spv `s_p:num`,`a:int64`]
   `read (memory :> bytes64 a) s = word_add src (word ofs)`;;

(*** After the stream: bc in BIT_DStream, and the pointer at ofs unless    ***)
(*** some code needed more bits than were left (then bc > 64)              ***)

let tail_ptr = `read (r_ptr:tailreg) s = word_add src (word ofs)`;;

let tail_post = with_memsafe tail_rr tail_wr (mk_abs(`s:armstate`,
  list_mk_exists([`ofs:num`; `bc:num`],list_mk_conj
   [`read PC s = word(pc + a_post)`; tail_common; tail_bc_mem;
    `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
    mk_disj(mk_conj(t4_good `L:num`,tail_ptr),t4_bad `L:num`)])));;

(*** The good state of jj bytes for the loop for the last bytes ***)

let tail_tgood =
  list_mk_conj [t4_good `jj:num`; `ofs = 0 \/ bc + 12 * (L - jj) <= 52`;
                tail_ptr];;

(*** The loop for the last bytes, for the measure m = L - jj ***)

let tail_tinv = with_memsafe tail_rr tail_wr
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `bc:num`],list_mk_conj
   [`m = L - jj /\ jj < L`;
    `read PC s = word(pc + a_tinv)`; tail_common;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_tshift:tailreg) s = word(64 - tl) /\
     read (r_tbc:tailreg) s = word bc`;
    mk_eq(`read (r_tcont:tailreg) s`,t4_win);
    `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
    mk_disj(tail_tgood,t4_bad `jj:num`)])));;

(*** Before that loop, with the container and bc in memory, and the        ***)
(*** pointer unless the state is bad                                       ***)

let tail_tail = with_memsafe tail_rr tail_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + a_tail)`; tail_common;
  `read (r_op:tailreg) s = word_add op (word jj) /\ jj <= L`;
  tail_cont_mem; tail_bc_mem;
  `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
  mk_disj(tail_tgood,t4_bad `jj:num`)]));;

(*** The main loop: the reload, with the flag of the body (BIT_DStream in  ***)
(*** memory being up to date when it is 0), and the body of 4 bytes        ***)

let tail_loopregs =
 `read (r_op:tailreg) s = word_add op (word jj) /\
  read (r_ptr:tailreg) s = word_add src (word ofs) /\
  read (r_rshift:tailreg) s = word(64 - tl) /\
  read (r_olim:tailreg) s = word_add op (word (L - 3)) /\
  read (r_lim:tailreg) s = word_add src (word 8) /\ 3 < L /\ jj <= L`;;

let tail_rinv = with_memsafe tail_rr tail_wr
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + a_rinv)`; tail_common; tail_loopregs;
    mk_eq(`read (r_rcont:tailreg) s`,t4_win);
    `read (r_rbc:tailreg) s = word bc`;
    mk_disj(list_mk_conj
      [`read (r_rflag:tailreg) s = word 0 /\
        read (r_rcopy:tailreg) s = word_add src (word ofs)`;
       tail_cont_mem; tail_bc_mem],
      `read (r_rflag:tailreg) s = word 1`);
    `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
    t4_good `jj:num`])));;

let tail_body flag = with_memsafe tail_rr tail_wr
 (mk_abs(`s:armstate`,list_mk_conj
  [`read PC s = word(pc + a_body)`; tail_common; tail_loopregs;
   mk_eq(`read (r_bcont:tailreg) s`,t4_win);
   (if flag
    then `read (r_bbc:tailreg) s = word bc /\
          read (r_rflag:tailreg) s = word 1 /\
          jj + 4 <= L /\ bc <= 7`
    else `read (r_bbc:tailreg) s = word bc /\ jj + 4 <= L /\ bc <= 7`);
   `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
   t4_good `jj:num`]));;

(*** The entry, with BIT_DStream in memory, in a good or bad state ***)

let tail_entry spec = with_memsafe tail_rr tail_wr
 (mk_abs(`s:armstate`,list_mk_conj
  ([`read PC s = word(pc + a_entry)`; tail_common;
    mk_conj(`read (r_op:tailreg) s = word_add op (word jj)`,spec.e_regs)] @
   spec.e_mems @
   [tail_cont_mem; tail_bc_mem; tail_ptr_mem;
    `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
    mk_disj(t4_good `jj:num`,t4_bad `jj:num`)])));;

(*** The goals ***)

let tail_tloop_goal spec = mk_tail_goal spec [`ofs:num`]
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(tail_tinv,[`m:num`; `s:armstate`]))))
  tail_post;;

let tail_tail_goal spec =
  mk_tail_goal spec [`jj:num`; `ofs:num`; `bc:num`] tail_tail tail_post;;

let tail_body_goal spec =
  mk_tail_goal spec [`jj:num`; `ofs:num`; `bc:num`] (tail_body spec.b_flag)
  (mk_abs(`s:armstate`,
          list_mk_comb(tail_rinv,[`L - (jj + 4)`; `s:armstate`])));;

let tail_loop_goal spec = mk_tail_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(tail_rinv,[`m:num`; `s:armstate`]))))
  tail_post;;

let tail_entry_goal spec =
  mk_tail_goal spec [`jj:num`; `ofs:num`; `bc:num`] (tail_entry spec)
  tail_post;;

(*** The four tails ***)

let tail4 =
 {tk = 4; sofs = 344;
  fregs = `[PC; X0; X1; X2; X3; X4; X6; X12; X13; X14; X16; X17; X18; X30]`;
  op = `X12`; oend = `X9`; start = `X27`; ptr = `X3`;
  t_cont = `X6`; t_bc = `X1`; t_shift = `X4`;
  r_cont = `X2`; r_bc = `X0`; r_flag = `X18`; r_copy = `X1`;
  r_shift = `X4`; olim = `X13`; lim = `X14`;
  b_cont = `X2`; b_bc = `X0`; b_flag = true;
  a_post = 0x6294; a_tinv = 0x6268; a_tail = 0x6250;
  a_rinv = 0x6210; a_body = 0x6180; a_entry = 0x6134; a_ret = 0x66ac;
  e_regs = `read X18 s = word 0 /\ jj <= L`;
  e_mems =
   [subst [t4_spk 112,`a:int64`]
     `read (memory :> bytes64 a) s = word_sub (word_add op (word L)) (word 3)`;
    subst [t4_spk 136,`a:int64`]
     `read (memory :> bytes64 a) s = word_add src (word 8)`]};;

let tail1 =
 {tk = 1; sofs = 224;
  fregs = `[PC; X0; X1; X2; X3; X4; X17; X19; X21; X22; X24; X25; X30]`;
  op = `X19`; oend = `X7`; start = `X11`; ptr = `X21`;
  t_cont = `X3`; t_bc = `X1`; t_shift = `X2`;
  r_cont = `X1`; r_bc = `X0`; r_flag = `X3`; r_copy = `X17`;
  r_shift = `X4`; olim = `X22`; lim = `X16`;
  b_cont = `X1`; b_bc = `X0`; b_flag = true;
  a_post = 0x5e64; a_tinv = 0x5e38; a_tail = 0x5e20;
  a_rinv = 0x5ddc; a_body = 0x5d4c; a_entry = 0x5d00; a_ret = 0x669c;
  e_regs = `read X16 s = word_add src (word 8) /\ jj <= L`;
  e_mems = []};;

let tail2 =
 {tk = 2; sofs = 264;
  fregs = `[PC; X0; X1; X2; X3; X4; X7; X13; X16; X17; X19; X22; X24; X30]`;
  op = `X13`; oend = `X8`; start = `X10`; ptr = `X7`;
  t_cont = `X4`; t_bc = `X1`; t_shift = `X2`;
  r_cont = `X1`; r_bc = `X0`; r_flag = `X3`; r_copy = `X4`;
  r_shift = `X2`; olim = `X16`; lim = `X19`;
  b_cont = `X1`; b_bc = `X0`; b_flag = false;
  a_post = 0x5fcc; a_tinv = 0x5fa0; a_tail = 0x5f88;
  a_rinv = 0x5f44; a_body = 0x5eb4; a_entry = 0x5e64; a_ret = 0x66cc;
  e_regs = `jj <= L`;
  e_mems =
   [subst [t4_spk 104,`a:int64`]
     `read (memory :> bytes64 a) s = word_add src (word 8)`]};;

let tail3 =
 {tk = 3; sofs = 304;
  fregs = `[PC; X0; X1; X2; X3; X4; X8; X13; X14; X16; X17; X19; X22; X30]`;
  op = `X14`; oend = `X6`; start = `X15`; ptr = `X8`;
  t_cont = `X4`; t_bc = `X1`; t_shift = `X2`;
  r_cont = `X0`; r_bc = `X1`; r_flag = `X2`; r_copy = `X4`;
  r_shift = `X3`; olim = `X13`; lim = `X16`;
  b_cont = `X0`; b_bc = `X17`; b_flag = true;
  a_post = 0x6134; a_tinv = 0x6108; a_tail = 0x60f0;
  a_rinv = 0x60ac; a_body = 0x601c; a_entry = 0x5fcc; a_ret = 0x66bc;
  e_regs = `jj <= L`;
  e_mems =
   [subst [t4_spk 128,`a:int64`]
     `read (memory :> bytes64 a) s = word_add src (word 8)`]};;

(*** The proofs of the pieces of a tail, generic in the tail: the tactics  ***)
(*** of the tail of stream 4, with simulation up to the next cut point     ***)
(*** where the paths of the tails differ                                   ***)

(*** The disjunction of the good and the bad state: split, or the good     ***)
(*** state chosen in a goal                                                ***)

let is_state_disj t =
  is_disj t &&
  can (find_term (fun u -> is_const u && fst(dest_const u) = "huf_decode"))
      (lhand t);;

let TAIL_STATE_CASES_TAC =
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (is_state_disj o concl));;

let TAIL_CONJ_TAC =
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) -> if is_state_disj w then DISJ1_TAC else NO_TAC) THEN
      REPEAT CONJ_TAC) THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
    NO_TAC) ORELSE
   ZSTD_ARITH_TAC);;

let TAIL_TLOOP_TAC =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  PUFF_INIT_TAC "s0" THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (free_in `bc:num` o concl)) THENL
   [ASM_CASES_TAC `bc < 64` THENL
     [T4_LOOKUP_TAC THEN T4_STEP_TAC THENL
       [T4_GOOD_END_TAC; T4_GOOD_LOOP_TAC];
      ALL_TAC];
    ALL_TAC] THEN
  (T4_ANY_TAC THEN T4_STEP_TAC THENL [T4_BAD_END_TAC; T4_BAD_LOOP_TAC]);;

let TAIL_TAIL_PROOF_TAC tloop_th =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN TAIL_STATE_CASES_TAC THEN
  (ASM_CASES_TAC `jj:num = L` THENL
    [FIRST_X_ASSUM(SUBST_ALL_TAC o
       check (fun th -> concl th = `jj:num = L`)) THEN
     ZSTD_STEPS_TAC (1--2) THEN PUFF_FINAL_TAC THEN
     MAP_EVERY EXISTS_TAC [`ofs:num`; `bc:num`] THEN ASM_REWRITE_TAC[];
     ZSTD_STEPS_TAC (1--6) THEN T4_SHIFT_TAC THEN
     ZSTD_CONTINUE_TAC tloop_th [] THEN
     EXISTS_TAC `L - jj:num` THEN
     MAP_EVERY EXISTS_TAC [`jj:num`; `bc:num`] THEN
     MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ZSTD_ARITH_TAC]);;

let TAIL_BODY_TAC =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--5) THEN T4_SYM_TAC 5 0 `bc:num` THEN HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (6--8) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (9--13) THEN T4_SYM_TAC 13 1 `nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (14--16) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (17--21) THEN T4_SYM_TAC 21 2 `nb1 + nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (22--24) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (25--29) THEN T4_SYM_TAC 29 3 `nb2 + nb1 + nb0 + bc:num` THEN
  HUF_HIDE_SUB_TAC THEN
  ZSTD_STEPS_TAC (30--32) THEN T4_DROP_TABLE_TAC THEN
  ZSTD_STEPS_TAC (33--36) THEN
  PUFF_FINAL_TAC THEN T4_BODY_MEM_TAC `s36:armstate` THEN
  MAP_EVERY EXISTS_TAC
   [`jj + 4`; `ofs:num`; `nb3 + nb2 + nb1 + nb0 + bc:num`] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

(*** The current state ***)

let TAIL_SLICE_TAC ofs' = W(fun (asl,w) -> T4_SLICE_TAC ofs' (rand w));;

(*** The paths after the reload, to the body or to the tail ***)

let TAIL_RELOAD_PATHS_TAC spec body_th tail_th =
  let to_body ofs' bc' =
    ZSTD_SIM_UNTIL_TAC [spec.a_body] THEN
    ZSTD_CONTINUE_WITH_TAC T4_RELOAD_WEAKEN_TAC
     body_th [ofs',`ofs:num`; bc',`bc:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN T4_CONJ_TAC
  and to_tail ofs' bc' =
    ZSTD_SIM_UNTIL_TAC [spec.a_tail] THEN
    ZSTD_CONTINUE_WITH_TAC
     (GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC)
     tail_th [ofs',`ofs:num`; bc',`bc:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN TAIL_CONJ_TAC in
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    TAIL_SLICE_TAC `ofs - bc DIV 8` THEN
    ASM_CASES_TAC `jj + 4 <= L` THENL
     [to_body `ofs - bc DIV 8` `bc MOD 8`;
      to_tail `ofs - bc DIV 8` `bc MOD 8`];
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [to_tail `ofs:num` `bc:num`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [TAIL_SLICE_TAC `ofs - bc DIV 8` THEN
    ASM_CASES_TAC `jj + 4 <= L` THENL
     [to_body `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
      to_tail `ofs - bc DIV 8` `bc - 8 * bc DIV 8`];
    TAIL_SLICE_TAC `0` THEN to_tail `0` `bc - 8 * ofs`];;

let TAIL_LOOP_TAC spec body_th tail_th =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  T4_OPVAL_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
                     can (find_term ((=) spec.r_flag)) (concl th))) THEN
  TAIL_RELOAD_PATHS_TAC spec body_th tail_th;;

(*** The entry: the call of BIT_reloadDStream_internal at the current      ***)
(*** state, with the pointer bc DIV 8 bytes back                           ***)

let TAIL_CALL_TAC spec =
  let bd = t4_spk spec.sofs in
  let bdaddr = map (fun k ->
    WORD_RULE(subst [mk_small_numeral k,`k:num`;
                     mk_small_numeral spec.sofs,`b:num`;
                     mk_small_numeral(spec.sofs + k),`k':num`]
     `word_add (word_add (word_sub stackpointer (word 496)) (word b))
               (word k):int64 =
      word_add (word_sub stackpointer (word 496)) (word k')`)) [8; 16] in
  let ret = mk_comb(`word:num->int64`,
              mk_binop `(+):num->num->num` `pc:num`
                (mk_small_numeral spec.a_ret)) in
  TAIL_SLICE_TAC `ofs - bc DIV 8` THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (SPECL
   [`pc:num`; ret; bd; t4_win; `bc:num`; `word_add src (word ofs):int64`;
    subst [`ofs - bc DIV 8`,`ofs:num`] t4_win] BITR_CORRECT))) THEN
  REWRITE_TAC(MP (SPECL [`src:int64`; `ofs:num`; `bc DIV 8`] T4_SUB_ADDR)
                (ASSUME `bc DIV 8 <= ofs`) :: bdaddr) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let s = fst(dest_var(rand(rand w))) in
    let n = int_of_string(String.sub s 1 (String.length s - 1)) in
    ARM_BIGSTEP_TAC ZSTD_EXEC ("s"^string_of_int(n + 1))) THENL
   [T4_CONJ_TAC; EVENTS_UNABBREV_TAC];;

(*** At most 3 bytes left, after the comparison ***)

let TAIL_SHORT_TAC spec tail_th =
  let until = ZSTD_SIM_UNTIL_TAC [spec.a_tail] in
  let to_tail ofs' bc' =
    until THEN ZSTD_CONTINUE_TAC tail_th [ofs',`ofs:num`; bc',`bc:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN TAIL_CONJ_TAC in
  ASM_CASES_TAC `8 <= ofs` THENL
   [T4_OFS8_TAC `8 <= ofs` THEN
    SUBGOAL_THEN
     `bc DIV 8 <= ofs /\ (ofs - bc DIV 8) + 8 <= LENGTH(st:byte list)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_SIM_UNTIL_TAC [0x1c20] THEN TAIL_CALL_TAC spec THEN
    to_tail `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [to_tail `ofs:num` `bc:num`; ALL_TAC] THEN
  T4_OFS8_TAC `~(ofs = 0)` THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [TAIL_SLICE_TAC `ofs - bc DIV 8` THEN
    to_tail `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    TAIL_SLICE_TAC `0` THEN to_tail `0` `bc - 8 * ofs`];;

(*** More than 3 bytes left: the main loop of the tail ***)

let TAIL_OLIM_LEMMA = prove
 (`!(op:int64) L. 3 <= L
                  ==> word_sub (word_add op (word L)) (word 3) =
                      word_add op (word (L - 3))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC T4_SUB_ADDR THEN ASM_REWRITE_TAC[]);;

let TAIL_OLIM =
  SUBGOAL_THEN `3 <= L` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`op:int64`; `L:num`]
    TAIL_OLIM_LEMMA) (ASSUME `3 <= L`)]);;

let TAIL_LONG_TAC spec loop_th =
  TAIL_OLIM THEN
  ZSTD_STEPS_TAC (1--4) THEN T4_LE3_TAC THEN
  ZSTD_SIM_UNTIL_TAC [spec.a_rinv] THEN TAIL_OLIM THEN
  T4_SHIFT_TAC THEN ZSTD_CONTINUE_TAC loop_th [] THEN
  EXISTS_TAC `L - jj:num` THEN
  MAP_EVERY EXISTS_TAC [`jj:num`; `ofs:num`; `bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN T4_CONJ_TAC;;

(*** A bad state goes to the tail with a dummy pointer ***)

let TAIL_BAD_TAC spec tail_th =
  (fun tac -> ASM_CASES_TAC `L <= jj + 3` THENL [tac; TAIL_OLIM THEN tac])
  (ZSTD_STEPS_TAC (1--4) THEN T4_LE3_TAC THEN
   ZSTD_SIM_UNTIL_TAC [spec.a_tail] THEN
   ZSTD_CONTINUE_TAC tail_th [] THEN
   MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN
   REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ZSTD_ARITH_TAC);;

let TAIL_ENTRY_TAC spec tail_th loop_th =
  T4_ENTRY_INIT_TAC THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  TAIL_STATE_CASES_TAC THENL
   [ASM_CASES_TAC `L <= jj + 3` THENL
     [ZSTD_STEPS_TAC (1--4) THEN T4_LE3_TAC THEN TAIL_SHORT_TAC spec tail_th;
      TAIL_LONG_TAC spec loop_th];
    TAIL_BAD_TAC spec tail_th];;

(*** The tails of the four streams, by the generic tactics ***)

let TAIL4_BODY = prove(tail_body_goal tail4, ACCEPT_TAC T4_BODY);;
let TAIL4_TLOOP = prove(tail_tloop_goal tail4, TAIL_TLOOP_TAC);;
let TAIL4_TAIL = prove(tail_tail_goal tail4, TAIL_TAIL_PROOF_TAC TAIL4_TLOOP);;
let TAIL4_LOOP = prove(tail_loop_goal tail4,
                       TAIL_LOOP_TAC tail4 TAIL4_BODY TAIL4_TAIL);;
let TAIL4_ENTRY = prove(tail_entry_goal tail4,
                        TAIL_ENTRY_TAC tail4 TAIL4_TAIL TAIL4_LOOP);;

let TAIL1_BODY = prove(tail_body_goal tail1, TAIL_BODY_TAC);;
let TAIL1_TLOOP = prove(tail_tloop_goal tail1, TAIL_TLOOP_TAC);;
let TAIL1_TAIL = prove(tail_tail_goal tail1, TAIL_TAIL_PROOF_TAC TAIL1_TLOOP);;
let TAIL1_LOOP = prove(tail_loop_goal tail1,
                       TAIL_LOOP_TAC tail1 TAIL1_BODY TAIL1_TAIL);;
let TAIL1_ENTRY = prove(tail_entry_goal tail1,
                        TAIL_ENTRY_TAC tail1 TAIL1_TAIL TAIL1_LOOP);;

let TAIL2_BODY = prove(tail_body_goal tail2, TAIL_BODY_TAC);;
let TAIL2_TLOOP = prove(tail_tloop_goal tail2, TAIL_TLOOP_TAC);;
let TAIL2_TAIL = prove(tail_tail_goal tail2, TAIL_TAIL_PROOF_TAC TAIL2_TLOOP);;
let TAIL2_LOOP = prove(tail_loop_goal tail2,
                       TAIL_LOOP_TAC tail2 TAIL2_BODY TAIL2_TAIL);;
let TAIL2_ENTRY = prove(tail_entry_goal tail2,
                        TAIL_ENTRY_TAC tail2 TAIL2_TAIL TAIL2_LOOP);;

let TAIL3_BODY = prove(tail_body_goal tail3, TAIL_BODY_TAC);;
let TAIL3_TLOOP = prove(tail_tloop_goal tail3, TAIL_TLOOP_TAC);;
let TAIL3_TAIL = prove(tail_tail_goal tail3, TAIL_TAIL_PROOF_TAC TAIL3_TLOOP);;
let TAIL3_LOOP = prove(tail_loop_goal tail3,
                       TAIL_LOOP_TAC tail3 TAIL3_BODY TAIL3_TAIL);;
let TAIL3_ENTRY = prove(tail_entry_goal tail3,
                        TAIL_ENTRY_TAC tail3 TAIL3_TAIL TAIL3_LOOP);;

(* ------------------------------------------------------------------------- *)
(* The end checks at 0x6294.                                                 *)
(* ------------------------------------------------------------------------- *)

(*** The end of the slow path at 0x6294: success, with the result n, if    ***)
(*** each stream k has its pointer p_k at its start a_k and all 64 bits    ***)
(*** of its container used, and otherwise the error -20, both with the     ***)
(*** callee-saved registers x25-x28 restored, at 0x5444                    ***)

let endchk_goal =
 `!pc stackpointer (p1:int64) (a1:int64) b1 (p2:int64) (a2:int64) b2
   (p3:int64) (a3:int64) b3 (p4:int64) (a4:int64) b4 n
   (v25:int64) (v26:int64) (v27:int64) (v28:int64) e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     b1 < 2 EXP 32 /\ b2 < 2 EXP 32 /\ b3 < 2 EXP 32 /\ b4 < 2 EXP 32 /\
     nonoverlapping (word_sub stackpointer (word 496),496) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x6294) /\
               read SP s = word_sub stackpointer (word 496) /\
               read X21 s = p1 /\ read X11 s = a1 /\
               read X7 s = p2 /\ read X10 s = a2 /\
               read X8 s = p3 /\ read X15 s = a3 /\
               read X3 s = p4 /\ read X27 s = a4 /\ read X20 s = word n /\
               read (memory :> bytes32 (word_add
                 (word_sub stackpointer (word 496)) (word 232))) s = word b1 /\
               read (memory :> bytes32 (word_add
                 (word_sub stackpointer (word 496)) (word 272))) s = word b2 /\
               read (memory :> bytes32 (word_add
                 (word_sub stackpointer (word 496)) (word 312))) s = word b3 /\
               read (memory :> bytes32 (word_add
                 (word_sub stackpointer (word 496)) (word 352))) s = word b4 /\
               read (memory :> bytes64 (word_add
                 (word_sub stackpointer (word 496)) (word 64))) s = v25 /\
               read (memory :> bytes64 (word_add
                 (word_sub stackpointer (word 496)) (word 72))) s = v26 /\
               read (memory :> bytes64 (word_add
                 (word_sub stackpointer (word 496)) (word 80))) s = v27 /\
               read (memory :> bytes64 (word_add
                 (word_sub stackpointer (word 496)) (word 88))) s = v28 /\
               read events s = e)
          (\s. read PC s = word(pc + 0x5444) /\
               read X0 s =
               (if p1 = a1 /\ b1 = 64 /\ p2 = a2 /\ b2 = 64 /\
                   p3 = a3 /\ b3 = 64 /\ p4 = a4 /\ b4 = 64
                then word n else word 18446744073709551596) /\
               read X25 s = v25 /\ read X26 s = v26 /\
               read X27 s = v27 /\ read X28 s = v28 /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [word_sub stackpointer (word 496),496] []))
          (MAYCHANGE [PC; X0; X1; X2; X3; X25; X26; X27; X28] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])`;;

(*** A pointer comparison, with both orientations of the disequality ***)

let ENDCHK_PTR_CASES_TAC p a =
  let eq = mk_eq(p,a) in
  let veq = mk_eq(mk_comb(`val:int64->num`,a),mk_comb(`val:int64->num`,p)) in
  ASM_CASES_TAC eq THENL
   [ALL_TAC;
    SUBGOAL_THEN (mk_conj(mk_neg(mk_eq(a,p)),mk_neg veq)) STRIP_ASSUME_TAC
    THENL [REWRITE_TAC[VAL_EQ] THEN ASM_MESON_TAC[]; ALL_TAC]];;

let ENDCHK_FIN_TAC =
  ZSTD_SIM_UNTIL_TAC [0x5444] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let ENDCHK_CORRECT = prove
 (endchk_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  let split2 p a b k =
    ENDCHK_PTR_CASES_TAC p a THENL [ASM_CASES_TAC b THEN k; k] in
  split2 `p1:int64` `a1:int64` `b1 = 64`
   (split2 `p2:int64` `a2:int64` `b2 = 64`
     (ENDCHK_PTR_CASES_TAC `p3:int64` `a3:int64` THENL
       [ENDCHK_PTR_CASES_TAC `p4:int64` `a4:int64` THENL
         [ASM_CASES_TAC `b3 = 64` THEN ASM_CASES_TAC `b4 = 64` THEN
          ENDCHK_FIN_TAC;
          ENDCHK_FIN_TAC];
        ENDCHK_FIN_TAC])));;

(* ------------------------------------------------------------------------- *)
(* The main loop at 0x56fc: the body, four symbols of each stream, the       *)
(* reloads of the streams and the exits.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The main loop of the slow path: lookups with any number of bits       ***)
(*** used, the index being that of the specification when the bits are     ***)
(*** in the container, and the step of the decoding from it                ***)

(*** The shift of a container by bc < 64 bits as the simulator puts it ***)

let ML_JSHL_SMALL = prove
 (`!c bc. c < 2 EXP 64 /\ bc < 64
          ==> word_jshl (word c:int64) (word bc) = word (2 EXP bc * c)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_jshl; DIMINDEX_64; VAL_WORD; word_shl] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `bc < 64 ==> bc < 2 EXP 64`] THEN
  REWRITE_TAC[MULT_SYM]);;

(*** The index from the bits of a stream in the container, for bc < 64 ***)

let ML_INDEX_COND = prove
 (`!(st:byte list) ofs bc tl.
        bc < 64 /\ 1 <= tl /\ tl <= 12 /\ (tl + bc <= 64 \/ ofs = 0)
        ==> val(word_jushr
                 (word_jshl
                   (word ((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                          2 EXP 64):int64) (word bc))
                 (word (64 - tl))) =
            zstd_back st (8 * ofs + 64 - bc) tl`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIMP_TAC[ML_JSHL_SMALL; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ;
           ASSUME `bc < 64`] THEN
  SUBGOAL_THEN
   `!y:int64. word_jushr y (word (64 - tl)) = word_ushr y (64 - tl)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[word_jushr; VAL_WORD; DIMINDEX_64] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 64`;
                 ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 2 EXP 64`];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
  REWRITE_TAC[ISPECL [`2 EXP bc`;
    `(num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64`]
    MULT_SYM] THEN
  MATCH_MP_TAC ZSTD_WINDOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(*** One step of the decoding, from a good state (position 8 * ofs + 64    ***)
(*** - bc) or a bad one (ofs = 0 and bc > 64), with the index x of the     ***)
(*** lookup that of the specification when bc < 64: good with bc + nb      ***)
(*** <= 64 and the symbol appended, or bad                                 ***)

let ML_STEP = prove
 (`!ws ml (st:byte list) r jj ofs bc tl x sym nb.
        huf_complete ws ml /\ 1 <= ml /\ ml <= tl /\ tl <= 12 /\
        x < 2 EXP tl /\
        (bc < 64 /\ (tl + bc <= 64 \/ ofs = 0)
         ==> x = zstd_back st (8 * ofs + 64 - bc) tl) /\
        huf_symbol ws (x DIV 2 EXP (tl - ml)) = sym /\
        (ml + 1) - EL sym ws = nb /\
        (ofs = 0 \/ tl + bc <= 64) /\
        (SND(SND(huf_decode ws ml st r jj)) /\
         FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\
         bc <= 64 \/
         ~SND(SND(huf_decode ws ml st r jj)) /\ ofs = 0 /\ 64 < bc)
        ==> (SND(SND(huf_decode ws ml st r (jj + 1))) /\
             FST(SND(huf_decode ws ml st r (jj + 1))) =
             8 * ofs + 64 - (bc + nb) /\ bc + nb <= 64 /\
             FST(huf_decode ws ml st r (jj + 1)) =
             APPEND (FST(huf_decode ws ml st r jj)) [word sym]) \/
            (~SND(SND(huf_decode ws ml st r (jj + 1))) /\ ofs = 0 /\
             64 < bc + nb)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= nb /\ nb <= ml` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ws:num list`; `ml:num`; `x DIV 2 EXP (tl - ml)`]
      HUF_NBITS_BOUND) THEN
    ASM_SIMP_TAC[DIV_EXP_LT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HUF_DECODE_SUC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "huf_decode"))
        (concl th))) THENL
   [ALL_TAC;
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC) THEN
  ASM_CASES_TAC `bc < 64` THENL
   [SUBGOAL_THEN
     `zstd_back st (8 * ofs + 64 - bc) ml = x DIV 2 EXP (tl - ml)`
    (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `x = zstd_back st (8 * ofs + 64 - bc) tl` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC ZSTD_BACK_DIV THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `nb <= 8 * ofs + 64 - bc` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    DISJ2_TAC THEN
    SUBGOAL_THEN `bc = 64 /\ ofs = 0` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`ws:num list`; `ml:num`; `zstd_back st 0 ml`]
      HUF_NBITS_BOUND) THEN
    ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN ASM_ARITH_TAC]);;

(*** A good state was good at every earlier point ***)

let HUF_DECODE_OK_MONO = prove
 (`!ws ml (st:byte list) r k m.
        k <= m /\ SND(SND(huf_decode ws ml st r m))
        ==> SND(SND(huf_decode ws ml st r k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `m:num`)) THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; ADD1; HUF_DECODE_SUC] THEN ASM_MESON_TAC[]);;

(*** Four bytes stored after a list of bytes in memory ***)

let ML_MEM_SNOC = prove
 (`!(a:int64) (l:byte list) n b s.
        LENGTH l = n /\
        read (memory :> bytes(a,n)) s = num_of_bytelist l /\
        read (memory :> bytes8(word_add a (word n))) s = b
        ==> read (memory :> bytes(a,n + 1)) s = num_of_bytelist(APPEND l [b])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `n:num`)) THEN
  MATCH_MP_TAC READ_MEMORY_BYTELIST_SNOC THEN ASM_REWRITE_TAC[]);;

let ML_MEM4 = prove
 (`!(a:int64) (l:byte list) b0 b1 b2 b3 s.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        read (memory :> bytes8(word_add a (word(LENGTH l)))) s = b0 /\
        read (memory :> bytes8(word_add a (word(LENGTH l + 1)))) s = b1 /\
        read (memory :> bytes8(word_add a (word(LENGTH l + 2)))) s = b2 /\
        read (memory :> bytes8(word_add a (word(LENGTH l + 3)))) s = b3
        ==> read (memory :> bytes(a,LENGTH l + 4)) s =
            num_of_bytelist(APPEND l [b0; b1; b2; b3])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `APPEND (l:byte list) [b0; b1; b2; b3] =
                APPEND (APPEND (APPEND (APPEND l [b0]) [b1]) [b2]) [b3]`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n + 4 = (((n + 1) + 1) + 1) + 1`] THEN
  MATCH_MP_TAC ML_MEM_SNOC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    MATCH_MP_TAC ML_MEM_SNOC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      MATCH_MP_TAC ML_MEM_SNOC THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
        MATCH_MP_TAC ML_MEM_SNOC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`]];
    ASM_REWRITE_TAC[ARITH_RULE `((n + 1) + 1) + 1 = n + 3`]]);;

(*** The body of the main loop at 0x56fc, to 0x590c: 4 symbols from each   ***)
(*** of the 4 streams, interleaved. Stream k at state jj of its decoding   ***)
(*** has its container from ofs and bc bits used, in a good state with     ***)
(*** ofs = 0 or bc <= 8 (so that the bits of all lookups are in the        ***)
(*** container unless the stream is at its start); after the body each     ***)
(*** stream is in a good state or a bad one                                ***)

type mlstream =
 {mk : int; mcont : term; mbcin : term; mbcout : term; mop : term};;

let ml_streams =
 [{mk = 1; mcont = `X22`; mbcin = `X26`; mbcout = `X26`; mop = `X19`};
  {mk = 2; mcont = `X21`; mbcin = `X2`; mbcout = `X2`; mop = `X13`};
  {mk = 3; mcont = `X30`; mbcin = `X17`; mbcout = `X17`; mop = `X14`};
  {mk = 4; mcont = `X18`; mbcin = `X0`; mbcout = `X4`; mop = `X12`}];;

let ml_names =
  ["st",`:byte list`; "src",`:int64`; "op",`:int64`; "L",`:num`;
   "r",`:num`; "ofs",`:num`; "bc",`:num`];;

let ml_var k (s,ty) = mk_var(s ^ string_of_int k,ty);;

let ml_inst m tm =
  vsubst ([m.mcont,tail_regv "r_cont"; m.mbcin,tail_regv "r_bcin";
           m.mbcout,tail_regv "r_bcout"; m.mop,tail_regv "r_op"] @
          map (fun (s,ty) -> ml_var m.mk (s,ty),mk_var(s,ty)) ml_names) tm;;

let ml_vars k = map (ml_var k) ml_names;;

(*** One stream before and after the body ***)

let ml_body_pre1 =
 `read (r_cont:tailreg) s =
  word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read (r_bcin:tailreg) s = word bc /\
  read (r_op:tailreg) s = word_add op (word j) /\
  read (memory :> bytes(op,j)) s =
  num_of_bytelist(FST(huf_decode ws ml st r j)) /\
  SND(SND(huf_decode ws ml st r j)) /\
  FST(SND(huf_decode ws ml st r j)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
  (ofs = 0 \/ bc <= 8) /\ j + 4 <= L`;;

let ml_body_post1 =
 `?bc' out'.
    read (r_cont:tailreg) s =
    word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
    read (r_bcout:tailreg) s = word bc' /\
    read (r_op:tailreg) s = word_add op (word (j + 4)) /\
    read (memory :> bytes(op,j + 4)) s = num_of_bytelist out' /\
    LENGTH(out':byte list) = j + 4 /\
    (SND(SND(huf_decode ws ml st r (j + 4))) /\
     FST(SND(huf_decode ws ml st r (j + 4))) = 8 * ofs + 64 - bc' /\
     bc' <= 64 /\ out' = FST(huf_decode ws ml st r (j + 4)) \/
     ~SND(SND(huf_decode ws ml st r (j + 4))) /\ ofs = 0 /\
     64 < bc' /\ bc' <= 64 + 12 * (j + 4))`;;

let ml_hyps_out =
  let one k = ml_inst (el (k - 1) ml_streams)
   `L < 2 EXP 28 /\ val(op:int64) + L < 2 EXP 64 /\
    nonoverlapping (op,L) (tbl:int64,2 * 2 EXP tl) /\
    nonoverlapping (op,L) (word pc,32000)` in
  let pair i k =
    subst [ml_var i ("op",`:int64`),`a:int64`; ml_var i ("L",`:num`),`m:num`;
           ml_var k ("op",`:int64`),`b:int64`; ml_var k ("L",`:num`),`n:num`]
     `nonoverlapping (a:int64,m) (b,n)` in
  map one [1;2;3;4] @
  [pair 1 2; pair 1 3; pair 1 4; pair 2 3; pair 2 4; pair 3 4];;

let ml_body_hyps = list_mk_conj
 ([`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ tl <= 12`] @ ml_hyps_out);;

let ml_rr = `[tbl,2 * 2 EXP tl]:(int64#num)list`
and ml_wr = `[op1,L1; op2,L2; op3,L3; op4,L4]:(int64#num)list`;;

let ml_body_frame =
 `MAYCHANGE [PC; X0; X2; X4; X6; X7; X8; X9; X12; X13; X14; X17; X19;
             X26; X28] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op1,L1); memory :> bytes(op2,L2);
             memory :> bytes(op3,L3); memory :> bytes(op4,L4)]`;;

let ml_body_pre = with_memsafe ml_rr ml_wr (mk_abs(`s:armstate`,
  list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x56fc) /\
      read X5 s = tbl /\ read X3 s = word(64 - tl) /\
      read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable ws ml tl)`] @
    map (fun m -> ml_inst m ml_body_pre1) ml_streams)));;

let ml_body_post = with_memsafe ml_rr ml_wr (mk_abs(`s:armstate`,
  list_mk_conj
   (`read PC s = word(pc + 0x590c)` ::
    map (fun m -> ml_inst m ml_body_post1) ml_streams)));;

let ml_body_vars =
  [`pc:num`; `tbl:int64`; `tl:num`; `ws:num list`; `ml:num`; `j:num`;
   `e:uarch_event list`] @ List.concat (map ml_vars [1;2;3;4]);;

let ml_body_goal =
  let tm = mk_imp(ml_body_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; ml_body_pre; ml_body_post; ml_body_frame]) in
  let fvs = frees tm in
  (match subtract fvs ml_body_vars with
     [] -> ()
   | v::_ -> failwith ("ml_body_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) ml_body_vars,tm);;

(*** The simulation of the body: after each step, each new index of a      ***)
(*** lookup is abbreviated (x_k), with the entry of the table for it, its  ***)
(*** symbol (sym_k) and number of bits (nb_k), and the fact that it is     ***)
(*** the index of the specification when the bits are in the container;    ***)
(*** the entries of the table are dropped once both bytes are loaded       ***)

let ML_INDEX_COND' = prove
 (`!(st:byte list) ofs bc tl.
        1 <= tl /\ tl <= 12
        ==> bc < 64 /\ (tl + bc <= 64 \/ ofs = 0)
            ==> val(word_jushr
                     (word_jshl
                       (word ((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                              2 EXP 64):int64) (word bc))
                     (word (64 - tl))) =
                zstd_back st (8 * ofs + 64 - bc) tl`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ML_INDEX_COND THEN ASM_REWRITE_TAC[]);;

let ml_counter = ref 0;;

(*** The lookups: the container variable, the bits used, x, sym and nb ***)

let ml_lookups = ref ([]:(term * term * term * term * term) list);;

let ml_index_pat =
  `word_shl (word_jushr (word_jshl (word c) (word b):int64)
                        (word (64 - tl))) 1`;;

let ml_window_pat =
  `(num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64`;;

let ML_INDEX_ONE_TAC (t:term) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let _,tmi,_ = term_match [] ml_index_pat t in
    let inst v = try rev_assoc v tmi with Failure _ -> v in
    let c = inst `c:num` and b = inst `b:num` in
    let wth = snd(find (fun (_,th) -> let u = concl th in
                          is_eq u && rhs u = c &&
                          can (term_match [] ml_window_pat) (lhs u)) asl) in
    let _,wmi,_ = term_match [] ml_window_pat (lhs(concl wth)) in
    let winst v = try rev_assoc v wmi with Failure _ -> v in
    let st = winst `st:byte list` and ofs = winst `ofs:num` in
    incr ml_counter;
    let k = string_of_int !ml_counter in
    let x = mk_var("x"^k,`:num`) and sym = mk_var("sym"^k,`:num`)
    and nb = mk_var("nb"^k,`:num`) in
    let y = subst [c,`c:num`; b,`b:num`] `word_jshl (word c) (word b):int64` in
    let xdef = mk_comb(`val:int64->num`,
                 list_mk_icomb "word_jushr" [y; `word (64 - tl):int64`]) in
    let ttth = snd(find (fun (_,th) -> concl th = `2 EXP tl = tt`) asl) in
    ml_lookups := !ml_lookups @ [c,b,x,sym,nb];
    (MP_TAC(ISPECL [y; `tl:num`] HUF_INDEX_ANY) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
                (fun th -> ASSUME_TAC th THEN
                           ASSUME_TAC(REWRITE_RULE[ttth] th))) THEN
     W(fun (asl,w) ->
       let tl1 = snd(find (fun (_,th) -> concl th = `1 <= tl`) asl)
       and tl2 = snd(find (fun (_,th) -> concl th = `tl <= 12`) asl) in
       ASSUME_TAC(REWRITE_RULE[wth]
         (MP (SPECL [st; ofs; b; `tl:num`] ML_INDEX_COND')
             (CONJ tl1 tl2)))) THEN
     ABBREV_TAC (mk_eq(x,xdef)) THEN
     MP_TAC(REWRITE_RULE[ttth]
       (ISPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; x; s]
         HUF_DTABLE_READ)) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
     MP_TAC(SPECL [x; `tl:num`; `ml:num`] DIV_EXP_LT) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     let xd = mk_binop `(DIV):num->num->num` x `2 EXP (tl - ml)` in
     MP_TAC(ISPECL [`ws:num list`; `ml:num`; xd] HUF_NBITS_BOUND) THEN
     MP_TAC(ISPECL [`ws:num list`; `ml:num`; xd] HUF_SYMBOL_BOUND) THEN
     ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
     ABBREV_TAC (mk_eq(sym,subst [x,`x:num`]
                   `huf_symbol ws (x DIV 2 EXP (tl - ml))`)) THEN
     ABBREV_TAC (mk_eq(nb,subst [sym,`sym:num`] `(ml + 1) - EL sym ws`))) gl;;

let ML_INDEX_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let tms = setify(List.concat(mapfilter (fun (_,th) ->
      let t = concl th in
      if is_eq t && is_comb(lhs t) && rand(lhs t) = s
      then find_terms (can (term_match [] ml_index_pat)) (rhs t)
      else fail()) asl)) in
    MAP_EVERY ML_INDEX_ONE_TAC tms gl;;

(*** The entries of the table whose index is in no register any more ***)

let ML_DROP_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let regvals = mapfilter (fun (_,th) ->
      let t = concl th in
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
          when s' = s && not(can (find_term ((=) `memory`)) c) &&
               not(c = `events`) -> v
      | _ -> fail()) asl in
    let live = itlist (union o frees) regvals [] in
    let xs = map (fun (_,_,x,_,_) -> x) !ml_lookups in
    let dead = filter (fun x -> not(mem x live)) xs in
    let pat = `read (memory :> bytes8 (word_add tbl a)) s = v` in
    DISCARD_ASSUMPTIONS_TAC (fun th ->
      let t = concl th in
      can (term_match [`tbl:int64`] pat) t &&
      exists (fun x -> free_in x t) dead) gl;;

let ML_NORM_TAC = ML_INDEX_TAC THEN ML_DROP_TAC THEN HUF_HIDE_SUB_TAC;;

let ML_STEPS_TAC ns =
  MAP_EVERY (fun n -> ZSTD_STEP_TAC n THEN ML_NORM_TAC) ns;;

(*** The end of the body: for each stream, the 4 steps of its decoding     ***)
(*** from its lookups (ML_STEP), and the good or the bad state after them  ***)

(*** A fact among the conjuncts of the assumptions ***)

let ML_FACT_TAC : tactic =
  fun (asl,w as gl) ->
    let ths = itlist (fun (_,th) acc -> CONJUNCTS th @ acc) asl [] in
    match filter (fun th -> aconv (concl th) w) ths with
      th::_ -> ACCEPT_TAC th gl
    | [] -> failwith "ML_FACT_TAC";;

(*** Arithmetic from the facts (also in conjunctions) about the variables  ***)
(*** of the goal and ml, tl                                                ***)

let ML_ARITH_TAC : tactic =
  fun (asl,w as gl) ->
    let vs = union [`ml:num`; `tl:num`] (frees w) in
    let numty = `:num` in
    let ok t =
      exists (fun op -> is_binary op t && type_of(lhand t) = numty)
             ["="; "<"; "<="] &&
      not(exists (fun v -> type_of v = `:armstate`) (frees t)) &&
      subset (frees t) vs in
    let facts = filter (ok o concl)
      (itlist (fun (_,th) acc -> CONJUNCTS th @ acc) asl []) in
    (MAP_EVERY MP_TAC facts THEN ARITH_TAC) gl;;

let ml_svar k s ty = ml_var k (s,ty);;

(*** The bits of the lookups of stream k stay in its container unless the  ***)
(*** stream is at its start                                                ***)

let ML_OFS_TAC k : tactic =
  let ofs = ml_svar k "ofs" `:num` and bc = ml_svar k "bc" `:num` in
  let d = mk_disj(mk_eq(ofs,`0`),mk_binop `(<=):num->num->bool` bc `8`) in
  FIRST_ASSUM(fun th -> if concl th = d then DISJ_CASES_TAC th else NO_TAC)
  THENL [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
         DISJ2_TAC THEN ML_ARITH_TAC];;

(*** The state disjunction for stream k at jj with bc ***)

let ML_WEAKEN = TAUT
 `!a b c d e. (a /\ b /\ c /\ d) \/ e ==> (a /\ b /\ c) \/ e`;;

let ml_jjs = [`j:num`; `j + 1`; `j + 2`; `j + 3`; `j + 4`];;

(*** Step i of the decoding of stream k from its lookup: the conclusion    ***)
(*** of ML_STEP as an assumption, at j + i + 1 with the bits nb + b of     ***)
(*** the next lookup, and its weaker form, the state for the next step     ***)

let ML_ONE_STEP_TAC k i : tactic =
  fun (asl,w as gl) ->
    let ck = mk_var("c"^string_of_int k,`:num`) in
    let lks = filter (fun (c,_,_,_,_) -> c = ck) !ml_lookups in
    let (_,b,x,sym,nb) = el i lks in
    let st = ml_svar k "st" `:byte list` and r = ml_svar k "r" `:num`
    and ofs = ml_svar k "ofs" `:num` in
    let jj = el i ml_jjs and jj' = el (i + 1) ml_jjs in
    let ttths = map snd (filter (fun (_,th) -> concl th = `2 EXP tl = tt`)
                                asl) in
    let th = REWRITE_RULE ttths
              (SPECL [`ws:num list`; `ml:num`; st; r; jj; ofs; b; `tl:num`;
                      x; sym; nb] ML_STEP) in
    let jj1 = mk_binop `(+):num->num->num` jj `1` in
    let eq1 = if jj1 = jj' then [] else [ARITH_RULE(mk_eq(jj1,jj'))]
    and eq2 = SPECL [b; nb] ADD_SYM in
    (MP_TAC th THEN ANTS_TAC THENL
      [REPEAT CONJ_TAC THEN
       FIRST [ML_FACT_TAC; ML_OFS_TAC k;
              DISJ1_TAC THEN REPEAT CONJ_TAC THEN ML_FACT_TAC];
       REWRITE_TAC eq1 THEN SUBST1_TAC eq2 THEN
       DISCH_THEN(fun th -> ASSUME_TAC th THEN
                            ASSUME_TAC(MATCH_MP ML_WEAKEN th))]) gl;;

(*** A register with its value up to the normal form of addresses ***)

let ML_REG_TAC : tactic =
  W(fun (asl,w) ->
    let l = lhs w in
    let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l)
                      asl) in
    GEN_REWRITE_TAC LAND_CONV [th] THEN CONV_TAC WORD_RULE);;

(*** The good state of stream k after the 4 steps, with the bytes stored   ***)
(*** (each earlier state being good too), or the bad one                   ***)

let ml_okt k jj =
  let st = ml_svar k "st" `:byte list` and r = ml_svar k "r" `:num` in
  mk_icomb(`SND:num#bool->bool`,
    mk_icomb(`SND:byte list#num#bool->num#bool`,
      list_mk_icomb "huf_decode" [`ws:num list`; `ml:num`; st; r; jj]));;

let ml_is_full k jj th =
  let t = concl th in
  is_disj t && length(conjuncts(lhand t)) = 4 &&
  hd(conjuncts(lhand t)) = ml_okt k jj;;

let ML_DISJ_TAC k : tactic =
  fun (asl,w as gl) ->
    let st = ml_svar k "st" `:byte list` and r = ml_svar k "r" `:num` in
    let left i =
      let jji = el i ml_jjs in
      let okt = ml_okt k jji in
      MP_TAC(ISPECL [`ws:num list`; `ml:num`; st; r; jji; `j + 4`]
               HUF_DECODE_OK_MONO) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC; ML_FACT_TAC]; DISCH_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
        check (ml_is_full k jji)) THENL
       [ALL_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = mk_neg okt then MP_TAC th
                                else NO_TAC) THEN
        FIRST_ASSUM(fun th -> if concl th = okt then REWRITE_TAC[th]
                              else NO_TAC)] in
    let fsts = W(fun (asl,w) ->
      let is_fst t =
        is_eq t && is_comb(lhs t) &&
        (match lhs t with
           Comb(Const("FST",_),d) ->
             (try let f,args = strip_comb d in
                  fst(dest_const f) = "huf_decode" && el 2 args = st
              with Failure _ -> false)
         | _ -> false) &&
        can (term_match [] `APPEND (l:byte list) [b]`) (rhs t) in
      let ths = map snd (filter (fun (_,th) -> is_fst(concl th)) asl) in
      REWRITE_TAC ths THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]) in
    (FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
       check (ml_is_full k `j + 4`)) THENL
      [DISJ1_TAC THEN left 1 THEN left 2 THEN left 3 THEN
       REPEAT CONJ_TAC THEN FIRST [ML_FACT_TAC; CONV_TAC SYM_CONV THEN fsts];
       DISJ2_TAC THEN REPEAT CONJ_TAC THEN FIRST [ML_FACT_TAC; ML_ARITH_TAC]])
    gl;;

(*** The bytes stored, after those of the state at j ***)

let ML_MEM_TAC k : tactic =
  fun (asl,w as gl) ->
    let ck = mk_var("c"^string_of_int k,`:num`) in
    let lks = filter (fun (c,_,_,_,_) -> c = ck) !ml_lookups in
    let st = ml_svar k "st" `:byte list` and r = ml_svar k "r" `:num`
    and op = ml_svar k "op" `:int64` in
    let s = find_term (fun t -> type_of t = `:armstate` && is_var t) w in
    let fstj = mk_icomb(`FST:byte list#num#bool->byte list`,
                 list_mk_icomb "huf_decode"
                   [`ws:num list`; `ml:num`; st; r; `j:num`]) in
    let bs = map (fun (_,_,_,sym,_) -> mk_comb(`word:num->byte`,sym)) lks in
    (MP_TAC(ISPECL ([op; fstj] @ bs @ [s]) ML_MEM4) THEN
     REWRITE_TAC[HUF_DECODE_LENGTH] THEN
     ANTS_TAC THENL [REPEAT CONJ_TAC THEN ML_FACT_TAC; REWRITE_TAC[]]) gl;;

(*** The post of stream k ***)

let ML_STREAM_TAC k : tactic =
  fun (asl,w as gl) ->
    let ck = mk_var("c"^string_of_int k,`:num`) in
    let lks = filter (fun (c,_,_,_,_) -> c = ck) !ml_lookups in
    let (_,b3,_,_,nb3) = el 3 lks in
    let st = ml_svar k "st" `:byte list` and r = ml_svar k "r" `:num` in
    let fstj = mk_icomb(`FST:byte list#num#bool->byte list`,
                 list_mk_icomb "huf_decode"
                   [`ws:num list`; `ml:num`; st; r; `j:num`]) in
    let bs = map (fun (_,_,_,sym,_) -> mk_comb(`word:num->byte`,sym)) lks in
    let outv = list_mk_icomb "APPEND" [fstj; mk_list(bs,`:byte`)] in
    (EXISTS_TAC (mk_binop `(+):num->num->num` nb3 b3) THEN
     EXISTS_TAC outv THEN
     ML_ONE_STEP_TAC k 0 THEN ML_ONE_STEP_TAC k 1 THEN
     ML_ONE_STEP_TAC k 2 THEN ML_ONE_STEP_TAC k 3 THEN
     REPEAT CONJ_TAC THENL
      [ML_FACT_TAC; ML_FACT_TAC; ML_REG_TAC; ML_MEM_TAC k;
       REWRITE_TAC[LENGTH_APPEND; HUF_DECODE_LENGTH; LENGTH] THEN ARITH_TAC;
       ML_DISJ_TAC k]) gl;;

(*** The postcondition abbreviated during the simulation, and back ***)

let ML_ABBREV_POST_TAC : tactic =
  fun (asl,w as gl) ->
    let p = rand(rator w) in
    ABBREV_TAC (mk_eq(mk_var("ml_post",type_of p),p)) gl;;

let ML_EXPAND_POST_TAC =
  FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_eq t && is_var(rhs t) && fst(dest_var(rhs t)) = "ml_post"
    then SUBST1_TAC(SYM th) else NO_TAC) THEN BETA_TAC;;

(*** The body ***)

let ML_BODY = prove
 (ml_body_goal,
  (fun gl -> ml_counter := 0; ml_lookups := []; ALL_TAC gl) THEN
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `1 <= tl` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `ml:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun k ->
    let st = ml_svar k "st" `:byte list` and ofs = ml_svar k "ofs" `:num` in
    ABBREV_TAC (mk_eq(mk_var("c"^string_of_int k,`:num`),
      subst [st,`st:byte list`; ofs,`ofs:num`]
       `(num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64`)))
   [1;2;3;4] THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN ML_ABBREV_POST_TAC THEN
  ML_STEPS_TAC (1--132) THEN ML_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  REPEAT CONJ_TAC THENL
   [ML_FACT_TAC; ML_STREAM_TAC 1; ML_STREAM_TAC 2; ML_STREAM_TAC 3;
    ML_STREAM_TAC 4]);;

(*** The main loop: the states at the body (0x56fc), after the body      ***)
(*** (0x590c) and at the exit to the order check (0x5ce4)                ***)

type mlreg =
 {rk : int; rcont : term; rbcin : term; rbcout : term; rptr : term;
  rop : term; rlim : term; rsofs : int; rflag : term -> term};;

let ml_spk k = t4_spk k;;

let ml_mem32 k v =
  subst [ml_spk k,`a:int64`; v,`v:num`]
   `read (memory :> bytes32 a) s = word v`;;

let ml_regs =
 [{rk = 1; rcont = `X22`; rbcin = `X26`; rbcout = `X26`; rptr = `X23`;
   rop = `X19`; rlim = `X16`; rsofs = 224;
   rflag = fun v -> subst [v,`v:num`] `read X1 s = word v`};
  {rk = 2; rcont = `X21`; rbcin = `X2`; rbcout = `X2`; rptr = `X24`;
   rop = `X13`; rlim = `X20`; rsofs = 264; rflag = ml_mem32 184};
  {rk = 3; rcont = `X30`; rbcin = `X17`; rbcout = `X17`; rptr = `X25`;
   rop = `X14`; rlim = `X27`; rsofs = 304; rflag = ml_mem32 124};
  {rk = 4; rcont = `X18`; rbcin = `X0`; rbcout = `X4`; rptr = `X11`;
   rop = `X12`; rlim = `X10`; rsofs = 344;
   rflag = fun v -> subst [v,`v:num`] `read X15 s = word v`}];;

let ml_win =
 `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64)
  :int64`;;

let ml_struct =
  [subst [tail_spv `s_c:num`,`a:int64`; ml_win,`w:int64`]
    `read (memory :> bytes64 a) s = w`;
   subst [tail_spv `s_p:num`,`a:int64`]
    `read (memory :> bytes64 a) s = word_add src (word ofs)`];;

(*** One stream at the body ***)

let ml_inv1 = list_mk_conj
 ([mk_eq(`read (r_cont:tailreg) s`,ml_win);
   `read (r_bcin:tailreg) s = word bc /\
    read (r_ptr:tailreg) s = word_add src (word ofs) /\
    read (r_op:tailreg) s = word_add op (word j) /\
    read (r_lim:tailreg) s = word_add src (word 8) /\
    read (memory :> bytes(src,LENGTH(st:byte list))) s =
    num_of_bytelist st /\
    read (memory :> bytes(op,j)) s =
    num_of_bytelist(FST(huf_decode ws ml st r j)) /\
    SND(SND(huf_decode ws ml st r j)) /\
    FST(SND(huf_decode ws ml st r j)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
    (ofs = 0 \/ bc <= 8) /\ (ofs = 0 \/ ofs + 8 <= LENGTH st) /\
    j + 4 <= L`]);;

(*** One stream at the exit: BIT_DStream in memory ***)

let ml_rinst m tm =
  vsubst ([m.rcont,tail_regv "r_cont"; m.rbcin,tail_regv "r_bcin";
           m.rbcout,tail_regv "r_bcout"; m.rptr,tail_regv "r_ptr";
           m.rop,tail_regv "r_op"; m.rlim,tail_regv "r_lim";
           mk_small_numeral m.rsofs,tail_numv "s_c";
           mk_small_numeral(m.rsofs + 8),tail_numv "s_b";
           mk_small_numeral(m.rsofs + 16),tail_numv "s_p"] @
          map (fun (s,ty) -> ml_var m.rk (s,ty),mk_var(s,ty))
              (ml_names @ ["out",`:byte list`])) tm;;

(*** The slots of the frame of the loop, and the flags ***)

let ml_sv k = ml_var k ("src",`:int64`)
and ml_ov k = ml_var k ("op",`:int64`)
and ml_Lv k = ml_var k ("L",`:num`);;

let ml_mem64 k v =
  subst [ml_spk k,`a:int64`; v,`v:int64`]
   `read (memory :> bytes64 a) s = v`;;

let ml_slots =
  let add8 k = mk_comb(mk_comb(`word_add:int64->int64->int64`,ml_sv k),
                       `word 8:int64`)
  and oend = mk_comb(mk_comb(`word_add:int64->int64->int64`,ml_ov 4),
                     mk_comb(`word:num->int64`,ml_Lv 4)) in
  [ml_mem64 104 (add8 2);
   ml_mem64 112 (mk_comb(mk_comb(`word_sub:int64->int64->int64`,oend),
                         `word 3:int64`));
   ml_mem64 128 (add8 3); ml_mem64 136 (add8 4);
   ml_mem64 144 oend; ml_mem64 152 (ml_sv 1);
   ml_mem64 160 (ml_ov 2); ml_mem64 168 (ml_ov 3); ml_mem64 176 (ml_ov 4);
   ml_mem32 188 `tl:num`; ml_mem64 192 `word n:int64`;
   ml_mem64 200 (ml_sv 2); ml_mem64 208 (ml_sv 3); ml_mem64 216 (ml_sv 4)];;

(*** The hypotheses of the pieces of the loop ***)

let ml_hyps =
  let st k = ml_var k ("st",`:byte list`) in
  let ins k = mk_pair(ml_sv k,mk_comb(`LENGTH:byte list->num`,st k))
  and outs k = mk_pair(ml_ov k,ml_Lv k) in
  let tbl = `tbl:int64,2 * 2 EXP tl`
  and code = `word pc:int64,32000`
  and stk = `word_sub stackpointer (word 496):int64,496` in
  let nonov a b = list_mk_icomb "nonoverlapping" [a; b] in
  let one k = ml_rinst (el (k - 1) ml_regs)
   `L < 2 EXP 28 /\ val(op:int64) + L < 2 EXP 64 /\
    8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64` in
  [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ tl <= 12`;
   `L4 <= L1 /\ L4 <= L2 /\ L4 <= L3`] @
  map one [1;2;3;4] @
  List.concat (map (fun k ->
    [nonov (outs k) tbl; nonov (outs k) code; nonov (outs k) stk] @
    map (fun i -> nonov (outs k) (ins i)) [1;2;3;4]) [1;2;3;4]) @
  map (fun (i,k) -> nonov (outs i) (outs k))
      [1,2; 1,3; 1,4; 2,3; 2,4; 3,4] @
  map (fun k -> nonov stk (ins k)) [1;2;3;4] @
  [nonov stk tbl; nonov stk code] @
  map (fun k -> nonov (ins k) code) [1;2;3;4];;

let ml_lrr =
  let st k = ml_var k ("st",`:byte list`) in
  mk_list([`tbl:int64,2 * 2 EXP tl`] @
          map (fun k -> mk_pair(ml_sv k,mk_comb(`LENGTH:byte list->num`,
                                                st k))) [1;2;3;4] @
          [`word_sub stackpointer (word 496):int64,496`],`:int64#num`)
and ml_lwr =
  mk_list(map (fun k -> mk_pair(ml_ov k,ml_Lv k)) [1;2;3;4] @
          [`word_sub stackpointer (word 496):int64,496`],`:int64#num`);;

let ml_allvars k = map (ml_var k) (ml_names @ ["out",`:byte list`]);;

(*** The reload: from after the body to the body again (j + 4 bytes of   ***)
(*** each stream) or to the exit                                         ***)

let ml_pervars k = map (ml_var k)
  ["ofs",`:num`; "bc",`:num`];;

let ml_loop_vars =
  [`pc:num`; `stackpointer:int64`; `tbl:int64`; `tl:num`; `ws:num list`;
   `ml:num`; `n:num`; `j:num`; `e:uarch_event list`] @
  List.concat (map ml_allvars [1;2;3;4]);;

let mk_ml_goal pre post frame =
  let tm = mk_imp(list_mk_conj ml_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; frame]) in
  let fvs = frees tm in
  (match subtract fvs ml_loop_vars with
     [] -> ()
   | v::_ -> failwith ("mk_ml_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) ml_loop_vars,tm);;

(*** The reloads after the body, one stream at a time, as pieces with   ***)
(*** small contexts: reloaded (the pointer at least 8 bytes after the   ***)
(*** start) or not                                                      ***)

let mk_small_goal vars hyps pre post frame =
  let tm = mk_imp(list_mk_conj hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; frame]) in
  let fvs = frees tm in
  (match subtract fvs vars with
     [] -> ()
   | v::_ -> failwith ("mk_small_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vars,tm);;

let ml_code_hyps =
 [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`];;

(*** A stream reloaded: registers for the limit, the pointer, bc and the ***)
(*** container, the flag set (in a register or in the frame), and the    ***)
(*** registers used as temporaries                                      ***)

type rlspec =
 {ra : int; rb : int;             (* from ra to rb                       *)
  rlim : term; rptr : term; rbc : term; rcont : term;
  rbcout : term;                  (* the register of bc after the reload *)
  rflag : (term * int) option;    (* a register set to 1 ... *)
  rflagm : int option;            (* ... or a 32-bit slot set to 1       *)
  rtmp : term list;               (* the other registers written         *)
  rextra : term list};;           (* other facts after it                *)

let ml_rl_hyps =
  ml_code_hyps @
  [`8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64`;
   `nonoverlapping (src:int64,LENGTH(st:byte list)) (word pc,32000)`];;

(*** A stream not reloaded: the status 3 in w0 ***)

let rl1 = {ra = 0x590c; rb = 0x5688; rlim = `X16`; rptr = `X23`;
           rbc = `X26`; rcont = `X22`; rbcout = `X26`;
           rflag = Some(`X1`,1); rflagm = None; rtmp = [`X0`];
           rextra = [`read X0 s = word 0`]};;
let rl2 = {ra = 0x5688; rb = 0x56a8; rlim = `X20`; rptr = `X24`;
           rbc = `X2`; rcont = `X21`; rbcout = `X2`;
           rflag = None; rflagm = Some 184; rtmp = [`X6`; `X7`];
           rextra = []};;
let rl3 = {ra = 0x56a8; rb = 0x56c8; rlim = `X27`; rptr = `X25`;
           rbc = `X17`; rcont = `X30`; rbcout = `X17`;
           rflag = None; rflagm = Some 124; rtmp = [`X6`; `X7`];
           rextra = []};;

(*** Stream 4 after the body: reloaded (then the loop goes on if no      ***)
(*** stream had status 3 and there are 4 more bytes for stream 4) or not ***)

let ml_rd r v = mk_eq(mk_comb(mk_comb(`read:(armstate,int64)component->
                                      armstate->int64`,r),`s:armstate`),v);;

let ml_pcat a = mk_eq(`read PC s`,
                      mk_comb(`word:num->int64`,
                        mk_binop `(+):num->num->num` `pc:num`
                          (mk_small_numeral a)));;

(*** The exits of the main loop (0x62f8 when stream 4 is not reloaded,  ***)
(*** 0x65fc otherwise) to the order check (0x5ce4): BIT_DStream of each  ***)
(*** stream back in the frame (the container and the pointer only where  ***)
(*** the flag says they changed), and the registers of the tails         ***)

let ml_ex_vars =
  [`pc:num`; `stackpointer:int64`;
   `c1:int64`; `c2:int64`; `c3:int64`; `c4:int64`;
   `b1:num`; `b2:num`; `b3:num`; `b4:num`;
   `p1:int64`; `p2:int64`; `p3:int64`; `p4:int64`;
   `f1:num`; `f2:num`; `f3:num`; `f4:num`;
   `oend:int64`; `s1:int64`; `s2:int64`; `s3:int64`; `s4:int64`;
   `o2:int64`; `o3:int64`; `o4:int64`; `tl:num`; `n:num`;
   `e:uarch_event list`];;

let ml_ex_struct k c p =
  [ml_mem64 (224 + 40 * (k - 1)) c;
   ml_mem64 (240 + 40 * (k - 1)) p];;

let ml_ex_flagdisj k =
  let f = mk_var("f"^string_of_int k,`:num`)
  and c = mk_var("c"^string_of_int k,`:int64`)
  and p = mk_var("p"^string_of_int k,`:int64`) in
  mk_disj(list_mk_conj(mk_eq(f,`0`) :: ml_ex_struct k c p),mk_eq(f,`1`));;

let ml_ex_slots =
  [ml_mem64 144 `oend:int64`; ml_mem64 152 `s1:int64`;
   ml_mem64 160 `o2:int64`; ml_mem64 168 `o3:int64`;
   ml_mem64 176 `o4:int64`; ml_mem32 188 `tl:num`;
   ml_mem64 192 `word n:int64`; ml_mem64 200 `s2:int64`;
   ml_mem64 208 `s3:int64`; ml_mem64 216 `s4:int64`];;

let ml_ex_post_body =
  list_mk_conj
   ([`read PC s = word(pc + 0x5ce4)`;
     `read X9 s = oend /\ read X11 s = s1 /\ read X7 s = o2 /\
      read X8 s = o3 /\ read X6 s = o4 /\ read X20 s = word n /\
      read X10 s = s2 /\ read X15 s = s3 /\ read X27 s = s4 /\
      read X23 s = word tl`] @
    List.concat (map (fun k ->
      let c = mk_var("c"^string_of_int k,`:int64`)
      and b = mk_var("b"^string_of_int k,`:num`)
      and p = mk_var("p"^string_of_int k,`:int64`) in
      ml_ex_struct k c p @ [ml_mem32 (232 + 40 * (k - 1)) b]) [1;2;3;4]) @
    [`?e2. read events s = APPEND e2 e /\
           memaccess_inbounds e2 [word_sub stackpointer (word 496),496]
                                 [word_sub stackpointer (word 496),496]`]);;

let ml_ex_hyps =
  ml_code_hyps @
  [`aligned 16 (stackpointer:int64)`;
   `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                   (word pc,32000)`;
   `b1 < 2 EXP 32 /\ b2 < 2 EXP 32 /\ b3 < 2 EXP 32 /\ b4 < 2 EXP 32 /\
    tl < 2 EXP 32`];;

let ml_exa_goal =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x62f8) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X11 s = p4 /\ read X26 s = word b1 /\ read X15 s = word f4 /\
      read X2 s = word b2 /\ read X23 s = p1 /\ read X17 s = word b3 /\
      read X4 s = word b4 /\ read X1 s = word f1 /\ read X22 s = c1 /\
      read X21 s = c2 /\ read X24 s = p2 /\ read X30 s = c3 /\
      read X25 s = p3 /\ read X18 s = c4`;
     ml_mem32 184 `f2:num`; ml_mem32 124 `f3:num`] @
    ml_ex_slots @ map ml_ex_flagdisj [1;2;3;4] @
    [`read events s = e`])) in
  let frame =
   `MAYCHANGE [PC; X0; X6; X7; X8; X9; X10; X11; X15; X20; X23; X27; X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 144),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 224),160)]` in
  mk_small_goal ml_ex_vars ml_ex_hyps pre
    (mk_abs(`s:armstate`,ml_ex_post_body)) frame;;

let ml_exb_goal =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x65fc) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X11 s = p4 /\ read X26 s = word b1 /\
      read X2 s = word b2 /\ read X23 s = p1 /\ read X17 s = word b3 /\
      read X0 s = word b4 /\ read X1 s = word f1 /\ read X22 s = c1 /\
      read X21 s = c2 /\ read X24 s = p2 /\ read X30 s = c3 /\
      read X25 s = p3 /\ read X18 s = c4`;
     ml_mem32 184 `f2:num`; ml_mem32 124 `f3:num`] @
    ml_ex_slots @ map ml_ex_flagdisj [1;2;3] @
    [`read events s = e`])) in
  let frame =
   `MAYCHANGE [PC; X0; X3; X6; X7; X8; X9; X10; X11; X15; X20; X23; X27;
               X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 144),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 224),160)]` in
  mk_small_goal ml_ex_vars ml_ex_hyps pre
    (mk_abs(`s:armstate`,ml_ex_post_body)) frame;;

(*** The proofs: one case for each flag ***)

let ML_EX_TAC ks : tactic =
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun k ->
    FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
      check (fun th -> concl th = vsubst [`s0:armstate`,`s:armstate`]
                                         (ml_ex_flagdisj k))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = mk_var("f"^string_of_int k,`:num`))))
   ks THEN
  ZSTD_SIM_UNTIL_TAC [0x5ce4] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  T4_CONJ_TAC;;

let ML_EXA = prove(ml_exa_goal, ML_EX_TAC [1;2;3;4]);;
let ML_EXB = prove(ml_exb_goal, ML_EX_TAC [1;2;3]);;

(*** The main loop as a whole: from the body with j bytes of each stream ***)
(*** decoded to the exit, by the pieces (the body, the four reloads and  ***)
(*** the two exits), each simulated in its own small context             ***)

(*** A theorem with its quantified variables instantiated by name ***)

let ml_inst_thm th (alist:(string * term) list) =
  let th0 = SPEC_ALL th in
  let vs = frees(concl th0) in
  let sub = mapfilter (fun v ->
    let n = fst(dest_var v) in
    (assoc n alist,v)) vs in
  INST sub th0;;

(*** A piece run by a big step from the current state: th with its      ***)
(*** variables instantiated (e being the events so far), its hypotheses  ***)
(*** from the assumptions, and the remaining conjuncts of its            ***)
(*** precondition                                                        ***)

let ML_HYP_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [ML_FACT_TAC; ASM_REWRITE_TAC[] THEN NO_TAC;
         REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         NONOVERLAPPING_TAC; ML_ARITH_TAC];;

let ML_PRE_MEMSAFE_TAC : tactic =
  W(fun (asl,w) ->
    if is_memsafe_clause w then
      REWRITE_TAC[puff_memsafe] THEN EXISTS_TAC `[]:uarch_event list` THEN
      ASM_REWRITE_TAC[APPEND; MEMACCESS_INBOUNDS_NIL]
    else NO_TAC);;

let ML_BIGSTEP_TAC th alist : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun (asl,w) ->
    let s = rand w in
    let rd = list_mk_icomb "read" [`events`; s] in
    let ec = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
                                  is_eq t && lhs t = rd) asl))) in
    let th' = ml_inst_thm th (("e",ec)::alist) in
    let n = let sn = fst(dest_var s) in
            int_of_string(String.sub sn 1 (String.length sn - 1)) in
    MP_TAC th' THEN ANTS_TAC THENL [ML_HYP_TAC; ALL_TAC] THEN
    ARM_BIGSTEP_TAC ZSTD_EXEC ("s"^string_of_int(n + 1)) THEN
    W(fun (_,w) ->
      if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                       with Failure _ -> false)
      then EVENTS_UNABBREV_TAC THEN MEMSAFE_STRIP_TAC
      else REPEAT CONJ_TAC THEN
           FIRST [ML_PRE_MEMSAFE_TAC; ML_FACT_TAC; T4_CONJ_TAC]));;

(*** The names of the variables of stream k ***)

let ml_alist k =
  map (fun (s,ty) -> s,ml_var k (s,ty)) (ml_names @ ["out",`:byte list`]);;

(*** The state of a stream after jj bytes, good or bad, as one predicate ***)
(*** (so that the big steps of the loop keep it as one assumption)       ***)

let huf_dstate = new_definition
 `huf_dstate ws ml (st:byte list) r jj ofs bc out <=>
    SND(SND(huf_decode ws ml st r jj)) /\
    FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
    out = FST(huf_decode ws ml st r jj) \/
    ~SND(SND(huf_decode ws ml st r jj)) /\ ofs = 0 /\ 64 < bc /\
    bc <= 64 + 12 * jj`;;

(*** The body with that predicate in its postcondition ***)

let ML_BODY_DSTATE =
  let fold_conv = REWRITE_CONV[GSYM huf_dstate] in
  let th = SPEC_ALL ML_BODY in
  let th' = CONV_RULE (RAND_CONV(RATOR_CONV(RAND_CONV
              (ABS_CONV(ONCE_DEPTH_CONV fold_conv))))) th in
  GEN_ALL th';;

(*** The state of a stream after the reload: back by the bytes used if  ***)
(*** at least 8 bytes after its start                                    ***)

let huf_rlofs = new_definition
 `huf_rlofs ofs bc = if 8 <= ofs then ofs - bc DIV 8 else ofs`;;

let huf_rlbc = new_definition
 `huf_rlbc ofs bc = if 8 <= ofs then bc MOD 8 else bc`;;

let ml_rlwin =
 `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * huf_rlofs ofs bc)) MOD
       2 EXP 64):int64`;;

let ml_oldwin =
 `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
       2 EXP 64):int64`;;

(*** Streams 1-3: the pointer, bc and the container, the flag set if    ***)
(*** reloaded, the status in w0 (3 if not reloaded)                      ***)

let ml_rlu_vars =
  [`pc:num`; `stackpointer:int64`; `src:int64`; `st:byte list`; `ofs:num`;
   `bc:num`; `f:num`; `w:num`; `op:int64`; `L:num`; `j:num`;
   `e:uarch_event list`];;

let ml_rlu_goal (sp:rlspec) =
  let rd r v = mk_eq(mk_comb(mk_comb(`read:(armstate,int64)component->
                                       armstate->int64`,r),`s:armstate`),v) in
  let stk = match sp.rflagm with Some _ -> true | None -> false in
  let flagpre,flagpost = match sp.rflag, sp.rflagm with
      Some(r,_),_ -> [rd r `word f:int64`],
                     [rd r `word(if 8 <= ofs then 1 else f):int64`]
    | None,Some k ->
        [ml_mem32 k `f:num`],
        [ml_mem32 k `if 8 <= ofs then 1 else f`]
    | None,None -> [],[] in
  let w0pre,w0post =
    if sp.ra = 0x590c then [],[`read X0 s = word(if 8 <= ofs then 0 else 3)`]
    else [`read X0 s = word w`],[`read X0 s = word(if 8 <= ofs then w else 3)`]
  in
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc`; ml_pcat sp.ra;
     rd sp.rlim `word_add src (word 8):int64`;
     rd sp.rptr `word_add src (word ofs):int64`;
     rd sp.rbc `word bc:int64`; rd sp.rcont ml_oldwin] @ flagpre @ w0pre @
    [`read (memory :> bytes(src,LENGTH(st:byte list))) s =
      num_of_bytelist st`] @
    (if stk then [`read SP s = word_sub stackpointer (word 496)`] else []) @
    [`read events s = e`])) in
  let wr = match sp.rflagm with
      Some k -> mk_list([mk_pair(ml_spk k,`4`)],`:int64#num`)
    | None -> `[]:(int64#num)list` in
  let ms = subst [wr,`wr:(int64#num)list`]
   `?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2 [src,LENGTH(st:byte list)] wr` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   ([ml_pcat sp.rb;
     rd sp.rptr `word_add src (word (huf_rlofs ofs bc)):int64`;
     rd sp.rbcout `word (huf_rlbc ofs bc):int64`;
     rd sp.rcont ml_rlwin] @ flagpost @ w0post @ [ms])) in
  let regs = mk_list(`PC` :: `X0` :: sp.rptr :: sp.rbcout :: sp.rcont ::
                     (match sp.rflag with Some(r,_) -> [r] | None -> []) @
                     filter (fun r -> r <> `X0`) sp.rtmp,
                     `:(armstate,int64)component`) in
  let frame = match sp.rflagm with
      Some k ->
        subst [regs,`r:((armstate,int64)component)list`; ml_spk k,`a:int64`]
         `MAYCHANGE (r:((armstate,int64)component)list) ,,
          MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(a,4)]`
    | None ->
        subst [regs,`r:((armstate,int64)component)list`]
         `MAYCHANGE (r:((armstate,int64)component)list) ,,
          MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` in
  let hyps = ml_rl_hyps @
   [`ofs <= LENGTH(st:byte list) /\ bc < 2 EXP 32 /\ f < 2 EXP 32 /\
     w < 2 EXP 32`;
    `8 <= ofs ==> ofs + 8 <= LENGTH(st:byte list) /\ bc <= 64`] @
   (if stk then [`aligned 16 (stackpointer:int64)`;
                 `nonoverlapping (word_sub (stackpointer:int64) (word 496),
                                  496) (src:int64,LENGTH(st:byte list))`;
                 `nonoverlapping (word_sub (stackpointer:int64) (word 496),
                                  496) (word pc,32000)`]
    else []) in
  mk_small_goal ml_rlu_vars hyps pre post frame;;

let ML_RLU_TAC (sp:rlspec) : tactic =
  REWRITE_TAC[GSYM puff_memsafe; huf_rlofs; huf_rlbc] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ASM_CASES_TAC `8 <= ofs` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = `8 <= ofs`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    SUBGOAL_THEN
     `bc DIV 8 <= ofs /\ (ofs - bc DIV 8) + 8 <= LENGTH(st:byte list)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ML_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
        `ofs + 8 <= LENGTH(st:byte list)`] THEN ARITH_TAC;
      DISCH_TAC] THEN
    T4_SLICE_TAC `ofs - bc DIV 8` `s0:armstate` THEN
    ZSTD_SIM_UNTIL_TAC [sp.rb] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`src:int64`; `ofs:num`;
      `bc DIV 8`] T4_SUB_ADDR) (ASSUME `bc DIV 8 <= ofs`)]) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN T4_CONJ_TAC;
    MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
        `ofs <= LENGTH(st:byte list)`] THEN ARITH_TAC;
      DISCH_TAC] THEN
    ZSTD_SIM_UNTIL_TAC [sp.rb] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    T4_CONJ_TAC];;

let ML_RL1U = prove(ml_rlu_goal rl1, ML_RLU_TAC rl1);;
let ML_RL2U = prove(ml_rlu_goal rl2, ML_RLU_TAC rl2);;
let ML_RL3U = prove(ml_rlu_goal rl3, ML_RLU_TAC rl3);;

(*** Stream 4, and the decision of the loop ***)

let ml_rl4u_goal =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc`; ml_pcat 0x56c8;
    `read X10 s = word_add src (word 8) /\
     read X11 s = word_add src (word ofs) /\
     read X4 s = word bc`;
    ml_rd `X18` ml_oldwin;
    `read X0 s = word w /\
     read X12 s = word_add op (word (j + 4)) /\ read X15 s = word f /\
     read SP s = word_sub stackpointer (word 496)`;
    subst [ml_spk 112,`a:int64`]
     `read (memory :> bytes64 a) s = word_add op (word (L - 3))`;
    `read (memory :> bytes(src,LENGTH(st:byte list))) s =
     num_of_bytelist st /\
     read events s = e`]) in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [`read PC s = (if 8 <= ofs
                  then if w = 0 /\ j + 8 <= L then word(pc + 0x56fc)
                       else word(pc + 0x65fc)
                  else word(pc + 0x62f8))`;
    ml_rd `X11` `word_add src (word (huf_rlofs ofs bc)):int64`;
    ml_rd `X18` ml_rlwin;
    `read X0 s = (if 8 <= ofs then word (bc MOD 8) else word w)`;
    `read X4 s = (if 8 <= ofs then word(if j + 8 <= L then 1 else 0)
                  else word bc)`;
    `read X15 s = (if 8 <= ofs then word(if w = 0 /\ j + 8 <= L then 1 else 0)
                   else word f)`;
    `?e2. read events s = APPEND e2 e /\
          memaccess_inbounds e2
           [src,LENGTH(st:byte list);
            word_add (word_sub stackpointer (word 496)) (word 112),8] []`])
  in
  let frame = `MAYCHANGE [PC; X0; X4; X6; X11; X15; X18] ,,
               MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` in
  mk_small_goal ml_rlu_vars
   (ml_rl_hyps @
    [`ofs <= LENGTH(st:byte list) /\ bc < 2 EXP 32 /\ f < 2 EXP 32`;
     `8 <= ofs ==> ofs + 8 <= LENGTH(st:byte list) /\ bc <= 64`;
     `aligned 16 (stackpointer:int64)`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (src:int64,LENGTH(st:byte list))`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word pc,32000)`;
     `val(op:int64) + L < 2 EXP 64 /\ j + 4 <= L /\ 3 <= L /\
      (w = 0 \/ w = 3)`])
   pre post frame;;

(*** The flags of the comparison of the output with its limit ***)

let ML_RL4_FIN_TAC : tactic =
  REWRITE_TAC[WORD_AND_0; WORD_ZX_0; VAL_WORD; DIMINDEX_64;
              VAL_WORD_SUB_CASES] THEN
  SUBGOAL_THEN `(L - 3 - (j + 4)) MOD 2 EXP 64 = L - 3 - (j + 4) /\
                (L - 3) MOD 2 EXP 64 = L - 3 /\
                (j + 4) MOD 2 EXP 64 = j + 4`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MAP_EVERY UNDISCH_TAC [`val(op:int64) + L < 2 EXP 64`; `j + 4 <= L`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
  FA_ARITHV_TAC [`L:num`; `j:num`; `op:int64`; `w:num`];;

let ML_RL4U = prove
 (ml_rl4u_goal,
  REWRITE_TAC[GSYM puff_memsafe; huf_rlofs; huf_rlbc] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ASM_CASES_TAC `8 <= ofs` THEN
  ASM_REWRITE_TAC[] THENL
   [(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = `8 <= ofs`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  SUBGOAL_THEN
   `bc DIV 8 <= ofs /\ (ofs - bc DIV 8) + 8 <= LENGTH(st:byte list)`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ML_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs + 8 <= LENGTH(st:byte list)`] THEN ARITH_TAC;
    DISCH_TAC] THEN
  T4_SLICE_TAC `ofs - bc DIV 8` `s0:armstate` THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`op:int64`; k] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`val(op:int64) + L < 2 EXP 64`; `j + 4 <= L`;
                             `3 <= L`] THEN ARITH_TAC;
      DISCH_TAC])
   [`j + 4`; `L - 3`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    concl th = `w = 0 \/ w = 3`)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_CASES_TAC `j + 8 <= L` THEN
  ASM_REWRITE_TAC[] THEN
  ZSTD_SIM_UNTIL_TAC [0x56fc; 0x65fc] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`src:int64`; `ofs:num`;
    `bc DIV 8`] T4_SUB_ADDR) (ASSUME `bc DIV 8 <= ofs`)]) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST [ML_FACT_TAC; T4_CONJ_TAC])) THEN ML_RL4_FIN_TAC;
    MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
        `ofs <= LENGTH(st:byte list)`] THEN ARITH_TAC;
      DISCH_TAC] THEN
    ZSTD_SIM_UNTIL_TAC [0x62f8] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    T4_CONJ_TAC]);;

(*** The main loop as one theorem: from the body to an exit (0x62f8 or  ***)
(*** 0x65fc). The flags are all f, and f = 0 only before the first      ***)
(*** reload, when the containers and pointers are those in the frame    ***)
(*** (from the initial offsets ofs0_k); after the loop a flag is 0 only ***)
(*** for a stream never reloaded                                        ***)

let ml_o0 k = mk_var("ofs0"^string_of_int k,`:num`);;

let ml_struct0 k =
  let m = el (k - 1) ml_regs in
  ml_rinst m (list_mk_conj
   (map (subst [mk_var("ofs0_",`:num`),`ofs:num`])
     [subst [tail_spv `s_c:num`,`a:int64`]
       `read (memory :> bytes64 a) s =
        word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs0_)) MOD
             2 EXP 64)`;
      subst [tail_spv `s_p:num`,`a:int64`]
       `read (memory :> bytes64 a) s = word_add src (word ofs0_)`])) |>
  vsubst [ml_o0 k,mk_var("ofs0_",`:num`)];;

let ml_flagsf =
  list_mk_conj(map (fun (m:mlreg) -> m.rflag `f:num`) ml_regs @
   [`f = 0 \/ f = 1`;
    mk_imp(`f = 0`,list_mk_conj(map (fun k ->
      mk_eq(ml_var k ("ofs",`:num`),ml_o0 k)) [1;2;3;4]))]);;

let ml_inv_body2 jt =
  list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x56fc) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X5 s = tbl /\
      read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable ws ml tl) /\
      read X3 s = word(64 - tl)`;
     el 1 ml_slots] @
    map ml_struct0 [1;2;3;4] @
    map (fun m -> ml_rinst m (subst [jt,`j:num`] ml_inv1)) ml_regs @
    [ml_flagsf]);;

let ml_inv2 = with_memsafe ml_lrr ml_lwr
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists(`j:num` :: List.concat(map ml_pervars [1;2;3;4]) @
                 [`f:num`],
    mk_conj(`m = L4 - j`,ml_inv_body2 `j:num`))));;

(*** One stream at the exit of the loop ***)

let ml_lexit1 = list_mk_conj
 [mk_eq(`read (r_cont:tailreg) s`,ml_win);
  `read (r_ptr:tailreg) s = word_add src (word ofs) /\
   read (r_op:tailreg) s = word_add op (word j) /\
   read (memory :> bytes(src,LENGTH(st:byte list))) s =
   num_of_bytelist st /\
   read (memory :> bytes(op,j)) s = num_of_bytelist out /\
   LENGTH(out:byte list) = j /\
   huf_dstate ws ml st r j ofs bc out /\
   (ofs = 0 \/ ofs + 8 <= LENGTH st) /\ j <= L`];;

let ml_lexit_common =
  list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read SP s = word_sub stackpointer (word 496) /\
      read X26 s = word bc1 /\ read X2 s = word bc2 /\ read X17 s = word bc3 /\
      read X1 s = word f1`;
     ml_mem32 184 `f2:num`; ml_mem32 124 `f3:num`] @
    map (fun m -> ml_rinst m ml_lexit1) ml_regs @
    map (fun k ->
      let f = mk_var("f"^string_of_int k,`:num`) in
      mk_conj(mk_disj(mk_eq(f,`0`),mk_eq(f,`1`)),
              mk_imp(mk_eq(f,`0`),mk_eq(ml_var k ("ofs",`:num`),ml_o0 k))))
      [1;2;3;4]);;

let ml_lexit = with_memsafe ml_lrr ml_lwr (mk_abs(`s:armstate`,
  list_mk_exists(`j:num` :: List.concat(map (fun k ->
                   ml_pervars k @ [ml_var k ("out",`:byte list`)])
                 [1;2;3;4]) @ [`f1:num`; `f2:num`; `f3:num`; `f4:num`],
   mk_conj(ml_lexit_common,
     mk_disj(`read PC s = word(pc + 0x62f8) /\ read X4 s = word bc4 /\
              read X15 s = word f4`,
             `read PC s = word(pc + 0x65fc) /\ read X0 s = word bc4`)))));;

let ml_loop2_frame =
 `MAYCHANGE [PC; X0; X1; X2; X4; X6; X7; X8; X9; X11; X12; X13; X14; X15;
             X17; X18; X19; X21; X22; X23; X24; X25; X26; X28; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op1,L1); memory :> bytes(op2,L2);
             memory :> bytes(op3,L3); memory :> bytes(op4,L4);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 184),4);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 124),4)]`;;

let ml_loop2_vars =
  ml_loop_vars @ [`ofs01:num`; `ofs02:num`; `ofs03:num`; `ofs04:num`];;

let ml_loop2_goal =
  let tm = mk_imp(list_mk_conj ml_hyps,
                  list_mk_icomb "ensures"
                   [`arm`;
                    mk_abs(`s:armstate`,mk_exists(`m:num`,
                      list_mk_comb(ml_inv2,[`m:num`; `s:armstate`])));
                    ml_lexit; ml_loop2_frame]) in
  let fvs = frees tm in
  (match subtract fvs ml_loop2_vars with
     [] -> ()
   | v::_ -> failwith ("ml_loop2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) ml_loop2_vars,tm);;

(*** The state of a stream after the reload ***)

let ML_DSTATE_RELOAD = prove
 (`!ws ml (st:byte list) r jj ofs bc out.
        huf_dstate ws ml st r jj ofs bc out
        ==> huf_dstate ws ml st r jj (huf_rlofs ofs bc) (huf_rlbc ofs bc) out`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_dstate; huf_rlofs; huf_rlbc] THEN
  ASM_CASES_TAC `8 <= ofs` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let ML_DSTATE_NORMAL = prove
 (`!ws ml (st:byte list) r jj ofs bc out.
        huf_dstate ws ml st r jj ofs bc out /\ 8 <= ofs ==> bc <= 64`,
  REWRITE_TAC[huf_dstate] THEN ARITH_TAC);;

let ML_DSTATE_BOUND = prove
 (`!ws ml (st:byte list) r jj ofs bc out.
        huf_dstate ws ml st r jj ofs bc out ==> bc <= 64 + 12 * jj`,
  REWRITE_TAC[huf_dstate] THEN ARITH_TAC);;

(*** The facts of stream k for its reload, with the bits used b after   ***)
(*** the body                                                           ***)

let ML_LOOP_FACTS_TAC k b : tactic =
  let ofs = ml_var k ("ofs",`:num`) and st = ml_var k ("st",`:byte list`)
  and lv = ml_var k ("L",`:num`) in
  let lst = mk_comb(`LENGTH:byte list->num`,st) in
  let ds th = let t = concl th in
    is_comb t && (try fst(dest_const(fst(strip_comb t))) = "huf_dstate" &&
                      el 2 (snd(strip_comb t)) = st with Failure _ -> false) in
  let g1 = mk_imp(mk_binop `(<=):num->num->bool` `8` ofs,
                  mk_conj(mk_binop `(<=):num->num->bool`
                            (mk_binop `(+):num->num->num` ofs `8`) lst,
                          mk_binop `(<=):num->num->bool` b `64`))
  and g2 = mk_binop `(<=):num->num->bool` ofs lst
  and g3 = mk_binop `(<):num->num->bool` b `2 EXP 32` in
  let disj = mk_disj(mk_eq(ofs,`0`),
                     mk_binop `(<=):num->num->bool`
                       (mk_binop `(+):num->num->num` ofs `8`) lst) in
  W(fun (asl,w) ->
    let dth = snd(find (fun (_,th) -> ds th) asl) in
    let bth = MATCH_MP ML_DSTATE_BOUND dth in
    SUBGOAL_THEN (list_mk_conj [g1; g2; g3]) STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THENL
         [MP_TAC(ASSUME disj) THEN UNDISCH_TAC (lhand g1) THEN ARITH_TAC;
          ACCEPT_TAC(MATCH_MP ML_DSTATE_NORMAL
                       (CONJ dth (ASSUME (lhand g1))))];
        MP_TAC(ASSUME disj) THEN ARITH_TAC;
        MP_TAC bth THEN
        MAP_EVERY UNDISCH_TAC [subst [lv,`L:num`] `j + 4 <= L`;
                               subst [lv,`L:num`] `L < 2 EXP 28`] THEN
        ARITH_TAC];
      ALL_TAC]);;

(*** The proof of the main loop: each iteration by big steps of the  ***)
(*** pieces, the body and the four reloads, then the decision        ***)

let ML_STATUS_TAC wv ofs prev =
  ABBREV_TAC (mk_eq(wv,mk_cond(mk_binop `(<=):num->num->bool` `8` ofs,
                               prev,`3`))) THEN
  SUBGOAL_THEN (mk_conj(mk_disj(mk_eq(wv,`0`),mk_eq(wv,`3`)),
                        mk_binop `(<):num->num->bool` wv `2 EXP 32`))
   (CONJUNCTS_THEN ASSUME_TAC) THENL
   [EXPAND_TAC (fst(dest_var wv)) THEN COND_CASES_TAC THEN
    TRY(FIRST_ASSUM(fun th -> if is_disj(concl th) &&
          (lhand(lhand(concl th)) = prev) then DISJ_CASES_TAC th else NO_TAC))
    THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let ML_CASE_REWRITE_TAC (facts:term list) =
  let ths = map ASSUME facts in
  RULE_ASSUM_TAC(fun th ->
    if mem (concl th) facts then th
    else REWRITE_RULE([huf_rlofs; huf_rlbc] @ ths) th);;

let ml_is_dstate k th =
  let st = ml_var k ("st",`:byte list`) in
  let t = concl th in
  is_comb t && (try fst(dest_const(fst(strip_comb t))) = "huf_dstate" &&
                    el 2 (snd(strip_comb t)) = st with Failure _ -> false);;

(*** The good state of a reloaded stream k from its huf_dstate ***)

let ML_GOOD_TAC k : tactic =
  let ofs = ml_var k ("ofs",`:num`) in
  let c8 = mk_binop `(<=):num->num->bool` `8` ofs in
  W(fun (asl,w) ->
    let dth = snd(find (fun (_,th) -> ml_is_dstate k th) asl) in
    MP_TAC(REWRITE_RULE[huf_dstate] dth) THEN
    DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
     [ALL_TAC;
      W(fun (asl,w) ->
        let z = mk_eq(ofs,`0`) in
        let fth = EQ_MP (ARITH_RULE(mk_eq(mk_conj(c8,z),`F`)))
                        (CONJ (ASSUME c8) (ASSUME z)) in
        CONTR_TAC fth)]);;

let ML_DIVISION_TAC b : tactic =
  MP_TAC(SPECL [b; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC);;

(*** A goal read c s = y from a fact read c s = x and x = y ***)

let ML_MEMEQ_TAC : tactic =
  W(fun (asl,w) ->
    let l = lhs w in
    let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l)
                      asl) in
    GEN_REWRITE_TAC LAND_CONV [th] THEN
    TRY AP_TERM_TAC THEN (ML_FACT_TAC ORELSE
      (CONV_TAC SYM_CONV THEN ML_FACT_TAC)));;

let ML_LOOPCASE_CONJ_TAC : tactic =
  FIRST [ML_FACT_TAC;
         REWRITE_TAC[MP (SPECL [`op4:int64`; `L4:num`] TAIL_OLIM_LEMMA)
                       (ASSUME `3 <= L4`)] THEN ML_FACT_TAC;
         ML_MEMEQ_TAC;
         CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         DISJ2_TAC THEN ML_ARITH_TAC;
         ML_ARITH_TAC;
         FA_ARITHV_TAC [`L1:num`; `L2:num`; `L3:num`; `L4:num`; `j:num`]];;

let ML_EXITFACTS_TAC k b : tactic =
  let ofs = ml_var k ("ofs",`:num`) and st = ml_var k ("st",`:byte list`)
  and o0 = ml_o0 k in
  let lst = mk_comb(`LENGTH:byte list->num`,st) in
  let rlo = list_mk_icomb "huf_rlofs" [ofs; b] in
  let g1 = mk_disj(mk_eq(rlo,`0`),
                   mk_binop `(<=):num->num->bool`
                     (mk_binop `(+):num->num->num` rlo `8`) lst) in
  let fk = mk_cond(mk_binop `(<=):num->num->bool` `8` ofs,`1`,`f:num`) in
  let g2 = mk_conj(mk_disj(mk_eq(fk,`0`),mk_eq(fk,`1`)),
                   mk_imp(mk_eq(fk,`0`),mk_eq(rlo,o0))) in
  W(fun (asl,w) ->
    let dth = snd(find (fun (_,th) -> ml_is_dstate k th) asl) in
    ASSUME_TAC(MATCH_MP ML_DSTATE_RELOAD dth) THEN
    SUBGOAL_THEN g1 ASSUME_TAC THENL
     [REWRITE_TAC[huf_rlofs] THEN COND_CASES_TAC THENL
       [DISJ2_TAC THEN FIRST_ASSUM(fun th ->
          if is_imp(concl th) && lhand(concl th) = mk_binop
             `(<=):num->num->bool` `8` ofs then MP_TAC th else NO_TAC) THEN
        MP_TAC(ASSUME(mk_binop `(<=):num->num->bool` `8` ofs)) THEN
        ARITH_TAC;
        ML_FACT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN g2 (CONJUNCTS_THEN ASSUME_TAC) THENL
     [ASM_CASES_TAC (mk_binop `(<=):num->num->bool` `8` ofs) THEN
      ASM_REWRITE_TAC[huf_rlofs] THEN CONV_TAC NUM_REDUCE_CONV THEN
      W(fun (asl,w) ->
        let imp = snd(find (fun (_,th) -> is_imp(concl th) &&
                                lhand(concl th) = `f = 0`) asl)
        and dsj = ASSUME `f = 0 \/ f = 1` in
        MP_TAC imp THEN MP_TAC dsj THEN CONV_TAC TAUT);
      ALL_TAC]);;

let ml_fk k =
  mk_cond(mk_binop `(<=):num->num->bool` `8` (ml_var k ("ofs",`:num`)),
          `1`,`f:num`);;

let ml_wits_exit =
  `j + 4` ::
  List.concat (map (fun (k,b,ov) ->
    let ofs = ml_var k ("ofs",`:num`) in
    [list_mk_icomb "huf_rlofs" [ofs; b]; list_mk_icomb "huf_rlbc" [ofs; b];
     ov])
   [1,`bc':num`,`out':byte list`; 2,`bc'':num`,`out'':byte list`;
    3,`bc''':num`,`out''':byte list`; 4,`bc'''':num`,`out'''':byte list`]) @
  map ml_fk [1;2;3;4];;

(*** The loop ***)

let ML_LOOP2 = prove
 (ml_loop2_goal,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `j:num` THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC (List.concat(map ml_pervars [1;2;3;4])) THEN
  ENSURES_EXISTS_PRE_TAC `f:num` THEN PUFF_INIT_TAC "s0" THEN
  ML_BIGSTEP_TAC ML_BODY_DSTATE [] THEN
  ML_LOOP_FACTS_TAC 1 `bc':num` THEN ML_LOOP_FACTS_TAC 2 `bc'':num` THEN
  ML_LOOP_FACTS_TAC 3 `bc''':num` THEN ML_LOOP_FACTS_TAC 4 `bc'''':num` THEN
  SUBGOAL_THEN `f < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(ASSUME `f = 0 \/ f = 1`) THEN ARITH_TAC; ALL_TAC] THEN
  ML_BIGSTEP_TAC ML_RL1U
   [("src",`src1:int64`); ("st",`st1:byte list`); ("ofs",`ofs1:num`);
    ("bc",`bc':num`); ("w",`0`)] THEN
  ML_STATUS_TAC `w1:num` `ofs1:num` `0` THEN
  ML_BIGSTEP_TAC ML_RL2U
   [("src",`src2:int64`); ("st",`st2:byte list`); ("ofs",`ofs2:num`);
    ("bc",`bc'':num`); ("w",`w1:num`)] THEN
  ML_STATUS_TAC `w2:num` `ofs2:num` `w1:num` THEN
  ML_BIGSTEP_TAC ML_RL3U
   [("src",`src3:int64`); ("st",`st3:byte list`); ("ofs",`ofs3:num`);
    ("bc",`bc''':num`); ("w",`w2:num`)] THEN
  ML_STATUS_TAC `w3:num` `ofs3:num` `w2:num` THEN
  SUBGOAL_THEN `3 <= L4` ASSUME_TAC THENL
   [MP_TAC(ASSUME `j + 4 <= L4`) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`op4:int64`; `L4:num`]
    TAIL_OLIM_LEMMA) (ASSUME `3 <= L4`)]) THEN
  ML_BIGSTEP_TAC ML_RL4U
   [("src",`src4:int64`); ("st",`st4:byte list`); ("ofs",`ofs4:num`);
    ("bc",`bc'''':num`); ("w",`w3:num`); ("op",`op4:int64`);
    ("L",`L4:num`)] THEN
  ASM_CASES_TAC `8 <= ofs4 /\ w3 = 0 /\ j + 8 <= L4` THENL
   [SUBGOAL_THEN `8 <= ofs1 /\ 8 <= ofs2 /\ 8 <= ofs3` STRIP_ASSUME_TAC
    THENL
     [MAP_EVERY EXPAND_TAC ["w3"; "w2"; "w1"] THEN
      POP_ASSUM MP_TAC THEN MAP_EVERY EXPAND_TAC ["w3"; "w2"; "w1"] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
      concl th = `8 <= ofs4 /\ w3 = 0 /\ j + 8 <= L4`)) THEN
    ML_CASE_REWRITE_TAC [`8 <= ofs1`; `8 <= ofs2`; `8 <= ofs3`;
                         `8 <= ofs4`; `j + 8 <= L4`; `w3 = 0`] THEN
    PUFF_FINAL_TAC THEN MAP_EVERY ML_GOOD_TAC [1;2;3;4] THEN
    MAP_EVERY ML_DIVISION_TAC
     [`bc':num`; `bc'':num`; `bc''':num`; `bc'''':num`] THEN
    DISJ1_TAC THEN EXISTS_TAC `L4 - (j + 4)` THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m = L4 - j`; `j + 8 <= L4`] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `j + 4` THEN
    MAP_EVERY EXISTS_TAC
     [`ofs1 - bc' DIV 8`; `bc' MOD 8`; `ofs2 - bc'' DIV 8`; `bc'' MOD 8`;
      `ofs3 - bc''' DIV 8`; `bc''' MOD 8`; `ofs4 - bc'''' DIV 8`;
      `bc'''' MOD 8`; `1`] THEN
    REPEAT CONJ_TAC THEN ML_LOOPCASE_CONJ_TAC;
    ML_EXITFACTS_TAC 1 `bc':num` THEN ML_EXITFACTS_TAC 2 `bc'':num` THEN
    ML_EXITFACTS_TAC 3 `bc''':num` THEN ML_EXITFACTS_TAC 4 `bc'''':num` THEN
    PUFF_FINAL_TAC THEN DISJ2_TAC THEN MAP_EVERY EXISTS_TAC ml_wits_exit THEN
    REPEAT CONJ_TAC THEN TRY(FIRST [ML_FACT_TAC; ML_LOOPCASE_CONJ_TAC]) THEN
    ASM_CASES_TAC `8 <= ofs4` THENL
     [SUBGOAL_THEN `~(w3 = 0 /\ j + 8 <= L4)` ASSUME_TAC THENL
       [MP_TAC(ASSUME `~(8 <= ofs4 /\ w3 = 0 /\ j + 8 <= L4)`) THEN
        REWRITE_TAC[ASSUME `8 <= ofs4`];
        ALL_TAC] THEN
      DISJ2_TAC THEN
      ML_CASE_REWRITE_TAC [`8 <= ofs4`; `~(w3 = 0 /\ j + 8 <= L4)`] THEN
      REWRITE_TAC[huf_rlbc; ASSUME `8 <= ofs4`] THEN CONJ_TAC THEN
      ML_FACT_TAC;
      DISJ1_TAC THEN ML_CASE_REWRITE_TAC [`~(8 <= ofs4)`] THEN
      REWRITE_TAC[huf_rlbc; ASSUME `~(8 <= ofs4)`] THEN
      REPEAT CONJ_TAC THEN ML_FACT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The initializations of the BIT_DStreams of the four streams (0x54c0,      *)
(* 0x5508, 0x554c, 0x5594).                                                  *)
(* ------------------------------------------------------------------------- *)

(*** The initialization of the BIT_DStream of a stream of l bytes (stream ***)
(*** 1 at 0x54c0): the container from the last 8 bytes (or all of them,  ***)
(*** fewer than 8), bc the bits of the padding (with the missing bytes),  ***)
(*** the pointer, start and limit; errors for l = 0 and a last byte 0    ***)

let in_ofs0 = `if 8 <= l then l - 8 else 0`;;
let in_bc0 =
 `(if 8 <= l then 0 else 8 * (8 - l)) +
  huf_lastshift(EL (l - 1) (st:byte list))`;;

let in_err =
 `word(if l = 0 then 18446744073709551544
       else if 8 <= l then 18446744073709551615
       else 18446744073709551596):int64`;;

let in1_goal =
  let win = subst [in_ofs0,`ofs:num`]
   `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64)
    :int64` in
  let src = `word_add csrc (word 6):int64` in
  let pre = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x54c0) /\
     read SP s = word_sub stackpointer (word 496) /\
     read X18 s = csrc /\ read X12 s = word l /\ read X2 s = word l /\
     read X25 s = v25 /\ read X26 s = v26 /\ read X0 s = x0`;
    subst [src,`a:int64`]
     `read (memory :> bytes(a,LENGTH(st:byte list))) s = num_of_bytelist st`;
    `read events s = e`]) in
  let good = list_mk_conj
   ([`read PC s = word(pc + 0x5508)`;
     `read X10 s = word_add csrc (word (6 + l)) /\
      read X16 s = word_add csrc (word 14) /\
      read X11 s = word_add csrc (word 6)`;
     mk_eq(`read X26 s`,mk_comb(`word:num->int64`,in_bc0));
     ml_mem64 224 win; ml_mem32 232 in_bc0;
     ml_mem64 240 (subst [in_ofs0,`ofs:num`]
                    `word_add csrc (word (6 + ofs)):int64`);
     ml_mem64 248 src; ml_mem64 256 `word_add csrc (word 14):int64`;
     ml_mem64 64 `v25:int64`; ml_mem64 72 `v26:int64`;
     `read X0 s = x0`]) in
  let bad = list_mk_conj
   [`read PC s = word(pc + 0x5444)`; mk_eq(`read X0 s`,in_err);
    `read X26 s = v26`] in
  let ms = subst [src,`a:int64`]
   `?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2 [a,LENGTH(st:byte list);
                                word_sub stackpointer (word 496),496]
                               [word_sub stackpointer (word 496),496]` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [mk_disj(mk_conj(`~(l = 0) /\ ~(EL (l - 1) (st:byte list) = word 0)`,good),
            mk_conj(`l = 0 \/ EL (l - 1) (st:byte list) = word 0`,bad));
    `read X25 s = v25`; ms]) in
  let frame =
   `MAYCHANGE [PC; X0; X10; X11; X12; X15; X16; X18; X21; X25; X26] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),16);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 224),40)]` in
  mk_small_goal
   [`pc:num`; `stackpointer:int64`; `csrc:int64`; `st:byte list`; `l:num`;
    `v25:int64`; `v26:int64`; `x0:int64`; `e:uarch_event list`]
   (ml_code_hyps @
    [`aligned 16 (stackpointer:int64)`;
     `LENGTH(st:byte list) = l /\ l < 2 EXP 16 /\
      val(csrc:int64) + 6 + l + 8 < 2 EXP 64`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word_add (csrc:int64) (word 6),LENGTH(st:byte list))`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word pc,32000)`])
   pre post frame;;

(*** Addresses as the simulator puts them, and the shift of the        ***)
(*** container from the last byte (with the missing bytes if short)    ***)

let IN_WORD_NEG = prove
 (`!a b k. k <= b /\ k <= 2 EXP 64
           ==> word(a + b + (2 EXP 64 - k)):int64 = word(a + (b - k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a + b + (2 EXP 64 - k) = (a + (b - k)) + 2 EXP 64`
  SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD; WORD_2EXP64; WORD_ADD_0]]);;

let IN_NORM_ADDR_RULE =
  CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                      ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) o
  REWRITE_RULE[WORD_ADD_0];;

let IN_ADDR_ASSOC = prove
 (`!(p:int64) a b. word_add (word_add p (word a)) (word b) =
                   word_add p (word (a + b))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let IN_SHIFT32 = prove
 (`!b:byte. ~(val b = 0)
            ==> word_sub (word (32 - bitsize (val b))) (word 23):int32 =
                word(huf_lastshift b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[huf_lastshift; WORD_CLZ_BITSIZE; DIMINDEX_8; GSYM VAL_EQ_0] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bitsize(val(b:byte)) <= 8` ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE] THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `32 - bitsize(val(b:byte)) = (8 - bitsize(val b) + 1) + 23`
  SUBST1_TAC THENL
   [UNDISCH_TAC `bitsize(val(b:byte)) <= 8` THEN ARITH_TAC;
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let IN_SHIFT64 = prove
 (`!b:byte. ~(val b = 0)
            ==> word_zx (word_sub (word (32 - bitsize (val b)))
                                  (word 23):int32):int64 =
                word(huf_lastshift b)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `b:byte` FA_SHIFT_REG) THEN
  ASM_REWRITE_TAC[SUB_0]);;

let IN_SHIFT_SHORT = prove
 (`!b:byte. ~(val b = 0)
            ==> !n. (32 - bitsize (val b) + n) - 23 = n + huf_lastshift b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[huf_lastshift; WORD_CLZ_BITSIZE; DIMINDEX_8; GSYM VAL_EQ_0] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bitsize(val(b:byte)) <= 8` MP_TAC THENL
   [REWRITE_TAC[BITSIZE_LE] THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ARITH_TAC]);;

let IN_SHIFT_SHORT32 = prove
 (`!b:byte n. ~(val b = 0) /\ n <= 56
              ==> word_sub (word (32 - bitsize (val b) + n)) (word 23):int32 =
                  word (n + huf_lastshift b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bitsize(val(b:byte)) <= 8` ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE] THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `32 - bitsize(val(b:byte)) + n = (n + huf_lastshift b) + 23`
  SUBST1_TAC THENL
   [REWRITE_TAC[huf_lastshift; WORD_CLZ_BITSIZE; DIMINDEX_8;
                GSYM VAL_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `bitsize(val(b:byte)) <= 8` THEN
    ARITH_TAC;
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let IN_SHIFT_SHORT64 = prove
 (`!b:byte n. ~(val b = 0) /\ n <= 56
              ==> word_zx (word_sub (word (32 - bitsize (val b) + n))
                                    (word 23):int32):int64 =
                  word (n + huf_lastshift b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[IN_SHIFT_SHORT32] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  MP_TAC(SPEC `b:byte` HUF_LASTSHIFT_BOUND) THEN DISCH_TAC THEN
  SUBGOAL_THEN `n + huf_lastshift b < 2 EXP 32 /\
                n + huf_lastshift b < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`n <= 56`; `huf_lastshift b <= 9`] THEN
    ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let WORD_MOD_SIZE_64 = prove
 (`!n. word(n MOD 2 EXP 64):int64 = word n`,
  REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE]);;

let WORD_MOD_SIZE_64N =
  CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) WORD_MOD_SIZE_64;;

(*** The value of a short stream of k bytes ***)

let IN_BYTELIST_LEMMA k =
  let st = `st:byte list` in
  let terms = map (fun i -> mk_comb(`val:byte->num`,
                    list_mk_icomb "EL" [mk_small_numeral i; st])) (0--(k-1)) in
  let rhs = end_itlist (fun a b -> mk_binop `(+):num->num->num` a
                          (mk_binop `( * ):num->num->num` `256` b)) terms in
  let rec suc_conv tm =
    if tm = `0` then REFL tm else (num_CONV THENC RAND_CONV suc_conv) tm in
  prove(mk_forall(st,mk_imp(mk_eq(`LENGTH(st:byte list)`,mk_small_numeral k),
                            mk_eq(`num_of_bytelist st`,rhs))),
    GEN_TAC THEN CONV_TAC(LAND_CONV(RAND_CONV suc_conv)) THEN
    REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[num_of_bytelist; EL_CONS] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES]);;

(*** The facts for the loads of a stream of l bytes at base, before the ***)
(*** load: the last byte (the address rewritten by eqth), the 8 bytes   ***)
(*** at l - 8 (rewritten by eqths) and the bytes of a short stream      ***)

let in_stream_fact base (asl,w) =
  let s = rand w in
  let bpat = subst [s,`s:armstate`; base,`b:int64`]
    `read (memory :> bytes(b,LENGTH(st:byte list))) s` in
  s,snd(find (fun (_,th) -> let t = concl th in
               is_eq t && lhs t = bpat) asl);;

let IN_LASTBYTE_TAC (base:term) (eqth:thm) : tactic =
  SUBGOAL_THEN `l - 1 < LENGTH(st:byte list)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`LENGTH(st:byte list) = l`; `~(l = 0)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  W(fun gl ->
    let s,bth = in_stream_fact base gl in
    let th8 = MP (ISPECL [base; `st:byte list`; `l - 1`; s]
                    READ_MEMORY_BYTES8_BYTELIST)
                 (CONJ bth (ASSUME `l - 1 < LENGTH(st:byte list)`)) in
    ASSUME_TAC(GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV)
                 [GSYM eqth] (IN_NORM_ADDR_RULE th8)));;

let IN_CONT_TAC (base:term) (eqths:thm list) : tactic =
  SUBGOAL_THEN `(l - 8) + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`LENGTH(st:byte list) = l`; `8 <= l`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  W(fun gl ->
    let s,bth = in_stream_fact base gl in
    let th64 = MP (ISPECL [base; `LENGTH(st:byte list)`; `num_of_bytelist st`;
                           `l - 8`; s] READ_MEMORY_BYTES64_SLICE)
                  (CONJ bth (ASSUME `(l - 8) + 8 <= LENGTH(st:byte list)`)) in
    ASSUME_TAC(GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV)
                 (map GSYM eqths) (IN_NORM_ADDR_RULE th64)));;

let IN_BYTES_TAC (base:term) k : tactic =
  fun (asl,w as gl) ->
    let s,bth = in_stream_fact base gl in
    let lth = snd(find (fun (_,th) -> let t = concl th in
                          is_eq t && lhs t = `LENGTH(st:byte list)`) asl) in
    let one i =
      let ith = EQT_ELIM(CONV_RULE(RAND_CONV NUM_REDUCE_CONV)
                  (REWRITE_CONV[lth] (mk_binop `(<):num->num->bool`
                     (mk_small_numeral i) `LENGTH(st:byte list)`))) in
      let th8 = MP (ISPECL [base; `st:byte list`; mk_small_numeral i; s]
                      READ_MEMORY_BYTES8_BYTELIST) (CONJ bth ith) in
      ASSUME_TAC(IN_NORM_ADDR_RULE th8) in
    MAP_EVERY one (0--(k-1)) gl;;

(*** The cases of the last byte of a short stream of k bytes ***)

let IN_LAST_CASES_TAC k : tactic =
  let b = list_mk_icomb "EL" [mk_small_numeral(k - 1); `st:byte list`] in
  ASM_CASES_TAC(mk_eq(b,`word 0:byte`)) THENL
   [ALL_TAC;
    SUBGOAL_THEN (mk_neg(mk_eq(mk_comb(`val:byte->num`,b),`0`))) ASSUME_TAC
    THENL [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC]];;

(*** The final state of a long stream and of a short stream ***)

let IN_SHIFT_RULE_TAC : tactic =
  let b = `EL (l - 1) (st:byte list)` in
  let nz = ASSUME `~(val(EL (l - 1) (st:byte list)) = 0)` in
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ADDR_ASSOC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC b IN_SHIFT64) nz;
                              MP (SPEC b IN_SHIFT32) nz]);;

let IN_SHORT_SHIFT_THMS k =
  let b = list_mk_icomb "EL" [mk_small_numeral(k - 1); `st:byte list`] in
  let n = mk_small_numeral(8 * (8 - k)) in
  let nz = ASSUME(mk_neg(mk_eq(mk_comb(`val:byte->num`,b),`0`))) in
  let nle = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<=):num->num->bool` n `56`)) in
  [MP (SPEC b IN_SHIFT_SHORT) nz;
   MP (SPECL [b; n] IN_SHIFT_SHORT32) (CONJ nz nle);
   MP (SPECL [b; n] IN_SHIFT_SHORT64) (CONJ nz nle)];;

let IN_SHORT_FIN_TAC k : tactic =
  let lth = ASSUME(mk_eq(`LENGTH(st:byte list)`,mk_small_numeral k)) in
  let ths = IN_SHORT_SHIFT_THMS k in
  RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; WORD_MOD_SIZE_64;
              WORD_MOD_SIZE_64N] THEN
  REWRITE_TAC[MP (SPEC `st:byte list` (IN_BYTELIST_LEMMA k)) lth] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(*** A whole init: base the start of the stream, lastq the address of  ***)
(*** the last byte as the simulator puts it (from ~(l = 0)), conteqs   ***)
(*** for the address of the container, evq for the addresses in the    ***)
(*** events, and the addresses of the loads, the test of the last byte ***)
(*** and the end                                                       ***)

type inspec =
 {ibase : term; ilastq : thm; iconteqs : thm list; ievq : thm list;
  ifirstq : thm list; ilast : int; icont : int; icbz : int; ishort : int;
  iend : int};;

(*** The first byte of a short stream at other addresses A, for the    ***)
(*** equations A = base in ifirstq (just before the load, at ishort)   ***)

let IN_FIRST_TAC (sp:inspec) : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let pat = subst [s,`s:armstate`; sp.ibase,`b:int64`]
      `read (memory :> bytes8 b) s = EL 0 (st:byte list)` in
    let th = snd(find (fun (_,th) -> concl th = pat) asl) in
    MAP_EVERY (fun eq ->
      ASSUME_TAC(GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [GSYM eq] th))
     sp.ifirstq);;

let IN_EVADDR_TAC (sp:inspec) : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE sp.ievq);;

let IN_LONG_TAC (sp:inspec) : tactic =
  ZSTD_SIM_UNTIL_TAC [sp.ilast] THEN IN_LASTBYTE_TAC sp.ibase sp.ilastq THEN
  ZSTD_SIM_UNTIL_TAC [sp.icont] THEN IN_CONT_TAC sp.ibase sp.iconteqs THEN
  ZSTD_SIM_UNTIL_TAC [sp.icbz] THEN
  ASM_CASES_TAC `EL (l - 1) (st:byte list) = word 0` THENL
   [ZSTD_SIM_UNTIL_TAC [0x5444] THEN IN_EVADDR_TAC sp THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(val(EL (l - 1) (st:byte list)) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    ZSTD_SIM_UNTIL_TAC [sp.iend] THEN IN_EVADDR_TAC sp THEN PUFF_FINAL_TAC THEN
    IN_SHIFT_RULE_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; NUM_REDUCE_CONV `2 EXP 64`] THEN
    ASM_REWRITE_TAC[]];;

let IN_SHORT_TAC (sp:inspec) k : tactic =
  IN_BYTES_TAC sp.ibase k THEN ZSTD_SIM_UNTIL_TAC [sp.ishort] THEN
  IN_FIRST_TAC sp THEN IN_LAST_CASES_TAC k THENL
   [ZSTD_SIM_UNTIL_TAC [0x5444] THEN IN_EVADDR_TAC sp THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[];
    ZSTD_SIM_UNTIL_TAC [sp.iend] THEN IN_EVADDR_TAC sp THEN PUFF_FINAL_TAC THEN
    IN_SHORT_FIN_TAC k];;

let IN_TAC (sp:inspec) : tactic =
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `l = 0` THENL
   [ZSTD_SIM_UNTIL_TAC [0x5444] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `8 <= l` THENL [IN_LONG_TAC sp; ALL_TAC] THEN
  SUBGOAL_THEN `l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(8 <= l)`; `~(l = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THENL
  map (IN_SHORT_TAC sp) (1--7);;

(*** Stream 1 ***)

let in1 =
  let nz = ASSUME `~(l = 0)` in
  let one = ARITH_RULE `~(l = 0) ==> 1 <= l /\ 1 <= 2 EXP 64` in
  let red = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) in
  {ibase = `word_add csrc (word 6):int64`;
   ilastq = MP (red(SPECL [`6`; `l:num`; `1`] IN_WORD_NEG)) (MP one nz);
   iconteqs = [];
   ievq = [MP (red(SPECL [`word_add csrc (word 6):int64`; `l:num`; `1`]
                          FA_ADDR_NEG)) (MP one nz)];
   ifirstq = []; ilast = 0x54d8; icont = 0x54f0; icbz = 0x54f8;
   ishort = 0x5a54; iend = 0x5508};;

let IN1_CORRECT = prove(in1_goal, IN_TAC in1);;

(*** The inits of streams 2, 3 and 4 (at 0x5508, 0x554c and 0x5594), as  ***)
(*** that of stream 1 but with the start p of the stream in a register,  ***)
(*** p = q + l' for the start q and the size l' of the stream before     ***)
(*** (the first byte of a short stream is loaded from there); on errors  ***)
(*** the registers saved in the frame are restored                       ***)

let in_win k =
  ml_mem64 k (subst [in_ofs0,`ofs:num`]
   `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64)
    :int64`);;

let in_struct k =
  [in_win k; ml_mem32 (k + 8) in_bc0;
   ml_mem64 (k + 16) (subst [in_ofs0,`ofs:num`]
                       `word_add p (word ofs):int64`);
   ml_mem64 (k + 24) `p:int64`;
   ml_mem64 (k + 32) `word_add p (word 8):int64`];;

let in_vars =
  [`pc:num`; `stackpointer:int64`; `p:int64`; `q:int64`; `st:byte list`;
   `l:num`; `l':num`; `v25:int64`; `v26:int64`; `v27:int64`; `v28:int64`;
   `x26:int64`; `x28:int64`; `x0:int64`; `e:uarch_event list`];;

let in_hyps =
  ml_code_hyps @
  [`aligned 16 (stackpointer:int64)`;
   `LENGTH(st:byte list) = l /\ l < 2 EXP 32 /\
    val(p:int64) + l + 8 < 2 EXP 64`;
   `word_add q (word l') = p:int64 /\ l' < 2 EXP 16`;
   `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                   (p:int64,LENGTH(st:byte list))`;
   `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                   (word pc,32000)`];;

let mk_in_goal ia preregs premem good bad common frame =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc`;
     mk_eq(`read PC s`,mk_comb(`word:num->int64`,
                         mk_binop `(+):num->num->num` `pc:num`
                           (mk_small_numeral ia)));
     `read SP s = word_sub stackpointer (word 496)`; preregs] @ premem @
    [`read (memory :> bytes(p,LENGTH(st:byte list))) s = num_of_bytelist st`;
     `read events s = e`])) in
  let ms =
   `?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2 [p,LENGTH(st:byte list);
                                word_sub stackpointer (word 496),496]
                               [word_sub stackpointer (word 496),496]` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   ([mk_disj(mk_conj(`~(l = 0) /\ ~(EL (l - 1) (st:byte list) = word 0)`,
                     list_mk_conj good),
             mk_conj(`l = 0 \/ EL (l - 1) (st:byte list) = word 0`,
                     list_mk_conj(`read PC s = word(pc + 0x5444)` ::
                                  mk_eq(`read X0 s`,in_err) :: bad)))] @
    common @ [ms])) in
  mk_small_goal in_vars in_hyps pre post frame;;

let in2_goal =
  mk_in_goal 0x5508
   `read X10 s = p /\ read X5 s = word l /\ read X13 s = word l /\
    read X11 s = q /\ read X2 s = word l' /\
    read X25 s = v25 /\ read X26 s = x26 /\ read X0 s = x0`
   [ml_mem64 64 `v25:int64`; ml_mem64 72 `v26:int64`]
   ([`read PC s = word(pc + 0x554c)`;
     `read X15 s = word_add p (word l) /\ read X26 s = x26 /\
      read X0 s = x0`;
     mk_eq(`read X2 s`,mk_comb(`word:num->int64`,in_bc0))] @
    in_struct 264 @ [ml_mem64 104 `word_add p (word 8):int64`])
   [`read X26 s = v26`]
   [`read X25 s = v25`]
   `MAYCHANGE [PC; X0; X2; X5; X12; X15; X25; X26] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 104),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 264),40)]`;;

let in3_goal =
  mk_in_goal 0x554c
   `read X15 s = p /\ read X17 s = word l /\ read X4 s = word l /\
    read X10 s = q /\ read X13 s = word l' /\
    read X25 s = v25 /\ read X26 s = x26 /\
    read X27 s = v27 /\ read X28 s = v28 /\ read X0 s = x0`
   [ml_mem64 64 `v25:int64`; ml_mem64 72 `v26:int64`]
   ([`read PC s = word(pc + 0x5594)`;
     `read X27 s = word_add p (word l) /\ read X26 s = x26 /\
      read X0 s = x0`;
     mk_eq(`read X17 s`,mk_comb(`word:num->int64`,in_bc0))] @
    in_struct 304 @
    [ml_mem64 128 `word_add p (word 8):int64`;
     ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`])
   [`read X26 s = v26 /\ read X27 s = v27`]
   [`read X25 s = v25 /\ read X28 s = v28`]
   `MAYCHANGE [PC; X0; X5; X12; X13; X17; X25; X26; X27; X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 80),16);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 128),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 304),40)]`;;

let in4_goal =
  mk_in_goal 0x5594
   `read X27 s = p /\ read X0 s = word l /\ read X3 s = word (l + 6) /\
    read X15 s = q /\ read X4 s = word l' /\
    read X25 s = v25 /\ read X26 s = x26 /\ read X28 s = x28`
   [ml_mem64 64 `v25:int64`; ml_mem64 72 `v26:int64`;
    ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`]
   ([`read PC s = word(pc + 0x55e0)`;
     `read X26 s = x26 /\ read X27 s = p /\ read X28 s = x28`] @
    in_struct 344 @ [ml_mem64 136 `word_add p (word 8):int64`])
   [`read X26 s = v26 /\ read X27 s = v27 /\ read X28 s = v28`]
   [`read X25 s = v25`]
   `MAYCHANGE [PC; X0; X3; X4; X5; X12; X25; X26; X27; X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 136),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 344),40)]`;;

(*** The proofs ***)

let in_neg k a =
  let nz = ASSUME `~(l = 0)` in
  let red = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) in
  let c = mk_conj(mk_binop `(<=):num->num->bool` k a,
                  mk_binop `(<=):num->num->bool` k `2 EXP 64`) in
  let cth = MP (ARITH_RULE(mk_imp(`~(l = 0)`,c))) nz in
  let fix = REWRITE_RULE[ARITH_RULE `(l + 6) - 7 = l - 1`] in
  fix(MP (red(SPECL [a; k] FA_WORD_NEG)) cth),
  (fun p -> fix(MP (red(SPECL [p; a; k] FA_ADDR_NEG)) cth));;

let IN_ZX_ADDR = prove
 (`!(q:int64) l' p.
        word_add q (word l') = p /\ l' < 2 EXP 16
        ==> word_add q (word_zx (word_zx (word l':int64):int32)) = p`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  SUBGOAL_THEN `l' < 2 EXP 32 /\ l' < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `l' < 2 EXP 16` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

let in_spec a last cont cbz short iend =
  let q,ev = if a = `l:num` then in_neg `1` a else in_neg `7` a in
  let zx = MP (SPECL [`q:int64`; `l':num`; `p:int64`] IN_ZX_ADDR)
              (CONJ (ASSUME `word_add q (word l') = p:int64`)
                    (ASSUME `l' < 2 EXP 16`)) in
  {ibase = `p:int64`; ilastq = q; iconteqs = []; ievq = [ev `p:int64`; zx];
   ifirstq = [zx]; ilast = last; icont = cont; icbz = cbz; ishort = short;
   iend = iend};;

let in2 = in_spec `l:num` 0x551c 0x5534 0x553c 0x5b00 0x554c;;
let in3 = in_spec `l:num` 0x5564 0x557c 0x5584 0x5ba4 0x5594;;
let in4 =
  let sp = in_spec `l + 6` 0x55a8 0x55c0 0x55c8 0x5c44 0x55e0
  and eq = ARITH_RULE `(l + 6) - 14 = l - 8` in
  {sp with iconteqs = [eq]; ievq = sp.ievq @ [eq]};;

let IN2_CORRECT = prove(in2_goal, IN_TAC in2);;
let IN3_CORRECT = prove(in3_goal, IN_TAC in3);;
let IN4_CORRECT = prove(in4_goal, IN_TAC in4);;

(* ------------------------------------------------------------------------- *)
(* The entry checks of the slow path at 0x5458.                              *)
(* ------------------------------------------------------------------------- *)

(*** The entry checks of the slow path (0x5458): n > 5, at least 10      ***)
(*** bytes, the first three streams within the block (the size of the   ***)
(*** fourth not wrapping) and opStart4 <= oend; the registers for the   ***)
(*** inits: the sizes, the starts of the outputs and the table header   ***)

let en_j k = list_mk_icomb "huf_jump" [`blk:byte list`; mk_small_numeral k];;

let en_l4 = `LENGTH(blk:byte list) - (6 + huf_jump blk 0 + huf_jump blk 1 +
                                      huf_jump blk 2)`;;

let en_ok = `5 < n /\ 9 < LENGTH(blk:byte list) /\
             6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2 <=
             LENGTH blk`;;

let en_goal =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x5458) /\
     read X19 s = dst /\ read X20 s = word n /\ read X18 s = src /\
     read X23 s = word(LENGTH(blk:byte list)) /\ read X22 s = dt`;
    `read (memory :> bytes(src,LENGTH(blk:byte list))) s =
     num_of_bytelist blk`;
    `read (memory :> bytes32 dt) s = dh`;
    `read events s = e`]) in
  let q = `(n + 3) DIV 4` in
  let good = list_mk_conj
   [`read PC s = word(pc + 0x54c0)`;
    mk_eq(`read X12 s`,mk_comb(`word:num->int64`,en_j 0));
    mk_eq(`read X2 s`,mk_comb(`word:num->int64`,en_j 0));
    mk_eq(`read X5 s`,mk_comb(`word:num->int64`,en_j 1));
    mk_eq(`read X13 s`,mk_comb(`word:num->int64`,en_j 1));
    mk_eq(`read X17 s`,mk_comb(`word:num->int64`,en_j 2));
    mk_eq(`read X4 s`,mk_comb(`word:num->int64`,en_j 2));
    mk_eq(`read X0 s`,mk_comb(`word:num->int64`,en_l4));
    mk_eq(`read X3 s`,mk_comb(`word:num->int64`,
                        mk_binop `(+):num->num->num` en_l4 `6`));
    `read X9 s = word_add dst (word n)`;
    subst [q,`q:num`]
     `read X7 s = word_add dst (word q) /\
      read X8 s = word_add dst (word (2 * q)) /\
      read X6 s = word_add dst (word (3 * q))`;
    `read X14 s = word_zx (dh:int32) /\ read X1 s = word 0`] in
  let bad = `read PC s = word(pc + 0x5444) /\
             read X0 s = word 18446744073709551596` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [mk_disj(mk_conj(en_ok,good),mk_conj(mk_neg en_ok,bad));
    `?e2. read events s = APPEND e2 e /\
          memaccess_inbounds e2 [src,LENGTH(blk:byte list); dt,4] []`]) in
  let frame =
   `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X12;
               X13; X14; X17] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` in
  mk_small_goal
   [`pc:num`; `dst:int64`; `n:num`; `src:int64`; `blk:byte list`;
    `dt:int64`; `dh:int32`; `e:uarch_event list`]
   (ml_code_hyps @
    [`val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64 /\
      val(dst:int64) + n < 2 EXP 64 /\ n < 2 EXP 28`])
   pre post frame;;

(*** The flags of the ccmp with 9, the jump table, the output pointers ***)
(*** and the size of the fourth stream, wrapped or not                 ***)

let EN_SUB_FLAG = prove
 (`!b k. b < 2 EXP 64 /\ k < 2 EXP 64
         ==> ((&b:int) - &k = &(val(word_sub (word b) (word k):int64)) <=>
              k <= b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ASM_CASES_TAC `k <= b:num` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB];
    SUBGOAL_THEN `k <= 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN INT_ARITH_TAC]);;

let EN_SUB3_WRAP = prove
 (`!x a b c. a + b + c <= x + 2 EXP 64
             ==> word_sub (word_sub (word_sub (word x) (word a)) (word b))
                          (word c):int64 = word((x + 2 EXP 64) - (a + b + c))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN
  REWRITE_TAC[WORD_ADD; WORD_2EXP64] THEN CONV_TAC WORD_RULE);;

let EN_CCMP_TAC : tactic =
  SUBGOAL_THEN `LENGTH(blk:byte list) < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC [1;2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`LENGTH(blk:byte list)`; `9`]
    EN_SUB_FLAG) (CONJ (ASSUME `LENGTH(blk:byte list) < 2 EXP 64`)
                       (ARITH_RULE `9 < 2 EXP 64`))]);;

let EN_JUMP_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let bpat = subst [s,`s:armstate`]
      `read (memory :> bytes(src,LENGTH(blk:byte list))) s` in
    let bth = snd(find (fun (_,th) -> let t = concl th in
                          is_eq t && lhs t = bpat) asl) in
    let lth = ASSUME `9 < LENGTH(blk:byte list)` in
    let arith t = MP (INST [`LENGTH(blk:byte list)`,`n:num`] (ARITH_RULE t))
                     lth in
    let one k =
      let ofs = mk_small_numeral(2 * k) and kk = mk_small_numeral k in
      let c1 = arith(subst [ofs,`o2:num`] `9 < n ==> o2 + 2 <= n`) in
      let r = MP (SPECL [`src:int64`; `LENGTH(blk:byte list)`;
                         `num_of_bytelist blk`; ofs; s]
                    READ_MEMORY_BYTES16_SLICE) (CONJ bth c1) in
      let c2 = arith(subst [kk,`k:num`] `9 < n ==> 2 * k + 2 <= n`) in
      let j = MP (SPECL [`blk:byte list`; kk] HUF_JUMP_NUM) c2 in
      let r' = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) r
      and j' = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) j in
      REWRITE_RULE[j'; WORD_ADD_0] r' in
    (MAP_EVERY (ASSUME_TAC o one) [0;1;2] THEN
     MAP_EVERY (fun k ->
       let kk = mk_small_numeral k in
       let j = mk_var("j"^string_of_int k,`:num`) in
       ASSUME_TAC(SPECL [`blk:byte list`; kk] HUF_JUMP_BOUND) THEN
       ABBREV_TAC (mk_eq(j,list_mk_icomb "huf_jump" [`blk:byte list`; kk])))
      [0;1;2]) gl;;

let EN_OPS_TAC : tactic =
  ABBREV_TAC `q = (n + 3) DIV 4` THEN
  FA_STATE_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
    ARITH_RULE `q + q = 2 * q`; ARITH_RULE `q + 2 * q = 3 * q`] THEN
  SUBGOAL_THEN `3 * q <= n` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `5 < n` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`dst:int64`; `3 * q`] VAL_WORD_ADD_NOWRAP) THEN
  MP_TAC(SPECL [`dst:int64`; `n:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `val(dst:int64) + n < 2 EXP 64` THEN ARITH_TAC;
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`val(dst:int64) + n < 2 EXP 64`; `3 * q <= n`] THEN
    ARITH_TAC;
    DISCH_TAC];;

let EN_NOWRAP_TAC : tactic =
  let c = `6 + j0 + j1 + j2 <= LENGTH(blk:byte list)` in
  FA_STATE_REWRITE_TAC[MP (SPECL [`LENGTH(blk:byte list)`; `j2:num`;
                                  `j1 + j0:num`] FA_SUB_SUB)
    (MP (ARITH_RULE(mk_imp(c,`j2 + j1 + j0 <= LENGTH(blk:byte list)`)))
        (ASSUME c))] THEN
  ABBREV_TAC `l4 = LENGTH(blk:byte list) - (6 + j0 + j1 + j2)` THEN
  SUBGOAL_THEN `LENGTH(blk:byte list) - (j2 + j1 + j0) = l4 + 6 /\
                l4 <= LENGTH blk` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`LENGTH(blk:byte list) - (6 + j0 + j1 + j2) = l4`; c] THEN ARITH_TAC;
    ALL_TAC] THEN
  FA_STATE_REWRITE_TAC
   [ASSUME `LENGTH(blk:byte list) - (j2 + j1 + j0) = l4 + 6`] THEN
  ZSTD_SIM_UNTIL_TAC [0x54a4] THEN FA_STATE_REWRITE_TAC[ADD_SUB] THEN
  SUBGOAL_THEN `l4 < 2 EXP 64 /\ LENGTH(blk:byte list) < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`l4 <= LENGTH(blk:byte list)`;
      `val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_SIM_UNTIL_TAC [0x54c0] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let EN_WRAP_TAC : tactic =
  ZSTD_SIM_UNTIL_TAC [0x54a0] THEN
  MP_TAC(SPECL [`LENGTH(blk:byte list)`; `j2:num`; `j1 + j0:num`; `6`]
    EN_SUB3_WRAP) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`j0 < 65536`; `j1 < 65536`; `j2 < 65536`] THEN
    ARITH_TAC;
    DISCH_THEN(fun th -> FA_STATE_REWRITE_TAC[th])] THEN
  ABBREV_TAC
   `w4 = (LENGTH(blk:byte list) + 2 EXP 64) - (j2 + (j1 + j0) + 6)` THEN
  SUBGOAL_THEN `w4 < 2 EXP 64 /\ LENGTH(blk:byte list) < w4 /\
                LENGTH blk < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w4" THEN
    MAP_EVERY UNDISCH_TAC
     [`~(6 + j0 + j1 + j2 <= LENGTH(blk:byte list))`;
      `val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`;
      `j0 < 65536`; `j1 < 65536`; `j2 < 65536`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_SIM_UNTIL_TAC [0x5444] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(6 + j0 + j1 + j2 <= LENGTH(blk:byte list))` THEN ARITH_TAC;;

let EN_CORRECT = prove
 (en_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `5 < n` THENL
   [ALL_TAC;
    ZSTD_SIM_UNTIL_TAC [0x5444] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]]
  THEN EN_CCMP_TAC THEN
  ASM_CASES_TAC `9 < LENGTH(blk:byte list)` THENL
   [ALL_TAC;
    ZSTD_SIM_UNTIL_TAC [0x5444] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]]
  THEN EN_JUMP_TAC THEN ZSTD_SIM_UNTIL_TAC [0x5498] THEN EN_OPS_TAC THEN
  ASM_CASES_TAC `6 + j0 + j1 + j2 <= LENGTH(blk:byte list)` THENL
   [EN_NOWRAP_TAC; EN_WRAP_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The setup of the main loop at 0x55e0.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The setup of the main loop at 0x55e0: the loop (0x56fc) if the      ***)
(*** fourth segment has at least 8 bytes, with the registers of the     ***)
(*** loop from BIT_DStream in the frame and the slots of the frame, and ***)
(*** otherwise straight to the order check (0x5ce4)                     ***)

let st_goal =
  let ss = map (fun k -> mk_var("s"^string_of_int k,`:int64`)) [1;2;3;4]
  and cs = map (fun k -> mk_var("c"^string_of_int k,`:int64`)) [1;2;3;4]
  and ps = map (fun k -> mk_var("p"^string_of_int k,`:int64`)) [1;2;3;4] in
  let add8 v = mk_comb(mk_comb(`word_add:int64->int64->int64`,v),
                       `word 8:int64`) in
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x55e0) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X9 s = word_add dst (word n) /\
      read X6 s = word_add dst (word (3 * q)) /\
      read X7 s = word_add dst (word q) /\
      read X8 s = word_add dst (word (2 * q)) /\
      read X20 s = word n /\ read X22 s = dt /\
      read X14 s = word_zx (dh:int32) /\
      read X11 s = s1 /\ read X10 s = s2 /\ read X15 s = s3 /\
      read X27 s = s4`] @
    List.concat (map (fun k ->
      let a = 224 + 40 * (k - 1) in
      [ml_mem64 a (el (k - 1) cs); ml_mem64 (a + 16) (el (k - 1) ps)])
     [1;2;3;4]) @
    [ml_mem32 352 `b4:num`;
     ml_mem64 104 (add8 (el 1 ss)); ml_mem64 128 (add8 (el 2 ss));
     ml_mem64 136 (add8 (el 3 ss));
     `read events s = e`])) in
  let loop = list_mk_conj
   ([`read PC s = word(pc + 0x56fc)`;
     `read X3 s = word(64 - tl) /\ read X5 s = word_add dt (word 4)`;
     `read X22 s = c1 /\ read X23 s = p1 /\
      read X21 s = c2 /\ read X24 s = p2 /\
      read X30 s = c3 /\ read X25 s = p3 /\
      read X18 s = c4 /\ read X11 s = p4 /\ read X0 s = word b4`;
     `read X13 s = word_add dst (word q) /\
      read X14 s = word_add dst (word (2 * q)) /\
      read X12 s = word_add dst (word (3 * q))`;
     `read X20 s = word_add s2 (word 8) /\
      read X27 s = word_add s3 (word 8) /\
      read X10 s = word_add s4 (word 8) /\ read X15 s = word 0`;
     ml_mem64 112 `word_add dst (word (n - 3)):int64`;
     ml_mem32 124 `0`; ml_mem32 184 `0`;
     ml_mem64 144 `word_add dst (word n):int64`; ml_mem64 152 `s1:int64`;
     ml_mem64 160 `word_add dst (word q):int64`;
     ml_mem64 168 `word_add dst (word (2 * q)):int64`;
     ml_mem64 176 `word_add dst (word (3 * q)):int64`;
     ml_mem32 188 `tl:num`; ml_mem64 192 `word n:int64`;
     ml_mem64 200 `s2:int64`; ml_mem64 208 `s3:int64`;
     ml_mem64 216 `s4:int64`]) in
  let skip = list_mk_conj
   [`read PC s = word(pc + 0x5ce4)`;
    `read X5 s = word_add dt (word 4) /\ read X23 s = word tl`;
    `read X11 s = s1 /\ read X10 s = s2 /\ read X15 s = s3 /\
     read X27 s = s4 /\ read X20 s = word n`;
    `read X13 s = word_add dst (word q) /\
     read X14 s = word_add dst (word (2 * q)) /\
     read X12 s = word_add dst (word (3 * q))`;
    ml_mem64 112 `word_add dst (word (n - 3)):int64`] in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [mk_disj(mk_conj(`8 <= n - 3 * q`,loop),mk_conj(`n - 3 * q < 8`,skip));
    `?e2. read events s = APPEND e2 e /\
          memaccess_inbounds e2 [word_sub stackpointer (word 496),496]
                                [word_sub stackpointer (word 496),496]`]) in
  let frame =
   `MAYCHANGE [PC; X0; X3; X4; X5; X10; X11; X12; X13; X14; X15; X18; X20;
               X21; X22; X23; X24; X25; X27; X28; X30] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 112),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 124),4);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 144),80)]` in
  mk_small_goal
   ([`pc:num`; `stackpointer:int64`; `dst:int64`; `n:num`; `q:num`;
     `dt:int64`; `dh:int32`; `tl:num`; `b4:num`] @ ss @ cs @ ps @
    [`e:uarch_event list`])
   (ml_code_hyps @
    [`aligned 16 (stackpointer:int64)`;
     `val(dst:int64) + n < 2 EXP 64 /\ 3 * q <= n /\ 5 < n /\
      n < 2 EXP 28 /\ b4 < 2 EXP 32`;
     `val(word_subword (dh:int32) (16,8):byte) = tl /\ 1 <= tl /\ tl <= 12`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word pc,32000)`])
   pre post frame;;

(*** The proof ***)

let ST_SUB_ADD = prove
 (`!(p:int64) a b. b <= a
                   ==> word_sub (word_add p (word a)) (word_add p (word b)) =
                       word (a - b)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let ST_SHIFT_LEMMA = prove
 (`!tl. tl < 13
        ==> 1 <= tl
            ==> word_zx (word_and (word_sub (word 0) (word tl))
                                  (word 63):int32):int64 = word (64 - tl)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

let ST_ZX32 = prove
 (`!b. b < 2 EXP 32 ==> word_zx (word b:int32):int64 = word b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  SUBGOAL_THEN `b < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `b < 2 EXP 32` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

let ST_SUB3 = prove
 (`!(p:int64) n. 3 <= n
                 ==> word_sub (word_add p (word n)) (word 3) =
                     word_add p (word (n - 3))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let ST_FIN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`dst:int64`; `n:num`] ST_SUB3)
    (MP (ARITH_RULE `5 < n ==> 3 <= n`) (ASSUME `5 < n`))]) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let ST_VAL_TAC : tactic =
  MP_TAC(SPECL [`dst:int64`; `n:num`; `3`] VAL_WORD_SUB_ADD_NOWRAP) THEN
  MP_TAC(SPECL [`dst:int64`; `3 * q`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`val(dst:int64) + n < 2 EXP 64`; `3 * q <= n`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`val(dst:int64) + n < 2 EXP 64`;
                           `8 <= n - 3 * q`] THEN ARITH_TAC;
    DISCH_TAC];;

let ST_CORRECT = prove
 (st_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ZSTD_SIM_UNTIL_TAC [0x55f4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FA_UBFX]) THEN
  FA_STATE_REWRITE_TAC
    [ASSUME `val(word_subword (dh:int32) (16,8):byte) = tl`] THEN
  FA_STATE_REWRITE_TAC[MP (SPECL [`dst:int64`; `n:num`; `3 * q`] ST_SUB_ADD)
    (ASSUME `3 * q <= n`)] THEN
  ASM_CASES_TAC `8 <= n - 3 * q` THENL
   [ZSTD_SIM_UNTIL_TAC [0x55fc] THEN ST_VAL_TAC THEN
    ZSTD_SIM_UNTIL_TAC [0x56fc] THEN
    FA_STATE_REWRITE_TAC
     [MP (SPEC `b4:num` ST_ZX32) (ASSUME `b4 < 2 EXP 32`);
      MP (MP (SPEC `tl:num` ST_SHIFT_LEMMA)
             (MP (ARITH_RULE `tl <= 12 ==> tl < 13`) (ASSUME `tl <= 12`)))
         (ASSUME `1 <= tl`)] THEN
    ST_FIN_TAC;
    ZSTD_SIM_UNTIL_TAC [0x5ce4] THEN ST_FIN_TAC THEN
    UNDISCH_TAC `~(8 <= n - 3 * q)` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The rest, from the check of the order of the outputs at 0x5ce4 to 0x5444: *)
(* the tails and the end checks.                                             *)
(* ------------------------------------------------------------------------- *)

(*** The rest of the slow path, from the order check (0x5ce4) to 0x5444:  ***)
(*** the tails again with the state of a stream before as huf_dstate and  ***)
(*** after as huf_fstate (with the bytes out and the pointer as values),  ***)
(*** so that big steps with them need no case splits                     ***)

let huf_fstate = new_definition
 `huf_fstate ws ml (st:byte list) r L ofs bc (m:num) (p:int64) src <=>
    (ofs = 0 \/ ofs + 8 <= LENGTH st) /\
    (SND(SND(huf_decode ws ml st r L)) /\
     FST(SND(huf_decode ws ml st r L)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
     m = num_of_bytelist(FST(huf_decode ws ml st r L)) /\
     p = word_add src (word ofs) \/
     ~SND(SND(huf_decode ws ml st r L)) /\ ofs = 0 /\ 64 < bc /\
     bc <= 64 + 12 * L)`;;

let RS_ENSURES_WEAKEN = prove
 (`!P P' Q Q' (C:armstate->armstate->bool).
        (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s)
        ==> ensures arm P Q C ==> ensures arm P' Q' C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `P:armstate->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC `Q:armstate->bool` THEN ASM_REWRITE_TAC[]);;

let rs_tail_entry spec = with_memsafe tail_rr tail_wr
 (mk_abs(`s:armstate`,list_mk_conj
  ([`read PC s = word(pc + a_entry)`; tail_common;
    mk_conj(`read (r_op:tailreg) s = word_add op (word jj)`,spec.e_regs)] @
   spec.e_mems @
   [tail_cont_mem; tail_bc_mem; tail_ptr_mem;
    `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
    `read (memory :> bytes(op,jj)) s = num_of_bytelist out /\
     huf_dstate ws ml st r jj ofs bc out`])));;

(*** (without the code: a big step must not see it in the callee's post, ***)
(*** or it takes that for the code before the step)                      ***)

let rs_tail_common = list_mk_conj(tl(conjuncts tail_common));;

let rs_tail_post = with_memsafe tail_rr tail_wr (mk_abs(`s:armstate`,
  list_mk_exists([`ofs:num`; `bc:num`; `m:num`; `p:int64`],list_mk_conj
   [`read PC s = word(pc + a_post)`; rs_tail_common; tail_bc_mem;
    `read (memory :> bytes(op,L)) s = m /\ read (r_ptr:tailreg) s = p /\
     huf_fstate ws ml st r L ofs bc m p src`])));;

let rs_tail_goal spec =
  mk_tail_goal spec [`jj:num`; `ofs:num`; `bc:num`; `out:byte list`]
    (rs_tail_entry spec) rs_tail_post;;

let rs_has_hd t =
  can (find_term (fun u -> try fst(dest_const u) = "huf_decode"
                           with Failure _ -> false)) t;;

let RS_TAIL_TAC (th:thm) : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL th)) THEN
  MATCH_MP_TAC RS_ENSURES_WEAKEN THEN CONJ_TAC THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THENL
   [DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "huf_dstate"
      with Failure _ -> false)) THEN
    REWRITE_TAC[huf_dstate] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `ofs':num` (X_CHOOSE_THEN `bc':num`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`ofs':num`; `bc':num`] THEN
    W(fun (asl,w) ->
      let v1,b1 = dest_exists w in
      let v2,b2 = dest_exists b1 in
      let cs = conjuncts b2 in
      let mt = lhs(find (fun t -> is_eq t && rhs t = v1) cs)
      and pt = lhs(find (fun t -> is_eq t && rhs t = v2) cs) in
      MAP_EVERY EXISTS_TAC [mt; pt]) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
      check (fun th -> is_disj(concl th) && rs_has_hd(concl th))) THEN
    ASM_REWRITE_TAC[huf_fstate]];;

let RS_TAIL1 = prove(rs_tail_goal tail1, RS_TAIL_TAC TAIL1_ENTRY);;
let RS_TAIL2 = prove(rs_tail_goal tail2, RS_TAIL_TAC TAIL2_ENTRY);;
let RS_TAIL3 = prove(rs_tail_goal tail3, RS_TAIL_TAC TAIL3_ENTRY);;
let RS_TAIL4 = prove(rs_tail_goal tail4, RS_TAIL_TAC TAIL4_ENTRY);;

(*** The goal of the rest: from 0x5ce4, with each stream after j bytes in ***)
(*** a good or a bad state (huf_dstate), to 0x5444 with the result n     ***)
(*** exactly when each stream decodes its L bytes ending at position 0,  ***)
(*** and then the bytes out                                              ***)

let rs_exit1 = list_mk_conj
 (ml_struct @
  [subst [tail_spv `s_b:num`,`a:int64`]
    `read (memory :> bytes32 a) s = word bc`;
   `read (r_op:tailreg) s = word_add op (word j) /\
    read (memory :> bytes(src,LENGTH(st:byte list))) s =
    num_of_bytelist st /\
    read (memory :> bytes(op,j)) s = num_of_bytelist out /\
    LENGTH(out:byte list) = j /\
    huf_dstate ws ml st r j ofs bc out /\
    (ofs = 0 \/ ofs + 8 <= LENGTH st) /\ j <= L`]);;

let rs_ok k =
  ml_rinst (el (k - 1) ml_regs)
   `SND(SND(huf_decode ws ml (st:byte list) r L)) /\
    FST(SND(huf_decode ws ml st r L)) = 0`;;

let rs_allok = list_mk_conj(map rs_ok [1;2;3;4]);;

let rs_mem k =
  ml_rinst (el (k - 1) ml_regs)
   `read (memory :> bytes(op,L)) s =
    num_of_bytelist(FST(huf_decode ws ml (st:byte list) r L))`;;

let rs_saved =
 [ml_mem64 64 `v25:int64`; ml_mem64 72 `v26:int64`;
  ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`];;

let rs_pre =
  let oend = mk_comb(mk_comb(`word_add:int64->int64->int64`,ml_ov 4),
                     mk_comb(`word:num->int64`,ml_Lv 4)) in
  with_memsafe ml_lrr ml_lwr (mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x5ce4) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X5 s = tbl /\
      read (memory :> bytes(tbl,2 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable ws ml tl)`;
     mk_eq(`read X9 s`,oend);
     mk_eq(`read X11 s`,ml_sv 1); mk_eq(`read X7 s`,ml_ov 2);
     mk_eq(`read X8 s`,ml_ov 3); mk_eq(`read X6 s`,ml_ov 4);
     `read X20 s = word n`; mk_eq(`read X10 s`,ml_sv 2);
     mk_eq(`read X15 s`,ml_sv 3); mk_eq(`read X27 s`,ml_sv 4);
     `read X23 s = word tl`;
     mk_eq(`read X16 s`,mk_comb(mk_comb(`word_add:int64->int64->int64`,
                                         ml_sv 1),`word 8:int64`))] @
    [el 0 ml_slots; el 1 ml_slots; el 2 ml_slots; el 3 ml_slots] @
    rs_saved @
    map (fun m -> ml_rinst m rs_exit1) ml_regs)));;

let rs_post = with_memsafe ml_lrr ml_lwr (mk_abs(`s:armstate`,list_mk_conj
  [`read PC s = word(pc + 0x5444)`;
   mk_eq(`read X0 s`,mk_cond(rs_allok,`word n:int64`,
                             `word 18446744073709551596:int64`));
   mk_imp(rs_allok,list_mk_conj(map rs_mem [1;2;3;4]));
   `read X25 s = v25 /\ read X26 s = v26 /\
    read X27 s = v27 /\ read X28 s = v28`]));;

let rs_frame =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X6; X7; X8; X12; X13; X14; X16; X17;
             X18; X19; X21; X22; X24; X25; X26; X27; X28; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op1,L1); memory :> bytes(op2,L2);
             memory :> bytes(op3,L3); memory :> bytes(op4,L4);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 224),160)]`;;

let rs_vars =
  [`pc:num`; `stackpointer:int64`; `tbl:int64`; `tl:num`; `ws:num list`;
   `ml:num`; `n:num`; `j:num`; `v25:int64`; `v26:int64`; `v27:int64`;
   `v28:int64`; `e:uarch_event list`] @
  List.concat (map ml_allvars [1;2;3;4]);;

let rs_goal =
  let tm = mk_imp(list_mk_conj
                   (ml_hyps @
                    [`word_add op1 (word L1) = op2:int64 /\
                      word_add op2 (word L2) = op3:int64 /\
                      word_add op3 (word L3) = op4:int64`]),
                  list_mk_icomb "ensures"
                    [`arm`; rs_pre; rs_post; rs_frame]) in
  let fvs = frees tm in
  (match subtract fvs rs_vars with
     [] -> ()
   | v::_ -> failwith ("rs_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) rs_vars,tm);;

(*** The end of a stream from its final state ***)

let HUF_FSTATE_END = prove
 (`!ws ml (st:byte list) r L ofs bc m p src.
        huf_fstate ws ml st r L ofs bc m p src /\
        val src + LENGTH st < 2 EXP 64
        ==> ((p = src /\ bc = 64) <=>
             SND(SND(huf_decode ws ml st r L)) /\
             FST(SND(huf_decode ws ml st r L)) = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_fstate] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
                             ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `word_add src (word ofs) = (src:int64) <=> ofs = 0`
    SUBST1_TAC THENL
     [REWRITE_TAC[WORD_RULE `word_add x y = x <=> y = word 0`] THEN
      REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      MATCH_MP_TAC(MESON[] `x = y ==> (x = 0 <=> y = 0)`) THEN
      MATCH_MP_TAC MOD_LT THEN
      MAP_EVERY UNDISCH_TAC
       [`ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;
        `val(src:int64) + LENGTH(st:byte list) < 2 EXP 64`] THEN
      ARITH_TAC;
      UNDISCH_TAC `bc <= 64` THEN ARITH_TAC];
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN
    UNDISCH_TAC `64 < bc` THEN ARITH_TAC]);;

let HUF_FSTATE_MEM = prove
 (`!ws ml (st:byte list) r L ofs bc m p src.
        huf_fstate ws ml st r L ofs bc m p src /\
        SND(SND(huf_decode ws ml st r L))
        ==> m = num_of_bytelist(FST(huf_decode ws ml st r L))`,
  REWRITE_TAC[huf_fstate] THEN MESON_TAC[]);;

let HUF_FSTATE_BC = prove
 (`!ws ml (st:byte list) r L ofs bc m p src.
        huf_fstate ws ml st r L ofs bc m p src /\ L < 2 EXP 28
        ==> bc < 2 EXP 32`,
  REWRITE_TAC[huf_fstate] THEN ARITH_TAC);;

(*** The proof: the order check, the tails and the end checks by big steps ***)

let RS_ORDER_FACTS_TAC : tactic =
  MAP_EVERY (fun (a,b,c) ->
    let la = mk_var("L"^string_of_int a,`:num`) in
    let oa = mk_var("op"^string_of_int a,`:int64`)
    and ob = mk_var("op"^string_of_int b,`:int64`) in
    let lt = mk_binop `(<):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,oa))
                  la) `2 EXP 64` in
    let eqab = mk_eq(list_mk_icomb "word_add"
                       [oa; mk_comb(`word:num->int64`,la)],ob) in
    let th1 = MP (SPECL [oa; la] VAL_WORD_ADD_NOWRAP) (ASSUME lt) in
    let th1' = REWRITE_RULE[ASSUME eqab] th1 in
    let ltj = mk_binop `(<):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,oa))
                  `j:num`) `2 EXP 64` in
    ASSUME_TAC th1' THEN
    SUBGOAL_THEN ltj ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [lt; `j <= L4`; c] THEN ARITH_TAC; ALL_TAC] THEN
    ASSUME_TAC(MP (SPECL [oa; `j:num`] VAL_WORD_ADD_NOWRAP) (ASSUME ltj)))
   [1,2,`L4 <= L1`; 2,3,`L4 <= L2`; 3,4,`L4 <= L3`];;

(*** The order check, with the ends of the first three outputs as        ***)
(*** op_k + L_k (with the equations to op_k+1 out of the way)             ***)

let RS_ORDER_TAC : tactic =
  let hs = [`word_add op1 (word L1) = op2:int64`;
            `word_add op2 (word L2) = op3:int64`;
            `word_add op3 (word L3) = op4:int64`]
  and regs = [`X7`; `X8`; `X6`] in
  W(fun (asl,w) ->
    let s = rand w in
    let hths = map (fun h -> snd(find (fun (_,th) -> concl th = h) asl)) hs in
    let rule th =
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
          when s' = s && mem c regs ->
          let k = index c regs in
          GEN_REWRITE_RULE RAND_CONV [GSYM(el k hths)] th
      | _ -> th in
    DISCARD_ASSUMPTIONS_TAC (fun th -> mem (concl th) hs) THEN
    RULE_ASSUM_TAC rule THEN
    ZSTD_SIM_UNTIL_TAC [0x5d00] THEN MAP_EVERY ASSUME_TAC hths);;

(*** The simulation turns 2 EXP 64 into a numeral, which big steps miss ***)

let RS_2EXP64_TAC : tactic =
  let n64 = `18446744073709551616` in
  let rule = REWRITE_RULE[SYM(NUM_REDUCE_CONV `2 EXP 64`)] in
  RULE_ASSUM_TAC(fun th ->
    let t = concl th in
    if can (find_term ((=) n64)) t &&
       not(can (find_term ((=) `events`)) t) && not(maychange_term t)
    then rule th else th);;

let rs_fstate k asl =
  let st = ml_var k ("st",`:byte list`) in
  snd(find (fun (_,th) ->
    let t = concl th in
    try fst(dest_const(fst(strip_comb t))) = "huf_fstate" &&
        el 2 (snd(strip_comb t)) = st
    with Failure _ -> false) asl);;

let RS_ENDCHK_TAC : tactic =
  W(fun (asl,w) ->
    let fths = map (fun k -> rs_fstate k asl) [1;2;3;4] in
    let args k = snd(strip_comb(concl(el (k - 1) fths))) in
    let bcs = map (fun k -> el 6 (args k)) [1;2;3;4]
    and ps = map (fun k -> el 8 (args k)) [1;2;3;4] in
    MAP_EVERY (fun k ->
      let lk = subst [ml_Lv k,`L:num`] `L < 2 EXP 28` in
      ASSUME_TAC(MATCH_MP HUF_FSTATE_BC
                   (CONJ (el (k - 1) fths) (ASSUME lk)))) [1;2;3;4] THEN
    ML_BIGSTEP_TAC ENDCHK_CORRECT
     (map2 (fun k p -> ("p"^string_of_int k,p)) [1;2;3;4] ps @
      map2 (fun k b -> ("b"^string_of_int k,b)) [1;2;3;4] bcs @
      map (fun k -> ("a"^string_of_int k,ml_sv k)) [1;2;3;4]));;

(*** The result from the end checks, and the bytes out ***)

let RS_FINAL_TAC : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let fths = map (fun k -> rs_fstate k asl) [1;2;3;4] in
    let lt k =
      let src = ml_sv k and st = ml_var k ("st",`:byte list`) in
      let a = subst [src,`src:int64`; st,`st:byte list`]
                `val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`
      and c = subst [src,`src:int64`; st,`st:byte list`]
                `val(src:int64) + LENGTH(st:byte list) < 2 EXP 64` in
      MP (ARITH_RULE(mk_imp(a,c))) (ASSUME a) in
    let ends = map (fun k ->
      MATCH_MP HUF_FSTATE_END (CONJ (el (k - 1) fths) (lt k))) [1;2;3;4] in
    let x0 = snd(find (fun (_,th) -> let t = concl th in
                 is_eq t && lhs t = list_mk_icomb "read" [`X0`; s]) asl) in
    let cond = fst(dest_cond(rhs(concl x0))) in
    let eqth = itlist PROVE_HYP ends
      (UNDISCH_ALL(TAUT(itlist (curry mk_imp) (map concl ends)
                              (mk_eq(cond,rs_allok))))) in
    let mems = map (fun th -> MATCH_MP (REWRITE_RULE[IMP_CONJ]
                       (SPEC_ALL HUF_FSTATE_MEM)) th) fths in
    ASSUME_TAC eqth THEN MAP_EVERY ASSUME_TAC mems) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN REPEAT CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;

let RS_CORRECT = prove
 (rs_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RS_ORDER_FACTS_TAC THEN
  RS_ORDER_TAC THEN RS_2EXP64_TAC THEN
  MAP_EVERY (fun (k,th) ->
    RS_2EXP64_TAC THEN ML_BIGSTEP_TAC th (ml_alist k @ [("jj",`j:num`)]))
   [1,RS_TAIL1; 2,RS_TAIL2; 3,RS_TAIL3; 4,RS_TAIL4] THEN
  RS_ENDCHK_TAC THEN RS_FINAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The back of the slow path, from the setup of the main loop at 0x55e0 to   *)
(* 0x5444.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*** The main loop from its first iteration (j = 0, all flags 0), with    ***)
(*** the disjunctions of its exit folded into definitions and without     ***)
(*** the code in its post, for big steps                                 ***)

let ml_ofsok = new_definition
 `ml_ofsok ofs (st:byte list) <=> ofs = 0 \/ ofs + 8 <= LENGTH st`;;

let ml_flagok = new_definition
 `ml_flagok f ofs ofs0 <=> (f = 0 \/ f = 1) /\ (f = 0 ==> ofs = ofs0)`;;

let ml_bc0 k = mk_var("bc0"^string_of_int k,`:num`);;

let ml_loop2w_pre =
  let sub = List.concat (map (fun k ->
              [ml_o0 k,ml_var k ("ofs",`:num`);
               ml_bc0 k,ml_var k ("bc",`:num`)]) [1;2;3;4]) @
            [`0`,`f:num`] in
  with_memsafe ml_lrr ml_lwr
   (mk_abs(`s:armstate`,vsubst sub (ml_inv_body2 `0`)));;

let ml_lexit1F =
  subst [`ml_ofsok ofs (st:byte list)`,
         `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`] ml_lexit1;;

let ml_lexit_commonF =
  list_mk_conj
   ([`read SP s = word_sub stackpointer (word 496) /\
      read X26 s = word bc1 /\ read X2 s = word bc2 /\ read X17 s = word bc3 /\
      read X1 s = word f1`;
     ml_mem32 184 `f2:num`; ml_mem32 124 `f3:num`] @
    map (fun m -> ml_rinst m ml_lexit1F) ml_regs @
    map (fun k ->
      list_mk_icomb "ml_flagok"
       [mk_var("f"^string_of_int k,`:num`); ml_var k ("ofs",`:num`);
        ml_o0 k]) [1;2;3;4]);;

let ml_lexit_vars =
  `j:num` :: List.concat(map (fun k ->
               ml_pervars k @ [ml_var k ("out",`:byte list`)]) [1;2;3;4]) @
  [`f1:num`; `f2:num`; `f3:num`; `f4:num`];;

let ml_lexitF = with_memsafe ml_lrr ml_lwr (mk_abs(`s:armstate`,
  list_mk_exists(ml_lexit_vars,
   mk_conj(ml_lexit_commonF,
     mk_disj(`read PC s = word(pc + 0x62f8) /\ read X4 s = word bc4 /\
              read X15 s = word f4`,
             `read PC s = word(pc + 0x65fc) /\ read X0 s = word bc4`)))));;

let ml_loop2wf_goal =
  let tm = mk_imp(list_mk_conj ml_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; ml_loop2w_pre; ml_lexitF; ml_loop2_frame]) in
  let vs = ml_loop2_vars @ map ml_bc0 [1;2;3;4] in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("ml_loop2wf_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let ML_LOOP2WF = prove
 (ml_loop2wf_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL ML_LOOP2)) THEN
  MATCH_MP_TAC RS_ENSURES_WEAKEN THEN CONJ_TAC THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `L4:num` THEN EXISTS_TAC `0` THEN
    MAP_EVERY EXISTS_TAC
     (List.concat(map (fun k -> [ml_o0 k; ml_bc0 k]) [1;2;3;4])) THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[SUB_0];
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
    THEN MAP_EVERY EXISTS_TAC ml_lexit_vars THEN
    ASM_REWRITE_TAC[ml_ofsok; ml_flagok]]);;

(*** The back of the slow path, from the setup of the main loop (0x55e0) ***)
(*** to 0x5444: the setup, then the loop and its exits or the skip, then ***)
(*** the rest; with the outputs at dst + k * q, segments q, q, q and     ***)
(*** n - 3 * q, and stream k starting at r_k = 8 * ofs0_k + 64 - bc0_k   ***)

let bk_op k =
  match k with
    1 -> `dst:int64`
  | 2 -> `word_add dst (word q):int64`
  | 3 -> `word_add dst (word (2 * q)):int64`
  | _ -> `word_add dst (word (3 * q)):int64`;;

let bk_L k = if k = 4 then `n - 3 * q` else `q:num`;;

let bk_r k =
  subst [ml_o0 k,`x:num`; ml_bc0 k,`b:num`] `8 * x + 64 - b`;;

let bk_inst =
  List.concat (map (fun k ->
    [bk_op k,ml_ov k; bk_L k,ml_Lv k; bk_r k,ml_var k ("r",`:num`)])
   [1;2;3;4]) @
  [`word_add dt (word 4):int64`,`tbl:int64`];;

let bk_win k =
  vsubst [ml_var k ("st",`:byte list`),`st:byte list`;
          ml_o0 k,`ofs:num`] ml_win;;

let bk_pre = mk_abs(`s:armstate`,list_mk_conj
 ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
    read PC s = word(pc + 0x55e0) /\
    read SP s = word_sub stackpointer (word 496) /\
    read X9 s = word_add dst (word n) /\
    read X6 s = word_add dst (word (3 * q)) /\
    read X7 s = word_add dst (word q) /\
    read X8 s = word_add dst (word (2 * q)) /\
    read X19 s = dst /\ read X20 s = word n /\ read X22 s = dt /\
    read X14 s = word_zx (dh:int32) /\
    read X11 s = src1 /\ read X10 s = src2 /\ read X15 s = src3 /\
    read X27 s = src4 /\ read X16 s = word_add src1 (word 8) /\
    read X26 s = word bc01 /\ read X2 s = word bc02 /\
    read X17 s = word bc03 /\ read X1 s = word 0`] @
  List.concat (map (fun k ->
    let a = 224 + 40 * (k - 1) in
    [ml_mem64 a (bk_win k); ml_mem32 (a + 8) (ml_bc0 k);
     ml_mem64 (a + 16) (mk_comb(mk_comb(`word_add:int64->int64->int64`,
                                        ml_sv k),
                                mk_comb(`word:num->int64`,ml_o0 k)))])
   [1;2;3;4]) @
  [el 0 ml_slots; el 2 ml_slots; el 3 ml_slots] @ rs_saved @
  map (fun k -> vsubst [ml_sv k,`src:int64`;
                        ml_var k ("st",`:byte list`),`st:byte list`]
     `read (memory :> bytes(src,LENGTH(st:byte list))) s =
      num_of_bytelist st`) [1;2;3;4] @
  [`read (memory :> bytes(word_add dt (word 4),2 * 2 EXP tl)) s =
    num_of_bytelist(huf_dtable ws ml tl)`;
   `read events s = e`]));;

let bk_post = vsubst bk_inst rs_post;;

let bk_frame =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
             X13; X14; X15; X16; X17; X18; X19; X20; X21; X22; X23; X24;
             X25; X26; X27; X28; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(dst,q); memory :> bytes(word_add dst (word q),q);
             memory :> bytes(word_add dst (word (2 * q)),q);
             memory :> bytes(word_add dst (word (3 * q)),n - 3 * q);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 112),272)]`;;

let bk_hyps =
  let stk = `word_sub stackpointer (word 496):int64,496`
  and code = `word pc:int64,32000`
  and tbl = `word_add dt (word 4):int64,2 * 2 EXP tl`
  and out = `(dst:int64),(n:num)` in
  let ins k = mk_pair(ml_sv k,mk_comb(`LENGTH:byte list->num`,
                                      ml_var k ("st",`:byte list`))) in
  let nonov a b = list_mk_icomb "nonoverlapping" [a; b] in
  [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ tl <= 12`;
   `val(word_subword (dh:int32) (16,8):byte) = tl`;
   `(n + 3) DIV 4 = q /\ 5 < n /\ n < 2 EXP 28 /\
    val(dst:int64) + n < 2 EXP 64`] @
  map (fun k ->
    vsubst [ml_sv k,`src:int64`; ml_var k ("st",`:byte list`),`st:byte list`;
            ml_o0 k,`ofs0:num`; ml_bc0 k,`bc0:num`]
     `8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64 /\
      bc0 <= 64 /\ (ofs0 = 0 \/ bc0 <= 8) /\
      (ofs0 = 0 \/ ofs0 + 8 <= LENGTH st)`) [1;2;3;4] @
  [nonov out tbl; nonov out code; nonov out stk] @
  map (fun k -> nonov out (ins k)) [1;2;3;4] @
  map (fun k -> nonov stk (ins k)) [1;2;3;4] @
  [nonov stk tbl; nonov stk code] @
  map (fun k -> nonov (ins k) code) [1;2;3;4];;

let bk_vars =
  [`pc:num`; `stackpointer:int64`; `dst:int64`; `n:num`; `q:num`;
   `dt:int64`; `dh:int32`; `tl:num`; `ws:num list`; `ml:num`;
   `v25:int64`; `v26:int64`; `v27:int64`; `v28:int64`;
   `e:uarch_event list`] @
  List.concat (map (fun k ->
    [ml_var k ("st",`:byte list`); ml_sv k; ml_o0 k; ml_bc0 k]) [1;2;3;4]);;

let bk_goal =
  let tm = mk_imp(list_mk_conj bk_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; bk_pre; bk_post; bk_frame]) in
  let fvs = frees tm in
  (match subtract fvs bk_vars with
     [] -> ()
   | v::_ -> failwith ("bk_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) bk_vars,tm);;

(*** Facts about the outputs ***)

let BK_FACTS_TAC : tactic =
  SUBGOAL_THEN `3 * q <= n /\ n - 3 * q <= q /\ q < 2 EXP 28 /\
                n - 3 * q < 2 EXP 28 /\ 3 <= n /\ 3 * q <= n + 3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(n + 3) DIV 4 = q`; `5 < n`; `n < 2 EXP 28`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun k ->
    let kq = if k = 1 then `q:num` else mk_binop `( * ):num->num->num`
               (mk_small_numeral k) `q:num` in
    MP_TAC(SPECL [`dst:int64`; kq] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`val(dst:int64) + n < 2 EXP 64`;
                             `3 * q <= n`] THEN ARITH_TAC;
      DISCH_TAC]) [1;2;3] THEN
  ASSUME_TAC(MP (SPECL [`dst:int64`; `n:num`] ST_SUB3)
                (ASSUME `3 <= n`)) THEN
  SUBGOAL_THEN
   `word_add (word_add dst (word (3 * q))) (word (n - 3 * q)) =
    word_add dst (word n):int64 /\
    word_add (word_add dst (word q)) (word q) =
    word_add dst (word (2 * q)):int64 /\
    word_add (word_add dst (word (2 * q))) (word q) =
    word_add dst (word (3 * q)):int64 /\
    word_add dst (word 0) = dst:int64`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD_0; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `3 * q <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(dst:int64) + q < 2 EXP 64 /\
    val(word_add dst (word q):int64) + q < 2 EXP 64 /\
    val(word_add dst (word (2 * q)):int64) + q < 2 EXP 64 /\
    val(word_add dst (word (3 * q)):int64) + (n - 3 * q) < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`val(dst:int64) + n < 2 EXP 64`; `3 * q <= n`;
                           `n - 3 * q <= q`] THEN ARITH_TAC;
    ALL_TAC];;

(*** A stream at its start ***)

let HUF_DSTATE_INIT = prove
 (`!ws ml (st:byte list) ofs bc.
        bc <= 64 ==> huf_dstate ws ml st (8 * ofs + 64 - bc) 0 ofs bc []`,
  REWRITE_TAC[huf_dstate; huf_decode] THEN ARITH_TAC);;

let BK_INIT_STATES_TAC : tactic =
  MAP_EVERY (fun k ->
    let st = ml_var k ("st",`:byte list`) in
    let b = mk_binop `(<=):num->num->bool` (ml_bc0 k) `64` in
    ASSUME_TAC(MP (SPECL [`ws:num list`; `ml:num`; st; ml_o0 k; ml_bc0 k]
                     HUF_DSTATE_INIT) (ASSUME b))) [1;2;3;4];;

(*** Big steps: the instantiations, the flags at the exits, and the      ***)
(*** conjuncts of preconditions                                           ***)

let bk_st_alist =
  [("b4",ml_bc0 4)] @
  List.concat (map (fun k ->
    let ks = string_of_int k in
    [("s"^ks,ml_sv k); ("c"^ks,bk_win k);
     ("p"^ks,mk_comb(mk_comb(`word_add:int64->int64->int64`,ml_sv k),
                     mk_comb(`word:num->int64`,ml_o0 k)))]) [1;2;3;4]);;

let bk_alist =
  [("tbl",`word_add dt (word 4):int64`)] @
  List.concat (map (fun k ->
    let ks = string_of_int k in
    [("op"^ks,bk_op k); ("L"^ks,bk_L k); ("r"^ks,bk_r k)]) [1;2;3;4]);;

let bk_auto_alist th (asl,w) =
  let s = rand w in
  let th0 = SPEC_ALL th in
  let tvs = frees(concl th0) in
  let _,[_; p; _; _] = strip_comb(rand(concl th0)) in
  let sv,body = dest_abs p in
  let facts = map (concl o snd) asl in
  let one t =
    if not(is_eq t) then [] else
    match lhs t with
      Comb(Comb(Const("read",_),c),s') when s' = sv ->
        (try let f = find (fun u -> is_eq u &&
                             lhs u = list_mk_icomb "read" [c; s]) facts in
             let _,tmi,_ = term_match [] (rhs t) (rhs f) in
             filter (fun (_,v) -> mem v tvs) tmi
         with Failure _ -> [])
    | _ -> [] in
  let insts = List.concat (map one (conjuncts body)) in
  map (fun (t,v) -> fst(dest_var v),t) (setify insts);;

let bk_dstate_alist asl =
  List.concat (map (fun k ->
    let st = ml_var k ("st",`:byte list`) in
    let th = snd(find (fun (_,th) -> let t = concl th in
      try fst(dest_const(fst(strip_comb t))) = "huf_dstate" &&
          el 2 (snd(strip_comb t)) = st
      with Failure _ -> false) asl) in
    let args = snd(strip_comb(concl th)) in
    let ks = string_of_int k in
    [("j",el 4 args); ("ofs"^ks,el 5 args); ("bc"^ks,el 6 args);
     ("out"^ks,el 7 args)]) [1;2;3;4]);;

let bk_skip_alist =
  ("j",`0`) ::
  List.concat (map (fun k ->
    let ks = string_of_int k in
    [("ofs"^ks,ml_o0 k); ("bc"^ks,ml_bc0 k); ("out"^ks,`[]:byte list`)])
   [1;2;3;4]);;

let BK_FLAG_TAC : tactic =
  W(fun (asl,w) ->
    let l,r = dest_disj w in
    let f = lhs r in
    let fth = snd(find (fun (_,th) -> let t = concl th in
      try let c,args = strip_comb t in
          fst(dest_const c) = "ml_flagok" && hd args = f
      with Failure _ -> false) asl) in
    let fth' = REWRITE_RULE[ml_flagok] fth in
    let d = CONJUNCT1 fth' and i = CONJUNCT2 fth' in
    DISJ_CASES_TAC d THENL
     [DISJ1_TAC THEN
      FIRST_ASSUM(fun eq0 ->
        if concl eq0 = mk_eq(f,`0`)
        then ASM_REWRITE_TAC[MP i eq0] else NO_TAC);
      DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let BK_PRE_TAC : tactic =
  FIRST
   [ASM_REWRITE_TAC[WORD_ADD_0; huf_decode; num_of_bytelist;
                    READ_MEMORY_BYTES_0; ml_ofsok; ml_flagok; LENGTH;
                    LE_0; SUB_0] THEN NO_TAC;
    REWRITE_TAC[GSYM ml_ofsok] THEN FIRST_ASSUM ACCEPT_TAC;
    BK_FLAG_TAC; MEMSAFE_TAC;
    REWRITE_TAC[huf_decode] THEN ML_ARITH_TAC];;

let BK_BIGSTEP_TAC th alist : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun (asl,w) ->
    let s = rand w in
    let rd = list_mk_icomb "read" [`events`; s] in
    let ec = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
                                  is_eq t && lhs t = rd) asl))) in
    let th' = ml_inst_thm th (("e",ec)::alist) in
    let n = let sn = fst(dest_var s) in
            int_of_string(String.sub sn 1 (String.length sn - 1)) in
    MP_TAC th' THEN ANTS_TAC THENL [ML_HYP_TAC; ALL_TAC] THEN
    ARM_BIGSTEP_TAC ZSTD_EXEC ("s"^string_of_int(n + 1)) THEN
    W(fun (_,w) ->
      if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                       with Failure _ -> false)
      then EVENTS_UNABBREV_TAC THEN MEMSAFE_STRIP_TAC
      else REPEAT CONJ_TAC THEN
           FIRST [ML_PRE_MEMSAFE_TAC; ML_FACT_TAC; T4_CONJ_TAC;
                  BK_PRE_TAC]));;

let BK_BCBOUND_TAC : tactic =
  W(fun (asl,w) ->
    let dths = filter (fun (_,th) -> let t = concl th in
      try fst(dest_const(fst(strip_comb t))) = "huf_dstate"
      with Failure _ -> false) asl in
    MAP_EVERY (fun (_,dth) ->
      let args = snd(strip_comb(concl dth)) in
      let bc = el 6 args in
      let bth = MATCH_MP ML_DSTATE_BOUND dth in
      SUBGOAL_THEN (mk_binop `(<):num->num->bool` bc `2 EXP 32`) ASSUME_TAC
      THENL [MP_TAC bth THEN FA_ARITHV_TAC [`q:num`]; ALL_TAC]) dths);;

(*** Going on with the theorem th of a later piece (with frame weakening) ***)

let BK_GOON_TAC th alist : tactic =
  W(fun (asl,w) ->
    let th1 = ml_inst_thm th alist in
    let hyp = lhand(concl th1) in
    let hth = TAC_PROOF((asl,hyp),ML_HYP_TAC) in
    let eth0 = MP th1 hth in
    let _,bod = dest_abs(rand(rator w)) in
    let c = rator(rator(rand bod)) in
    let c0 = rand(concl eth0) in
    let sth = TAC_PROOF((asl,list_mk_icomb "subsumed" [c0;c]),
                        SUBSUMED_MAYCHANGE_TAC) in
    let eth = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ sth eth0) in
    MATCH_MP_TAC(MATCH_MP EVENTUALLY_ENSURES eth) THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [ML_FACT_TAC; T4_CONJ_TAC; BK_PRE_TAC];
      CONJ_TAC THENL
       [MONOTONE_MAYCHANGE_TAC;
        BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]]);;

let bk_at a (asl,w) =
  let s = rand w in
  exists (fun (_,th) -> concl th =
            mk_eq(list_mk_icomb "read" [`PC`; s],
                  mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `pc:num`
                      (mk_small_numeral a)))) asl;;

let BK_LOOP_TAC : tactic =
  BK_BIGSTEP_TAC ML_LOOP2WF bk_alist THEN RS_2EXP64_TAC THEN
  BK_BCBOUND_TAC THEN
  W(fun gl -> if bk_at 0x62f8 gl
              then BK_BIGSTEP_TAC ML_EXA (bk_auto_alist ML_EXA gl)
              else BK_BIGSTEP_TAC ML_EXB (bk_auto_alist ML_EXB gl)) THEN
  RS_2EXP64_TAC THEN
  W(fun (asl,w) -> BK_GOON_TAC RS_CORRECT (bk_alist @ bk_dstate_alist asl));;

let BK_SKIP_TAC : tactic =
  RS_2EXP64_TAC THEN BK_GOON_TAC RS_CORRECT (bk_alist @ bk_skip_alist);;

let BK_CORRECT = prove
 (bk_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN BK_FACTS_TAC THEN
  BK_INIT_STATES_TAC THEN BK_BIGSTEP_TAC ST_CORRECT bk_st_alist THEN
  W(fun gl -> if bk_at 0x56fc gl then BK_LOOP_TAC else BK_SKIP_TAC));;

(* ------------------------------------------------------------------------- *)
(* The result of the four streams, from the specification.                   *)
(* ------------------------------------------------------------------------- *)

(*** Theory for the slow path: the start of a stream from its init (the  ***)
(*** end of the stream in the specification), a valid stream is not     ***)
(*** empty and ends with a nonzero byte, and the result from the four    ***)
(*** streams                                                             ***)

let HUF_LASTSHIFT_NONZERO = prove
 (`!b:byte. ~(b = word 0)
            ==> huf_lastshift b = 9 - bitsize(val b) /\
                1 <= bitsize(val b) /\ bitsize(val b) <= 8`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(val(b:byte) = 0) /\ val b < 256` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0] THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= bitsize(val(b:byte)) /\ bitsize(val b) <= 8`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE; ARITH_RULE `1 <= b <=> ~(b = 0)`;
                BITSIZE_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `val(b:byte) < 256` THEN ARITH_TAC;
    ASM_REWRITE_TAC[huf_lastshift; WORD_CLZ_BITSIZE; DIMINDEX_8] THEN
    UNDISCH_TAC `bitsize(val(b:byte)) <= 8` THEN ARITH_TAC]);;

let in_init_facts =
  let ofs = in_ofs0 and bc = in_bc0 in
  subst [ofs,`ofs0:num`; bc,`bc0:num`]
   `bc0 <= 64 /\ (ofs0 = 0 \/ bc0 <= 8) /\
    (ofs0 = 0 \/ ofs0 + 8 <= LENGTH(st:byte list)) /\
    zstd_end st (8 * ofs0 + 64 - bc0)`;;

let IN_INIT_FACTS = prove
 (mk_forall(`st:byte list`,mk_forall(`l:num`,
   mk_imp(`LENGTH(st:byte list) = l /\ ~(l = 0) /\
           ~(EL (l - 1) st = word 0)`,in_init_facts))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `b = EL (l - 1) (st:byte list)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUF_LASTSHIFT_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(st:byte list = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ZSTD_END_LAST] THEN
  SUBGOAL_THEN `~(val(b:byte) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0]; ASM_REWRITE_TAC[]] THEN
  MAP_EVERY UNDISCH_TAC
   [`1 <= bitsize(val(b:byte))`; `bitsize(val(b:byte)) <= 8`; `~(l = 0)`] THEN
  ARITH_TAC);;

let HUF_STREAM_LAST = prove
 (`!ws ml (st:byte list) out.
        huf_stream ws ml st out
        ==> ~(LENGTH st = 0) /\ ~(EL (LENGTH st - 1) st = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_stream] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  SPEC_TAC(`SND(huf_bits ws ml (out:byte list))`,`r:num`) THEN
  GEN_TAC THEN ASM_CASES_TAC `st:byte list = []` THENL
   [ASM_REWRITE_TAC[zstd_end]; ALL_TAC] THEN
  ASM_SIMP_TAC[ZSTD_END_LAST] THEN
  ASM_REWRITE_TAC[LENGTH_EQ_NIL; GSYM VAL_EQ_0] THEN SIMP_TAC[]);;

(*** Splitting the output in four, and putting it together ***)

let ZSTD_SUBLIST_EL = prove
 (`!(l:byte list) a n i. i < n ==> EL i (zstd_sublist l a n) = EL (a + i) l`,
  SIMP_TAC[zstd_sublist; EL_LIST_OF_SEQ]);;

let ZSTD_SUBLIST_APPEND = prove
 (`!(l:byte list) a m k.
        zstd_sublist l a (m + k) =
        APPEND (zstd_sublist l a m) (zstd_sublist l (a + m) k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_APPEND; LENGTH_ZSTD_SUBLIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ZSTD_SUBLIST_EL; EL_APPEND; LENGTH_ZSTD_SUBLIST] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ZSTD_SUBLIST_EL;
               ARITH_RULE `~(i < m) /\ i < m + k ==> i - m < k`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let ZSTD_SUBLIST_ALL = prove
 (`!(l:byte list). zstd_sublist l 0 (LENGTH l) = l`,
  GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_ZSTD_SUBLIST] THEN
  SIMP_TAC[ZSTD_SUBLIST_EL; ADD_CLAUSES]);;

let ZSTD_SUBLIST_SPLIT4 = prove
 (`!(out:byte list) q n.
        LENGTH out = n /\ 3 * q <= n
        ==> out = APPEND (zstd_sublist out 0 q)
                   (APPEND (zstd_sublist out q q)
                    (APPEND (zstd_sublist out (2 * q) q)
                            (zstd_sublist out (3 * q) (n - 3 * q))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ZSTD_SUBLIST_ALL] THEN
  SUBGOAL_THEN `LENGTH(out:byte list) = q + q + q + (n - 3 * q)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ZSTD_SUBLIST_APPEND] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `q + q = 2 * q /\ 2 * q + q = 3 * q`]);;

let ZSTD_SUBLIST_APPEND_LEFT = prove
 (`!(l1:byte list) l2 a k.
        a + k <= LENGTH l1
        ==> zstd_sublist (APPEND l1 l2) a k = zstd_sublist l1 a k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_ZSTD_SUBLIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ZSTD_SUBLIST_EL; EL_APPEND;
               ARITH_RULE `i < k /\ a + k <= l ==> a + i < l`]);;

let ZSTD_SUBLIST_APPEND_RIGHT = prove
 (`!(l1:byte list) l2 a k.
        LENGTH l1 <= a
        ==> zstd_sublist (APPEND l1 l2) a k =
            zstd_sublist l2 (a - LENGTH l1) k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_ZSTD_SUBLIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ZSTD_SUBLIST_EL; EL_APPEND;
               ARITH_RULE `l <= a ==> ~(a + i < l)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let ZSTD_SUBLIST_JOIN4 = prove
 (`!(l1:byte list) l2 l3 l4 q m.
        LENGTH l1 = q /\ LENGTH l2 = q /\ LENGTH l3 = q /\ LENGTH l4 = m
        ==> let out = APPEND l1 (APPEND l2 (APPEND l3 l4)) in
            LENGTH out = 3 * q + m /\
            zstd_sublist out 0 q = l1 /\ zstd_sublist out q q = l2 /\
            zstd_sublist out (2 * q) q = l3 /\
            zstd_sublist out (3 * q) m = l4`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ZSTD_SUBLIST_APPEND_LEFT; ZSTD_SUBLIST_APPEND_RIGHT;
               LENGTH_APPEND; LE_REFL; ADD_CLAUSES; SUB_REFL;
               ARITH_RULE `q <= 2 * q /\ q <= 3 * q /\ 2 * q - q = q /\
                           3 * q - q = 2 * q /\ q <= 2 * q`;
               ARITH_RULE `q + q <= 2 * q + q /\ 2 * q - q = q`] THEN
  REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ZSTD_SUBLIST_ALL] THEN
  ASM_REWRITE_TAC[]);;

let TRIPLE_EQ = prove
 (`!(d:A#B#C) a b c.
        d = (a,b,c) <=> FST d = a /\ FST(SND d) = b /\ SND(SND d) = c`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

(*** The result of the four streams: n and the bytes out for a valid    ***)
(*** block, and otherwise an error                                       ***)

let th_st =
 [`st1 = zstd_sublist (blk:byte list) 6 (huf_jump blk 0)`;
  `st2 = zstd_sublist (blk:byte list) (6 + huf_jump blk 0) (huf_jump blk 1)`;
  `st3 = zstd_sublist (blk:byte list) (6 + huf_jump blk 0 + huf_jump blk 1)
                      (huf_jump blk 2)`;
  `st4 = zstd_sublist (blk:byte list)
          (6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2)
          (LENGTH blk -
           (6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2))`];;

let th_hd k L =
  let st = mk_var("st"^string_of_int k,`:byte list`)
  and r = mk_var("r"^string_of_int k,`:num`) in
  list_mk_icomb "huf_decode" [`ws:num list`; `ml:num`; st; r; L];;

let th_L k = if k = 4 then `n - 3 * q` else `q:num`;;

let th_ok =
  list_mk_conj (map (fun k ->
    let h = th_hd k (th_L k) in
    mk_conj(mk_comb(`SND:num#bool->bool`,
                    mk_comb(`SND:byte list#num#bool->num#bool`,h)),
            mk_eq(mk_comb(`FST:num#bool->num`,
                    mk_comb(`SND:byte list#num#bool->num#bool`,h)),`0`)))
   [1;2;3;4]);;

let th_mems =
  list_mk_conj (map (fun k ->
    mk_eq(mk_var("m"^string_of_int k,`:num`),
          mk_comb(`num_of_bytelist`,
                  mk_comb(`FST:byte list#num#bool->byte list`,
                          th_hd k (th_L k))))) [1;2;3;4]);;

let huf_streams4_result =
  list_mk_forall
   ([`ws:num list`; `ml:num`; `blk:byte list`; `n:num`; `q:num`;
     `x0:int64`] @
    map (fun k -> mk_var("m"^string_of_int k,`:num`)) [1;2;3;4] @
    map (fun k -> mk_var("st"^string_of_int k,`:byte list`)) [1;2;3;4] @
    map (fun k -> mk_var("r"^string_of_int k,`:num`)) [1;2;3;4],
   mk_imp(list_mk_conj
     ([`huf_complete ws ml /\ LENGTH(ws:num list) <= 256`;
       `(n + 3) DIV 4 = q /\ 5 < n`;
       `6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2 <=
        LENGTH(blk:byte list)`] @ th_st @
      map (fun k -> list_mk_icomb "zstd_end"
                     [mk_var("st"^string_of_int k,`:byte list`);
                      mk_var("r"^string_of_int k,`:num`)]) [1;2;3;4] @
      [mk_eq(`x0:int64`,mk_cond(th_ok,`word n:int64`,
                                `word 18446744073709551596:int64`));
       mk_imp(th_ok,th_mems)]),
    `(!out. LENGTH out = n /\ huf_streams4 T ws ml blk out
            ==> x0 = word n /\
                m1 + 2 EXP (8 * q) * (m2 + 2 EXP (8 * q) *
                                      (m3 + 2 EXP (8 * q) * m4)) =
                num_of_bytelist out) /\
     ((!out. LENGTH out = n ==> ~huf_streams4 T ws ml blk out)
      ==> zstd_is_error x0)`));;

let th_char =
  `!out:byte list. LENGTH out = n
      ==> (huf_streams4 T ws ml blk out <=>
           huf_decode ws ml (zstd_sublist blk 6 (huf_jump blk 0)) r1 q =
           (zstd_sublist out 0 q,0,T) /\
           huf_decode ws ml
            (zstd_sublist blk (6 + huf_jump blk 0) (huf_jump blk 1)) r2 q =
           (zstd_sublist out q q,0,T) /\
           huf_decode ws ml
            (zstd_sublist blk (6 + huf_jump blk 0 + huf_jump blk 1)
                          (huf_jump blk 2)) r3 q =
           (zstd_sublist out (2 * q) q,0,T) /\
           huf_decode ws ml
            (zstd_sublist blk
              (6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2)
              (LENGTH blk -
               (6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2)))
            r4 (n - 3 * q) =
           (zstd_sublist out (3 * q) (n - 3 * q),0,T))`;;

let HUF_STREAMS4_RESULT = prove
 (huf_streams4_result,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun k ->
    let v = mk_var("st"^string_of_int k,`:byte list`) in
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = v))) [1;2;3;4] THEN
  SUBGOAL_THEN `3 * q <= n` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(n + 3) DIV 4 = q`; `5 < n`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN th_char ASSUME_TAC THENL
   [X_GEN_TAC `out:byte list` THEN DISCH_TAC THEN
    REWRITE_TAC[huf_streams4] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[HUF_STREAM_DECODE; LENGTH_ZSTD_SUBLIST] THEN
    MATCH_MP_TAC(TAUT `a /\ b ==> (a /\ b /\ c <=> c)`) THEN
    MAP_EVERY UNDISCH_TAC
     [`6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2 <=
       LENGTH(blk:byte list)`; `5 < n`] THEN ARITH_TAC;
    ALL_TAC] THEN
  let th_dk k = vsubst (map (fun e -> rhs e,lhs e) th_st) (th_hd k (th_L k))
  and dv k = mk_var("d"^string_of_int k,`:byte list#num#bool`) in
  MAP_EVERY (fun k -> ABBREV_TAC (mk_eq(dv k,th_dk k))) [1;2;3;4] THEN
  SUBGOAL_THEN
   `LENGTH(FST(d1:byte list#num#bool)) = q /\
    LENGTH(FST(d2:byte list#num#bool)) = q /\
    LENGTH(FST(d3:byte list#num#bool)) = q /\
    LENGTH(FST(d4:byte list#num#bool)) = n - 3 * q`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d1";"d2";"d3";"d4"] THEN
    REWRITE_TAC[HUF_DECODE_LENGTH];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[TRIPLE_EQ] o
    check (fun th -> is_forall(concl th))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `out:byte list` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `out:byte list` o
      check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [MP (SPECL [`out:byte list`; `q:num`; `n:num`] ZSTD_SUBLIST_SPLIT4)
         (CONJ (ASSUME `LENGTH(out:byte list) = n`)
               (ASSUME `3 * q <= n`))] THEN
    REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_ZSTD_SUBLIST];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV] THEN
  ABBREV_TAC `out = APPEND (FST(d1:byte list#num#bool))
                     (APPEND (FST(d2:byte list#num#bool))
                       (APPEND (FST(d3:byte list#num#bool))
                               (FST(d4:byte list#num#bool))))` THEN
  MP_TAC(SPECL [`FST(d1:byte list#num#bool)`; `FST(d2:byte list#num#bool)`;
                `FST(d3:byte list#num#bool)`; `FST(d4:byte list#num#bool)`;
                `q:num`; `n - 3 * q`] ZSTD_SUBLIST_JOIN4) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) &&
       is_neg(rand(snd(dest_forall(concl th))))
    then MP_TAC(SPEC `out:byte list` th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then MP_TAC(SPEC `out:byte list` th)
    else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `3 * q <= n ==> 3 * q + n - 3 * q = n`] THEN
  CONV_TAC TAUT);;

(*** What a valid block needs: the checks of the code all pass ***)

let th_a4 = `6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2`;;

let huf_streams4_necessary =
  let streams =
   [`zstd_sublist (blk:byte list) 6 (huf_jump blk 0)`,`huf_jump blk 0`;
    `zstd_sublist (blk:byte list) (6 + huf_jump blk 0) (huf_jump blk 1)`,
    `huf_jump blk 1`;
    `zstd_sublist (blk:byte list) (6 + huf_jump blk 0 + huf_jump blk 1)
                  (huf_jump blk 2)`,`huf_jump blk 2`;
    subst [th_a4,`a4:num`]
     `zstd_sublist (blk:byte list) a4 (LENGTH blk - a4)`,
    subst [th_a4,`a4:num`] `LENGTH(blk:byte list) - a4`] in
  let one (st,l) =
    subst [st,`st:byte list`; l,`l:num`]
     `~(l = 0) /\ ~(EL (l - 1) (st:byte list) = word 0)` in
  mk_forall(`ws:num list`,mk_forall(`ml:num`,mk_forall(`blk:byte list`,
   mk_forall(`out:byte list`,
    mk_imp(`huf_streams4 T ws ml blk out`,
     list_mk_conj
      ([`5 < LENGTH(out:byte list) /\ 9 < LENGTH(blk:byte list)`;
        mk_binop `(<=):num->num->bool` th_a4 `LENGTH(blk:byte list)`] @
       map one streams))))));;

let HUF_STREAMS4_NECESSARY = prove
 (huf_streams4_necessary,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_streams4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP HUF_STREAM_LAST)) THEN
  REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The slow path as a whole, from 0x5458 to 0x5444.                          *)
(* ------------------------------------------------------------------------- *)

(*** The slow path of HUF_decompress4X1_usingDTable_internal, from 0x5458 ***)
(*** to 0x5444: the result n and the bytes out for a valid block and an   ***)
(*** error otherwise, with x25-x28 restored                              ***)

let sp_rr =
 `[src,LENGTH(blk:byte list); dt,4; word_add dt (word 4),2 * 2 EXP tl;
   word_sub stackpointer (word 496),496]:(int64#num)list`
and sp_wr =
 `[dst,n; word_sub stackpointer (word 496),496]:(int64#num)list`;;

let sp_pre = mk_abs(`s:armstate`,
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x5458) /\
  read SP s = word_sub stackpointer (word 496) /\
  read X19 s = dst /\ read X20 s = word n /\ read X18 s = src /\
  read X23 s = word(LENGTH(blk:byte list)) /\ read X22 s = dt /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28 /\
  read (memory :> bytes(src,LENGTH blk)) s = num_of_bytelist blk /\
  read (memory :> bytes32 dt) s = dh /\
  read (memory :> bytes(word_add dt (word 4),2 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable ws ml tl) /\
  read events s = e`);;

let sp_post = with_memsafe sp_rr sp_wr (mk_abs(`s:armstate`,
 `read PC s = word(pc + 0x5444) /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28 /\
  (!out. LENGTH out = n /\ huf_streams4 T ws ml blk out
         ==> read X0 s = word n /\
             read (memory :> bytes(dst,n)) s = num_of_bytelist out) /\
  ((!out. LENGTH out = n ==> ~huf_streams4 T ws ml blk out)
   ==> zstd_is_error(read X0 s))`));;

let sp_frame =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
             X13; X14; X15; X16; X17; X18; X19; X20; X21; X22; X23; X24;
             X25; X26; X27; X28; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(dst,n);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),432)]`;;

let sp_hyps =
  let stk = `word_sub stackpointer (word 496):int64,496`
  and code = `word pc:int64,32000`
  and tbl = `word_add dt (word 4):int64,2 * 2 EXP tl`
  and out = `(dst:int64),(n:num)`
  and ins = `(src:int64),LENGTH(blk:byte list)` in
  let nonov a b = list_mk_icomb "nonoverlapping" [a; b] in
  [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ tl <= 12`;
   `val(word_subword (dh:int32) (16,8):byte) = tl`;
   `n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64`;
   `8 <= val(src:int64) /\ val src + LENGTH(blk:byte list) + 8 < 2 EXP 64 /\
    LENGTH blk < 2 EXP 32`;
   nonov out tbl; nonov out code; nonov out stk; nonov out ins;
   nonov stk ins; nonov stk tbl; nonov stk code; nonov ins code;
   nonov tbl code];;

let sp_vars =
  [`pc:num`; `stackpointer:int64`; `dst:int64`; `n:num`; `src:int64`;
   `blk:byte list`; `dt:int64`; `dh:int32`; `tl:num`; `ws:num list`;
   `ml:num`; `v25:int64`; `v26:int64`; `v27:int64`; `v28:int64`;
   `e:uarch_event list`];;

let sp_goal =
  let tm = mk_imp(list_mk_conj sp_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; sp_pre; sp_post; sp_frame]) in
  let fvs = frees tm in
  (match subtract fvs sp_vars with
     [] -> ()
   | v::_ -> failwith ("sp_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) sp_vars,tm);;

(*** The bytes of part of a block ***)

let READ_MEMORY_SUBLIST = prove
 (`!(a:int64) (l:byte list) m k s.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        m + k <= LENGTH l
        ==> read (memory :> bytes(word_add a (word m),k)) s =
            num_of_bytelist(zstd_sublist l m k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ZSTD_SUBLIST_SUB_LIST] THEN
  MP_TAC(ISPECL [`a:int64`; `l:byte list`; `m:num`; `k:num`; `s:armstate`]
    READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_SIMP_TAC[]);;

(*** An equation of addresses, equal in the normal form of the simulator ***)

let SP_WORD_EQ_TAC : tactic =
  CONV_TAC(BINOP_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[] THEN NO_TAC;;

(*** Going on with a later piece, with a tactic for its postcondition;  ***)
(*** the frames are compared with only the facts subfacts (the arithmetic ***)
(*** of the containments would take ages with all the assumptions)        ***)

let SP_GOON_TAC subfacts wtac th alist : tactic =
  W(fun (asl,w) ->
    let th1 = ml_inst_thm th (("e",current_events (asl,w))::alist) in
    let hyp = lhand(concl th1) in
    let hth = TAC_PROOF((asl,hyp),ML_HYP_TAC) in
    let eth0 = MP th1 hth in
    let _,bod = dest_abs(rand(rator w)) in
    let c = rator(rator(rand bod)) in
    let c0 = rand(concl eth0) in
    let sasl = filter (fun (_,th) -> mem (concl th) subfacts) asl in
    let sth = TAC_PROOF((sasl,list_mk_icomb "subsumed" [c0;c]),
                        SUBSUMED_MAYCHANGE_TAC) in
    let eth = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ sth eth0) in
    MATCH_MP_TAC(MATCH_MP EVENTUALLY_ENSURES eth) THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [ML_FACT_TAC; SP_WORD_EQ_TAC; T4_CONJ_TAC; BK_PRE_TAC];
      CONJ_TAC THENL [MONOTONE_MAYCHANGE_TAC; BETA_TAC THEN wtac]]);;

(*** The abbreviations of the jump table, the streams and the outputs,   ***)
(*** and facts about them, after the entry checks                         ***)

let sp_st k =
  let jl = [`j0:num`; `j1:num`; `j2:num`; `l4:num`]
  and al = [`6`; `6 + j0`; `6 + j0 + j1`; `6 + j0 + j1 + j2`] in
  el (k - 1) al,el (k - 1) jl;;

let sp_src k =
  let a,_ = sp_st k in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`src:int64`),
          mk_comb(`word:num->int64`,a));;

let SP_ABBREV_TAC : tactic =
  ABBREV_TAC `j0 = huf_jump blk 0` THEN ABBREV_TAC `j1 = huf_jump blk 1` THEN
  ABBREV_TAC `j2 = huf_jump blk 2` THEN ABBREV_TAC `q = (n + 3) DIV 4` THEN
  ABBREV_TAC `l4 = LENGTH(blk:byte list) - (6 + j0 + j1 + j2)` THEN
  MAP_EVERY (fun k ->
    let a,l = sp_st k in
    ABBREV_TAC (mk_eq(mk_var("st"^string_of_int k,`:byte list`),
                      list_mk_icomb "zstd_sublist" [`blk:byte list`; a; l])))
   [1;2;3;4];;

let SP_FACTS_TAC : tactic =
  MAP_EVERY (fun k ->
    let j = mk_var("j"^string_of_int k,`:num`) in
    let eq = ASSUME(mk_eq(list_mk_icomb "huf_jump"
                            [`blk:byte list`; mk_small_numeral k],j)) in
    ASSUME_TAC(REWRITE_RULE[eq]
      (SPECL [`blk:byte list`; mk_small_numeral k] HUF_JUMP_BOUND)))
   [0;1;2] THEN
  SUBGOAL_THEN `6 + j0 + j1 + j2 + l4 = LENGTH(blk:byte list) /\
                l4 < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`LENGTH(blk:byte list) - (6 + j0 + j1 + j2) = l4`;
      `6 + j0 + j1 + j2 <= LENGTH(blk:byte list)`;
      `LENGTH(blk:byte list) < 2 EXP 32`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun k ->
    let a,l = sp_st k in
    let st = mk_var("st"^string_of_int k,`:byte list`) in
    ASSUME_TAC(REWRITE_RULE[LENGTH_ZSTD_SUBLIST]
      (AP_TERM `LENGTH:byte list->num`
        (SYM(ASSUME(mk_eq(list_mk_icomb "zstd_sublist"
                            [`blk:byte list`; a; l],st)))))))
   [1;2;3;4] THEN
  W(fun (asl,w) ->
    let s = rand w in
    let bth = snd(find (fun (_,th) -> let t = concl th in
      is_eq t && lhs t = subst [s,`s:armstate`]
        `read (memory :> bytes(src,LENGTH(blk:byte list))) s`) asl) in
    MAP_EVERY (fun k ->
      let a,l = sp_st k in
      let st = mk_var("st"^string_of_int k,`:byte list`) in
      let c = mk_binop `(<=):num->num->bool`
                (mk_binop `(+):num->num->num` a l) `LENGTH(blk:byte list)` in
      SUBGOAL_THEN c ASSUME_TAC THENL
       [UNDISCH_TAC `6 + j0 + j1 + j2 + l4 = LENGTH(blk:byte list)` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      W(fun (asl,w) ->
        let th = MP (ISPECL [`src:int64`; `blk:byte list`; a; l; s]
                       READ_MEMORY_SUBLIST) (CONJ bth (ASSUME c)) in
        let sth = ASSUME(mk_eq(list_mk_icomb "zstd_sublist"
                                 [`blk:byte list`; a; l],st))
        and lth = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,st),l)) in
        ASSUME_TAC(REWRITE_RULE[sth; GSYM lth] th)))
     [1;2;3;4]) THEN
  MAP_EVERY (fun k ->
    let a,_ = sp_st k in
    MP_TAC(SPECL [`src:int64`; a] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`;
        `6 + j0 + j1 + j2 + l4 = LENGTH(blk:byte list)`] THEN ARITH_TAC;
      DISCH_TAC]) [1;2;3;4] THEN
  MAP_EVERY (fun k ->
    let a,l = sp_st k in
    let t = mk_binop `(<):num->num->bool`
              (mk_binop `(+):num->num->num`
                 (mk_comb(`val:int64->num`,sp_src k))
                 (mk_binop `(+):num->num->num` l `8`)) `2 EXP 64` in
    SUBGOAL_THEN t ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`;
        `6 + j0 + j1 + j2 + l4 = LENGTH(blk:byte list)`] THEN ARITH_TAC;
      ALL_TAC]) [1;2;3;4] THEN
  SUBGOAL_THEN
   `val(src:int64) + 6 + j0 + 8 < 2 EXP 64 /\
    j0 < 2 EXP 16 /\ j1 < 2 EXP 16 /\ j2 < 2 EXP 16 /\
    j0 < 2 EXP 32 /\ j1 < 2 EXP 32 /\ j2 < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`;
      `6 + j0 + j1 + j2 + l4 = LENGTH(blk:byte list)`;
      `j0 < 65536`; `j1 < 65536`; `j2 < 65536`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add src (word 6)) (word j0) =
    word_add src (word (6 + j0)):int64 /\
    word_add (word_add src (word (6 + j0))) (word j1) =
    word_add src (word (6 + j0 + j1)):int64 /\
    word_add (word_add src (word (6 + j0 + j1))) (word j2) =
    word_add src (word (6 + j0 + j1 + j2)):int64 /\
    word_add (word_add src (word 6)) (word 8) =
    word_add src (word 14):int64`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(*** The inits of the streams: their instantiations, and the facts about ***)
(*** the starts of the streams for the back                              ***)

let sp_in_alist k =
  if k = 1 then
    [("csrc",`src:int64`); ("st",`st1:byte list`); ("l",`j0:num`)]
  else
    let _,l = sp_st k and _,lp = sp_st (k - 1) in
    [("p",sp_src k); ("q",sp_src (k - 1));
     ("st",mk_var("st"^string_of_int k,`:byte list`)); ("l",l); ("l'",lp)];;

let SP_IN_TAC k : tactic =
  let th = el (k - 1) [IN1_CORRECT; IN2_CORRECT; IN3_CORRECT; IN4_CORRECT] in
  W(fun gl -> BK_BIGSTEP_TAC th (sp_in_alist k @ bk_auto_alist th gl));;

let sp_ofs0 k =
  let _,l = sp_st k in
  vsubst [l,`l:num`; mk_var("st"^string_of_int k,`:byte list`),
          `st:byte list`] in_ofs0;;

let sp_bc0 k =
  let _,l = sp_st k in
  vsubst [l,`l:num`; mk_var("st"^string_of_int k,`:byte list`),
          `st:byte list`] in_bc0;;

let sp_bk_alist =
  List.concat (map (fun k ->
    let ks = string_of_int k in
    [("src"^ks,sp_src k); ("ofs0"^ks,sp_ofs0 k); ("bc0"^ks,sp_bc0 k)])
   [1;2;3;4]);;

let SP_INIT_FACTS_TAC : tactic =
  MAP_EVERY (fun k ->
    let _,l = sp_st k in
    let st = mk_var("st"^string_of_int k,`:byte list`) in
    let c = list_mk_conj
      [mk_eq(mk_comb(`LENGTH:byte list->num`,st),l);
       mk_neg(mk_eq(l,`0`));
       mk_neg(mk_eq(list_mk_icomb "EL"
                     [mk_binop `(-):num->num->num` l `1`; st],
                    `word 0:byte`))] in
    SUBGOAL_THEN c ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o MATCH_MP IN_INIT_FACTS))
   [1;2;3;4] THEN
  MAP_EVERY (fun k ->
    let _,l = sp_st k in
    let st = mk_var("st"^string_of_int k,`:byte list`) in
    let lth = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,st),l)) in
    let t = mk_binop `(<):num->num->bool`
              (mk_binop `(+):num->num->num`
                 (mk_comb(`val:int64->num`,sp_src k))
                 (mk_binop `(+):num->num->num`
                    (mk_comb(`LENGTH:byte list->num`,st)) `8`)) `2 EXP 64` in
    SUBGOAL_THEN t ASSUME_TAC THENL
     [REWRITE_TAC[lth] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) [1;2;3;4] THEN
  SUBGOAL_THEN `3 * q <= n` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(n + 3) DIV 4 = q`; `5 < n`] THEN ARITH_TAC;
    ALL_TAC];;

(*** The errors: no valid block ***)

let sp_en_bad =
  mk_neg `5 < n /\ 9 < LENGTH(blk:byte list) /\
          6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2 <=
          LENGTH blk`;;

let SP_FAIL_TAC : tactic =
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `out:byte list` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HUF_STREAMS4_NECESSARY) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `LENGTH(out:byte list) = n`)) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = sp_en_bad)) THEN
        REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN NO_TAC);
    DISCH_TAC THEN REWRITE_TAC[zstd_is_error] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV];;

(*** The bytes out as the four segments, and the final result ***)

let SP_BYTES4 = prove
 (`!(dst:int64) q n s.
        3 * q <= n
        ==> read (memory :> bytes(dst,n)) s =
            read (memory :> bytes(dst,q)) s +
            2 EXP (8 * q) *
            (read (memory :> bytes(word_add dst (word q),q)) s +
             2 EXP (8 * q) *
             (read (memory :> bytes(word_add dst (word (2 * q)),q)) s +
              2 EXP (8 * q) *
              read (memory :> bytes(word_add dst (word (3 * q)),n - 3 * q))
                   s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = q + q + q + (n - 3 * q)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `q + q = 2 * q /\ q + 2 * q = 3 * q`]);;

let sp_result_th (asl,w) =
  let x0 = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
             is_eq t &&
             (match lhs t with Comb(Comb(Const("read",_),c),_) -> c = `X0`
                             | _ -> false)) asl))) in
  let mem k = subst [bk_op k,`a:int64`; bk_L k,`k:num`]
               `read (memory :> bytes(a,k)) (s':armstate)` in
  let r k = subst [sp_ofs0 k,`x:num`; sp_bc0 k,`b:num`] `8 * x + 64 - b` in
  ISPECL
   ([`ws:num list`; `ml:num`; `blk:byte list`; `n:num`; `q:num`; x0] @
    map mem [1;2;3;4] @
    map (fun k -> mk_var("st"^string_of_int k,`:byte list`)) [1;2;3;4] @
    map r [1;2;3;4])
   HUF_STREAMS4_RESULT;;

(*** The memory safety at the end, from the facts about the traces and   ***)
(*** the arithmetic of the lengths only: with all the facts, the failed   ***)
(*** tries of the containments take minutes and gigabytes                 ***)

let SP_MEMSAFE_TAC : tactic =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="] in
  let okvars = [`n:num`; `q:num`; `j0:num`; `j1:num`; `j2:num`; `l4:num`;
                `blk:byte list`; `st1:byte list`; `st2:byte list`;
                `st3:byte list`; `st4:byte list`; `tl:num`] in
  let keep t =
    (match strip_comb t with
       Const("memaccess_inbounds",_),_ -> true
     | _ -> false) ||
    (is_eq t && is_comb(lhs t) &&
     (try rand(rator(lhs t)) = `events` with Failure _ -> false)) ||
    ((is_num_relop t || (is_neg t && is_num_relop(dest_neg t))) &&
     subset (frees t) okvars &&
     not(can (find_term (fun u -> is_const u && fst(dest_const u) = "EL")) t))
  in
  W(fun (asl,w) ->
    let sasl = filter (fun (_,th) -> keep(concl th)) asl in
    ACCEPT_TAC(TAC_PROOF((sasl,w),MEMSAFE_TAC)));;

let SP_FINAL_TAC : tactic =
  X_GEN_TAC `s':armstate` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MEMSAFE_STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ c ==> a /\ b /\ c`) THEN
  CONJ_TAC THENL [ALL_TAC; SP_MEMSAFE_TAC] THEN
  REWRITE_TAC[MATCH_MP SP_BYTES4 (ASSUME `3 * q <= n`)] THEN
  W(fun gl -> MP_TAC(sp_result_th gl)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC];;

let SP_BACK_TAC : tactic =
  SP_INIT_FACTS_TAC THEN
  SP_GOON_TAC [`3 * q <= n`; `val(dst:int64) + n < 2 EXP 64`;
               `n < 2 EXP 28`] SP_FINAL_TAC BK_CORRECT sp_bk_alist;;

let SP_GUARD tac : tactic =
  W(fun gl -> if bk_at 0x5444 gl then SP_FAIL_TAC else tac);;

let SP_CORRECT = prove
 (sp_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN BK_BIGSTEP_TAC EN_CORRECT [] THEN
  SP_GUARD
   (SP_ABBREV_TAC THEN SP_FACTS_TAC THEN SP_IN_TAC 1 THEN
    SP_GUARD
     (SP_IN_TAC 2 THEN
      SP_GUARD
       (SP_IN_TAC 3 THEN
        SP_GUARD
         (SP_IN_TAC 4 THEN SP_GUARD SP_BACK_TAC)))));;

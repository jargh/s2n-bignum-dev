(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The slow path of the decoding of Huffman-coded literals in four streams   *)
(* with double-symbol tables in zstd, compiled by gcc 12 at -O2 for AArch64: *)
(* HUF_decompress4X2_usingDTable_internal from 0x32d0 to 0x333c.             *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode4x1_gcc12_O2.ml";;
needs "arm/proofs/zstd_huf_decode4x2_fast_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress4X2_usingDTable_internal at 0x30c0 goes to its slow path at *)
(* 0x32d0 when bit 5 of the flags (HUF_flags_disableFast) is set or its fast *)
(* path does not apply. The slow path checks that the output has more than 5 *)
(* bytes and the block more than 9, reads the jump table of the sizes of the *)
(* first three streams (the fourth taking the rest), initializes a bit       *)
(* stream for each (error codes for an empty stream or one whose last byte   *)
(* is 0), decodes the four streams together in its main loop, 4 lookups of   *)
(* each stream (of one or two symbols each) between reloads, with only the   *)
(* room of the fourth output checked, then checks that the outputs are in    *)
(* order, decodes the rest of each stream and checks that each stream ends   *)
(* at its start with all 64 bits of its container used, returning n or an    *)
(* error code at the epilogue at 0x333c. SP2_CORRECT: for a block that       *)
(* decodes to n bytes (huf_streams4 T), the result is n with the output at   *)
(* dst. SP2S_CORRECT: for any block the result is n or an error code, and    *)
(* the memory accesses are within the block, the table, the output and the   *)
(* frame. SP2ALL_CORRECT has both. The last symbol of a stream adds the bits *)
(* of both symbols of a two-symbol entry to the bits used (up to 64), so the *)
(* end check also passes when the code of the second symbol is cut off at    *)
(* the start of the stream: the slow path accepts some blocks that           *)
(* huf_streams4 T rejects, and the theorems do not say that the result is an *)
(* error for an invalid block. In the main loop the other outputs may run    *)
(* ahead of the fourth (8 bytes an iteration against 4), but stay within the *)
(* output, and the check of the order after the loop catches those past      *)
(* their segments. The output must not be at address 0: the loop of 5        *)
(* lookups of a tail compares with its end less 9, which wraps for an output *)
(* of 8 bytes at 0.                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Facts about the decoding of a valid stream (huf_decode): the room it      *)
(* needs, its steps by the entries of the double-symbol table, and the       *)
(* lookups of the code.                                                      *)
(* ------------------------------------------------------------------------- *)

(*** The code of HUF_decompress4X2_usingDTable_internal ***)

let SLOW2_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc
  [0x30c0,0x5300];;

(*** The decoding of a valid stream, of L symbols ending at position 0: ***)
(*** after jj of them, the bits left are at most ml for each symbol    ***)
(*** left                                                              ***)

let HUF_DECODE_ROOM = prove
 (`!ws ml (st:byte list) r L jj.
        huf_complete ws ml /\
        SND(SND(huf_decode ws ml st r L)) /\
        FST(SND(huf_decode ws ml st r L)) = 0 /\ jj <= L
        ==> FST(SND(huf_decode ws ml st r jj)) <= ml * (L - jj)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS] o check (is_binary "<=" o concl)) THEN
  REWRITE_TAC[ADD_SUB2] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`jj:num`,`jj:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THENL [SIMP_TAC[ADD_CLAUSES; MULT_CLAUSES; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN X_GEN_TAC `jj:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `jj + 1`) THEN
  REWRITE_TAC[ARITH_RULE `(jj + 1) + d = SUC(jj + d)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND(SND(huf_decode ws ml (st:byte list) r (jj + 1)))`
  MP_TAC THENL
   [MATCH_MP_TAC HUF_DECODE_OK_MONO THEN
    EXISTS_TAC `SUC(jj + d)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HUF_DECODE_SUC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back (st:byte list)
                    (FST(SND(huf_decode ws ml st r jj))) ml`]
    HUF_NBITS_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN SIMPLE_ARITH_TAC);;

(*** One lookup of the double-symbol table from a good state of a valid ***)
(*** decoding (the bits of the lookup in the container): one or two     ***)
(*** more symbols, and the bits of their codes used                     ***)

let ML2_STEP = prove
 (`!ws ml (st:byte list) r L jj ofs bc tl.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\
        SND(SND(huf_decode ws ml st r L)) /\
        FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\
        bc <= 64 /\ (ofs = 0 \/ tl + bc <= 64) /\ jj + 2 <= L
        ==> let e = huf_dentry2 ws ml tl (zstd_back st (8 * ofs + 64 - bc) tl)
            in SND(SND(huf_decode ws ml st r (jj + EL 3 e))) /\
               bc + EL 2 e <= 64 /\
               FST(SND(huf_decode ws ml st r (jj + EL 3 e))) =
               8 * ofs + 64 - (bc + EL 2 e) /\
               FST(huf_decode ws ml st r (jj + EL 3 e)) =
               APPEND (FST(huf_decode ws ml st r jj))
                      (if EL 3 e = 2 then [word(EL 0 e); word(EL 1 e)]
                       else [word(EL 0 e)])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `st:byte list`; `r:num`;
                `jj:num`] HUF_DECODE_X2_STEP) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`;
                `zstd_back (st:byte list) (8 * ofs + 64 - bc) tl`]
    HUF_DENTRY2_BOUNDS) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC
   `e = huf_dentry2 ws ml tl (zstd_back (st:byte list)
                                (8 * ofs + 64 - bc) tl)` THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `SND(SND(huf_decode ws ml (st:byte list) r (jj + EL 3 e)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HUF_DECODE_OK_MONO THEN EXISTS_TAC `L:num` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`EL 3 e = 1 \/ EL 3 e = 2`; `jj + 2 <= L`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `SND(SND(huf_decode ws ml (st:byte list) r (jj + EL 3 e))) <=>
    SND(SND(huf_decode ws ml st r jj)) /\ EL 2 e <= 8 * ofs + 64 - bc` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bc + EL 2 e <= 64` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ofs = 0 \/ tl + bc <= 64`; `EL 2 e <= 8 * ofs + 64 - bc`;
      `EL 2 e <= tl`; `bc <= 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`bc + EL 2 e <= 64`; `bc <= 64`] THEN ARITH_TAC);;

(*** The last symbol of a valid decoding: the first symbol of the entry, ***)
(*** at the start of the stream, all its bits then used (64 in the       ***)
(*** container, the code keeping 64 for an entry of two symbols)         ***)

let ML2_LAST = prove
 (`!ws ml (st:byte list) r L ofs bc tl.
        huf_complete ws ml /\ ml <= tl /\ tl <= 12 /\
        SND(SND(huf_decode ws ml st r (L + 1))) /\
        FST(SND(huf_decode ws ml st r (L + 1))) = 0 /\
        FST(SND(huf_decode ws ml st r L)) = 8 * ofs + 64 - bc /\
        bc <= 64 /\ (ofs = 0 \/ tl + bc <= 64)
        ==> let e = huf_dentry2 ws ml tl (zstd_back st (8 * ofs + 64 - bc) tl)
            in FST(huf_decode ws ml st r (L + 1)) =
               APPEND (FST(huf_decode ws ml st r L)) [word(EL 0 e)] /\
               ofs = 0 /\
               (if EL 3 e = 1 then bc + EL 2 e = 64
                else bc < 64 /\ 64 < bc + EL 2 e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_SIMP_TAC[HUF_DENTRY2_BACK] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HUF_DECODE_SUC]) THEN
  REWRITE_TAC[HUF_DECODE_SUC] THEN
  FIRST_X_ASSUM(fun th ->
    if concl th =
       `FST(SND(huf_decode ws ml (st:byte list) r L)) = 8 * ofs + 64 - bc`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]
    else NO_TAC) THEN
  ABBREV_TAC `s1 = huf_symbol ws (zstd_back (st:byte list)
                                    (8 * ofs + 64 - bc) ml)` THEN
  ABBREV_TAC `nb1 = (ml + 1) - EL s1 ws` THEN
  ABBREV_TAC `s2 = huf_symbol ws (zstd_back (st:byte list)
                                   ((8 * ofs + 64 - bc) - nb1) ml)` THEN
  ABBREV_TAC `nb2 = (ml + 1) - EL s2 ws` THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back (st:byte list) (8 * ofs + 64 - bc) ml`]
    HUF_NBITS_BOUND) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back (st:byte list) ((8 * ofs + 64 - bc) - nb1) ml`]
    HUF_NBITS_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `ofs = 0 /\ bc + nb1 = 64` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`SND(SND(huf_decode ws ml (st:byte list) r L)) /\
       nb1 <= 8 * ofs + 64 - bc`;
      `(8 * ofs + 64 - bc) - nb1 = 0`; `bc <= 64`;
      `ofs = 0 \/ tl + bc <= 64`; `nb1 <= ml`; `ml <= tl`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`bc + nb1 = 64`; `1 <= nb1`; `1 <= nb2`] THEN
  ARITH_TAC);;

(*** ... and at least one bit for each symbol left ***)

let HUF_DECODE_ROOM2 = prove
 (`!ws ml (st:byte list) r L jj.
        huf_complete ws ml /\
        SND(SND(huf_decode ws ml st r L)) /\
        FST(SND(huf_decode ws ml st r L)) = 0 /\ jj <= L
        ==> L - jj <= FST(SND(huf_decode ws ml st r jj))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS] o check (is_binary "<=" o concl)) THEN
  REWRITE_TAC[ADD_SUB2] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`jj:num`,`jj:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[LE_0]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN X_GEN_TAC `jj:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `jj + 1`) THEN
  REWRITE_TAC[ARITH_RULE `(jj + 1) + d = SUC(jj + d)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND(SND(huf_decode ws ml (st:byte list) r (jj + 1)))`
  MP_TAC THENL
   [MATCH_MP_TAC HUF_DECODE_OK_MONO THEN
    EXISTS_TAC `SUC(jj + d)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HUF_DECODE_SUC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`;
                 `zstd_back (st:byte list)
                    (FST(SND(huf_decode ws ml st r jj))) ml`]
    HUF_NBITS_BOUND) THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND] THEN SIMPLE_ARITH_TAC);;

(*** The shift of the index of the last symbol of a stream, by -tl ***)
(*** without the mask                                             ***)

let T2_JUSHR_NEG = prove
 (`!(y:int64) tl. 1 <= tl /\ tl <= 12
        ==> word_jushr y (word_zx (word_sub (word 0) (word tl):int32)) =
            word_jushr y (word(64 - tl))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_jushr; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD_SUB; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE
   `1 <= tl /\ tl <= 12 <=>
    tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/
    tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The tails of the four streams for a valid stream (HUF_decodeStreamX2      *)
(* inlined, from the check of the order of the outputs): loops of 4 or 5     *)
(* lookups with reloads (tl = 12 or tl <= 11), of one lookup with reloads    *)
(* and without, and the last symbol, as pieces generic in the stream, then   *)
(* their proofs for each stream and the whole tail of each (TAIL2_k_TAIL).   *)
(* ------------------------------------------------------------------------- *)

(*** The tails of the four streams of the slow path, for a valid stream: ***)
(*** the stream st of LENGTH st bytes at src, whose decoding from r has  ***)
(*** exactly L symbols, ending at position 0, to the L bytes at op, with ***)
(*** BIT_DStream at sp - 496 + sofs and the table of 2^tl entries of 4   ***)
(*** bytes at tbl                                                        ***)

let t2_sp = `word_sub stackpointer (word 496):int64`;;

let t2_spk k = mk_comb(mk_comb(`word_add:int64->int64->int64`,t2_sp),
                       mk_comb(`word:num->int64`,mk_small_numeral k));;

let t2_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\
  huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
  1 <= ml /\ ml <= tl /\ 1 <= tl /\ tl <= 12 /\ L < 2 EXP 28 /\
  8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64 /\
  val(op:int64) + L < 2 EXP 64 /\
  SND(SND(huf_decode ws ml st r L)) /\
  FST(SND(huf_decode ws ml st r L)) = 0 /\
  nonoverlapping (op,L) (src,LENGTH st) /\
  nonoverlapping (op,L) (tbl:int64,4 * 2 EXP tl) /\
  nonoverlapping (op,L) (word_sub stackpointer (word 496),496) /\
  nonoverlapping (op,L) (word pc,32000) /\
  nonoverlapping (word_sub stackpointer (word 496),496) (src,LENGTH st) /\
  nonoverlapping (word_sub stackpointer (word 496),496)
                 (tbl,4 * 2 EXP tl) /\
  nonoverlapping (word_sub stackpointer (word 496),496) (word pc,32000)`;;

let t2_vars =
 [`pc:num`; `stackpointer:int64`; `src:int64`; `st:byte list`; `op:int64`;
  `L:num`; `tbl:int64`; `tl:num`; `ws:num list`; `ml:num`; `r:num`;
  `x25:int64`; `x26:int64`; `e:uarch_event list`];;

let t2_win = `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                   2 EXP 64):int64`;;

(*** The good state of jj symbols decoded, at ofs with bc bits used ***)

let t2_good jj =
  subst [jj,`jj:num`]
  `SND(SND(huf_decode ws ml st r jj)) /\
   FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   read (memory :> bytes(op,jj)) s =
   num_of_bytelist(FST(huf_decode ws ml (st:byte list) r jj))`;;

(*** The code of the function, and its simulation, as FL2_STEP_TAC: the ***)
(*** small words normalized only in the values that a step changed       ***)

let ML2_STEP_TAC n =
  let flags = [`NF`; `ZF`; `CF`; `VF`; `PC`; `events`] in
  let reads s asl = mapfilter (fun (_,th) ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
        when s' = s -> (c,v)
    | _ -> fail()) asl in
  let evc = `events` in
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),(Const(_,_) as c)),
                                    s')),t)
          when s' = s && not(c = evc) -> can (find_term is_cond) t
      | _ -> false) asl in
  fun (asl0,w0 as gl) ->
    let old = reads (rand w0) asl0 in
    (ARM_STEPS_TAC SLOW2_EXEC [n] THEN
     (fun (asl,w as gl) ->
        let s = rand w in
        let conv = ZSTD_SMALL_WORD_CONV asl in
        let rule th =
          match concl th with
            Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),v)
              when s' = s && not(mem c flags) && not(mem (c,v) old) ->
                CONV_RULE (RAND_CONV
                  (REWRITE_CONV[WORD_ADD_ASSOC_NUM] THENC conv)) th
          | _ -> th in
        RULE_ASSUM_TAC rule gl) THEN
     (fun gl -> if conditional gl then
                  (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                   TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                     WORD_CMP_64_SFLAGS) THEN
                   TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                   PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                   TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
                else ALL_TAC gl)) gl;;

let ML2_STEPS_TAC ns = MAP_EVERY ML2_STEP_TAC ns;;

(*** The lookup of the table at state s with the container c of the ***)
(*** stream at ofs, bc bits used: the index of the specification     ***)
(*** when the bits are in the container, and the bytes of its entry  ***)

let ML2_INDEX = prove
 (`!(st:byte list) ofs bc tl c.
        c = (num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64 /\
        bc < 64 /\ 1 <= tl /\ tl <= 12 /\ (tl + bc <= 64 \/ ofs = 0)
        ==> word_shl (word_jushr (word_jshl (word c:int64) (word bc))
                                 (word (64 - tl))) 2 =
            word(4 * zstd_back st (8 * ofs + 64 - bc) tl)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[word_shl] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `val(word_jushr
          (word_jshl
            (word ((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                   2 EXP 64):int64) (word bc))
          (word (64 - tl))) =
    zstd_back st (8 * ofs + 64 - bc) tl`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ML_INDEX_COND THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXP_2] THEN ARITH_TAC]);;

(*** Stream 1's tail, the main loop for tl = 12 (4 lookups between ***)
(*** reloads): the body at 0x3b08, with room for 8 more bytes       ***)

let t2_rr = `[src,LENGTH(st:byte list); tbl,4 * 2 EXP tl;
              word_sub stackpointer (word 496),496]:(int64#num)list`
and t2_wr1 = `[op,L; word_add (word_sub stackpointer (word 496)) (word 224),24;
               word_add (word_sub stackpointer (word 496)) (word 64),16]
              :(int64#num)list`;;

let t2_frame1 =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X16; X17; X19; X21; X22; X25; X26;
             X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op,L);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 224),24);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),16)]`;;

let mk_t2_goal frame extra pre post =
  let tm = mk_imp(t2_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; frame]) in
  let vs = t2_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_t2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let t2_common1 =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read SP s = word_sub stackpointer (word 496) /\
  read X5 s = tbl /\ read X12 s = word_add op (word L) /\
  read X18 s = src /\ read X28 s = word_add src (word 8) /\
  read X23 s = word tl /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable2 ws ml tl)`;;

let t2_b4pre1 = with_memsafe t2_rr t2_wr1 (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x3b08)`; t2_common1;
  `read X19 s = word_add op (word jj) /\
   read X3 s = word_add src (word ofs) /\
   read X0 s = word bc /\ read X2 s = word 1 /\
   read X25 s = word_add op (word (L - 7)) /\
   read X16 s = word(64 - tl)`;
  mk_eq(`read X1 s`,t2_win);
  `bc <= 7 /\ jj + 8 <= L /\ (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list))`;
  t2_good `jj:num`]));;

let t2_b4goal1 = mk_t2_goal t2_frame1 [`jj:num`; `ofs:num`; `bc:num`]
  t2_b4pre1 t2_b4pre1;;

(*** The lookups of the slow path, numbered as the simulation goes: the ***)
(*** index of the specification from the container and the bits used   ***)
(*** (the bits in the container), the entry and its bytes               ***)

let ml2_counter = ref 0;;

let ML2_INDEX' = prove
 (`!(st:byte list) ofs bc tl c.
        c = (num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64 /\
        bc < 64 /\ 1 <= tl /\ tl <= 12 /\ (tl + bc <= 64 \/ ofs = 0)
        ==> word_shl (word_jushr (word (2 EXP bc * c):int64)
                                 (word (64 - tl))) 2 =
            word(4 * zstd_back st (8 * ofs + 64 - bc) tl)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `word (2 EXP bc * c):int64 = word_jshl (word c) (word bc)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ML_JSHL_SMALL THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    MATCH_MP_TAC ML2_INDEX THEN ASM_REWRITE_TAC[]]);;

let ml2_index_pat =
  `word_shl (word_jushr (word_jshl (word c) (word b):int64)
                        (word (64 - tl))) 2`
and ml2_index_pat' =
  `word_shl (word_jushr (word (2 EXP b * c):int64) (word (64 - tl))) 2`;;

let ml2_window_pat =
  `(num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64`
and ml2_window_pat_n =
  `(num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
   18446744073709551616`
and ml2_window_pat0 =
  `(num_of_bytelist (st:byte list) DIV 1) MOD 18446744073709551616`;;

(*** Arithmetic from the facts of the given forms only, connected to the ***)
(*** variables of the goal by variables other than tl and ml (so that a  ***)
(*** stream of the main loop only uses its own facts); the cases of the  ***)
(*** length of an entry are left out, its bounds being there, and the    ***)
(*** facts with conditionals (the statuses of the main loop)             ***)

let ML2_ARITH_TAC : tactic =
  let glob = [`tl:num`; `ml:num`] in
  fun (asl,w as gl) ->
    let rel t =
      (is_binary "<=" t || is_binary "<" t || is_binary "=" t) &&
      type_of(lhand t) = `:num` in
    let rec rel' t =
      rel t || is_neg t && rel(dest_neg t) ||
      (is_disj t || is_imp t) && rel'(lhand t) && rel'(rand t) in
    let len_cases t =
      is_disj t && is_eq(lhand t) && is_eq(rand t) &&
      lhs(lhand t) = lhs(rand t) && rhs(lhand t) = `1` &&
      rhs(rand t) = `2` in
    let ok t =
      rel' t && not(len_cases t) && not(can (find_term is_cond) t) &&
      not(exists (fun v -> type_of v = `:armstate`) (frees t)) &&
      not(can (find_term (fun u -> is_const u &&
            mem (fst(dest_const u))
              ["huf_decode"; "zstd_back"; "huf_dentry2"; "EL";
               "num_of_bytelist"])) t) in
    let ths = filter (fun th -> ok(concl th))
                (List.concat(map (CONJUNCTS o snd) asl)) in
    let fv th = subtract (frees(concl th)) glob in
    let rec close vs acc rest =
      let nw,rest' = partition (fun th -> let f = fv th in
                       f = [] || intersect f vs <> []) rest in
      if nw = [] then acc
      else close (itlist (union o fv) nw vs) (nw @ acc) rest' in
    let ths' = close (subtract (frees w) glob) [] ths in
    (MAP_EVERY MP_TAC ths' THEN ARITH_TAC) gl;;

let ML2_INDEX_ONE_TAC (t:term) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let jform = can (term_match [] ml2_index_pat) t in
    let _,tmi,_ = term_match [] (if jform then ml2_index_pat
                                 else ml2_index_pat') t in
    let inst v = try rev_assoc v tmi with Failure _ -> v in
    let c = inst `c:num` and b = inst `b:num` in
    let wth =
      try snd(find (fun (_,th) -> let u = concl th in
                     is_eq u && rhs u = c &&
                     can (term_match [] ml2_window_pat) (lhs u)) asl)
      with Failure _ ->
      if can (term_match [] ml2_window_pat) c then REFL c else
      if can (term_match [] ml2_window_pat0) c then
        let _,wmi,_ = term_match [] ml2_window_pat0 c in
        let stv = try rev_assoc `st:byte list` wmi
                  with Failure _ -> `st:byte list` in
        let w2 = subst [stv,`st:byte list`; `0`,`ofs:num`] ml2_window_pat in
        NUM_REDUCE_CONV w2 else
        let _,wmi,_ = term_match [] ml2_window_pat_n c in
        let winst v = try rev_assoc v wmi with Failure _ -> v in
        let w2 = subst [winst `st:byte list`,`st:byte list`;
                        winst `ofs:num`,`ofs:num`] ml2_window_pat in
        NUM_REDUCE_CONV w2 in
    let _,wmi,_ = term_match [] ml2_window_pat (lhs(concl wth)) in
    let winst v = try rev_assoc v wmi with Failure _ -> v in
    let st = winst `st:byte list` and ofs = winst `ofs:num` in
    incr ml2_counter;
    let k = string_of_int !ml2_counter in
    let idx = mk_var("idx"^k,`:num`) and ev = mk_var("e"^k,`:num list`)
    and av = mk_var("a"^k,`:num`) and bv = mk_var("b"^k,`:num`)
    and nb = mk_var("nb"^k,`:num`) and len = mk_var("len"^k,`:num`) in
    let pos = subst [ofs,`ofs:num`; b,`b:num`] `8 * ofs + 64 - b` in
    let back = list_mk_icomb "zstd_back" [st; pos; `tl:num`] in
    let lt a b = mk_binop `(<):num->num->bool` a b
    and le a b = mk_binop `(<=):num->num->bool` a b in
    let conds = list_mk_conj
      [lt b `64`; `1 <= tl`; `tl <= 12`;
       mk_disj(le (mk_binop `(+):num->num->num` `tl:num` b) `64`,
               mk_eq(ofs,`0`))] in
    let et =
      list_mk_icomb "huf_dentry2" [`ws:num list`; `ml:num`; `tl:num`; idx] in
    let el n = mk_icomb(mk_icomb(`EL:num->num list->num`,mk_small_numeral n),
                        ev) in
    let ttth = try snd(find (fun (_,th) -> concl th = `2 EXP tl = tt`) asl)
               with Failure _ -> REFL `2 EXP tl` in
    let ttr = REWRITE_RULE[ttth] in
    (SUBGOAL_THEN conds (fun cth ->
       RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [st; ofs; b; `tl:num`; c]
                                         (if jform then ML2_INDEX
                                          else ML2_INDEX'))
                                      (CONJ (SYM wth) cth)]))
     THENL [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(SPECL [st; pos; `tl:num`] ZSTD_BACK_BOUND) THEN
     DISCH_THEN(fun bth -> ASSUME_TAC bth THEN ASSUME_TAC(ttr bth)) THEN
     ABBREV_TAC (mk_eq(idx,back)) THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; idx]
       HUF_DENTRY2_BOUNDS) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     MP_TAC(ttr(SPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; idx; s]
       HUF_DTABLE2_READ16)) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     MP_TAC(ttr(SPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; idx; s]
       HUF_DTABLE2_READ)) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[];
       DISCH_THEN(fun rth -> let [r0;_;r2;r3] = CONJUNCTS rth in
         ASSUME_TAC r0 THEN ASSUME_TAC r2 THEN ASSUME_TAC r3)] THEN
     ABBREV_TAC (mk_eq(ev,et)) THEN
     ABBREV_TAC (mk_eq(av,el 0)) THEN ABBREV_TAC (mk_eq(bv,el 1)) THEN
     ABBREV_TAC (mk_eq(nb,el 2)) THEN ABBREV_TAC (mk_eq(len,el 3)) THEN
     FIRST_X_ASSUM(fun bth ->
       if is_conj(concl bth) && free_in len (concl bth) &&
          free_in nb (concl bth)
       then MAP_EVERY ASSUME_TAC (CONJUNCTS bth)
       else NO_TAC) THEN
     SUBGOAL_THEN (list_mk_conj [le `1` len; le len `2`])
       STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC (mk_disj(mk_eq(len,`1`),mk_eq(len,`2`))) THEN ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN (list_mk_conj [lt nb `64`; lt len `256`;
                                 lt (mk_binop `(+):num->num->num` av
                                      (mk_binop `( * ):num->num->num`
                                        `256` bv)) `65536`])
       STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC]) gl;;

let ML2_INDEX_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let tms = setify(List.concat(mapfilter (fun (_,th) ->
      let t = concl th in
      if is_eq t && is_comb(lhs t) && rand(lhs t) = s
      then find_terms (fun u -> can (term_match [] ml2_index_pat) u ||
                                can (term_match [] ml2_index_pat') u) (rhs t)
      else fail()) asl)) in
    MAP_EVERY ML2_INDEX_ONE_TAC tms gl;;

let ML2_NORM_TAC = ML2_INDEX_TAC THEN TRY FL2_MERGE_TAC THEN HUF_HIDE_SUB_TAC;;

(*** After lookups of a stream from the good state at j (stream st from ***)
(*** r, at ofs): the steps of the decoding by ML2_STEP, the position and ***)
(*** the bytes stored as those decoded                                   ***)

let ML2_DECODE_TAC (st:term) (r:term) (ofs:term) (j:term) : tactic =
  fun (asl,w as gl) ->
    let facts = fl_all_facts asl in
    let idxpat = subst [st,`st:byte list`; ofs,`ofs:num`]
      `zstd_back (st:byte list) (8 * ofs + 64 - x) tl = idx` in
    let looks = mapfilter (fun th ->
      let _,tmi,_ = term_match [] idxpat (concl th) in
      let inst v = try rev_assoc v tmi with Failure _ -> v in
      (inst `x:num`,inst `idx:num`,th)) facts in
    let size x = length(striplist (dest_binop `(+):num->num->num`) x) in
    let looks = sort (fun (x,_,_) (y,_,_) -> size x < size y) looks in
    let lfact l = find (fun th -> let t = concl th in is_eq t && lhs t = l)
                       facts in
    let elfact n ev = lfact (mk_icomb(mk_icomb(`EL:num->num list->num`,
                                               mk_small_numeral n),ev)) in
    let dec jt = list_mk_icomb "huf_decode"
                   [`ws:num list`; `ml:num`; st; r; jt] in
    let fst_snd jt = mk_icomb(`FST:num#bool->num`,
                       mk_icomb(`SND:byte list#num#bool->num#bool`,dec jt)) in
    let addac a b =
      if a = b then REFL a else EQT_ELIM(REWRITE_CONV[ADD_AC] (mk_eq(a,b))) in
    let step (jt,posth,ths) (x,idx,ith) =
      let eth = lfact (list_mk_icomb "huf_dentry2"
                         [`ws:num list`; `ml:num`; `tl:num`; idx]) in
      let ev = rhs(concl eth) in
      let ths5 = [ith; eth; elfact 0 ev; elfact 1 ev; elfact 2 ev;
                  elfact 3 ev] in
      let lemma = SPECL [`ws:num list`; `ml:num`; st; r; `L:num`; jt; ofs; x;
                         `tl:num`] ML2_STEP in
      let lemma' =
        REWRITE_RULE ths5 (CONV_RULE(TOP_DEPTH_CONV let_CONV) lemma) in
      let ant = lhand(concl lemma') in
      let cs = conjuncts ant in
      let cpos = el 4 cs in
      let ppos =
        if concl posth = cpos then posth else
        let r = rhs(concl posth) in
        let x' = rand(rand r) and x3 = rand(rand(rhs cpos)) in
        TRANS posth
          (AP_TERM (rator r) (AP_TERM (rator(rand r)) (addac x' x3))) in
      let prove_ant t =
        if t = cpos then ppos
        else try find (fun th -> concl th = t) facts
             with Failure _ -> TAC_PROOF((asl,t),ML2_ARITH_TAC) in
      let th = MP lemma' (end_itlist CONJ (map prove_ant cs)) in
      let [f1;f2;f3;f4] = CONJUNCTS th in
      let lenv = rhs(concl(elfact 3 ev)) in
      let jt' = mk_binop `(+):num->num->num` jt lenv in
      let jn = fl_num_norm jt' in
      let norm th = if jn = jt' then th else
        CONV_RULE(ONCE_DEPTH_CONV(fun t -> if t = jt' then addac jt' jn
                                           else failwith "")) th in
      (jn,norm f3,norm f4 :: norm f1 :: f2 :: ths) in
    let posth0 = lfact (fst_snd j) in
    let jn,posth,ths =
      itlist (fun l acc -> step acc l) (rev looks) (j,posth0,[]) in
    let fths = filter (fun th -> is_eq(concl th) &&
                       is_comb(lhs(concl th)) &&
                       fst(strip_comb(lhs(concl th))) =
                       `FST:byte list#num#bool->byte list`) ths in
    let memth = snd(find (fun (_,th) -> let t = concl th in
      is_eq t &&
      (match lhs t with
         Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
              Comb(Const("bytes",_),ar))),_) ->
           snd(dest_pair ar) = jn &&
           can (find_term ((=) (dec j))) (rhs t)
       | _ -> false)) asl) in
    let memth' = REWRITE_RULE (map SYM fths) memth in
    (MAP_EVERY ASSUME_TAC (posth :: memth' :: ths)) gl;;

(*** The saved x25 and x26 in the frame, and BIT_DStream of stream 1 in ***)
(*** the frame                                                          ***)

let t2_saved1 = list_mk_conj
 [subst [t2_spk 64,`a:int64`] `read (memory :> bytes64 a) s = x25`;
  subst [t2_spk 72,`a:int64`] `read (memory :> bytes64 a) s = x26`];;

let t2_bd1 = list_mk_conj
 [subst [t2_spk 224,`a:int64`; t2_win,`w:int64`]
   `read (memory :> bytes64 a) s = w`;
  subst [t2_spk 232,`a:int64`] `read (memory :> bytes32 a) s = word bc`;
  subst [t2_spk 240,`a:int64`]
   `read (memory :> bytes64 a) s = word_add src (word ofs)`];;

(*** 0x3bb4: the head of the main loop of the tail for tl = 12, before ***)
(*** the reload; BIT_DStream in the frame up to date when w2 = 0       ***)

let t2_r4inv1 = with_memsafe t2_rr t2_wr1
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + 0x3bb4)`; t2_common1; t2_saved1;
    `read X19 s = word_add op (word jj) /\
     read X3 s = word_add src (word ofs) /\
     read X0 s = word bc /\
     read X25 s = word_add op (word (L - 7)) /\
     read X16 s = word(64 - tl)`;
    mk_eq(`read X1 s`,t2_win);
    mk_disj(mk_conj(`read X2 s = word 0`,t2_bd1),`read X2 s = word 1`);
    `7 <= L /\ jj <= L /\ (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list))`;
    t2_good `jj:num`])));;

let t2_b4pre1' = with_memsafe t2_rr t2_wr1 (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x3b08)`; t2_common1; t2_saved1;
  `read X19 s = word_add op (word jj) /\
   read X3 s = word_add src (word ofs) /\
   read X0 s = word bc /\ read X2 s = word 1 /\
   read X25 s = word_add op (word (L - 7)) /\
   read X16 s = word(64 - tl)`;
  mk_eq(`read X1 s`,t2_win);
  `bc <= 7 /\ jj + 8 <= L /\ (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list))`;
  t2_good `jj:num`]));;

let t2_b4goal1' = mk_t2_goal t2_frame1 [`jj:num`; `ofs:num`; `bc:num`]
  t2_b4pre1'
  (mk_abs(`s:armstate`,mk_exists(`m':num`,mk_conj(`m' < L - jj`,
     list_mk_comb(t2_r4inv1,[`m':num`; `s:armstate`])))));;

(*** The tails of the four streams, valid case, generic in the stream: ***)
(*** the registers, the offset of BIT_DStream in the frame and the     ***)
(*** addresses of the cut points                                       ***)

type tail2spec =
 {k2 : int;                     (* the stream                          *)
  sofs2 : int;                  (* BIT_DStream at sp - 496 + sofs2     *)
  regs2 : term;                 (* the registers that the tail changes *)
  op2 : term; end2 : term;      (* the output pointer and its end      *)
  start2 : term; room2 : term;  (* the start of the stream; end - op   *)
  lim2 : term;                  (* the fact: the limit start + 8       *)
  pptr2 : term;                 (* the pointer at the end of the tail  *)
  c4 : term; bc4 : term; p4 : term; f4 : term; e74 : term; sh4 : term;
  bbc4 : term;                  (* bc in the body of the 4 lookups     *)
  c5 : term; bc5 : term; p5 : term; f5 : term; e95 : term; sh5 : term;
  bbc5 : term;
  c1 : term; bc1 : term; p1 : term; f1 : term; e21 : term; sh1 : term;
  lim1 : term;                  (* the fact for the limit in the loop  *)
  pc1 : term;                   (* the copy of the pointer in the loop *)
  c0 : term; bc0 : term; sh0 : term;
  eregs2 : term list;           (* facts of the entry about registers  *)
  extra2 : term list;           (* and after it (the frame)            *)
  wr2 : term list;              (* more regions written                *)
  a_entry : int; a_short : int; a_r4 : int; a_b4 : int; a_r5 : int;
  a_b5 : int; a_mid : int; a_r1 : int; a_after1 : int; a_l0 : int;
  a_last : int; a_post : int;
  a_ret : int};;                (* after the call of the reload        *)

let t2v s = mk_var(s,`:(armstate,int64)component`);;

let t2_spv v =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,t2_sp),
          mk_comb(`word:num->int64`,v));;

let t2_frame_mem off n =
  subst [t2_spk off,`a:int64`; mk_small_numeral n,`n:num`]
    `memory :> bytes(a,n)`;;

let tail2_inst spec tm =
  let num = mk_small_numeral and nv s = mk_var(s,`:num`) in
  vsubst
   ([spec.regs2,`r_regs:((armstate,int64)component)list`] @
    map (fun (t,s) -> t,t2v s)
     [spec.op2,"r_op"; spec.end2,"r_end"; spec.start2,"r_start";
      spec.room2,"r_room"; spec.pptr2,"r_pptr";
      spec.c4,"r_c4"; spec.bc4,"r_bc4"; spec.p4,"r_p4"; spec.f4,"r_f4";
      spec.e74,"r_e74"; spec.sh4,"r_sh4"; spec.bbc4,"r_bbc4";
      spec.c5,"r_c5"; spec.bc5,"r_bc5"; spec.p5,"r_p5"; spec.f5,"r_f5";
      spec.e95,"r_e95"; spec.sh5,"r_sh5"; spec.bbc5,"r_bbc5";
      spec.c1,"r_c1"; spec.bc1,"r_bc1"; spec.p1,"r_p1"; spec.f1,"r_f1";
      spec.e21,"r_e21"; spec.sh1,"r_sh1"; spec.pc1,"r_pc1";
      spec.c0,"r_c0"; spec.bc0,"r_bc0"; spec.sh0,"r_sh0"] @
    map (fun (n,s) -> num n,nv s)
     [spec.a_entry,"a_entry"; spec.a_short,"a_short"; spec.a_r4,"a_r4";
      spec.a_b4,"a_b4"; spec.a_r5,"a_r5"; spec.a_b5,"a_b5";
      spec.a_mid,"a_mid"; spec.a_r1,"a_r1"; spec.a_after1,"a_after1";
      spec.a_l0,"a_l0"; spec.a_last,"a_last"; spec.a_post,"a_post";
      spec.sofs2,"s_c"; spec.sofs2 + 8,"s_b"; spec.sofs2 + 16,"s_p"])
   tm;;

let t2_lim_mem off =
  subst [t2_spk off,`a:int64`]
   `read (memory :> bytes64 a) s = word_add src (word 8)`;;

let tail2_1 =
 {k2 = 1; sofs2 = 224;
  regs2 = `[PC; X0; X1; X2; X3; X4; X16; X17; X19; X21; X22; X25; X26;
            X30]`;
  op2 = `X19`; end2 = `X12`; start2 = `X18`; room2 = `X21`;
  lim2 = `read X28 s = word_add src (word 8)`; pptr2 = `X21`;
  c4 = `X1`; bc4 = `X0`; p4 = `X3`; f4 = `X2`; e74 = `X25`; sh4 = `X16`;
  bbc4 = `X0`;
  c5 = `X1`; bc5 = `X0`; p5 = `X3`; f5 = `X2`; e95 = `X26`; sh5 = `X4`;
  bbc5 = `X0`;
  c1 = `X2`; bc1 = `X0`; p1 = `X21`; f1 = `X3`; e21 = `X4`; sh1 = `X16`;
  lim1 = `read X28 s = word_add src (word 8)`;
  pc1 = `X17`;
  c0 = `X16`; bc0 = `X2`; sh0 = `X3`;
  eregs2 = [`read X25 s = x25 /\ read X26 s = x26`];
  extra2 = [t2_saved1];
  wr2 = [`word_add (word_sub stackpointer (word 496)) (word 64):int64,16`];
  a_entry = 0x3ab4; a_short = 0x4b50; a_r4 = 0x3bb4; a_b4 = 0x3b08;
  a_r5 = 0x51c4; a_b5 = 0x50f0; a_mid = 0x3bfc; a_r1 = 0x3c7c;
  a_after1 = 0x3cc0; a_l0 = 0x3cd8; a_last = 0x3d0c; a_post = 0x3d64;
  a_ret = 0x5274};;

let tail2_2 =
 {k2 = 2; sofs2 = 264;
  regs2 = `[PC; X0; X1; X2; X3; X4; X7; X12; X16; X17; X19; X22; X25;
            X30]`;
  op2 = `X7`; end2 = `X13`; start2 = `X15`; room2 = `X19`;
  lim2 = t2_lim_mem 96; pptr2 = `X12`;
  c4 = `X2`; bc4 = `X0`; p4 = `X4`; f4 = `X3`; e74 = `X16`; sh4 = `X12`;
  bbc4 = `X1`;
  c5 = `X2`; bc5 = `X0`; p5 = `X4`; f5 = `X3`; e95 = `X16`; sh5 = `X12`;
  bbc5 = `X1`;
  c1 = `X2`; bc1 = `X0`; p1 = `X12`; f1 = `X3`; e21 = `X4`; sh1 = `X16`;
  lim1 = `read X22 s = word_add src (word 8)`;
  pc1 = `X17`;
  c0 = `X16`; bc0 = `X3`; sh0 = `X2`;
  eregs2 = []; extra2 = []; wr2 = [];
  a_entry = 0x3d64; a_short = 0x49f4; a_r4 = 0x3e60; a_b4 = 0x3db4;
  a_r5 = 0x4f04; a_b5 = 0x4e30; a_mid = 0x3eac; a_r1 = 0x3f30;
  a_after1 = 0x3f74; a_l0 = 0x3f8c; a_last = 0x3fc0; a_post = 0x4018;
  a_ret = 0x52e0};;

let tail2_3 =
 {k2 = 3; sofs2 = 304;
  regs2 = `[PC; X0; X1; X2; X3; X4; X6; X7; X13; X16; X17; X19; X22;
            X30]`;
  op2 = `X6`; end2 = `X11`; start2 = `X9`; room2 = `X13`;
  lim2 = t2_lim_mem 104; pptr2 = `X7`;
  c4 = `X2`; bc4 = `X0`; p4 = `X4`; f4 = `X3`; e74 = `X13`; sh4 = `X7`;
  bbc4 = `X1`;
  c5 = `X2`; bc5 = `X0`; p5 = `X4`; f5 = `X3`; e95 = `X13`; sh5 = `X7`;
  bbc5 = `X1`;
  c1 = `X2`; bc1 = `X0`; p1 = `X13`; f1 = `X3`; e21 = `X4`; sh1 = `X16`;
  lim1 = `read X19 s = word_add src (word 8)`;
  pc1 = `X7`;
  c0 = `X16`; bc0 = `X1`; sh0 = `X3`;
  eregs2 = []; extra2 = []; wr2 = [];
  a_entry = 0x4018; a_short = 0x4adc; a_r4 = 0x4114; a_b4 = 0x4068;
  a_r5 = 0x4db4; a_b5 = 0x4ce0; a_mid = 0x4160; a_r1 = 0x41e4;
  a_after1 = 0x422c; a_l0 = 0x4244; a_last = 0x4278; a_post = 0x42d0;
  a_ret = 0x524c};;

let tail2_4 =
 {k2 = 4; sofs2 = 344;
  regs2 = `[PC; X0; X1; X2; X3; X4; X6; X8; X10; X11; X13; X16; X17;
            X19; X30]`;
  op2 = `X10`; end2 = `X14`; start2 = `X24`; room2 = `X6`;
  lim2 = t2_lim_mem 112; pptr2 = `X3`;
  c4 = `X2`; bc4 = `X0`; p4 = `X4`; f4 = `X3`; e74 = `X11`; sh4 = `X6`;
  bbc4 = `X0`;
  c5 = `X2`; bc5 = `X0`; p5 = `X4`; f5 = `X3`; e95 = `X11`; sh5 = `X6`;
  bbc5 = `X0`;
  c1 = `X2`; bc1 = `X0`; p1 = `X3`; f1 = `X8`; e21 = `X4`; sh1 = `X11`;
  lim1 = `read X17 s = word_add src (word 8)`;
  pc1 = `X1`;
  c0 = `X11`; bc0 = `X1`; sh0 = `X6`;
  eregs2 = [subst [t2_spk 120,`a:int64`]
             `read (memory :> bytes64 a) s =
              word_sub (word_add op (word L)) (word 7)`];
  extra2 = []; wr2 = [];
  a_entry = 0x42d0; a_short = 0x4a68; a_r4 = 0x43cc; a_b4 = 0x4320;
  a_r5 = 0x5054; a_b5 = 0x4f80; a_mid = 0x4418; a_r1 = 0x4498;
  a_after1 = 0x44d8; a_l0 = 0x44f0; a_last = 0x4524; a_post = 0x457c;
  a_ret = 0x52b8};;

(*** The frame and the regions written of a tail ***)

let tail2_wr spec =
  mk_list(`op:int64,L:num` ::
          subst [t2_spk spec.sofs2,`a:int64`] `a:int64,24` :: spec.wr2,
          `:int64#num`);;

let tail2_frame spec =
  let mems = map (fun t -> let a,n = dest_pair t in
                    subst [a,`a:int64`; n,`n:num`] `memory :> bytes(a,n)`)
                 (dest_list(tail2_wr spec)) in
  list_mk_icomb ",,"
   [list_mk_icomb "MAYCHANGE" [spec.regs2];
    list_mk_icomb ",,"
     [`MAYCHANGE [NF; ZF; CF; VF]`;
      list_mk_icomb ",,"
       [`MAYCHANGE [events]`;
        list_mk_icomb "MAYCHANGE"
         [mk_list(mems,type_of(hd mems))]]]];;

let mk_tail2_goal spec extra pre post =
  let pre' = tail2_inst spec pre and post' = tail2_inst spec post in
  let tm = mk_imp(t2_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; pre'; post'; tail2_frame spec]) in
  let vs = t2_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_tail2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let with_tail2_memsafe spec tm =
  with_memsafe t2_rr (tail2_wr spec) tm;;

(*** The facts that hold all through, and BIT_DStream in the frame ***)

let t2c_common spec = list_mk_conj
 [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
   read SP s = word_sub stackpointer (word 496) /\
   read X5 s = tbl /\ read (r_end:tailreg) s = word_add op (word L) /\
   read (r_start:tailreg) s = src`;
  spec.lim2;
  `read X23 s = word tl /\
   read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
   read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
   num_of_bytelist(huf_dtable2 ws ml tl)`];;

let t2c_common_x spec = list_mk_conj(t2c_common spec :: spec.extra2);;

let t2c_bd = list_mk_conj
 [subst [t2_spv `s_c:num`,`a:int64`; t2_win,`w:int64`]
   `read (memory :> bytes64 a) s = w`;
  subst [t2_spv `s_b:num`,`a:int64`] `read (memory :> bytes32 a) s = word bc`;
  subst [t2_spv `s_p:num`,`a:int64`]
   `read (memory :> bytes64 a) s = word_add src (word ofs)`];;

(*** ... without the pointer, which stream 4 does not store back after ***)
(*** the loop of one lookup                                            ***)

let t2c_bd2 = list_mk_conj
 [subst [t2_spv `s_c:num`,`a:int64`; t2_win,`w:int64`]
   `read (memory :> bytes64 a) s = w`;
  subst [t2_spv `s_b:num`,`a:int64`]
   `read (memory :> bytes32 a) s = word bc`];;

let t2c_ofsok = `ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)`;;

(*** The entry, with BIT_DStream in the frame, and the output not at 0 ***)
(*** (else the end less 9 of an output of 8 bytes wraps around, the    ***)
(*** loop of 5 lookups going on)                                       ***)

let t2c_entry spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_conj
   ([`read PC s = word(pc + a_entry)`; t2c_common spec] @ spec.eregs2 @
    [`read (r_op:tailreg) s = word_add op (word jj)`; t2c_bd;
     `jj <= L /\ ~(val(op:int64) = 0)`; t2c_ofsok; t2_good `jj:num`])));;

(*** 0x3bfc (stream 1): after the main loop of the tail, with BIT_DStream ***)
(*** in the frame and the room left in r_room                              ***)

let t2c_mid spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`read PC s = word(pc + a_mid)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_room:tailreg) s = word(L - jj)`; t2c_bd;
    `jj <= L /\ (ofs = 0 \/ bc <= 7)`; t2c_ofsok; t2_good `jj:num`])));;

(*** The head of the main loop of the tail for tl = 12 (4 lookups), and ***)
(*** its body, with room for 8 more bytes                               ***)

let t2c_r4inv spec = with_tail2_memsafe spec
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + a_r4)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_p4:tailreg) s = word_add src (word ofs) /\
     read (r_bc4:tailreg) s = word bc /\
     read (r_e74:tailreg) s = word_add op (word (L - 7)) /\
     read (r_sh4:tailreg) s = word(64 - tl)`;
    mk_eq(`read (r_c4:tailreg) s`,t2_win);
    mk_disj(mk_conj(`read (r_f4:tailreg) s = word 0`,t2c_bd),
            `read (r_f4:tailreg) s = word 1`);
    `7 <= L /\ jj <= L`; t2c_ofsok; t2_good `jj:num`])));;

let t2c_b4pre spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_conj
   [`read PC s = word(pc + a_b4)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_p4:tailreg) s = word_add src (word ofs) /\
     read (r_bbc4:tailreg) s = word bc /\
     read (r_f4:tailreg) s = word 1 /\
     read (r_e74:tailreg) s = word_add op (word (L - 7)) /\
     read (r_sh4:tailreg) s = word(64 - tl)`;
    mk_eq(`read (r_c4:tailreg) s`,t2_win);
    `bc <= 7 /\ jj + 8 <= L`; t2c_ofsok; t2_good `jj:num`]));;

let t2c_b4_goal spec = mk_tail2_goal spec [`jj:num`; `ofs:num`; `bc:num`]
  (t2c_b4pre spec)
  (mk_abs(`s:armstate`,mk_exists(`m':num`,mk_conj(`m' < L - jj`,
     list_mk_comb(t2c_r4inv spec,[`m':num`; `s:armstate`])))));;

let t2c_r4_goal spec = mk_tail2_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2c_r4inv spec,[`m:num`; `s:armstate`]))))
  (t2c_mid spec);;

(*** The same for tl <= 11 (5 lookups), with room for 10 more bytes ***)

let t2_r45_subst tm =
  let nv s = mk_var(s,`:num`) in
  subst ([`L - 9`,`L - 7`; `9 <= L /\ tl <= 11`,`7 <= L`;
          `jj + 10 <= L /\ tl <= 11`,`jj + 8 <= L`;
          nv "a_r5",nv "a_r4"; nv "a_b5",nv "a_b4"] @
         map (fun (a,b) -> t2v b,t2v a)
          ["r_c4","r_c5"; "r_bc4","r_bc5"; "r_p4","r_p5"; "r_f4","r_f5";
           "r_e74","r_e95"; "r_sh4","r_sh5"; "r_bbc4","r_bbc5"]) tm;;

let t2c_r5inv spec = t2_r45_subst(t2c_r4inv spec)
and t2c_b5pre spec = t2_r45_subst(t2c_b4pre spec);;

let t2c_b5_goal spec = mk_tail2_goal spec [`jj:num`; `ofs:num`; `bc:num`]
  (t2c_b5pre spec)
  (mk_abs(`s:armstate`,mk_exists(`m':num`,mk_conj(`m' < L - jj`,
     list_mk_comb(t2c_r5inv spec,[`m':num`; `s:armstate`])))));;

let t2c_r5_goal spec = mk_tail2_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2c_r5inv spec,[`m:num`; `s:armstate`]))))
  (t2c_mid spec);;

(*** The loop of one lookup between reloads, with room for 2 more   ***)
(*** bytes: before its first reload, BIT_DStream in the frame and the ***)
(*** copy of the pointer up to date whatever the flag (which stream 4 ***)
(*** does not set before the loop); its exit with BIT_DStream in the  ***)
(*** frame but the pointer                                            ***)

let t2c_r1inv spec = with_tail2_memsafe spec
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + a_r1)`; t2c_common_x spec; spec.lim1;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_p1:tailreg) s = word_add src (word ofs) /\
     read (r_bc1:tailreg) s = word bc /\
     read (r_e21:tailreg) s = word_add op (word (L - 2)) /\
     read (r_sh1:tailreg) s = word(64 - tl)`;
    mk_eq(`read (r_c1:tailreg) s`,t2_win);
    mk_disj(mk_conj(t2c_bd,
                    `read (r_pc1:tailreg) s = word_add src (word ofs)`),
            `read (r_f1:tailreg) s = word 1`);
    `2 <= L /\ jj <= L`; t2c_ofsok; t2_good `jj:num`])));;

let t2c_after1 spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`read PC s = word(pc + a_after1)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_e21:tailreg) s = word_add op (word (L - 2)) /\
     read (r_pptr:tailreg) s = word_add src (word ofs)`; t2c_bd2;
    `2 <= L /\ jj <= L /\ (L < jj + 2 \/ ofs = 0) /\
     (ofs = 0 \/ bc <= 7)`; t2c_ofsok;
    t2_good `jj:num`])));;

let t2c_r1_goal spec = mk_tail2_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2c_r1inv spec,[`m:num`; `s:armstate`]))))
  (t2c_after1 spec);;

(*** Simulation with normalization up to one of the given addresses, as ***)
(*** long as the branches are decided                                    ***)

let ML2_SIM_UNTIL_TAC stops =
  let num_of_state s =
    let n = fst(dest_var s) in
    int_of_string(String.sub n 1 (String.length n - 1)) in
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k n (asl,w as gl) =
    let pc = current_pc gl in
    if mem pc stops then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "ML2_SIM_UNTIL_TAC"
    else (ML2_STEP_TAC n THEN ML2_NORM_TAC THEN run (k - 1) (n + 1)) gl in
  fun (asl,w as gl) -> run 200 (num_of_state(rand w) + 1) gl;;

(*** The value v in read c s = word_add b (word v) or word v ***)

let t2_regval (asl:(string*thm)list) (s:term) (c:term) =
  let t = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
            is_eq t && lhs t = list_mk_icomb "read" [c; s]) asl))) in
  match t with
    Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),v)) -> v
  | Comb(Const("word",_),v) -> v
  | _ -> failwith "t2_regval";;

(*** The state of the facts about a register ***)

let t2_state (asl:(string*thm)list) (c:term) =
  let rc = mk_icomb(`read:((armstate,int64)component)->armstate->int64`,c) in
  rand(lhs(concl(snd(find (fun (_,th) -> let t = concl th in
    is_eq t && is_comb(lhs t) && rator(lhs t) = rc) asl))));;

(*** The room left in the output ***)

let T2_ROOM = prove
 (`!(op:int64) L jj. jj <= L
        ==> word_sub (word_add op (word L)) (word_add op (word jj)) =
            word(L - jj)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add (op:int64) a) (word_add op b) =
                         word_sub a b`] THEN
  ASM_SIMP_TAC[WORD_SUB]);;

(*** The conjuncts of the invariants ***)

let T2_CONJ_TAC =
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) -> if is_disj w &&
         can (find_term (fun t -> t = `word 1:int64`)) (rand w)
       then DISJ2_TAC else NO_TAC)) THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC;
         ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
         ML2_ARITH_TAC;
         ASM_REWRITE_TAC[] THEN ML2_ARITH_TAC;
         MATCH_MP_TAC T2_ROOM THEN ML2_ARITH_TAC;
         MATCH_MP_TAC T4_SUB_ADDR THEN ML2_ARITH_TAC];;

(*** The body of the main loop of the tail: 4 lookups, then the head ***)

let TAIL2_INIT_TAC =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  ABBREV_TAC `c = (num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                  2 EXP 64` THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  (fun gl -> ml2_counter := 0; ALL_TAC gl);;

let TAIL2_BODY_TAC spec a_head bcreg =
  TAIL2_INIT_TAC THEN ML2_SIM_UNTIL_TAC [a_head] THEN
  ML2_DECODE_TAC `st:byte list` `r:num` `ofs:num` `jj:num` THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  W(fun (asl,w) ->
    let s = t2_state asl spec.op2 in
    let jv = fl_num_norm(t2_regval asl s spec.op2)
    and bv = t2_regval asl s bcreg in
    EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jv) THEN
    CONJ_TAC THENL
     [ML2_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [jv; `ofs:num`; bv] THEN T2_CONJ_TAC]);;

(*** The reload at the head of a loop of the tail, from the state at ofs ***)
(*** with bc bits used: normal (at least 8 bytes after the start), at the ***)
(*** start, or the partial reload that stops at the start or not         ***)

let TAIL2_SLICE_TAC ofs' = W(fun (asl,w) -> T4_SLICE_TAC ofs' (rand w));;

let T2_RELOAD_CASES_TAC (tac:term -> term -> tactic)
                        (tac0:term -> term -> tactic) =
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ML2_ARITH_TAC ORELSE
      (MP_TAC(ASSUME t2c_ofsok) THEN MP_TAC(ASSUME `8 <= ofs`) THEN ARITH_TAC);
      ALL_TAC] THEN
    TAIL2_SLICE_TAC `ofs - bc DIV 8` THEN
    tac `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL [tac0 `ofs:num` `bc:num`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN MP_TAC(ASSUME `~(ofs = 0)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [TAIL2_SLICE_TAC `ofs - bc DIV 8` THEN
    tac `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    TAIL2_SLICE_TAC `0` THEN tac0 `0` `bc - 8 * ofs`];;

(*** The values of op + k for the comparisons of the output pointer ***)

let T2_OPVAL_TAC ks =
  MAP_EVERY (fun k ->
    let th = SPECL [`op:int64`; k] VAL_WORD_ADD_NOWRAP in
    MP_TAC th THEN ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN ML2_ARITH_TAC; DISCH_TAC]) ks;;

(*** The loop at the head a_head with the body body_th at a_body for room ***)
(*** room <= L - jj, exiting to a_mid with BIT_DStream in the frame       ***)

let TAIL2_TO_BODY_TAC body_th a_body ofs' bc' =
  ML2_SIM_UNTIL_TAC [a_body] THEN FL_EXPAND_POST_TAC THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m':num`
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    DISJ1_TAC THEN EXISTS_TAC `m':num` THEN CONJ_TAC THENL
     [ML2_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC])
   body_th [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

let TAIL2_TO_MID_TAC a_mid ofs' bc' =
  ML2_SIM_UNTIL_TAC [a_mid] THEN FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`jj:num`; ofs'; bc'] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

let TAIL2_LOOP_TAC spec (fl:term) room a_body a_mid body_th =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs <= LENGTH(st:byte list)`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  T2_OPVAL_TAC [`jj:num`; mk_binop `(-):num->num->num` `L:num`
                   (mk_small_numeral(dest_small_numeral room - 1))] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
                     can (find_term ((=) fl)) (concl th))) THEN
  T2_RELOAD_CASES_TAC
   (fun ofs' bc' ->
      ASM_CASES_TAC (mk_binop `(<=):num->num->bool`
                       (mk_binop `(+):num->num->num` `jj:num` room) `L:num`)
      THENL [TAIL2_TO_BODY_TAC body_th a_body ofs' bc';
             TAIL2_TO_MID_TAC a_mid ofs' bc'])
   (TAIL2_TO_MID_TAC a_mid);;

(*** The loop of one lookup between reloads: after the reload the lookup ***)
(*** and back to the head, or the exit with BIT_DStream in the frame     ***)

let ML2_SIM_UNTIL1_TAC stops =
  W(fun (asl,w) ->
    let n = let v = fst(dest_var(rand w)) in
            int_of_string(String.sub v 1 (String.length v - 1)) in
    ML2_STEP_TAC (n + 1) THEN ML2_NORM_TAC THEN ML2_SIM_UNTIL_TAC stops);;

(*** The same, splitting the cases of the branches not decided (the ***)
(*** flag not set before the loop of one lookup of stream 4)          ***)

let ML2_SIM_SPLIT_UNTIL_TAC stops =
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k (asl,w as gl) =
    let pc = current_pc gl in
    let s = rand w in
    if mem pc stops then ALL_TAC gl
    else if k = 0 then failwith "ML2_SIM_SPLIT_UNTIL_TAC"
    else if is_cond pc then
      let c = lhand(rator pc) in
      let pcl = mk_comb(`read PC`,s) in
      (ASM_CASES_TAC c THEN
       POP_ASSUM(fun cth ->
         FIRST_X_ASSUM(fun th ->
           if is_eq(concl th) && lhs(concl th) = pcl
           then ASSUME_TAC(REWRITE_RULE[cth] th) else NO_TAC)) THEN
       run (k - 1)) gl
    else
      let n = let v = fst(dest_var s) in
              int_of_string(String.sub v 1 (String.length v - 1)) in
      (ML2_STEP_TAC (n + 1) THEN ML2_NORM_TAC THEN run (k - 1)) gl in
  run 200;;

let TAIL2_L1_LOOK_TAC spec ofs' bc' =
  let pos = subst [ofs',`ofs':num`; bc',`bc':num`]
    `FST(SND(huf_decode ws ml (st:byte list) r jj)) = 8 * ofs' + 64 - bc'` in
  SUBGOAL_THEN pos ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ML2_ARITH_TAC; ALL_TAC] THEN
  (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  ML2_SIM_UNTIL1_TAC [spec.a_r1] THEN
  ML2_DECODE_TAC `st:byte list` `r:num` ofs' `jj:num` THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
  W(fun (asl,w) ->
    let s = t2_state asl spec.op2 in
    let jv = fl_num_norm(t2_regval asl s spec.op2)
    and bv = t2_regval asl s spec.bc1 in
    EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jv) THEN
    CONJ_TAC THENL
     [ML2_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [jv; ofs'; bv] THEN T2_CONJ_TAC]);;

(*** A variable for the value of the register c if it is not known, so ***)
(*** that the conditions on it do not refer to an old state            ***)

let T2_REG_ABBREV_TAC (c:term) : tactic =
  fun (asl,w as gl) ->
    let rc = list_mk_icomb "read" [c; rand w] in
    if exists (fun (_,th) -> let t = concl th in is_eq t && lhs t = rc) asl
    then ALL_TAC gl
    else ABBREV_TAC (mk_eq(mk_var("fv",type_of rc),rc)) gl;;

let TAIL2_TO_AFTER_TAC spec ofs' bc' =
  T2_REG_ABBREV_TAC spec.f1 THEN
  ML2_SIM_SPLIT_UNTIL_TAC [spec.a_after1] THEN FL_EXPAND_POST_TAC THEN
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`jj:num`; ofs'; bc'] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

let TAIL2_L1_TAC spec =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs <= LENGTH(st:byte list)`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  T2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
                     can (find_term ((=) spec.f1)) (concl th))) THEN
  T2_RELOAD_CASES_TAC
   (fun ofs' bc' ->
      ASM_CASES_TAC `jj + 2 <= L` THENL
       [TAIL2_L1_LOOK_TAC spec ofs' bc';
        TAIL2_TO_AFTER_TAC spec ofs' bc'])
   (TAIL2_TO_AFTER_TAC spec);;

(*** The loop without reloads at the start of the stream (2 more bytes ***)
(*** of room each time), the last symbol and the end of the tail        ***)

let t2_win0 = subst [`0`,`ofs:num`] t2_win;;

let t2c_bd0 =
  subst [t2_spv `s_c:num`,`a:int64`; t2_win0,`w:int64`]
   `read (memory :> bytes64 a) s = w`;;

let t2c_l0inv spec = with_tail2_memsafe spec
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + a_l0)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_e21:tailreg) s = word_add op (word (L - 2)) /\
     read (r_bc0:tailreg) s = word bc /\
     read (r_sh0:tailreg) s = word(64 - tl) /\
     read (r_pptr:tailreg) s = word_add src (word 0)`;
    mk_eq(`read (r_c0:tailreg) s`,t2_win0); t2c_bd0;
    `2 <= L /\ jj + 2 <= L`; subst [`0`,`ofs:num`] (t2_good `jj:num`)])));;

(*** Before the last symbol: no symbol left, or one with its bits in ***)
(*** the container                                                  ***)

let t2c_last spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`read PC s = word(pc + a_last)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_pptr:tailreg) s = word_add src (word ofs)`; t2c_bd2;
    `jj = L \/ jj + 1 = L /\ (ofs = 0 \/ bc <= 52)`; t2c_ofsok;
    t2_good `jj:num`])));;

(*** The end of the tail: the stream at its start with all 64 bits of the ***)
(*** container used, and the L bytes decoded at op                        ***)

let t2c_post spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_conj
   [`read PC s = word(pc + a_post)`; t2c_common_x spec;
    `read (r_pptr:tailreg) s = word_add src (word 0)`;
    subst [t2_spv `s_c:num`,`a:int64`; t2_win0,`w:int64`]
     `read (memory :> bytes64 a) s = w`;
    subst [t2_spv `s_b:num`,`a:int64`]
     `read (memory :> bytes32 a) s = word 64`;
    `read (memory :> bytes(op,L)) s =
     num_of_bytelist(FST(huf_decode ws ml (st:byte list) r L))`]));;

let t2c_l0_goal spec = mk_tail2_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2c_l0inv spec,[`m:num`; `s:armstate`]))))
  (t2c_last spec);;

let t2c_last_goal spec = mk_tail2_goal spec [] (t2c_last spec)
  (t2c_post spec);;

let t2c_after1_goal spec = mk_tail2_goal spec [] (t2c_after1 spec)
  (t2c_last spec);;

let t2c_mid_goal spec = mk_tail2_goal spec [] (t2c_mid spec)
  (t2c_last spec);;

let t2c_entry_goal spec = mk_tail2_goal spec [`jj:num`; `ofs:num`; `bc:num`]
  (t2c_entry spec) (t2c_mid spec);;

let t2c_tail_goal spec = mk_tail2_goal spec [`jj:num`; `ofs:num`; `bc:num`]
  (t2c_entry spec) (t2c_post spec);;

(*** The bits left in a valid stream: at least one for each symbol left ***)

let T2_BITS_LEFT_TAC =
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; `L:num`;
                `jj:num`] HUF_DECODE_ROOM2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ML2_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC;;

(*** The loop without reloads: the lookup, then the comparison at ***)
(*** a_l0 + 0x28 decided by the room after it                     ***)

let TAIL2_L0_TAC spec =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  T2_BITS_LEFT_TAC THEN
  T2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  ML2_SIM_UNTIL_TAC [spec.a_l0 + 0x28] THEN
  W(fun (asl,w) ->
    let s = t2_state asl spec.op2 in
    let jv = fl_num_norm(t2_regval asl s spec.op2) in
    let room = mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` jv `2`) `L:num` in
    T2_OPVAL_TAC [jv] THEN ASM_CASES_TAC room) THEN
  ML2_SIM_UNTIL1_TAC [spec.a_l0; spec.a_last] THEN
  ML2_DECODE_TAC `st:byte list` `r:num` `0` `jj:num` THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THENL
   [DISJ1_TAC THEN
    W(fun (asl,w) ->
      let s = t2_state asl spec.op2 in
      let jv = fl_num_norm(t2_regval asl s spec.op2)
      and bv = t2_regval asl s spec.bc0 in
      EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jv) THEN
      CONJ_TAC THENL
       [ML2_ARITH_TAC;
        MAP_EVERY EXISTS_TAC [jv; bv] THEN
        ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC]);
    DISJ2_TAC THEN
    W(fun (asl,w) ->
      let s = t2_state asl spec.op2 in
      let jv = fl_num_norm(t2_regval asl s spec.op2)
      and bv = rand(rhs(concl(snd(find (fun (_,th) -> let t = concl th in
                 is_eq t && can (term_match [] (subst [s,`s:armstate`;
                   t2_spv(mk_small_numeral(spec.sofs2 + 8)),`a:int64`]
                   `read (memory :> bytes32 a) s = word b`)) t) asl)))) in
      MAP_EVERY EXISTS_TAC [jv; `0`; bv] THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC)];;

(*** The last symbol: from the facts of its lookup, ML2_LAST ***)

let T2_LAST_FACTS_TAC =
  W(fun (asl,w) ->
    let facts = List.concat(map (CONJUNCTS o snd) asl) in
    let ith = find (fun th -> can (term_match []
                `zstd_back (st:byte list) (8 * ofs + 64 - bc) tl = idx1`)
                (concl th)) facts in
    let lemma = SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                       `jj:num`; `ofs:num`; `bc:num`; `tl:num`] ML2_LAST in
    let lfact l = find (fun th -> let t = concl th in is_eq t && lhs t = l)
                       facts in
    let eth = lfact `huf_dentry2 ws ml tl idx1` in
    let ev = rhs(concl eth) in
    let elf n = lfact (mk_icomb(mk_icomb(`EL:num->num list->num`,
                                         mk_small_numeral n),ev)) in
    MP_TAC(REWRITE_RULE [ith; eth; elf 0; elf 2; elf 3]
            (CONV_RULE(TOP_DEPTH_CONV let_CONV) lemma)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `jj + 1 = L`)] THEN
      ASM_REWRITE_TAC[] THEN ML2_ARITH_TAC;
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))]);;

(*** The shift of the index of the last symbol, by -tl without the mask ***)

let T2_SHIFT_NEG_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP T2_JUSHR_NEG
    (CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`))]) THEN ML2_NORM_TAC;;

(*** The case c of the conditional fact of the last symbol ***)

let T2_COND_CASE_TAC ctm =
  FIRST_X_ASSUM(fun th -> if is_cond(concl th) then
    MP_TAC(REWRITE_RULE[ASSUME ctm] th) else NO_TAC) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

(*** The L bytes of the output after the byte of the last symbol ***)

let T2_LAST_MEM_TAC =
  W(fun (asl,w) ->
    let s = rand w in
    SUBGOAL_THEN (subst [s,`s:armstate`]
      `read (memory :> bytes(op,L)) s =
       num_of_bytelist(FST(huf_decode ws ml (st:byte list) r L))`)
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> concl th = `jj + 1 = L`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ML_MEM_SNOC THEN
      ASM_REWRITE_TAC[HUF_DECODE_LENGTH];
      ALL_TAC]);;

(*** The postcondition at the end of the tail ***)

let T2_POST_TAC =
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN REPEAT CONJ_TAC THEN
  FIRST [T2_CONJ_TAC; ASM_REWRITE_TAC[WORD_ADD_0] THEN NO_TAC;
         ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ML2_ARITH_TAC];;

(*** The last symbol, if any: its first byte stored and the bits used set ***)
(*** to 64, from the position 0 of the stream                             ***)

let TAIL2_LAST_TAC spec =
  ZSTD_INTRO_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FL_ABBREV_POST_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) && free_in `jj:num` (concl th) &&
                     free_in `L:num` (concl th))) THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `jj:num = L`)) THEN
    SUBGOAL_THEN `ofs = 0 /\ bc = 64` STRIP_ASSUME_TAC THENL
     [MP_TAC(TRANS
        (SYM(ASSUME `FST(SND(huf_decode ws ml (st:byte list) r L)) = 0`))
        (ASSUME `FST(SND(huf_decode ws ml (st:byte list) r L)) =
                 8 * ofs + 64 - bc`)) THEN
      MP_TAC(ASSUME `bc <= 64`) THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `ofs = 0` || concl th = `bc = 64`))) THEN
    T2_OPVAL_TAC [`L:num`] THEN
    ML2_SIM_UNTIL_TAC [spec.a_post] THEN T2_POST_TAC;
    T2_BITS_LEFT_TAC THEN T2_OPVAL_TAC [`jj:num`; `L:num`] THEN
    (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
    ABBREV_TAC `tt = 2 EXP tl` THEN
    ML2_SIM_UNTIL_TAC [spec.a_last + 0x20] THEN T2_SHIFT_NEG_TAC THEN
    T2_LAST_FACTS_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ofs = 0`)) THEN
    ASM_CASES_TAC `len1 = 1` THENL
     [T2_COND_CASE_TAC `len1 = 1`; T2_COND_CASE_TAC `~(len1 = 1)`] THEN
    ML2_SIM_UNTIL_TAC [spec.a_post] THEN T2_LAST_MEM_TAC THEN T2_POST_TAC];;

(*** After the loop of one lookup: the loop without reloads (from the ***)
(*** start of the stream) if 2 bytes are left, else the last symbol   ***)

let TAIL2_AFTER1_TAC spec l0_th =
  ZSTD_INTRO_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FL_ABBREV_POST_TAC THEN
  T2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  ASM_CASES_TAC `jj + 2 <= L` THENL
   [SUBGOAL_THEN `ofs = 0` SUBST_ALL_TAC THENL [ML2_ARITH_TAC; ALL_TAC] THEN
    ML2_SIM_UNTIL_TAC [spec.a_l0] THEN T4_SHIFT_TAC THEN
    FL_EXPAND_POST_TAC THEN
    ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN DISCH_THEN ACCEPT_TAC) l0_th [] THEN
    MEMSAFE_ELIM_TAC THEN EXISTS_TAC `L - jj` THEN
    MAP_EVERY EXISTS_TAC [`jj:num`; `bc:num`] THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;
    ML2_SIM_UNTIL_TAC [spec.a_last] THEN FL_EXPAND_POST_TAC THEN
    PUFF_FINAL_TAC THEN
    MAP_EVERY EXISTS_TAC [`jj:num`; `ofs:num`; `bc:num`] THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC];;

(*** Two pieces in sequence, with the condition mid between them ***)

let T2_TRANS_TAC spec mid th1 th2 =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (tail2_inst spec mid) THEN REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC th1 THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC th2 THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];;

let t2c_r1last_goal spec = mk_tail2_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2c_r1inv spec,[`m:num`; `s:armstate`]))))
  (t2c_last spec);;

(*** After the main loop of the tail: the loop of one lookup (BIT_DStream ***)
(*** from the frame, the flag 0) if 2 bytes are left, else the last       ***)
(*** symbol                                                               ***)

let TAIL2_MID_TAC spec r1last_th =
  ZSTD_INTRO_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FL_ABBREV_POST_TAC THEN
  ASM_CASES_TAC `jj + 2 <= L` THENL
   [ML2_SIM_UNTIL_TAC [spec.a_r1] THEN T4_SHIFT_TAC THEN
    FL_EXPAND_POST_TAC THEN
    ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN DISCH_THEN ACCEPT_TAC)
      r1last_th [] THEN
    MEMSAFE_ELIM_TAC THEN EXISTS_TAC `L - jj` THEN
    MAP_EVERY EXISTS_TAC [`jj:num`; `ofs:num`; `bc:num`] THEN
    REPEAT CONJ_TAC THEN
    TRY(W(fun (asl,w) ->
      if is_disj w && can (find_term ((=) `word 1:int64`)) (rand w)
      then DISJ1_TAC else NO_TAC)) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;
    ML2_SIM_UNTIL_TAC [spec.a_last] THEN FL_EXPAND_POST_TAC THEN
    PUFF_FINAL_TAC THEN
    MAP_EVERY EXISTS_TAC [`jj:num`; `ofs:num`; `bc:num`] THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC];;

(*** The entry of the tail: at most 7 bytes left, one reload and the end ***)
(*** of the tail; else its main loop, of 5 lookups for tl <= 11 and of  ***)
(*** 4 for tl = 12                                                       ***)

(*** The call of BIT_reloadDStream_internal, the pointer at least 8 bytes ***)
(*** after the start of the stream: bc DIV 8 bytes back, bc MOD 8 bits    ***)
(*** used                                                                 ***)

let TAIL2_CALL_TAC spec =
  let bd = t2_spk spec.sofs2 in
  let bdaddr = map (fun k ->
    WORD_RULE(subst [mk_small_numeral k,`k:num`;
                     mk_small_numeral spec.sofs2,`b:num`;
                     mk_small_numeral(spec.sofs2 + k),`k':num`]
     `word_add (word_add (word_sub stackpointer (word 496)) (word b))
               (word k):int64 =
      word_add (word_sub stackpointer (word 496)) (word k')`)) [8; 16] in
  let ret = mk_comb(`word:num->int64`,
              mk_binop `(+):num->num->num` `pc:num`
                (mk_small_numeral spec.a_ret)) in
  TAIL2_SLICE_TAC `ofs - bc DIV 8` THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (SPECL
   [`pc:num`; ret; bd; t2_win; `bc:num`; `word_add src (word ofs):int64`;
    subst [`ofs - bc DIV 8`,`ofs:num`] t2_win] BITR_CORRECT))) THEN
  REWRITE_TAC(MP (SPECL [`src:int64`; `ofs:num`; `bc DIV 8`] T4_SUB_ADDR)
                (ASSUME `bc DIV 8 <= ofs`) :: bdaddr) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let s = fst(dest_var(rand(rand w))) in
    let n = int_of_string(String.sub s 1 (String.length s - 1)) in
    ARM_BIGSTEP_TAC SLOW2_EXEC ("s"^string_of_int(n + 1))) THENL
   [T4_CONJ_TAC; EVENTS_UNABBREV_TAC];;

(*** To the end of the main loop of the tail, jj' bytes decoded and the ***)
(*** stream at ofs' with bc' bits used                                  ***)

let TAIL2_ENTRY_TO_MID_TAC spec jj' ofs' bc' =
  ML2_SIM_UNTIL_TAC [spec.a_mid] THEN FL_EXPAND_POST_TAC THEN
  PUFF_FINAL_TAC THEN MAP_EVERY EXISTS_TAC [jj'; ofs'; bc'] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

(*** At most 7 bytes left: the reload by the call, none at the start, or ***)
(*** the partial reload up to the start or not                          ***)

let TAIL2_SHORT_TAC spec =
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN
     `ofs + 8 <= LENGTH(st:byte list) /\ bc DIV 8 <= ofs /\
      (ofs - bc DIV 8) + 8 <= LENGTH(st:byte list)`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC] THEN
    ML2_SIM_UNTIL_TAC [0x1c20] THEN TAIL2_CALL_TAC spec THEN
    TAIL2_ENTRY_TO_MID_TAC spec `jj:num` `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [TAIL2_ENTRY_TO_MID_TAC spec `jj:num` `ofs:num` `bc:num`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN MP_TAC(ASSUME `~(ofs = 0)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [TAIL2_SLICE_TAC `ofs - bc DIV 8` THEN
    TAIL2_ENTRY_TO_MID_TAC spec `jj:num` `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    TAIL2_SLICE_TAC `0` THEN
    TAIL2_ENTRY_TO_MID_TAC spec `jj:num` `0` `bc - 8 * ofs`];;

(*** At least 8 bytes left: the head of the main loop of the tail, the ***)
(*** flag 0 and BIT_DStream in the frame                               ***)

let TAIL2_ENTRY_LOOP_TAC a_head loop_th =
  ML2_SIM_UNTIL_TAC [a_head] THEN T4_SHIFT_TAC THEN FL_EXPAND_POST_TAC THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN DISCH_THEN ACCEPT_TAC) loop_th [] THEN
  MEMSAFE_ELIM_TAC THEN EXISTS_TAC `L - jj` THEN
  MAP_EVERY EXISTS_TAC [`jj:num`; `ofs:num`; `bc:num`] THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
    if is_disj w && can (find_term ((=) `word 1:int64`)) (rand w)
    then DISJ1_TAC else NO_TAC)) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

(*** An output of 8 bytes for tl <= 11: the end less 9 before the output, ***)
(*** the loop of 5 lookups left after the first reload                    ***)

let T2_VAL_PRED = prove
 (`!x:int64. ~(val x = 0)
             ==> val(word_add x (word 18446744073709551615)) = val x - 1`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let TAIL2_ENTRY_L8_TAC spec =
  SUBGOAL_THEN `L = 8 /\ jj = 0` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ML2_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP T2_VAL_PRED (ASSUME `~(val(op:int64) = 0)`)) THEN
  DISCH_TAC THEN ML2_SIM_UNTIL_TAC [spec.a_r5] THEN
  T2_RELOAD_CASES_TAC (TAIL2_ENTRY_TO_MID_TAC spec `0`)
                      (TAIL2_ENTRY_TO_MID_TAC spec `0`);;

let TAIL2_ENTRY_TAC spec l4_th l5_th =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs <= LENGTH(st:byte list)`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  T2_OPVAL_TAC [`jj:num`; `L:num`] THEN
  ML2_STEP_TAC 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`op:int64`; `L:num`; `jj:num`]
    T2_ROOM) (ASSUME `jj <= L`)]) THEN
  ASM_CASES_TAC `jj + 8 <= L` THENL
   [ASM_CASES_TAC `tl <= 11` THENL
     [ASM_CASES_TAC `9 <= L` THENL
       [TAIL2_ENTRY_LOOP_TAC spec.a_r5 l5_th; TAIL2_ENTRY_L8_TAC spec];
      TAIL2_ENTRY_LOOP_TAC spec.a_r4 l4_th];
    TAIL2_SHORT_TAC spec];;

(*** The whole tail, from the three pieces ***)

let t2c_midpost_goal spec = mk_tail2_goal spec [] (t2c_mid spec)
  (t2c_post spec);;

(*** The proofs of the pieces of the tails, by stream ***)

let TAIL2_1_B4 = prove(t2c_b4_goal tail2_1,
  TAIL2_BODY_TAC tail2_1 tail2_1.a_r4 tail2_1.bc4);;
let TAIL2_1_L4 = prove(t2c_r4_goal tail2_1,
  TAIL2_LOOP_TAC tail2_1 (tail2_inst tail2_1 (t2v "r_f4")) `8`
    tail2_1.a_b4 tail2_1.a_mid TAIL2_1_B4);;
let TAIL2_1_B5 = prove(t2c_b5_goal tail2_1,
  TAIL2_BODY_TAC tail2_1 tail2_1.a_r5 tail2_1.bc5);;
let TAIL2_1_L5 = prove(t2c_r5_goal tail2_1,
  TAIL2_LOOP_TAC tail2_1 (tail2_inst tail2_1 (t2v "r_f5")) `10`
    tail2_1.a_b5 tail2_1.a_mid TAIL2_1_B5);;
let TAIL2_1_LAST = prove(t2c_last_goal tail2_1, TAIL2_LAST_TAC tail2_1);;
let TAIL2_1_L0 = prove(t2c_l0_goal tail2_1, TAIL2_L0_TAC tail2_1);;
let TAIL2_1_AFTER1 = prove(t2c_after1_goal tail2_1,
  TAIL2_AFTER1_TAC tail2_1 TAIL2_1_L0);;
let TAIL2_1_L1 = prove(t2c_r1_goal tail2_1, TAIL2_L1_TAC tail2_1);;
let TAIL2_1_R1LAST = prove(t2c_r1last_goal tail2_1,
  T2_TRANS_TAC tail2_1 (t2c_after1 tail2_1) TAIL2_1_L1 TAIL2_1_AFTER1);;
let TAIL2_1_MID = prove(t2c_mid_goal tail2_1,
  TAIL2_MID_TAC tail2_1 TAIL2_1_R1LAST);;

let TAIL2_2_B4 = prove(t2c_b4_goal tail2_2,
  TAIL2_BODY_TAC tail2_2 tail2_2.a_r4 tail2_2.bc4);;
let TAIL2_2_L4 = prove(t2c_r4_goal tail2_2,
  TAIL2_LOOP_TAC tail2_2 (tail2_inst tail2_2 (t2v "r_f4")) `8`
    tail2_2.a_b4 tail2_2.a_mid TAIL2_2_B4);;
let TAIL2_2_B5 = prove(t2c_b5_goal tail2_2,
  TAIL2_BODY_TAC tail2_2 tail2_2.a_r5 tail2_2.bc5);;
let TAIL2_2_L5 = prove(t2c_r5_goal tail2_2,
  TAIL2_LOOP_TAC tail2_2 (tail2_inst tail2_2 (t2v "r_f5")) `10`
    tail2_2.a_b5 tail2_2.a_mid TAIL2_2_B5);;
let TAIL2_2_LAST = prove(t2c_last_goal tail2_2, TAIL2_LAST_TAC tail2_2);;
let TAIL2_2_L0 = prove(t2c_l0_goal tail2_2, TAIL2_L0_TAC tail2_2);;
let TAIL2_2_AFTER1 = prove(t2c_after1_goal tail2_2,
  TAIL2_AFTER1_TAC tail2_2 TAIL2_2_L0);;
let TAIL2_2_L1 = prove(t2c_r1_goal tail2_2, TAIL2_L1_TAC tail2_2);;
let TAIL2_2_R1LAST = prove(t2c_r1last_goal tail2_2,
  T2_TRANS_TAC tail2_2 (t2c_after1 tail2_2) TAIL2_2_L1 TAIL2_2_AFTER1);;
let TAIL2_2_MID = prove(t2c_mid_goal tail2_2,
  TAIL2_MID_TAC tail2_2 TAIL2_2_R1LAST);;

let TAIL2_3_B4 = prove(t2c_b4_goal tail2_3,
  TAIL2_BODY_TAC tail2_3 tail2_3.a_r4 tail2_3.bc4);;
let TAIL2_3_L4 = prove(t2c_r4_goal tail2_3,
  TAIL2_LOOP_TAC tail2_3 (tail2_inst tail2_3 (t2v "r_f4")) `8`
    tail2_3.a_b4 tail2_3.a_mid TAIL2_3_B4);;
let TAIL2_3_B5 = prove(t2c_b5_goal tail2_3,
  TAIL2_BODY_TAC tail2_3 tail2_3.a_r5 tail2_3.bc5);;
let TAIL2_3_L5 = prove(t2c_r5_goal tail2_3,
  TAIL2_LOOP_TAC tail2_3 (tail2_inst tail2_3 (t2v "r_f5")) `10`
    tail2_3.a_b5 tail2_3.a_mid TAIL2_3_B5);;
let TAIL2_3_LAST = prove(t2c_last_goal tail2_3, TAIL2_LAST_TAC tail2_3);;
let TAIL2_3_L0 = prove(t2c_l0_goal tail2_3, TAIL2_L0_TAC tail2_3);;
let TAIL2_3_AFTER1 = prove(t2c_after1_goal tail2_3,
  TAIL2_AFTER1_TAC tail2_3 TAIL2_3_L0);;
let TAIL2_3_L1 = prove(t2c_r1_goal tail2_3, TAIL2_L1_TAC tail2_3);;
let TAIL2_3_R1LAST = prove(t2c_r1last_goal tail2_3,
  T2_TRANS_TAC tail2_3 (t2c_after1 tail2_3) TAIL2_3_L1 TAIL2_3_AFTER1);;
let TAIL2_3_MID = prove(t2c_mid_goal tail2_3,
  TAIL2_MID_TAC tail2_3 TAIL2_3_R1LAST);;

let TAIL2_4_B4 = prove(t2c_b4_goal tail2_4,
  TAIL2_BODY_TAC tail2_4 tail2_4.a_r4 tail2_4.bc4);;
let TAIL2_4_L4 = prove(t2c_r4_goal tail2_4,
  TAIL2_LOOP_TAC tail2_4 (tail2_inst tail2_4 (t2v "r_f4")) `8`
    tail2_4.a_b4 tail2_4.a_mid TAIL2_4_B4);;
let TAIL2_4_B5 = prove(t2c_b5_goal tail2_4,
  TAIL2_BODY_TAC tail2_4 tail2_4.a_r5 tail2_4.bc5);;
let TAIL2_4_L5 = prove(t2c_r5_goal tail2_4,
  TAIL2_LOOP_TAC tail2_4 (tail2_inst tail2_4 (t2v "r_f5")) `10`
    tail2_4.a_b5 tail2_4.a_mid TAIL2_4_B5);;
let TAIL2_4_LAST = prove(t2c_last_goal tail2_4, TAIL2_LAST_TAC tail2_4);;
let TAIL2_4_L0 = prove(t2c_l0_goal tail2_4, TAIL2_L0_TAC tail2_4);;
let TAIL2_4_AFTER1 = prove(t2c_after1_goal tail2_4,
  TAIL2_AFTER1_TAC tail2_4 TAIL2_4_L0);;
let TAIL2_4_L1 = prove(t2c_r1_goal tail2_4, TAIL2_L1_TAC tail2_4);;
let TAIL2_4_R1LAST = prove(t2c_r1last_goal tail2_4,
  T2_TRANS_TAC tail2_4 (t2c_after1 tail2_4) TAIL2_4_L1 TAIL2_4_AFTER1);;
let TAIL2_4_MID = prove(t2c_mid_goal tail2_4,
  TAIL2_MID_TAC tail2_4 TAIL2_4_R1LAST);;

(*** The entries and the whole tails ***)

let TAIL2_1_ENTRY = prove(t2c_entry_goal tail2_1,
  TAIL2_ENTRY_TAC tail2_1 TAIL2_1_L4 TAIL2_1_L5);;
let TAIL2_1_MIDPOST = prove(t2c_midpost_goal tail2_1,
  T2_TRANS_TAC tail2_1 (t2c_last tail2_1) TAIL2_1_MID TAIL2_1_LAST);;
let TAIL2_1_TAIL = prove(t2c_tail_goal tail2_1,
  T2_TRANS_TAC tail2_1 (t2c_mid tail2_1) TAIL2_1_ENTRY TAIL2_1_MIDPOST);;

let TAIL2_2_ENTRY = prove(t2c_entry_goal tail2_2,
  TAIL2_ENTRY_TAC tail2_2 TAIL2_2_L4 TAIL2_2_L5);;
let TAIL2_2_MIDPOST = prove(t2c_midpost_goal tail2_2,
  T2_TRANS_TAC tail2_2 (t2c_last tail2_2) TAIL2_2_MID TAIL2_2_LAST);;
let TAIL2_2_TAIL = prove(t2c_tail_goal tail2_2,
  T2_TRANS_TAC tail2_2 (t2c_mid tail2_2) TAIL2_2_ENTRY TAIL2_2_MIDPOST);;

let TAIL2_3_ENTRY = prove(t2c_entry_goal tail2_3,
  TAIL2_ENTRY_TAC tail2_3 TAIL2_3_L4 TAIL2_3_L5);;
let TAIL2_3_MIDPOST = prove(t2c_midpost_goal tail2_3,
  T2_TRANS_TAC tail2_3 (t2c_last tail2_3) TAIL2_3_MID TAIL2_3_LAST);;
let TAIL2_3_TAIL = prove(t2c_tail_goal tail2_3,
  T2_TRANS_TAC tail2_3 (t2c_mid tail2_3) TAIL2_3_ENTRY TAIL2_3_MIDPOST);;

let TAIL2_4_ENTRY = prove(t2c_entry_goal tail2_4,
  TAIL2_ENTRY_TAC tail2_4 TAIL2_4_L4 TAIL2_4_L5);;
let TAIL2_4_MIDPOST = prove(t2c_midpost_goal tail2_4,
  T2_TRANS_TAC tail2_4 (t2c_last tail2_4) TAIL2_4_MID TAIL2_4_LAST);;
let TAIL2_4_TAIL = prove(t2c_tail_goal tail2_4,
  T2_TRANS_TAC tail2_4 (t2c_mid tail2_4) TAIL2_4_ENTRY TAIL2_4_MIDPOST);;

(* ------------------------------------------------------------------------- *)
(* The main loop for a valid block: the body of 4 lookups of each stream     *)
(* (ML2_BODY), the reloads of each stream (RL2_k), the exits (EX2_A, EX2_B)  *)
(* and the loop as a whole (ML2_LOOP).                                       *)
(* ------------------------------------------------------------------------- *)

(*** The main loop of the slow path: 4 lookups of each stream between ***)
(*** reloads, only stream 4's room checked                           ***)

(*** One lookup of a valid decoding with 2 symbols left, or more bits ***)
(*** than for one symbol; the bits left after it at least one for    ***)
(*** each symbol left                                                 ***)

let ML2_STEP2 = prove
 (`!ws ml (st:byte list) r L jj ofs bc tl.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ ml <= tl /\
        SND(SND(huf_decode ws ml st r L)) /\
        FST(SND(huf_decode ws ml st r L)) = 0 /\
        FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\
        bc <= 64 /\ (ofs = 0 \/ tl + bc <= 64) /\
        (jj + 2 <= L \/ ml + bc < 8 * ofs + 64)
        ==> let e = huf_dentry2 ws ml tl (zstd_back st (8 * ofs + 64 - bc) tl)
            in SND(SND(huf_decode ws ml st r (jj + EL 3 e))) /\
               bc + EL 2 e <= 64 /\
               FST(SND(huf_decode ws ml st r (jj + EL 3 e))) =
               8 * ofs + 64 - (bc + EL 2 e) /\
               jj + 2 <= L /\ jj + EL 3 e <= L /\
               L + bc + EL 2 e <= 8 * ofs + 64 + jj + EL 3 e /\
               FST(huf_decode ws ml st r (jj + EL 3 e)) =
               APPEND (FST(huf_decode ws ml st r jj))
                      (if EL 3 e = 2 then [word(EL 0 e); word(EL 1 e)]
                       else [word(EL 0 e)])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `jj + 2 <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj(concl th) && free_in `ml:num` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ml < 8 * ofs + 64 - bc` ASSUME_TAC THENL
     [UNDISCH_TAC `ml + bc < 8 * ofs + 64` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `jj <= L` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                    `L:num`; `jj:num`] HUF_DECODE_POS_MONO) THEN
      ASM_SIMP_TAC[LT_IMP_LE] THEN
      UNDISCH_TAC `ml < 8 * ofs + 64 - bc` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                  `L:num`; `jj:num`] HUF_DECODE_ROOM) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ml < 8 * ofs + 64 - bc` THEN
    SPEC_TAC(`8 * ofs + 64 - bc`,`p:num`) THEN GEN_TAC THEN
    ASM_CASES_TAC `L - jj <= 1` THENL
     [SUBGOAL_THEN `ml * (L - jj) <= ml` MP_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `ml = ml * 1`] THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL];
        ARITH_TAC];
      UNDISCH_TAC `~(L - jj <= 1)` THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; `L:num`;
                `jj:num`; `ofs:num`; `bc:num`; `tl:num`] ML2_STEP) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`;
                `zstd_back (st:byte list) (8 * ofs + 64 - bc) tl`]
    HUF_DENTRY2_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ZSTD_BACK_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(SND(huf_decode ws ml (st:byte list) r jj))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HUF_DECODE_OK_MONO THEN EXISTS_TAC `L:num` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `jj + 2 <= L` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC
   `e = huf_dentry2 ws ml tl (zstd_back (st:byte list)
                                (8 * ofs + 64 - bc) tl)` THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `jj + EL 3 e <= L` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`EL 3 e = 1 \/ EL 3 e = 2`; `jj + 2 <= L`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                `L:num`; `jj + EL 3 e`] HUF_DECODE_ROOM2) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`bc + EL 2 e <= 64`; `jj + EL 3 e <= L`] THEN
  ARITH_TAC);;

(*** The streams in the main loop: the registers of the container, the  ***)
(*** bits used, the pointer and the output; the variables of stream k   ***)
(*** are those of a tail with k appended                                ***)

type ml2spec = {mk2 : int; mc2 : term; mbc2 : term; mptr2 : term;
                mop2 : term};;

let ml2_streams =
 [{mk2 = 1; mc2 = `X12`; mbc2 = `X3`; mptr2 = `X16`; mop2 = `X19`};
  {mk2 = 2; mc2 = `X13`; mbc2 = `X22`; mptr2 = `X17`; mop2 = `X7`};
  {mk2 = 3; mc2 = `X14`; mbc2 = `X21`; mptr2 = `X18`; mop2 = `X6`};
  {mk2 = 4; mc2 = `X11`; mbc2 = `X8`; mptr2 = `X15`; mop2 = `X10`}];;

let ml2_names =
  ["st",`:byte list`; "src",`:int64`; "op",`:int64`; "L",`:num`;
   "r",`:num`; "ofs",`:num`; "bc",`:num`; "jj",`:num`];;

let ml2_var k (s,ty) = mk_var(s ^ string_of_int k,ty);;

let ml2_inst m tm =
  vsubst ([m.mc2,t2v "r_c"; m.mbc2,t2v "r_bc"; m.mptr2,t2v "r_ptr";
           m.mop2,t2v "r_op"] @
          map (fun (s,ty) -> ml2_var m.mk2 (s,ty),mk_var(s,ty)) ml2_names)
         tm;;

let ml2_vars k = map (ml2_var k) ml2_names;;

(*** The body of the main loop, 0x3750 to 0x39d0: 4 lookups of each   ***)
(*** stream, from a good state with its bits in the container, 2      ***)
(*** symbols left for each lookup (8 symbols left, or bits for them)  ***)

let ml2_body_pre1 =
 `read (r_c:tailreg) s =
  word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read (r_bc:tailreg) s = word bc /\
  read (r_op:tailreg) s = word_add op (word jj) /\
  read (memory :> bytes(op,jj)) s =
  num_of_bytelist(FST(huf_decode ws ml st r jj)) /\
  SND(SND(huf_decode ws ml st r jj)) /\
  FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
  (ofs = 0 \/ bc <= 8) /\ jj <= L /\
  (jj + 8 <= L \/ 49 + bc <= 8 * ofs + 64)`;;

let ml2_body_post1 =
 `?jj' bc'.
    read (r_c:tailreg) s =
    word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
         2 EXP 64) /\
    read (r_bc:tailreg) s = word bc' /\
    read (r_op:tailreg) s = word_add op (word jj') /\
    read (memory :> bytes(op,jj')) s =
    num_of_bytelist(FST(huf_decode ws ml st r jj')) /\
    SND(SND(huf_decode ws ml st r jj')) /\
    FST(SND(huf_decode ws ml st r jj')) = 8 * ofs + 64 - bc' /\
    bc' <= 64 /\ (~(ofs = 0) ==> bc' <= 56) /\ jj < jj' /\ jj' <= L`;;

let ml2_hyps_out =
  let one k = ml2_inst (el (k - 1) ml2_streams)
   `L < 2 EXP 28 /\ val(op:int64) + L < 2 EXP 64 /\
    SND(SND(huf_decode ws ml (st:byte list) r L)) /\
    FST(SND(huf_decode ws ml st r L)) = 0 /\
    nonoverlapping (op,L) (tbl:int64,4 * 2 EXP tl) /\
    nonoverlapping (op,L) (word pc,32000)` in
  let pair i k =
    subst [ml2_var i ("op",`:int64`),`a:int64`;
           ml2_var i ("L",`:num`),`m:num`;
           ml2_var k ("op",`:int64`),`b:int64`;
           ml2_var k ("L",`:num`),`n:num`]
     `nonoverlapping (a:int64,m) (b,n)` in
  map one [1;2;3;4] @
  [pair 1 2; pair 1 3; pair 1 4; pair 2 3; pair 2 4; pair 3 4];;

let ml2_body_hyps = list_mk_conj
 ([`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ 1 <= tl /\ tl <= 12`] @ ml2_hyps_out);;

let ml2_rr = `[tbl,4 * 2 EXP tl]:(int64#num)list`
and ml2_wr = `[op1,L1; op2,L2; op3,L3; op4,L4]:(int64#num)list`;;

let ml2_body_frame =
 `MAYCHANGE [PC; X0; X1; X3; X4; X6; X7; X8; X9; X10; X19; X20; X21; X22;
             X23; X24; X25; X26; X27; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op1,L1); memory :> bytes(op2,L2);
             memory :> bytes(op3,L3); memory :> bytes(op4,L4)]`;;

let ml2_body_pre = with_memsafe ml2_rr ml2_wr (mk_abs(`s:armstate`,
  list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x3750) /\
      read X5 s = tbl /\ read X2 s = word(64 - tl) /\
      read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable2 ws ml tl)`] @
    map (fun m -> ml2_inst m ml2_body_pre1) ml2_streams)));;

let ml2_body_post = with_memsafe ml2_rr ml2_wr (mk_abs(`s:armstate`,
  list_mk_conj
   (`read PC s = word(pc + 0x39d0)` ::
    map (fun m -> ml2_inst m ml2_body_post1) ml2_streams)));;

let ml2_body_vars =
  [`pc:num`; `tbl:int64`; `tl:num`; `ws:num list`; `ml:num`;
   `e:uarch_event list`] @ List.concat (map ml2_vars [1;2;3;4]);;

let ml2_body_goal =
  let tm = mk_imp(ml2_body_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; ml2_body_pre; ml2_body_post; ml2_body_frame]) in
  let fvs = frees tm in
  (match subtract fvs ml2_body_vars with
     [] -> ()
   | v::_ -> failwith ("ml2_body_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) ml2_body_vars,tm);;

(*** The steps of the decodings for the lookups indexed so far and not ***)
(*** yet taken, each stream (st,r,ofs,L) at the position of the bits   ***)
(*** used before the lookup (so that those of its next lookups are     ***)
(*** known)                                                            ***)

let ml2_ac_key t =
  sort (<) (map string_of_term
              (striplist (dest_binop `(+):num->num->num`) t));;

let ML2_STEP_NOW_TAC (streams:(term*term*term*term) list) : tactic =
  fun (asl,w as gl) ->
    let facts = fl_all_facts asl in
    let lfact l = find (fun th -> let t = concl th in is_eq t && lhs t = l)
                       facts in
    let elfact n ev = lfact (mk_icomb(mk_icomb(`EL:num->num list->num`,
                                               mk_small_numeral n),ev)) in
    let addac a b =
      if a = b then REFL a else EQT_ELIM(REWRITE_CONV[ADD_AC] (mk_eq(a,b))) in
    let one (st,r,ofs,l) =
      let idxpat = subst [st,`st:byte list`; ofs,`ofs:num`]
        `zstd_back (st:byte list) (8 * ofs + 64 - x) tl = idx` in
      let pospat = subst [st,`st:byte list`; r,`r:num`; ofs,`ofs:num`]
        `FST(SND(huf_decode ws ml (st:byte list) r j)) = 8 * ofs + 64 - x` in
      let poss = mapfilter (fun th ->
        let _,tmi,_ = term_match [st; r; ofs; `ws:num list`; `ml:num`]
                    pospat (concl th) in
        let inst v = try rev_assoc v tmi with Failure _ -> v in
        (inst `j:num`,inst `x:num`,th)) facts in
      let looks = mapfilter (fun th ->
        let _,tmi,_ = term_match [st; ofs; `tl:num`] idxpat (concl th) in
        let inst v = try rev_assoc v tmi with Failure _ -> v in
        let x = inst `x:num` and idx = inst `idx:num` in
        let eth = lfact (list_mk_icomb "huf_dentry2"
                           [`ws:num list`; `ml:num`; `tl:num`; idx]) in
        let ev = rhs(concl eth) in
        let nb = rhs(concl(elfact 2 ev)) in
        if exists (fun (_,x',_) -> free_in nb x') poss then fail()
        else (x,idx,th,eth,ev)) facts in
      map (fun (x,idx,ith,eth,ev) ->
        let key = ml2_ac_key x in
        let (j,x',posth) = find (fun (_,x',_) -> ml2_ac_key x' = key) poss in
        let posth' =
          if x' = x then posth else
          let r = rhs(concl posth) in
          TRANS posth (AP_TERM (rator r)
                         (AP_TERM (rator(rand r)) (addac x' x))) in
        let ths5 = [ith; eth; elfact 0 ev; elfact 1 ev; elfact 2 ev;
                    elfact 3 ev] in
        let lemma = SPECL [`ws:num list`; `ml:num`; st; r; l; j; ofs; x;
                           `tl:num`] ML2_STEP2 in
        let lemma' =
          REWRITE_RULE ths5 (CONV_RULE(TOP_DEPTH_CONV let_CONV) lemma) in
        let cs = conjuncts(lhand(concl lemma')) in
        let prove_ant t =
          if t = concl posth' then posth'
          else try find (fun th -> concl th = t) facts
               with Failure _ -> TAC_PROOF((asl,t),ML2_ARITH_TAC) in
        let th = MP lemma' (end_itlist CONJ (map prove_ant cs)) in
        let lenv = rhs(concl(elfact 3 ev)) in
        let jt' = mk_binop `(+):num->num->num` j lenv in
        let jn = fl_num_norm jt' in
        let norm th = if jn = jt' then th else
          CONV_RULE(ONCE_DEPTH_CONV(fun t -> if t = jt' then addac jt' jn
                                             else failwith "")) th in
        map norm (CONJUNCTS th)) looks in
    let ths = List.concat(List.concat(map one streams)) in
    MAP_EVERY ASSUME_TAC ths gl;;

(*** The facts of the entries of the table that were loaded, and those ***)
(*** of their first bytes (only for the last symbol of a stream), left ***)
(*** out (as FL2_DROP_TAC)                                             ***)

let ML2_DROP_TAC : tactic =
  let tblv = `tbl:int64` in
  fun (asl,w as gl) ->
    let s = rand w in
    let regvals = mapfilter (fun (_,th) ->
      let t = concl th in
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(_,_)),s')),
             Comb(Const("word",_),v))
          when s' = s -> v
      | _ -> fail()) asl in
    let is_entry th =
      let t = concl th in
      is_eq t &&
      (match lhs t with
         Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),
              Comb(Const(("bytes16" | "bytes8") as c,_),a))),_) ->
           (match a with
              Comb(Comb(Const("word_add",_),b),
                   Comb(Const("word",_),k)) ->
                b = tblv &&
                ((match rhs t with
                    Comb(Const("word",_),v) -> mem v regvals
                  | _ -> false) ||
                 c = "bytes8" && is_binary "*" k)
            | _ -> false)
       | _ -> false) in
    DISCARD_ASSUMPTIONS_TAC is_entry gl;;

(*** Simulation with the steps at once ***)

let ML2_SIM_UNTIL_NOW_TAC streams stops =
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k (asl,w as gl) =
    let pc = current_pc gl in
    if mem pc stops then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "ML2_SIM_UNTIL_NOW_TAC"
    else
      let n = let v = fst(dest_var(rand w)) in
              int_of_string(String.sub v 1 (String.length v - 1)) in
      (ML2_STEP_TAC (n + 1) THEN ML2_NORM_TAC THEN
       ML2_STEP_NOW_TAC streams THEN ML2_DROP_TAC THEN run (k - 1)) gl in
  run 400;;

(*** The body: the steps of the four decodings during the simulation, ***)
(*** the bytes stored as those decoded, the last position of each     ***)

let ml2_stream_terms =
  map (fun k -> ml2_var k ("st",`:byte list`),ml2_var k ("r",`:num`),
                ml2_var k ("ofs",`:num`),ml2_var k ("L",`:num`)) [1;2;3;4];;

let ML2_ROOM_START_TAC =
  MAP_EVERY (fun k ->
    let v s ty = ml2_var k (s,ty) in
    let inst = subst [v "bc" `:num`,`bc:num`; v "jj" `:num`,`jj:num`;
                      v "L" `:num`,`L:num`; v "ofs" `:num`,`ofs:num`] in
    MP_TAC(SPECL [`ws:num list`; `ml:num`; v "st" `:byte list`;
                  v "r" `:num`; v "L" `:num`; v "jj" `:num`]
           HUF_DECODE_ROOM2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (inst `L + bc <= 8 * ofs + 64 + jj`) ASSUME_TAC THENL
     [MAP_EVERY (fun t -> MP_TAC(ASSUME(inst t)))
       [`bc <= 64`; `jj <= L`; `L - jj <= 8 * ofs + 64 - bc`] THEN
      ARITH_TAC;
      ALL_TAC])
   [1;2;3;4];;

let ML2_BODY_MEM_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let facts = fl_all_facts asl in
    let fths = filter (fun th -> let t = concl th in
      is_eq t && is_comb(lhs t) &&
      fst(strip_comb(lhs t)) = `FST:byte list#num#bool->byte list`) facts in
    let mems = mapfilter (fun (_,th) -> let t = concl th in
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),_),Comb(Const("bytes",_),_))),s')),r)
          when s' = s && can (find_term (fun u -> is_const u &&
                                fst(dest_const u) = "huf_decode")) r -> th
      | _ -> fail()) asl in
    MAP_EVERY (fun th -> ASSUME_TAC(REWRITE_RULE (map SYM fths) th)) mems gl;;

let ML2_LAST_POS (asl:(string*thm)list) (st,r,ofs) =
  let pospat = subst [st,`st:byte list`; r,`r:num`; ofs,`ofs:num`]
    `FST(SND(huf_decode ws ml (st:byte list) r j)) = 8 * ofs + 64 - x` in
  let poss = mapfilter (fun th ->
    let _,tmi,_ = term_match [st; r; ofs; `ws:num list`; `ml:num`]
                    pospat (concl th) in
    let inst v = try rev_assoc v tmi with Failure _ -> v in
    (inst `j:num`,inst `x:num`)) (fl_all_facts asl) in
  let size j = length(striplist (dest_binop `(+):num->num->num`) j) in
  end_itlist (fun (j,x) (j',x') -> if size j >= size j' then (j,x)
                                    else (j',x')) poss;;

(*** The conjuncts of a postcondition with many facts around: each by a ***)
(*** fact, or by the fact about its left side and arithmetic           ***)

let T2_LITE_CONJ_TAC =
  REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    let facts = fl_all_facts asl in
    match filter (fun th -> concl th = w) facts with
      th::_ -> ACCEPT_TAC th
    | [] ->
    match filter (fun th -> let t = concl th in
                    is_eq w && is_eq t && lhs t = lhs w) facts with
      th::_ ->
        GEN_REWRITE_TAC LAND_CONV [th] THEN
        FIRST [REFL_TAC; AP_TERM_TAC THEN ARITH_TAC;
               AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ARITH_TAC]
    | [] -> ML2_ARITH_TAC);;

fl2_keep_bases := [];;

let ML2_BODY_TAC =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  ML2_ROOM_START_TAC THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
  ML2_SIM_UNTIL_NOW_TAC ml2_stream_terms [0x39d0] THEN
  ML2_BODY_MEM_TAC THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let m = find (fun m -> free_in (ml2_var m.mk2 ("st",`:byte list`)) w)
                 ml2_streams in
    let v s ty = ml2_var m.mk2 (s,ty) in
    let jv,bv = ML2_LAST_POS asl (v "st" `:byte list`,v "r" `:num`,
                                  v "ofs" `:num`) in
    MAP_EVERY EXISTS_TAC [jv; bv] THEN T2_LITE_CONJ_TAC);;

(*** The proof of the body of the main loop ***)

let ML2_BODY = prove(ml2_body_goal, ML2_BODY_TAC);;

(*** The reloads of the main loop after its body (0x39d0 to 0x3750), one ***)
(*** stream at a time as pieces with small contexts: reloaded (the       ***)
(*** pointer at least 8 bytes after the start, as huf_rlofs and          ***)
(*** huf_rlbc of the 4X1 proof) or not, with the status in w0            ***)

type rl2spec =
 {ra2 : int; rb2 : int;           (* from ra2 to rb2                      *)
  rlim2 : term;                   (* the fact of the limit start + 8      *)
  rptr2 : term; rbc2 : term; rcont2 : term;
  rflag2 : int;                   (* the 32-bit slot of the flag          *)
  rfirst2 : bool;                 (* stream 1: w0 set to 0 if reloaded    *)
  rrd2 : term list;               (* more regions read                    *)
  rregs2 : term};;                (* the registers written                *)

let rl2_1 =
 {ra2 = 0x39d0; rb2 = 0x36cc; rlim2 = `read X28 s = word_add src (word 8)`;
  rptr2 = `X16`; rbc2 = `X3`; rcont2 = `X12`; rflag2 = 140; rfirst2 = true;
  rrd2 = []; rregs2 = `[PC; X0; X1; X3; X12; X16]`};;

let rl2_2 =
 {ra2 = 0x36cc; rb2 = 0x36f0; rlim2 = t2_lim_mem 96;
  rptr2 = `X17`; rbc2 = `X22`; rcont2 = `X13`; rflag2 = 132; rfirst2 = false;
  rrd2 = [mk_pair(t2_spk 96,`8`)];
  rregs2 = `[PC; X0; X1; X4; X13; X17; X22]`};;

let rl2_3 =
 {ra2 = 0x36f0; rb2 = 0x3714; rlim2 = t2_lim_mem 104;
  rptr2 = `X18`; rbc2 = `X21`; rcont2 = `X14`; rflag2 = 136; rfirst2 = false;
  rrd2 = [mk_pair(t2_spk 104,`8`)];
  rregs2 = `[PC; X0; X1; X4; X14; X18; X21]`};;

let rl2_vars =
  [`pc:num`; `stackpointer:int64`; `src:int64`; `st:byte list`; `ofs:num`;
   `bc:num`; `f:num`; `w:num`; `e:uarch_event list`];;

let rl2_hyps =
 [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
  `8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64`;
  `nonoverlapping (src:int64,LENGTH(st:byte list)) (word pc,32000)`;
  `ofs <= LENGTH(st:byte list) /\ bc < 2 EXP 32 /\ f < 2 EXP 32 /\
   w < 2 EXP 32`;
  `8 <= ofs ==> ofs + 8 <= LENGTH(st:byte list) /\ bc <= 64`;
  `aligned 16 (stackpointer:int64)`;
  `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                  (src:int64,LENGTH(st:byte list))`;
  `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                  (word pc,32000)`];;

let rl2_win =
 `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * huf_rlofs ofs bc)) MOD
       2 EXP 64):int64`;;

let rl2_goal (sp:rl2spec) =
  let rd r v = mk_eq(list_mk_icomb "read" [r; `s:armstate`],v) in
  let w0pre,w0post =
    if sp.rfirst2 then [],[`read X0 s = word(if 8 <= ofs then 0 else 3)`]
    else [`read X0 s = word w`],[`read X0 s = word(if 8 <= ofs then w else 3)`]
  in
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc`;
     mk_eq(`read PC s`,mk_comb(`word:num->int64`,
       mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral sp.ra2)));
     sp.rlim2;
     rd sp.rptr2 `word_add src (word ofs):int64`;
     rd sp.rbc2 `word bc:int64`; rd sp.rcont2 t2_win;
     ml_mem32 sp.rflag2 `f:num`] @ w0pre @
    [`read (memory :> bytes(src,LENGTH(st:byte list))) s =
      num_of_bytelist st`;
     `read SP s = word_sub stackpointer (word 496)`;
     `read events s = e`])) in
  let rr = mk_list(`src:int64,LENGTH(st:byte list)` :: sp.rrd2,
                   `:int64#num`)
  and wr = mk_list([mk_pair(t2_spk sp.rflag2,`4`)],`:int64#num`) in
  let ms = subst [rr,`rr:(int64#num)list`; wr,`wr:(int64#num)list`]
   `?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 rr wr` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   ([mk_eq(`read PC s`,mk_comb(`word:num->int64`,
       mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral sp.rb2)));
     rd sp.rptr2 `word_add src (word (huf_rlofs ofs bc)):int64`;
     rd sp.rbc2 `word (huf_rlbc ofs bc):int64`;
     rd sp.rcont2 rl2_win;
     ml_mem32 sp.rflag2 `if 8 <= ofs then 1 else f`] @ w0post @ [ms])) in
  let frame =
    subst [sp.rregs2,`r:((armstate,int64)component)list`;
           t2_spk sp.rflag2,`a:int64`]
     `MAYCHANGE (r:((armstate,int64)component)list) ,,
      MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(a,4)]` in
  mk_small_goal rl2_vars rl2_hyps pre post frame;;

let RL2_TAC (sp:rl2spec) : tactic =
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
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
        `ofs + 8 <= LENGTH(st:byte list)`] THEN ARITH_TAC;
      DISCH_TAC] THEN
    T4_SLICE_TAC `ofs - bc DIV 8` `s0:armstate` THEN
    ML2_SIM_UNTIL_TAC [sp.rb2] THEN
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
    ML2_SIM_UNTIL_TAC [sp.rb2] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    T4_CONJ_TAC];;

let RL2_1 = prove(rl2_goal rl2_1, RL2_TAC rl2_1);;
let RL2_2 = prove(rl2_goal rl2_2, RL2_TAC rl2_2);;
let RL2_3 = prove(rl2_goal rl2_3, RL2_TAC rl2_3);;

(*** Stream 4 and the decision of the loop: on if all four streams were ***)
(*** reloaded (w0 = 0) and 8 more bytes of stream 4 fit; exits 0x47d4    ***)
(*** (stream 4 not reloaded) and 0x4bbc                                  ***)

let rl2_4_vars = rl2_vars @ [`op:int64`; `L:num`; `jj:num`];;

let rl2_4_goal =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x3714)`;
    t2_lim_mem 112;
    `read X15 s = word_add src (word ofs) /\ read X8 s = word bc`;
    mk_eq(`read X11 s`,t2_win);
    `read X0 s = word w /\ read X10 s = word_add op (word jj)`;
    subst [t2_spk 120,`a:int64`]
     `read (memory :> bytes64 a) s = word_add op (word (L - 7))`;
    ml_mem32 184 `f:num`;
    `read (memory :> bytes(src,LENGTH(st:byte list))) s =
     num_of_bytelist st /\
     read SP s = word_sub stackpointer (word 496) /\
     read events s = e`]) in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [`read PC s = (if 8 <= ofs
                  then if w = 0 /\ jj + 8 <= L then word(pc + 0x3750)
                       else word(pc + 0x4bbc)
                  else word(pc + 0x47d4))`;
    `read X15 s = word_add src (word (huf_rlofs ofs bc)) /\
     read X8 s = word (huf_rlbc ofs bc)`;
    mk_eq(`read X11 s`,rl2_win);
    `read X0 s = (if 8 <= ofs then word(if w = 0 /\ jj + 8 <= L then 1 else 0)
                  else word w)`;
    ml_mem32 184 `if 8 <= ofs then (if w = 0 /\ jj + 8 <= L then 1 else 0)
                  else f`;
    subst [t2_spk 112,`a:int64`; t2_spk 120,`b:int64`; t2_spk 184,`c:int64`]
     `?e2. read events s = APPEND e2 e /\
           memaccess_inbounds e2 [src,LENGTH(st:byte list); a,8; b,8]
                                 [c,4]`]) in
  let frame =
    subst [t2_spk 184,`a:int64`]
     `MAYCHANGE [PC; X0; X1; X8; X11; X15] ,,
      MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(a,4)]` in
  mk_small_goal rl2_4_vars
   (rl2_hyps @
    [`val(op:int64) + L < 2 EXP 64 /\ jj <= L /\ 7 <= L /\
      (w = 0 \/ w = 3)`])
   pre post frame;;

(*** The flag of the comparison of stream 4 with its limit ***)

let RL2_4_FIN_TAC : tactic =
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(L - 7 - jj) MOD 2 EXP 64 = L - 7 - jj`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(op:int64) + L < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L - 7 - jj = 0 <=> ~(jj + 8 <= L)`
   (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`jj <= L`; `7 <= L`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

let RL2_4_TAC : tactic =
  REWRITE_TAC[GSYM puff_memsafe; huf_rlofs; huf_rlbc] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  T2_OPVAL_TAC [`jj:num`; `L - 7`] THEN
  ASM_CASES_TAC `8 <= ofs` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(concl th) = `8 <= ofs`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    SUBGOAL_THEN
     `bc DIV 8 <= ofs /\ (ofs - bc DIV 8) + 8 <= LENGTH(st:byte list)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
        `ofs + 8 <= LENGTH(st:byte list)`] THEN ARITH_TAC;
      DISCH_TAC] THEN
    T4_SLICE_TAC `ofs - bc DIV 8` `s0:armstate` THEN
    ASM_CASES_TAC `jj + 8 <= L` THENL
     [ALL_TAC;
      ASM_CASES_TAC `jj = L - 7` THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o
          check (fun th -> concl th = `jj = L - 7`));
        ALL_TAC]] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      check (fun th -> concl th = `w = 0 \/ w = 3`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ML2_SIM_UNTIL_TAC [0x3750; 0x4bbc] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`src:int64`; `ofs:num`;
      `bc DIV 8`] T4_SUB_ADDR) (ASSUME `bc DIV 8 <= ofs`)]) THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [T4_CONJ_TAC; RL2_4_FIN_TAC];
    MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC
       [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
        `ofs <= LENGTH(st:byte list)`] THEN ARITH_TAC;
      DISCH_TAC] THEN
    ML2_SIM_UNTIL_TAC [0x47d4] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    T4_CONJ_TAC];;

let RL2_4 = prove(rl2_4_goal, RL2_4_TAC);;

(*** The exits of the main loop (0x47d4 when stream 4 is not reloaded,  ***)
(*** 0x4bbc otherwise) to the check of the order of the outputs          ***)
(*** (0x3a98): BIT_DStream of each stream back in the frame (the         ***)
(*** container and the pointer only where the flag says they changed),  ***)
(*** and the registers of the tails restored from the frame             ***)

let ex2_vars =
  [`pc:num`; `stackpointer:int64`;
   `c1:int64`; `c2:int64`; `c3:int64`; `c4:int64`;
   `b1:num`; `b2:num`; `b3:num`; `b4:num`;
   `p1:int64`; `p2:int64`; `p3:int64`; `p4:int64`;
   `f1:num`; `f2:num`; `f3:num`; `f4:num`;
   `oend:int64`; `s1:int64`; `s2:int64`; `s3:int64`; `s4:int64`;
   `o2:int64`; `o3:int64`; `o4:int64`; `tl:num`; `n:num`;
   `x25:int64`; `x26:int64`; `e:uarch_event list`];;

let ex2_flagslot = [140; 132; 136; 184];;

let ex2_struct k c p =
  [ml_mem64 (224 + 40 * (k - 1)) c;
   ml_mem64 (240 + 40 * (k - 1)) p];;

let ex2_flagdisj k =
  let f = mk_var("f"^string_of_int k,`:num`)
  and c = mk_var("c"^string_of_int k,`:int64`)
  and p = mk_var("p"^string_of_int k,`:int64`) in
  mk_disj(list_mk_conj(mk_eq(f,`0`) :: ex2_struct k c p),mk_eq(f,`1`));;

let ex2_slots =
  [ml_mem64 144 `oend:int64`; ml_mem64 152 `s1:int64`;
   ml_mem64 160 `o2:int64`; ml_mem64 168 `o3:int64`;
   ml_mem64 176 `o4:int64`; ml_mem32 188 `tl:num`;
   ml_mem64 192 `word n:int64`; ml_mem64 200 `s2:int64`;
   ml_mem64 208 `s3:int64`; ml_mem64 216 `s4:int64`;
   ml_mem64 64 `x25:int64`; ml_mem64 72 `x26:int64`];;

let ex2_post =
  mk_abs(`s:armstate`,list_mk_conj
   ([`read PC s = word(pc + 0x3a98)`;
     `read X14 s = oend /\ read X18 s = s1 /\ read X12 s = o2 /\
      read X13 s = o3 /\ read X11 s = o4 /\ read X20 s = word n /\
      read X15 s = s2 /\ read X9 s = s3 /\ read X24 s = s4 /\
      read X23 s = word tl /\ read X25 s = x25 /\ read X26 s = x26`] @
    List.concat (map (fun k ->
      let c = mk_var("c"^string_of_int k,`:int64`)
      and b = mk_var("b"^string_of_int k,`:num`)
      and p = mk_var("p"^string_of_int k,`:int64`) in
      ex2_struct k c p @ [ml_mem32 (232 + 40 * (k - 1)) b]) [1;2;3;4]) @
    [`?e2. read events s = APPEND e2 e /\
           memaccess_inbounds e2 [word_sub stackpointer (word 496),496]
                                 [word_sub stackpointer (word 496),496]`]));;

let ex2_hyps =
 [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
  `aligned 16 (stackpointer:int64)`;
  `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                  (word pc,32000)`;
  `b1 < 2 EXP 32 /\ b2 < 2 EXP 32 /\ b3 < 2 EXP 32 /\ b4 < 2 EXP 32 /\
   tl < 2 EXP 32 /\ f1 < 2 EXP 32 /\ f2 < 2 EXP 32 /\ f3 < 2 EXP 32 /\
   f4 < 2 EXP 32`];;

let ex2_frame =
 `MAYCHANGE [PC; X0; X1; X2; X4; X9; X11; X12; X13; X14; X15; X18; X20;
             X23; X24; X25; X26; X27] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                     (word 224),160)]`;;

let ex2_goal a ks =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read SP s = word_sub stackpointer (word 496)`;
     mk_eq(`read PC s`,mk_comb(`word:num->int64`,
       mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral a)));
     `read X12 s = c1 /\ read X3 s = word b1 /\ read X16 s = p1 /\
      read X13 s = c2 /\ read X22 s = word b2 /\ read X17 s = p2 /\
      read X14 s = c3 /\ read X21 s = word b3 /\ read X18 s = p3 /\
      read X11 s = c4 /\ read X8 s = word b4 /\ read X15 s = p4`] @
    map (fun k -> ml_mem32 (el (k - 1) ex2_flagslot)
                    (mk_var("f"^string_of_int k,`:num`))) ks @
    ex2_slots @ map ex2_flagdisj ks @
    [`read events s = e`])) in
  mk_small_goal ex2_vars ex2_hyps pre ex2_post ex2_frame;;

let EX2_TAC ks : tactic =
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun k ->
    FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
      check (fun th -> concl th = vsubst [`s0:armstate`,`s:armstate`]
                                         (ex2_flagdisj k))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = mk_var("f"^string_of_int k,`:num`))))
   ks THEN
  ML2_SIM_UNTIL_TAC [0x3a98] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  T4_CONJ_TAC;;

let EX2_A = prove(ex2_goal 0x47d4 [1;2;3;4], EX2_TAC [1;2;3;4]);;
let EX2_B = prove(ex2_goal 0x4bbc [1;2;3], EX2_TAC [1;2;3]);;

(*** The main loop as one theorem: from the body to an exit (0x47d4 or  ***)
(*** 0x4bbc). The flags are all f, and f = 0 only before the first      ***)
(*** reload, when the containers and pointers are those in the frame    ***)
(*** (from the initial offsets ofs0_k); after the loop a flag is 0 only ***)
(*** for a stream never reloaded                                        ***)

type ml2q = {qk : int; qcont : term; qbc : term; qptr : term; qop : term;
             qlim : term; qsofs : int; qflag : int};;

let ml2_q =
 [{qk = 1; qcont = `X12`; qbc = `X3`; qptr = `X16`; qop = `X19`;
   qlim = `read X28 s = word_add src (word 8)`; qsofs = 224; qflag = 140};
  {qk = 2; qcont = `X13`; qbc = `X22`; qptr = `X17`; qop = `X7`;
   qlim = t2_lim_mem 96; qsofs = 264; qflag = 132};
  {qk = 3; qcont = `X14`; qbc = `X21`; qptr = `X18`; qop = `X6`;
   qlim = t2_lim_mem 104; qsofs = 304; qflag = 136};
  {qk = 4; qcont = `X11`; qbc = `X8`; qptr = `X15`; qop = `X10`;
   qlim = t2_lim_mem 112; qsofs = 344; qflag = 184}];;

let ml2_qinst q tm =
  vsubst ([q.qcont,t2v "r_c"; q.qbc,t2v "r_bc"; q.qptr,t2v "r_ptr";
           q.qop,t2v "r_op"] @
          map (fun (s,ty) -> ml2_var q.qk (s,ty),mk_var(s,ty)) ml2_names)
         tm;;

let ml2_o0 k = mk_var("ofs0"^string_of_int k,`:num`);;

(*** One stream at the body, and the frame from its initial offset ***)

let ml2_inv1 q = ml2_qinst q (list_mk_conj
 [mk_eq(`read (r_c:tailreg) s`,t2_win);
  `read (r_bc:tailreg) s = word bc /\
   read (r_ptr:tailreg) s = word_add src (word ofs) /\
   read (r_op:tailreg) s = word_add op (word jj)`;
  q.qlim;
  `read (memory :> bytes(src,LENGTH(st:byte list))) s =
   num_of_bytelist st /\
   read (memory :> bytes(op,jj)) s =
   num_of_bytelist(FST(huf_decode ws ml st r jj)) /\
   SND(SND(huf_decode ws ml st r jj)) /\
   FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   (ofs = 0 \/ bc <= 8) /\ (ofs = 0 \/ ofs + 8 <= LENGTH st) /\ jj <= L /\
   (jj + 8 <= L \/ 49 + bc <= 8 * ofs + 64)`]);;

let ml2_struct0 q =
  vsubst [ml2_o0 q.qk,`ofs:num`; ml2_var q.qk ("src",`:int64`),`src:int64`;
          ml2_var q.qk ("st",`:byte list`),`st:byte list`]
   (list_mk_conj
     [subst [t2_spk q.qsofs,`a:int64`; t2_win,`w:int64`]
       `read (memory :> bytes64 a) s = w`;
      subst [t2_spk (q.qsofs + 16),`a:int64`]
       `read (memory :> bytes64 a) s = word_add src (word ofs)`]);;

let ml2_flags =
  list_mk_conj(map (fun q -> ml_mem32 q.qflag `f:num`) ml2_q @
   [`f = 0 \/ f = 1`;
    mk_imp(`f = 0`,list_mk_conj(map (fun k ->
      mk_eq(ml2_var k ("ofs",`:num`),ml2_o0 k)) [1;2;3;4]))]);;

let ml2_lrr =
  mk_list([`tbl:int64,4 * 2 EXP tl`] @
          map (fun k -> mk_pair(ml2_var k ("src",`:int64`),
                  mk_comb(`LENGTH:byte list->num`,
                          ml2_var k ("st",`:byte list`)))) [1;2;3;4] @
          [`word_sub stackpointer (word 496):int64,496`],`:int64#num`)
and ml2_lwr =
  mk_list(map (fun k -> mk_pair(ml2_var k ("op",`:int64`),
                                ml2_var k ("L",`:num`))) [1;2;3;4] @
          [`word_sub stackpointer (word 496):int64,496`],`:int64#num`);;

let ml2_inv_body =
  list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x3750) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X5 s = tbl /\ read X2 s = word(64 - tl) /\
      read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable2 ws ml tl)`;
     subst [t2_spk 120,`a:int64`]
      `read (memory :> bytes64 a) s = word_add op4 (word (L4 - 7))`;
     `jj4 + 8 <= L4`] @
    map ml2_struct0 ml2_q @ map ml2_inv1 ml2_q @ [ml2_flags]);;

let ml2_pervars k = map (ml2_var k) ["jj",`:num`; "ofs",`:num`; "bc",`:num`];;

let ml2_inv = with_memsafe ml2_lrr ml2_lwr
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists(List.concat(map ml2_pervars [1;2;3;4]) @ [`f:num`],
    mk_conj(`m = L4 - jj4`,ml2_inv_body))));;

(*** One stream at the exit of the loop ***)

let ml2_lexit1 q = ml2_qinst q (list_mk_conj
 [mk_eq(`read (r_c:tailreg) s`,t2_win);
  `read (r_bc:tailreg) s = word bc /\
   read (r_ptr:tailreg) s = word_add src (word ofs) /\
   read (r_op:tailreg) s = word_add op (word jj) /\
   read (memory :> bytes(src,LENGTH(st:byte list))) s =
   num_of_bytelist st /\
   read (memory :> bytes(op,jj)) s =
   num_of_bytelist(FST(huf_decode ws ml st r jj)) /\
   SND(SND(huf_decode ws ml st r jj)) /\
   FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   (ofs = 0 \/ ofs + 8 <= LENGTH st) /\ jj <= L`]);;

let ml2_lexit_raw = mk_abs(`s:armstate`,
  list_mk_exists(List.concat(map ml2_pervars [1;2;3;4]) @
                 [`f1:num`; `f2:num`; `f3:num`; `f4:num`],
   list_mk_conj
    ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
       read SP s = word_sub stackpointer (word 496)`;
      ml_mem32 140 `f1:num`; ml_mem32 132 `f2:num`; ml_mem32 136 `f3:num`] @
     map ml2_lexit1 ml2_q @
     map (fun k ->
       let f = mk_var("f"^string_of_int k,`:num`) in
       mk_conj(mk_disj(mk_eq(f,`0`),mk_eq(f,`1`)),
               mk_imp(mk_eq(f,`0`),mk_eq(ml2_var k ("ofs",`:num`),ml2_o0 k))))
       [1;2;3;4] @
     [mk_disj(mk_conj(`read PC s = word(pc + 0x47d4)`,ml_mem32 184 `f4:num`),
              `read PC s = word(pc + 0x4bbc)`)])));;

let ml2_lexit = with_memsafe ml2_lrr ml2_lwr ml2_lexit_raw;;

let ml2_loop_frame =
 `MAYCHANGE [PC; X0; X1; X3; X4; X6; X7; X8; X9; X10; X11; X12; X13; X14;
             X15; X16; X17; X18; X19; X20; X21; X22; X23; X24; X25; X26;
             X27; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op1,L1); memory :> bytes(op2,L2);
             memory :> bytes(op3,L3); memory :> bytes(op4,L4);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 132),12);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 184),4)]`;;

let ml2_loop_hyps =
  let st k = ml2_var k ("st",`:byte list`)
  and sv k = ml2_var k ("src",`:int64`)
  and ov k = ml2_var k ("op",`:int64`)
  and lv k = ml2_var k ("L",`:num`) in
  let ins k = mk_pair(sv k,mk_comb(`LENGTH:byte list->num`,st k))
  and outs k = mk_pair(ov k,lv k) in
  let tbl = `tbl:int64,4 * 2 EXP tl`
  and code = `word pc:int64,32000`
  and stk = `word_sub stackpointer (word 496):int64,496` in
  let nonov a b = list_mk_icomb "nonoverlapping" [a; b] in
  let one k = ml2_qinst (el (k - 1) ml2_q)
   `L < 2 EXP 28 /\ val(op:int64) + L < 2 EXP 64 /\
    8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64 /\
    SND(SND(huf_decode ws ml st r L)) /\
    FST(SND(huf_decode ws ml st r L)) = 0` in
  [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ 1 <= tl /\ tl <= 12`] @
  map one [1;2;3;4] @
  List.concat (map (fun k ->
    [nonov (outs k) tbl; nonov (outs k) code; nonov (outs k) stk] @
    map (fun i -> nonov (outs k) (ins i)) [1;2;3;4]) [1;2;3;4]) @
  map (fun (i,k) -> nonov (outs i) (outs k))
      [1,2; 1,3; 1,4; 2,3; 2,4; 3,4] @
  map (fun k -> nonov stk (ins k)) [1;2;3;4] @
  [nonov stk tbl; nonov stk code] @
  map (fun k -> nonov (ins k) code) [1;2;3;4];;

let ml2_loop_vars =
  [`pc:num`; `stackpointer:int64`; `tbl:int64`; `tl:num`; `ws:num list`;
   `ml:num`; `e:uarch_event list`] @
  List.concat (map (fun k -> map (ml2_var k)
    ["st",`:byte list`; "src",`:int64`; "op",`:int64`; "L",`:num`;
     "r",`:num`]) [1;2;3;4]) @
  map ml2_o0 [1;2;3;4];;

let ml2_loop_goal =
  let tm = mk_imp(list_mk_conj ml2_loop_hyps,
                  list_mk_icomb "ensures"
                   [`arm`;
                    mk_abs(`s:armstate`,mk_exists(`m:num`,
                      list_mk_comb(ml2_inv,[`m:num`; `s:armstate`])));
                    ml2_lexit; ml2_loop_frame]) in
  let fvs = frees tm in
  (match subtract fvs ml2_loop_vars with
     [] -> ()
   | v::_ -> failwith ("ml2_loop_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) ml2_loop_vars,tm);;

(*** A piece by a big step from the current state (as ML_BIGSTEP_TAC) ***)

let ML2_BIGSTEP_TAC th alist : tactic =
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
    ARM_BIGSTEP_TAC SLOW2_EXEC ("s"^string_of_int(n + 1)) THEN
    W(fun (_,w) ->
      if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                       with Failure _ -> false)
      then EVENTS_UNABBREV_TAC THEN MEMSAFE_STRIP_TAC
      else REPEAT CONJ_TAC THEN
           FIRST [ML_PRE_MEMSAFE_TAC; ML_FACT_TAC; T4_CONJ_TAC]));;

(*** The facts of stream q for its reload, with the bits used after the ***)
(*** body (in the register of q)                                        ***)

let ML2_LOOP_FACTS_TAC (q:ml2q) : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let b = t2_regval asl s q.qbc in
    let v x ty = ml2_var q.qk (x,ty) in
    let ofs = v "ofs" `:num` and st = v "st" `:byte list` in
    let lst = mk_comb(`LENGTH:byte list->num`,st) in
    let le a b = mk_binop `(<=):num->num->bool` a b in
    let g1 = mk_imp(le `8` ofs,
                    mk_conj(le (mk_binop `(+):num->num->num` ofs `8`) lst,
                            le b `64`))
    and g2 = le ofs lst
    and g3 = mk_binop `(<):num->num->bool` b `2 EXP 32` in
    SUBGOAL_THEN (list_mk_conj [g1; g2; g3]) STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC]);;

(*** The reload of stream q by a big step, its bits used from the state ***)

let ML2_RL_STEP_TAC th (q:ml2q) extra : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let b = t2_regval asl s q.qbc in
    let v x ty = ml2_var q.qk (x,ty) in
    ML2_BIGSTEP_TAC th
     ([("src",v "src" `:int64`); ("st",v "st" `:byte list`);
       ("ofs",v "ofs" `:num`); ("bc",b)] @ extra));;

(*** The loop up to the decision: the body and the four reloads by big ***)
(*** steps, the statuses w1, w2, w3 of streams 1-3                     ***)

let ML2_LOOP_START_TAC =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
    (List.concat(map ml2_pervars [1;2;3;4])) THEN
  ENSURES_EXISTS_PRE_TAC `f:num` THEN PUFF_INIT_TAC "s0" THEN
  ML2_BIGSTEP_TAC ML2_BODY [] THEN
  MAP_EVERY ML2_LOOP_FACTS_TAC ml2_q THEN
  SUBGOAL_THEN `f < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(ASSUME `f = 0 \/ f = 1`) THEN ARITH_TAC; ALL_TAC] THEN
  ML2_RL_STEP_TAC RL2_1 (el 0 ml2_q) [("f",`f:num`); ("w",`0`)] THEN
  ML_STATUS_TAC `w1:num` `ofs1:num` `0` THEN
  ML2_RL_STEP_TAC RL2_2 (el 1 ml2_q) [("f",`f:num`); ("w",`w1:num`)] THEN
  ML_STATUS_TAC `w2:num` `ofs2:num` `w1:num` THEN
  ML2_RL_STEP_TAC RL2_3 (el 2 ml2_q) [("f",`f:num`); ("w",`w2:num`)] THEN
  ML_STATUS_TAC `w3:num` `ofs3:num` `w2:num` THEN
  SUBGOAL_THEN `7 <= L4` ASSUME_TAC THENL
   [MP_TAC(ASSUME `jj4 + 8 <= L4`) THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let j4 = t2_regval asl (rand w) `X10` in
    ML2_RL_STEP_TAC RL2_4 (el 3 ml2_q)
     [("f",`f:num`); ("w",`w3:num`); ("op",`op4:int64`); ("L",`L4:num`);
      ("jj",j4)]);;

(*** The values of stream q at the decision: its bytes after the body ***)
(*** (in its output register) and its bits used then (in huf_rlbc)     ***)

let ml2_stream_vals (asl:(string*thm)list) (s:term) (q:ml2q) =
  let j = t2_regval asl s q.qop in
  let bt = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
             is_eq t && lhs t = list_mk_icomb "read" [q.qbc; s]) asl))) in
  let b = rand(rand bt) in
  j,b;;

(*** Arithmetic from the facts about the variables of the goal only (also ***)
(*** implications, disjunctions and conjunctions of relations)            ***)

let ML2_NARROW_ARITH_TAC : tactic =
  fun (asl,w as gl) ->
    let vs = union [`tl:num`; `ml:num`] (frees w) in
    let rel t =
      (is_binary "<=" t || is_binary "<" t || is_binary "=" t) &&
      type_of(lhand t) = `:num` in
    let rec rel' t =
      rel t || is_neg t && rel(dest_neg t) ||
      (is_disj t || is_imp t || is_conj t) && rel'(lhand t) && rel'(rand t) in
    let ok t =
      rel' t && subset (frees t) vs && not(can (find_term is_cond) t) &&
      not(can (find_term (fun u -> is_const u &&
            mem (fst(dest_const u))
              ["huf_decode"; "zstd_back"; "huf_dentry2"; "EL";
               "num_of_bytelist"])) t) in
    let ths = filter (fun th -> ok(concl th))
                (List.concat(map (CONJUNCTS o snd) asl)) in
    (MAP_EVERY MP_TAC ths THEN ARITH_TAC) gl;;

(*** Arithmetic from the facts sharing a variable with the goal (other ***)
(*** than tl and ml), one step only                                     ***)

let ML2_DEPTH1_ARITH_TAC : tactic =
  let glob = [`tl:num`; `ml:num`] in
  fun (asl,w as gl) ->
    let rel t =
      (is_binary "<=" t || is_binary "<" t || is_binary "=" t) &&
      type_of(lhand t) = `:num` in
    let rec rel' t =
      rel t || is_neg t && rel(dest_neg t) ||
      (is_disj t || is_imp t || is_conj t) && rel'(lhand t) && rel'(rand t) in
    let vs = subtract (frees w) glob in
    let ok t =
      rel' t && not(can (find_term is_cond) t) &&
      not(exists (fun v -> type_of v = `:armstate`) (frees t)) &&
      not(can (find_term (fun u -> is_const u &&
            mem (fst(dest_const u))
              ["huf_decode"; "zstd_back"; "huf_dentry2"; "EL";
               "num_of_bytelist"])) t) &&
      (let f = subtract (frees t) glob in f = [] || intersect f vs <> []) in
    let ths = filter (fun th -> ok(concl th))
                (List.concat(map (CONJUNCTS o snd) asl)) in
    (MAP_EVERY MP_TAC ths THEN ARITH_TAC) gl;;

(*** The conjuncts at the decision: by a fact, by the fact about the left ***)
(*** side and arithmetic, by arithmetic (first from the facts about the   ***)
(*** variables of the goal only: the closure of the facts can take in all ***)
(*** four streams and their divisions), or by the cases of a reload       ***)

let rec ML2_LOOP_CONJ_TAC (asl,w as gl) =
  let facts = fl_all_facts asl in
  let cased =
    can (find_term (fun t -> is_const t &&
           mem (fst(dest_const t)) ["huf_rlofs"; "huf_rlbc"])) w ||
    can (find_term is_cond) w in
  let by_fact =
    match filter (fun th -> aconv (concl th) w) facts with
      th::_ -> ACCEPT_TAC th
    | [] -> NO_TAC
  and by_lhs =
    if not(is_eq w) then NO_TAC else
    match filter (fun th -> let t = concl th in is_eq t && lhs t = lhs w)
                 facts with
      th::_ -> GEN_REWRITE_TAC LAND_CONV [th] THEN
               FIRST [REFL_TAC; AP_TERM_TAC THEN ARITH_TAC;
                      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
                      ML2_NARROW_ARITH_TAC; ML2_DEPTH1_ARITH_TAC;
                      ML2_ARITH_TAC]
    | [] -> NO_TAC
  and by_cases =
    REWRITE_TAC[huf_rlofs; huf_rlbc] THEN ASM_REWRITE_TAC[] THEN
    W(fun (_,w) -> if can (find_term is_cond) w
                   then COND_CASES_TAC THEN ASM_REWRITE_TAC[]
                   else ALL_TAC) THEN
    REPEAT CONJ_TAC THEN ML2_LOOP_CONJ_TAC in
  if cased then FIRST [by_fact; by_cases] gl
  else FIRST [by_fact; by_lhs; CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
              ML2_NARROW_ARITH_TAC; ML2_DEPTH1_ARITH_TAC; ML2_ARITH_TAC] gl;;

(*** On: all four reloaded, 8 more bytes of stream 4; the invariant with ***)
(*** the bytes after the body and the offsets after the reloads          ***)

let ML2_LOOP_ON_TAC vals : tactic =
  SUBGOAL_THEN `8 <= ofs1 /\ 8 <= ofs2 /\ 8 <= ofs3` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w3"; "w2"; "w1"] THEN
    POP_ASSUM MP_TAC THEN MAP_EVERY EXPAND_TAC ["w3"; "w2"; "w1"] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    is_conj(concl th) && lhand(concl th) = `8 <= ofs4`)) THEN
  W(fun (asl,w) ->
    let j4 = fst(el 3 vals) in
    ML_CASE_REWRITE_TAC
     [`8 <= ofs1`; `8 <= ofs2`; `8 <= ofs3`; `8 <= ofs4`; `w3 = 0`;
      mk_binop `(<=):num->num->bool`
        (mk_binop `(+):num->num->num` j4 `8`) `L4:num`]) THEN
  PUFF_FINAL_TAC THEN
  MAP_EVERY (fun (_,b) -> ML_DIVISION_TAC b) vals THEN
  DISJ1_TAC THEN
  EXISTS_TAC (mk_binop `(-):num->num->num` `L4:num` (fst(el 3 vals))) THEN
  CONJ_TAC THENL
   [FIRST [ML2_NARROW_ARITH_TAC; ML2_DEPTH1_ARITH_TAC; ML2_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   (List.concat(map2 (fun k (j,b) ->
      let ofs = ml2_var k ("ofs",`:num`) in
      [j; mk_binop `(-):num->num->num` ofs
            (mk_binop `DIV` b `8`);
       mk_binop `MOD` b `8`]) [1;2;3;4] vals) @ [`1`]) THEN
  REPEAT CONJ_TAC THEN ML2_LOOP_CONJ_TAC;;

(*** Off: the exit, each stream reloaded or not; the facts of the  ***)
(*** decision (the pc, w0 and the status in the frame) for stream 4 ***)
(*** reloaded or not                                                 ***)

let ML2_LOOP_OFF_CASE_TAC vals : tactic =
  let j4 = fst(el 3 vals) in
  let c2 = mk_conj(`w3 = 0`,mk_binop `(<=):num->num->bool`
                     (mk_binop `(+):num->num->num` j4 `8`) `L4:num`) in
  let rule cs th =
    if mem (concl th) cs ||
       not(can (find_term ((=) `8 <= ofs4`)) (concl th)) then th
    else REWRITE_RULE (map ASSUME cs) th in
  ASM_CASES_TAC `8 <= ofs4` THENL
   [SUBGOAL_THEN (mk_neg c2) ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th -> let t = concl th in
        is_neg t && is_conj(dest_neg t) && lhand(dest_neg t) = `8 <= ofs4`))
      THEN REWRITE_TAC[ASSUME `8 <= ofs4`];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(rule [`8 <= ofs4`; mk_neg c2]);
    RULE_ASSUM_TAC(rule [`~(8 <= ofs4)`])];;

let ML2_LOOP_OFF_TAC vals : tactic =
  ML2_LOOP_OFF_CASE_TAC vals THEN PUFF_FINAL_TAC THEN
  MAP_EVERY (fun (_,b) -> ML_DIVISION_TAC b) vals THEN
  DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC
   (List.concat(map2 (fun k (j,b) ->
      let ofs = ml2_var k ("ofs",`:num`) in
      [j; list_mk_icomb "huf_rlofs" [ofs; b];
       list_mk_icomb "huf_rlbc" [ofs; b]]) [1;2;3;4] vals) @
    map (fun k ->
      mk_cond(mk_binop `(<=):num->num->bool` `8` (ml2_var k ("ofs",`:num`)),
              `1`,`f:num`)) [1;2;3;4]) THEN
  REPEAT CONJ_TAC THEN ML2_LOOP_CONJ_TAC;;

(*** The status of the flags (f = 0 only before any reload) one stream ***)
(*** at a time                                                          ***)

let ML2_FLAG_SPLIT_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let t = concl th in
    if is_imp t && lhand t = `f = 0` && is_conj(rand t) then
      MAP_EVERY (fun c -> ASSUME_TAC(DISCH `f = 0` c))
        (CONJUNCTS(UNDISCH th))
    else NO_TAC);;

let ML2_LOOP_DECIDE_TAC : tactic =
  ML2_FLAG_SPLIT_TAC THEN
  W(fun (asl,w) ->
    let s = rand w in
    let vals = map (ml2_stream_vals asl s) ml2_q in
    let j4 = fst(el 3 vals) in
    let cnd = list_mk_conj
      [`8 <= ofs4`; `w3 = 0`;
       mk_binop `(<=):num->num->bool`
         (mk_binop `(+):num->num->num` j4 `8`) `L4:num`] in
    ASM_CASES_TAC cnd THENL
     [ML2_LOOP_ON_TAC vals; ML2_LOOP_OFF_TAC vals]);;

let ML2_LOOP_TAC = ML2_LOOP_START_TAC THEN ML2_LOOP_DECIDE_TAC;;

(*** The proof of the main loop ***)

let ML2_LOOP = prove(ml2_loop_goal, ML2_LOOP_TAC);;

(* ------------------------------------------------------------------------- *)
(* The setup of the main loop (ST2_CORRECT), the rest after it for a valid   *)
(* block (RS2_CORRECT), the inits of the four bit streams (IN2_k_CORRECT)    *)
(* and the entry checks (EN2_CORRECT).                                       *)
(* ------------------------------------------------------------------------- *)

(*** The setup of the main loop at 0x3614: the loop (0x3750) if the     ***)
(*** fourth segment has at least 8 bytes, with the registers of the    ***)
(*** loop from BIT_DStream in the frame and the slots of the frame,    ***)
(*** and otherwise straight to the order check (0x3a98)                ***)

let st2_vars =
  [`pc:num`; `stackpointer:int64`; `dst:int64`; `n:num`; `q:num`;
   `dt:int64`; `dh:int32`; `tl:num`; `x25:int64`; `x26:int64`] @
  map (fun k -> mk_var("b"^string_of_int k,`:num`)) [1;2;3;4] @
  map (fun k -> mk_var("s"^string_of_int k,`:int64`)) [1;2;3;4] @
  map (fun k -> mk_var("c"^string_of_int k,`:int64`)) [1;2;3;4] @
  map (fun k -> mk_var("p"^string_of_int k,`:int64`)) [1;2;3;4] @
  [`e:uarch_event list`];;

let st2_goal =
  let sv k = mk_var("s"^string_of_int k,`:int64`)
  and cv k = mk_var("c"^string_of_int k,`:int64`)
  and pv k = mk_var("p"^string_of_int k,`:int64`) in
  let add8 v = mk_comb(mk_comb(`word_add:int64->int64->int64`,v),
                       `word 8:int64`) in
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x3614) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X14 s = word_add dst (word n) /\
      read X11 s = word_add dst (word (3 * q)) /\
      read X12 s = word_add dst (word q) /\
      read X13 s = word_add dst (word (2 * q)) /\
      read X19 s = dst /\ read X20 s = word n /\ read X23 s = dt /\
      read X8 s = word_zx (dh:int32) /\ read X1 s = word 0 /\
      read X3 s = word b1 /\ read X22 s = word b2 /\ read X21 s = word b3 /\
      read X18 s = s1 /\ read X15 s = s2 /\ read X9 s = s3 /\
      read X24 s = s4 /\ read X25 s = x25 /\ read X26 s = x26`] @
    List.concat (map (fun k ->
      let a = 224 + 40 * (k - 1) in
      [ml_mem64 a (cv k); ml_mem64 (a + 16) (pv k)]) [1;2;3;4]) @
    [ml_mem32 352 `b4:num`;
     `read events s = e`])) in
  let loop = list_mk_conj
   ([`read PC s = word(pc + 0x3750)`;
     `read X2 s = word(64 - tl) /\ read X5 s = word_add dt (word 4)`;
     `read X12 s = c1 /\ read X16 s = p1 /\ read X3 s = word b1 /\
      read X13 s = c2 /\ read X17 s = p2 /\ read X22 s = word b2 /\
      read X14 s = c3 /\ read X18 s = p3 /\ read X21 s = word b3 /\
      read X11 s = c4 /\ read X15 s = p4 /\ read X8 s = word b4`;
     `read X19 s = dst /\ read X7 s = word_add dst (word q) /\
      read X6 s = word_add dst (word (2 * q)) /\
      read X10 s = word_add dst (word (3 * q))`;
     ml_mem64 120 `word_add dst (word (n - 7)):int64`;
     ml_mem32 132 `0`; ml_mem32 136 `0`; ml_mem32 140 `0`;
     ml_mem32 184 `0`;
     ml_mem64 144 `word_add dst (word n):int64`; ml_mem64 152 `s1:int64`;
     ml_mem64 160 `word_add dst (word q):int64`;
     ml_mem64 168 `word_add dst (word (2 * q)):int64`;
     ml_mem64 176 `word_add dst (word (3 * q)):int64`;
     ml_mem32 188 `tl:num`; ml_mem64 192 `word n:int64`;
     ml_mem64 200 `s2:int64`; ml_mem64 208 `s3:int64`;
     ml_mem64 216 `s4:int64`;
     ml_mem64 64 `x25:int64`; ml_mem64 72 `x26:int64`]) in
  let skip = list_mk_conj
   [`read PC s = word(pc + 0x3a98)`;
    `read X5 s = word_add dt (word 4) /\ read X23 s = word tl`;
    `read X18 s = s1 /\ read X15 s = s2 /\ read X9 s = s3 /\
     read X24 s = s4 /\ read X20 s = word n /\
     read X25 s = x25 /\ read X26 s = x26`;
    `read X14 s = word_add dst (word n) /\
     read X19 s = dst /\ read X7 s = word_add dst (word q) /\
     read X6 s = word_add dst (word (2 * q)) /\
     read X10 s = word_add dst (word (3 * q)) /\
     read X12 s = word_add dst (word q) /\
     read X13 s = word_add dst (word (2 * q)) /\
     read X11 s = word_add dst (word (3 * q))`;
    ml_mem64 120 `word_sub (word_add dst (word n)) (word 7):int64`] in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [mk_disj(mk_conj(`8 <= n - 3 * q`,loop),mk_conj(`n - 3 * q < 8`,skip));
    `?e2. read events s = APPEND e2 e /\
          memaccess_inbounds e2 [word_sub stackpointer (word 496),496]
                                [word_sub stackpointer (word 496),496]`]) in
  let frame =
   `MAYCHANGE [PC; X0; X2; X4; X5; X6; X7; X8; X10; X11; X12; X13; X14;
               X15; X16; X17; X18; X23; X25; X26; X27; X30] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),16);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 120),24);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 144),80)]` in
  mk_small_goal st2_vars
   (ml_code_hyps @
    [`aligned 16 (stackpointer:int64)`;
     `val(dst:int64) + n < 2 EXP 64 /\ 3 * q <= n /\ 5 < n /\
      n < 2 EXP 28 /\ b4 < 2 EXP 32`;
     `val(word_subword (dh:int32) (16,8):byte) = tl /\ 1 <= tl /\ tl <= 12`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word pc,32000)`])
   pre post frame;;

let ST2_SUB7 = prove
 (`!(p:int64) n. 7 <= n
                 ==> word_sub (word_add p (word n)) (word 7) =
                     word_add p (word (n - 7))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let ST2_VAL_TAC : tactic =
  MP_TAC(SPECL [`dst:int64`; `n - 7`] VAL_WORD_ADD_NOWRAP) THEN
  MP_TAC(SPECL [`dst:int64`; `3 * q`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN ML2_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN ML2_ARITH_TAC; DISCH_TAC];;

let ST2_CORRECT = prove
 (st2_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN ML2_SIM_UNTIL_TAC [0x3628] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FA_UBFX]) THEN
  FA_STATE_REWRITE_TAC
    [ASSUME `val(word_subword (dh:int32) (16,8):byte) = tl`] THEN
  FA_STATE_REWRITE_TAC[MP (SPECL [`dst:int64`; `n:num`; `3 * q`] ST_SUB_ADD)
    (ASSUME `3 * q <= n`)] THEN
  ASM_CASES_TAC `8 <= n - 3 * q` THENL
   [SUBGOAL_THEN `7 <= n` ASSUME_TAC THENL [ML2_ARITH_TAC; ALL_TAC] THEN
    FA_STATE_REWRITE_TAC[MP (SPECL [`dst:int64`; `n:num`] ST2_SUB7)
      (ASSUME `7 <= n`)] THEN
    ML2_SIM_UNTIL_TAC [0x3630] THEN ST2_VAL_TAC THEN
    ML2_SIM_UNTIL_TAC [0x3750] THEN
    FA_STATE_REWRITE_TAC
     [MP (SPEC `b4:num` ST_ZX32) (ASSUME `b4 < 2 EXP 32`);
      MP (MP (SPEC `tl:num` ST_SHIFT_LEMMA)
             (MP (ARITH_RULE `tl <= 12 ==> tl < 13`) (ASSUME `tl <= 12`)))
         (ASSUME `1 <= tl`)] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    ML2_SIM_UNTIL_TAC [0x3a98] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    ML2_ARITH_TAC]);;

(*** The rest of the slow path, valid case: from the check of the order ***)
(*** of the outputs (0x3a98), the tails of the four streams and the     ***)
(*** end checks, to the epilogue (0x333c) with the result n and the     ***)
(*** bytes of the four outputs                                          ***)

(*** The tails without the code in their postconditions (a big step must ***)
(*** not see it there, or it takes that for the code before the step)    ***)

let RS2_ENSURES_WEAKEN = RS_ENSURES_WEAKEN;;

let rs2_tail_post spec =
  let p = tail2_inst spec (t2c_post spec) in
  let v,b = dest_abs p in
  let code = subst [v,`s:armstate`]
    `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc` in
  let rec drop t =
    if is_conj t then
      let l,r = dest_conj t in
      if l = code then drop r
      else if is_conj l then mk_conj(drop l,r)
      else mk_conj(l,drop r)
    else t in
  mk_abs(v,drop b);;

let rs2_tail_goal spec =
  let tm = mk_imp(t2_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; tail2_inst spec (t2c_entry spec);
                    rs2_tail_post spec; tail2_frame spec]) in
  let vs = t2_vars @ [`jj:num`; `ofs:num`; `bc:num`] in
  list_mk_forall(filter (fun v -> mem v (frees tm)) vs,tm);;

let RS2_TAIL_TAC th : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL th)) THEN
  MATCH_MP_TAC RS2_ENSURES_WEAKEN THEN CONJ_TAC THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[];;

(*** The end checks at 0x457c: success, with the result n, if each      ***)
(*** stream k has its pointer p_k at its start a_k and all 64 bits of   ***)
(*** its container used, and otherwise the error -20, both with the     ***)
(*** callee-saved registers x25-x28 restored, at 0x333c (as ENDCHK)     ***)

let endchk2_goal =
 `!pc stackpointer (p1:int64) (a1:int64) b1 (p2:int64) (a2:int64) b2
   (p3:int64) (a3:int64) b3 (p4:int64) (a4:int64) b4 n
   (v25:int64) (v26:int64) (v27:int64) (v28:int64) e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     aligned 16 stackpointer /\
     b1 < 2 EXP 32 /\ b2 < 2 EXP 32 /\ b3 < 2 EXP 32 /\ b4 < 2 EXP 32 /\
     nonoverlapping (word_sub stackpointer (word 496),496) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x457c) /\
               read SP s = word_sub stackpointer (word 496) /\
               read X21 s = p1 /\ read X18 s = a1 /\
               read X12 s = p2 /\ read X15 s = a2 /\
               read X7 s = p3 /\ read X9 s = a3 /\
               read X3 s = p4 /\ read X24 s = a4 /\ read X20 s = word n /\
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
          (\s. read PC s = word(pc + 0x333c) /\
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

let ENDCHK2_FIN_TAC =
  ML2_SIM_UNTIL_TAC [0x333c] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let ENDCHK2_CORRECT = prove
 (endchk2_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  let split2 p a b k =
    ENDCHK_PTR_CASES_TAC p a THENL [ASM_CASES_TAC b THEN k; k] in
  split2 `p1:int64` `a1:int64` `b1 = 64`
   (split2 `p2:int64` `a2:int64` `b2 = 64`
     (ENDCHK_PTR_CASES_TAC `p3:int64` `a3:int64` THENL
       [ENDCHK_PTR_CASES_TAC `p4:int64` `a4:int64` THENL
         [ASM_CASES_TAC `b3 = 64` THEN ASM_CASES_TAC `b4 = 64` THEN
          ENDCHK2_FIN_TAC;
          ENDCHK2_FIN_TAC];
        ENDCHK2_FIN_TAC])));;

(*** The goal of the rest: from 0x3a98 with each stream after jj bytes ***)
(*** in a good state, its BIT_DStream in the frame, to 0x333c with the ***)
(*** result n and the bytes of the four outputs                        ***)

let rs2_inst k tm =
  vsubst (map (fun (s,ty) -> ml2_var k (s,ty),mk_var(s,ty)) ml2_names) tm;;

let rs2_exit1 (q:ml2q) = rs2_inst q.qk (list_mk_conj
 [vsubst [q.qop,t2v "r_op"]
   `read (r_op:tailreg) s = word_add op (word jj)`;
  subst [mk_small_numeral q.qsofs,`s_c:num`;
         mk_small_numeral(q.qsofs + 8),`s_b:num`;
         mk_small_numeral(q.qsofs + 16),`s_p:num`] t2c_bd;
  `read (memory :> bytes(src,LENGTH(st:byte list))) s =
   num_of_bytelist st /\
   read (memory :> bytes(op,jj)) s =
   num_of_bytelist(FST(huf_decode ws ml st r jj)) /\
   SND(SND(huf_decode ws ml st r jj)) /\
   FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
   (ofs = 0 \/ ofs + 8 <= LENGTH st) /\ jj <= L`]);;

let rs2_lrr = ml2_lrr and rs2_lwr =
  mk_list(map (fun k -> mk_pair(ml2_var k ("op",`:int64`),
                                ml2_var k ("L",`:num`))) [1;2;3;4] @
          [`word_sub stackpointer (word 496):int64,496`],`:int64#num`);;

let rs2_pre =
  let v k s ty = ml2_var k (s,ty) in
  with_memsafe rs2_lrr rs2_lwr (mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x3a98) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X5 s = tbl /\
      read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable2 ws ml tl) /\
      read X23 s = word tl /\ read X20 s = word n`;
     mk_eq(`read X14 s`,list_mk_icomb "word_add"
       [v 4 "op" `:int64`; mk_comb(`word:num->int64`,v 4 "L" `:num`)]);
     mk_eq(`read X12 s`,v 2 "op" `:int64`);
     mk_eq(`read X13 s`,v 3 "op" `:int64`);
     mk_eq(`read X11 s`,v 4 "op" `:int64`);
     mk_eq(`read X18 s`,v 1 "src" `:int64`);
     mk_eq(`read X15 s`,v 2 "src" `:int64`);
     mk_eq(`read X9 s`,v 3 "src" `:int64`);
     mk_eq(`read X24 s`,v 4 "src" `:int64`);
     rs2_inst 1 `read X28 s = word_add src (word 8)`;
     rs2_inst 2 (t2_lim_mem 96); rs2_inst 3 (t2_lim_mem 104);
     rs2_inst 4 (t2_lim_mem 112);
     rs2_inst 4 (subst [t2_spk 120,`a:int64`]
       `read (memory :> bytes64 a) s =
        word_sub (word_add op (word L)) (word 7)`);
     `read X25 s = v25 /\ read X26 s = v26`;
     ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`] @
    map rs2_exit1 ml2_q)));;

let rs2_post = with_memsafe rs2_lrr rs2_lwr (mk_abs(`s:armstate`,
  list_mk_conj
   ([`read PC s = word(pc + 0x333c) /\ read X0 s = word n`] @
    map (fun k -> rs2_inst k
     `read (memory :> bytes(op,L)) s =
      num_of_bytelist(FST(huf_decode ws ml (st:byte list) r L))`)
      [1;2;3;4] @
    [`read X25 s = v25 /\ read X26 s = v26 /\
      read X27 s = v27 /\ read X28 s = v28`])));;

let rs2_frame =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X6; X7; X8; X10; X11; X12; X13; X16;
             X17; X19; X21; X22; X25; X26; X27; X28; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(op1,L1); memory :> bytes(op2,L2);
             memory :> bytes(op3,L3); memory :> bytes(op4,L4);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),16);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 224),160)]`;;

let rs2_hyps =
  ml2_loop_hyps @
  [`word_add op1 (word L1) = op2:int64 /\
    word_add op2 (word L2) = op3:int64 /\
    word_add op3 (word L3) = op4:int64`;
   `~(val(op1:int64) = 0) /\ ~(val(op2:int64) = 0) /\
    ~(val(op3:int64) = 0) /\ ~(val(op4:int64) = 0)`];;

let rs2_vars =
  [`pc:num`; `stackpointer:int64`; `tbl:int64`; `tl:num`; `ws:num list`;
   `ml:num`; `n:num`; `v25:int64`; `v26:int64`; `v27:int64`; `v28:int64`;
   `e:uarch_event list`] @
  List.concat (map (fun k -> map (ml2_var k) ml2_names) [1;2;3;4]);;

let rs2_goal =
  let tm = mk_imp(list_mk_conj rs2_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; rs2_pre; rs2_post; rs2_frame]) in
  let fvs = frees tm in
  (match subtract fvs rs2_vars with
     [] -> ()
   | v::_ -> failwith ("rs2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) rs2_vars,tm);;

(*** The tails without the code in their postconditions ***)

let RS2_TAIL1 = prove(rs2_tail_goal tail2_1, RS2_TAIL_TAC TAIL2_1_TAIL);;
let RS2_TAIL2 = prove(rs2_tail_goal tail2_2, RS2_TAIL_TAC TAIL2_2_TAIL);;
let RS2_TAIL3 = prove(rs2_tail_goal tail2_3, RS2_TAIL_TAC TAIL2_3_TAIL);;
let RS2_TAIL4 = prove(rs2_tail_goal tail2_4, RS2_TAIL_TAC TAIL2_4_TAIL);;

(*** The facts for the order check: the values of the outputs and of ***)
(*** their current positions                                         ***)

let RS2_ORDER_FACTS_TAC : tactic =
  MAP_EVERY (fun (a,b) ->
    let la = ml2_var a ("L",`:num`) and ja = ml2_var a ("jj",`:num`) in
    let oa = ml2_var a ("op",`:int64`) and ob = ml2_var b ("op",`:int64`) in
    let lt = mk_binop `(<):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,oa))
                  la) `2 EXP 64` in
    let eqab = mk_eq(list_mk_icomb "word_add"
                       [oa; mk_comb(`word:num->int64`,la)],ob) in
    let th1 = MP (SPECL [oa; la] VAL_WORD_ADD_NOWRAP) (ASSUME lt) in
    let th1' = REWRITE_RULE[ASSUME eqab] th1 in
    let ltj = mk_binop `(<):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,oa))
                  ja) `2 EXP 64` in
    ASSUME_TAC th1' THEN
    SUBGOAL_THEN ltj ASSUME_TAC THENL [ML2_ARITH_TAC; ALL_TAC] THEN
    ASSUME_TAC(MP (SPECL [oa; ja] VAL_WORD_ADD_NOWRAP) (ASSUME ltj)))
   [1,2; 2,3; 3,4];;

(*** The order check, with the ends of the first three outputs as op_k + ***)
(*** L_k (with the equations to op_k+1 out of the way)                   ***)

let RS2_ORDER_TAC : tactic =
  let hs = [`word_add op1 (word L1) = op2:int64`;
            `word_add op2 (word L2) = op3:int64`;
            `word_add op3 (word L3) = op4:int64`]
  and regs = [`X12`; `X13`; `X11`] in
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
    ML2_SIM_UNTIL_TAC [0x3ab4] THEN MAP_EVERY ASSUME_TAC hths);;

(*** The tail of stream k by a big step, and the end checks ***)

let RS2_TAIL_STEP_TAC k th : tactic =
  let names = map fst ml2_names in
  ML2_BIGSTEP_TAC th
   (map (fun n -> n,ml2_var k (n,assoc n ml2_names)) names @
    [("x25",`v25:int64`); ("x26",`v26:int64`)]);;

let RS2_ENDCHK_TAC : tactic =
  ML2_BIGSTEP_TAC ENDCHK2_CORRECT
   (map (fun k -> "a"^string_of_int k,ml2_var k ("src",`:int64`))
        [1;2;3;4] @
    map (fun k -> "p"^string_of_int k,
           list_mk_icomb "word_add"
             [ml2_var k ("src",`:int64`); `word 0:int64`])
        [1;2;3;4] @
    map (fun k -> "b"^string_of_int k,`64`) [1;2;3;4]);;

let RS2_CORRECT = prove
 (rs2_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RS2_ORDER_FACTS_TAC THEN
  RS2_ORDER_TAC THEN
  MAP_EVERY (fun (k,th) -> RS2_TAIL_STEP_TAC k th)
   [1,RS2_TAIL1; 2,RS2_TAIL2; 3,RS2_TAIL3; 4,RS2_TAIL4] THEN
  RS2_ENDCHK_TAC THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0]);;

(*** The initializations of the BIT_DStreams of the four streams of the ***)
(*** slow path (0x34f8, 0x3540, 0x3584, 0x35c8), as those of the 4X1     ***)
(*** proof (IN1..IN4) with the code of 4X2                               ***)

(*** The simulation of the 4X1 proof with the code of 4X2 ***)

let ZSTD2_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC SLOW2_EXEC [n] THEN ZSTD_SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                  WORD_CMP_64_SFLAGS) THEN
                TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let ZSTD2_SIM_UNTIL_TAC stops =
  let num_of_state s =
    let n = fst(dest_var s) in
    int_of_string(String.sub n 1 (String.length n - 1)) in
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k n (asl,w as gl) =
    let pc = current_pc gl in
    if mem pc stops then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "ZSTD2_SIM_UNTIL_TAC"
    else (ZSTD2_STEP_TAC n THEN run (k - 1) (n + 1)) gl in
  fun (asl,w as gl) -> run 80 (num_of_state(rand w) + 1) gl;;

(*** The tactics of the inits (as IN_LONG_TAC, IN_SHORT_TAC, IN_TAC), the ***)
(*** errors at the epilogue 0x333c                                        ***)

let IN2_LONG_TAC (sp:inspec) : tactic =
  ZSTD2_SIM_UNTIL_TAC [sp.ilast] THEN IN_LASTBYTE_TAC sp.ibase sp.ilastq THEN
  ZSTD2_SIM_UNTIL_TAC [sp.icont] THEN IN_CONT_TAC sp.ibase sp.iconteqs THEN
  ZSTD2_SIM_UNTIL_TAC [sp.icbz] THEN
  ASM_CASES_TAC `EL (l - 1) (st:byte list) = word 0` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x333c] THEN IN_EVADDR_TAC sp THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(val(EL (l - 1) (st:byte list)) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    ZSTD2_SIM_UNTIL_TAC [sp.iend] THEN IN_EVADDR_TAC sp THEN
    PUFF_FINAL_TAC THEN
    IN_SHIFT_RULE_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; NUM_REDUCE_CONV `2 EXP 64`] THEN
    ASM_REWRITE_TAC[]];;

let IN2_SHORT_TAC (sp:inspec) k : tactic =
  IN_BYTES_TAC sp.ibase k THEN ZSTD2_SIM_UNTIL_TAC [sp.ishort] THEN
  IN_FIRST_TAC sp THEN IN_LAST_CASES_TAC k THENL
   [ZSTD2_SIM_UNTIL_TAC [0x333c] THEN IN_EVADDR_TAC sp THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    ZSTD2_SIM_UNTIL_TAC [sp.iend] THEN IN_EVADDR_TAC sp THEN
    PUFF_FINAL_TAC THEN
    IN_SHORT_FIN_TAC k];;

let IN2_TAC (sp:inspec) : tactic =
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `l = 0` THENL
   [ZSTD2_SIM_UNTIL_TAC [0x333c] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `8 <= l` THENL [IN2_LONG_TAC sp; ALL_TAC] THEN
  SUBGOAL_THEN `l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(8 <= l)`; `~(l = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THENL
  map (IN2_SHORT_TAC sp) (1--7);;

(*** Stream 1 at 0x34f8 (cSrc in x22, its size in x3 and x4); x27 and  ***)
(*** x28 saved in the frame                                            ***)

let in2_1_goal =
  let win = subst [in_ofs0,`ofs:num`]
   `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64)
    :int64` in
  let src = `word_add csrc (word 6):int64` in
  let pre = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x34f8) /\
     read SP s = word_sub stackpointer (word 496) /\
     read X22 s = csrc /\ read X3 s = word l /\ read X4 s = word l /\
     read X27 s = v27 /\ read X28 s = v28 /\ read X0 s = x0`;
    subst [src,`a:int64`]
     `read (memory :> bytes(a,LENGTH(st:byte list))) s = num_of_bytelist st`;
    `read events s = e`]) in
  let good = list_mk_conj
   ([`read PC s = word(pc + 0x3540)`;
     `read X15 s = word_add csrc (word (6 + l)) /\
      read X28 s = word_add csrc (word 14) /\
      read X18 s = word_add csrc (word 6)`;
     mk_eq(`read X3 s`,mk_comb(`word:num->int64`,in_bc0));
     ml_mem64 224 win; ml_mem32 232 in_bc0;
     ml_mem64 240 (subst [in_ofs0,`ofs:num`]
                    `word_add csrc (word (6 + ofs)):int64`);
     ml_mem64 248 src; ml_mem64 256 `word_add csrc (word 14):int64`;
     ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`;
     `read X0 s = x0`]) in
  let bad = list_mk_conj
   [`read PC s = word(pc + 0x333c)`; mk_eq(`read X0 s`,in_err);
    `read X27 s = v27 /\ read X28 s = v28`] in
  let ms = subst [src,`a:int64`]
   `?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2 [a,LENGTH(st:byte list);
                                word_sub stackpointer (word 496),496]
                               [word_sub stackpointer (word 496),496]` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [mk_disj(mk_conj(`~(l = 0) /\ ~(EL (l - 1) (st:byte list) = word 0)`,good),
            mk_conj(`l = 0 \/ EL (l - 1) (st:byte list) = word 0`,bad));
    ms]) in
  let frame =
   `MAYCHANGE [PC; X0; X3; X9; X15; X16; X17; X18; X27; X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 80),16);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 224),40)]` in
  mk_small_goal
   [`pc:num`; `stackpointer:int64`; `csrc:int64`; `st:byte list`; `l:num`;
    `v27:int64`; `v28:int64`; `x0:int64`; `e:uarch_event list`]
   (ml_code_hyps @
    [`aligned 16 (stackpointer:int64)`;
     `LENGTH(st:byte list) = l /\ l < 2 EXP 16 /\
      val(csrc:int64) + 6 + l + 8 < 2 EXP 64`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word_add (csrc:int64) (word 6),LENGTH(st:byte list))`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word pc,32000)`])
   pre post frame;;

let in2_1 =
  let nz = ASSUME `~(l = 0)` in
  let one = ARITH_RULE `~(l = 0) ==> 1 <= l /\ 1 <= 2 EXP 64` in
  let red = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) in
  {ibase = `word_add csrc (word 6):int64`;
   ilastq = MP (red(SPECL [`6`; `l:num`; `1`] IN_WORD_NEG)) (MP one nz);
   iconteqs = [];
   ievq = [MP (red(SPECL [`word_add csrc (word 6):int64`; `l:num`; `1`]
                          FA_ADDR_NEG)) (MP one nz)];
   ifirstq = []; ilast = 0x3510; icont = 0x3528; icbz = 0x3530;
   ishort = 0x39fc; iend = 0x3540};;

(*** Streams 2, 3 and 4 (at 0x3540, 0x3584 and 0x35c8), as stream 1 but ***)
(*** with the start p of the stream in a register, p = q + l' for the   ***)
(*** start q and the size l' of the stream before (the first byte of a  ***)
(*** short stream is loaded from there); on errors x27 and x28 are      ***)
(*** restored from the frame, otherwise x28 (the limit of stream 1) is  ***)
(*** kept                                                               ***)

let mk_in2_goal ia preregs good frame =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc`;
     mk_eq(`read PC s`,mk_comb(`word:num->int64`,
                         mk_binop `(+):num->num->num` `pc:num`
                           (mk_small_numeral ia)));
     `read SP s = word_sub stackpointer (word 496)`; preregs;
     `read X28 s = x28`;
     ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`;
     `read (memory :> bytes(p,LENGTH(st:byte list))) s = num_of_bytelist st`;
     `read events s = e`])) in
  let ms =
   `?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2 [p,LENGTH(st:byte list);
                                word_sub stackpointer (word 496),496]
                               [word_sub stackpointer (word 496),496]` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [mk_disj(mk_conj(`~(l = 0) /\ ~(EL (l - 1) (st:byte list) = word 0)`,
                    list_mk_conj (good @ [`read X28 s = x28`])),
            mk_conj(`l = 0 \/ EL (l - 1) (st:byte list) = word 0`,
                    list_mk_conj [`read PC s = word(pc + 0x333c)`;
                                  mk_eq(`read X0 s`,in_err);
                                  `read X27 s = v27 /\ read X28 s = v28`]));
    ms]) in
  mk_small_goal
   [`pc:num`; `stackpointer:int64`; `p:int64`; `q:int64`; `st:byte list`;
    `l:num`; `l':num`; `v27:int64`; `v28:int64`; `x0:int64`; `x28:int64`;
    `e:uarch_event list`]
   (ml_code_hyps @
    [`aligned 16 (stackpointer:int64)`;
     `LENGTH(st:byte list) = l /\ l < 2 EXP 32 /\
      val(p:int64) + l + 8 < 2 EXP 64`;
     `word_add q (word l') = p:int64 /\ l' < 2 EXP 16`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (p:int64,LENGTH(st:byte list))`;
     `nonoverlapping (word_sub (stackpointer:int64) (word 496),496)
                     (word pc,32000)`])
   pre post frame;;

let in2_2_goal =
  mk_in2_goal 0x3540
   `read X15 s = p /\ read X6 s = word l /\ read X7 s = word l /\
    read X18 s = q /\ read X4 s = word l' /\ read X0 s = x0`
   ([`read PC s = word(pc + 0x3584)`;
     `read X9 s = word_add p (word l) /\ read X0 s = x0`;
     mk_eq(`read X22 s`,mk_comb(`word:num->int64`,in_bc0))] @
    in_struct 264 @ [ml_mem64 96 `word_add p (word 8):int64`])
   `MAYCHANGE [PC; X0; X4; X6; X9; X16; X22; X27; X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 96),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 264),40)]`;;

let in2_3_goal =
  mk_in2_goal 0x3584
   `read X9 s = p /\ read X10 s = word l /\ read X5 s = word l /\
    read X15 s = q /\ read X7 s = word l' /\ read X0 s = x0`
   ([`read PC s = word(pc + 0x35c8)`;
     `read X24 s = word_add p (word l) /\ read X0 s = x0`;
     mk_eq(`read X21 s`,mk_comb(`word:num->int64`,in_bc0))] @
    in_struct 304 @ [ml_mem64 104 `word_add p (word 8):int64`])
   `MAYCHANGE [PC; X0; X4; X6; X10; X16; X21; X24; X27; X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 104),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 304),40)]`;;

let in2_4_goal =
  mk_in2_goal 0x35c8
   `read X24 s = p /\ read X0 s = word l /\ read X2 s = word (l + 6) /\
    read X9 s = q /\ read X5 s = word l'`
   ([`read PC s = word(pc + 0x3614)`] @
    in_struct 344 @ [ml_mem64 112 `word_add p (word 8):int64`])
   `MAYCHANGE [PC; X0; X2; X4; X5; X6; X27; X28] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 112),8);
               memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 344),40)]`;;

let in2_2 = in_spec `l:num` 0x3554 0x356c 0x3574 0x45c8 0x3584;;
let in2_3 = in_spec `l:num` 0x3598 0x35b0 0x35b8 0x4664 0x35c8;;
let in2_4 =
  let sp = in_spec `l + 6` 0x35dc 0x35f4 0x35fc 0x46f4 0x3614
  and eq = ARITH_RULE `(l + 6) - 14 = l - 8` in
  {sp with iconteqs = [eq]; ievq = sp.ievq @ [eq]};;

let IN2_1_CORRECT = prove(in2_1_goal, IN2_TAC in2_1);;
let IN2_2_CORRECT = prove(in2_2_goal, IN2_TAC in2_2);;
let IN2_3_CORRECT = prove(in2_3_goal, IN2_TAC in2_3);;
let IN2_4_CORRECT = prove(in2_4_goal, IN2_TAC in2_4);;

(*** The entry checks of the slow path (0x32d0), as EN of the 4X1 proof: ***)
(*** n > 5, at least 10 bytes, the first three streams within the block ***)
(*** (the size of the fourth not wrapping) and opStart4 <= oend; the    ***)
(*** registers for the inits: the sizes (twice), the starts of the      ***)
(*** outputs and the table header                                       ***)

let en2_goal =
  let pre = mk_abs(`s:armstate`,list_mk_conj
   [`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
     read PC s = word(pc + 0x32d0) /\
     read X19 s = dst /\ read X20 s = word n /\ read X22 s = src /\
     read X18 s = word(LENGTH(blk:byte list)) /\ read X23 s = dt`;
    `read (memory :> bytes(src,LENGTH(blk:byte list))) s =
     num_of_bytelist blk`;
    `read (memory :> bytes32 dt) s = dh`;
    `read events s = e`]) in
  let q = `(n + 3) DIV 4` in
  let good = list_mk_conj
   [`read PC s = word(pc + 0x34f8)`;
    mk_eq(`read X3 s`,mk_comb(`word:num->int64`,en_j 0));
    mk_eq(`read X4 s`,mk_comb(`word:num->int64`,en_j 0));
    mk_eq(`read X6 s`,mk_comb(`word:num->int64`,en_j 1));
    mk_eq(`read X7 s`,mk_comb(`word:num->int64`,en_j 1));
    mk_eq(`read X10 s`,mk_comb(`word:num->int64`,en_j 2));
    mk_eq(`read X5 s`,mk_comb(`word:num->int64`,en_j 2));
    mk_eq(`read X0 s`,mk_comb(`word:num->int64`,en_l4));
    mk_eq(`read X2 s`,mk_comb(`word:num->int64`,
                        mk_binop `(+):num->num->num` en_l4 `6`));
    `read X14 s = word_add dst (word n)`;
    subst [q,`q:num`]
     `read X12 s = word_add dst (word q) /\
      read X13 s = word_add dst (word (2 * q)) /\
      read X11 s = word_add dst (word (3 * q))`;
    `read X8 s = word_zx (dh:int32) /\ read X1 s = word 0`] in
  let bad = `read PC s = word(pc + 0x333c) /\
             read X0 s = word 18446744073709551596` in
  let post = mk_abs(`s:armstate`,list_mk_conj
   [mk_disj(mk_conj(en_ok,good),mk_conj(mk_neg en_ok,bad));
    `?e2. read events s = APPEND e2 e /\
          memaccess_inbounds e2 [src,LENGTH(blk:byte list); dt,4] []`]) in
  let frame =
   `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
               X13; X14] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` in
  mk_small_goal
   [`pc:num`; `dst:int64`; `n:num`; `src:int64`; `blk:byte list`;
    `dt:int64`; `dh:int32`; `e:uarch_event list`]
   (ml_code_hyps @
    [`val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64 /\
      val(dst:int64) + n < 2 EXP 64 /\ n < 2 EXP 28`])
   pre post frame;;

let EN2_CCMP_TAC : tactic =
  SUBGOAL_THEN `LENGTH(blk:byte list) < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY ZSTD2_STEP_TAC [1;2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`LENGTH(blk:byte list)`; `9`]
    EN_SUB_FLAG) (CONJ (ASSUME `LENGTH(blk:byte list) < 2 EXP 64`)
                       (ARITH_RULE `9 < 2 EXP 64`))]);;

let EN2_NOWRAP_TAC : tactic =
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
  ZSTD2_SIM_UNTIL_TAC [0x3318] THEN FA_STATE_REWRITE_TAC[ADD_SUB] THEN
  SUBGOAL_THEN `l4 < 2 EXP 64 /\ LENGTH(blk:byte list) < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`l4 <= LENGTH(blk:byte list)`;
      `val(src:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ZSTD2_SIM_UNTIL_TAC [0x34f8] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let EN2_WRAP_TAC : tactic =
  ZSTD2_SIM_UNTIL_TAC [0x3318] THEN
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
  ZSTD2_SIM_UNTIL_TAC [0x333c] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(6 + j0 + j1 + j2 <= LENGTH(blk:byte list))` THEN ARITH_TAC;;

let EN2_CORRECT = prove
 (en2_goal,
  REWRITE_TAC[GSYM puff_memsafe] THEN ZSTD_INTRO_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `5 < n` THENL
   [ALL_TAC;
    ZSTD2_SIM_UNTIL_TAC [0x333c] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]]
  THEN EN2_CCMP_TAC THEN
  ASM_CASES_TAC `9 < LENGTH(blk:byte list)` THENL
   [ALL_TAC;
    ZSTD2_SIM_UNTIL_TAC [0x333c] THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[]]
  THEN EN_JUMP_TAC THEN ZSTD2_SIM_UNTIL_TAC [0x3310] THEN EN_OPS_TAC THEN
  ASM_CASES_TAC `6 + j0 + j1 + j2 <= LENGTH(blk:byte list)` THENL
   [EN2_NOWRAP_TAC; EN2_WRAP_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The back of the slow path from the setup (BK2_CORRECT) and the slow path  *)
(* as a whole for a valid block (SP2_CORRECT).                               *)
(* ------------------------------------------------------------------------- *)

(*** The main loop from its first iteration (all jj_k = 0, all flags 0), ***)
(*** with the disjunctions of its exit folded into definitions (as for   ***)
(*** the 4X1 proof, ml_ofsok and ml_flagok) and without the code in its ***)
(*** exit, for big steps                                                 ***)

let ml2_bc0 k = mk_var("bc0"^string_of_int k,`:num`);;

let ml2_loopw_pre =
  let sub = List.concat (map (fun k ->
              [`0`,ml2_var k ("jj",`:num`);
               ml2_o0 k,ml2_var k ("ofs",`:num`);
               ml2_bc0 k,ml2_var k ("bc",`:num`)]) [1;2;3;4]) @
            [`0`,`f:num`] in
  with_memsafe ml2_lrr ml2_lwr
   (mk_abs(`s:armstate`,vsubst sub ml2_inv_body));;

(*** Substitution in the body of an assertion \s. ?x1 ... xn. P (subst ***)
(*** does not replace terms with bound variables), before the memory   ***)
(*** safety conjunct is added (which flattens the conjunctions)        ***)

let rec ml2_subst_body pairs tm =
  if is_abs tm then let v,b = dest_abs tm in mk_abs(v,ml2_subst_body pairs b)
  else if is_exists tm then
    let v,b = dest_exists tm in mk_exists(v,ml2_subst_body pairs b)
  else subst pairs tm;;

(*** The exit without the code (a big step takes the code of its post for ***)
(*** that before the step)                                                ***)

let ml2_nocode_pair =
 (`read SP s = word_sub stackpointer (word 496)`,
  `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
   read SP s = word_sub stackpointer (word 496)`);;

let ml2_lexitF =
  let fold k =
    let ofs = ml2_var k ("ofs",`:num`) and st = ml2_var k ("st",`:byte list`)
    and f = mk_var("f"^string_of_int k,`:num`) in
    let lst = mk_comb(`LENGTH:byte list->num`,st) in
    [mk_disj(mk_eq(ofs,`0`),mk_binop `(<=):num->num->bool`
                              (mk_binop `(+):num->num->num` ofs `8`) lst),
     list_mk_icomb "ml_ofsok" [ofs; st];
     mk_conj(mk_disj(mk_eq(f,`0`),mk_eq(f,`1`)),
             mk_imp(mk_eq(f,`0`),mk_eq(ofs,ml2_o0 k))),
     list_mk_icomb "ml_flagok" [f; ofs; ml2_o0 k]] in
  let pairs = List.concat(map (fun k -> let [(a,b); (c,d)] = fold k in
                                        [(b,a); (d,c)]) [1;2;3;4]) @
              [ml2_nocode_pair] in
  with_memsafe ml2_lrr ml2_lwr (ml2_subst_body pairs ml2_lexit_raw);;

let ml2_loopwf_goal =
  let tm = mk_imp(list_mk_conj ml2_loop_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; ml2_loopw_pre; ml2_lexitF; ml2_loop_frame]) in
  let vs = ml2_loop_vars @ map ml2_bc0 [1;2;3;4] in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("ml2_loopwf_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let ML2_LOOPWF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL ML2_LOOP)) THEN
  MATCH_MP_TAC RS_ENSURES_WEAKEN THEN CONJ_TAC THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `L4:num` THEN
    MAP_EVERY EXISTS_TAC
     (List.concat(map (fun k -> [`0`; ml2_o0 k; ml2_bc0 k]) [1;2;3;4])) THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[SUB_0];
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
    THEN MAP_EVERY EXISTS_TAC
      (List.concat(map ml2_pervars [1;2;3;4]) @
       [`f1:num`; `f2:num`; `f3:num`; `f4:num`]) THEN
    ASM_REWRITE_TAC[ml_ofsok; ml_flagok]];;

let ML2_LOOPWF = prove(ml2_loopwf_goal, ML2_LOOPWF_TAC);;

(*** The back of the slow path, from the setup of the main loop (0x3614) ***)
(*** to 0x333c: the setup, then the loop and its exits or the skip, then ***)
(*** the rest; the outputs at dst + k * q, segments q, q, q and n - 3 *  ***)
(*** q, and stream k starting at r_k = 8 * ofs0_k + 64 - bc0_k, each one ***)
(*** decoding its segment to position 0                                  ***)

let bk2_r k =
  subst [ml2_o0 k,`x:num`; ml2_bc0 k,`b:num`] `8 * x + 64 - b`;;

let bk2_sv k = ml2_var k ("src",`:int64`)
and bk2_st k = ml2_var k ("st",`:byte list`);;

let bk2_inst =
  List.concat (map (fun k ->
    [bk_op k,ml2_var k ("op",`:int64`); bk_L k,ml2_var k ("L",`:num`);
     bk2_r k,ml2_var k ("r",`:num`)]) [1;2;3;4]) @
  [`word_add dt (word 4):int64`,`tbl:int64`];;

let bk2_win k =
  vsubst [bk2_st k,`st:byte list`; ml2_o0 k,`ofs:num`] t2_win;;

let bk2_pre = mk_abs(`s:armstate`,list_mk_conj
 ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
    read PC s = word(pc + 0x3614) /\
    read SP s = word_sub stackpointer (word 496) /\
    read X14 s = word_add dst (word n) /\
    read X11 s = word_add dst (word (3 * q)) /\
    read X12 s = word_add dst (word q) /\
    read X13 s = word_add dst (word (2 * q)) /\
    read X19 s = dst /\ read X20 s = word n /\ read X23 s = dt /\
    read X8 s = word_zx (dh:int32) /\ read X1 s = word 0 /\
    read X3 s = word bc01 /\ read X22 s = word bc02 /\
    read X21 s = word bc03 /\
    read X18 s = src1 /\ read X15 s = src2 /\ read X9 s = src3 /\
    read X24 s = src4 /\ read X25 s = v25 /\ read X26 s = v26 /\
    read X28 s = word_add src1 (word 8)`] @
  List.concat (map (fun k ->
    let a = 224 + 40 * (k - 1) in
    [ml_mem64 a (bk2_win k); ml_mem32 (a + 8) (ml2_bc0 k);
     ml_mem64 (a + 16) (mk_comb(mk_comb(`word_add:int64->int64->int64`,
                                        bk2_sv k),
                                mk_comb(`word:num->int64`,ml2_o0 k)))])
   [1;2;3;4]) @
  [ml_mem64 96 `word_add src2 (word 8):int64`;
   ml_mem64 104 `word_add src3 (word 8):int64`;
   ml_mem64 112 `word_add src4 (word 8):int64`;
   ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`] @
  map (fun k -> vsubst [bk2_sv k,`src:int64`; bk2_st k,`st:byte list`]
     `read (memory :> bytes(src,LENGTH(st:byte list))) s =
      num_of_bytelist st`) [1;2;3;4] @
  [`read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
    num_of_bytelist(huf_dtable2 ws ml tl)`;
   `read events s = e`]));;

let bk2_post = vsubst bk2_inst rs2_post;;

let bk2_frame =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
             X13; X14; X15; X16; X17; X18; X19; X20; X21; X22; X23; X24;
             X25; X26; X27; X28; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(dst,q); memory :> bytes(word_add dst (word q),q);
             memory :> bytes(word_add dst (word (2 * q)),q);
             memory :> bytes(word_add dst (word (3 * q)),n - 3 * q);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),320)]`;;

let bk2_hyps =
  let stk = `word_sub stackpointer (word 496):int64,496`
  and code = `word pc:int64,32000`
  and tbl = `word_add dt (word 4):int64,4 * 2 EXP tl`
  and out = `(dst:int64),(n:num)` in
  let ins k = mk_pair(bk2_sv k,mk_comb(`LENGTH:byte list->num`,bk2_st k)) in
  let nonov a b = list_mk_icomb "nonoverlapping" [a; b] in
  [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ 1 <= tl /\ tl <= 12`;
   `val(word_subword (dh:int32) (16,8):byte) = tl`;
   `(n + 3) DIV 4 = q /\ 5 < n /\ n < 2 EXP 28 /\
    val(dst:int64) + n < 2 EXP 64 /\ ~(val dst = 0)`] @
  map (fun k ->
    vsubst [bk2_sv k,`src:int64`; bk2_st k,`st:byte list`;
            ml2_o0 k,`ofs0:num`; ml2_bc0 k,`bc0:num`;
            bk2_r k,`r:num`; bk_L k,`L:num`]
     `8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64 /\
      bc0 <= 64 /\ (ofs0 = 0 \/ bc0 <= 8) /\
      (ofs0 = 0 \/ ofs0 + 8 <= LENGTH st) /\
      SND(SND(huf_decode ws ml st r L)) /\
      FST(SND(huf_decode ws ml st r L)) = 0`) [1;2;3;4] @
  [nonov out tbl; nonov out code; nonov out stk] @
  map (fun k -> nonov out (ins k)) [1;2;3;4] @
  map (fun k -> nonov stk (ins k)) [1;2;3;4] @
  [nonov stk tbl; nonov stk code] @
  map (fun k -> nonov (ins k) code) [1;2;3;4];;

let bk2_vars =
  [`pc:num`; `stackpointer:int64`; `dst:int64`; `n:num`; `q:num`;
   `dt:int64`; `dh:int32`; `tl:num`; `ws:num list`; `ml:num`;
   `v25:int64`; `v26:int64`; `v27:int64`; `v28:int64`;
   `e:uarch_event list`] @
  List.concat (map (fun k ->
    [bk2_st k; bk2_sv k; ml2_o0 k; ml2_bc0 k]) [1;2;3;4]);;

let bk2_goal =
  let tm = mk_imp(list_mk_conj bk2_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; bk2_pre; bk2_post; bk2_frame]) in
  let fvs = frees tm in
  (match subtract fvs bk2_vars with
     [] -> ()
   | v::_ -> failwith ("bk2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) bk2_vars,tm);;

(*** Big steps as BK_BIGSTEP_TAC with the code of 4X2 ***)

let BK2_BIGSTEP_TAC th alist : tactic =
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
    ARM_BIGSTEP_TAC SLOW2_EXEC ("s"^string_of_int(n + 1)) THEN
    W(fun (_,w) ->
      if is_comb w && (try fst(dest_const(fst(strip_comb w))) = "eventually"
                       with Failure _ -> false)
      then EVENTS_UNABBREV_TAC THEN MEMSAFE_STRIP_TAC
      else REPEAT CONJ_TAC THEN
           FIRST [ML_PRE_MEMSAFE_TAC; ML_FACT_TAC; T4_CONJ_TAC;
                  BK_PRE_TAC]));;

(*** Facts about the outputs (as BK_FACTS_TAC), the outputs not at 0 ***)

let BK2_FACTS_TAC : tactic =
  BK_FACTS_TAC THEN
  SUBGOAL_THEN `2 <= q` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(n + 3) DIV 4 = q`; `5 < n`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(val(word_add dst (word q):int64) = 0) /\
    ~(val(word_add dst (word (2 * q)):int64) = 0) /\
    ~(val(word_add dst (word (3 * q)):int64) = 0)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= q` THEN ARITH_TAC;
    ALL_TAC];;

(*** The end less 7 of the outputs for the loop (8 bytes of stream 4) ***)

let BK2_LIMIT_TAC : tactic =
  SUBGOAL_THEN `7 <= n /\ 3 * q + 7 <= n /\ 8 <= q` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`8 <= n - 3 * q`; `n - 3 * q <= q`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add dst (word (3 * q))) (word (n - 3 * q - 7)) =
    word_add dst (word (n - 7)):int64 /\
    word_sub (word_add dst (word n)) (word 7) =
    word_add dst (word (n - 7)):int64`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `3 * q + 7 <= n` THEN ARITH_TAC;
      MATCH_MP_TAC ST2_SUB7 THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC];;

let bk2_st_alist =
  [("b1",ml2_bc0 1); ("b2",ml2_bc0 2); ("b3",ml2_bc0 3); ("b4",ml2_bc0 4);
   ("x25",`v25:int64`); ("x26",`v26:int64`)] @
  List.concat (map (fun k ->
    let ks = string_of_int k in
    [("s"^ks,bk2_sv k); ("c"^ks,bk2_win k);
     ("p"^ks,mk_comb(mk_comb(`word_add:int64->int64->int64`,bk2_sv k),
                     mk_comb(`word:num->int64`,ml2_o0 k)))]) [1;2;3;4]);;

let bk2_alist =
  [("tbl",`word_add dt (word 4):int64`)] @
  List.concat (map (fun k ->
    let ks = string_of_int k in
    [("op"^ks,bk_op k); ("L"^ks,bk_L k); ("r"^ks,bk2_r k)]) [1;2;3;4]);;

let bk2_skip_alist =
  List.concat (map (fun k ->
    let ks = string_of_int k in
    [("jj"^ks,`0`); ("ofs"^ks,ml2_o0 k); ("bc"^ks,ml2_bc0 k)]) [1;2;3;4]);;

(*** The stream states at the exit of the loop, from their positions ***)

let bk2_state_alist asl =
  List.concat (map (fun k ->
    let st = bk2_st k in
    let pospat = subst [st,`st:byte list`]
      `FST(SND(huf_decode ws ml (st:byte list) r j)) = 8 * ofs + 64 - x` in
    let (j,ov,x) = tryfind (fun (_,th) ->
      let _,tmi,_ = term_match [st; `ws:num list`; `ml:num`] pospat
                      (concl th) in
      let inst v = try rev_assoc v tmi with Failure _ -> v in
      (inst `j:num`,inst `ofs:num`,inst `x:num`)) asl in
    let ks = string_of_int k in
    [("jj"^ks,j); ("ofs"^ks,ov); ("bc"^ks,x)]) [1;2;3;4]);;

(*** At the exit of the loop: the bits used and the flags as 32-bit ***)
(*** values for the exits                                          ***)

let BK2_EXIT_FACTS_TAC : tactic =
  MAP_EVERY (fun k ->
    let f = mk_var("f"^string_of_int k,`:num`)
    and bc = ml2_var k ("bc",`:num`) in
    let lt x = mk_binop `(<):num->num->bool` x `2 EXP 32` in
    SUBGOAL_THEN (lt bc) ASSUME_TAC THENL [ML2_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      match strip_comb(concl th) with
        Const("ml_flagok",_),[f';_;_] when f' = f ->
          let d = CONJUNCT1(REWRITE_RULE[ml_flagok] th) in
          ASSUME_TAC(MP (ARITH_RULE(mk_imp(concl d,lt f))) d)
      | _ -> NO_TAC)) [1;2;3;4];;

let BK2_LOOP_TAC : tactic =
  BK2_LIMIT_TAC THEN
  BK2_BIGSTEP_TAC ML2_LOOPWF bk2_alist THEN RS_2EXP64_TAC THEN
  BK2_EXIT_FACTS_TAC THEN
  W(fun gl -> if bk_at 0x47d4 gl
              then BK2_BIGSTEP_TAC EX2_A (bk_auto_alist EX2_A gl)
              else BK2_BIGSTEP_TAC EX2_B (bk_auto_alist EX2_B gl)) THEN
  RS_2EXP64_TAC THEN
  W(fun (asl,w) ->
    BK_GOON_TAC RS2_CORRECT (bk2_alist @ bk2_state_alist asl));;

let BK2_SKIP_TAC : tactic =
  RS_2EXP64_TAC THEN BK_GOON_TAC RS2_CORRECT (bk2_alist @ bk2_skip_alist);;

let BK2_TAC : tactic =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN BK2_FACTS_TAC THEN
  BK2_BIGSTEP_TAC ST2_CORRECT bk2_st_alist THEN
  W(fun gl -> if bk_at 0x3750 gl then BK2_LOOP_TAC else BK2_SKIP_TAC);;

let BK2_CORRECT = prove(bk2_goal, BK2_TAC);;

(*** The slow path as a whole for a valid block (0x32d0 to 0x333c): the ***)
(*** result n and the bytes out, with x25-x28 restored; as SP of the    ***)
(*** 4X1 proof, the errors excluded by the validity                     ***)

let sp2_rr =
 `[src,LENGTH(blk:byte list); dt,4; word_add dt (word 4),4 * 2 EXP tl;
   word_sub stackpointer (word 496),496]:(int64#num)list`
and sp2_wr =
 `[dst,n; word_sub stackpointer (word 496),496]:(int64#num)list`;;

let sp2_pre = mk_abs(`s:armstate`,
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read PC s = word(pc + 0x32d0) /\
  read SP s = word_sub stackpointer (word 496) /\
  read X19 s = dst /\ read X20 s = word n /\ read X22 s = src /\
  read X18 s = word(LENGTH(blk:byte list)) /\ read X23 s = dt /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28 /\
  read (memory :> bytes(src,LENGTH blk)) s = num_of_bytelist blk /\
  read (memory :> bytes32 dt) s = dh /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable2 ws ml tl) /\
  read events s = e`);;

let sp2_post = with_memsafe sp2_rr sp2_wr (mk_abs(`s:armstate`,
 `read PC s = word(pc + 0x333c) /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28 /\
  read X0 s = word n /\
  read (memory :> bytes(dst,n)) s = num_of_bytelist out`));;

let sp2_frame =
 `MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
             X13; X14; X15; X16; X17; X18; X19; X20; X21; X22; X23; X24;
             X25; X26; X27; X28; X30] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes(dst,n);
             memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),432)]`;;

let sp2_hyps =
  let stk = `word_sub stackpointer (word 496):int64,496`
  and code = `word pc:int64,32000`
  and tbl = `word_add dt (word 4):int64,4 * 2 EXP tl`
  and out = `(dst:int64),(n:num)`
  and ins = `(src:int64),LENGTH(blk:byte list)` in
  let nonov a b = list_mk_icomb "nonoverlapping" [a; b] in
  [`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `aligned 16 (stackpointer:int64)`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ 1 <= tl /\ tl <= 12`;
   `val(word_subword (dh:int32) (16,8):byte) = tl`;
   `n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64 /\ ~(val dst = 0)`;
   `8 <= val(src:int64) /\ val src + LENGTH(blk:byte list) + 8 < 2 EXP 64 /\
    LENGTH blk < 2 EXP 32`;
   `LENGTH(out:byte list) = n /\ huf_streams4 T ws ml blk out`;
   nonov out tbl; nonov out code; nonov out stk; nonov out ins;
   nonov stk ins; nonov stk tbl; nonov stk code; nonov ins code;
   nonov tbl code];;

let sp2_vars =
  [`pc:num`; `stackpointer:int64`; `dst:int64`; `n:num`; `src:int64`;
   `blk:byte list`; `dt:int64`; `dh:int32`; `tl:num`; `ws:num list`;
   `ml:num`; `v25:int64`; `v26:int64`; `v27:int64`; `v28:int64`;
   `out:byte list`; `e:uarch_event list`];;

let sp2_goal =
  let tm = mk_imp(list_mk_conj sp2_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; sp2_pre; sp2_post; sp2_frame]) in
  let fvs = frees tm in
  (match subtract fvs sp2_vars with
     [] -> ()
   | v::_ -> failwith ("sp2_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) sp2_vars,tm);;

(*** The conditions of a valid block (HUF_STREAMS4_NECESSARY) ***)

let SP2_NECESSARY_TAC : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP HUF_STREAMS4_NECESSARY o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "huf_streams4"
    with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

(*** An error branch, impossible for a valid block: its condition false ***)
(*** by the facts                                                       ***)

let SP2_FAIL_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if (is_disj t || is_neg t) &&
       not(can (find_term (fun u -> u = `read:(armstate,int64)component->
                                           armstate->int64`)) t)
    then MP_TAC th THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN NO_TAC
    else NO_TAC);;

let SP2_GUARD tac : tactic =
  W(fun gl -> if bk_at 0x333c gl then SP2_FAIL_TAC else tac);;

let SP2_IN_TAC k : tactic =
  let th = el (k - 1) [IN2_1_CORRECT; IN2_2_CORRECT; IN2_3_CORRECT;
                       IN2_4_CORRECT] in
  W(fun gl -> BK2_BIGSTEP_TAC th (sp_in_alist k @ bk_auto_alist th gl));;

(*** The validity of each stream from the start of its decoding ***)

let SP2_OK_TAC : tactic =
  FIRST_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "huf_streams4"
    with Failure _ -> false)) THEN
  REWRITE_TAC[huf_streams4] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let hs = filter (fun (_,th) ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "huf_stream"
      with Failure _ -> false) asl in
    MAP_EVERY (fun (_,th) ->
      let [_; _; st; ov] = snd(strip_comb(concl th)) in
      let eth = snd(find (fun (_,e) -> let t = concl e in
        (try fst(dest_const(fst(strip_comb t))) = "zstd_end" &&
             el 0 (snd(strip_comb t)) = st with Failure _ -> false)) asl) in
      let r = el 1 (snd(strip_comb(concl eth))) in
      MP_TAC(SPECL [`ws:num list`; `ml:num`; st; r; ov] HUF_STREAM_DECODE) THEN
      ASM_REWRITE_TAC[LENGTH_ZSTD_SUBLIST; TRIPLE_EQ] THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) hs);;

(*** The bytes out from the four segments ***)

let sp2_result_th (asl,w) =
  let mem k = subst [bk_op k,`a:int64`; bk_L k,`k:num`]
               `read (memory :> bytes(a,k)) (s':armstate)` in
  let r k = subst [sp_ofs0 k,`x:num`; sp_bc0 k,`b:num`] `8 * x + 64 - b` in
  ISPECL
   ([`ws:num list`; `ml:num`; `blk:byte list`; `n:num`; `q:num`;
     `word n:int64`] @
    map mem [1;2;3;4] @
    map (fun k -> mk_var("st"^string_of_int k,`:byte list`)) [1;2;3;4] @
    map r [1;2;3;4])
   HUF_STREAMS4_RESULT;;

let SP2_FINAL_TAC : tactic =
  X_GEN_TAC `s':armstate` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MEMSAFE_STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; SP_MEMSAFE_TAC] THEN
  REWRITE_TAC[MATCH_MP SP_BYTES4 (ASSUME `3 * q <= n`)] THEN
  W(fun gl -> MP_TAC(sp2_result_th gl)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `out:byte list` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]];;

let SP2_BACK_TAC : tactic =
  SP_INIT_FACTS_TAC THEN SP2_OK_TAC THEN
  SP_GOON_TAC [`3 * q <= n`; `val(dst:int64) + n < 2 EXP 64`;
               `n < 2 EXP 28`] SP2_FINAL_TAC BK2_CORRECT sp_bk_alist;;

let SP2_TAC : tactic =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN SP2_NECESSARY_TAC THEN
  BK2_BIGSTEP_TAC EN2_CORRECT [] THEN
  SP2_GUARD
   (SP_ABBREV_TAC THEN SP_FACTS_TAC THEN SP2_IN_TAC 1 THEN
    SP2_GUARD
     (SP2_IN_TAC 2 THEN
      SP2_GUARD
       (SP2_IN_TAC 3 THEN
        SP2_GUARD
         (SP2_IN_TAC 4 THEN SP2_GUARD SP2_BACK_TAC))));;

let SP2_CORRECT = prove(sp2_goal, SP2_TAC);;

(* ------------------------------------------------------------------------- *)
(* Safety: the slow path for any block. The lookups with the index only      *)
(* bounded by the table, the tails (TAIL2S_k_TAIL), the main loop            *)
(* (ML2S_LOOP), the rest (RS2S_CORRECT), the back (BK2S_CORRECT) and the     *)
(* slow path as a whole (SP2S_CORRECT): the result n or an error, within the *)
(* regions.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*** The slow path for any block (safety): the lookups with any bits, ***)
(*** the index only bounded by the size of the table                ***)

let HUF_INDEX2_ANY = prove
 (`!(y:int64) tl.
        1 <= tl /\ tl <= 12
        ==> word_shl (word_jushr y (word (64 - tl))) 2 =
            word (4 * val(word_jushr y (word (64 - tl)))) /\
            val(word_jushr y (word (64 - tl))) < 2 EXP tl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_jushr y (word (64 - tl)) = word_ushr (y:int64) (64 - tl)`
  SUBST1_TAC THENL
   [REWRITE_TAC[word_jushr; VAL_WORD; DIMINDEX_64] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 64`;
                 ARITH_RULE `1 <= tl /\ tl <= 12 ==> 64 - tl < 2 EXP 64`];
    ALL_TAC] THEN
  REWRITE_TAC[word_shl; VAL_WORD_USHR] THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
  SUBGOAL_THEN `64 - tl + tl = 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]);;

let sf2_index_pat = `word_shl (word_jushr y (word (64 - tl))) 2:int64`;;

(*** One lookup: the index abbreviated, bounded by the table, and the ***)
(*** entry with its bytes (as ML2_INDEX_ONE_TAC, from the table only)  ***)

let SF2_INDEX_ONE_TAC (t:term) : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let _,tmi,_ = term_match [`tl:num`] sf2_index_pat t in
    let y = rev_assoc `y:int64` tmi in
    incr ml2_counter;
    let k = string_of_int !ml2_counter in
    let idx = mk_var("idx"^k,`:num`) and ev = mk_var("e"^k,`:num list`)
    and av = mk_var("a"^k,`:num`) and bv = mk_var("b"^k,`:num`)
    and nb = mk_var("nb"^k,`:num`) and len = mk_var("len"^k,`:num`) in
    let lt a b = mk_binop `(<):num->num->bool` a b
    and le a b = mk_binop `(<=):num->num->bool` a b in
    let th = MP (SPECL [y; `tl:num`] HUF_INDEX2_ANY)
                (CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`)) in
    let eq = CONJUNCT1 th and bth = CONJUNCT2 th in
    let vt = lhand(concl bth) in
    let et =
      list_mk_icomb "huf_dentry2" [`ws:num list`; `ml:num`; `tl:num`; idx] in
    let el n = mk_icomb(mk_icomb(`EL:num->num list->num`,mk_small_numeral n),
                        ev) in
    let ttth = try snd(find (fun (_,th) -> concl th = `2 EXP tl = tt`) asl)
               with Failure _ -> REFL `2 EXP tl` in
    let ttr = REWRITE_RULE[ttth] in
    (RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN
     ASSUME_TAC bth THEN ASSUME_TAC(ttr bth) THEN
     ABBREV_TAC (mk_eq(idx,vt)) THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; idx]
       HUF_DENTRY2_BOUNDS) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     MP_TAC(ttr(SPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; idx; s]
       HUF_DTABLE2_READ16)) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     MP_TAC(ttr(SPECL [`ws:num list`; `ml:num`; `tl:num`; `tbl:int64`; idx; s]
       HUF_DTABLE2_READ)) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[];
       DISCH_THEN(fun rth -> let [r0;_;r2;r3] = CONJUNCTS rth in
         ASSUME_TAC r0 THEN ASSUME_TAC r2 THEN ASSUME_TAC r3)] THEN
     ABBREV_TAC (mk_eq(ev,et)) THEN
     ABBREV_TAC (mk_eq(av,el 0)) THEN ABBREV_TAC (mk_eq(bv,el 1)) THEN
     ABBREV_TAC (mk_eq(nb,el 2)) THEN ABBREV_TAC (mk_eq(len,el 3)) THEN
     FIRST_X_ASSUM(fun bth ->
       if is_conj(concl bth) && free_in len (concl bth) &&
          free_in nb (concl bth)
       then MAP_EVERY ASSUME_TAC (CONJUNCTS bth)
       else NO_TAC) THEN
     SUBGOAL_THEN (list_mk_conj [le `1` len; le len `2`])
       STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC (mk_disj(mk_eq(len,`1`),mk_eq(len,`2`))) THEN ARITH_TAC;
       ALL_TAC] THEN
     SUBGOAL_THEN (list_mk_conj [lt nb `64`; lt len `256`;
                                 lt (mk_binop `(+):num->num->num` av
                                      (mk_binop `( * ):num->num->num`
                                        `256` bv)) `65536`])
       STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC]) gl;;

let SF2_INDEX_TAC : tactic =
  fun (asl,w as gl) ->
    let s = rand w in
    let tms = setify(List.concat(mapfilter (fun (_,th) ->
      let t = concl th in
      if is_eq t && is_comb(lhs t) && rand(lhs t) = s
      then find_terms (fun u -> can (term_match [`tl:num`] sf2_index_pat) u)
                      (rhs t)
      else fail()) asl)) in
    MAP_EVERY SF2_INDEX_ONE_TAC tms gl;;

let SF2_NORM_TAC = SF2_INDEX_TAC THEN HUF_HIDE_SUB_TAC THEN ML2_DROP_TAC;;

(*** Simulation with the lookups of any bits ***)

let SF2_SIM_UNTIL_TAC stops =
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k (asl,w as gl) =
    let pc = current_pc gl in
    if mem pc stops then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "SF2_SIM_UNTIL_TAC"
    else
      let n = let v = fst(dest_var(rand w)) in
              int_of_string(String.sub v 1 (String.length v - 1)) in
      (ML2_STEP_TAC (n + 1) THEN SF2_NORM_TAC THEN run (k - 1)) gl in
  run 400;;

(*** The tails of the four streams for any stream (safety): the same ***)
(*** pieces as for a valid stream, with bounds instead of the states  ***)
(*** of the decoding                                                  ***)

let t2s_hyps =
  let cs = conjuncts t2_hyps in
  let bad t = can (find_term (fun u -> is_const u &&
                    fst(dest_const u) = "huf_decode")) t in
  list_mk_conj(filter (not o bad) cs);;

let mk_tail2s_goal spec extra pre post =
  let pre' = tail2_inst spec pre and post' = tail2_inst spec post in
  let tm = mk_imp(t2s_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; pre'; post'; tail2_frame spec]) in
  let vs = t2_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_tail2s_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** The head of the loop of 4 lookups and its body ***)

let t2s_r4inv spec = with_tail2_memsafe spec
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + a_r4)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_p4:tailreg) s = word_add src (word ofs) /\
     read (r_bc4:tailreg) s = word bc /\
     read (r_e74:tailreg) s = word_add op (word (L - 7)) /\
     read (r_sh4:tailreg) s = word(64 - tl)`;
    mk_eq(`read (r_c4:tailreg) s`,t2_win);
    mk_disj(mk_conj(`read (r_f4:tailreg) s = word 0`,t2c_bd),
            `read (r_f4:tailreg) s = word 1`);
    `7 <= L /\ jj <= L /\ bc <= 64`; t2c_ofsok])));;

let t2s_b4pre spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_conj
   [`read PC s = word(pc + a_b4)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_p4:tailreg) s = word_add src (word ofs) /\
     read (r_bbc4:tailreg) s = word bc /\
     read (r_f4:tailreg) s = word 1 /\
     read (r_e74:tailreg) s = word_add op (word (L - 7)) /\
     read (r_sh4:tailreg) s = word(64 - tl)`;
    mk_eq(`read (r_c4:tailreg) s`,t2_win);
    `bc <= 7 /\ jj + 8 <= L`; t2c_ofsok]));;

let t2s_b4_goal spec = mk_tail2s_goal spec [`jj:num`; `ofs:num`; `bc:num`]
  (t2s_b4pre spec)
  (mk_abs(`s:armstate`,mk_exists(`m':num`,mk_conj(`m' < L - jj`,
     list_mk_comb(t2s_r4inv spec,[`m':num`; `s:armstate`])))));;

let TAIL2S_INIT_TAC =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  (fun gl -> ml2_counter := 0; ALL_TAC gl);;

let TAIL2S_BODY_TAC spec a_head bcreg =
  TAIL2S_INIT_TAC THEN SF2_SIM_UNTIL_TAC [a_head] THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  W(fun (asl,w) ->
    let s = t2_state asl spec.op2 in
    let jv = fl_num_norm(t2_regval asl s spec.op2)
    and bv = t2_regval asl s bcreg in
    EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jv) THEN
    CONJ_TAC THENL
     [ML2_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [jv; `ofs:num`; bv] THEN T2_CONJ_TAC]);;

(*** After the main loop of the tail: the pointer in the frame is that ***)
(*** of the stream unless more than 64 bits were used (then the static ***)
(*** buffer of the code, never read)                                   ***)

let t2s_bd = list_mk_conj
 [subst [t2_spv `s_c:num`,`a:int64`; t2_win,`w:int64`]
   `read (memory :> bytes64 a) s = w`;
  subst [t2_spv `s_b:num`,`a:int64`] `read (memory :> bytes32 a) s = word bc`;
  subst [t2_spv `s_p:num`,`a:int64`]
   `read (memory :> bytes64 a) s = (p:int64)`];;

let t2s_ok =
 `jj <= L /\ bc <= 64 + 12 * jj /\
  (bc <= 64 ==> p = word_add (src:int64) (word ofs) /\
                (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list))) /\
  (64 < bc ==> ofs = 0)`;;

let t2s_mid spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`; `p:int64`],list_mk_conj
   [`read PC s = word(pc + a_mid)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_room:tailreg) s = word(L - jj)`; t2s_bd; t2s_ok])));;

let t2s_r4_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_r4inv spec,[`m:num`; `s:armstate`]))))
  (t2s_mid spec);;

let TAIL2S_TO_BODY_TAC body_th a_body ofs' bc' =
  ML2_SIM_UNTIL_TAC [a_body] THEN FL_EXPAND_POST_TAC THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m':num`
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    DISJ1_TAC THEN EXISTS_TAC `m':num` THEN CONJ_TAC THENL
     [ML2_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC])
   body_th [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

let TAIL2S_TO_MID_TAC a_mid ofs' bc' =
  ML2_SIM_UNTIL_TAC [a_mid] THEN FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`jj:num`; ofs'; bc';
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`src:int64`),
            mk_comb(`word:num->int64`,ofs'))] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

let TAIL2S_LOOP_TAC spec (fl:term) room a_body a_mid body_th =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs <= LENGTH(st:byte list)`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  T2_OPVAL_TAC [`jj:num`; mk_binop `(-):num->num->num` `L:num`
                   (mk_small_numeral(dest_small_numeral room - 1))] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
                     can (find_term ((=) fl)) (concl th))) THEN
  T2_RELOAD_CASES_TAC
   (fun ofs' bc' ->
      ASM_CASES_TAC (mk_binop `(<=):num->num->bool`
                       (mk_binop `(+):num->num->num` `jj:num` room) `L:num`)
      THENL [TAIL2S_TO_BODY_TAC body_th a_body ofs' bc';
             TAIL2S_TO_MID_TAC a_mid ofs' bc'])
   (TAIL2S_TO_MID_TAC a_mid);;

(*** The same for tl <= 11 (5 lookups) ***)

let t2s_r5inv spec = t2_r45_subst(t2s_r4inv spec)
and t2s_b5pre spec = t2_r45_subst(t2s_b4pre spec);;

let t2s_b5_goal spec = mk_tail2s_goal spec [`jj:num`; `ofs:num`; `bc:num`]
  (t2s_b5pre spec)
  (mk_abs(`s:armstate`,mk_exists(`m':num`,mk_conj(`m' < L - jj`,
     list_mk_comb(t2s_r5inv spec,[`m':num`; `s:armstate`])))));;

let t2s_r5_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_r5inv spec,[`m:num`; `s:armstate`]))))
  (t2s_mid spec);;

(*** The loop of one lookup: its head as for a valid stream (bc <= 64), ***)
(*** its exit to after it with the pointer (the static buffer when     ***)
(*** more than 64 bits were used)                                      ***)

let t2s_r1inv spec = with_tail2_memsafe spec
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + a_r1)`; t2c_common_x spec; spec.lim1;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_p1:tailreg) s = word_add src (word ofs) /\
     read (r_bc1:tailreg) s = word bc /\
     read (r_e21:tailreg) s = word_add op (word (L - 2)) /\
     read (r_sh1:tailreg) s = word(64 - tl)`;
    mk_eq(`read (r_c1:tailreg) s`,t2_win);
    mk_disj(mk_conj(t2c_bd,
                    `read (r_pc1:tailreg) s = word_add src (word ofs)`),
            `read (r_f1:tailreg) s = word 1`);
    `2 <= L /\ jj <= L /\ bc <= 64`; t2c_ofsok])));;

let t2s_after1 spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`; `p:int64`],list_mk_conj
   [`read PC s = word(pc + a_after1)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_e21:tailreg) s = word_add op (word (L - 2)) /\
     read (r_pptr:tailreg) s = p`;
    list_mk_conj(butlast(conjuncts t2s_bd)); `2 <= L`; t2s_ok])));;

let t2s_r1_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_r1inv spec,[`m:num`; `s:armstate`]))))
  (t2s_after1 spec);;

let SF2_SIM_SPLIT_UNTIL_TAC stops =
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k (asl,w as gl) =
    let pc = current_pc gl in
    let s = rand w in
    if mem pc stops then ALL_TAC gl
    else if k = 0 then failwith "SF2_SIM_SPLIT_UNTIL_TAC"
    else if is_cond pc then
      let c = lhand(rator pc) in
      let pcl = mk_comb(`read PC`,s) in
      (ASM_CASES_TAC c THEN
       POP_ASSUM(fun cth ->
         ASSUME_TAC cth THEN
         FIRST_X_ASSUM(fun th ->
           if is_eq(concl th) && lhs(concl th) = pcl
           then ASSUME_TAC(REWRITE_RULE[cth] th) else NO_TAC)) THEN
       run (k - 1)) gl
    else
      let n = let v = fst(dest_var s) in
              int_of_string(String.sub v 1 (String.length v - 1)) in
      (ML2_STEP_TAC (n + 1) THEN SF2_NORM_TAC THEN run (k - 1)) gl in
  run 200;;

let t2s_pc_is a (asl,w) =
  let t = mk_comb(`word:num->int64`,
            mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral a)) in
  exists (fun (_,th) -> let u = concl th in
    is_eq u && rhs u = t && is_comb(lhs u) &&
    rator(lhs u) = `read PC`) asl;;

let TAIL2S_L1_LOOK_TAC spec ofs' bc' =
  (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  W(fun (asl,w) ->
    let n = let v = fst(dest_var(rand w)) in
            int_of_string(String.sub v 1 (String.length v - 1)) in
    ML2_STEP_TAC (n + 1) THEN SF2_NORM_TAC) THEN
  SF2_SIM_SPLIT_UNTIL_TAC [spec.a_r1; spec.a_after1] THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  W(fun (asl,w) ->
    let s = t2_state asl spec.op2 in
    let jv = fl_num_norm(t2_regval asl s spec.op2)
    and bv = t2_regval asl s spec.bc1 in
    if t2s_pc_is spec.a_r1 (asl,w) then
      DISJ1_TAC THEN
      EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jv) THEN
      CONJ_TAC THENL
       [ML2_ARITH_TAC;
        MAP_EVERY EXISTS_TAC [jv; ofs'; bv] THEN T2_CONJ_TAC]
    else
      let pv = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
                 is_eq t && lhs t = list_mk_icomb "read" [spec.pptr2; s])
                 asl))) in
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [jv; ofs'; bv; pv] THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC);;

let TAIL2S_TO_AFTER_TAC spec ofs' bc' =
  T2_REG_ABBREV_TAC spec.f1 THEN
  ML2_SIM_SPLIT_UNTIL_TAC [spec.a_after1] THEN FL_EXPAND_POST_TAC THEN
  PUFF_FINAL_TAC THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`jj:num`; ofs'; bc';
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`src:int64`),
            mk_comb(`word:num->int64`,ofs'))] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

let TAIL2S_L1_TAC spec =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs <= LENGTH(st:byte list)`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  T2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) o
    check (fun th -> is_disj(concl th) &&
                     can (find_term ((=) spec.f1)) (concl th))) THEN
  T2_RELOAD_CASES_TAC
   (fun ofs' bc' ->
      ASM_CASES_TAC `jj + 2 <= L` THENL
       [TAIL2S_L1_LOOK_TAC spec ofs' bc';
        TAIL2S_TO_AFTER_TAC spec ofs' bc'])
   (TAIL2S_TO_AFTER_TAC spec);;

(*** The end of the tail: the pointer and the bits used, any ***)

let t2s_post spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_exists([`p:int64`; `b:int32`],list_mk_conj
   [`read PC s = word(pc + a_post)`; t2c_common_x spec;
    `read (r_pptr:tailreg) s = p`;
    subst [t2_spv `s_b:num`,`a:int64`]
     `read (memory :> bytes32 a) s = b`])));;

(*** Before the last symbol: at most one byte left ***)

let t2s_last spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`; `p:int64`],list_mk_conj
   [`read PC s = word(pc + a_last)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_pptr:tailreg) s = p`;
    list_mk_conj(butlast(conjuncts t2s_bd));
    `jj <= L /\ L <= jj + 1 /\ bc <= 64 + 12 * jj`])));;

let t2s_last_goal spec = mk_tail2s_goal spec [] (t2s_last spec)
  (t2s_post spec);;

(*** The post from the state: the pointer and the bits used where they ***)
(*** are                                                               ***)

let T2S_POST_TAC spec : tactic =
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  W(fun (asl,w) ->
    let s = t2_state asl spec.op2 in
    let rv c = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
                 is_eq t && lhs t = c) asl))) in
    let pv = rv (list_mk_icomb "read" [spec.pptr2; s])
    and bv = rv (list_mk_icomb "read"
                  [subst [t2_spk(spec.sofs2 + 8),`a:int64`]
                     `memory :> bytes32 a`; s]) in
    MAP_EVERY EXISTS_TAC [pv; bv] THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; T2_CONJ_TAC]);;

let TAIL2S_LAST_TAC spec =
  ZSTD_INTRO_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN ENSURES_EXISTS_PRE_TAC `p:int64` THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  T2_OPVAL_TAC [`jj:num`; `L:num`] THEN
  ASM_CASES_TAC `jj:num = L` THENL
   [ML2_SIM_UNTIL_TAC [spec.a_post] THEN T2S_POST_TAC spec;
    (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
    ABBREV_TAC `tt = 2 EXP tl` THEN
    SF2_SIM_UNTIL_TAC [spec.a_last + 0x20] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP T2_JUSHR_NEG
      (CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`))]) THEN SF2_NORM_TAC THEN
    SF2_SIM_SPLIT_UNTIL_TAC [spec.a_post] THEN T2S_POST_TAC spec];;

(*** The loop without reloads ***)

let t2s_l0inv spec = with_tail2_memsafe spec
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`; `p:int64`],list_mk_conj
   [`m = L - jj`;
    `read PC s = word(pc + a_l0)`; t2c_common_x spec;
    `read (r_op:tailreg) s = word_add op (word jj) /\
     read (r_e21:tailreg) s = word_add op (word (L - 2)) /\
     read (r_bc0:tailreg) s = word bc /\
     read (r_sh0:tailreg) s = word(64 - tl) /\
     read (r_pptr:tailreg) s = p`;
    mk_eq(`read (r_c0:tailreg) s`,t2_win);
    hd(conjuncts t2s_bd);
    `2 <= L /\ jj + 2 <= L /\ bc <= 64 + 12 * jj`])));;

let t2s_l0_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_l0inv spec,[`m:num`; `s:armstate`]))))
  (t2s_last spec);;

let TAIL2S_L0_TAC spec =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN ENSURES_EXISTS_PRE_TAC `p:int64` THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  T2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  SF2_SIM_UNTIL_TAC [spec.a_l0 + 0x28] THEN
  W(fun (asl,w) ->
    let s = t2_state asl spec.op2 in
    let jv = fl_num_norm(t2_regval asl s spec.op2) in
    let room = mk_binop `(<=):num->num->bool`
                 (mk_binop `(+):num->num->num` jv `2`) `L:num` in
    T2_OPVAL_TAC [jv] THEN ASM_CASES_TAC room) THEN
  W(fun (asl,w) ->
    let n = let v = fst(dest_var(rand w)) in
            int_of_string(String.sub v 1 (String.length v - 1)) in
    ML2_STEP_TAC (n + 1) THEN SF2_NORM_TAC) THEN
  SF2_SIM_UNTIL_TAC [spec.a_l0; spec.a_last] THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THENL
   [DISJ1_TAC THEN
    W(fun (asl,w) ->
      let s = t2_state asl spec.op2 in
      let jv = fl_num_norm(t2_regval asl s spec.op2)
      and bv = t2_regval asl s spec.bc0 in
      EXISTS_TAC (mk_binop `(-):num->num->num` `L:num` jv) THEN
      CONJ_TAC THENL
       [ML2_ARITH_TAC;
        MAP_EVERY EXISTS_TAC [jv; `ofs:num`; bv; `p:int64`] THEN
        ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC]);
    DISJ2_TAC THEN
    W(fun (asl,w) ->
      let s = t2_state asl spec.op2 in
      let jv = fl_num_norm(t2_regval asl s spec.op2)
      and bv = rand(rhs(concl(snd(find (fun (_,th) -> let t = concl th in
                 is_eq t && can (term_match [] (subst [s,`s:armstate`;
                   t2_spv(mk_small_numeral(spec.sofs2 + 8)),`a:int64`]
                   `read (memory :> bytes32 a) s = word b`)) t) asl)))) in
      MAP_EVERY EXISTS_TAC [jv; `ofs:num`; bv; `p:int64`] THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC)];;

(*** The pieces to the end of the tail ***)

let t2s_l0post_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_l0inv spec,[`m:num`; `s:armstate`]))))
  (t2s_post spec);;

let t2s_after1_goal spec = mk_tail2s_goal spec [] (t2s_after1 spec)
  (t2s_post spec);;

let t2s_r1post_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_r1inv spec,[`m:num`; `s:armstate`]))))
  (t2s_post spec);;

let t2s_mid_goal spec = mk_tail2s_goal spec [] (t2s_mid spec)
  (t2s_post spec);;

let t2s_r4post_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_r4inv spec,[`m:num`; `s:armstate`]))))
  (t2s_post spec);;

let t2s_r5post_goal spec = mk_tail2s_goal spec []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(t2s_r5inv spec,[`m:num`; `s:armstate`]))))
  (t2s_post spec);;

let T2S_TRANS_TAC spec mid th1 th2 =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (tail2_inst spec mid) THEN REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC th1 THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC th2 THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];;

(*** Going on with a piece th to the end, from the witnesses ws of its ***)
(*** precondition (mm the measure of a loop, if any)                   ***)

let T2S_GOON_TAC th (mm:term option) (ws:term list) : tactic =
  FL_EXPAND_POST_TAC THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN DISCH_THEN ACCEPT_TAC) th [] THEN
  MEMSAFE_ELIM_TAC THEN
  (match mm with Some m -> EXISTS_TAC m | None -> ALL_TAC) THEN
  MAP_EVERY EXISTS_TAC ws THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
    if is_disj w && can (find_term ((=) `word 1:int64`)) (rand w)
    then DISJ1_TAC else NO_TAC)) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN T2_CONJ_TAC;;

let t2s_regv (asl:(string*thm)list) (c:term) =
  let s = rand(lhs(concl(snd(find (fun (_,th) -> let t = concl th in
    is_eq t && is_comb(lhs t) && rator(lhs t) = mk_icomb(`read:
      ((armstate,int64)component)->armstate->int64`,`PC`)) asl)))) in
  rhs(concl(snd(find (fun (_,th) -> let t = concl th in
    is_eq t && lhs t = list_mk_icomb "read" [c; s]) asl)));;

let TAIL2S_AFTER1_TAC spec l0post_th last_th =
  ZSTD_INTRO_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN ENSURES_EXISTS_PRE_TAC `p:int64` THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  T2_OPVAL_TAC [`jj:num`; `L - 2`] THEN
  ASM_CASES_TAC `jj + 2 <= L` THENL
   [ML2_SIM_UNTIL_TAC [spec.a_l0] THEN T4_SHIFT_TAC THEN
    T2S_GOON_TAC l0post_th (Some `L - jj`)
      [`jj:num`; `ofs:num`; `bc:num`; `p:int64`];
    ML2_SIM_UNTIL_TAC [spec.a_last] THEN
    T2S_GOON_TAC last_th None [`jj:num`; `ofs:num`; `bc:num`; `p:int64`]];;

let TAIL2S_MID_TAC spec r1post_th after1_th last_th =
  ZSTD_INTRO_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN ENSURES_EXISTS_PRE_TAC `p:int64` THEN
  PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  ASM_CASES_TAC `jj + 2 <= L` THENL
   [ASM_CASES_TAC `bc <= 64` THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `bc <= 64`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      ML2_SIM_UNTIL_TAC [spec.a_r1] THEN T4_SHIFT_TAC THEN
      T2S_GOON_TAC r1post_th (Some `L - jj`)
        [`jj:num`; `ofs:num`; `bc:num`];
      ML2_SIM_UNTIL_TAC [spec.a_after1] THEN
      W(fun (asl,w) ->
        T2S_GOON_TAC after1_th None
         [`jj:num`; `ofs:num`; `bc:num`; t2s_regv asl spec.pptr2])];
    ML2_SIM_UNTIL_TAC [spec.a_last] THEN
    W(fun (asl,w) ->
      T2S_GOON_TAC last_th None
       [`jj:num`; `ofs:num`; `bc:num`; t2s_regv asl spec.pptr2])];;

(*** The entry of the tail, with any bits used (more than 64 only at the ***)
(*** start of the stream), to the end of the tail                        ***)

let t2s_entry spec = with_tail2_memsafe spec (mk_abs(`s:armstate`,
  list_mk_conj
   ([`read PC s = word(pc + a_entry)`; t2c_common spec] @ spec.eregs2 @
    [`read (r_op:tailreg) s = word_add op (word jj)`; t2c_bd;
     `jj <= L /\ ~(val(op:int64) = 0) /\ bc <= 64 + 12 * jj /\
      (64 < bc ==> ofs = 0)`; t2c_ofsok])));;

let t2s_tail_goal spec = mk_tail2s_goal spec [`jj:num`; `ofs:num`; `bc:num`]
  (t2s_entry spec) (t2s_post spec);;

let T2S_MEMV (asl:(string*thm)list) spec k =
  t2s_regv asl (subst [t2_spk(spec.sofs2 + k),`a:int64`]
                  `memory :> bytes64 a`);;

let TAIL2S_SHORT_TAC spec mid_th =
  let tomid ofs' bc' =
    ML2_SIM_UNTIL_TAC [spec.a_mid] THEN
    T2S_GOON_TAC mid_th None
     [`jj:num`; ofs'; bc';
      mk_comb(mk_comb(`word_add:int64->int64->int64`,`src:int64`),
              mk_comb(`word:num->int64`,ofs'))] in
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN
     `ofs + 8 <= LENGTH(st:byte list) /\ bc DIV 8 <= ofs /\
      (ofs - bc DIV 8) + 8 <= LENGTH(st:byte list)`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC] THEN
    ML2_SIM_UNTIL_TAC [0x1c20] THEN TAIL2_CALL_TAC spec THEN
    tomid `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL [tomid `ofs:num` `bc:num`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN MP_TAC(ASSUME `~(ofs = 0)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [TAIL2_SLICE_TAC `ofs - bc DIV 8` THEN
    tomid `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    TAIL2_SLICE_TAC `0` THEN tomid `0` `bc - 8 * ofs`];;

let TAIL2S_ENTRY_L8_TAC spec mid_th =
  let mid8 = INST [`8`,`L:num`] (SPEC_ALL mid_th) in
  let tomid ofs' bc' =
    ML2_SIM_UNTIL_TAC [spec.a_mid] THEN
    T2S_GOON_TAC mid8 None
     [`0`; ofs'; bc';
      mk_comb(mk_comb(`word_add:int64->int64->int64`,`src:int64`),
              mk_comb(`word:num->int64`,ofs'))] in
  SUBGOAL_THEN `L = 8 /\ jj = 0` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ML2_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP T2_VAL_PRED (ASSUME `~(val(op:int64) = 0)`)) THEN
  DISCH_TAC THEN ML2_SIM_UNTIL_TAC [spec.a_r5] THEN
  T2_RELOAD_CASES_TAC tomid tomid;;

let TAIL2S_ENTRY_TAC spec r4post_th r5post_th mid_th after1_th last_th =
  let overflow_mid =
    ASM_CASES_TAC `tl <= 11` THEN ML2_SIM_UNTIL_TAC [spec.a_mid] THEN
    W(fun (asl,w) ->
      T2S_GOON_TAC mid_th None
       [`jj:num`; `ofs:num`; `bc:num`; T2S_MEMV asl spec 16]) in
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [MP_TAC(ASSUME t2c_ofsok) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`src:int64`; `ofs:num`] VAL_WORD_ADD_NOWRAP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(src:int64) + LENGTH(st:byte list) + 8 < 2 EXP 64`;
      `ofs <= LENGTH(st:byte list)`] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `bc < 2 EXP 32` ASSUME_TAC THENL [ML2_ARITH_TAC; ALL_TAC] THEN
  T2_OPVAL_TAC [`jj:num`; `L:num`] THEN
  ML2_STEP_TAC 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`op:int64`; `L:num`; `jj:num`]
    T2_ROOM) (ASSUME `jj <= L`)]) THEN
  ASM_CASES_TAC `bc <= 64` THENL
   [ASM_CASES_TAC `jj + 8 <= L` THENL
     [ASM_CASES_TAC `tl <= 11` THENL
       [ASM_CASES_TAC `9 <= L` THENL
         [ML2_SIM_UNTIL_TAC [spec.a_r5] THEN T4_SHIFT_TAC THEN
          T2S_GOON_TAC r5post_th (Some `L - jj`)
            [`jj:num`; `ofs:num`; `bc:num`];
          TAIL2S_ENTRY_L8_TAC spec mid_th];
        ML2_SIM_UNTIL_TAC [spec.a_r4] THEN T4_SHIFT_TAC THEN
        T2S_GOON_TAC r4post_th (Some `L - jj`)
          [`jj:num`; `ofs:num`; `bc:num`]];
      TAIL2S_SHORT_TAC spec mid_th];
    ASM_CASES_TAC `jj + 8 <= L` THENL
     [overflow_mid;
      ASM_CASES_TAC `jj + 2 <= L` THENL
       [ML2_SIM_UNTIL_TAC [spec.a_after1] THEN
        W(fun (asl,w) ->
          T2S_GOON_TAC after1_th None
           [`jj:num`; `ofs:num`; `bc:num`; t2s_regv asl spec.pptr2]);
        ML2_SIM_UNTIL_TAC [spec.a_last] THEN
        W(fun (asl,w) ->
          T2S_GOON_TAC last_th None
           [`jj:num`; `ofs:num`; `bc:num`; t2s_regv asl spec.pptr2])]]];;

(*** The proofs of the pieces of the tails for any block (safety), by ***)
(*** stream                                                            ***)

let TAIL2S_1_B4 = prove(t2s_b4_goal tail2_1,
  TAIL2S_BODY_TAC tail2_1 tail2_1.a_r4 tail2_1.bc4);;
let TAIL2S_1_L4 = prove(t2s_r4_goal tail2_1,
  TAIL2S_LOOP_TAC tail2_1 (tail2_inst tail2_1 (t2v "r_f4")) `8`
    tail2_1.a_b4 tail2_1.a_mid TAIL2S_1_B4);;
let TAIL2S_1_B5 = prove(t2s_b5_goal tail2_1,
  TAIL2S_BODY_TAC tail2_1 tail2_1.a_r5 tail2_1.bc5);;
let TAIL2S_1_L5 = prove(t2s_r5_goal tail2_1,
  TAIL2S_LOOP_TAC tail2_1 (tail2_inst tail2_1 (t2v "r_f5")) `10`
    tail2_1.a_b5 tail2_1.a_mid TAIL2S_1_B5);;
let TAIL2S_1_L1 = prove(t2s_r1_goal tail2_1, TAIL2S_L1_TAC tail2_1);;
let TAIL2S_1_LAST = prove(t2s_last_goal tail2_1, TAIL2S_LAST_TAC tail2_1);;
let TAIL2S_1_L0 = prove(t2s_l0_goal tail2_1, TAIL2S_L0_TAC tail2_1);;
let TAIL2S_1_L0POST = prove(t2s_l0post_goal tail2_1,
  T2S_TRANS_TAC tail2_1 (t2s_last tail2_1) TAIL2S_1_L0 TAIL2S_1_LAST);;
let TAIL2S_1_AFTER1 = prove(t2s_after1_goal tail2_1,
  TAIL2S_AFTER1_TAC tail2_1 TAIL2S_1_L0POST TAIL2S_1_LAST);;
let TAIL2S_1_R1POST = prove(t2s_r1post_goal tail2_1,
  T2S_TRANS_TAC tail2_1 (t2s_after1 tail2_1) TAIL2S_1_L1 TAIL2S_1_AFTER1);;
let TAIL2S_1_MID = prove(t2s_mid_goal tail2_1,
  TAIL2S_MID_TAC tail2_1 TAIL2S_1_R1POST TAIL2S_1_AFTER1 TAIL2S_1_LAST);;
let TAIL2S_1_R4POST = prove(t2s_r4post_goal tail2_1,
  T2S_TRANS_TAC tail2_1 (t2s_mid tail2_1) TAIL2S_1_L4 TAIL2S_1_MID);;
let TAIL2S_1_R5POST = prove(t2s_r5post_goal tail2_1,
  T2S_TRANS_TAC tail2_1 (t2s_mid tail2_1) TAIL2S_1_L5 TAIL2S_1_MID);;
let TAIL2S_1_TAIL = prove(t2s_tail_goal tail2_1,
  TAIL2S_ENTRY_TAC tail2_1 TAIL2S_1_R4POST TAIL2S_1_R5POST TAIL2S_1_MID
    TAIL2S_1_AFTER1 TAIL2S_1_LAST);;

let TAIL2S_2_B4 = prove(t2s_b4_goal tail2_2,
  TAIL2S_BODY_TAC tail2_2 tail2_2.a_r4 tail2_2.bc4);;
let TAIL2S_2_L4 = prove(t2s_r4_goal tail2_2,
  TAIL2S_LOOP_TAC tail2_2 (tail2_inst tail2_2 (t2v "r_f4")) `8`
    tail2_2.a_b4 tail2_2.a_mid TAIL2S_2_B4);;
let TAIL2S_2_B5 = prove(t2s_b5_goal tail2_2,
  TAIL2S_BODY_TAC tail2_2 tail2_2.a_r5 tail2_2.bc5);;
let TAIL2S_2_L5 = prove(t2s_r5_goal tail2_2,
  TAIL2S_LOOP_TAC tail2_2 (tail2_inst tail2_2 (t2v "r_f5")) `10`
    tail2_2.a_b5 tail2_2.a_mid TAIL2S_2_B5);;
let TAIL2S_2_L1 = prove(t2s_r1_goal tail2_2, TAIL2S_L1_TAC tail2_2);;
let TAIL2S_2_LAST = prove(t2s_last_goal tail2_2, TAIL2S_LAST_TAC tail2_2);;
let TAIL2S_2_L0 = prove(t2s_l0_goal tail2_2, TAIL2S_L0_TAC tail2_2);;
let TAIL2S_2_L0POST = prove(t2s_l0post_goal tail2_2,
  T2S_TRANS_TAC tail2_2 (t2s_last tail2_2) TAIL2S_2_L0 TAIL2S_2_LAST);;
let TAIL2S_2_AFTER1 = prove(t2s_after1_goal tail2_2,
  TAIL2S_AFTER1_TAC tail2_2 TAIL2S_2_L0POST TAIL2S_2_LAST);;
let TAIL2S_2_R1POST = prove(t2s_r1post_goal tail2_2,
  T2S_TRANS_TAC tail2_2 (t2s_after1 tail2_2) TAIL2S_2_L1 TAIL2S_2_AFTER1);;
let TAIL2S_2_MID = prove(t2s_mid_goal tail2_2,
  TAIL2S_MID_TAC tail2_2 TAIL2S_2_R1POST TAIL2S_2_AFTER1 TAIL2S_2_LAST);;
let TAIL2S_2_R4POST = prove(t2s_r4post_goal tail2_2,
  T2S_TRANS_TAC tail2_2 (t2s_mid tail2_2) TAIL2S_2_L4 TAIL2S_2_MID);;
let TAIL2S_2_R5POST = prove(t2s_r5post_goal tail2_2,
  T2S_TRANS_TAC tail2_2 (t2s_mid tail2_2) TAIL2S_2_L5 TAIL2S_2_MID);;
let TAIL2S_2_TAIL = prove(t2s_tail_goal tail2_2,
  TAIL2S_ENTRY_TAC tail2_2 TAIL2S_2_R4POST TAIL2S_2_R5POST TAIL2S_2_MID
    TAIL2S_2_AFTER1 TAIL2S_2_LAST);;

let TAIL2S_3_B4 = prove(t2s_b4_goal tail2_3,
  TAIL2S_BODY_TAC tail2_3 tail2_3.a_r4 tail2_3.bc4);;
let TAIL2S_3_L4 = prove(t2s_r4_goal tail2_3,
  TAIL2S_LOOP_TAC tail2_3 (tail2_inst tail2_3 (t2v "r_f4")) `8`
    tail2_3.a_b4 tail2_3.a_mid TAIL2S_3_B4);;
let TAIL2S_3_B5 = prove(t2s_b5_goal tail2_3,
  TAIL2S_BODY_TAC tail2_3 tail2_3.a_r5 tail2_3.bc5);;
let TAIL2S_3_L5 = prove(t2s_r5_goal tail2_3,
  TAIL2S_LOOP_TAC tail2_3 (tail2_inst tail2_3 (t2v "r_f5")) `10`
    tail2_3.a_b5 tail2_3.a_mid TAIL2S_3_B5);;
let TAIL2S_3_L1 = prove(t2s_r1_goal tail2_3, TAIL2S_L1_TAC tail2_3);;
let TAIL2S_3_LAST = prove(t2s_last_goal tail2_3, TAIL2S_LAST_TAC tail2_3);;
let TAIL2S_3_L0 = prove(t2s_l0_goal tail2_3, TAIL2S_L0_TAC tail2_3);;
let TAIL2S_3_L0POST = prove(t2s_l0post_goal tail2_3,
  T2S_TRANS_TAC tail2_3 (t2s_last tail2_3) TAIL2S_3_L0 TAIL2S_3_LAST);;
let TAIL2S_3_AFTER1 = prove(t2s_after1_goal tail2_3,
  TAIL2S_AFTER1_TAC tail2_3 TAIL2S_3_L0POST TAIL2S_3_LAST);;
let TAIL2S_3_R1POST = prove(t2s_r1post_goal tail2_3,
  T2S_TRANS_TAC tail2_3 (t2s_after1 tail2_3) TAIL2S_3_L1 TAIL2S_3_AFTER1);;
let TAIL2S_3_MID = prove(t2s_mid_goal tail2_3,
  TAIL2S_MID_TAC tail2_3 TAIL2S_3_R1POST TAIL2S_3_AFTER1 TAIL2S_3_LAST);;
let TAIL2S_3_R4POST = prove(t2s_r4post_goal tail2_3,
  T2S_TRANS_TAC tail2_3 (t2s_mid tail2_3) TAIL2S_3_L4 TAIL2S_3_MID);;
let TAIL2S_3_R5POST = prove(t2s_r5post_goal tail2_3,
  T2S_TRANS_TAC tail2_3 (t2s_mid tail2_3) TAIL2S_3_L5 TAIL2S_3_MID);;
let TAIL2S_3_TAIL = prove(t2s_tail_goal tail2_3,
  TAIL2S_ENTRY_TAC tail2_3 TAIL2S_3_R4POST TAIL2S_3_R5POST TAIL2S_3_MID
    TAIL2S_3_AFTER1 TAIL2S_3_LAST);;

let TAIL2S_4_B4 = prove(t2s_b4_goal tail2_4,
  TAIL2S_BODY_TAC tail2_4 tail2_4.a_r4 tail2_4.bc4);;
let TAIL2S_4_L4 = prove(t2s_r4_goal tail2_4,
  TAIL2S_LOOP_TAC tail2_4 (tail2_inst tail2_4 (t2v "r_f4")) `8`
    tail2_4.a_b4 tail2_4.a_mid TAIL2S_4_B4);;
let TAIL2S_4_B5 = prove(t2s_b5_goal tail2_4,
  TAIL2S_BODY_TAC tail2_4 tail2_4.a_r5 tail2_4.bc5);;
let TAIL2S_4_L5 = prove(t2s_r5_goal tail2_4,
  TAIL2S_LOOP_TAC tail2_4 (tail2_inst tail2_4 (t2v "r_f5")) `10`
    tail2_4.a_b5 tail2_4.a_mid TAIL2S_4_B5);;
let TAIL2S_4_L1 = prove(t2s_r1_goal tail2_4, TAIL2S_L1_TAC tail2_4);;
let TAIL2S_4_LAST = prove(t2s_last_goal tail2_4, TAIL2S_LAST_TAC tail2_4);;
let TAIL2S_4_L0 = prove(t2s_l0_goal tail2_4, TAIL2S_L0_TAC tail2_4);;
let TAIL2S_4_L0POST = prove(t2s_l0post_goal tail2_4,
  T2S_TRANS_TAC tail2_4 (t2s_last tail2_4) TAIL2S_4_L0 TAIL2S_4_LAST);;
let TAIL2S_4_AFTER1 = prove(t2s_after1_goal tail2_4,
  TAIL2S_AFTER1_TAC tail2_4 TAIL2S_4_L0POST TAIL2S_4_LAST);;
let TAIL2S_4_R1POST = prove(t2s_r1post_goal tail2_4,
  T2S_TRANS_TAC tail2_4 (t2s_after1 tail2_4) TAIL2S_4_L1 TAIL2S_4_AFTER1);;
let TAIL2S_4_MID = prove(t2s_mid_goal tail2_4,
  TAIL2S_MID_TAC tail2_4 TAIL2S_4_R1POST TAIL2S_4_AFTER1 TAIL2S_4_LAST);;
let TAIL2S_4_R4POST = prove(t2s_r4post_goal tail2_4,
  T2S_TRANS_TAC tail2_4 (t2s_mid tail2_4) TAIL2S_4_L4 TAIL2S_4_MID);;
let TAIL2S_4_R5POST = prove(t2s_r5post_goal tail2_4,
  T2S_TRANS_TAC tail2_4 (t2s_mid tail2_4) TAIL2S_4_L5 TAIL2S_4_MID);;
let TAIL2S_4_TAIL = prove(t2s_tail_goal tail2_4,
  TAIL2S_ENTRY_TAC tail2_4 TAIL2S_4_R4POST TAIL2S_4_R5POST TAIL2S_4_MID
    TAIL2S_4_AFTER1 TAIL2S_4_LAST);;

(*** The body of the main loop for any block (safety), 0x3750 to 0x39d0: ***)
(*** 4 lookups of each stream with any bits, each index bounded by the  ***)
(*** table; each output 4 to 8 bytes on, each stream at most 48 more    ***)
(*** bits used                                                          ***)

let ml2s_body_pre1 =
 `read (r_c:tailreg) s =
  word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
  read (r_bc:tailreg) s = word bc /\
  read (r_op:tailreg) s = word_add op (word jj) /\
  bc <= 64 /\ jj + 8 <= L`;;

let ml2s_body_post1 =
 `?jj' bc'.
    read (r_c:tailreg) s =
    word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
         2 EXP 64) /\
    read (r_bc:tailreg) s = word bc' /\
    read (r_op:tailreg) s = word_add op (word jj') /\
    jj + 4 <= jj' /\ jj' <= jj + 8 /\ bc' <= bc + 48`;;

let ml2s_hyps_out =
  map (fun k -> ml2_inst (el (k - 1) ml2_streams)
   `L < 2 EXP 28 /\ val(op:int64) + L < 2 EXP 64 /\
    nonoverlapping (op,L) (tbl:int64,4 * 2 EXP tl) /\
    nonoverlapping (op,L) (word pc,32000)`) [1;2;3;4];;

let ml2s_body_hyps = list_mk_conj
 ([`aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64`;
   `huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
    1 <= ml /\ ml <= tl /\ 1 <= tl /\ tl <= 12`] @ ml2s_hyps_out);;

let ml2s_body_pre = with_memsafe ml2_rr ml2_wr (mk_abs(`s:armstate`,
  list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x3750) /\
      read X5 s = tbl /\ read X2 s = word(64 - tl) /\
      read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable2 ws ml tl)`] @
    map (fun m -> ml2_inst m ml2s_body_pre1) ml2_streams)));;

let ml2s_body_post = with_memsafe ml2_rr ml2_wr (mk_abs(`s:armstate`,
  list_mk_conj
   (`read PC s = word(pc + 0x39d0)` ::
    map (fun m -> ml2_inst m ml2s_body_post1) ml2_streams)));;

let ml2s_body_goal =
  let tm = mk_imp(ml2s_body_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; ml2s_body_pre; ml2s_body_post; ml2_body_frame]) in
  let fvs = frees tm in
  (match subtract fvs ml2_body_vars with
     [] -> ()
   | v::_ -> failwith ("ml2s_body_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) ml2_body_vars,tm);;

(*** The simulation with the lookups of any bits, then for each stream ***)
(*** its output and bits used from the registers                       ***)

let ML2S_BODY_TAC =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN FL_ABBREV_POST_TAC THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN
  (fun gl -> ml2_counter := 0; ALL_TAC gl) THEN
  SF2_SIM_UNTIL_TAC [0x39d0] THEN
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let m = find (fun m -> free_in (ml2_var m.mk2 ("st",`:byte list`)) w)
                 ml2_streams in
    let s = t2_state asl m.mop2 in
    let jv = fl_num_norm(t2_regval asl s m.mop2)
    and bv = t2_regval asl s m.mbc2 in
    MAP_EVERY EXISTS_TAC [jv; bv] THEN T2_LITE_CONJ_TAC);;

(*** The bound of the outputs of streams 1-3 by that of stream 4 in the ***)
(*** main loop for any block (only the room of stream 4 is checked)     ***)

let ml2s_jbound = `jj1 <= 2 * jj4 /\ jj2 <= 2 * jj4 /\ jj3 <= 2 * jj4`;;

let ML2S_BODY = prove(ml2s_body_goal, ML2S_BODY_TAC);;

(*** The main loop for any block (safety), from the body to an exit: as ***)
(*** ML2_LOOP without the decodings. Only the room of stream 4 is       ***)
(*** checked, so the outputs of streams 1-3 are bounded by twice that   ***)
(*** of stream 4 (4 to 8 bytes an iteration), within regions L_k of at  ***)
(*** least twice the room L4 of stream 4                                ***)

let ml2s_inv1 q = ml2_qinst q (list_mk_conj
 [mk_eq(`read (r_c:tailreg) s`,t2_win);
  `read (r_bc:tailreg) s = word bc /\
   read (r_ptr:tailreg) s = word_add src (word ofs) /\
   read (r_op:tailreg) s = word_add op (word jj)`;
  q.qlim;
  `read (memory :> bytes(src,LENGTH(st:byte list))) s =
   num_of_bytelist st /\
   bc <= 64 /\ (ofs = 0 \/ bc <= 8) /\ (ofs = 0 \/ ofs + 8 <= LENGTH st)`]);;

let ml2s_inv_body =
  list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x3750) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X5 s = tbl /\ read X2 s = word(64 - tl) /\
      read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable2 ws ml tl)`;
     subst [t2_spk 120,`a:int64`]
      `read (memory :> bytes64 a) s = word_add op4 (word (L4 - 7))`;
     `jj4 + 8 <= L4`; ml2s_jbound] @
    map ml2_struct0 ml2_q @ map ml2s_inv1 ml2_q @ [ml2_flags]);;

let ml2s_inv = with_memsafe ml2_lrr ml2_lwr
 (list_mk_abs([`m:num`; `s:armstate`],
  list_mk_exists(List.concat(map ml2_pervars [1;2;3;4]) @ [`f:num`],
    mk_conj(`m = L4 - jj4`,ml2s_inv_body))));;

(*** One stream at the exit: more than 64 bits used only at the start of ***)
(*** the stream, and at most 12 for each byte                            ***)

let ml2s_lexit1 q = ml2_qinst q (list_mk_conj
 [mk_eq(`read (r_c:tailreg) s`,t2_win);
  `read (r_bc:tailreg) s = word bc /\
   read (r_ptr:tailreg) s = word_add src (word ofs) /\
   read (r_op:tailreg) s = word_add op (word jj) /\
   read (memory :> bytes(src,LENGTH(st:byte list))) s =
   num_of_bytelist st /\
   bc <= 64 + 12 * jj /\ (64 < bc ==> ofs = 0) /\
   (ofs = 0 \/ ofs + 8 <= LENGTH st)`]);;

let ml2s_lexit_raw = mk_abs(`s:armstate`,
  list_mk_exists(List.concat(map ml2_pervars [1;2;3;4]) @
                 [`f1:num`; `f2:num`; `f3:num`; `f4:num`],
   list_mk_conj
    ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
       read SP s = word_sub stackpointer (word 496)`;
      ml_mem32 140 `f1:num`; ml_mem32 132 `f2:num`; ml_mem32 136 `f3:num`;
      ml2s_jbound; `jj4 <= L4`] @
     map ml2s_lexit1 ml2_q @
     map (fun k ->
       let f = mk_var("f"^string_of_int k,`:num`) in
       mk_conj(mk_disj(mk_eq(f,`0`),mk_eq(f,`1`)),
               mk_imp(mk_eq(f,`0`),mk_eq(ml2_var k ("ofs",`:num`),ml2_o0 k))))
       [1;2;3;4] @
     [mk_disj(mk_conj(`read PC s = word(pc + 0x47d4)`,ml_mem32 184 `f4:num`),
              `read PC s = word(pc + 0x4bbc)`)])));;

let ml2s_lexit = with_memsafe ml2_lrr ml2_lwr ml2s_lexit_raw;;

(*** The hypotheses: those of ML2_LOOP without the decodings and without ***)
(*** the outputs apart, and the regions L_k of streams 1-3 at least      ***)
(*** twice L4                                                            ***)

let ml2s_loop_hyps =
  let bad t =
    can (find_term (fun u -> is_const u &&
           fst(dest_const u) = "huf_decode")) t ||
    (match strip_comb t with
       Const("nonoverlapping",_),[a;b] ->
         let isout p = can (find_term (fun u -> is_var u &&
                         String.length(fst(dest_var u)) = 3 &&
                         String.sub (fst(dest_var u)) 0 2 = "op")) p in
         isout a && isout b
     | _ -> false) in
  let strip t = match filter (not o bad) (conjuncts t) with
                  [] -> failwith "strip"
                | cs -> list_mk_conj cs in
  mapfilter strip ml2_loop_hyps @
  [`2 * L4 <= L1 /\ 2 * L4 <= L2 /\ 2 * L4 <= L3`];;

let ml2s_loop_goal =
  let tm = mk_imp(list_mk_conj ml2s_loop_hyps,
                  list_mk_icomb "ensures"
                   [`arm`;
                    mk_abs(`s:armstate`,mk_exists(`m:num`,
                      list_mk_comb(ml2s_inv,[`m:num`; `s:armstate`])));
                    ml2s_lexit; ml2_loop_frame]) in
  let fvs = frees tm in
  (match subtract fvs ml2_loop_vars with
     [] -> ()
   | v::_ -> failwith ("ml2s_loop_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) ml2_loop_vars,tm);;

(*** The facts of stream q after the body for the exit, while no ***)
(*** divisions are around (the arithmetic with them is slow), not ***)
(*** connecting its output and its bits (ML2_ARITH_TAC would then ***)
(*** take in the divisions of all four streams)                   ***)

let ML2S_LOOP_FACTS_TAC (q:ml2q) : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let b = t2_regval asl s q.qbc and j = t2_regval asl s q.qop in
    let ofs = ml2_var q.qk ("ofs",`:num`) in
    let g = subst [b,`b:num`; j,`j:num`; ofs,`ofs:num`]
              `b <= 112 /\ 4 <= j /\ (64 < b ==> ofs = 0)` in
    SUBGOAL_THEN g STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC]);;

(*** The loop up to the decision: the room of each stream for the body, ***)
(*** the body and the four reloads by big steps                        ***)

let ML2S_LOOP_START_TAC =
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
    (List.concat(map ml2_pervars [1;2;3;4])) THEN
  ENSURES_EXISTS_PRE_TAC `f:num` THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `jj1 + 8 <= L1 /\ jj2 + 8 <= L2 /\ jj3 + 8 <= L3`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN ML2_ARITH_TAC; ALL_TAC] THEN
  ML2_BIGSTEP_TAC ML2S_BODY [] THEN
  MAP_EVERY ML2_LOOP_FACTS_TAC ml2_q THEN
  MAP_EVERY ML2S_LOOP_FACTS_TAC ml2_q THEN
  SUBGOAL_THEN `f < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(ASSUME `f = 0 \/ f = 1`) THEN ARITH_TAC; ALL_TAC] THEN
  ML2_RL_STEP_TAC RL2_1 (el 0 ml2_q) [("f",`f:num`); ("w",`0`)] THEN
  ML_STATUS_TAC `w1:num` `ofs1:num` `0` THEN
  ML2_RL_STEP_TAC RL2_2 (el 1 ml2_q) [("f",`f:num`); ("w",`w1:num`)] THEN
  ML_STATUS_TAC `w2:num` `ofs2:num` `w1:num` THEN
  ML2_RL_STEP_TAC RL2_3 (el 2 ml2_q) [("f",`f:num`); ("w",`w2:num`)] THEN
  ML_STATUS_TAC `w3:num` `ofs3:num` `w2:num` THEN
  SUBGOAL_THEN `7 <= L4` ASSUME_TAC THENL
   [MP_TAC(ASSUME `jj4 + 8 <= L4`) THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let j4 = t2_regval asl (rand w) `X10` in
    SUBGOAL_THEN (mk_binop `(<=):num->num->bool` j4 `L4:num`) ASSUME_TAC
    THENL [ML2_ARITH_TAC; ALL_TAC] THEN
    ML2_RL_STEP_TAC RL2_4 (el 3 ml2_q)
     [("f",`f:num`); ("w",`w3:num`); ("op",`op4:int64`); ("L",`L4:num`);
      ("jj",j4)]);;

let ML2S_LOOP_TAC = ML2S_LOOP_START_TAC THEN ML2_LOOP_DECIDE_TAC;;

let ML2S_LOOP = prove(ml2s_loop_goal, ML2S_LOOP_TAC);;

(*** The rest of the slow path for any block (safety): from the check of ***)
(*** the order of the outputs (0x3a98), its error or the tails of the   ***)
(*** four streams and the end checks, to the epilogue (0x333c) with the ***)
(*** result n or an error                                               ***)

(*** The safety tails without the code in their postconditions ***)

let rs2s_tail_post spec =
  let p = tail2_inst spec (t2s_post spec) in
  let v,b = dest_abs p in
  let code = subst [v,`s:armstate`]
    `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc` in
  let rec drop t =
    if is_exists t then let x,u = dest_exists t in mk_exists(x,drop u)
    else if is_conj t then
      let l,r = dest_conj t in
      if l = code then drop r
      else if is_conj l then mk_conj(drop l,r)
      else mk_conj(l,drop r)
    else t in
  mk_abs(v,drop b);;

let rs2s_tail_goal spec =
  let tm = mk_imp(t2s_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; tail2_inst spec (t2s_entry spec);
                    rs2s_tail_post spec; tail2_frame spec]) in
  let vs = t2_vars @ [`jj:num`; `ofs:num`; `bc:num`] in
  list_mk_forall(filter (fun v -> mem v (frees tm)) vs,tm);;

let RS2S_TAIL_TAC th : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL th)) THEN
  MATCH_MP_TAC RS2_ENSURES_WEAKEN THEN CONJ_TAC THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THENL
   [DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p:int64` (X_CHOOSE_THEN `b:int32`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`p:int64`; `b:int32`] THEN ASM_REWRITE_TAC[]];;

(*** The goal: each stream after jj bytes with any bits used (more than ***)
(*** 64 only with the pointer at the start), its BIT_DStream in the     ***)
(*** frame; the outputs of streams 1-3 at most twice that of stream 4   ***)

let rs2s_exit1 (q:ml2q) = rs2_inst q.qk (list_mk_conj
 [vsubst [q.qop,t2v "r_op"]
   `read (r_op:tailreg) s = word_add op (word jj)`;
  subst [mk_small_numeral q.qsofs,`s_c:num`;
         mk_small_numeral(q.qsofs + 8),`s_b:num`;
         mk_small_numeral(q.qsofs + 16),`s_p:num`] t2c_bd;
  `read (memory :> bytes(src,LENGTH(st:byte list))) s =
   num_of_bytelist st /\
   bc <= 64 + 12 * jj /\ (64 < bc ==> ofs = 0) /\
   (ofs = 0 \/ ofs + 8 <= LENGTH st)`]);;

(*** The regions written: those of the tails, and those of the main loop ***)
(*** (op_k, M_k) for streams 1-3, which may go past their segments       ***)

let rs2s_lwr =
  mk_list(map (fun k -> mk_pair(ml2_var k ("op",`:int64`),
                                ml2_var k ("L",`:num`))) [1;2;3;4] @
          map (fun k -> mk_pair(ml2_var k ("op",`:int64`),
                                mk_var("M"^string_of_int k,`:num`))) [1;2;3] @
          [`word_sub stackpointer (word 496):int64,496`],`:int64#num`);;

let rs2s_pre =
  let v k s ty = ml2_var k (s,ty) in
  with_memsafe rs2_lrr rs2s_lwr (mk_abs(`s:armstate`,list_mk_conj
   ([`aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
      read PC s = word(pc + 0x3a98) /\
      read SP s = word_sub stackpointer (word 496) /\
      read X5 s = tbl /\
      read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
      num_of_bytelist(huf_dtable2 ws ml tl) /\
      read X23 s = word tl /\ read X20 s = word n`;
     mk_eq(`read X14 s`,list_mk_icomb "word_add"
       [v 4 "op" `:int64`; mk_comb(`word:num->int64`,v 4 "L" `:num`)]);
     mk_eq(`read X12 s`,v 2 "op" `:int64`);
     mk_eq(`read X13 s`,v 3 "op" `:int64`);
     mk_eq(`read X11 s`,v 4 "op" `:int64`);
     mk_eq(`read X18 s`,v 1 "src" `:int64`);
     mk_eq(`read X15 s`,v 2 "src" `:int64`);
     mk_eq(`read X9 s`,v 3 "src" `:int64`);
     mk_eq(`read X24 s`,v 4 "src" `:int64`);
     rs2_inst 1 `read X28 s = word_add src (word 8)`;
     rs2_inst 2 (t2_lim_mem 96); rs2_inst 3 (t2_lim_mem 104);
     rs2_inst 4 (t2_lim_mem 112);
     rs2_inst 4 (subst [t2_spk 120,`a:int64`]
       `read (memory :> bytes64 a) s =
        word_sub (word_add op (word L)) (word 7)`);
     `read X25 s = v25 /\ read X26 s = v26`;
     ml_mem64 80 `v27:int64`; ml_mem64 88 `v28:int64`;
     ml2s_jbound; `jj4 <= L4`] @
    map rs2s_exit1 ml2_q)));;

let rs2s_post = with_memsafe rs2_lrr rs2s_lwr (mk_abs(`s:armstate`,
 `read PC s = word(pc + 0x333c) /\
  (read X0 s = word n \/ read X0 s = word 18446744073709551596) /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28`));;

let rs2s_hyps =
  let bad t =
    can (find_term (fun u -> is_const u &&
           fst(dest_const u) = "huf_decode")) t ||
    (match strip_comb t with
       Const("nonoverlapping",_),[a;b] ->
         let isout p = can (find_term (fun u -> is_var u &&
                         String.length(fst(dest_var u)) = 3 &&
                         String.sub (fst(dest_var u)) 0 2 = "op")) p in
         isout a && isout b
     | _ -> false) in
  let strip t = match filter (not o bad) (conjuncts t) with
                  [] -> failwith "strip"
                | cs -> list_mk_conj cs in
  mapfilter strip ml2_loop_hyps @
  [`word_add op1 (word L1) = op2:int64 /\
    word_add op2 (word L2) = op3:int64 /\
    word_add op3 (word L3) = op4:int64`;
   `~(val(op1:int64) = 0) /\ ~(val(op2:int64) = 0) /\
    ~(val(op3:int64) = 0) /\ ~(val(op4:int64) = 0)`;
   `val(op1:int64) + 2 * L4 < 2 EXP 64 /\ val(op2:int64) + 2 * L4 < 2 EXP 64 /\
    val(op3:int64) + 2 * L4 < 2 EXP 64`];;

let rs2s_vars = rs2_vars @ [`M1:num`; `M2:num`; `M3:num`];;

let rs2s_goal =
  let tm = mk_imp(list_mk_conj rs2s_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; rs2s_pre; rs2s_post; rs2_frame]) in
  let fvs = frees tm in
  (match subtract fvs rs2s_vars with
     [] -> ()
   | v::_ -> failwith ("rs2s_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) rs2s_vars,tm);;

let RS2S_TAIL1 = prove(rs2s_tail_goal tail2_1, RS2S_TAIL_TAC TAIL2S_1_TAIL);;
let RS2S_TAIL2 = prove(rs2s_tail_goal tail2_2, RS2S_TAIL_TAC TAIL2S_2_TAIL);;
let RS2S_TAIL3 = prove(rs2s_tail_goal tail2_3, RS2S_TAIL_TAC TAIL2S_3_TAIL);;
let RS2S_TAIL4 = prove(rs2s_tail_goal tail2_4, RS2S_TAIL_TAC TAIL2S_4_TAIL);;

(*** The facts for the order check (as RS2_ORDER_FACTS_TAC, each output ***)
(*** bounded by twice that of stream 4): the values of op_k + L_k and of ***)
(*** op_k + jj_k, with op_k itself (with op_k+1 the comparisons of the   ***)
(*** simulation get mixed forms, which it cannot decide when they fail)  ***)

let RS2S_ORDER_FACTS_TAC : tactic =
  MAP_EVERY (fun (a,b) ->
    let la = ml2_var a ("L",`:num`) and ja = ml2_var a ("jj",`:num`) in
    let oa = ml2_var a ("op",`:int64`) in
    let lt = mk_binop `(<):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,oa))
                  la) `2 EXP 64` in
    let th1 = MP (SPECL [oa; la] VAL_WORD_ADD_NOWRAP) (ASSUME lt) in
    let ltj = mk_binop `(<):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,oa))
                  ja) `2 EXP 64` in
    ASSUME_TAC th1 THEN
    SUBGOAL_THEN ltj ASSUME_TAC THENL [ML2_ARITH_TAC; ALL_TAC] THEN
    ASSUME_TAC(MP (SPECL [oa; ja] VAL_WORD_ADD_NOWRAP) (ASSUME ltj)))
   [1,2; 2,3; 3,4];;

(*** The order check with the ends of the first three outputs as op_k + ***)
(*** L_k, split on the three comparisons: the tails, or the error -20   ***)

let RS2S_ORDER_TAC (ok:tactic) (bad:tactic) : tactic =
  let hs = [`word_add op1 (word L1) = op2:int64`;
            `word_add op2 (word L2) = op3:int64`;
            `word_add op3 (word L3) = op4:int64`]
  and regs = [`X12`; `X13`; `X11`] in
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
    ASM_CASES_TAC `jj1 <= L1` THEN ASM_CASES_TAC `jj2 <= L2` THEN
    ASM_CASES_TAC `jj3 <= L3` THEN
    ML2_SIM_UNTIL_TAC [0x3ab4; 0x333c] THEN MAP_EVERY ASSUME_TAC hths THEN
    W(fun gl -> if bk_at 0x3ab4 gl then ok else bad));;

(*** The tail of stream k by a big step, and the end checks with the ***)
(*** pointers and the bits used at the ends of the tails (the facts  ***)
(*** about the bits as words of their values only: the big step      ***)
(*** rewrites its precondition with the facts)                       ***)

let RS2S_TAIL_STEP_TAC k th : tactic =
  let names = map fst ml2_names in
  ML2_BIGSTEP_TAC th
   (map (fun n -> n,ml2_var k (n,assoc n ml2_names)) names @
    [("x25",`v25:int64`); ("x26",`v26:int64`)]);;

let RS2S_BITS_TAC : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let one k =
      let rd = subst [t2_spk (232 + 40 * (k - 1)),`a:int64`; s,`s:armstate`]
                 `read (memory :> bytes32 a) (s:armstate)` in
      FIRST_X_ASSUM(fun th ->
        let t = concl th in
        if is_eq t && lhs t = rd then
          let b = rhs t in
          ASSUME_TAC(REWRITE_RULE[DIMINDEX_32] (ISPEC b VAL_BOUND)) THEN
          ASSUME_TAC(TRANS th (SYM(ISPEC b WORD_VAL)))
        else NO_TAC) in
    MAP_EVERY one [1;2;3;4]);;

let RS2S_ENDCHK_TAC : tactic =
  RS2S_BITS_TAC THEN
  W(fun (asl,w) ->
    let s = rand w in
    let regs = [`X21`; `X12`; `X7`; `X3`] in
    let pv k = rhs(concl(snd(find (fun (_,th) -> let t = concl th in
                 is_eq t && lhs t = list_mk_icomb "read" [el (k - 1) regs; s])
                 asl))) in
    let slot k = t2_spk (232 + 40 * (k - 1)) in
    let bv k =
      let t = snd(find (fun (_,th) -> let t = concl th in
                is_eq t && is_comb(lhs t) && rand(lhs t) = s &&
                can (find_term ((=) (slot k))) (lhs t) &&
                is_comb(rhs t) && rator(rhs t) = `word:num->int32`) asl) in
      rand(rhs(concl t)) in
    ML2_BIGSTEP_TAC ENDCHK2_CORRECT
     (map (fun k -> "a"^string_of_int k,ml2_var k ("src",`:int64`))
          [1;2;3;4] @
      map (fun k -> "p"^string_of_int k,pv k) [1;2;3;4] @
      map (fun k -> "b"^string_of_int k,bv k) [1;2;3;4]));;

let RS2S_OK_TAC : tactic =
  MAP_EVERY (fun (k,th) -> RS2S_TAIL_STEP_TAC k th)
   [1,RS2S_TAIL1; 2,RS2S_TAIL2; 3,RS2S_TAIL3; 4,RS2S_TAIL4] THEN
  RS2S_ENDCHK_TAC THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[];;

let RS2S_BAD_TAC : tactic =
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let RS2S_CORRECT = prove
 (rs2s_goal,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN RS2S_ORDER_FACTS_TAC THEN
  RS2S_ORDER_TAC RS2S_OK_TAC RS2S_BAD_TAC);;

(*** The main loop for any block from its first iteration, with the ***)
(*** disjunctions of its exit folded into definitions, for big steps ***)
(*** (as ML2_LOOPWF)                                                 ***)

let ml2s_loopw_pre =
  let sub = List.concat (map (fun k ->
              [`0`,ml2_var k ("jj",`:num`);
               ml2_o0 k,ml2_var k ("ofs",`:num`);
               ml2_bc0 k,ml2_var k ("bc",`:num`)]) [1;2;3;4]) @
            [`0`,`f:num`] in
  with_memsafe ml2_lrr ml2_lwr
   (mk_abs(`s:armstate`,vsubst sub ml2s_inv_body));;

let ml2s_lexitF =
  let fold k =
    let ofs = ml2_var k ("ofs",`:num`) and st = ml2_var k ("st",`:byte list`)
    and f = mk_var("f"^string_of_int k,`:num`) in
    let lst = mk_comb(`LENGTH:byte list->num`,st) in
    [mk_disj(mk_eq(ofs,`0`),mk_binop `(<=):num->num->bool`
                              (mk_binop `(+):num->num->num` ofs `8`) lst),
     list_mk_icomb "ml_ofsok" [ofs; st];
     mk_conj(mk_disj(mk_eq(f,`0`),mk_eq(f,`1`)),
             mk_imp(mk_eq(f,`0`),mk_eq(ofs,ml2_o0 k))),
     list_mk_icomb "ml_flagok" [f; ofs; ml2_o0 k]] in
  let pairs = List.concat(map (fun k -> let [(a,b); (c,d)] = fold k in
                                        [(b,a); (d,c)]) [1;2;3;4]) @
              [ml2_nocode_pair] in
  with_memsafe ml2_lrr ml2_lwr (ml2_subst_body pairs ml2s_lexit_raw);;

let ml2s_loopwf_goal =
  let tm = mk_imp(list_mk_conj ml2s_loop_hyps,
                  list_mk_icomb "ensures"
                   [`arm`; ml2s_loopw_pre; ml2s_lexitF; ml2_loop_frame]) in
  let vs = ml2_loop_vars @ map ml2_bc0 [1;2;3;4] in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("ml2s_loopwf_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let ML2S_LOOPWF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL ML2S_LOOP)) THEN
  MATCH_MP_TAC RS_ENSURES_WEAKEN THEN CONJ_TAC THEN
  X_GEN_TAC `s:armstate` THEN BETA_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `L4:num` THEN
    MAP_EVERY EXISTS_TAC
     (List.concat(map (fun k -> [`0`; ml2_o0 k; ml2_bc0 k]) [1;2;3;4])) THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[SUB_0];
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
    THEN MAP_EVERY EXISTS_TAC
      (List.concat(map ml2_pervars [1;2;3;4]) @
       [`f1:num`; `f2:num`; `f3:num`; `f4:num`]) THEN
    ASM_REWRITE_TAC[ml_ofsok; ml_flagok]];;

let ML2S_LOOPWF = prove(ml2s_loopwf_goal, ML2S_LOOPWF_TAC);;

(*** The back of the slow path for any block, from the setup of the main ***)
(*** loop (0x3614) to 0x333c: the setup, then the loop and its exits or  ***)
(*** the skip, then the rest; the regions of the tails the segments,    ***)
(*** and those of the loop from dst + k * q to the end of the output (in ***)
(*** the order of the regions of RS2S_CORRECT)                          ***)

let bk2s_regions =
 [`dst:int64,q:num`; `word_add dst (word q):int64,q:num`;
  `word_add dst (word (2 * q)):int64,q:num`;
  `word_add dst (word (3 * q)):int64,n - 3 * q`;
  `dst:int64,n:num`; `word_add dst (word q):int64,n - q`;
  `word_add dst (word (2 * q)):int64,n - 2 * q`];;

let bk2s_rr = vsubst bk2_inst rs2_lrr
and bk2s_wr =
  mk_list(bk2s_regions @ [`word_sub stackpointer (word 496):int64,496`],
          `:int64#num`);;

let bk2s_post = with_memsafe bk2s_rr bk2s_wr (mk_abs(`s:armstate`,
 `read PC s = word(pc + 0x333c) /\
  (read X0 s = word n \/ read X0 s = word 18446744073709551596) /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28`));;

let bk2s_frame =
  let mems = map (fun t -> let a,n = dest_pair t in
                    subst [a,`a:int64`; n,`n:num`] `memory :> bytes(a,n)`)
                 bk2s_regions @
             [`memory :> bytes(word_add (word_sub stackpointer (word 496))
                                       (word 64),320)`] in
  list_mk_icomb ",,"
   [`MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17; X18; X19; X20; X21; X22; X23; X24;
                X25; X26; X27; X28; X30]`;
    list_mk_icomb ",,"
     [`MAYCHANGE [NF; ZF; CF; VF]`;
      list_mk_icomb ",,"
       [`MAYCHANGE [events]`;
        list_mk_icomb "MAYCHANGE" [mk_list(mems,type_of(hd mems))]]]];;

let bk2s_hyps =
  let bad t = can (find_term (fun u -> is_const u &&
                    fst(dest_const u) = "huf_decode")) t in
  map (fun t -> list_mk_conj(filter (not o bad) (conjuncts t))) bk2_hyps;;

let bk2s_goal =
  let tm = mk_imp(list_mk_conj bk2s_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; bk2_pre; bk2s_post; bk2s_frame]) in
  let fvs = frees tm in
  (match subtract fvs bk2_vars with
     [] -> ()
   | v::_ -> failwith ("bk2s_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) bk2_vars,tm);;

(*** The regions of the loop apart from the others, from those of the ***)
(*** whole output                                                      ***)

let BK2S_NONOV_SUFFIX = prove
 (`!(a:int64) n k (b:int64) m.
        k <= n /\ nonoverlapping (a,n) (b,m)
        ==> nonoverlapping (word_add a (word k),n - k) (b,m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`a:int64`; `n:num`; `b:int64`; `m:num`] THEN
  ASM_REWRITE_TAC[contained; DIMINDEX_64; CONTAINED_MODULO_REFL] THEN
  CONJ_TAC THENL [MEMSAFE_CONTAINED_MODULO_TAC; REWRITE_TAC[LE_REFL]]);;

let BK2S_NONOV_TAC : tactic =
  W(fun (asl,w) ->
    let outs = `(dst:int64),(n:num)` in
    let others = mapfilter (fun (_,th) ->
      match strip_comb(concl th) with
        Const("nonoverlapping",_),[a;b] when a = outs -> b
      | _ -> fail()) asl in
    let kqs = [`q:num`; `2 * q`; `3 * q`] in
    MAP_EVERY (fun kq ->
      let le = mk_binop `(<=):num->num->bool` kq `n:num` in
      SUBGOAL_THEN le ASSUME_TAC THENL
       [UNDISCH_TAC `3 * q <= n` THEN ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY (fun b ->
        let bb,bm = dest_pair b in
        let th = SPECL [`dst:int64`; `n:num`; kq; bb; bm] BK2S_NONOV_SUFFIX in
        ASSUME_TAC(MP th (CONJ (ASSUME le)
          (ASSUME(list_mk_icomb "nonoverlapping" [outs; b])))))
        others) kqs);;

(*** The loop with the regions to the end of the output ***)

let bk2s_loop_alist =
  [("tbl",`word_add dt (word 4):int64`);
   ("L1",`n:num`); ("L2",`n - q`); ("L3",`n - 2 * q`);
   ("L4",`n - 3 * q`)] @
  map (fun k -> ("op"^string_of_int k,bk_op k)) [1;2;3;4];;

let bk2s_m_alist = [("M1",`n:num`); ("M2",`n - q`); ("M3",`n - 2 * q`)];;

let BK2S_RS_TAC : tactic =
  W(fun gl ->
    let th = ml_inst_thm RS2S_CORRECT (bk2_alist @ bk2s_m_alist) in
    BK_GOON_TAC RS2S_CORRECT
      (bk2_alist @ bk2s_m_alist @ bk_auto_alist th gl));;

let BK2S_LOOP_TAC : tactic =
  BK2_LIMIT_TAC THEN BK2S_NONOV_TAC THEN
  BK2_BIGSTEP_TAC ML2S_LOOPWF bk2s_loop_alist THEN RS_2EXP64_TAC THEN
  BK2_EXIT_FACTS_TAC THEN
  W(fun gl -> if bk_at 0x47d4 gl
              then BK2_BIGSTEP_TAC EX2_A (bk_auto_alist EX2_A gl)
              else BK2_BIGSTEP_TAC EX2_B (bk_auto_alist EX2_B gl)) THEN
  RS_2EXP64_TAC THEN BK2S_RS_TAC;;

let BK2S_SKIP_TAC : tactic =
  BK2S_NONOV_TAC THEN RS_2EXP64_TAC THEN
  BK_GOON_TAC RS2S_CORRECT (bk2_alist @ bk2s_m_alist @ bk2_skip_alist);;

let BK2S_TAC : tactic =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN BK2_FACTS_TAC THEN
  BK2_BIGSTEP_TAC ST2_CORRECT bk2_st_alist THEN
  W(fun gl -> if bk_at 0x3750 gl then BK2S_LOOP_TAC else BK2S_SKIP_TAC);;

let BK2S_CORRECT = prove(bk2s_goal, BK2S_TAC);;

(*** The slow path as a whole for any block (0x32d0 to 0x333c): the ***)
(*** result n or an error, within the regions, x25-x28 restored     ***)

let sp2s_post = with_memsafe sp2_rr sp2_wr (mk_abs(`s:armstate`,
 `read PC s = word(pc + 0x333c) /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28 /\
  (read X0 s = word n \/ zstd_is_error(read X0 s))`));;

let sp2s_hyps =
  filter (fun t -> not(can (find_term (fun u -> is_const u &&
                     fst(dest_const u) = "huf_streams4")) t)) sp2_hyps;;

let sp2s_goal =
  let tm = mk_imp(list_mk_conj sp2s_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; sp2_pre; sp2s_post; sp2_frame]) in
  let fvs = frees tm in
  (match subtract fvs sp2_vars with
     [] -> ()
   | v::_ -> failwith ("sp2s_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) sp2_vars,tm);;

(*** An error at the epilogue ***)

let SP2S_FAIL_TAC : tactic =
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[zstd_is_error] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let SP2S_GUARD tac : tactic =
  W(fun gl -> if bk_at 0x333c gl then SP2S_FAIL_TAC else tac);;

(*** The end, from the back: n or the error -20 ***)

let SP2S_FINAL_TAC : tactic =
  X_GEN_TAC `s':armstate` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MEMSAFE_STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj(concl th) && is_eq(lhand(concl th)) &&
      lhs(lhand(concl th)) = `read X0 s'`)) THEN
    ASM_REWRITE_TAC[zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    SP_MEMSAFE_TAC];;

let SP2S_BACK_TAC : tactic =
  SP_INIT_FACTS_TAC THEN
  SP_GOON_TAC [`3 * q <= n`; `val(dst:int64) + n < 2 EXP 64`;
               `n < 2 EXP 28`] SP2S_FINAL_TAC BK2S_CORRECT sp_bk_alist;;

let SP2S_TAC : tactic =
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  BK2_BIGSTEP_TAC EN2_CORRECT [] THEN
  SP2S_GUARD
   (SP_ABBREV_TAC THEN SP_FACTS_TAC THEN SP2_IN_TAC 1 THEN
    SP2S_GUARD
     (SP2_IN_TAC 2 THEN
      SP2S_GUARD
       (SP2_IN_TAC 3 THEN
        SP2S_GUARD
         (SP2_IN_TAC 4 THEN SP2S_GUARD SP2S_BACK_TAC))));;

let SP2S_CORRECT = prove(sp2s_goal, SP2S_TAC);;

(* ------------------------------------------------------------------------- *)
(* The slow path for any block, with the result and the bytes out for a      *)
(* valid one (SP2ALL_CORRECT).                                               *)
(* ------------------------------------------------------------------------- *)

(*** The slow path for any block: the result n and the bytes out for a ***)
(*** valid block (SP2_CORRECT), and always n or an error within the   ***)
(*** regions (SP2S_CORRECT); a valid output is unique                 ***)

let HUF_STREAM_UNIQUE = prove
 (`!ws ml (st:byte list) o1 o2.
        huf_complete ws ml /\ LENGTH ws <= 256 /\
        huf_stream ws ml st o1 /\ huf_stream ws ml st o2 /\
        LENGTH o1 = LENGTH o2
        ==> o1 = o2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:num` o MATCH_MP HUF_STREAM_END) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                `o1:byte list`] HUF_STREAM_DECODE) THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                `o2:byte list`] HUF_STREAM_DECODE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o TRANS (SYM th))) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let HUF_STREAMS4_UNIQUE = prove
 (`!ws ml (blk:byte list) o1 o2.
        huf_complete ws ml /\ LENGTH ws <= 256 /\
        huf_streams4 T ws ml blk o1 /\ huf_streams4 T ws ml blk o2 /\
        LENGTH o1 = LENGTH o2
        ==> o1 = o2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_streams4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if concl th = `LENGTH(o1:byte list) = LENGTH(o2:byte list)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
    else NO_TAC) THEN
  ABBREV_TAC `n = LENGTH(o2:byte list)` THEN
  ABBREV_TAC `q = (n + 3) DIV 4` THEN
  MP_TAC(SPECL [`o1:byte list`; `q:num`; `n:num`] ZSTD_SUBLIST_SPLIT4) THEN
  MP_TAC(SPECL [`o2:byte list`; `q:num`; `n:num`] ZSTD_SUBLIST_SPLIT4) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_THEN(fun th' ->
    ONCE_REWRITE_TAC[th'] THEN GEN_REWRITE_TAC RAND_CONV [th])) THEN
  MATCH_MP_TAC(MESON[]
   `(a:byte list) = a' /\ b = b' /\ c = c' /\ d = d'
    ==> APPEND a (APPEND b (APPEND c d)) =
        APPEND a' (APPEND b' (APPEND c' d'))`) THEN
  let seg st =
    MATCH_MP_TAC HUF_STREAM_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; st] THEN
    ASM_REWRITE_TAC[LENGTH_ZSTD_SUBLIST] in
  REPEAT CONJ_TAC THENL
   [seg `zstd_sublist (blk:byte list) 6 (huf_jump blk 0)`;
    seg `zstd_sublist (blk:byte list) (6 + huf_jump blk 0) (huf_jump blk 1)`;
    seg `zstd_sublist (blk:byte list) (6 + huf_jump blk 0 + huf_jump blk 1)
                      (huf_jump blk 2)`;
    seg `zstd_sublist (blk:byte list)
           (6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2)
           (LENGTH blk -
            (6 + huf_jump blk 0 + huf_jump blk 1 + huf_jump blk 2))`]);;

let sp2all_post = with_memsafe sp2_rr sp2_wr (mk_abs(`s:armstate`,
 `read PC s = word(pc + 0x333c) /\
  read X25 s = v25 /\ read X26 s = v26 /\
  read X27 s = v27 /\ read X28 s = v28 /\
  (!out. LENGTH out = n /\ huf_streams4 T ws ml blk out
         ==> read X0 s = word n /\
             read (memory :> bytes(dst,n)) s = num_of_bytelist out) /\
  (read X0 s = word n \/ zstd_is_error(read X0 s))`));;

let sp2all_goal =
  let tm = mk_imp(list_mk_conj sp2s_hyps,
                  list_mk_icomb "ensures"
                    [`arm`; sp2_pre; sp2all_post; sp2_frame]) in
  let fvs = frees tm in
  list_mk_forall(filter (fun v -> mem v fvs) sp2_vars,tm);;

let SP2ALL_CORRECT = prove
 (sp2all_goal,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `?out:byte list. LENGTH out = n /\
                                 huf_streams4 T ws ml blk out` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `out0:byte list` STRIP_ASSUME_TAC) THEN
    MP_TAC(INST [`out0:byte list`,`out:byte list`] (SPEC_ALL SP2_CORRECT)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RS_ENSURES_WEAKEN THEN CONJ_TAC THEN
    X_GEN_TAC `s:armstate` THEN BETA_TAC THENL
     [SIMP_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `out:byte list` THEN STRIP_TAC THEN
      SUBGOAL_THEN `out:byte list = out0` SUBST1_TAC THENL
       [MATCH_MP_TAC HUF_STREAMS4_UNIQUE THEN
        MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `blk:byte list`] THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]];
    MP_TAC(SPEC_ALL SP2S_CORRECT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RS_ENSURES_WEAKEN THEN CONJ_TAC THEN
    X_GEN_TAC `s:armstate` THEN BETA_TAC THENL
     [SIMP_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* HUF_decompress1X2_usingDTable_internal(dst,dstSize,cSrc,cSrcSize,DTable)  *)
(* of zstd, at 0x2b30 in the image (as a copy specialized for its constant   *)
(* argument flags), which decodes the dstSize bytes of the single Huffman-   *)
(* coded stream at cSrc with the double-symbol decoding table DTable built   *)
(* by HUF_readDTableX2_wksp (HUF_DECOMPRESS1X2_USINGDTABLE_CORRECT). For a   *)
(* valid stream the result is dstSize, with the output at dst, and the       *)
(* result is always dstSize or an error code. As in the slow path of the     *)
(* four-stream decoding, the last symbol adds the bits of both symbols of a  *)
(* two-symbol entry to the bits used (up to 64), so the end check also       *)
(* passes when the code of the second symbol is cut off at the start of the  *)
(* stream: the code accepts some streams that are not valid, and for those   *)
(* the theorem says only that the result is dstSize or an error code. The    *)
(* output must not be at address 0, for the comparisons with its end less 9. *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode4x2_gcc12_O2.ml";;

(*** HUF_decompress1X2_usingDTable_internal at 0x2b30 (a copy of the ***)
(*** function specialized for its constant flags): the code, and its ***)
(*** simulation as by ZSTD_STEP_TAC                                  ***)

let D12_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc
  [0x2b30,0x30b8];;

let D12_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC D12_EXEC [n] THEN ZSTD_SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                  WORD_CMP_64_SFLAGS) THEN
                TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let D12_STEPS_TAC ns = MAP_EVERY D12_STEP_TAC ns;;

let D12_SIM_UNTIL_TAC stops =
  let num_of_state s =
    let n = fst(dest_var s) in
    int_of_string(String.sub n 1 (String.length n - 1)) in
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k n (asl,w as gl) =
    let pc = current_pc gl in
    if pc = `returnaddress:int64` || mem pc stops then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "D12_SIM_UNTIL_TAC"
    else (D12_STEP_TAC n THEN run (k - 1) (n + 1)) gl in
  fun (asl,w as gl) -> run 80 (num_of_state(rand w) + 1) gl;;

let D12_RUN_TAC = D12_SIM_UNTIL_TAC [];;

(* ------------------------------------------------------------------------- *)
(* The state of the decoding, as for the single-symbol decoding of           *)
(* zstd_huf_decode1x1_gcc12_O2.ml. The stream st, of LENGTH st bytes at src, *)
(* is read backwards from the position r of the bit above its last 1 bit,    *)
(* and huf_decode ws ml st r jj gives the first jj bytes decoded, the        *)
(* position after them and whether no code needed more bits than were left.  *)
(* The bit container in x7 holds the 8 bytes of st from ofs (or all of a     *)
(* shorter stream, with ofs = 0), src + ofs being the pointer in x3, and bc  *)
(* in w5 of its bits are used; the jj bytes decoded are at dst, which x6     *)
(* points after, and the double-symbol table of 2^tl entries of 4 bytes is   *)
(* at dt = DTable + 4 in x0, its entry for a state of tl bits giving one or  *)
(* two symbols, their bits and their number. The state is good when the      *)
(* decoding of the jj bytes is ok at the position of the container, 8 * ofs  *)
(* + 64 - bc, with the bytes at dst.                                         *)
(*                                                                           *)
(* The main loops and the loop of one lookup look up the table only after a  *)
(* reload, with at least 57 bits in the container (or the start of the       *)
(* stream in it), so they keep the state good for any stream. Once at the    *)
(* start of the stream, the loop without reloads and the last symbol can use *)
(* more bits than are left; there the state is good if the decoding of the n *)
(* bytes is valid, and the bits used are only bounded otherwise.             *)
(*                                                                           *)
(* The pieces, each to the return with the result as huf_x2_result, are at:  *)
(*                                                                           *)
(*   0x2e58  D12_LAST, the last symbol (at most one byte left) and the end   *)
(*           check                                                           *)
(*   0x2e28  D12_L0, the loop of one lookup without reloads                  *)
(*   0x2e14  D12_L0E, its head                                               *)
(*   0x2ddc  D12_L1, the loop of a reload and one lookup                     *)
(*   0x2d74  D12_MID, after the main loop                                    *)
(*   0x2be8  D12_B5 and 0x2cbc D12_L5, the body of 5 lookups for tl <= 11    *)
(*           and its loop                                                    *)
(*   0x2ee0  D12_B4 and 0x2f8c D12_L4, the body of 4 lookups for tl = 12     *)
(*           and its loop                                                    *)
(*   0x2d38  D12_SINGLE, the reload for at most 7 bytes                      *)
(*                                                                           *)
(* Each has the conjunct puff_memsafe e rr wr s, for the trace e at the      *)
(* entry: the loads are from the stream, the table and the byte DTable[2]    *)
(* (read at the entry), and the stores to the n bytes at dst.                *)
(* ------------------------------------------------------------------------- *)

(*** The pieces: the stream st of LENGTH st bytes at src, read from the ***)
(*** position r of its last 1 bit, its n bytes decoded to dst, with the ***)
(*** double-symbol table of 2^tl entries of 4 bytes at dt = DTable + 4  ***)
(*** and tl in DTable[2]                                                ***)

let d12_rr =
 `[src,LENGTH(st:byte list); word_add dtable (word 2),1;
   dt,4 * 2 EXP tl]:(int64#num)list`
and d12_wr = `[dst,n]:(int64#num)list`;;

let d12_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
  huf_complete ws ml /\ LENGTH(ws:num list) <= 256 /\
  1 <= ml /\ ml <= tl /\ tl <= 12 /\ n < 2 EXP 28 /\
  8 <= val(src:int64) /\ val src + LENGTH(st:byte list) + 8 < 2 EXP 64 /\
  LENGTH st < 2 EXP 60 /\ val(dst:int64) + n < 2 EXP 64 /\
  ~(val dst = 0) /\
  nonoverlapping (dst,n) (src,LENGTH st) /\
  nonoverlapping (dst,n) (dt:int64,4 * 2 EXP tl) /\
  nonoverlapping (dst,n) (word pc,32000)`;;

let d12_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [memory :> bytes(dst,n)]`;;

let d12_vars =
 [`pc:num`; `returnaddress:int64`; `dst:int64`; `n:num`; `src:int64`;
  `st:byte list`; `dtable:int64`; `dt:int64`; `ws:num list`; `ml:num`;
  `tl:num`; `r:num`; `e:uarch_event list`];;

let mk_d12_goal extra pre post =
  let tm = mk_imp(d12_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; d12_frame]) in
  let vs = d12_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_d12_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** At the return: n or an error code, and n with the bytes decoded ***)
(*** when the decoding of the n bytes uses exactly the bits from r   ***)
(*** (as a constant, which the simulation does not rewrite)          ***)

let huf_x2_result = new_definition
 `huf_x2_result ws ml (st:byte list) r n (x0:int64) mem <=>
    (x0 = word n \/ zstd_is_error x0) /\
    (SND(SND(huf_decode ws ml st r n)) /\
     FST(SND(huf_decode ws ml st r n)) = 0
     ==> x0 = word n /\
         mem = num_of_bytelist(FST(huf_decode ws ml st r n)))`;;

let d12_valid =
 `SND(SND(huf_decode ws ml (st:byte list) r n)) /\
  FST(SND(huf_decode ws ml st r n)) = 0`;;

let d12_post = with_memsafe d12_rr d12_wr `\s.
  read PC s = returnaddress /\
  huf_x2_result ws ml (st:byte list) r n (read X0 s)
                (read (memory :> bytes(dst,n)) s)`;;

(*** The facts that hold all through, and the state after jj bytes: the ***)
(*** output pointer, the container (the 8 bytes from ofs, or the whole  ***)
(*** stream from ofs = 0) and bc bits of it used                        ***)

let d12_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read X30 s = returnaddress /\ read X0 s = dt /\ read X1 s = word n /\
  read X2 s = src /\ read X9 s = word tl /\
  read X10 s = word_add dst (word n) /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(dt,4 * 2 EXP tl)) s =
  num_of_bytelist(huf_dtable2 ws ml tl)`;;

let d12_win = `word((num_of_bytelist (st:byte list) DIV 2 EXP (8 * ofs)) MOD
                    2 EXP 64):int64`;;

let d12_state = list_mk_conj
 [`read X6 s = word_add dst (word jj) /\
   read X3 s = word_add src (word ofs)`;
  mk_eq(`read X7 s`,d12_win);
  `read X5 s = word bc /\ (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
   jj <= n`];;

(*** Good: the decoding of jj bytes from r ok, at the position of the ***)
(*** container, with the bytes at dst                                 ***)

let d12_good =
 `SND(SND(huf_decode ws ml st r jj)) /\
  FST(SND(huf_decode ws ml st r jj)) = 8 * ofs + 64 - bc /\ bc <= 64 /\
  read (memory :> bytes(dst,jj)) s =
  num_of_bytelist(FST(huf_decode ws ml (st:byte list) r jj))`;;

(* ------------------------------------------------------------------------- *)
(* The lookups of the table, the last symbol and the end check. The index of *)
(* a lookup is that of the specification when the container still holds tl   *)
(* bits or the start of the stream (D12_INDEXW), and otherwise any index     *)
(* below 2^tl (D12_INDEX_ANY). The bytes of an entry, read after the store   *)
(* of its symbols, are read again (the facts about them do not survive the   *)
(* store, the table having 2^tl entries). An assumption ofs = 0 is kept as   *)
(* ofs <= 0, as the simulation would substitute it in the values that it     *)
(* computes.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*** The lookups: the index from the container when its bits are those ***)
(*** of the specification (as ML2_INDEX'), or any index below 2^tl     ***)

let D12_INDEXW = prove
 (`!(st:byte list) ofs bc tl.
     bc < 64 /\ 1 <= tl /\ tl <= 12 /\ (tl + bc <= 64 \/ ofs = 0)
     ==> word_shl (word_jushr
           (word (2 EXP bc * (num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                  18446744073709551616):int64) (word (64 - tl))) 2 =
         word (4 * zstd_back st (8 * ofs + 64 - bc) tl)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ML2_INDEX' THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let D12_INDEX_ANY = prove
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
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
                  ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
  SUBGOAL_THEN `64 - tl + tl = 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]);;

(*** The start of a piece, with 1 <= tl ***)

let D12_INTRO_TAC : tactic =
  ZSTD_INTRO_TAC THEN
  SUBGOAL_THEN `1 <= tl` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC];;

(*** The shift 64 - tl of the lookups, from -tl masked or not ***)

let D12_SHIFT_TAC : tactic =
  W(fun (asl,w) ->
    let h = CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`) in
    let th1 = MP (SPEC `tl:num` HUF_SHIFT_WORD) h
    and th2 = GEN `y:int64`
                (MP (SPECL [`y:int64`; `tl:num`] T2_JUSHR_NEG) h) in
    FA_STATE_REWRITE_TAC[th1; th2]);;

(*** The arithmetic of the pieces: the facts about the variables of the ***)
(*** stream only                                                        ***)

let D12_ARITH_TAC =
  FA_ARITHV_TAC
   ([`ofs:num`; `bc:num`; `jj:num`; `n:num`; `m:num`; `ml:num`; `tl:num`;
     `ws:num list`; `st:byte list`; `r:num`] @
    map (fun i -> mk_var("j"^string_of_int i,`:num`)) (1--5) @
    map (fun i -> mk_var("b"^string_of_int i,`:num`)) (1--5));;

(*** Arithmetic from the atomic facts first, for each conjunct and each ***)
(*** disjunct of the goal                                               ***)

let D12_SARITH_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [SIMPLE_ARITH_TAC; DISJ1_TAC THEN SIMPLE_ARITH_TAC;
         DISJ2_TAC THEN SIMPLE_ARITH_TAC; D12_ARITH_TAC];;

(*** A lookup at a good state at position pos (8 * ofs + 64 - bc), under ***)
(*** the condition cnd of the index lemmas idx: the index as the tl bits ***)
(*** below pos, the entry e of the table with its bytes and bounds       ***)

let D12_LOOKUP_GENA_TAC (arith:tactic) (s:term) (pos:term) (cnd:term)
                        (idx:thm list) =
  let x = list_mk_icomb "zstd_back" [`st:byte list`; pos; `tl:num`] in
  SUBGOAL_THEN cnd ASSUME_TAC THENL [arith; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = cnd
    then FA_STATE_REWRITE_TAC (map (fun l -> MATCH_MP l th) idx)
    else NO_TAC) THEN
  MP_TAC(ISPECL [`st:byte list`; pos; `tl:num`] ZSTD_BACK_BOUND) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `dt:int64`; x; s]
     HUF_DTABLE2_READ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `dt:int64`; x; s]
     HUF_DTABLE2_READ16) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; x] HUF_DENTRY2_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th) THEN
      MAP_EVERY ASSUME_TAC (CONJUNCTS
        (MATCH_MP (ARITH_RULE `!a. (a = 1 \/ a = 2) ==> 1 <= a /\ a <= 2`)
                  (last(CONJUNCTS th)))))];;

let D12_LOOKUP_GEN_TAC = D12_LOOKUP_GENA_TAC D12_SARITH_TAC;;

let D12_LOOKUPA_TAC (arith:tactic) (s:term) (ofs:term) (bc:term) =
  let pos = subst [ofs,`ofs:num`; bc,`bc:num`] `8 * ofs + 64 - bc` in
  let cnd = subst [ofs,`ofs:num`; bc,`bc:num`]
     `bc < 64 /\ 1 <= tl /\ tl <= 12 /\ (tl + bc <= 64 \/ ofs = 0)` in
  D12_LOOKUP_GENA_TAC arith s pos cnd
   [SPECL [`st:byte list`; ofs; bc; `tl:num`] D12_INDEXW];;

let D12_LOOKUP_TAC = D12_LOOKUPA_TAC D12_SARITH_TAC;;

(*** A lookup with any index (once the bits ran out): the index below ***)
(*** 2^tl, as x, and the entry of the table with its bytes            ***)

let D12_LOOKUP_ANY_TAC (s:term) : tactic =
  W(fun (asl,w) ->
    let pat = `word_shl (word_jushr y (word (64 - tl))) 2:int64` in
    let t = tryfind (fun (_,th) ->
      find_term (fun u -> can (term_match [`tl:num`] pat) u) (concl th)) asl in
    let _,tmi,_ = term_match [`tl:num`] pat t in
    let y = rev_assoc `y:int64` tmi in
    let th = MP (ISPECL [y; `tl:num`] D12_INDEX_ANY)
                (CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`)) in
    let vt = lhand(concl(CONJUNCT2 th)) in
    FA_STATE_REWRITE_TAC[CONJUNCT1 th] THEN
    ASSUME_TAC(CONJUNCT2 th) THEN
    ABBREV_TAC (mk_eq(`x:num`,vt))) THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `dt:int64`; `x:num`; s]
     HUF_DTABLE2_READ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `dt:int64`; `x:num`; s]
     HUF_DTABLE2_READ16) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `x:num`]
    HUF_DENTRY2_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th) THEN
      MAP_EVERY ASSUME_TAC (CONJUNCTS
        (MATCH_MP (ARITH_RULE `!a. (a = 1 \/ a = 2) ==> 1 <= a /\ a <= 2`)
                  (last(CONJUNCTS th)))))];;

(*** 0x2e58, at most one byte left: the end check, or the last symbol  ***)
(*** (the first of the entry) and the bits used, of both symbols of an ***)
(*** entry of two (up to 64), then the end check: good if the decoding ***)
(*** of the n bytes is valid                                           ***)

let d12_lastbody = list_mk_conj
 [`read PC s = word(pc + 0x2e58)`; d12_common; d12_state;
  `n <= jj + 1`;
  mk_imp(d12_valid,mk_conj(d12_good,`ofs = 0 \/ tl + bc <= 64`));
  `bc <= 64 + 12 * jj`];;

let d12_last = with_memsafe d12_rr d12_wr
  (mk_abs(`s:armstate`,d12_lastbody));;

let d12_last_goal = mk_d12_goal [`jj:num`; `ofs:num`; `bc:num`]
  d12_last d12_post;;

(*** The entry read again after the store of a symbol (the facts of its ***)
(*** bytes do not survive the store, the table having 2^tl entries)     ***)

let D12_REREAD_TAC (x:term) : tactic =
  W(fun (asl,w) ->
    MP_TAC(ISPECL [`ws:num list`; `ml:num`; `tl:num`; `dt:int64`; x; rand w]
       HUF_DTABLE2_READ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]);;

(*** The bytes of the entry for the index x as numbers ***)

let d12_entry (x:term) =
  list_mk_icomb "huf_dentry2" [`ws:num list`; `ml:num`; `tl:num`; x];;

let d12_el k (x:term) =
  mk_icomb(mk_icomb(`EL:num->num list->num`,mk_small_numeral k),d12_entry x);;

let d12_len12 (x:term) =
  mk_disj(mk_eq(d12_el 3 x,`1`),mk_eq(d12_el 3 x,`2`));;

let D12_VALA_TAC (arith:tactic) (x:term) : tactic =
  let vth k =
    mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,d12_el k x)),
          d12_el k x) in
  MAP_EVERY (fun k ->
    SUBGOAL_THEN (vth k)
     (fun th -> FA_STATE_REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      (FIRST_ASSUM ACCEPT_TAC ORELSE arith);
      ALL_TAC]) [0;1;2;3];;

let D12_VAL_TAC = D12_VALA_TAC D12_SARITH_TAC;;

(*** Simulation up to the return, one of the given addresses or a branch ***)
(*** not decided, then the cases of its condition, to the return         ***)

let D12_SIM_COND_TAC stops =
  let num_of_state s =
    let n = fst(dest_var s) in
    int_of_string(String.sub n 1 (String.length n - 1)) in
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k n (asl,w as gl) =
    let pc = current_pc gl in
    if pc = `returnaddress:int64` || mem pc stops || is_cond pc
    then ALL_TAC gl
    else if k = 0 then failwith "D12_SIM_COND_TAC"
    else (D12_STEP_TAC n THEN run (k - 1) (n + 1)) gl in
  fun (asl,w as gl) -> run 80 (num_of_state(rand w) + 1) gl;;

let D12_CASE_BRANCH_TAC (c:term) : tactic =
  let pc_cond th =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),r)
        -> is_cond r
    | _ -> false in
  ASM_CASES_TAC c THEN
  FIRST_ASSUM(fun th ->
    if concl th = c || concl th = mk_neg c then
      RULE_ASSUM_TAC(fun th' ->
        if pc_cond th' then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

let rec D12_SPLIT_TAC (fin:tactic) : tactic =
  fun gl ->
   (D12_SIM_COND_TAC [] THEN
    W(fun gl ->
      let pc = current_pc gl in
      if pc = `returnaddress:int64` then fin
      else if is_cond pc then
        D12_CASE_BRANCH_TAC (lhand(rator pc)) THEN D12_SPLIT_TAC fin
      else failwith "D12_SPLIT_TAC")) gl;;

(*** At the return: for a decoding not valid, n or an error; for a valid ***)
(*** one, n and the bytes                                                ***)

let D12_NOTVALID_FIN_TAC : tactic =
  PUFF_FINAL_TAC THEN
  ASM_REWRITE_TAC[huf_x2_result; zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV;;

let D12_VALID_FIN_TAC : tactic =
  PUFF_FINAL_TAC THEN REWRITE_TAC[huf_x2_result] THEN ASM_REWRITE_TAC[];;

(*** The facts of a valid decoding from the implication of the invariant ***)

let D12_VALID_FACTS_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    if is_imp(concl th) && lhand(concl th) = d12_valid
    then MP_TAC(MP th (ASSUME d12_valid)) else NO_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASSUME_TAC(CONJUNCT1(ASSUME d12_valid)) THEN
  ASSUME_TAC(CONJUNCT2(ASSUME d12_valid));;

(*** 0x2e58 for a valid decoding: the n bytes done, at the start of ***)
(*** the stream with all 64 bits used, or the last symbol with the  ***)
(*** facts of ML2_LAST                                              ***)

let D12_LAST_N_TAC : tactic =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `jj:num = n`)) THEN
  SUBGOAL_THEN `ofs = 0 /\ bc = 64` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  D12_RUN_TAC THEN D12_VALID_FIN_TAC;;

(*** The bytes after the store of the first symbol of the entry for x ***)

let D12_SNOC_TAC (x:term) : tactic =
  W(fun (asl,w) ->
    MP_TAC(ISPECL
     [`dst:int64`; `FST(huf_decode ws ml (st:byte list) r jj)`;
      mk_comb(`word:num->byte`,d12_el 0 x); rand(lhs w)]
     READ_MEMORY_BYTELIST_SNOC)) THEN
  ASM_REWRITE_TAC[HUF_DECODE_LENGTH];;

let D12_LAST_V_TAC : tactic =
  let x0 = `zstd_back (st:byte list) (8 * ofs + 64 - bc) tl` in
  SUBGOAL_THEN `n = jj + 1` SUBST_ALL_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                `jj + 1`; `jj:num`] HUF_DECODE_ROOM2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `bc < 64` ASSUME_TAC THENL [D12_ARITH_TAC; ALL_TAC] THEN
  D12_STEPS_TAC (1--6) THEN D12_SHIFT_TAC THEN
  D12_LOOKUP_TAC `s6:armstate` `ofs:num` `bc:num` THEN
  D12_STEPS_TAC (7--9) THEN D12_REREAD_TAC x0 THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; `jj:num`;
                `ofs:num`; `bc:num`; `tl:num`] ML2_LAST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC (mk_eq(`x:num`,x0)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ofs = 0`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  D12_VAL_TAC `x:num` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    concl th = d12_len12 `x:num`)) THEN
  FIRST_X_ASSUM(fun th -> if is_cond(concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  D12_RUN_TAC THEN D12_VALID_FIN_TAC THEN D12_SNOC_TAC `x:num`;;

(*** 0x2e58 for a decoding not valid: any index, n or an error ***)

let D12_LAST_NV_TAC : tactic =
  D12_STEPS_TAC (1--6) THEN D12_SHIFT_TAC THEN
  D12_LOOKUP_ANY_TAC `s6:armstate` THEN
  D12_STEPS_TAC (7--9) THEN D12_REREAD_TAC `x:num` THEN
  D12_VAL_TAC `x:num` THEN D12_SPLIT_TAC D12_NOTVALID_FIN_TAC;;

let D12_LAST_TAC : tactic =
  D12_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC d12_valid THENL
   [D12_VALID_FACTS_TAC THEN ASM_CASES_TAC `jj:num = n` THENL
     [D12_LAST_N_TAC; D12_LAST_V_TAC];
    ASM_CASES_TAC `jj:num = n` THENL
     [D12_SPLIT_TAC D12_NOTVALID_FIN_TAC; D12_LAST_NV_TAC]];;

let D12_LAST = prove(d12_last_goal, D12_LAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop without reloads and its head, and the loop of a reload and one   *)
(* lookup: the decoding after a lookup of a good state by ML2_STEP when the  *)
(* decoding of the n bytes is valid, and by HUF_DECODE_X2_STEP for any       *)
(* stream when the bits of the entry are in the container.                   *)
(* ------------------------------------------------------------------------- *)

(*** 0x2e28, the loop of one lookup without reloads while two bytes are ***)
(*** left, for the measure m = n - jj, the container at ofs fixed: good ***)
(*** at the start of the stream (ofs = 0) if the decoding is valid      ***)

let d12_l0body = list_mk_conj
 [`read PC s = word(pc + 0x2e28)`; d12_common; d12_state;
  `read X12 s = word(64 - tl) /\ read X13 s = word_add dst (word(n - 2)) /\
   jj + 2 <= n`;
  mk_imp(d12_valid,mk_conj(d12_good,`ofs = 0`));
  `bc <= 64 + 12 * jj`];;

let d12_l0inv = with_memsafe d12_rr d12_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `bc:num`],
    mk_conj(`m = n - jj`,d12_l0body))));;

let d12_l0_goal = mk_d12_goal [`ofs:num`]
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(d12_l0inv,[`m:num`; `s:armstate`]))))
  d12_post;;

(*** The decoding after a lookup of a good state after jj bytes at ofs ***)
(*** with bc bits used, two bytes or more left (ML2_STEP), and the     ***)
(*** store of the symbols merged into the bytes before                 ***)

let D12_STEP_FACTS_TAC (ofs:term) (bc:term) : tactic =
  let pos = subst [ofs,`ofs:num`; bc,`bc:num`] `8 * ofs + 64 - bc` in
  let x = list_mk_icomb "zstd_back" [`st:byte list`; pos; `tl:num`] in
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; `n:num`;
                `jj:num`; ofs; bc; `tl:num`] ML2_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN D12_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  W(fun (asl,w) ->
    MP_TAC(ISPECL [`dst:int64`;
                   `FST(huf_decode ws ml (st:byte list) r jj)`;
                   d12_el 0 x; d12_el 1 x; d12_el 3 x; rand w]
      READ_MEMORY_X2_STORE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HUF_DECODE_LENGTH];
    REWRITE_TAC[HUF_DECODE_LENGTH] THEN DISCH_TAC];;

(*** An assumption ofs = 0 as ofs <= 0, which the simulation does not ***)
(*** substitute in the values it computes                             ***)

let D12_OFS0_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    if concl th = `ofs = 0`
    then ASSUME_TAC(MP (ARITH_RULE `ofs = 0 ==> ofs <= 0`) th)
    else NO_TAC);;

(*** The values of dst + k for the comparisons of the output pointer ***)

let D12_OPVAL_TAC ks =
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`dst:int64`; k] VAL_WORD_ADD_NOWRAP) THEN
    ANTS_TAC THENL
     [MP_TAC(ASSUME `val(dst:int64) + n < 2 EXP 64`) THEN D12_ARITH_TAC;
      DISCH_TAC]) ks;;

(*** After a lookup of the entry for x: the output pointer and the bits ***)
(*** used as words of numbers                                           ***)

let D12_AFTER_TAC (x:term) : tactic =
  D12_VAL_TAC x THEN FA_STATE_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];;

(*** On to the next iteration of a loop with jj' bytes and bc' bits used, ***)
(*** ofs fixed: the measure and the conjuncts of the invariant            ***)

let D12_NEXT_TAC (jj':term) (bc':term) : tactic =
  DISJ1_TAC THEN EXISTS_TAC (mk_binop `(-):num->num->num` `n:num` jj') THEN
  CONJ_TAC THENL [D12_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [jj'; bc'] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY D12_ARITH_TAC THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      D12_ARITH_TAC);;

(*** Going on with a later piece th from the state, as the second ***)
(*** disjunct of the postcondition of a loop if loop is set       ***)

let D12_GOON_TAC (loop:bool) th insts : tactic =
  let wtac =
    if loop then GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN
                 FIRST_ASSUM ACCEPT_TAC
    else GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC in
  ZSTD_CONTINUE_WITH_TAC wtac th insts THEN
  MEMSAFE_ELIM_TAC THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY D12_ARITH_TAC THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      D12_ARITH_TAC);;

(*** One iteration: the lookup (good for a valid decoding, else any ***)
(*** index), then on to the next iteration or the last symbol       ***)

let D12_L0_ITER_TAC (valid:bool) : tactic =
  let x0 = `zstd_back (st:byte list) (8 * ofs + 64 - bc) tl` in
  let x = if valid then x0 else `x:num` in
  let jj' = mk_binop `(+):num->num->num` `jj:num` (d12_el 3 x)
  and bc' = mk_binop `(+):num->num->num` `bc:num` (d12_el 2 x) in
  (if valid then
     D12_VALID_FACTS_TAC THEN D12_OFS0_TAC THEN
     MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                   `n:num`; `jj:num`] HUF_DECODE_ROOM2) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN D12_ARITH_TAC; DISCH_TAC] THEN
     SUBGOAL_THEN `bc < 64` ASSUME_TAC THENL [D12_ARITH_TAC; ALL_TAC] THEN
     D12_STEPS_TAC (1--3) THEN
     D12_LOOKUP_TAC `s3:armstate` `ofs:num` `bc:num`
   else
     D12_STEPS_TAC (1--3) THEN D12_LOOKUP_ANY_TAC `s3:armstate`) THEN
  D12_STEPS_TAC (4--6) THEN D12_REREAD_TAC x THEN
  D12_STEPS_TAC (7--10) THEN
  (if valid then D12_STEP_FACTS_TAC `ofs:num` `bc:num` else ALL_TAC) THEN
  D12_AFTER_TAC x THEN D12_OPVAL_TAC [jj'; `n - 2`] THEN
  ASM_CASES_TAC (mk_binop `(<=):num->num->bool`
                   (mk_binop `(+):num->num->num` jj' `2`) `n:num`) THEN
  D12_STEPS_TAC (11--12) THENL
   [PUFF_FINAL_TAC THEN D12_NEXT_TAC jj' bc';
    D12_GOON_TAC true D12_LAST [jj',`jj:num`; bc',`bc:num`]];;

let D12_L0_TAC : tactic =
  D12_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `bc:num` THEN
  PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC d12_valid THENL
   [D12_L0_ITER_TAC true; D12_L0_ITER_TAC false];;

let D12_L0 = prove(d12_l0_goal, D12_L0_TAC);;

(*** 0x2e14, the head of that loop: the loop if two bytes are left, else ***)
(*** the last symbol                                                     ***)

let d12_l0e = with_memsafe d12_rr d12_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x2e14)`; d12_common; d12_state;
  `read X13 s = word_add dst (word(n - 2)) /\ 2 <= n`;
  mk_imp(d12_valid,mk_conj(d12_good,
    `ofs = 0 \/ n < jj + 2 /\ tl + bc <= 64`));
  `bc <= 64 + 12 * jj`]));;

let d12_l0e_goal = mk_d12_goal [`jj:num`; `ofs:num`; `bc:num`]
  d12_l0e d12_post;;

let D12_L0E_TAC : tactic =
  D12_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  D12_OPVAL_TAC [`jj:num`; `n - 2`] THEN
  ASM_CASES_TAC `jj + 2 <= n` THENL
   [D12_STEPS_TAC (1--5) THEN D12_SHIFT_TAC THEN
    D12_GOON_TAC false D12_L0 [] THEN
    EXISTS_TAC `n - jj:num` THEN MAP_EVERY EXISTS_TAC [`jj:num`; `bc:num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY D12_ARITH_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_imp(concl th) && lhand(concl th) = d12_valid)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    D12_ARITH_TAC;
    D12_STEPS_TAC (1--2) THEN D12_GOON_TAC false D12_LAST [] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_imp(concl th) && lhand(concl th) = d12_valid)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    D12_ARITH_TAC];;

let D12_L0E = prove(d12_l0e_goal, D12_L0E_TAC);;

(*** 0x2ddc, the loop of a reload and one lookup while two bytes are    ***)
(*** left, for the measure m = n - jj; good all through (after a reload ***)
(*** at least 57 bits are left), the bits used at most 7 after a        ***)
(*** reload, 19 after a lookup, unless at the start of the stream       ***)

let d12_l1body = list_mk_conj
 [`read PC s = word(pc + 0x2ddc)`; d12_common; d12_state;
  `read X11 s = word_add src (word 8) /\
   read X13 s = word_add dst (word(n - 2)) /\ read X14 s = word(64 - tl) /\
   2 <= n`;
  d12_good; `ofs = 0 \/ bc <= 19`];;

let d12_l1inv = with_memsafe d12_rr d12_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],
    mk_conj(`m = n - jj`,d12_l1body))));;

let d12_l1_goal = mk_d12_goal []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(d12_l1inv,[`m:num`; `s:armstate`]))))
  d12_post;;

(*** The container after a reload to ofs' ***)

let D12_SLICE_TAC ofs' : tactic =
  W(fun (asl,w) ->
    MP_TAC(SPECL [`src:int64`; `LENGTH(st:byte list)`;
                  `num_of_bytelist(st:byte list)`; ofs'; rand w]
       READ_MEMORY_BYTES64_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN D12_ARITH_TAC;
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC]);;

(*** The position of the decoding as pos after a reload (the fact with ***)
(*** the old one replaced)                                             ***)

let D12_POS_TAC pos : tactic =
  let t = mk_eq(`FST(SND(huf_decode ws ml (st:byte list) r jj))`,pos) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && lhs c = lhs t && not(c = t)
      then REWRITE_TAC[th] else NO_TAC) THEN
    D12_ARITH_TAC;
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && lhs c = lhs t && not(c = t)
      then ALL_TAC else NO_TAC)];;

(*** The bits used after a partial reload, bc MOD 8 ***)

let D12_MOD8_TAC : tactic =
  SUBGOAL_THEN `bc - 8 * bc DIV 8 = bc MOD 8`
    (fun th -> FA_STATE_REWRITE_TAC[th]) THENL
   [D12_ARITH_TAC; ALL_TAC];;

(*** Going on with a piece th with the instantiation insts, the forms ***)
(*** of its precondition for ofs = 0 reduced                          ***)

let D12_GOON0_TAC (loop:bool) th insts : tactic =
  let wtac =
    if loop then GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN
                 FIRST_ASSUM ACCEPT_TAC
    else GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC in
  ZSTD_CONTINUE_WITH_TAC wtac th insts THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY D12_ARITH_TAC THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      D12_ARITH_TAC);;

(*** The decoding after a lookup of a good state after jj bytes at ofs ***)
(*** with bc bits used, the bits of the entry in the container (any    ***)
(*** stream: HUF_DECODE_X2_STEP), and the store of the symbols merged  ***)
(*** into the bytes before                                             ***)

let D12_GSTEP_FACTS_TAC (ofs:term) (bc:term) : tactic =
  let pos = subst [ofs,`ofs:num`; bc,`bc:num`] `8 * ofs + 64 - bc` in
  let x = list_mk_icomb "zstd_back" [`st:byte list`; pos; `tl:num`] in
  let jj' = mk_binop `(+):num->num->num` `jj:num` (d12_el 3 x) in
  let okt = list_mk_icomb "huf_decode"
              [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; jj'] in
  let ok = mk_icomb(`SND:num#bool->bool`,
                    mk_icomb(`SND:byte list#num#bool->num#bool`,okt)) in
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `st:byte list`; `r:num`;
                `jj:num`] HUF_DECODE_X2_STEP) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN ok ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN D12_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    MP_TAC(ISPECL [`dst:int64`;
                   `FST(huf_decode ws ml (st:byte list) r jj)`;
                   d12_el 0 x; d12_el 1 x; d12_el 3 x; rand w]
      READ_MEMORY_X2_STORE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HUF_DECODE_LENGTH];
    REWRITE_TAC[HUF_DECODE_LENGTH] THEN DISCH_TAC];;

(*** After a reload to ofs - bc DIV 8 with bc MOD 8 bits used, two bytes ***)
(*** left: the lookup, on to the next iteration at 0x2ddc                ***)

let D12_L1_LOOKUP_TAC : tactic =
  let ofs' = `ofs - bc DIV 8` and bc' = `bc MOD 8` in
  let x = `zstd_back (st:byte list) (8 * (ofs - bc DIV 8) + 64 - bc MOD 8)
                     tl` in
  let jj' = mk_binop `(+):num->num->num` `jj:num` (d12_el 3 x)
  and bc'' = mk_binop `(+):num->num->num` bc' (d12_el 2 x) in
  D12_POS_TAC (subst [ofs',`ofs':num`; bc',`bc':num`] `8 * ofs' + 64 - bc'`)
  THEN D12_SIM_UNTIL_TAC [0x2db8] THEN
  W(fun (_,w) -> D12_LOOKUP_TAC (rand w) ofs' bc') THEN
  D12_SIM_UNTIL_TAC [0x2dc4] THEN D12_REREAD_TAC x THEN
  D12_SIM_UNTIL_TAC [0x2ddc] THEN D12_GSTEP_FACTS_TAC ofs' bc' THEN
  D12_AFTER_TAC x THEN PUFF_FINAL_TAC THEN
  DISJ1_TAC THEN EXISTS_TAC (mk_binop `(-):num->num->num` `n:num` jj') THEN
  CONJ_TAC THENL [D12_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [jj'; ofs'; bc''] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN D12_ARITH_TAC;;

(*** After a full reload (normal, or partial): the lookup if two bytes ***)
(*** are left, else the head of the loop without reloads               ***)

let D12_BIG_TAC : tactic =
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC];;

let D12_L1_RELOADED_TAC (partial:bool) : tactic =
  let fix = if partial then D12_MOD8_TAC else ALL_TAC in
  D12_BIG_TAC THEN D12_SLICE_TAC `ofs - bc DIV 8` THEN
  ASM_CASES_TAC `jj + 2 <= n` THENL
   [D12_SIM_UNTIL_TAC [0x2db0] THEN fix THEN D12_L1_LOOKUP_TAC;
    D12_SIM_UNTIL_TAC [0x2e14] THEN fix THEN
    D12_GOON_TAC true D12_L0E
      [`ofs - bc DIV 8`,`ofs:num`; `bc MOD 8`,`bc:num`]];;

(*** After a reload clipped at the start of the stream: the head of the ***)
(*** loop without reloads                                               ***)

let D12_L1_CLIPPED_TAC : tactic =
  D12_BIG_TAC THEN D12_SLICE_TAC `0` THEN D12_SIM_UNTIL_TAC [0x2e14] THEN
  D12_GOON0_TAC true D12_L0E [`0`,`ofs:num`; `bc - 8 * ofs`,`bc:num`];;

let D12_L1_TAC : tactic =
  D12_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  D12_OPVAL_TAC [`jj:num`; `n - 2`] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [D12_L1_RELOADED_TAC false;
    ASM_CASES_TAC `ofs = 0` THENL
     [D12_OFS0_TAC THEN D12_SIM_UNTIL_TAC [0x2e14] THEN
      D12_GOON_TAC true D12_L0E [];
      ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
       [D12_L1_RELOADED_TAC true; D12_L1_CLIPPED_TAC]]];;

let D12_L1 = prove(d12_l1_goal, D12_L1_TAC);;

(*** Going on with a later piece th with the instantiation insts and the ***)
(*** witnesses ws of the existentials of its precondition                ***)

let D12_GOON_EX_TAC (loop:bool) th insts (ws:term list) : tactic =
  let wtac =
    if loop then GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN
                 FIRST_ASSUM ACCEPT_TAC
    else GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC in
  ZSTD_CONTINUE_WITH_TAC wtac th insts THEN
  MEMSAFE_ELIM_TAC THEN MAP_EVERY EXISTS_TAC ws THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY D12_ARITH_TAC THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      D12_ARITH_TAC);;

(*** 0x2d74, after the main loop (or the reload for at most 7 bytes) ***)
(*** with n - jj bytes left in x8: the last symbol if at most one is ***)
(*** left, else the loop of one lookup                               ***)

let d12_mid = with_memsafe d12_rr d12_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x2d74)`; d12_common; d12_state;
  `read X8 s = word(n - jj) /\ read X11 s = word_add src (word 8)`;
  d12_good; `ofs = 0 \/ bc <= 7`]));;

let d12_mid_goal = mk_d12_goal [`jj:num`; `ofs:num`; `bc:num`]
  d12_mid d12_post;;

let D12_MID_TAC : tactic =
  D12_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n <= jj + 1` THENL
   [D12_SIM_UNTIL_TAC [0x2e58] THEN D12_GOON_TAC false D12_LAST [];
    D12_SIM_UNTIL_TAC [0x2ddc] THEN D12_SHIFT_TAC THEN
    D12_GOON_EX_TAC false D12_L1 []
     [`n - jj:num`; `jj:num`; `ofs:num`; `bc:num`]];;

let D12_MID = prove(d12_mid_goal, D12_MID_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main loops: after a reload, five lookups for tl <= 11 (with room for  *)
(* 10 bytes) or four for tl = 12 (with room for 8), their bytes and bits     *)
(* after each lookup abbreviated, and the arithmetic of each lookup from the *)
(* atomic facts about its variables only.                                    *)
(* ------------------------------------------------------------------------- *)

(*** The bodies of the main loops: k lookups after a reload (at most 7  ***)
(*** bits used), lookup i at the state of i - 1 lookups, after j(i-1)   ***)
(*** bytes and b(i-1) bits (j0 = jj and b0 = bc), with the index ready  ***)
(*** at the address a of the spec, the symbols stored before r, and the ***)
(*** lookup done before d. The bytes and bits after lookup i are        ***)
(*** abbreviated as ji and bi, with jj + i <= ji <= jj + 2i and         ***)
(*** bi <= bc + i * tl.                                                 ***)

let d12_jv i = if i = 0 then `jj:num`
               else mk_var("j"^string_of_int i,`:num`);;

let d12_bv i = if i = 0 then `bc:num`
               else mk_var("b"^string_of_int i,`:num`);;

let d12_pos b = subst [b,`bc:num`] `8 * ofs + 64 - bc`;;

let d12_bx i =
  list_mk_icomb "zstd_back" [`st:byte list`; d12_pos(d12_bv i); `tl:num`];;

(*** Arithmetic for lookup i: the facts about the variables of the ***)
(*** stream and of lookups i - 1 and i only                        ***)

let D12_IARITH_TAC (i:int) : tactic =
  let vs0 = [`jj:num`; `bc:num`; `tl:num`; `ofs:num`; `n:num`; `m:num`;
             `ws:num list`; `ml:num`; `st:byte list`; d12_jv (i - 1);
             d12_bv (i - 1); d12_jv i; d12_bv i] in
  let numty = `:num` in
  let is_rel t =
    exists (fun op -> is_binary op t && type_of(lhand t) = numty)
           ["="; "<"; "<="] in
  fun (asl,w as gl) ->
    let vs = union vs0 (frees w) in
    let ok t = (is_rel t || (is_neg t && is_rel (rand t))) &&
               not(exists (fun v -> type_of v = `:armstate`) (frees t)) &&
               subset (frees t) vs in
    let facts = filter (ok o concl) (map snd asl) in
    (MAP_EVERY MP_TAC facts THEN ARITH_TAC) gl;;

(*** The decoding of lookup i: the bytes, position and state after it, ***)
(*** the store merged into the bytes before, then the abbreviations    ***)

let D12_BODY_STEP_TAC (i:int) (fold:tactic) : tactic =
  let jp = d12_jv (i - 1) and bp = d12_bv (i - 1) in
  let ji = d12_jv i and bi = d12_bv i in
  let x = d12_bx (i - 1) in
  let jt = mk_binop `(+):num->num->num` jp (d12_el 3 x)
  and bt = mk_binop `(+):num->num->num` (d12_el 2 x) bp in
  let dec j = list_mk_icomb "huf_decode"
    [`ws:num list`; `ml:num`; `st:byte list`; `r:num`; j] in
  let ok j = mk_icomb(`SND:num#bool->bool`,
               mk_icomb(`SND:byte list#num#bool->num#bool`,dec j))
  and ps j = mk_icomb(`FST:num#bool->num`,
               mk_icomb(`SND:byte list#num#bool->num#bool`,dec j))
  and fs j = mk_icomb(`FST:byte list#num#bool->byte list`,dec j) in
  let num k = mk_small_numeral k in
  let bnds = list_mk_conj
    [mk_binop `(<=):num->num->bool`
       (mk_binop `(+):num->num->num` `jj:num` (num i)) ji;
     mk_binop `(<=):num->num->bool` ji
       (mk_binop `(+):num->num->num` `jj:num` (num(2 * i)));
     mk_binop `(<=):num->num->bool` bi
       (mk_binop `(+):num->num->num` `bc:num`
          (mk_binop `( * ):num->num->num` (num i) `tl:num`))] in
  D12_VALA_TAC (D12_IARITH_TAC i) x THEN
  FA_STATE_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN fold THEN
  MP_TAC(SPECL [`ws:num list`; `ml:num`; `tl:num`; `st:byte list`; `r:num`;
                jp] HUF_DECODE_X2_STEP) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  W(fun (asl,w) ->
    MP_TAC(ISPECL [`dst:int64`; fs jp; d12_el 0 x; d12_el 1 x; d12_el 3 x;
                   rand w] READ_MEMORY_X2_STORE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HUF_DECODE_LENGTH];
    REWRITE_TAC[HUF_DECODE_LENGTH] THEN DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(ji,jt)) THEN ABBREV_TAC (mk_eq(bi,bt)) THEN
  SUBGOAL_THEN bnds STRIP_ASSUME_TAC THENL [D12_IARITH_TAC i; ALL_TAC] THEN
  let posi = d12_pos bi in
  SUBGOAL_THEN (mk_eq(ps ji,posi)) ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> let c = concl th in
      if is_eq c && lhs c = ps ji && not(rhs c = posi)
      then REWRITE_TAC[th] else NO_TAC) THEN
    D12_IARITH_TAC i;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && lhs c = ps ji && not(rhs c = posi)
    then ALL_TAC else NO_TAC) THEN
  SUBGOAL_THEN (ok ji) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_iff c && lhs c = ok ji then REWRITE_TAC[th] else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN D12_IARITH_TAC i;
    FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_iff c && lhs c = ok ji then ALL_TAC else NO_TAC)] THEN
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && lhs c = fs ji then FA_STATE_REWRITE_TAC[GSYM th]
    else NO_TAC);;

(*** The body: the k lookups by the addresses (a, r, d) of each ***)

let D12_BODY_TAC (spec:(int*int*int) list) : tactic =
  let k = length spec in
  let one i (a,r,d) =
    let x = d12_bx (i - 1) in
    let fold = if i = 1 then ALL_TAC else
      let jp = d12_jv (i - 1) and bp = d12_bv (i - 1) in
      let x' = d12_bx (i - 2) in
      FA_STATE_REWRITE_TAC
       [ASSUME(mk_eq(mk_binop `(+):num->num->num` (d12_jv (i - 2))
                       (d12_el 3 x'),jp));
        ASSUME(mk_eq(mk_binop `(+):num->num->num` (d12_el 2 x')
                       (d12_bv (i - 2)),bp))] in
    D12_SIM_UNTIL_TAC [a] THEN
    W(fun (_,w) -> D12_LOOKUPA_TAC (D12_IARITH_TAC (i - 1)) (rand w)
                     `ofs:num` (d12_bv (i - 1))) THEN
    D12_SIM_UNTIL_TAC [r] THEN D12_REREAD_TAC x THEN
    D12_SIM_UNTIL_TAC [d] THEN D12_BODY_STEP_TAC i fold in
  MAP_EVERY (fun i -> one i (el (i - 1) spec)) (1--k);;

(*** The goal of a piece with the hypotheses d12_hyps and more ***)

let mk_d12h_goal more extra pre post =
  let tm = mk_imp(mk_conj(d12_hyps,more),
                  list_mk_icomb "ensures" [`arm`; pre; post; d12_frame]) in
  let vs = d12_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_d12h_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** The end of the output less 9 (or 7) for the comparisons of the main ***)
(*** loops, as a number                                                  ***)

let D12_END_LESS = prove
 (`!(dst:int64) n k.
     k <= val dst + n /\ val dst + n < 2 EXP 64
     ==> word_sub (word_add dst (word n)) (word k):int64 =
         word((val dst + n) - k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add (dst:int64) (word n) = word(((val dst + n) - k) + k)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `k <= x ==> (x - k) + k = x`] THEN
    REWRITE_TAC[WORD_ADD; WORD_VAL];
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let D12_END_LESS2 = prove
 (`!(dst:int64) n k.
     k <= n /\ val dst + n < 2 EXP 64
     ==> word_add dst (word(n - k)):int64 = word((val dst + n) - k)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let D12_ENDVAL_TAC (k:term) : tactic =
  let t = subst [k,`k:num`]
   `val(word((val(dst:int64) + n) - k):int64) = (val dst + n) - k` in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ASSUME `val(dst:int64) + n < 2 EXP 64`) THEN ARITH_TAC;
    ALL_TAC];;

(*** 0x2cbc, the loop of a reload and five lookups for tl <= 11 while ***)
(*** more than nine bytes are left (the output below the end less 9), ***)
(*** for the measure m = n - jj; good all through                     ***)

let d12_l5more = `tl <= 11 /\ 9 <= val(dst:int64) + n`;;

let d12_end9 = `word((val(dst:int64) + n) - 9):int64`;;

let d12_l5body = list_mk_conj
 [`read PC s = word(pc + 0x2cbc)`; d12_common; d12_state;
  `read X11 s = word_add src (word 8) /\ read X8 s = word(64 - tl)`;
  mk_eq(`read X13 s`,d12_end9); d12_good];;

let d12_l5inv = with_memsafe d12_rr d12_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],
    mk_conj(`m = n - jj`,d12_l5body))));;

let d12_l5_goal = mk_d12h_goal d12_l5more []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(d12_l5inv,[`m:num`; `s:armstate`]))))
  d12_post;;

(*** 0x2be8, the body of five lookups after a reload, with at least ten ***)
(*** bytes left                                                         ***)

let d12_b5body = list_mk_conj
 [`read PC s = word(pc + 0x2be8)`; d12_common; d12_state;
  `read X11 s = word_add src (word 8) /\ read X8 s = word(64 - tl) /\
   read X12 s = word 1`;
  mk_eq(`read X13 s`,d12_end9);
  `jj + 10 <= n /\ bc <= 7`; d12_good];;

let d12_b5 = with_memsafe d12_rr d12_wr (mk_abs(`s:armstate`,d12_b5body));;

let d12_b5_goal = mk_d12h_goal d12_l5more [`jj:num`; `ofs:num`; `bc:num`]
  d12_b5
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     mk_conj(`m < n - jj`,
             list_mk_comb(d12_l5inv,[`m:num`; `s:armstate`])))));;

let D12_B5_TAC : tactic =
  D12_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  D12_BODY_TAC [0x2bf8,0x2c04,0x2c14; 0x2c20,0x2c2c,0x2c3c;
                0x2c48,0x2c54,0x2c64; 0x2c70,0x2c7c,0x2c8c;
                0x2c98,0x2ca4,0x2cb4] THEN
  SUBGOAL_THEN `b5 <= 62` ASSUME_TAC THENL [D12_IARITH_TAC 5; ALL_TAC] THEN
  D12_SIM_UNTIL_TAC [0x2cbc] THEN PUFF_FINAL_TAC THEN
  EXISTS_TAC `n - j5:num` THEN CONJ_TAC THENL [D12_IARITH_TAC 5; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`j5:num`; `ofs:num`; `b5:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  D12_IARITH_TAC 5;;

let D12_B5 = prove(d12_b5_goal, D12_B5_TAC);;

(*** The loop: the body to a later iteration (its measure m = n - jj), ***)
(*** the exits to 0x2d74 after the main loop                           ***)

let D12_BODY_WTAC : tactic =
  GEN_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN POP_ASSUM MP_TAC THEN
  TRY(SUBST1_TAC(ASSUME `m = n - jj`)) THEN REWRITE_TAC[];;

let D12_TO_MID_TAC : tactic =
  D12_SIM_UNTIL_TAC [0x2d74] THEN
  FA_STATE_REWRITE_TAC[WORD_RULE
   `word_sub (word_add (dst:int64) (word n)) (word_add dst (word jj)) =
    word_sub (word n) (word jj)`] THEN
  FA_STATE_REWRITE_TAC[GSYM(REWRITE_RULE[ASSUME `jj <= n`]
                              (ISPECL [`n:num`; `jj:num`] WORD_SUB))];;

let D12_L5_RELOADED_TAC (partial:bool) : tactic =
  let fix = if partial then D12_MOD8_TAC else ALL_TAC in
  let ofs' = `ofs - bc DIV 8` and bc' = `bc MOD 8` in
  D12_BIG_TAC THEN D12_SLICE_TAC ofs' THEN
  ASM_CASES_TAC `jj + 10 <= n` THENL
   [D12_SIM_UNTIL_TAC [0x2be8] THEN fix THEN
    ZSTD_CONTINUE_WITH_TAC D12_BODY_WTAC D12_B5
      [ofs',`ofs:num`; bc',`bc:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN D12_ARITH_TAC;
    D12_TO_MID_TAC THEN fix THEN
    D12_GOON_TAC true D12_MID [ofs',`ofs:num`; bc',`bc:num`]];;

let D12_L5_TAC : tactic =
  D12_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  D12_OPVAL_TAC [`jj:num`] THEN D12_ENDVAL_TAC `9` THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [D12_L5_RELOADED_TAC false;
    ASM_CASES_TAC `ofs = 0` THENL
     [D12_OFS0_TAC THEN D12_TO_MID_TAC THEN D12_GOON_TAC true D12_MID [];
      ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
       [D12_L5_RELOADED_TAC true;
        D12_BIG_TAC THEN D12_SLICE_TAC `0` THEN D12_TO_MID_TAC THEN
        D12_GOON0_TAC true D12_MID
          [`0`,`ofs:num`; `bc - 8 * ofs`,`bc:num`]]]];;

let D12_L5 = prove(d12_l5_goal, D12_L5_TAC);;

(*** 0x2f8c, the loop of a reload and four lookups for tl = 12 while   ***)
(*** more than seven bytes are left (the output below the end less 7), ***)
(*** for the measure m = n - jj; good all through                      ***)

let d12_l4more = `12 <= tl /\ 7 <= val(dst:int64) + n`;;

let d12_end7 = `word((val(dst:int64) + n) - 7):int64`;;

let d12_l4body = list_mk_conj
 [`read PC s = word(pc + 0x2f8c)`; d12_common; d12_state;
  `read X11 s = word_add src (word 8) /\ read X12 s = word(64 - tl)`;
  mk_eq(`read X13 s`,d12_end7); d12_good];;

let d12_l4inv = with_memsafe d12_rr d12_wr (list_mk_abs
 ([`m:num`; `s:armstate`],
  list_mk_exists([`jj:num`; `ofs:num`; `bc:num`],
    mk_conj(`m = n - jj`,d12_l4body))));;

let d12_l4_goal = mk_d12h_goal d12_l4more []
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     list_mk_comb(d12_l4inv,[`m:num`; `s:armstate`]))))
  d12_post;;

(*** 0x2ee0, the body of four lookups after a reload, with at least ***)
(*** eight bytes left                                               ***)

let d12_b4body = list_mk_conj
 [`read PC s = word(pc + 0x2ee0)`; d12_common; d12_state;
  `read X11 s = word_add src (word 8) /\ read X12 s = word(64 - tl) /\
   read X8 s = word 1`;
  mk_eq(`read X13 s`,d12_end7);
  `jj + 8 <= n /\ bc <= 7`; d12_good];;

let d12_b4 = with_memsafe d12_rr d12_wr (mk_abs(`s:armstate`,d12_b4body));;

let d12_b4_goal = mk_d12h_goal d12_l4more [`jj:num`; `ofs:num`; `bc:num`]
  d12_b4
  (mk_abs(`s:armstate`,mk_exists(`m:num`,
     mk_conj(`m < n - jj`,
             list_mk_comb(d12_l4inv,[`m:num`; `s:armstate`])))));;

let D12_B4_TAC : tactic =
  D12_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  D12_BODY_TAC [0x2ef0,0x2efc,0x2f0c; 0x2f18,0x2f24,0x2f34;
                0x2f40,0x2f4c,0x2f5c; 0x2f68,0x2f74,0x2f84] THEN
  SUBGOAL_THEN `b4 <= 55` ASSUME_TAC THENL [D12_IARITH_TAC 4; ALL_TAC] THEN
  D12_SIM_UNTIL_TAC [0x2f8c] THEN PUFF_FINAL_TAC THEN
  EXISTS_TAC `n - j4:num` THEN CONJ_TAC THENL [D12_IARITH_TAC 4; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`j4:num`; `ofs:num`; `b4:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  D12_IARITH_TAC 4;;

let D12_B4 = prove(d12_b4_goal, D12_B4_TAC);;

(*** The loop: the body to a later iteration, the exits to 0x2d74 ***)

let D12_L4_RELOADED_TAC (partial:bool) : tactic =
  let fix = if partial then D12_MOD8_TAC else ALL_TAC in
  let ofs' = `ofs - bc DIV 8` and bc' = `bc MOD 8` in
  D12_BIG_TAC THEN D12_SLICE_TAC ofs' THEN
  ASM_CASES_TAC `jj + 8 <= n` THENL
   [D12_SIM_UNTIL_TAC [0x2ee0] THEN fix THEN
    ZSTD_CONTINUE_WITH_TAC D12_BODY_WTAC D12_B4
      [ofs',`ofs:num`; bc',`bc:num`] THEN
    MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN D12_ARITH_TAC;
    D12_TO_MID_TAC THEN fix THEN
    D12_GOON_TAC true D12_MID [ofs',`ofs:num`; bc',`bc:num`]];;

let D12_L4_TAC : tactic =
  D12_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `jj:num` THEN ENSURES_EXISTS_PRE_TAC `ofs:num` THEN
  ENSURES_EXISTS_PRE_TAC `bc:num` THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  D12_OPVAL_TAC [`jj:num`] THEN D12_ENDVAL_TAC `7` THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [D12_L4_RELOADED_TAC false;
    ASM_CASES_TAC `ofs = 0` THENL
     [D12_OFS0_TAC THEN D12_TO_MID_TAC THEN D12_GOON_TAC true D12_MID [];
      ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
       [D12_L4_RELOADED_TAC true;
        D12_BIG_TAC THEN D12_SLICE_TAC `0` THEN D12_TO_MID_TAC THEN
        D12_GOON0_TAC true D12_MID
          [`0`,`ofs:num`; `bc - 8 * ofs`,`bc:num`]]]];;

let D12_L4 = prove(d12_l4_goal, D12_L4_TAC);;

(* ------------------------------------------------------------------------- *)
(* The reload for at most 7 bytes (or none), and the start: BIT_initDStream, *)
(* then the reload or the main loop of 5 lookups (tl <= 11) or of 4 (tl =    *)
(* 12).                                                                      *)
(* ------------------------------------------------------------------------- *)

(*** 0x2d38, at most 7 bytes (none decoded yet): one reload, then the ***)
(*** last symbol if at most one byte, else the loop of one lookup     ***)

let d12_single = with_memsafe d12_rr d12_wr (mk_abs(`s:armstate`,list_mk_conj
 [`read PC s = word(pc + 0x2d38)`; d12_common;
  `read X6 s = dst /\ read X3 s = word_add src (word ofs)`;
  mk_eq(`read X7 s`,d12_win);
  `read X5 s = word bc /\ (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list))`;
  `read X8 s = word n /\ read X11 s = word_add src (word 8) /\ n <= 7`;
  `8 * ofs + 64 - bc = r /\ bc <= 64`]));;

let d12_single_goal = mk_d12_goal [`ofs:num`; `bc:num`] d12_single d12_post;;

(*** Going on with a piece th at jj = 0, its facts about the decoding of ***)
(*** no bytes reduced                                                    ***)

let D12_GOON_J0_TAC th insts (ws:term list) : tactic =
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC)
    th ((`0`,`jj:num`)::insts) THEN
  MEMSAFE_ELIM_TAC THEN MAP_EVERY EXISTS_TAC ws THEN
  REWRITE_TAC[HUF_DECODE_0; READ_MEMORY_BYTES_0; num_of_bytelist;
              WORD_ADD_0; SUB_0; ADD_CLAUSES; LE_0] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY D12_SARITH_TAC THEN
  TRY(DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      D12_SARITH_TAC);;

(*** After the reload to ofs' with bc' bits used: the last symbol if at ***)
(*** most one byte, else the loop of one lookup (from 0x2fd8)           ***)

let D12_SINGLE_FIN_TAC ofs' bc' : tactic =
  ASM_CASES_TAC `n <= 1` THENL
   [D12_SIM_UNTIL_TAC [0x2e58] THEN
    D12_GOON_J0_TAC D12_LAST [ofs',`ofs:num`; bc',`bc:num`] [];
    D12_SIM_UNTIL_TAC [0x2ddc] THEN D12_SHIFT_TAC THEN
    D12_GOON_J0_TAC D12_L1 [] [`n:num`; `0`; ofs'; bc']];;

let D12_SINGLE_TAC : tactic =
  D12_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [D12_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`bc:num`; `8`] DIVISION) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [D12_BIG_TAC THEN D12_SLICE_TAC `ofs - bc DIV 8` THEN
    D12_SINGLE_FIN_TAC `ofs - bc DIV 8` `bc MOD 8`;
    ASM_CASES_TAC `ofs = 0` THENL
     [D12_OFS0_TAC THEN D12_SINGLE_FIN_TAC `ofs:num` `bc:num`;
      D12_BIG_TAC THEN ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
       [D12_SLICE_TAC `ofs - bc DIV 8` THEN
        D12_SIM_UNTIL_TAC [0x2d74] THEN D12_MOD8_TAC THEN
        D12_GOON_J0_TAC D12_MID [`ofs - bc DIV 8`,`ofs:num`;
                                 `bc MOD 8`,`bc:num`] [];
        D12_SLICE_TAC `0` THEN D12_SIM_UNTIL_TAC [0x2d74] THEN
        ZSTD_CONTINUE_WITH_TAC
         (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC)
         D12_MID [`0`,`jj:num`; `0`,`ofs:num`; `bc - 8 * ofs`,`bc:num`] THEN
        MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[HUF_DECODE_0; READ_MEMORY_BYTES_0; num_of_bytelist;
                    WORD_ADD_0; SUB_0; ADD_CLAUSES; LE_0] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
        TRY(FIRST_ASSUM ACCEPT_TAC) THEN D12_SARITH_TAC]]];;

let D12_SINGLE = prove(d12_single_goal, D12_SINGLE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The result: from huf_x2_result at the end r of the stream to huf_stream.  *)
(* ------------------------------------------------------------------------- *)

let HUF_X2_RESULT = prove
 (`!ws ml (st:byte list) r n (x0:int64) mem.
        huf_complete ws ml /\ LENGTH ws <= 256 /\ zstd_end st r /\
        huf_x2_result ws ml st r n x0 mem
        ==> (!out. LENGTH out = n /\ huf_stream ws ml st out
                   ==> x0 = word n /\ mem = num_of_bytelist out) /\
            (x0 = word n \/ zstd_is_error x0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[huf_x2_result] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `out:byte list` THEN STRIP_TAC THEN
  SUBGOAL_THEN `huf_decode ws ml (st:byte list) r n = (out,0,T)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `LENGTH(out:byte list) = n`)) THEN
    MP_TAC(SPECL [`ws:num list`; `ml:num`; `st:byte list`; `r:num`;
                  `out:byte list`] HUF_STREAM_DECODE) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The start: BIT_initDStream, then the reload for at most 7 bytes or the    *)
(* main loop of 5 lookups (tl <= 11) or of 4 (tl = 12). A stream of 8 bytes  *)
(* or more starts with the container holding its last 8 bytes, and a        *)
(* shorter one with it holding its bytes (put together in a switch on the    *)
(* length), with bc counting the missing ones as used; in both cases at the  *)
(* position below the top bit of the last byte, which is the end of the      *)
(* stream in the specification. An empty stream, and one whose last byte is  *)
(* 0, are errors.                                                            *)
(* ------------------------------------------------------------------------- *)

(*** The last byte b of the stream, with vb = val b, read at step 5 ***)

let D12_INIT_TAC : tactic =
  D12_STEPS_TAC (1--4) THEN
  SUBGOAL_THEN `1 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`src:int64`; `st:byte list`; `LENGTH(st:byte list) - 1`;
                 `s4:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_PRED_LEMMA] THEN DISCH_TAC THEN
  ABBREV_TAC `b = EL (LENGTH(st:byte list) - 1) st` THEN
  D12_STEPS_TAC [5] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP ZSTD_LAST_ADDR
    (ASSUME `1 <= LENGTH(st:byte list)`)]) THEN
  ABBREV_TAC `vb = val(b:byte)` THEN
  SUBGOAL_THEN `vb < 256` ASSUME_TAC THENL
   [EXPAND_TAC "vb" THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC];;

(*** The postcondition of the theorem from that of a piece, for the ***)
(*** stream ending at r = 8 * (LENGTH st - 1) + bitsize vb - 1      ***)

let d12_top_r = `8 * (LENGTH(st:byte list) - 1) + bitsize vb - 1`;;

let D12_TOP_WEAKEN_TAC : tactic =
  X_GEN_TAC `s':armstate` THEN REWRITE_TAC[puff_memsafe] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ m ==> a /\ b /\ m`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_ASSUM ACCEPT_TAC ORELSE
    HUF_LENGTH_FACTS_TAC (fun ths ->
      FIRST_ASSUM(MP_TAC o check (is_exists o concl)) THEN
      REWRITE_TAC ths)] THEN
  MATCH_MP_TAC HUF_X2_RESULT THEN EXISTS_TAC d12_top_r THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MP_TAC(SPECL [`st:byte list`; d12_top_r] ZSTD_END_LAST) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SIMPLE_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ASSUME `EL (LENGTH(st:byte list) - 1) st = b`;
                ASSUME `val(b:byte) = vb`; ASSUME `~(vb = 0)`]];;

(*** Going on with the piece th, with the table at DTable + 4, the end ***)
(*** of the stream and the instantiation insts, and the witnesses ws   ***)
(*** of its precondition                                               ***)

let D12_TOP_GOON_TAC th insts (ws:term list) : tactic =
  ZSTD_CONTINUE_WITH_TAC D12_TOP_WEAKEN_TAC th
   ([`word_add dtable (word 4):int64`,`dt:int64`; d12_top_r,`r:num`] @
    insts) THEN
  MEMSAFE_ELIM_TAC THEN MAP_EVERY EXISTS_TAC ws THEN
  REWRITE_TAC[HUF_DECODE_0; READ_MEMORY_BYTES_0; num_of_bytelist;
              WORD_ADD_0; SUB_0; ADD_CLAUSES; LE_0; MULT_CLAUSES;
              WORD_CONTAINER_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0; WORD_CONTAINER_0] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ZSTD_ARITH_TAC ORELSE
   (AP_TERM_TAC THEN ZSTD_ARITH_TAC));;

(*** After the setup, at the test of n (0x2ba8 or 0x2d28), with the  ***)
(*** stream at ofs and bc bits used: the reload for at most 7 bytes, ***)
(*** else the main loop for tl <= 11 or for tl = 12                  ***)

let D12_TOP_DISPATCH_TAC (ofs:term) (bc:term) : tactic =
  let h = CONJ (ASSUME `1 <= tl`) (ASSUME `tl <= 12`) in
  ASM_CASES_TAC `n <= 7` THENL
   [ASM_CASES_TAC `n = 0` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n = 0`)) THEN
      D12_SIM_UNTIL_TAC [0x2d38] THEN
      D12_TOP_GOON_TAC D12_SINGLE [ofs,`ofs:num`; bc,`bc:num`; `0`,`n:num`]
       [];
      D12_SIM_UNTIL_TAC [0x2d38] THEN
      D12_TOP_GOON_TAC D12_SINGLE [ofs,`ofs:num`; bc,`bc:num`] []];
    SUBGOAL_THEN `9 <= val(dst:int64) + n /\ 7 <= val dst + n`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(val(dst:int64) = 0)`; `~(n <= 7)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `tl <= 11` THENL
     [D12_SIM_UNTIL_TAC [0x2cbc] THEN
      FA_STATE_REWRITE_TAC[MP (SPEC `tl:num` HUF_SHIFT_WORD) h;
        MP (SPECL [`dst:int64`; `n:num`; `9`] D12_END_LESS)
           (CONJ (ASSUME `9 <= val(dst:int64) + n`)
                 (ASSUME `val(dst:int64) + n < 2 EXP 64`))] THEN
      D12_TOP_GOON_TAC D12_L5 [] [`n - 0`; `0`; ofs; bc];
      SUBGOAL_THEN `12 <= tl` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      D12_SIM_UNTIL_TAC [0x2f8c] THEN
      SUBGOAL_THEN `7 <= n` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      FA_STATE_REWRITE_TAC[MP (SPEC `tl:num` HUF_SHIFT_WORD) h;
        MP (SPECL [`dst:int64`; `n:num`; `7`] D12_END_LESS)
           (CONJ (ASSUME `7 <= val(dst:int64) + n`)
                 (ASSUME `val(dst:int64) + n < 2 EXP 64`));
        MP (SPECL [`dst:int64`; `n:num`; `7`] D12_END_LESS2)
           (CONJ (ASSUME `7 <= n`)
                 (ASSUME `val(dst:int64) + n < 2 EXP 64`))] THEN
      D12_TOP_GOON_TAC D12_L4 [] [`n - 0`; `0`; ofs; bc]]];;

(*** A stream of 8 bytes or more whose last byte is not 0 ***)

let D12_BIG_TOP_TAC : tactic =
  HUF_VB_FACTS_TAC THEN D12_STEPS_TAC (6--16) THEN
  HUF_RELOAD_SLICE_TAC `LENGTH(st:byte list) - 8` `s16:armstate` THEN
  D12_STEPS_TAC (17--18) THEN
  D12_TOP_DISPATCH_TAC `LENGTH(st:byte list) - 8` `32 - bitsize vb - 23`;;

(*** A stream of k bytes, 1 <= k <= 7: its bytes read, the container as ***)
(*** their sum                                                          ***)

let D12_SMALL_TOP_TAC k =
  let numt = mk_small_numeral in
  let els = map (fun i -> list_mk_icomb "EL" [numt i; `st:byte list`])
                (0--(k-1)) in
  let sum = itlist (fun e acc ->
              mk_binop `(+):num->num->num` (mk_icomb(`val:byte->num`,e))
                (mk_binop `( * ):num->num->num` `256` acc)) els `0` in
  let lst = mk_list(els,`:byte`) in
  let bc = mk_binop `(-):num->num->num`
             (mk_binop `(+):num->num->num` `32 - bitsize vb`
                (numt(8 * (8 - k)))) `23` in
  let memfact i =
    MP_TAC(ISPECL [`src:int64`; `st:byte list`; numt i; `s5:armstate`]
      READ_MEMORY_BYTES8_BYTELIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] in
  let range = ARITH_RULE(mk_eq(mk_binop `(<):num->num->bool` `i:num` (numt k),
                list_mk_disj(map (fun j -> mk_eq(`i:num`,numt j))
                                 (0--(k-1))))) in
  MAP_EVERY memfact (0--(k-1)) THEN
  SUBGOAL_THEN (mk_eq(`num_of_bytelist(st:byte list)`,sum)) ASSUME_TAC THENL
   [SUBGOAL_THEN (mk_eq(`st:byte list`,lst))
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] THEN
                 REWRITE_TAC[num_of_bytelist]) THEN
    REWRITE_TAC[LIST_EQ; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[range] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `vb = 0` THENL
   [D12_RUN_TAC THEN PUFF_FINAL_TAC THEN HUF_NO_STREAM_TAC HUF_LAST0_TAC;
    HUF_VB_FACTS_TAC THEN D12_SIM_UNTIL_TAC [0x2ba8] THEN
    D12_TOP_DISPATCH_TAC `0` bc];;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For the stream st of the n bytes at src, and the        *)
(* decoding table (built by HUF_readDTableX2_wksp) for the weights ws, with  *)
(* codes of at most ml bits and a table of tl bits, at DTable + 4, its       *)
(* header holding tl at DTable + 2, and the n bytes at dst (not at address   *)
(* 0): if st is the Huffman-coded stream of the n bytes out, the result is   *)
(* n, with out at dst; and the result is always n or an error code. The      *)
(* loads are from the stream, the table and its header, and the stores to    *)
(* the n bytes at dst.                                                       *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS1X2_USINGDTABLE_CORRECT = prove
 (`!pc returnaddress dst n src (st:byte list) dtable ws ml tl e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     huf_complete ws ml /\ LENGTH ws <= 256 /\
     1 <= ml /\ ml <= tl /\ tl <= 12 /\ n < 2 EXP 28 /\
     8 <= val src /\ val src + LENGTH st + 8 < 2 EXP 64 /\
     LENGTH st < 2 EXP 60 /\ val dst + n < 2 EXP 64 /\ ~(val dst = 0) /\
     nonoverlapping (dst,n) (src,LENGTH st) /\
     nonoverlapping (dst,n) (word_add dtable (word 4),4 * 2 EXP tl) /\
     nonoverlapping (dst,n) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x2b30) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; word n; src; word(LENGTH st); dtable] s /\
               read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
               read (memory :> bytes8(word_add dtable (word 2))) s = word tl /\
               read (memory :> bytes(word_add dtable (word 4),4 * 2 EXP tl))
                    s =
               num_of_bytelist(huf_dtable2 ws ml tl) /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!out. LENGTH out = n /\ huf_stream ws ml st out
                      ==> read X0 s = word n /\
                          read (memory :> bytes(dst,n)) s =
                          num_of_bytelist out) /\
               (read X0 s = word n \/ zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH st; word_add dtable (word 2),1;
                       word_add dtable (word 4),4 * 2 EXP tl]
                      [dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(dst,n)])`,
  D12_INTRO_TAC THEN REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `LENGTH(st:byte list) = 0` THENL
   [D12_RUN_TAC THEN PUFF_FINAL_TAC THEN
    HUF_NO_STREAM_TAC(REWRITE_TAC[zstd_end] THEN ASM_MESON_TAC[LENGTH_EQ_NIL]);
    ALL_TAC] THEN
  D12_INIT_TAC THEN
  ASM_CASES_TAC `8 <= LENGTH(st:byte list)` THENL
   [ASM_CASES_TAC `vb = 0` THENL
     [D12_RUN_TAC THEN PUFF_FINAL_TAC THEN HUF_NO_STREAM_TAC HUF_LAST0_TAC;
      D12_BIG_TOP_TAC];
    SUBGOAL_THEN
     `LENGTH(st:byte list) = 1 \/ LENGTH st = 2 \/ LENGTH st = 3 \/
      LENGTH st = 4 \/ LENGTH st = 5 \/ LENGTH st = 6 \/ LENGTH st = 7`
    (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [SIMPLE_ARITH_TAC; D12_SMALL_TOP_TAC 1; D12_SMALL_TOP_TAC 2;
      D12_SMALL_TOP_TAC 3; D12_SMALL_TOP_TAC 4; D12_SMALL_TOP_TAC 5;
      D12_SMALL_TOP_TAC 6; D12_SMALL_TOP_TAC 7]]);;

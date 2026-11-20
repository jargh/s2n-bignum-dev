(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* zstd's HUF_decompress4X_hufOnly_wksp, the decoding of Huffman-coded       *)
(* literals in four streams with the description of their tree, compiled by  *)
(* gcc 12 at -O2 for AArch64 (HUF_DECOMPRESS4X_HUFONLY_WKSP_CORRECT), and    *)
(* HUF_selectDecoder, which it calls (HUF_SELECTDECODER_CORRECT). The        *)
(* function reads the description at the start of the input into the table   *)
(* at dtable with HUF_readDTableX1_wksp or HUF_readDTableX2_wksp, as         *)
(* HUF_selectDecoder chooses from the sizes of the input and the output, and *)
(* decodes the four streams after it with the decoding for that kind of      *)
(* table, by a tail call. For an input l of the n bytes out                  *)
(* (huf_decompress4x1 T l out: the description and the four streams, in the  *)
(* zstd dialect), a workspace of at least 2124 bytes and a table with room   *)
(* for the table log (mtl, the byte 0 of its header, at least the            *)
(* Max_Number_of_Bits of the description, so that mtl = 12 is enough for any *)
(* description), the result is n with out at dst; and the result is always n *)
(* or an error code. The loads are from the input, the table, the workspace, *)
(* the stack, the GOT entries of memcpy and memset, the region (ea,el) of    *)
(* their contracts, BIT_mask and algoTime, and the stores to the table, the  *)
(* workspace, the stack and the n bytes at dst; the stack region of 816      *)
(* bytes covers the frame of 64 bytes, the frames of the readers below it    *)
(* and those of the decodings.                                               *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode4x2_gcc12_O2.ml";;
needs "arm/proofs/zstd_huf_read_dtable_x1_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_selectDecoder at 0x7154 (HUF_SELECTDECODER_CORRECT): the choice       *)
(* between the decodings with single-symbol and double-symbol tables, from   *)
(* the estimates of their times in the table algoTime of the image           *)
(* (huf_select_decoder).                                                     *)
(* ------------------------------------------------------------------------- *)

(*** HUF_selectDecoder at 0x7154: the choice of the decoder with double- ***)
(*** symbol tables (1) or with single-symbol ones (0), by the estimates  ***)
(*** of their times from the table algoTime of 16 rows of 4 words at     ***)
(*** 0x7c00 in the image, for the row q, the ratio of the sizes in 16ths ***)
(*** (15 when the input is not smaller than the output)                  ***)

let huf_algotime = new_definition
 `huf_algotime =
   [0; 0; 1; 1; 0; 0; 1; 1; 150; 216; 381; 119; 170; 205; 514; 112;
    177; 199; 539; 110; 197; 194; 644; 107; 221; 192; 735; 107;
    256; 189; 881; 106; 359; 188; 1167; 109; 582; 187; 1570; 114;
    688; 187; 1712; 122; 825; 186; 1965; 136; 976; 185; 2131; 150;
    1180; 186; 2070; 175; 1377; 185; 1731; 202; 1412; 185; 1695; 202]`;;

let huf_select_decoder = new_definition
 `huf_select_decoder dsize csize =
    let q = if csize < dsize then ((16 * csize) MOD 2 EXP 64) DIV dsize
            else 15
    and d = dsize DIV 256 in
    let t0 = (EL (4 * q) huf_algotime + EL (4 * q + 1) huf_algotime * d)
             MOD 2 EXP 32
    and t1 = (EL (4 * q + 2) huf_algotime +
              EL (4 * q + 3) huf_algotime * d) MOD 2 EXP 32 in
    if (t1 + t1 DIV 32) MOD 2 EXP 32 < t0 then 1 else 0`;;

let HUF_ALGOTIME_BYTES = prove
 (`num_of_bytelist(SUB_LIST(31744,256) zstd_huf_gcc12_O2_mc) =
   num_of_wordlist(MAP (word:num->int32) huf_algotime)`,
  REWRITE_TAC[zstd_huf_gcc12_O2_mc; huf_algotime] THEN
  CONV_TAC(ONCE_DEPTH_CONV SUB_LIST_CONV) THEN
  REWRITE_TAC[MAP; num_of_bytelist; num_of_wordlist; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let HUF_ALGOTIME_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc
          ==> read (memory :> bytes(word_add (word pc) (word 31744),256)) s =
              num_of_wordlist(MAP (word:num->int32) huf_algotime)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_bytes_loaded] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM HUF_ALGOTIME_BYTES] THEN
  MP_TAC(ISPECL [`s:armstate`; `word pc:int64`; `zstd_huf_gcc12_O2_mc`;
                 `31744`; `256`] BYTES_LOADED_SUB_LIST) THEN
  ASM_REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_SUB_LIST;
                  LENGTH_ZSTD_HUF_GCC12_O2_MC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let HUF_ALGOTIME_READ = prove
 (`!s pc k.
        aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\ k < 64
        ==> read (memory :> bytes32
                  (word_add (word_add (word pc) (word 31744)) (word(4 * k))))
                 s = word(EL k huf_algotime)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add (word pc) (word 31744):int64`;
                 `MAP (word:num->int32) huf_algotime`; `64`; `k:num`;
                 `s:armstate`] READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_SIMP_TAC[HUF_ALGOTIME_LOADED; ARITH_RULE `4 * 64 = 256`;
               LENGTH_MAP] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[huf_algotime; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EL_MAP THEN
  REWRITE_TAC[huf_algotime; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(*** The code of HUF_selectDecoder and of the entry points of the four- ***)
(*** stream decoding, and its simulation, as ZSTD_STEP_TAC              ***)

let SEL_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc
  [0x7154,0x71cc; 0x73d0,0x7508];;

let SEL_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC SEL_EXEC [n] THEN ZSTD_SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                  WORD_CMP_64_SFLAGS) THEN
                TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let SEL_STEPS_TAC ns = MAP_EVERY SEL_STEP_TAC ns;;

(*** The result in X0 for the sizes dsize of the output and csize of the ***)
(*** input. The function changes only x0-x5 and the flags, and its       ***)
(*** caller HUF_decompress4X_hufOnly_wksp keeps values in x6-x8 across   ***)
(*** the call, so the frame is exactly those                             ***)

let sel_goal =
 `!pc returnaddress dsize csize e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     dsize < 2 EXP 64 /\ csize < 2 EXP 64
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x7154) /\ read X30 s = returnaddress /\
               C_ARGUMENTS [word dsize; word csize] s /\ read events s = e)
          (\s. read PC s = returnaddress /\
               read X0 s = word(huf_select_decoder dsize csize) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [word(pc + 0x7c00),256] []))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])`;;

(*** The row q of the table from the ratio of the sizes, when the input ***)
(*** is smaller than the output                                         ***)

let SEL_ROW = prove
 (`!dsize csize.
     csize < dsize /\ dsize < 2 EXP 64
     ==> word_shl (word_subword (word_udiv (word (16 * csize)) (word dsize)
                                 :int64) (0,32)) 4:int64 =
         word(4 * (4 * (((16 * csize) MOD 2 EXP 64) DIV dsize))) /\
         ((16 * csize) MOD 2 EXP 64) DIV dsize < 16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((16 * csize) MOD 2 EXP 64) DIV dsize < 16` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(dsize = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ] THEN
    MP_TAC(SPECL [`16 * csize`; `2 EXP 64`] MOD_LE) THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD_SUBWORD; VAL_WORD_UDIV;
              VAL_WORD; DIMINDEX_64; ARITH_RULE `MIN 32 64 = 32`;
              EXP; DIV_1] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ABBREV_TAC `r = ((16 * csize) MOD 2 EXP 64) DIV dsize` THEN
  SUBGOAL_THEN `r < 2 EXP 32 /\ 2 EXP 4 * r < 2 EXP 64 /\
                4 * (4 * r) < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r < 16` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(*** The flags of the comparison of the estimates, unsigned ***)

let SEL_HI = prove
 (`!w0 w1:int32.
     (&(val w0) - &(val w1):int = &(val (word_sub w0 w1)) /\
      ~(val (word_sub w0 w1) = 0)) <=> val w1 < val w0`,
  REWRITE_TAC[NOCARRY_WORD_SUB; VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ] THEN
  ARITH_TAC);;

(*** The words of the row after its first, at the addresses as the loads ***)
(*** of the code give them, from the base tbl of the table               ***)

let SEL_READS_TAC : tactic =
  let wa x y = mk_comb(mk_comb(`word_add:int64->int64->int64`,x),y) in
  let forms = [`word_add tbl (word (4 * 4 * q + 4)):int64`,1;
               `word_add tbl (word (4 * 4 * q + 8)):int64`,2;
               `word_add tbl (word (4 * 4 * q + 12)):int64`,3] in
  let one (a,j) =
    let k = mk_binop `(+):num->num->num` `4 * q` (mk_small_numeral j) in
    let a' = wa `tbl:int64`
               (mk_comb(`word:num->int64`,
                        mk_binop `( * ):num->num->num` `4` k)) in
    let goal = subst [a,`a:int64`; k,`k:num`]
      `read (memory :> bytes32 a) s10 = word(EL k huf_algotime)` in
    SUBGOAL_THEN goal ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(a,a')) SUBST1_TAC THENL
       [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] in
  MAP_EVERY one forms;;

(*** The result: the comparison of the estimates t0 (in w0) and t1 + t1 ***)
(*** DIV 32 (in w1, from v1), as numbers modulo 2^32                    ***)

let SEL_RESULT_TAC (t0:term) (t1:term) : tactic =
  let wz = `val (word_zx (word (dsize DIV 256):int64):int32)` in
  ABBREV_TAC (mk_eq(`w0:int32`,subst [wz,`d:num`] t0)) THEN
  ABBREV_TAC (mk_eq(`v1:int32`,subst [wz,`d:num`] t1)) THEN
  ABBREV_TAC `w1:int32 = word_add v1 (word_ushr v1 5)` THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[SEL_HI] THEN AP_TERM_TAC THEN
  REWRITE_TAC[huf_select_decoder] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MAP_EVERY EXPAND_TAC ["w1"; "v1"; "w0"] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD; VAL_WORD_ZX_GEN;
              DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[COND_SWAP] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];;

let SEL_TAC : tactic =
  REWRITE_TAC[GSYM puff_memsafe] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `csize < dsize` THENL
   [SEL_STEPS_TAC (1--10) THEN PUFF_ADRP_TAC THEN
    MP_TAC(MP (SPECL [`dsize:num`; `csize:num`] SEL_ROW)
              (CONJ (ASSUME `csize < dsize`) (ASSUME `dsize < 2 EXP 64`)))
    THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th -> FA_STATE_REWRITE_TAC[th])
                                    ASSUME_TAC) THEN
    ABBREV_TAC `q = ((16 * csize) MOD 2 EXP 64) DIV dsize` THEN
    MAP_EVERY (fun j ->
      let k = if j = 0 then `4 * q`
              else mk_binop `(+):num->num->num` `4 * q` (mk_small_numeral j) in
      MP_TAC(SPECL [`s10:armstate`; `pc:num`; k] HUF_ALGOTIME_READ) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [UNDISCH_TAC `q < 16` THEN ARITH_TAC; DISCH_TAC])
     [0;1;2;3] THEN
    ABBREV_TAC `tbl = word_add (word pc) (word 31744):int64` THEN
    SEL_READS_TAC THEN SEL_STEPS_TAC (11--19) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `tbl:int64`)) THEN
    SEL_RESULT_TAC
     `word (val (word (EL (4 * q) huf_algotime):int32) +
            val (word (EL (4 * q + 1) huf_algotime):int32) * d):int32`
     `word (val (word (EL (4 * q + 2) huf_algotime):int32) +
            val (word (EL (4 * q + 3) huf_algotime):int32) * d):int32`;
    SEL_STEPS_TAC (1--13) THEN
    SEL_RESULT_TAC `word (1412 + 185 * d):int32` `word (1695 + 202 * d):int32`
    THEN REWRITE_TAC[huf_algotime] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];;

let HUF_SELECTDECODER_CORRECT = prove(sel_goal, SEL_TAC);;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress4X_hufOnly_wksp at 0x73e0                                   *)
(* (HUF_DECOMPRESS4X_HUFONLY_WKSP_CORRECT): the errors for no output or no   *)
(* input, the call of HUF_selectDecoder, then for each kind of table the     *)
(* call of its reader, its error or the error for no streams after the       *)
(* description, and the tail call of the four-stream decoding with that      *)
(* table.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** HUF_decompress4X_hufOnly_wksp at 0x73e0: the description of the      ***)
(*** tree at the start of the input read into the table at dtable by      ***)
(*** HUF_readDTableX1_wksp or HUF_readDTableX2_wksp, as HUF_selectDecoder ***)
(*** chooses, then the four streams after it decoded by the four-stream   ***)
(*** decoding with the same kind of table, by a tail call                 ***)

let hufonly_goal =
 `!pc returnaddress stackpointer dtable dst n src (l:byte list) wk wsz flags
    (dtd:int32) mtl fcpy fset ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\
     ~(stackpointer = word 336) /\ ~(stackpointer = word 432) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     val dtd MOD 256 = mtl /\ mtl <= 12 /\
     n < 2 EXP 28 /\ val(dst:int64) + n + 3 < 2 EXP 64 /\ ~(val dst = 0) /\
     LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 2124 <= 2 EXP 64 /\
     nonoverlapping (dtable:int64,4 + 4 * 2 EXP mtl) (wk,2124) /\
     nonoverlapping (dtable,4 + 4 * 2 EXP mtl)
                    (word_sub stackpointer (word 816),816) /\
     nonoverlapping (dtable,4 + 4 * 2 EXP mtl) (word pc,0x20018) /\
     nonoverlapping (dtable,4 + 4 * 2 EXP mtl) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (word_sub stackpointer (word 816),816) /\
     nonoverlapping (wk,2124) (word pc,0x20018) /\
     nonoverlapping (wk,2124) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 816),816)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 816),816) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 816),816) (ea,el) /\
     nonoverlapping (dst,n) (src,LENGTH l) /\
     nonoverlapping (dst,n) (dtable,4 + 4 * 2 EXP mtl) /\
     nonoverlapping (dst,n) (word_sub stackpointer (word 816),816) /\
     nonoverlapping (dst,n) (word pc,0x20018) /\
     nonoverlapping (src,LENGTH l) (word pc,0x20018)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x73e0) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dtable; dst; word n; src; word(LENGTH l); wk; wsz;
                            flags] s /\
               read (memory :> bytes32 dtable) s = dtd /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (2124 <= val(wsz:int64) /\
                (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
                ==> !out. LENGTH out = n /\ huf_decompress4x1 T l out
                          ==> read X0 s = word n /\
                              read (memory :> bytes(dst,n)) s =
                              num_of_bytelist out) /\
               (read X0 s = word n \/ zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; dtable,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 816),816;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128;
                       word(pc + 0x7c00),256]
                      [dtable,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 816),816; dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dtable,4 + 4 * 2 EXP mtl);
             memory :> bytes(wk,2124);
             memory :> bytes(word_sub stackpointer (word 816),816);
             memory :> bytes(dst,n)])`;;

(*** The start: the registers saved and restored, the arguments, and the ***)
(*** size of the table abbreviated (NONOVERLAPPING_TAC does not use the  ***)
(*** facts with powers of variables)                                     ***)

let HO_START_TAC =
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
  ENSURES_PRESERVED_TAC "x28" `X28` THEN
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `2 * 2 EXP (mtl + 1) = 4 * 2 EXP mtl /\ 1 <= 2 EXP mtl /\
                2 EXP mtl <= 4096`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXP_ADD; ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBST1_TAC(ARITH_RULE `4096 = 2 EXP 12`) THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tm = 2 EXP mtl`;;

(*** The frame of 64 bytes, and the stack regions of the functions ***)
(*** called, as parts of the stack region of 816 bytes             ***)

let HO_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 64)) (word 64):int64 = stackpointer`;;

let HO_STACK_REBASE = map WORD_RULE
 [`word_sub stackpointer (word 64):int64 =
   word_add (word_sub stackpointer (word 816)) (word 752)`;
  `word_sub stackpointer (word 496):int64 =
   word_add (word_sub stackpointer (word 816)) (word 320)`;
  `word_sub stackpointer (word 592):int64 =
   word_add (word_sub stackpointer (word 816)) (word 224)`;
  `word_sub stackpointer (word 688):int64 =
   word_add (word_sub stackpointer (word 816)) (word 128)`];;

let HO_FRAME_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE(WORD_ADD_ASSOC_NUM :: HO_STACK_REBASE) th)
    else th) THEN MONOTONE_MAYCHANGE_TAC;;

(*** No input or output: errors, and no valid block either ***)

let HUF_DECOMPRESS4X1_FACTS = prove
 (`!(l:byte list) out.
     huf_decompress4x1 T l out
     ==> 6 <= LENGTH out /\
         ?ws ml h. huf_weights T l ws ml h /\ h < LENGTH l /\
                   huf_streams4 T ws ml (zstd_sublist l h (LENGTH l - h)) out`,
  REWRITE_TAC[huf_decompress4x1] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:num list` (X_CHOOSE_THEN `ml:num`
    (X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `huf_streams4 T ws ml (zstd_sublist l h (LENGTH l - h)) out`
    THEN REWRITE_TAC[huf_streams4] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC[];
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[]]);;

let HO_NOOUT_TAC : tactic =
  SEL_STEPS_TAC (1--3) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  MESON_TAC[HUF_DECOMPRESS4X1_FACTS; ARITH_RULE `~(6 <= 0)`];;

let HO_NOIN_TAC : tactic =
  SEL_STEPS_TAC (6--10) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[HO_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HUF_DECOMPRESS4X1_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    HO_FRAME_TAC];;

(*** The call of HUF_selectDecoder at 0x741c, and the decoder chosen ***)

let HUF_SELECT_DECODER_01 = prove
 (`!d c. huf_select_decoder d c = 0 \/ huf_select_decoder d c = 1`,
  REWRITE_TAC[huf_select_decoder] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let HO_SEL_TAC : tactic =
  SEL_STEPS_TAC (11--16) THEN EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x7420):int64`; `n:num`; `LENGTH(l:byte list)`]
   HUF_SELECTDECODER_CORRECT))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  ARM_BIGSTEP_TAC SEL_EXEC "s17" THEN EVENTS_UNABBREV_TAC THEN
  MP_TAC(SPECL [`n:num`; `LENGTH(l:byte list)`] HUF_SELECT_DECODER_01) THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th ->
    FA_STATE_REWRITE_TAC[th] THEN ASSUME_TAC th)) THEN
  SEL_STEPS_TAC (18--24);;

(*** The header byte 0 of the table, mtl ***)

let HO_BYTE0 = prove
 (`!dtd:int32 mtl.
     val dtd MOD 256 = mtl ==> word_subword dtd (0,8):byte = word mtl`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1; MOD_MOD_REFL]);;

(*** The call of HUF_readDTableX1_wksp at 0x7484, with the flags as a   ***)
(*** 32-bit int (flags' in the goal) and the header byte 0 of the table ***)
(*** from its first word dtd                                            ***)

let HO_RD1_CALL_TAC : tactic =
  FIRST_ASSUM(fun th ->
    if concl th = `read (memory :> bytes32 dtable) s24 = dtd` then
     ASSUME_TAC(TRANS (MATCH_MP READ_MEMORY_BYTES8_0_OF_32 th)
                (MATCH_MP HO_BYTE0 (ASSUME `val(dtd:int32) MOD 256 = mtl`)))
    else NO_TAC) THEN
  SEL_STEPS_TAC (25--26) THEN
  SUBGOAL_THEN `~(word_sub stackpointer (word 64):int64 = word 272)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 64) = word 272 <=>
                           x = word 336`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(wk:int64) + 1492 <= 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `val(wk:int64) + 2124 <= 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[ASSUME `2 * 2 EXP (mtl + 1) = 4 * tm`;
                                  ASSUME `2 EXP mtl = tm`]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x7488):int64`;
    `word_sub stackpointer (word 64):int64`; `dtable:int64`; `src:int64`;
    `l:byte list`; `wk:int64`; `wsz:int64`;
    `word_zx(word_zx(flags':int64):int32):int64`; `mtl:num`;
    `fcpy:int64`; `fset:int64`; `ea:int64`; `el:num`; `ev:num`]
   HUF_READDTABLEX1_WKSP_CORRECT)))) THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM] THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC
                      NUM_LE_CONV)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC SEL_EXEC "s27" THEN EVENTS_UNABBREV_TAC;;

(*** The call of HUF_readDTableX2_wksp at 0x7440 ***)

let HO_RD2_CALL_TAC : tactic =
  SEL_STEPS_TAC (25--26) THEN
  SUBGOAL_THEN `~(word_sub stackpointer (word 64):int64 = word 368)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 64) = word 368 <=>
                           x = word 432`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[ASSUME `2 EXP mtl = tm`]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x7444):int64`;
    `word_sub stackpointer (word 64):int64`; `dtable:int64`; `src:int64`;
    `l:byte list`; `wk:int64`; `wsz:int64`;
    `word_zx(word_zx(flags':int64):int32):int64`; `dtd:int32`; `mtl:num`;
    `fcpy:int64`; `fset:int64`; `ea:int64`; `el:num`; `ev:num`]
   HUF_READDTABLEX2_WKSP_CORRECT)))) THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM] THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC
                      NUM_LE_CONV)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC SEL_EXEC "s27" THEN EVENTS_UNABBREV_TAC;;

(*** The error of a reader returned (0x74cc), for a workspace too small, ***)
(*** no description of a tree or a table log too large (ml above mtl + 1 ***)
(*** for the single-symbol table, above mtl for the double-symbol one)   ***)

let HO_POST_ERROR1 = prove
 (`!(l:byte list) (wsz:int64) mtl n (P:byte list->bool).
     ~(1492 <= val wsz /\ ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl + 1)
     ==> (2124 <= val wsz /\ (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
          ==> !out. LENGTH out = n /\ huf_decompress4x1 T l out ==> P out)`,
  REWRITE_TAC[huf_decompress4x1] THEN
  MESON_TAC[ARITH_RULE `2124 <= x ==> 1492 <= x`;
            ARITH_RULE `m <= t ==> m <= t + 1`]);;

let HO_POST_ERROR2 = prove
 (`!(l:byte list) (wsz:int64) mtl n (P:byte list->bool).
     ~(2124 <= val wsz /\ ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl)
     ==> (2124 <= val wsz /\ (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
          ==> !out. LENGTH out = n /\ huf_decompress4x1 T l out ==> P out)`,
  REWRITE_TAC[huf_decompress4x1] THEN MESON_TAC[]);;

let HO_ERROR_TAC (pth:thm) : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s27 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s27 = x0r`] THEN
  SEL_STEPS_TAC (28--29) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  SEL_STEPS_TAC (30--34) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[HO_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC pth THEN ASM_REWRITE_TAC[]; HO_FRAME_TAC];;

(*** The weights ws, ml with a description of h bytes, and the table for ***)
(*** the table log tl at dtable + 4: MAX ml (MIN (mtl + 1) 11) for the   ***)
(*** single-symbol table, huf_tablelog2 mtl ml for the double-symbol one ***)

let HO_TL1_FACTS = prove
 (`!ml mtl. 1 <= ml /\ ml <= 12 /\ ml <= mtl + 1
            ==> ml <= MAX ml (MIN (mtl + 1) 11) /\
                1 <= MAX ml (MIN (mtl + 1) 11) /\
                MAX ml (MIN (mtl + 1) 11) <= 12 /\
                MAX ml (MIN (mtl + 1) 11) <= mtl + 1`,
  REWRITE_TAC[MAX; MIN] THEN ARITH_TAC);;

let HO_TL2_FACTS = prove
 (`!ml mtl. 1 <= ml /\ ml <= 12 /\ ml <= mtl /\ mtl <= 12
            ==> ml <= huf_tablelog2 mtl ml /\ 1 <= huf_tablelog2 mtl ml /\
                huf_tablelog2 mtl ml <= 12 /\ huf_tablelog2 mtl ml <= mtl`,
  REWRITE_TAC[huf_tablelog2] THEN ARITH_TAC);;

let HO_WEIGHTS_PRE_TAC (dtab:term) (tlth:thm) (tlt:term) : tactic =
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ws:num list` (X_CHOOSE_THEN `ml:num`
      (X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC))) o
    check (fun th -> is_conj(concl th) && is_exists(rand(concl th)))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) dtab)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`ws:num list`; `ml:num`; `h:num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUF_WEIGHTS_FACTS) THEN
  MP_TAC(SPECL [`ml:num`; `mtl:num`] tlth) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC (mk_eq(`tl:num`,tlt));;

let HO_WEIGHTS_POST_TAC : tactic =
  SUBGOAL_THEN `h < 2 EXP 24` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`h <= LENGTH(l:byte list)`;
                           `LENGTH(l:byte list) < 2 EXP 24`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SEL_STEPS_TAC (28--29);;

let HO_RD1_WEIGHTS_TAC : tactic =
  HO_WEIGHTS_PRE_TAC `huf_dtable` HO_TL1_FACTS
    `MAX ml (MIN (mtl + 1) 11)` THEN
  SUBGOAL_THEN `2 * 2 EXP tl <= 4 * tm` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `2 EXP mtl = tm`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MATCH_MP_TAC(ARITH_RULE `x <= 2 * y ==> 2 * x <= 4 * y`) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  HO_WEIGHTS_POST_TAC;;

let HO_RD2_WEIGHTS_TAC : tactic =
  HO_WEIGHTS_PRE_TAC `huf_dtable2` HO_TL2_FACTS `huf_tablelog2 mtl ml` THEN
  SUBGOAL_THEN `4 * 2 EXP tl <= 4 * tm` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `2 EXP mtl = tm`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  HO_WEIGHTS_POST_TAC;;

(*** No streams after the description: the error -72 at 0x74e0 ***)

let HO_POST_SHORT = prove
 (`!(l:byte list) ws ml h out.
     huf_weights T l ws ml h /\ LENGTH l <= h ==> ~huf_decompress4x1 T l out`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[huf_decompress4x1; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ws':num list`; `ml':num`; `h':num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`h' < LENGTH(l:byte list)`; `h':num = h`;
                         `LENGTH(l:byte list) <= h`] THEN
  ARITH_TAC);;

let HO_SHORT_TAC : tactic =
  SUBGOAL_THEN `!out. ~huf_decompress4x1 T (l:byte list) out` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HO_POST_SHORT THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SEL_STEPS_TAC (30--37) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[HO_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN HO_FRAME_TAC;;

(*** The streams after the description: the tail call of the decoding at ***)
(*** 0x5300 or 0x30c0, with the table of sz bytes from dtable + 4, the   ***)
(*** facts for its hypotheses, then its result                           ***)

let HO_STREAM_PRE_TAC (sz:term) : tactic =
  SEL_STEPS_TAC (30--42) THEN FA_STATE_REWRITE_TAC[HO_SP_RESTORE] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [`src:int64`; `l:byte list`; `h:num`; rand w]
    READ_MEMORY_ZSTD_SUBLIST)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_add src (word h):int64) = val src + h`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ADD_NOWRAP THEN
    MAP_EVERY UNDISCH_TAC
     [`h <= LENGTH(l:byte list)`;
      `val(src:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `8 <= val(word_add src (word h):int64) /\
    val(word_add src (word h):int64) + (LENGTH(l:byte list) - h) + 8 <
    2 EXP 64 /\ LENGTH l - h < 2 EXP 32`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`h <= LENGTH(l:byte list)`; `8 <= val(src:int64)`;
      `val(src:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64`;
      `LENGTH(l:byte list) < 2 EXP 24`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let tb = mk_pair(`dtable:int64`,mk_binop `(+):num->num->num` `4` sz)
    and src' = `word_add src (word h):int64,LENGTH(l:byte list) - h` in
    let nv a b = list_mk_icomb "nonoverlapping" [a; b] in
    let facts = list_mk_conj
      [nv `dst:int64,n:num` tb;
       nv `word_sub stackpointer (word 688):int64,688` tb;
       nv `word_sub stackpointer (word 816):int64,816` tb;
       nv src' tb; nv tb `word pc:int64,32000`;
       nv `dst:int64,n:num` src';
       nv `word_sub stackpointer (word 688):int64,688` src';
       nv `word_sub stackpointer (word 816):int64,816` src';
       nv src' `word pc:int64,32000`] in
    SUBGOAL_THEN facts STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC (mk_binop `(<=):num->num->bool` sz `4 * tm`) THEN
      ABBREV_TAC `tt = 2 EXP tl` THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
  SUBGOAL_THEN `pc + 0x8000 <= 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `pc + 0x20018 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC];;

let HO_DEC_CALL_TAC (th:thm) : tactic =
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[LENGTH_ZSTD_SUBLIST]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `dst:int64`;
    `n:num`; `word_add src (word h):int64`;
    `zstd_sublist (l:byte list) h (LENGTH l - h)`;
    `dtable:int64`; `word_zx(word_zx(flags':int64):int32):int64`;
    `ws:num list`; `ml:num`; `tl:num`] th)))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC SEL_EXEC "s43" THEN EVENTS_UNABBREV_TAC;;

let HO_POST_OK = prove
 (`!(l:byte list) ws ml h n (P:byte list->bool).
     huf_weights T l ws ml h /\
     (!out. LENGTH out = n /\
            huf_streams4 T ws ml (zstd_sublist l h (LENGTH l - h)) out
            ==> P out)
     ==> (!out. LENGTH out = n /\ huf_decompress4x1 T l out ==> P out)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `out:byte list` THEN
  REWRITE_TAC[huf_decompress4x1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ws':num list`
    (X_CHOOSE_THEN `ml':num` (X_CHOOSE_THEN `h':num`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let HO_DEC_END_TAC : tactic =
  SUBGOAL_THEN
   `!out. LENGTH out = n /\ huf_decompress4x1 T (l:byte list) out
          ==> read X0 s43 = word n /\
              read (memory :> bytes (dst,n)) s43 = num_of_bytelist out`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HO_POST_OK THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN HO_FRAME_TAC;;

(*** The two paths, with single-symbol and double-symbol tables ***)

let HO_X1_TAC : tactic =
  HO_RD1_CALL_TAC THEN
  ASM_CASES_TAC `1492 <= val(wsz:int64) /\
                 ?ws ml h. huf_weights T (l:byte list) ws ml h /\
                           ml <= mtl + 1` THENL
   [HO_RD1_WEIGHTS_TAC THEN ASM_CASES_TAC `LENGTH(l:byte list) <= h` THENL
     [HO_SHORT_TAC;
      HO_STREAM_PRE_TAC `2 * 2 EXP tl` THEN
      HO_DEC_CALL_TAC HUF_DECOMPRESS4X1_USINGDTABLE_CORRECT THEN
      HO_DEC_END_TAC];
    HO_ERROR_TAC HO_POST_ERROR1];;

let HO_X2_TAC : tactic =
  HO_RD2_CALL_TAC THEN
  ASM_CASES_TAC `2124 <= val(wsz:int64) /\
                 ?ws ml h. huf_weights T (l:byte list) ws ml h /\ ml <= mtl`
  THENL
   [HO_RD2_WEIGHTS_TAC THEN ASM_CASES_TAC `LENGTH(l:byte list) <= h` THENL
     [HO_SHORT_TAC;
      HO_STREAM_PRE_TAC `4 * 2 EXP tl` THEN
      HO_DEC_CALL_TAC HUF_DECOMPRESS4X2_USINGDTABLE_CORRECT THEN
      HO_DEC_END_TAC];
    HO_ERROR_TAC HO_POST_ERROR2];;

let HO_TAC : tactic =
  HO_START_TAC THEN
  ASM_CASES_TAC `n = 0` THENL [HO_NOOUT_TAC; ALL_TAC] THEN
  SEL_STEPS_TAC (1--5) THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 0` THENL [HO_NOIN_TAC; ALL_TAC] THEN
  SEL_STEPS_TAC (6--10) THEN HO_SEL_TAC THENL [HO_X1_TAC; HO_X2_TAC];;

let HUF_DECOMPRESS4X_HUFONLY_WKSP_CORRECT = prove(hufonly_goal, HO_TAC);;

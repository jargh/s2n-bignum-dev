(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The single-stream decoding of Huffman-coded literals with single-symbol   *)
(* tables: zstd's HUF_decompress1X1_DCtx_wksp, compiled by gcc 12 at -O2 for *)
(* AArch64.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_read_dtable_x1_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress1X1_DCtx_wksp at 0x7340 builds the decoding table at dctx   *)
(* from the description of a Huffman tree at the start of the input l at     *)
(* src with HUF_readDTableX1_wksp, called at 0x737c with the workspace wk,   *)
(* and returns its error, if any. The stream is the rest of l, after the h   *)
(* bytes of the description: if there is none, the result is an error        *)
(* (0x73b8), and otherwise the function ends with the tail call of           *)
(* HUF_decompress1X1_usingDTable_internal at 0x73b4, which decodes it to the *)
(* n bytes at dst. The stack frame of 64 bytes is below the 432 bytes of     *)
(* HUF_readDTableX1_wksp, hence the region of 496 bytes below the stack      *)
(* pointer, and its hypothesis on the stack pointer becomes                  *)
(* ~(stackpointer = word 336). For an input that the RFC accepts and a table *)
(* with room for a table log of 11, the result is the output that the RFC    *)
(* gives (HUF_DECOMPRESS1X1_DCTX_WKSP_RFC).                                  *)
(* ------------------------------------------------------------------------- *)

(*** The start: the registers saved and restored, the arguments ***)

let DC_START_TAC =
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
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0";;

(*** The frame of 64 bytes as part of the stack region of 496 bytes ***)

let DC_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 64):int64 =
  word_add (word_sub stackpointer (word 496)) (word 432)`;;

let DC_FRAME_REBASE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE[DC_STACK_REBASE; WORD_ADD_ASSOC_NUM] th)
    else th);;

let DC_FRAME_TAC = DC_FRAME_REBASE_TAC THEN MONOTONE_MAYCHANGE_TAC;;

let DC_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 64)) (word 64):int64 =
  stackpointer`;;

(*** The call of HUF_readDTableX1_wksp at 0x737c, with the argument flags  ***)
(*** as a 32-bit int in X5 (flags is also a constant, so the variable is   ***)
(*** flags' in the goal)                                                   ***)

let DC_CALL_TAC =
  SUBGOAL_THEN `~(word_sub stackpointer (word 64):int64 = word 272)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 64) = word 272 <=>
                           x = word 336`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--16) THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[ASSUME `2 EXP (mtl + 1) = dsz`]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x7380):int64`;
    `word_sub stackpointer (word 64):int64`; `dctx:int64`; `src:int64`;
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
  ARM_BIGSTEP_TAC ZSTD_EXEC "s17" THEN EVENTS_UNABBREV_TAC;;

(* ------------------------------------------------------------------------- *)
(* The error of HUF_readDTableX1_wksp returned, for a workspace too small,   *)
(* no description of a tree or a table log above mtl + 1.                    *)
(* ------------------------------------------------------------------------- *)

let DC_POST_ERROR = prove
 (`!(l:byte list) (wsz:int64) mtl n (P:byte list->bool).
     ~(1492 <= val wsz /\ ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl + 1)
     ==> (1492 <= val wsz /\
          (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl + 1)
          ==> !out. LENGTH out = n /\ huf_decompress1x1 T l out ==> P out)`,
  REWRITE_TAC[huf_decompress1x1] THEN MESON_TAC[]);;

let DC_ERROR_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s17 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s17 = x0r`] THEN
  ZSTD_STEPS_TAC (18--19) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  ZSTD_STEPS_TAC (20--24) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[DC_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DC_POST_ERROR THEN ASM_REWRITE_TAC[]; DC_FRAME_TAC];;

(* ------------------------------------------------------------------------- *)
(* The weights ws, ml with a description of h bytes, ml <= mtl + 1, and the  *)
(* table for tl = MAX ml (MIN (mtl + 1) 11) at dctx + 4.                     *)
(* ------------------------------------------------------------------------- *)

let DC_TL_FACTS = prove
 (`!ml mtl. 1 <= ml /\ ml <= 12 /\ ml <= mtl + 1
            ==> ml <= MAX ml (MIN (mtl + 1) 11) /\
                1 <= MAX ml (MIN (mtl + 1) 11) /\
                MAX ml (MIN (mtl + 1) 11) <= 12 /\
                MAX ml (MIN (mtl + 1) 11) <= mtl + 1`,
  REWRITE_TAC[MAX; MIN] THEN ARITH_TAC);;

let DC_WEIGHTS_TAC =
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ws:num list` (X_CHOOSE_THEN `ml:num`
      (X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC))) o
    check (fun th -> is_conj(concl th) && is_exists(rand(concl th)))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `huf_dtable`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`ws:num list`; `ml:num`; `h:num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUF_WEIGHTS_FACTS) THEN
  MP_TAC(SPECL [`ml:num`; `mtl:num`] DC_TL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tl = MAX ml (MIN (mtl + 1) 11)` THEN
  SUBGOAL_THEN `2 EXP tl <= dsz` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `2 EXP (mtl + 1) = dsz`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `h < 2 EXP 24` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`h <= LENGTH(l:byte list)`;
                           `LENGTH(l:byte list) < 2 EXP 24`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (18--19);;

(*** No stream after the description: the error at 0x73b8 ***)

let DC_POST_SHORT = prove
 (`!(l:byte list) ws ml h out.
     huf_weights T l ws ml h /\ LENGTH l <= h ==> ~huf_decompress1x1 T l out`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[huf_decompress1x1; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ws':num list`; `ml':num`; `h':num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`h' < LENGTH(l:byte list)`; `h':num = h`;
                         `LENGTH(l:byte list) <= h`] THEN
  ARITH_TAC);;

let DC_SHORT_TAC =
  SUBGOAL_THEN `!out. ~huf_decompress1x1 T (l:byte list) out` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DC_POST_SHORT THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (20--27) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[DC_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DC_FRAME_TAC;;

(*** The stream after the description, decoded by the tail call of         ***)
(*** HUF_decompress1X1_usingDTable_internal at 0x73b4                      ***)

let DC_POST_OK = prove
 (`!(l:byte list) ws ml h n (P:byte list->bool) E.
     huf_weights T l ws ml h /\ h < LENGTH l /\
     (!out. LENGTH out = n /\
            huf_stream ws ml (zstd_sublist l h (LENGTH l - h)) out
            ==> P out) /\
     ((!out. LENGTH out = n
             ==> ~huf_stream ws ml (zstd_sublist l h (LENGTH l - h)) out)
      ==> E)
     ==> (!out. LENGTH out = n /\ huf_decompress1x1 T l out ==> P out) /\
         ((!out. LENGTH out = n ==> ~huf_decompress1x1 T l out) ==> E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `out:byte list` THEN REWRITE_TAC[huf_decompress1x1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ws':num list`
      (X_CHOOSE_THEN `ml':num` (X_CHOOSE_THEN `h':num`
        STRIP_ASSUME_TAC)))) THEN
    MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                  `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `out:byte list` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `out:byte list`) THEN
    ASM_REWRITE_TAC[huf_decompress1x1; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`ws:num list`; `ml:num`; `h:num`]) THEN
    ASM_REWRITE_TAC[]]);;

let DC_POST_ALL = prove
 (`!(l:byte list) ws ml h mtl.
     huf_weights T l ws ml h /\ ml <= mtl + 1
     ==> !ws' ml' h'. huf_weights T l ws' ml' h' ==> ml' <= mtl + 1`,
  MESON_TAC[HUF_WEIGHTS_DET]);;

let DC_STREAM_TAC =
  ZSTD_STEPS_TAC (20--31) THEN
  MP_TAC(ISPECL [`src:int64`; `l:byte list`; `h:num`; `s31:armstate`]
    READ_MEMORY_ZSTD_SUBLIST) THEN
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
    2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`h <= LENGTH(l:byte list)`; `8 <= val(src:int64)`;
      `val(src:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping (dst:int64,n) (word_add dctx (word 4),2 * 2 EXP tl)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `2 EXP tl <= dsz` THEN ABBREV_TAC `tt = 2 EXP tl` THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[LENGTH_ZSTD_SUBLIST]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `returnaddress:int64`; `dst:int64`; `n:num`;
    `word_add src (word h):int64`;
    `zstd_sublist (l:byte list) h (LENGTH l - h)`;
    `dctx:int64`; `ws:num list`; `ml:num`; `tl:num`]
   HUF_DECOMPRESS1X1_USINGDTABLE_CORRECT)))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC ZSTD_EXEC "s32" THEN EVENTS_UNABBREV_TAC THEN
  UNDISCH_TAC `2 EXP tl <= dsz` THEN ABBREV_TAC `tt = 2 EXP tl` THEN
  DISCH_TAC THEN PUFF_FINAL_TAC THEN
  CONJ_TAC THENL [ALL_TAC; DC_FRAME_TAC] THEN
  ASM_REWRITE_TAC[DC_SP_RESTORE] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC DC_POST_OK THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[GSYM NOT_LE];
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN MATCH_MP_TAC DC_POST_ALL THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* The whole function, for the input l at src, the decoding table at dctx    *)
(* with room for a table log of mtl + 1, mtl being its header byte 0, the    *)
(* workspace wk of wsz bytes and the n bytes at dst: if wsz is at least 1492 *)
(* and the description of a tree at the start of l, if any, has a table log  *)
(* ml of mtl + 1 at most, the result is n with the output out at dst when    *)
(* huf_decompress1x1 T l out holds for an out of n bytes, and otherwise an   *)
(* error code; for a smaller workspace or a larger ml, it is an error code.  *)
(* The loads are from the input, the table, the workspace, the stack, the    *)
(* GOT entries of memcpy and memset, the region (ea,el) of their contracts   *)
(* and BIT_mask, and the stores to the table, the workspace, the stack and   *)
(* the n bytes at dst.                                                       *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS1X1_DCTX_WKSP_CORRECT = prove
 (`!pc returnaddress stackpointer dctx dst n src (l:byte list) wk wsz flags
    mtl fcpy fset ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 336) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     mtl <= 12 /\ LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 1492 <= 2 EXP 64 /\
     n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64 /\
     nonoverlapping (dctx:int64,4 + 2 * 2 EXP (mtl + 1)) (wk,1492) /\
     nonoverlapping (dctx,4 + 2 * 2 EXP (mtl + 1))
                    (word_sub stackpointer (word 496),496) /\
     nonoverlapping (dctx,4 + 2 * 2 EXP (mtl + 1)) (word pc,0x20018) /\
     nonoverlapping (dctx,4 + 2 * 2 EXP (mtl + 1)) (src,LENGTH l) /\
     nonoverlapping (wk,1492) (word_sub stackpointer (word 496),496) /\
     nonoverlapping (wk,1492) (word pc,0x20018) /\
     nonoverlapping (wk,1492) (src,LENGTH l) /\
     nonoverlapping (wk,1492) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 496),496)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 496),496) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 496),496) (ea,el) /\
     nonoverlapping (dst,n) (src,LENGTH l) /\
     nonoverlapping (dst,n) (dctx,4 + 2 * 2 EXP (mtl + 1)) /\
     nonoverlapping (dst,n) (word pc,0x20018)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x7340) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dctx; dst; word n; src; word(LENGTH l); wk; wsz;
                            flags] s /\
               read (memory :> bytes8 dctx) s = word mtl /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (1492 <= val(wsz:int64) /\
                (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl + 1)
                ==> (!out. LENGTH out = n /\ huf_decompress1x1 T l out
                           ==> read X0 s = word n /\
                               read (memory :> bytes(dst,n)) s =
                               num_of_bytelist out) /\
                    ((!out. LENGTH out = n ==> ~huf_decompress1x1 T l out)
                     ==> zstd_is_error(read X0 s))) /\
               (~(1492 <= val wsz /\
                  (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl + 1))
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; dctx,4 + 2 * 2 EXP (mtl + 1); wk,1492;
                       word_sub stackpointer (word 496),496;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [dctx,4 + 2 * 2 EXP (mtl + 1); wk,1492;
                       word_sub stackpointer (word 496),496; dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dctx,4 + 2 * 2 EXP (mtl + 1));
             memory :> bytes(wk,1492);
             memory :> bytes(word_sub stackpointer (word 496),496);
             memory :> bytes(dst,n)])`,
  DC_START_TAC THEN RD_DSZ_ABBREV_TAC THEN DC_CALL_TAC THEN
  ASM_CASES_TAC `1492 <= val(wsz:int64) /\
                 ?ws ml h. huf_weights T (l:byte list) ws ml h /\
                           ml <= mtl + 1` THENL
   [DC_WEIGHTS_TAC THEN ASM_CASES_TAC `LENGTH(l:byte list) <= h` THENL
     [DC_SHORT_TAC; DC_STREAM_TAC];
    DC_ERROR_TAC]);;

(* ------------------------------------------------------------------------- *)
(* An input l that the RFC accepts with the output out of n bytes, for a     *)
(* table with room for a table log of 11 (mtl at least 10) and a workspace   *)
(* of at least 1492 bytes: the result is n, with out at dst.                 *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS1X1_DCTX_WKSP_RFC = prove
 (`!pc returnaddress stackpointer dctx dst n src (l:byte list) wk wsz flags
    mtl fcpy fset ea el ev e out.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 336) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     mtl <= 12 /\ LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 1492 <= 2 EXP 64 /\
     n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64 /\
     nonoverlapping (dctx:int64,4 + 2 * 2 EXP (mtl + 1)) (wk,1492) /\
     nonoverlapping (dctx,4 + 2 * 2 EXP (mtl + 1))
                    (word_sub stackpointer (word 496),496) /\
     nonoverlapping (dctx,4 + 2 * 2 EXP (mtl + 1)) (word pc,0x20018) /\
     nonoverlapping (dctx,4 + 2 * 2 EXP (mtl + 1)) (src,LENGTH l) /\
     nonoverlapping (wk,1492) (word_sub stackpointer (word 496),496) /\
     nonoverlapping (wk,1492) (word pc,0x20018) /\
     nonoverlapping (wk,1492) (src,LENGTH l) /\
     nonoverlapping (wk,1492) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 496),496)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 496),496) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 496),496) (ea,el) /\
     nonoverlapping (dst,n) (src,LENGTH l) /\
     nonoverlapping (dst,n) (dctx,4 + 2 * 2 EXP (mtl + 1)) /\
     nonoverlapping (dst,n) (word pc,0x20018) /\
     10 <= mtl /\ 1492 <= val(wsz:int64) /\
     LENGTH out = n /\ huf_decompress1x1 F l out
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x7340) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dctx; dst; word n; src; word(LENGTH l); wk; wsz;
                            flags] s /\
               read (memory :> bytes8 dctx) s = word mtl /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               read X0 s = word n /\
               read (memory :> bytes(dst,n)) s = num_of_bytelist out /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; dctx,4 + 2 * 2 EXP (mtl + 1); wk,1492;
                       word_sub stackpointer (word 496),496;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [dctx,4 + 2 * 2 EXP (mtl + 1); wk,1492;
                       word_sub stackpointer (word 496),496; dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dctx,4 + 2 * 2 EXP (mtl + 1));
             memory :> bytes(wk,1492);
             memory :> bytes(word_sub stackpointer (word 496),496);
             memory :> bytes(dst,n)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `dctx:int64`;
    `dst:int64`; `n:num`; `src:int64`; `l:byte list`; `wk:int64`;
    `wsz:int64`; `flags':int64`; `mtl:num`; `fcpy:int64`; `fset:int64`;
    `ea:int64`; `el:num`; `ev:num`; `e:uarch_event list`]
   HUF_DECOMPRESS1X1_DCTX_WKSP_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM)) THEN
  X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `1492 <= val(wsz:int64) /\
    (!ws ml h. huf_weights T (l:byte list) ws ml h ==> ml <= mtl + 1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `out:byte list`; `ws:num list`; `ml:num`;
                  `h:num`] HUF_DECOMPRESS1X1_RFC_TABLELOG) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `10 <= mtl` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let pc,th1 = CONJ_PAIR th in
    let th2,th3 = CONJ_PAIR th1 in
    REWRITE_TAC[pc; th3] THEN MATCH_MP_TAC(CONJUNCT1 th2)) THEN
  ASM_SIMP_TAC[HUF_DECOMPRESS1X1_RFC]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* zstd's HUF_decompress1X_DCtx_wksp, the decoding of Huffman-coded literals *)
(* in a single stream with the description of its tree, compiled by gcc 12   *)
(* at -O2 for AArch64 (HUF_DECOMPRESS1X_DCTX_WKSP_CORRECT), with             *)
(* HUF_decompress1X2_DCtx_wksp, its counterpart for double-symbol tables     *)
(* only (HUF_DECOMPRESS1X2_DCTX_WKSP_CORRECT), and                           *)
(* HUF_decompress1X_usingDTable, the decoding of a single stream with a      *)
(* table already built (HUF_DECOMPRESS1X_USINGDTABLE_X1 and                  *)
(* HUF_DECOMPRESS1X_USINGDTABLE_X2). The first gives an error for no output  *)
(* or an input longer than the output, copies an input as long as the output *)
(* with memcpy and repeats an input of one byte for a longer output with     *)
(* memset; otherwise (an input of 2 to n - 1 bytes for an output of n bytes) *)
(* it reads the description at the start of the input into the table at dctx *)
(* with HUF_readDTableX1_wksp or HUF_readDTableX2_wksp, as HUF_selectDecoder *)
(* chooses from the sizes of the input and the output, and decodes the       *)
(* stream after it with the decoding for that kind of table, by a tail call. *)
(* For such an input l of the n bytes out (huf_decompress1x1 T l out: the    *)
(* description and the stream, in the zstd dialect), a workspace of at least *)
(* 2124 bytes and a table with room for the table log (mtl, the byte 0 of    *)
(* its header, at least the Max_Number_of_Bits of the description, so that   *)
(* mtl = 12 is enough for any description), the result is n with out at dst; *)
(* the result is always n or an error code; and when HUF_selectDecoder       *)
(* chooses single-symbol tables, the result is an error code for an input    *)
(* that does not decode (with double-symbol ones, the decoding accepts some  *)
(* inputs that do not decode). For such an input that the RFC accepts, with  *)
(* mtl at least 11 and such a workspace, the result is the RFC's output      *)
(* (HUF_DECOMPRESS1X_DCTX_WKSP_RFC, and HUF_DECOMPRESS1X2_DCTX_WKSP_RFC for  *)
(* any input of the other function). The loads are from the input, the       *)
(* table, the workspace, the stack, the GOT entries of memcpy and memset,    *)
(* the region (ea,el) of their contracts, BIT_mask, algoTime and the n bytes *)
(* at dst (which the contracts let memcpy and memset read), and the stores   *)
(* to the table, the workspace, the stack and the n bytes at dst; the stack  *)
(* region of 592 bytes covers the frame of 64 bytes and the frames of the    *)
(* readers below it.                                                         *)
(* ========================================================================= *)

needs "arm/proofs/zstd_huf_decode1x2_gcc12_O2.ml";;
needs "arm/proofs/zstd_huf_decompress4x_gcc12_O2.ml";;
needs "arm/proofs/zstd_huf_decompress1x1_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* The code of HUF_decompress1X2_DCtx_wksp at 0x70c4,                        *)
(* HUF_decompress1X_DCtx_wksp at 0x71d0 and HUF_decompress1X_usingDTable at  *)
(* 0x7330, with the entries of memcpy and memset in the procedure linkage    *)
(* table, and its simulation.                                                *)
(* ------------------------------------------------------------------------- *)

let DCX_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc
  [0x640,0x650; 0x660,0x670; 0x70c4,0x7154; 0x71d0,0x7340];;

let DCX_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC DCX_EXEC [n] THEN ZSTD_SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                  WORD_CMP_64_SFLAGS) THEN
                TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let DCX_STEPS_TAC ns = MAP_EVERY DCX_STEP_TAC ns;;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress1X2_DCtx_wksp at 0x70c4                                     *)
(* (HUF_DECOMPRESS1X2_DCTX_WKSP_CORRECT) builds the double-symbol decoding   *)
(* table at dctx from the description of a Huffman tree at the start of the  *)
(* input l at src with HUF_readDTableX2_wksp, called at 0x7100 with the      *)
(* workspace wk, and returns its error, if any. The stream is the rest of l, *)
(* after the h bytes of the description: if there is none, the result is an  *)
(* error (0x713c), and otherwise the function ends with the tail call of     *)
(* HUF_decompress1X2_usingDTable_internal at 0x7138, which decodes it to the *)
(* n bytes at dst. The stack frame of 64 bytes is above the 528 bytes of     *)
(* HUF_readDTableX2_wksp, hence the region of 592 bytes below the stack      *)
(* pointer, and its hypothesis on the stack pointer becomes ~(stackpointer = *)
(* word 432). For an input that the RFC accepts and a table with room for a  *)
(* table log of 11, the result is the output that the RFC gives              *)
(* (HUF_DECOMPRESS1X2_DCTX_WKSP_RFC).                                        *)
(* ------------------------------------------------------------------------- *)

(*** HUF_decompress1X2_DCtx_wksp at 0x70c4: the start, the registers saved ***)
(*** and restored, the arguments, and the size of the table abbreviated    ***)

let D2C_START_TAC =
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
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  ABBREV_TAC `tm = 2 EXP mtl`;;

(*** The frame of 64 bytes above the 528 bytes of HUF_readDTableX2_wksp, ***)
(*** in the stack region of 592 bytes                                    ***)

let D2C_SP_RESTORE = WORD_RULE
 `word_add (word_sub stackpointer (word 64)) (word 64):int64 = stackpointer`;;

let D2C_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 64):int64 =
  word_add (word_sub stackpointer (word 592)) (word 528)`;;

let D2C_FRAME_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE[D2C_STACK_REBASE; WORD_ADD_ASSOC_NUM] th)
    else th) THEN MONOTONE_MAYCHANGE_TAC;;

(*** The call of HUF_readDTableX2_wksp at 0x7100, with the flags as a ***)
(*** 32-bit int (flags' in the goal)                                  ***)

let D2C_CALL_TAC =
  SUBGOAL_THEN `~(word_sub stackpointer (word 64):int64 = word 368)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 64) = word 368 <=>
                           x = word 432`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DCX_STEPS_TAC (1--16) THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[ASSUME `2 EXP mtl = tm`]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x7104):int64`;
    `word_sub stackpointer (word 64):int64`; `dctx:int64`; `src:int64`;
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
  ARM_BIGSTEP_TAC DCX_EXEC "s17" THEN EVENTS_UNABBREV_TAC;;

(*** The error of HUF_readDTableX2_wksp returned, for a workspace too ***)
(*** small, no description of a tree or a table log above mtl         ***)

let D2C_POST_ERROR = prove
 (`!(l:byte list) (wsz:int64) mtl n (P:byte list->bool).
     ~(2124 <= val wsz /\ ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl)
     ==> (2124 <= val wsz /\ (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
          ==> !out. LENGTH out = n /\ huf_decompress1x1 T l out ==> P out)`,
  REWRITE_TAC[huf_decompress1x1] THEN MESON_TAC[]);;

let D2C_ERROR_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s17 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s17 = x0r`] THEN
  DCX_STEPS_TAC (18--19) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  DCX_STEPS_TAC (20--24) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[D2C_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC D2C_POST_ERROR THEN ASM_REWRITE_TAC[]; D2C_FRAME_TAC];;

(*** The weights ws, ml with a description of h bytes, ml <= mtl, and the ***)
(*** table for tl = huf_tablelog2 mtl ml at dctx + 4                      ***)

let D2C_WEIGHTS_TAC : tactic =
  HO_WEIGHTS_PRE_TAC `huf_dtable2` HO_TL2_FACTS `huf_tablelog2 mtl ml` THEN
  SUBGOAL_THEN `4 * 2 EXP tl <= 4 * tm` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `2 EXP mtl = tm`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `h < 2 EXP 24` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`h <= LENGTH(l:byte list)`;
                           `LENGTH(l:byte list) < 2 EXP 24`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DCX_STEPS_TAC (18--19);;

(*** No stream after the description: the error -72 at 0x713c ***)

let D2C_POST_SHORT = prove
 (`!(l:byte list) ws ml h out.
     huf_weights T l ws ml h /\ LENGTH l <= h ==> ~huf_decompress1x1 T l out`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[huf_decompress1x1; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ws':num list`; `ml':num`; `h':num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`h' < LENGTH(l:byte list)`; `h':num = h`;
                         `LENGTH(l:byte list) <= h`] THEN
  ARITH_TAC);;

let D2C_SHORT_TAC =
  SUBGOAL_THEN `!out. ~huf_decompress1x1 T (l:byte list) out` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC D2C_POST_SHORT THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DCX_STEPS_TAC (20--27) THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[D2C_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN D2C_FRAME_TAC;;

(*** The stream after the description, decoded by the tail call of ***)
(*** HUF_decompress1X2_usingDTable_internal at 0x7138              ***)

let D2C_POST_OK = prove
 (`!(l:byte list) ws ml h n (P:byte list->bool).
     huf_weights T l ws ml h /\
     (!out. LENGTH out = n /\
            huf_stream ws ml (zstd_sublist l h (LENGTH l - h)) out
            ==> P out)
     ==> (!out. LENGTH out = n /\ huf_decompress1x1 T l out ==> P out)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `out:byte list` THEN
  REWRITE_TAC[huf_decompress1x1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ws':num list`
    (X_CHOOSE_THEN `ml':num` (X_CHOOSE_THEN `h':num`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`;
                `ws':num list`; `ml':num`; `h':num`] HUF_WEIGHTS_DET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let D2C_STREAM_TAC =
  DCX_STEPS_TAC (20--31) THEN FA_STATE_REWRITE_TAC[D2C_SP_RESTORE] THEN
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
    2 EXP 64 /\ LENGTH l - h < 2 EXP 60`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`h <= LENGTH(l:byte list)`; `8 <= val(src:int64)`;
      `val(src:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64`;
      `LENGTH(l:byte list) < 2 EXP 24`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping (dst:int64,n) (word_add dctx (word 4),4 * 2 EXP tl) /\
    nonoverlapping (dst,n) (word_add src (word h),LENGTH(l:byte list) - h) /\
    nonoverlapping (dst,n) (word pc,32000)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `4 * 2 EXP tl <= 4 * tm` THEN ABBREV_TAC `tt = 2 EXP tl` THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pc + 0x8000 <= 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `pc + 0x20018 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[LENGTH_ZSTD_SUBLIST]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `returnaddress:int64`; `dst:int64`; `n:num`;
    `word_add src (word h):int64`;
    `zstd_sublist (l:byte list) h (LENGTH l - h)`;
    `dctx:int64`; `ws:num list`; `ml:num`; `tl:num`]
   HUF_DECOMPRESS1X2_USINGDTABLE_CORRECT)))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC DCX_EXEC "s32" THEN EVENTS_UNABBREV_TAC THEN
  UNDISCH_TAC `4 * 2 EXP tl <= 4 * tm` THEN ABBREV_TAC `tt = 2 EXP tl` THEN
  DISCH_TAC THEN PUFF_FINAL_TAC THEN
  (CONJ_TAC THENL [ALL_TAC; D2C_FRAME_TAC]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC D2C_POST_OK THEN
  MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `out:byte list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `out:byte list` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `huf_stream`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[];;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress1X2_DCtx_wksp, for the input l at src, the decoding table   *)
(* at dctx with room for a table log of mtl, its header byte 0, the          *)
(* workspace wk of wsz bytes and the n bytes at dst (not at address 0): if   *)
(* wsz is at least 2124 and the description of a tree at the start of l, if *)
(* any, has a table log ml of mtl at most, the result is n with the output   *)
(* out at dst when huf_decompress1x1 T l out holds for an out of n bytes;    *)
(* and the result is always n or an error code. The loads are from the       *)
(* input, the table, the workspace, the stack, the GOT entries of memcpy and *)
(* memset, the region (ea,el) of their contracts and BIT_mask, and the       *)
(* stores to the table, the workspace, the stack and the n bytes at dst.     *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS1X2_DCTX_WKSP_CORRECT = prove
 (`!pc returnaddress stackpointer dctx dst n src (l:byte list) wk wsz flags
    (dtd:int32) mtl fcpy fset ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 432) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     val dtd MOD 256 = mtl /\ mtl <= 12 /\
     LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 2124 <= 2 EXP 64 /\
     n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64 /\ ~(val dst = 0) /\
     nonoverlapping (dctx:int64,4 + 4 * 2 EXP mtl) (wk,2124) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl)
                    (word_sub stackpointer (word 592),592) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (word pc,0x20018) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (word_sub stackpointer (word 592),592) /\
     nonoverlapping (wk,2124) (word pc,0x20018) /\
     nonoverlapping (wk,2124) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 592),592)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (ea,el) /\
     nonoverlapping (dst,n) (src,LENGTH l) /\
     nonoverlapping (dst,n) (dctx,4 + 4 * 2 EXP mtl) /\
     nonoverlapping (dst,n) (word pc,0x20018)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x70c4) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dctx; dst; word n; src; word(LENGTH l); wk; wsz;
                            flags] s /\
               read (memory :> bytes32 dctx) s = dtd /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (2124 <= val(wsz:int64) /\
                (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
                ==> !out. LENGTH out = n /\ huf_decompress1x1 T l out
                          ==> read X0 s = word n /\
                              read (memory :> bytes(dst,n)) s =
                              num_of_bytelist out) /\
               (read X0 s = word n \/ zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592; dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dctx,4 + 4 * 2 EXP mtl);
             memory :> bytes(wk,2124);
             memory :> bytes(word_sub stackpointer (word 592),592);
             memory :> bytes(dst,n)])`,
  D2C_START_TAC THEN D2C_CALL_TAC THEN
  ASM_CASES_TAC `2124 <= val(wsz:int64) /\
                 ?ws ml h. huf_weights T (l:byte list) ws ml h /\ ml <= mtl`
  THENL
   [D2C_WEIGHTS_TAC THEN ASM_CASES_TAC `LENGTH(l:byte list) <= h` THENL
     [D2C_SHORT_TAC; D2C_STREAM_TAC];
    D2C_ERROR_TAC]);;

(*** The RFC's reading from that of zstd: a table log of 11 at most, ***)
(*** hence the hypotheses of the theorem th, those in hyps by the    ***)
(*** assumptions, and its decoding of out                            ***)

let D2C_RFC_TAC (th:thm) (hyps:term) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `dctx:int64`;
    `dst:int64`; `n:num`; `src:int64`; `l:byte list`; `wk:int64`;
    `wsz:int64`; `flags':int64`; `dtd:int32`; `mtl:num`; `fcpy:int64`;
    `fset:int64`; `ea:int64`; `el:num`; `ev:num`; `e:uarch_event list`]
   th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM)) THEN
  X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN hyps (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`l:byte list`; `out:byte list`; `ws:num list`; `ml:num`;
                  `h:num`] HUF_DECOMPRESS1X1_RFC_TABLELOG) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `11 <= mtl` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let fa,rest = partition (is_forall o concl) (CONJUNCTS th) in
    REWRITE_TAC rest THEN MATCH_MP_TAC(hd fa)) THEN
  ASM_SIMP_TAC[HUF_DECOMPRESS1X1_RFC];;

(* ------------------------------------------------------------------------- *)
(* An input l that the RFC accepts with the output out of n bytes, for a     *)
(* table with room for a table log of 11 (mtl at least 11) and a workspace   *)
(* of at least 2124 bytes: the result is n, with out at dst.                 *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS1X2_DCTX_WKSP_RFC = prove
 (`!pc returnaddress stackpointer dctx dst n src (l:byte list) wk wsz flags
    (dtd:int32) mtl fcpy fset ea el ev e out.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 432) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     val dtd MOD 256 = mtl /\ mtl <= 12 /\
     LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 2124 <= 2 EXP 64 /\
     n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64 /\ ~(val dst = 0) /\
     nonoverlapping (dctx:int64,4 + 4 * 2 EXP mtl) (wk,2124) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl)
                    (word_sub stackpointer (word 592),592) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (word pc,0x20018) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (word_sub stackpointer (word 592),592) /\
     nonoverlapping (wk,2124) (word pc,0x20018) /\
     nonoverlapping (wk,2124) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 592),592)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (ea,el) /\
     nonoverlapping (dst,n) (src,LENGTH l) /\
     nonoverlapping (dst,n) (dctx,4 + 4 * 2 EXP mtl) /\
     nonoverlapping (dst,n) (word pc,0x20018) /\
     11 <= mtl /\ 2124 <= val(wsz:int64) /\
     LENGTH out = n /\ huf_decompress1x1 F l out
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x70c4) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dctx; dst; word n; src; word(LENGTH l); wk; wsz;
                            flags] s /\
               read (memory :> bytes32 dctx) s = dtd /\
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
                      [src,LENGTH l; dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592; dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dctx,4 + 4 * 2 EXP mtl);
             memory :> bytes(wk,2124);
             memory :> bytes(word_sub stackpointer (word 592),592);
             memory :> bytes(dst,n)])`,
  D2C_RFC_TAC HUF_DECOMPRESS1X2_DCTX_WKSP_CORRECT
   `2124 <= val(wsz:int64) /\
    (!ws ml h. huf_weights T (l:byte list) ws ml h ==> ml <= mtl)`);;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress1X_usingDTable at 0x7330 (HUF_DECOMPRESS1X_USINGDTABLE_X1   *)
(* and HUF_DECOMPRESS1X_USINGDTABLE_X2): the stream decoded with a table     *)
(* already built, by the single-symbol decoding when the byte 1 of its       *)
(* header is 0 and by the double-symbol one otherwise.                       *)
(* ------------------------------------------------------------------------- *)

(*** HUF_decompress1X_usingDTable at 0x7330: the decoding of a single      ***)
(*** stream with a table already built, by a tail call of the decoding     ***)
(*** for the kind of table that the byte 1 of its header gives (0 for      ***)
(*** single-symbol tables, which HUF_readDTableX1_wksp builds; else        ***)
(*** double-symbol ones, 1 from HUF_readDTableX2_wksp). The byte 1 is read ***)
(*** too, so the table is one region with its header                       ***)

let DISP1_TAC (th:thm) (ftac:tactic) : tactic =
  REWRITE_TAC[GSYM puff_memsafe] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ftac THEN REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  DCX_STEPS_TAC (1--3) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                                    "nonoverlapping" &&
                                    free_in `dst:int64` t &&
                                    free_in `dtable:int64` t
                                with Failure _ -> false) (list_mk_conj
              (map (concl o snd) asl)) in
    let sz = rand(rand t) in
    let sz4 = rand sz in
    SUBGOAL_THEN (list_mk_icomb "nonoverlapping"
                   [`dst:int64,n:num`;
                    mk_pair(`word_add dtable (word 4):int64`,sz4)])
    ASSUME_TAC THENL
     [ABBREV_TAC `tt = 2 EXP tl` THEN NONOVERLAPPING_TAC; ALL_TAC]) THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `returnaddress:int64`; `dst:int64`; `n:num`; `src:int64`;
    `st:byte list`; `dtable:int64`; `ws:num list`; `ml:num`; `tl:num`] th)))
  THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC DCX_EXEC "s4" THEN EVENTS_UNABBREV_TAC THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[];;

let HUF_DECOMPRESS1X_USINGDTABLE_X1 = prove
 (`!pc returnaddress dst n src (st:byte list) dtable ws ml tl e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     huf_complete ws ml /\ LENGTH ws <= 256 /\
     ml <= tl /\ 1 <= tl /\ tl <= 12 /\ n < 2 EXP 28 /\
     8 <= val src /\ val src + LENGTH st + 8 < 2 EXP 64 /\
     LENGTH st < 2 EXP 60 /\ val dst + n < 2 EXP 64 /\
     nonoverlapping (dst,n) (src,LENGTH st) /\
     nonoverlapping (dst,n) (dtable,4 + 2 * 2 EXP tl) /\
     nonoverlapping (dst,n) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x7330) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; word n; src; word(LENGTH st); dtable] s /\
               read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
               read (memory :> bytes8(word_add dtable (word 1))) s = word 0 /\
               read (memory :> bytes8(word_add dtable (word 2))) s = word tl /\
               read (memory :> bytes(word_add dtable (word 4),2 * 2 EXP tl))
                    s =
               num_of_bytelist(huf_dtable ws ml tl) /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!out. LENGTH out = n /\ huf_stream ws ml st out
                      ==> read X0 s = word n /\
                          read (memory :> bytes(dst,n)) s =
                          num_of_bytelist out) /\
               ((!out. LENGTH out = n ==> ~huf_stream ws ml st out)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH st; dtable,4 + 2 * 2 EXP tl] [dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(dst,n)])`,
  DISP1_TAC HUF_DECOMPRESS1X1_USINGDTABLE_CORRECT ALL_TAC);;

let HUF_DECOMPRESS1X_USINGDTABLE_X2 = prove
 (`!pc returnaddress dst n src (st:byte list) dtable ws ml tl (ttype:byte) e.
     aligned 4096 (word pc:int64) /\ pc + 0x8000 <= 2 EXP 64 /\
     ~(ttype = word 0) /\
     huf_complete ws ml /\ LENGTH ws <= 256 /\
     1 <= ml /\ ml <= tl /\ tl <= 12 /\ n < 2 EXP 28 /\
     8 <= val src /\ val src + LENGTH st + 8 < 2 EXP 64 /\
     LENGTH st < 2 EXP 60 /\ val dst + n < 2 EXP 64 /\ ~(val dst = 0) /\
     nonoverlapping (dst,n) (src,LENGTH st) /\
     nonoverlapping (dst,n) (dtable,4 + 4 * 2 EXP tl) /\
     nonoverlapping (dst,n) (word pc,32000)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x7330) /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; word n; src; word(LENGTH st); dtable] s /\
               read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
               read (memory :> bytes8(word_add dtable (word 1))) s = ttype /\
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
                      [src,LENGTH st; dtable,4 + 4 * 2 EXP tl] [dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(dst,n)])`,
  DISP1_TAC HUF_DECOMPRESS1X2_USINGDTABLE_CORRECT
   (FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM VAL_EQ_0] o
      check (fun th -> concl th = `~(ttype:byte = word 0)`))));;

(* ------------------------------------------------------------------------- *)
(* HUF_decompress1X_DCtx_wksp at 0x71d0                                      *)
(* (HUF_DECOMPRESS1X_DCTX_WKSP_CORRECT): the errors for no output or an      *)
(* input longer than the output, the copy of an input as long as the output  *)
(* by memcpy and the repetition of an input of one byte (for a longer        *)
(* output) by memset (both called through the procedure linkage table), the  *)
(* call of HUF_selectDecoder, then for each kind of table the call of its    *)
(* reader, its error or the error for no stream after the description, and   *)
(* the tail call of the single-stream decoding with that table. With single- *)
(* symbol tables chosen, an input that does not decode gives an error. For   *)
(* an input of more than one byte and fewer than n that the RFC accepts, a   *)
(* table with room for a table log of 11 and a workspace of at least 2124    *)
(* bytes, the result is the output that the RFC gives                        *)
(* (HUF_DECOMPRESS1X_DCTX_WKSP_RFC).                                         *)
(* ------------------------------------------------------------------------- *)

(*** HUF_decompress1X_DCtx_wksp at 0x71d0: no output an error; an input  ***)
(*** longer than the output an error; an input as long as the output     ***)
(*** copied by memcpy (not compressed), an input of one byte repeated by ***)
(*** memset; otherwise the description of the tree read into the table   ***)
(*** at dctx by HUF_readDTableX1_wksp or HUF_readDTableX2_wksp, as       ***)
(*** HUF_selectDecoder chooses, then the stream after it decoded with    ***)
(*** the same kind of table, by a tail call                              ***)

let dcx_goal =
 `!pc returnaddress stackpointer dctx dst n src (l:byte list) wk wsz flags
    (dtd:int32) mtl fcpy fset ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\
     ~(stackpointer = word 336) /\ ~(stackpointer = word 432) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     val dtd MOD 256 = mtl /\ mtl <= 12 /\
     n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64 /\ ~(val dst = 0) /\
     LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 2124 <= 2 EXP 64 /\
     nonoverlapping (dctx:int64,4 + 4 * 2 EXP mtl) (wk,2124) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl)
                    (word_sub stackpointer (word 592),592) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (word pc,0x20018) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (word_sub stackpointer (word 592),592) /\
     nonoverlapping (wk,2124) (word pc,0x20018) /\
     nonoverlapping (wk,2124) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 592),592)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (ea,el) /\
     nonoverlapping (dst,n) (src,LENGTH l) /\
     nonoverlapping (dst,n) (dctx,4 + 4 * 2 EXP mtl) /\
     nonoverlapping (dst,n) (word_sub stackpointer (word 592),592) /\
     nonoverlapping (dst,n) (word pc,0x20018) /\
     nonoverlapping (dst,n) (ea,el)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x71d0) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dctx; dst; word n; src; word(LENGTH l); wk; wsz;
                            flags] s /\
               read (memory :> bytes32 dctx) s = dtd /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (n = LENGTH l /\ ~(n = 0)
                ==> read X0 s = word n /\
                    read (memory :> bytes(dst,n)) s = num_of_bytelist l) /\
               (LENGTH l = 1 /\ 1 < n
                ==> read X0 s = word n /\
                    read (memory :> bytes(dst,n)) s =
                    num_of_bytelist(REPLICATE n (EL 0 l))) /\
               (1 < LENGTH l /\ LENGTH l < n /\ 2124 <= val(wsz:int64) /\
                (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
                ==> !out. LENGTH out = n /\ huf_decompress1x1 T l out
                          ==> read X0 s = word n /\
                              read (memory :> bytes(dst,n)) s =
                              num_of_bytelist out) /\
               (read X0 s = word n \/ zstd_is_error(read X0 s)) /\
               (n = 0 \/ n < LENGTH l ==> zstd_is_error(read X0 s)) /\
               (1 < LENGTH l /\ LENGTH l < n /\
                huf_select_decoder n (LENGTH l) = 0 /\
                (!out. LENGTH out = n ==> ~huf_decompress1x1 T l out)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128;
                       word(pc + 0x7c00),256; dst,n]
                      [dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592; dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dctx,4 + 4 * 2 EXP mtl);
             memory :> bytes(wk,2124);
             memory :> bytes(word_sub stackpointer (word 592),592);
             memory :> bytes(dst,n)])`;;

(*** The bytes of a region all set to b ***)

let READ_MEMORY_BYTES_REPLICATE = prove
 (`!(a:int64) n (b:byte) s.
        (!i. i < n ==> read (memory :> bytes8(word_add a (word i))) s = b)
        ==> read (memory :> bytes(a,n)) s = num_of_bytelist(REPLICATE n b)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_MEMORY_BYTES_0; REPLICATE; num_of_bytelist];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:byte`; `s:armstate`] THEN DISCH_TAC THEN
  REWRITE_TAC[ADD1; REPLICATE_SNOC] THEN
  MP_TAC(ISPECL [`a:int64`; `REPLICATE n (b:byte)`; `b:byte`; `s:armstate`]
    READ_MEMORY_BYTELIST_SNOC) THEN
  REWRITE_TAC[LENGTH_REPLICATE] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(*** The start: the registers saved and restored, the arguments, and the ***)
(*** size of the table abbreviated                                       ***)

let DX_START_TAC =
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
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun (k,f) ->
    let t = subst [mk_small_numeral k,`k:num`; f,`f:int64`]
      `read (memory :> bytes64 (word(pc + k))) s0 = f` in
    ASSUME_TAC(REWRITE_RULE[SPECL [`pc:num`; mk_small_numeral k] WORD_ADD]
                 (ASSUME t)))
   [131072,`fcpy:int64`; 131088,`fset:int64`] THEN
  SUBGOAL_THEN `2 * 2 EXP (mtl + 1) = 4 * 2 EXP mtl /\ 1 <= 2 EXP mtl /\
                2 EXP mtl <= 4096`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXP_ADD; ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBST1_TAC(ARITH_RULE `4096 = 2 EXP 12`) THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tm = 2 EXP mtl`;;

(*** The frame of 64 bytes above the stack regions of the readers, in the ***)
(*** stack region of 592 bytes                                            ***)

let DX_STACK_REBASE = map WORD_RULE
 [`word_sub stackpointer (word 64):int64 =
   word_add (word_sub stackpointer (word 592)) (word 528)`;
  `word_sub stackpointer (word 496):int64 =
   word_add (word_sub stackpointer (word 592)) (word 96)`];;

let DX_FRAME_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
          (REWRITE_RULE(WORD_ADD_ASSOC_NUM :: DX_STACK_REBASE) th)
    else th) THEN MONOTONE_MAYCHANGE_TAC;;

(*** Calls of memcpy and memset through the procedure linkage table (as  ***)
(*** ZSTD_MEMCPY_TAC and ZSTD_MEMSET_TAC with the code of this function) ***)

let DX_MEMCPY_TAC ths dst src len ret x n =
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> FIRST_ASSUM(fun th -> match strip_comb(concl th) with
      Const("memcpy_memsafe_contract",_),[_;_;_;_] ->
        MP_TAC(EVENTS_SPEC gl (SPECL [dst; src; len; ret; x]
          (REWRITE_RULE[memcpy_memsafe_contract] th)))
    | _ -> NO_TAC)) THEN
  REWRITE_TAC ths THEN ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC DCX_EXEC ("s"^string_of_int n) THEN EVENTS_UNABBREV_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC);;

let DX_MEMSET_TAC ths dst c len ret n =
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> FIRST_ASSUM(fun th -> match strip_comb(concl th) with
      Const("memset_memsafe_contract",_),[_;_;_;_] ->
        MP_TAC(EVENTS_SPEC gl (SPECL [dst; c; len; ret]
          (REWRITE_RULE[memset_memsafe_contract] th)))
    | _ -> NO_TAC)) THEN
  REWRITE_TAC ths THEN ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC DCX_EXEC ("s"^string_of_int n) THEN EVENTS_UNABBREV_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC);;

(*** The final state of a path, its postcondition abbreviated (fl_post,  ***)
(*** as FL_ABBREV_POST_TAC) against the substitutions of the simulation, ***)
(*** then each conjunct: by an assumption, the frame, arithmetic, the    ***)
(*** error of a callee, no decoding (an assumption that no output        ***)
(*** decodes under some hypotheses) or an error code as the result       ***)

let DX_END_TAC : tactic =
  let is_err th = is_imp(concl th) &&
                  can (find_term ((=) `zstd_is_error`)) (concl th) in
  let is_nodec th = is_imp(concl th) &&
                    can (find_term ((=) `huf_decompress1x1`))
                        (rand(concl th)) in
  let errs = REWRITE_TAC[zstd_is_error; VAL_WORD; DIMINDEX_64] THEN
             CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC in
  FL_EXPAND_POST_TAC THEN PUFF_FINAL_TAC THEN
  ASM_REWRITE_TAC[D2C_SP_RESTORE] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  (fun (asl,w as gl) -> if maychange_term w then DX_FRAME_TAC gl
                        else ALL_TAC gl) THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC) THEN SIMPLE_ARITH_TAC) THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC) THEN FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(fun th -> if is_err th then MATCH_MP_TAC th
                              else NO_TAC) THEN
      FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(fun th -> if is_nodec th then MP_TAC th
                              else NO_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN errs) THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      TRY errs);;

(*** No output: the error -70 at 0x72b8 ***)

let DX_NOOUT_TAC : tactic =
  FL_ABBREV_POST_TAC THEN DCX_STEPS_TAC (1--3) THEN DX_END_TAC;;

(*** An input longer than the output: the error -20 at 0x72f0 ***)

let DX_LONG_TAC : tactic =
  FL_ABBREV_POST_TAC THEN DCX_STEPS_TAC (1--12) THEN DX_END_TAC;;

(*** An input as long as the output, copied by memcpy (0x7320) ***)

let DX_RAW_TAC : tactic =
  FL_ABBREV_POST_TAC THEN
  DCX_STEPS_TAC (1--17) THEN PUFF_ADRP_TAC THEN DCX_STEPS_TAC (18--20) THEN
  SUBGOAL_THEN `read (memory :> bytes(src,n)) s20 = num_of_bytelist l /\
                val(word n:int64) = n`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `n = LENGTH(l:byte list)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC VAL_WORD_LT64 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DX_MEMCPY_TAC [ASSUME `val(word n:int64) = n`] `dst:int64` `src:int64`
    `word n:int64` `word(pc + 0x7324):int64` `num_of_bytelist l` 21 THEN
  DCX_STEPS_TAC (22--29) THEN DX_END_TAC;;

(*** An input of one byte, repeated by memset (0x72dc) ***)

let DX_ZX_VAL = prove
 (`!b:byte. word_zx (word (val b):int64) = b`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8;
              DIMINDEX_64] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 256 ==> x < 18446744073709551616`]);;

let DX_RLE_TAC : tactic =
  FL_ABBREV_POST_TAC THEN
  MP_TAC(ISPECL [`src:int64`; `l:byte list`; `0`; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] THEN
  DCX_STEPS_TAC (1--19) THEN PUFF_ADRP_TAC THEN DCX_STEPS_TAC (20--22) THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT64 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DX_MEMSET_TAC [ASSUME `val(word n:int64) = n`] `dst:int64`
    `word(val(EL 0 l:byte)):int64` `word n:int64` `word(pc + 0x72e0):int64`
    23 THEN
  SUBGOAL_THEN
   `read (memory :> bytes(dst,n)) s23 = num_of_bytelist(REPLICATE n (EL 0 l))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC READ_MEMORY_BYTES_REPLICATE THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `word_zx:int64->byte`)) (concl th)
      then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[DX_ZX_VAL];
    ALL_TAC] THEN
  DCX_STEPS_TAC (24--30) THEN DX_END_TAC;;

(*** The call of HUF_selectDecoder at 0x721c, and the decoder chosen ***)

let DX_SEL_TAC : tactic =
  FL_ABBREV_POST_TAC THEN
  SUBGOAL_THEN `pc + 0x8000 <= 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `pc + 0x20018 <= 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  DCX_STEPS_TAC (1--20) THEN EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x7220):int64`; `n:num`; `LENGTH(l:byte list)`]
   HUF_SELECTDECODER_CORRECT))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  ARM_BIGSTEP_TAC DCX_EXEC "s21" THEN EVENTS_UNABBREV_TAC THEN
  MP_TAC(SPECL [`n:num`; `LENGTH(l:byte list)`] HUF_SELECT_DECODER_01) THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th ->
    FA_STATE_REWRITE_TAC[th] THEN ASSUME_TAC th)) THEN
  DCX_STEPS_TAC (22--27);;

(*** The calls of the readers at 0x723c (HUF_readDTableX2_wksp) and ***)
(*** 0x727c (HUF_readDTableX1_wksp)                                 ***)

let DX_RD2_CALL_TAC : tactic =
  DCX_STEPS_TAC (28--29) THEN
  SUBGOAL_THEN `~(word_sub stackpointer (word 64):int64 = word 368)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 64) = word 368 <=>
                           x = word 432`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[ASSUME `2 EXP mtl = tm`]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 0x7240):int64`;
    `word_sub stackpointer (word 64):int64`; `dctx:int64`; `src:int64`;
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
  ARM_BIGSTEP_TAC DCX_EXEC "s30" THEN EVENTS_UNABBREV_TAC;;

let DX_RD1_CALL_TAC : tactic =
  FIRST_ASSUM(fun th ->
    if concl th = `read (memory :> bytes32 dctx) s27 = dtd` then
     ASSUME_TAC(TRANS (MATCH_MP READ_MEMORY_BYTES8_0_OF_32 th)
                (MATCH_MP HO_BYTE0 (ASSUME `val(dtd:int32) MOD 256 = mtl`)))
    else NO_TAC) THEN
  DCX_STEPS_TAC (28--29) THEN
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
   [`pc:num`; `word(pc + 0x7280):int64`;
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
  ARM_BIGSTEP_TAC DCX_EXEC "s30" THEN EVENTS_UNABBREV_TAC;;

(*** No decoding when the reader returned an error ***)

let DX_NODEC1 = prove
 (`!(l:byte list) (wsz:int64) mtl.
     ~(1492 <= val wsz /\
       ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl + 1) /\
     2124 <= val wsz /\ (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
     ==> !out. ~huf_decompress1x1 T l out`,
  REWRITE_TAC[huf_decompress1x1] THEN
  MESON_TAC[ARITH_RULE `2124 <= x ==> 1492 <= x`;
            ARITH_RULE `m <= t ==> m <= t + 1`]);;

let DX_NODEC2 = prove
 (`!(l:byte list) (wsz:int64) mtl.
     ~(2124 <= val wsz /\ ?ws ml h. huf_weights T l ws ml h /\ ml <= mtl) /\
     2124 <= val wsz /\ (!ws ml h. huf_weights T l ws ml h ==> ml <= mtl)
     ==> !out. ~huf_decompress1x1 T l out`,
  REWRITE_TAC[huf_decompress1x1] THEN MESON_TAC[]);;

(*** The error of a reader returned (0x72c0) ***)

let DX_ERROR_TAC (nodec:thm) : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s30 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s30 = x0r`] THEN
  DCX_STEPS_TAC (31--32) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  DCX_STEPS_TAC (33--37) THEN
  SUBGOAL_THEN `2124 <= val(wsz:int64) /\
                (!ws ml h. huf_weights T (l:byte list) ws ml h ==> ml <= mtl)
                ==> !out. ~huf_decompress1x1 T l out`
  ASSUME_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC nodec THEN
    MAP_EVERY EXISTS_TAC [`wsz:int64`; `mtl:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DX_END_TAC;;

(*** The weights ws, ml with a description of h bytes, and the table for ***)
(*** the table log tl at dctx + 4                                        ***)

let DX_WEIGHTS_TAC (dtab:term) (tlth:thm) (tlt:term) (szth:term)
                   (sztac:tactic) : tactic =
  HO_WEIGHTS_PRE_TAC dtab tlth tlt THEN
  SUBGOAL_THEN szth ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `2 EXP mtl = tm`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
    sztac;
    ALL_TAC] THEN
  SUBGOAL_THEN `h < 2 EXP 24` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`h <= LENGTH(l:byte list)`;
                           `LENGTH(l:byte list) < 2 EXP 24`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DCX_STEPS_TAC (31--32);;

(*** No stream after the description: the error -72 at 0x7300 ***)

let DX_SHORT_TAC : tactic =
  SUBGOAL_THEN `!out. ~huf_decompress1x1 T (l:byte list) out` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC D2C_POST_SHORT THEN
    MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DCX_STEPS_TAC (33--40) THEN DX_END_TAC;;

(*** No output that decodes, from no such output ***)

let DX_NOTEX = prove
 (`!P Q. ~(?x:A. P x /\ Q x) ==> !x. P x ==> ~Q x`,
  MESON_TAC[]);;

(*** The stream after the description, decoded by the tail call of the ***)
(*** decoding th at 0x72b4 or 0x7274, with the table of sz bytes from  ***)
(*** dctx + 4, the facts for its hypotheses, then its result           ***)

let DX_STREAM_TAC (th:thm) (sz:term) (x1:bool) : tactic =
  DCX_STEPS_TAC (33--44) THEN FA_STATE_REWRITE_TAC[D2C_SP_RESTORE] THEN
  MP_TAC(ISPECL [`src:int64`; `l:byte list`; `h:num`; `s44:armstate`]
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
    2 EXP 64 /\ LENGTH l - h < 2 EXP 60`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`h <= LENGTH(l:byte list)`; `8 <= val(src:int64)`;
      `val(src:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64`;
      `LENGTH(l:byte list) < 2 EXP 24`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let tb = mk_pair(`word_add dctx (word 4):int64`,sz) in
    let nv a b = list_mk_icomb "nonoverlapping" [a; b] in
    SUBGOAL_THEN (list_mk_conj
      [nv `dst:int64,n:num` tb;
       nv `dst:int64,n:num`
          `word_add src (word h):int64,LENGTH(l:byte list) - h`;
       nv `dst:int64,n:num` `word pc:int64,32000`])
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC (mk_binop `(<=):num->num->bool` sz `4 * tm`) THEN
      ABBREV_TAC `tt = 2 EXP tl` THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(REWRITE_RULE[LENGTH_ZSTD_SUBLIST]
                     (EVENTS_SPEC gl (ISPECL
   [`pc:num`; `returnaddress:int64`; `dst:int64`; `n:num`;
    `word_add src (word h):int64`;
    `zstd_sublist (l:byte list) h (LENGTH l - h)`;
    `dctx:int64`; `ws:num list`; `ml:num`; `tl:num`] th)))) THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC DCX_EXEC "s45" THEN EVENTS_UNABBREV_TAC THEN
  (if x1 then
     MP_TAC(SPECL [`l:byte list`; `ws:num list`; `ml:num`; `h:num`; `n:num`;
                   `\out. read X0 s45 = word n /\
                          read (memory :> bytes(dst,n)) s45 =
                          num_of_bytelist out`;
                   `zstd_is_error(read X0 s45)`] DC_POST_OK) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM NOT_LE]; ALL_TAC] THEN
     REWRITE_TAC[] THEN STRIP_TAC THEN
     SUBGOAL_THEN `read X0 s45 = word n \/ zstd_is_error(read X0 s45)`
     ASSUME_TAC THENL
      [ASM_CASES_TAC
        `?out:byte list. LENGTH out = n /\ huf_decompress1x1 T l out` THENL
        [FIRST_X_ASSUM(X_CHOOSE_THEN `out:byte list` STRIP_ASSUME_TAC) THEN
         DISJ1_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `out:byte list` o check (fun th ->
           is_forall(concl th) &&
           can (find_term ((=) `huf_decompress1x1`)) (concl th))) THEN
         ASM_REWRITE_TAC[] THEN SIMP_TAC[];
         DISJ2_TAC THEN
         FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
           can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
         MATCH_MP_TAC DX_NOTEX THEN FIRST_ASSUM ACCEPT_TAC];
       ALL_TAC]
   else
     SUBGOAL_THEN
      `!out. LENGTH out = n /\ huf_decompress1x1 T (l:byte list) out
             ==> read X0 s45 = word n /\
                 read (memory :> bytes(dst,n)) s45 = num_of_bytelist out`
     ASSUME_TAC THENL
      [MATCH_MP_TAC D2C_POST_OK THEN
       MAP_EVERY EXISTS_TAC [`ws:num list`; `ml:num`; `h:num`] THEN
       ASM_REWRITE_TAC[] THEN X_GEN_TAC `out:byte list` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `out:byte list` o check (fun th ->
         is_forall(concl th) &&
         can (find_term ((=) `huf_stream`)) (concl th))) THEN
       ASM_REWRITE_TAC[] THEN SIMP_TAC[];
       ALL_TAC]) THEN
  UNDISCH_TAC (mk_binop `(<=):num->num->bool` sz `4 * tm`) THEN
  ABBREV_TAC `tt = 2 EXP tl` THEN DISCH_TAC THEN DX_END_TAC;;

(*** The two paths, with single-symbol and double-symbol tables ***)

let DX_X1_TAC : tactic =
  DX_RD1_CALL_TAC THEN
  ASM_CASES_TAC `1492 <= val(wsz:int64) /\
                 ?ws ml h. huf_weights T (l:byte list) ws ml h /\
                           ml <= mtl + 1` THENL
   [DX_WEIGHTS_TAC `huf_dtable` HO_TL1_FACTS `MAX ml (MIN (mtl + 1) 11)`
      `2 * 2 EXP tl <= 4 * tm`
      (MATCH_MP_TAC(ARITH_RULE `x <= 2 * y ==> 2 * x <= 4 * y`) THEN
       REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
       REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC) THEN
    ASM_CASES_TAC `LENGTH(l:byte list) <= h` THENL
     [DX_SHORT_TAC;
      DX_STREAM_TAC HUF_DECOMPRESS1X1_USINGDTABLE_CORRECT `2 * 2 EXP tl`
        true];
    DX_ERROR_TAC DX_NODEC1];;

let DX_X2_TAC : tactic =
  DX_RD2_CALL_TAC THEN
  ASM_CASES_TAC `2124 <= val(wsz:int64) /\
                 ?ws ml h. huf_weights T (l:byte list) ws ml h /\ ml <= mtl`
  THENL
   [DX_WEIGHTS_TAC `huf_dtable2` HO_TL2_FACTS `huf_tablelog2 mtl ml`
      `4 * 2 EXP tl <= 4 * tm`
      (REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC)
    THEN
    ASM_CASES_TAC `LENGTH(l:byte list) <= h` THENL
     [DX_SHORT_TAC;
      DX_STREAM_TAC HUF_DECOMPRESS1X2_USINGDTABLE_CORRECT `4 * 2 EXP tl`
        false];
    DX_ERROR_TAC DX_NODEC2];;

let DX_TAC : tactic =
  DX_START_TAC THEN
  ASM_CASES_TAC `n = 0` THENL [DX_NOOUT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n < LENGTH(l:byte list)` THENL [DX_LONG_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) < n` THENL [ALL_TAC; DX_RAW_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 1` THENL [DX_RLE_TAC; ALL_TAC] THEN
  DX_SEL_TAC THENL [DX_X1_TAC; DX_X2_TAC];;

let HUF_DECOMPRESS1X_DCTX_WKSP_CORRECT = prove(dcx_goal, DX_TAC);;

(* ------------------------------------------------------------------------- *)
(* An input l of more than one byte and fewer than n that the RFC accepts    *)
(* with the output out of n bytes, for a table with room for a table log of  *)
(* 11 (mtl at least 11) and a workspace of at least 2124 bytes: the result   *)
(* is n, with out at dst. (Whatever the RFC makes of them, zstd gives an     *)
(* error for an input longer than the output, copies one as long as the      *)
(* output and repeats one of a single byte.)                                 *)
(* ------------------------------------------------------------------------- *)

let HUF_DECOMPRESS1X_DCTX_WKSP_RFC = prove
 (`!pc returnaddress stackpointer dctx dst n src (l:byte list) wk wsz flags
    (dtd:int32) mtl fcpy fset ea el ev e out.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\
     ~(stackpointer = word 336) /\ ~(stackpointer = word 432) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     val dtd MOD 256 = mtl /\ mtl <= 12 /\
     n < 2 EXP 28 /\ val(dst:int64) + n < 2 EXP 64 /\ ~(val dst = 0) /\
     LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(wk:int64) + 2124 <= 2 EXP 64 /\
     nonoverlapping (dctx:int64,4 + 4 * 2 EXP mtl) (wk,2124) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl)
                    (word_sub stackpointer (word 592),592) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (word pc,0x20018) /\
     nonoverlapping (dctx,4 + 4 * 2 EXP mtl) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (word_sub stackpointer (word 592),592) /\
     nonoverlapping (wk,2124) (word pc,0x20018) /\
     nonoverlapping (wk,2124) (src,LENGTH l) /\
     nonoverlapping (wk,2124) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 592),592)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 592),592) (ea,el) /\
     nonoverlapping (dst,n) (src,LENGTH l) /\
     nonoverlapping (dst,n) (dctx,4 + 4 * 2 EXP mtl) /\
     nonoverlapping (dst,n) (word_sub stackpointer (word 592),592) /\
     nonoverlapping (dst,n) (word pc,0x20018) /\
     nonoverlapping (dst,n) (ea,el) /\
     1 < LENGTH l /\ LENGTH l < n /\ 11 <= mtl /\ 2124 <= val(wsz:int64) /\
     LENGTH out = n /\ huf_decompress1x1 F l out
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x71d0) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dctx; dst; word n; src; word(LENGTH l); wk; wsz;
                            flags] s /\
               read (memory :> bytes32 dctx) s = dtd /\
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
                      [src,LENGTH l; dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128;
                       word(pc + 0x7c00),256; dst,n]
                      [dctx,4 + 4 * 2 EXP mtl; wk,2124;
                       word_sub stackpointer (word 592),592; dst,n]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE
            [memory :> bytes(dctx,4 + 4 * 2 EXP mtl);
             memory :> bytes(wk,2124);
             memory :> bytes(word_sub stackpointer (word 592),592);
             memory :> bytes(dst,n)])`,
  D2C_RFC_TAC HUF_DECOMPRESS1X_DCTX_WKSP_CORRECT
   `1 < LENGTH(l:byte list) /\ LENGTH l < n /\ 2124 <= val(wsz:int64) /\
    (!ws ml h. huf_weights T (l:byte list) ws ml h ==> ml <= mtl)`);;

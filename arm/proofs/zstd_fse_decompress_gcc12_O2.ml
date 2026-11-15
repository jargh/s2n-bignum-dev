(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decoding the FSE-coded weights of a Huffman tree description: zstd's      *)
(* FSE_decompress_wksp_bmi2, compiled by gcc 12 at -O2 for AArch64.          *)
(* ========================================================================= *)

needs "arm/proofs/zstd_fse_build_dtable_gcc12_O2.ml";;
needs "arm/proofs/zstd_fse_read_ncount_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* FSE_decompress_wksp_bmi2 decodes the FSE-coded weights of a Huffman tree  *)
(* description, as HUF_readStats calls it, with room for 255 weights, an     *)
(* Accuracy_Log of at most 6 and a workspace of 876 bytes. It reads the      *)
(* table description with FSE_readNCount (at 0x940, through the jump at      *)
(* 0xc60), checks its Accuracy_Log and that the workspace is big enough,     *)
(* builds the decoding table at wksp + 512 with FSE_buildDTable_internal (at *)
(* 0xe80), and decodes the stream after the description with two interleaved *)
(* states, in one of two copies of the decoding: from 0x163c in fastMode,    *)
(* when no probability is half of the states or more, so that every state    *)
(* has at least one bit, and from 0x11e0 otherwise. Each copy starts the     *)
(* stream and reads the two states, decodes 4 weights at a time in a main    *)
(* loop while there is room for them and the container can be reloaded, and  *)
(* 2 at a time in a tail loop until the stream runs out, the weight of the   *)
(* other state being the last one.                                           *)
(*                                                                           *)
(* The table BIT_mask of the image, and the entries of the decoding table.   *)
(* ------------------------------------------------------------------------- *)

(*** The table BIT_mask of 32 words 2^k - 1 at 0x7b70 in the image ***)

let zstd_bit_mask = new_definition
 `zstd_bit_mask = list_of_seq (\k. 2 EXP k - 1) 32`;;

let ZSTD_BIT_MASK_BYTES = prove
 (`num_of_bytelist(SUB_LIST(31600,128) zstd_huf_gcc12_O2_mc) =
   num_of_wordlist(MAP (word:num->int32) zstd_bit_mask)`,
  REWRITE_TAC[zstd_huf_gcc12_O2_mc; zstd_bit_mask] THEN
  CONV_TAC(ONCE_DEPTH_CONV SUB_LIST_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[MAP; num_of_bytelist; num_of_wordlist; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ZSTD_BIT_MASK_LOADED = prove
 (`!s pc. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc
          ==> read (memory :> bytes(word_add (word pc) (word 31600),128)) s =
              num_of_wordlist(MAP (word:num->int32) zstd_bit_mask)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_bytes_loaded] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM ZSTD_BIT_MASK_BYTES] THEN
  MP_TAC(ISPECL [`s:armstate`; `word pc:int64`; `zstd_huf_gcc12_O2_mc`;
                 `31600`; `128`] BYTES_LOADED_SUB_LIST) THEN
  ASM_REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_SUB_LIST;
                  LENGTH_ZSTD_HUF_GCC12_O2_MC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let READ_MEMORY_BYTES32_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int32 list) n j s:armstate.
        read (memory :> bytes(a,4 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes32(word_add a (word(4 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int32 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read (c:(armstate,num)component) s`)
           (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `32 * j = 8 * (4 * j)`;
              ARITH_RULE `4294967296 = 2 EXP (8 * 4)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let ZSTD_BIT_MASK_READ = prove
 (`!s pc k.
        aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\ k < 32
        ==> read (memory :> bytes32
                  (word_add (word_add (word pc) (word 31600)) (word(4 * k))))
                 s = word(2 EXP k - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add (word pc) (word 31600):int64`;
                 `MAP (word:num->int32) zstd_bit_mask`; `32`; `k:num`;
                 `s:armstate`] READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_SIMP_TAC[ZSTD_BIT_MASK_LOADED; ARITH_RULE `4 * 32 = 128`;
               LENGTH_MAP; zstd_bit_mask; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

(*** The entry of the FSE decoding table for a state ***)

let READ_MEMORY_BYTES16_BYTELIST = prove
 (`!a:int64 l i s:armstate.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        i + 2 <= LENGTH l
        ==> val(read (memory :> bytes16(word_add a (word i))) s) =
            val(EL i l) + 256 * val(EL (i + 1) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM READ_MEMORY_BYTES_2] THEN
  REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN
  ONCE_REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  MP_TAC(ISPECL [`a:int64`; `l:byte list`; `i:num`; `s:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  MP_TAC(ISPECL [`a:int64`; `l:byte list`; `i + 1`; `s:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let FSE_DTABLE_READ = prove
 (`!cs tl (tbl:int64) u s.
        5 <= tl /\ tl <= 12 /\ fse_valid cs tl /\ u < 2 EXP tl /\
        read (memory :> bytes(tbl,4 * 2 EXP tl)) s =
        num_of_bytelist(fse_dtable cs tl)
        ==> read (memory :> bytes16 (word_add tbl (word (4 * u)))) s =
            word(fse_base cs tl u) /\
            read (memory :> bytes8 (word_add tbl (word (4 * u + 2)))) s =
            word(fse_symbol cs tl u) /\
            read (memory :> bytes8 (word_add tbl (word (4 * u + 3)))) s =
            word(fse_nbits cs tl u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `u:num`] EL_FSE_DTABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `u:num`] FSE_NBITS_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fse_base cs tl u < 65536` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP tl` THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`2`; `fse_nbits cs tl u`] EXP_EQ_0) THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC;
      TRANS_TAC LE_TRANS `2 EXP 12` THEN ASM_REWRITE_TAC[LE_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    MP_TAC(ISPECL [`tbl:int64`; `fse_dtable cs tl`; `4 * u`; `s:armstate`]
      READ_MEMORY_BYTES16_BYTELIST) THEN
    ASM_REWRITE_TAC[LENGTH_FSE_DTABLE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
    SUBGOAL_THEN `fse_base cs tl u DIV 256 < 256` ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[MOD_LT]] THEN
    REWRITE_TAC[MOD_MOD_REFL] THEN
    MP_TAC(SPECL [`fse_base cs tl u`; `256`] DIVISION) THEN ARITH_TAC;
    MP_TAC(ISPECL [`tbl:int64`; `fse_dtable cs tl`; `4 * u + 2`;
                   `s:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
    ASM_REWRITE_TAC[LENGTH_FSE_DTABLE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    MP_TAC(ISPECL [`tbl:int64`; `fse_dtable cs tl`; `4 * u + 3`;
                   `s:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
    ASM_REWRITE_TAC[LENGTH_FSE_DTABLE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The bits read by the normal copy: the container shifted right by 64 - (bc *)
(* + nb) (the count being negated and taken modulo 64) and masked with       *)
(* BIT_mask[nb], which are the nb bits of the specification below the        *)
(* position 8 * ofs + 64 - bc.                                               *)
(* ------------------------------------------------------------------------- *)

(*** Reading nb bits below the position from the bit container ***)

let ZSTD_BACK_NUM = prove
 (`!(st:byte list) q k.
        k <= q
        ==> zstd_back st q k =
            (num_of_bytelist st DIV 2 EXP (q - k)) MOD 2 EXP k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zstd_back; ZSTD_BITS_NUM; EXP; DIV_1] THEN
  SUBGOAL_THEN `2 EXP q = 2 EXP k * 2 EXP (q - k)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[DIV_MOD] THEN REWRITE_TAC[MULT_SYM]);;

let FD_WINDOW_ARITH = prove
 (`!x a sh nb.
        sh + nb <= 64
        ==> (((x DIV 2 EXP a) MOD 2 EXP 64) DIV 2 EXP sh) MOD 2 EXP nb =
            (x DIV 2 EXP (a + sh)) MOD 2 EXP nb`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN (a + 64) (a + sh + nb) = (a + sh) + nb` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[DIV_DIV; GSYM EXP_ADD]]);;

let FD_SHIFT_NEG = prove
 (`!k. 1 <= k /\ k <= 64
       ==> val(word_zx (word_sub (word 0) (word k):int32):int64) MOD 64 =
           64 - k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx (word_sub (word 0) (word k):int32):int64) =
                4294967296 - k` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `k MOD 4294967296 = k` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> ~(k <= 0)`; ADD_CLAUSES] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 - k = 67108863 * 64 + (64 - k)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let FD_BITS_NORMAL = prove
 (`!(st:byte list) ofs bc nb.
        bc + nb <= 64 /\ nb < 32
        ==> word_and
             (word_jushr
               (word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                     18446744073709551616))
               (word_zx (word_sub (word 0) (word (nb + bc)):int32)))
             (word_zx (word (2 EXP nb - 1):int32)):int64 =
            word(zstd_back st (8 * ofs + 64 - bc) nb)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `nb = 0` THENL
   [ASM_REWRITE_TAC[EXP; SUB_REFL] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_AND_0] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`st:byte list`; `8 * ofs + 64 - bc`; `0`]
      ZSTD_BACK_BOUND) THEN
    REWRITE_TAC[EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_zx (word (2 EXP nb - 1):int32):int64 = word (2 EXP nb - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_32] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= e /\ e <= f ==> e - 1 < f`) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ;
                LE_EXP] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; word_jushr; VAL_WORD_USHR; DIMINDEX_64] THEN
  MP_TAC(SPEC `nb + bc:num` FD_SHIFT_NEG) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`; MOD_MOD_REFL] THEN
  ASM_SIMP_TAC[FD_WINDOW_ARITH;
               ARITH_RULE `bc + nb <= 64 ==> (64 - (nb + bc)) + nb <= 64`] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`st:byte list`; `8 * ofs + 64 - bc`; `nb:num`]
    ZSTD_BACK_NUM) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The decoding. As in the decoder of the literals, the stream st of LENGTH  *)
(* st bytes at src is read backwards: the container holds the 8 bytes from   *)
(* ofs (or all of a shorter stream, with ofs = 0) and bc of its bits have    *)
(* been used, the position being 8 * ofs + 64 - bc. The weights decoded so   *)
(* far, out, are at dst, a and b are the states, a being the next to decode, *)
(* and what the specification reads from there is what it reads from the     *)
(* start, (s1,s2,q0,[]), which is how the decoding is followed. The table is *)
(* at dt + 4, its header at dt. The assertions, for the normal copy and in   *)
(* brackets the fast one, are at:                                            *)
(*                                                                           *)
(*   0x11e0 [0x163c]  fd_i0, the start, with the stream at src               *)
(*   0x1214 [0x1670]  fd_i1, after BIT_initDStream                           *)
(*   0x1284 [0x16e0]  fd_i2, after the read of the first state               *)
(*   0x12e0 [0x173c]  fd_i3, after that of the second                        *)
(*   0x1414 [0x1858]  fd_minv, the main loop, with 4k weights so far         *)
(*   0x1344 [0x1798]  fd_mbody, after its reload                             *)
(*   0x144c [0x1890]  fd_ttail, after the main loop                          *)
(*   0x1470 [0x18ac]  fd_tinv, the tail loop                                 *)
(*   0x14e8 [0x191c]  fd_tmid, after the first weight of an iteration        *)
(*   0x156c [0x1998]  fd_tend, after the second                              *)
(*                                                                           *)
(* and each has a theorem that it leads to the return, with the result as in *)
(* fd_post, or in fd_spost from the start of the stream, proved from those   *)
(* of the later ones. Before 0x1288, x19 holds the workspace wksp rather     *)
(* than the table, which is at wksp + 512.                                   *)
(* ------------------------------------------------------------------------- *)

(*** The decoding part of FSE_decompress_wksp_bmi2, normal mode ***)

let fd_rr =
 `[src,LENGTH(st:byte list); dt,4 + 4 * 2 EXP tl;
   word_add (word pc) (word 31600),128;
   word_sub stackpointer (word 96),96]:(int64#num)list`
and fd_wr = `[dst,255]:(int64#num)list`;;

let fd_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\
  5 <= tl /\ tl <= 6 /\ fse_valid cs tl /\ LENGTH(cs:int list) <= 256 /\
  LENGTH(st:byte list) < 2 EXP 24 /\
  8 <= val(src:int64) /\ val src + LENGTH st + 8 < 2 EXP 64 /\
  val(dst:int64) + 255 < 2 EXP 64 /\
  nonoverlapping (dst,255) (src,LENGTH st) /\
  nonoverlapping (dst,255) (dt:int64,4 + 4 * 2 EXP tl) /\
  nonoverlapping (dst,255) (word pc,0x20018) /\
  nonoverlapping (dst,255) (word_sub stackpointer (word 96),96)`;;

let fd_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X29; X30; SP] ,,
  MAYCHANGE [memory :> bytes(dst,255)]`;;

let fd_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `dst:int64`;
  `src:int64`; `st:byte list`; `dt:int64`; `cs:int list`; `tl:num`;
  `s1:num`; `s2:num`; `q0:num`;
  `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`; `x23:int64`;
  `x24:int64`; `x25:int64`; `x29:int64`; `e:uarch_event list`];;

let mk_fd_goal extra pre post =
  let tm = mk_imp(fd_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; fd_frame]) in
  let vs = fd_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fd_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** At the return: the weights decoded, or an error code ***)

let fd_post = with_memsafe fd_rr fd_wr `\s.
  read PC s = returnaddress /\ read SP s = stackpointer /\
  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
  read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
  read X25 s = x25 /\ read X29 s = x29 /\ read X30 s = returnaddress /\
  (!w. fse_weights cs tl st (s1,s2,q0,[]) w
       ==> read X0 s = word(LENGTH w) /\
           read (memory :> bytes(dst,LENGTH w)) s =
           num_of_bytelist(MAP (word:num->byte) w)) /\
  ((!w. ~fse_weights cs tl st (s1,s2,q0,[]) w)
   ==> zstd_is_error(read X0 s))`;;

(*** The facts that hold all through the decoding ***)

let fd_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read SP s = word_sub stackpointer (word 96) /\
  read (memory :> bytes64 (word_sub stackpointer (word 96))) s = x29 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 8))) s =
  returnaddress /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 16))) s = x19 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 24))) s = x20 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 32))) s = x21 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 40))) s = x22 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 48))) s = x23 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 56))) s = x24 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 96)) (word 64))) s = x25 /\
  read X23 s = dst /\ read X20 s = src /\
  read X8 s = word_add src (word 8) /\
  read X19 s = word_add dt (word 4) /\
  read (memory :> bytes(src,LENGTH st)) s = num_of_bytelist st /\
  read (memory :> bytes(word_add dt (word 4),4 * 2 EXP tl)) s =
  num_of_bytelist(fse_dtable cs tl)`;;

(*** At 0x1470, the loop for the last weights, two at a time, for the  ***)
(*** measure m = 256 - j                                              ***)

let fd_tinv = with_memsafe fd_rr fd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   list_mk_exists([`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`],
    list_mk_conj
     [`m = 256 - LENGTH(out:num list) /\ LENGTH out <= 253 /\
       read PC s = word(pc + 0x1470) /\
       read X3 s = word a /\ read X12 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X4 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X9 s = word_add dst (word(LENGTH out)) /\
       read X10 s = word_add dst (word 253) /\
       read X11 s =
       word_add dst (word(if EVEN(LENGTH out) then 254 else 253)) /\
       read X6 s = word_add (word pc) (word 31600) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fd_common])));;

(* ------------------------------------------------------------------------- *)
(* The loop for the last weights, two at a time. Each weight is preceded by  *)
(* the check that there is room for two, and its state is updated with its   *)
(* bits if there are enough of them, the last weight being that of the other *)
(* state otherwise. The states are read from the table before the weights    *)
(* are stored, and again after (once the facts about the table have gone     *)
(* with the stores) when a weight comes after the last update.               *)
(* ------------------------------------------------------------------------- *)

(*** At 0x156c, after both weights of an iteration, out being all the ***)
(*** weights so far                                                   ***)

let fd_tend = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
   list_mk_conj
     [`LENGTH(out:num list) <= 254 /\
       read PC s = word(pc + 0x156c) /\
       read X3 s = word a /\ read X12 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X4 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X5 s = word_add dst (word(LENGTH out)) /\
       read X10 s = word_add dst (word 253) /\
       read X11 s =
       word_add dst (word(if EVEN(LENGTH out) then 254 else 253)) /\
       read X6 s = word_add (word pc) (word 31600) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fd_common]));;

(*** At 0x14e8, after the first weight y of an iteration, out being the ***)
(*** weights before it                                                  ***)

let fd_tmid = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
   list_mk_conj
     [`LENGTH(out:num list) <= 253 /\
       read PC s = word(pc + 0x14e8) /\
       read X3 s = word a /\ read X12 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X1 s = word_add src (word ofs) /\ read X0 s = word bc /\
       read X9 s = word_add dst (word(LENGTH out)) /\
       read X10 s = word_add dst (word 253) /\
       read X11 s =
       word_add dst (word(if EVEN(LENGTH out) then 254 else 253)) /\
       read X6 s = word_add (word pc) (word 31600) /\
       read (memory :> bytes(dst,LENGTH out + 1)) s =
       num_of_bytelist(MAP (word:num->byte) (APPEND out [y])) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (b,a,8 * ofs + 64 - bc,APPEND out [y]) w)`;
      fd_common]));;

(*** The error for too many weights, -70 (ERROR(dstSize_tooSmall)), the ***)
(*** weights in the goal being those of the specification from there   ***)

let FD_FULL_TAC =
  W(fun (asl,w) ->
    let t = find_term (fun t ->
      try fst(dest_const(repeat rator t)) = "fse_weights" &&
          length(snd(strip_comb t)) = 5
      with Failure _ -> false) w in
    let tm = mk_forall(rand t,mk_neg t) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FSE_WEIGHTS_FULL THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ZSTD_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[zstd_is_error] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_RULE);;

(*** From 0x156c: the check that two more weights fit, then the loop ***)

let FD_TC = prove
 (mk_fd_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`]
   fd_tend
   (let s = `s:armstate` in
    mk_abs(s,mk_disj(list_mk_comb(fd_tinv,[`256 - LENGTH(out:num list)`;s]),
                     mk_comb(fd_post,s)))),
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ASM_CASES_TAC `LENGTH(out:num list) <= 253` THENL
   [ZSTD_STEPS_TAC (1--4) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ZSTD_STEPS_TAC (1--11) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    FD_FULL_TAC]);;

(*** The facts about the table entry for the state u at the state s, and ***)
(*** the entry of BIT_mask for its number of bits                        ***)

let FD_ENTRY_TAC u s =
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `word_add dt (word 4):int64`;
                u; s] FSE_DTABLE_READ) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `tl <= 6` THEN ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; u] FSE_NBITS_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; u] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN (subst [u,`u:num`]
   `fse_nbits cs tl u < 256 /\ fse_symbol cs tl u < 256`)
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC (subst [u,`u:num`] `fse_nbits cs tl u <= tl`) THEN
    UNDISCH_TAC `tl <= 6` THEN
    UNDISCH_TAC (subst [u,`u:num`]
      `fse_symbol cs tl u < LENGTH(cs:int list)`) THEN
    UNDISCH_TAC `LENGTH(cs:int list) <= 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (subst [u,`u:num`]
   `val(word(fse_nbits cs tl u):int64) = fse_nbits cs tl u`)
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC (subst [u,`u:num`] `fse_nbits cs tl u < 256`) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [s; `pc:num`; subst [u,`u:num`] `fse_nbits cs tl u`]
    ZSTD_BIT_MASK_READ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `tl <= 6` THEN
    UNDISCH_TAC (subst [u,`u:num`] `fse_nbits cs tl u <= tl`) THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN (subst [u,`u:num`] `fse_base cs tl u < 64`) ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS (subst [u,`u:num`]
      `fse_base cs tl u + 2 EXP fse_nbits cs tl u`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `a < a + b <=> ~(b = 0)`; EXP_EQ_0; ARITH_EQ];
      TRANS_TAC LE_TRANS `2 EXP tl` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP 6` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV));;

(*** The table entry for the state u at the state s, after a store ***)

(*** with the addresses in the form of those of the loads from a pointer ***)
(*** to it                                                                ***)

let FD_TBL_ADDR = prove
 (`!(dt:int64) u.
        word_add (word_add dt (word 4)) (word(4 * u)) =
        word_add dt (word(4 + 4 * u))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let FD_DTABLE_READ_TAC u s =
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `word_add dt (word 4):int64`;
                u; s] FSE_DTABLE_READ) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `tl <= 6` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FD_TBL_ADDR] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o
    CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV));;

(*** A weight z stored after the weights l ***)

let FD_MEM_SNOC = prove
 (`!dst (l:num list) n z s.
        LENGTH l = n /\
        read (memory :> bytes(dst,n)) s =
        num_of_bytelist(MAP (word:num->byte) l) /\
        read (memory :> bytes8(word_add dst (word n))) s = word z
        ==> read (memory :> bytes(dst,n + 1)) s =
            num_of_bytelist(MAP (word:num->byte) (APPEND l [z]))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `LENGTH(l:num list) = n` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[MAP_APPEND; MAP] THEN
  MP_TAC(ISPECL [`dst:int64`; `MAP (word:num->byte) l`; `word z:byte`;
                 `s:armstate`] READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[LENGTH_MAP]);;

(*** The same for the facts at the state s about the weights l of length ***)
(*** n and the weight z after them, n + 1 being then normalized          ***)

let FD_MEM_SNOC_TAC l n z s =
  MP_TAC(SPECL [`dst:int64`; l; n; z; s] FD_MEM_SNOC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) o
               REWRITE_RULE[GSYM ADD_ASSOC])];;

let FD_NOT_ALL_NEQ = prove
 (`!a:A. (!x. ~(x = a)) <=> F`,
  MESON_TAC[]);;

let FD_WORD_SUB_BASE = prove
 (`!(x:int64) a b. word_sub (word_add (word_add x (word a)) (word b)) x =
                   word(a + b)`,
  CONV_TAC WORD_RULE);;

let FD_SP_RESTORE = prove
 (`!x:int64. word_add (word_sub x (word 96)) (word 96) = x`,
  CONV_TAC WORD_RULE);;

(*** At the return after the last two weights, the symbols of u and u', ***)
(*** when the next state update would need more bits than are left      ***)

let FD_STOP_TAC u u' ws =
  let tm = subst [u,`u:num`; u',`u':num`; ws,`ws:num list`]
   `!w. fse_weights cs tl (st:byte list) (u,u',8 * ofs + 64 - bc,ws) w <=>
        w = APPEND ws [fse_symbol cs tl u; fse_symbol cs tl u']` in
  SUBGOAL_THEN tm
   (fun th -> REWRITE_TAC[th; FORALL_UNWIND_THM2; FD_NOT_ALL_NEQ]) THENL
   [GEN_TAC THEN MATCH_MP_TAC FSE_WEIGHTS_STOP THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH;
              GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[FD_WORD_SUB_BASE; FD_SP_RESTORE];;

(*** The new state after an update, at the state s ***)

let FD_NEWSTATE = prove
 (`!(st:byte list) ofs bc nb base.
        bc + nb <= 64 /\ nb < 32
        ==> word_add
             (word_and
               (word_jushr
                 (word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                       18446744073709551616))
                 (word_zx (word_sub (word 0) (word (nb + bc)):int32)))
               (word_zx (word (2 EXP nb - 1):int32)))
             (word base):int64 =
            word(base + zstd_back st (8 * ofs + 64 - bc) nb)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FD_BITS_NORMAL; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let FD_NEWSTATE_TAC =
  W(fun (asl,w) ->
    let s = rand w in
    let conv tm =
      let ith = PART_MATCH (lhs o rand) FD_NEWSTATE tm in
      MP ith (TAC_PROOF((asl,lhand(concl ith)),
                        CONJ_TAC THEN SIMPLE_ARITH_TAC)) in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),_)
          when s' = s -> (try CONV_RULE(RAND_CONV conv) th
                          with Failure _ -> th)
      | _ -> th));;

(*** The container loaded from the offset ofs' at the state s ***)

let FD_SLICE_TAC ofs' s =
  MP_TAC(SPECL [`src:int64`; `LENGTH(st:byte list)`;
                `num_of_bytelist(st:byte list)`; ofs'; s]
     READ_MEMORY_BYTES64_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD_0] o
             CONV_RULE NUM_REDUCE_CONV);;

(*** The reload after an update leaving bq bits used, from the step k, ***)
(*** then fin ofs' bc' for the new offset and bits used                ***)

let FD_RELOAD_TAC k bq fin =
  let st n = mk_var("s"^string_of_int n,`:armstate`) in
  let dv = mk_binop `DIV` bq `8` and md = mk_binop `MOD` bq `8` in
  let ofs' = mk_binop `(-):num->num->num` `ofs:num` dv in
  let bc' = mk_binop `(-):num->num->num` bq
              (mk_binop `( * ):num->num->num` `8` dv) in
  let nz_tac =
    SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 7`
    STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] in
  MP_TAC(SPEC bq DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [nz_tac THEN
    ZSTD_STEPS_TAC (k--(k+4)) THEN FD_SLICE_TAC ofs' (st(k+4)) THEN
    ZSTD_STEPS_TAC ((k+5)--(k+6)) THEN fin ofs' md;
    ASM_CASES_TAC `ofs = 0` THENL
     [ZSTD_STEPS_TAC (k--(k+4)) THEN fin `ofs:num` bq;
      nz_tac THEN
      SUBGOAL_THEN (mk_binop `(<=):num->num->bool` dv `ofs:num`)
      ASSUME_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x < 2 /\ ~(ofs = 0) ==> x <= ofs`) THEN
        ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ZSTD_ARITH_TAC;
        ALL_TAC] THEN
      ZSTD_STEPS_TAC (k--(k+9)) THEN FD_SLICE_TAC ofs' (st(k+9)) THEN
      ZSTD_STEPS_TAC ((k+10)--(k+11)) THEN fin ofs' bc']];;

(*** The new state of the decoding after the update of u, the other state ***)
(*** being u' and the weights before it ws, as a step of the specification ***)

let FD_SPEC_STEP_TAC u u' ws =
  let nb = subst [u,`u:num`] `fse_nbits cs tl u` in
  let u'' = subst [u,`u:num`]
    `fse_base cs tl u + zstd_back (st:byte list) (8 * ofs + 64 - bc)
                                  (fse_nbits cs tl u)` in
  let tm = subst [u,`u:num`; u',`u':num`; ws,`ws:num list`; u'',`v:num`]
   `!w. fse_weights cs tl (st:byte list) (u,u',8 * ofs + 64 - bc,ws) w <=>
        fse_weights cs tl st
         (u',v,(8 * ofs + 64 - bc) - fse_nbits cs tl u,
          APPEND ws [fse_symbol cs tl u]) w` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FSE_WEIGHTS_STEP THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` u'' `2 EXP tl`) ASSUME_TAC THENL
   [MP_TAC(ISPECL [`st:byte list`; `8 * ofs + 64 - bc`; nb]
      ZSTD_BACK_BOUND) THEN
    UNDISCH_TAC (subst [u,`u:num`]
      `fse_base cs tl u + 2 EXP fse_nbits cs tl u <= 2 EXP tl`) THEN
    ARITH_TAC;
    ALL_TAC];;

(*** Going on at 0x156c with FD_TC, after the update of b with the reload ***)
(*** to the offset ofs' and bits used bc'                                  ***)

let FD_TB_FIN_TAC ofs' bc' =
  let out' = `APPEND (APPEND out [y:num]) [fse_symbol cs tl b]` in
  let b' = `fse_base cs tl b +
            zstd_back (st:byte list) (8 * ofs + 64 - bc)
                      (fse_nbits cs tl b)` in
  let wtac =
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(p ==> p') ==> p \/ q ==> p' \/ q`) THEN
    DISCH_TAC THEN
    EXISTS_TAC (mk_binop `(-):num->num->num` `256`
                  (mk_comb(`LENGTH:num list->num`,out'))) THEN
    ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC in
  SUBGOAL_THEN (mk_eq(vsubst [ofs',`ofs:num`; bc',`bc:num`]
                        `8 * ofs + 64 - bc`,
                      `(8 * ofs + 64 - bc) - fse_nbits cs tl b`))
  ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:num list->num`,out'),
                      `LENGTH(out:num list) + 2`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ZSTD_CONTINUE_WITH_TAC wtac FD_TC
   [b',`b:num`; ofs',`ofs:num`; bc',`bc:num`; out',`out:num list`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0; EVEN_ADD; ARITH; WORD_ADD_ASSOC_NUM] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

(*** From 0x14e8: the second weight of an iteration ***)

let fd_tb_post =
  let s = `s:armstate` and m' = `m':num` in
  mk_abs(s,mk_disj(mk_exists(m',mk_conj(`m' < 256 - LENGTH(out:num list)`,
                                        list_mk_comb(fd_tinv,[m';s]))),
                   mk_comb(fd_post,s)));;

let FD_TB = prove
 (mk_fd_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`; `y:num`]
   fd_tmid fd_tb_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(out:num list) = 253` THENL
   [SUBGOAL_THEN `~EVEN(LENGTH(out:num list))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                          ASSUME_TAC th) THEN
    ZSTD_STEPS_TAC (1--11) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    FD_FULL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(out:num list) <= 252` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  FD_ENTRY_TAC `b:num` `s0:armstate` THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `a:num`] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_CASES_TAC `EVEN(LENGTH(out:num list))` THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                        ASSUME_TAC th) THEN
  (ASM_CASES_TAC `fse_nbits cs tl b + bc <= 64` THENL
    [ZSTD_STEPS_TAC (1--18) THEN FD_NEWSTATE_TAC THEN
     FD_SPEC_STEP_TAC `b:num` `a:num` `APPEND out [y:num]` THEN
     FD_MEM_SNOC_TAC `APPEND out [y:num]` `LENGTH(out:num list) + 1`
       `fse_symbol cs tl b` `s18:armstate` THEN
     FD_RELOAD_TAC 19 `fse_nbits cs tl b + bc` FD_TB_FIN_TAC;
     ZSTD_STEPS_TAC (1--20) THEN
     FD_DTABLE_READ_TAC `a:num` `s20:armstate` THEN
     ZSTD_STEPS_TAC (21--32) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
     FD_MEM_SNOC_TAC `APPEND out [y:num]` `LENGTH(out:num list) + 1`
       `fse_symbol cs tl b` `s32:armstate` THEN
     FD_MEM_SNOC_TAC `APPEND (APPEND out [y:num]) [fse_symbol cs tl b]`
       `LENGTH(out:num list) + 2` `fse_symbol cs tl a` `s32:armstate` THEN
     FD_STOP_TAC `b:num` `a:num` `APPEND out [y:num]`]));;

(*** Going on at 0x14e8 with FD_TB, after the update of a with the reload ***)
(*** to the offset ofs' and bits used bc'                                  ***)

let FD_TA_FIN_TAC ofs' bc' =
  let a' = `fse_base cs tl a +
            zstd_back (st:byte list) (8 * ofs + 64 - bc)
                      (fse_nbits cs tl a)` in
  SUBGOAL_THEN (mk_eq(vsubst [ofs',`ofs:num`; bc',`bc:num`]
                        `8 * ofs + 64 - bc`,
                      `(8 * ofs + 64 - bc) - fse_nbits cs tl a`))
  ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_TB
   [a',`a:num`; ofs',`ofs:num`; bc',`bc:num`; `fse_symbol cs tl a`,`y:num`]
  THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

(*** The loop at 0x1470 for the last weights ***)

let FD_TLOOP = prove
 (mk_fd_goal []
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      list_mk_comb(fd_tinv,[`m:num`; `s:armstate`]))))
   fd_post,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
   [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`] THEN
  PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  FD_ENTRY_TAC `a:num` `s0:armstate` THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `b:num`] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_CASES_TAC `fse_nbits cs tl a + bc <= 64` THENL
   [ZSTD_STEPS_TAC (1--15) THEN FD_NEWSTATE_TAC THEN
    FD_SPEC_STEP_TAC `a:num` `b:num` `out:num list` THEN
    FD_MEM_SNOC_TAC `out:num list` `LENGTH(out:num list)`
      `fse_symbol cs tl a` `s15:armstate` THEN
    FD_RELOAD_TAC 16 `fse_nbits cs tl a + bc` FD_TA_FIN_TAC;
    ZSTD_STEPS_TAC (1--17) THEN
    FD_DTABLE_READ_TAC `b:num` `s17:armstate` THEN
    ZSTD_STEPS_TAC (18--28) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    FD_MEM_SNOC_TAC `out:num list` `LENGTH(out:num list)`
      `fse_symbol cs tl a` `s28:armstate` THEN
    FD_MEM_SNOC_TAC `APPEND out [fse_symbol cs tl a]`
      `LENGTH(out:num list) + 1` `fse_symbol cs tl b` `s28:armstate` THEN
    FD_STOP_TAC `a:num` `b:num` `out:num list`]);;

(* ------------------------------------------------------------------------- *)
(* After the main loop, and the main loop: the reload of the container, then *)
(* 4 weights while there is room for them, with enough bits since the        *)
(* container has at most 7 bits used after the reload.                       *)
(* ------------------------------------------------------------------------- *)

(*** At 0x144c, after the main loop, with an even number of weights ***)

let fd_ttail = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
   list_mk_conj
     [`LENGTH(out:num list) <= 252 /\ EVEN(LENGTH out) /\
       read PC s = word(pc + 0x144c) /\
       read X3 s = word a /\ read X12 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X4 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X9 s = word_add dst (word(LENGTH out)) /\
       read X21 s = word_add dst (word 255) /\
       read X6 s = word_add (word pc) (word 0x7000) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fd_common]));;

(*** The end pointer for the second weights of the loop, x11, for an even ***)
(*** number of weights                                                    ***)

let FD_AND_EVEN = prove
 (`!j. word_and (word(2 * j)) (word 18446744073709551614):int64 = word(2 * j)`,
  GEN_TAC THEN
  SUBGOAL_THEN `word(2 * j):int64 = word_shl (word j) 1` SUBST1_TAC THENL
   [REWRITE_TAC[word_shl; EXP_1; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG; MOD_MULT_RMOD] THEN
    REWRITE_TAC[MOD_MULT_LMOD] THEN REWRITE_TAC[MULT_SYM];
    BITBLAST_TAC]);;

let FD_X11 = prove
 (`!(dst:int64) l.
        l <= 254 /\ EVEN l
        ==> word_add (word_add dst (word l))
             (word_and
               (word_sub (word_add dst (word 254)) (word_add dst (word l)))
               (word 18446744073709551614)) =
            word_add dst (word 254)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_sub (word_add dst (word 254)) (word_add dst (word l)):int64 =
    word(254 - l)`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add x a) (word_add x b):int64 = word_sub a b`] THEN
    ASM_SIMP_TAC[WORD_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN(254 - l)` MP_TAC THENL
   [ASM_REWRITE_TAC[EVEN_SUB] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[FD_AND_EVEN] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(*** From 0x144c: the check that two more weights fit and the setup of the ***)
(*** loop for the last weights                                             ***)

let FD_TAIL = prove
 (mk_fd_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`]
   fd_ttail fd_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--9) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(REWR_CONV(MP
      (SPECL [`dst:int64`; `LENGTH(out:num list)`] FD_X11)
      (CONJ (ARITH_RULE `LENGTH(out:num list) <= 252
                         ==> LENGTH out <= 254`
             |> C MP (ASSUME `LENGTH(out:num list) <= 252`))
            (ASSUME `EVEN(LENGTH(out:num list))`))))) th
    with Failure _ -> th) THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_TLOOP [] THEN
  MEMSAFE_ELIM_TAC THEN
  EXISTS_TAC `256 - LENGTH(out:num list)` THEN
  MAP_EVERY EXISTS_TAC
   [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC);;

(*** At 0x1414, the main loop, for the measure m = 63 - k with 4 * k ***)
(*** weights so far                                                  ***)

let fd_minv = with_memsafe fd_rr fd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   list_mk_exists([`a:num`; `b:num`; `ofs:num`; `bc:num`; `k:num`;
                   `out:num list`],
    list_mk_conj
     [`m = 63 - k /\ LENGTH(out:num list) = 4 * k /\ k <= 63 /\
       read PC s = word(pc + 0x1414) /\
       read X3 s = word a /\ read X12 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X4 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X9 s = word_add dst (word(LENGTH out)) /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read X10 s = word_add (word pc) (word 31600) /\
       read X6 s = word_add (word pc) (word 0x7000) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fd_common])));;

(*** At 0x1344, after the reload, with the flag for room for 4 weights ***)

let fd_mbody = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`LENGTH(out:num list) = 4 * k /\ k <= 63 /\
       read PC s = word(pc + 0x1344) /\
       read X3 s = word a /\ read X12 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X4 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X9 s = word_add dst (word(LENGTH out)) /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read X10 s = word_add (word pc) (word 31600) /\
       read X6 s = word_add (word pc) (word 0x7000) /\
       read X11 s = word(if 4 * k < 252 then 1 else 0) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 7 /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fd_common]));;

let fd_mpost k =
  let s = `s:armstate` and m' = `m':num` in
  mk_abs(s,mk_disj(mk_exists(m',mk_conj(mk_binop `(<):num->num->bool` m'
                                          (mk_binop `(-):num->num->num`
                                             `63` k),
                                        list_mk_comb(fd_minv,[m';s]))),
                   mk_comb(fd_post,s)));;

(*** The table entry for the state u at the state s, with the addresses ***)
(*** in the form of those of loads from the table pointer plus 4u       ***)

let FD_DTABLE_READA_TAC u s =
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `word_add dt (word 4):int64`;
                u; s] FSE_DTABLE_READ) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `tl <= 6` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o
    CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV));;

(*** A step of the specification for the update of u, the other state ***)
(*** being u', with bcv bits used and the weights ws before it, both  ***)
(*** positions as in the code; then the new state is abbreviated as v ***)

let FD_SPEC_STEP2_TAC u u' bcv ws v =
  let nb = subst [u,`u:num`] `fse_nbits cs tl u` in
  let q = subst [bcv,`bcv:num`] `8 * ofs + 64 - bcv` in
  let u'' = subst [u,`u:num`; q,`q:num`]
    `fse_base cs tl u + zstd_back (st:byte list) q (fse_nbits cs tl u)` in
  let q' = subst [nb,`nb:num`; bcv,`bcv:num`] `8 * ofs + 64 - (nb + bcv)` in
  let tm = subst [u,`u:num`; u',`u':num`; ws,`ws:num list`; u'',`v:num`;
                  q,`q:num`; q',`q':num`]
   `!w. fse_weights cs tl (st:byte list) (u,u',q,ws) w <=>
        fse_weights cs tl st (u',v,q',APPEND ws [fse_symbol cs tl u]) w` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) FSE_WEIGHTS_STEP o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ZSTD_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` u'' `2 EXP tl`) ASSUME_TAC THENL
   [MP_TAC(ISPECL [`st:byte list`; q; nb] ZSTD_BACK_BOUND) THEN
    UNDISCH_TAC (subst [u,`u:num`]
      `fse_base cs tl u + 2 EXP fse_nbits cs tl u <= 2 EXP tl`) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC (mk_eq(v,u''));;

(*** The facts about the table entry for the state u at the state s, as ***)
(*** in FD_ENTRY_TAC, but with the addresses of the entry in both forms ***)
(*** and without normalizing the other assumptions                      ***)

let FD_ENTRY2_TAC u s =
  let sub t = subst [u,`u:num`] t in
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `word_add dt (word 4):int64`;
                u; s] FSE_DTABLE_READ) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `tl <= 6` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC(CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                       th) THEN
    STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV
                                 NORMALIZE_RELATIVE_ADDRESS_CONV)
                       (REWRITE_RULE[FD_TBL_ADDR] th))) THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; u] FSE_NBITS_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; u] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN (sub `fse_nbits cs tl u < 256 /\ fse_symbol cs tl u < 256`)
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC (sub `fse_nbits cs tl u <= tl`) THEN
    UNDISCH_TAC `tl <= 6` THEN
    UNDISCH_TAC (sub `fse_symbol cs tl u < LENGTH(cs:int list)`) THEN
    UNDISCH_TAC `LENGTH(cs:int list) <= 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (sub `val(word(fse_nbits cs tl u):int64) = fse_nbits cs tl u`)
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC (sub `fse_nbits cs tl u < 256`) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [s; `pc:num`; sub `fse_nbits cs tl u`] ZSTD_BIT_MASK_READ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `tl <= 6` THEN
    UNDISCH_TAC (sub `fse_nbits cs tl u <= tl`) THEN ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o
      CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))] THEN
  SUBGOAL_THEN (sub `fse_base cs tl u < 64`) ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS (sub `fse_base cs tl u + 2 EXP fse_nbits cs tl u`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `a < a + b <=> ~(b = 0)`; EXP_EQ_0; ARITH_EQ];
      TRANS_TAC LE_TRANS `2 EXP tl` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP 6` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC];;

(*** FD_MEM_SNOC_TAC with the length proved from the assumptions too ***)

let FD_MEM_SNOC2_TAC l n z s =
  MP_TAC(SPECL [`dst:int64`; l; n; z; s] FD_MEM_SNOC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) o
               REWRITE_RULE[GSYM ADD_ASSOC])];;

(*** From 0x1344: four weights, or the tail if there is no room for them ***)

let FD_MBODY = prove
 (mk_fd_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `k:num`; `out:num list`]
   fd_mbody (fd_mpost `k:num`),
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `4 * k < 252` THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                        ASSUME_TAC th) THENL
   [ALL_TAC;
    ZSTD_STEPS_TAC (1--5) THEN
    ZSTD_CONTINUE_WITH_TAC
     (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
      FIRST_ASSUM ACCEPT_TAC) FD_TAIL [] THEN
    MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[EVEN_MULT; ARITH] THEN ZSTD_ARITH_TAC] THEN
  FIRST_ASSUM((fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         ASSUME_TAC th) o
    check (fun th -> concl th = `LENGTH(out:num list) = 4 * k`)) THEN
  SUBGOAL_THEN `k <= 62` ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  FD_ENTRY2_TAC `a:num` `s0:armstate` THEN
  ZSTD_STEPS_TAC (1--13) THEN FD_ENTRY2_TAC `b:num` `s13:armstate` THEN
  ZSTD_STEPS_TAC (14--19) THEN FD_NEWSTATE_TAC THEN
  FD_SPEC_STEP2_TAC `a:num` `b:num` `bc:num` `out:num list` `a1:num` THEN
  ZSTD_STEPS_TAC (20--26) THEN FD_NEWSTATE_TAC THEN
  FD_SPEC_STEP2_TAC `b:num` `a1:num` `fse_nbits cs tl a + bc`
    `APPEND out [fse_symbol cs tl a]` `b1:num` THEN
  ZSTD_STEPS_TAC (27--29) THEN FD_ENTRY2_TAC `a1:num` `s29:armstate` THEN
  ZSTD_STEPS_TAC (30--36) THEN FD_ENTRY2_TAC `b1:num` `s36:armstate` THEN
  ZSTD_STEPS_TAC (37--50) THEN FD_NEWSTATE_TAC THEN
  FD_SPEC_STEP2_TAC `a1:num` `b1:num`
    `fse_nbits cs tl b + fse_nbits cs tl a + bc`
    `APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b]`
    `a2:num` THEN
  FD_SPEC_STEP2_TAC `b1:num` `a2:num`
    `fse_nbits cs tl a1 + fse_nbits cs tl b + fse_nbits cs tl a + bc`
    `APPEND (APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b])
            [fse_symbol cs tl a1]`
    `b2:num` THEN
  ZSTD_STEPS_TAC (51--52) THEN
  FD_MEM_SNOC2_TAC `out:num list` `4 * k` `fse_symbol cs tl a`
    `s52:armstate` THEN
  FD_MEM_SNOC2_TAC `APPEND out [fse_symbol cs tl a]` `4 * k + 1`
    `fse_symbol cs tl b` `s52:armstate` THEN
  FD_MEM_SNOC2_TAC
    `APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b]`
    `4 * k + 2` `fse_symbol cs tl a1` `s52:armstate` THEN
  FD_MEM_SNOC2_TAC
    `APPEND (APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b])
            [fse_symbol cs tl a1]`
    `4 * k + 3` `fse_symbol cs tl b1` `s52:armstate` THEN
  ABBREV_TAC
   `out4 = APPEND (APPEND (APPEND (APPEND out [fse_symbol cs tl a])
                                  [fse_symbol cs tl b])
                          [fse_symbol cs tl a1])
                  [fse_symbol cs tl b1]` THEN
  SUBGOAL_THEN `LENGTH(out4:num list) = 4 * k + 4` ASSUME_TAC THENL
   [EXPAND_TAC "out4" THEN ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `63 - (k + 1)` THEN
  CONJ_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`a2:num`; `b2:num`; `ofs:num`;
    `fse_nbits cs tl b1 + fse_nbits cs tl a1 + fse_nbits cs tl b +
     fse_nbits cs tl a + bc`;
    `k + 1`; `out4:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  ZSTD_ARITH_TAC);;

(*** The main loop at 0x1414: the reload, then FD_MBODY, or the tail if  ***)
(*** the start of the stream is reached                                  ***)

let FD_CSET = prove
 (`!(dst:int64) k.
        val dst + 255 < 2 EXP 64 /\ k <= 63
        ==> word(if val(word_add dst (word 252)) <=
                    val(word_add dst (word(4 * k)))
                 then 0 else 1):int64 =
            word(if 4 * k < 252 then 1 else 0)`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val(word_add dst (word 252):int64) = val dst + 252 /\
                val(word_add dst (word(4 * k)):int64) = val dst + 4 * k`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_ADD_NOWRAP THEN ASM_ARITH_TAC;
    REWRITE_TAC[LE_ADD_LCANCEL; GSYM NOT_LT; COND_SWAP]]);;

(*** The position after the reload to the offset ofs' and bits used bc' ***)

let FD_POS_TAC ofs' bc' =
  let tm0 = vsubst [ofs',`ofs:num`; bc',`bc:num`] `8 * ofs + 64 - bc` in
  let tm = rhs(concl(TRY_CONV NUM_REDUCE_CONV tm0)) in
  if tm = `8 * ofs + 64 - bc` then ALL_TAC else
  SUBGOAL_THEN (mk_eq(tm,`8 * ofs + 64 - bc`)) ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC];;

let FD_MLOOP_BODY_TAC ofs' bc' =
  FD_POS_TAC ofs' bc' THEN
  MP_TAC(SPECL [`dst:int64`; `k:num`] FD_CSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_MBODY
   [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FD_MLOOP_TAIL_TAC ofs' bc' =
  FD_POS_TAC ofs' bc' THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
    FIRST_ASSUM ACCEPT_TAC) FD_TAIL
   [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[EVEN_MULT; ARITH; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FD_MLOOP = prove
 (mk_fd_goal []
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      list_mk_comb(fd_minv,[`m:num`; `s:armstate`]))))
   fd_post,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
   [`a:num`; `b:num`; `ofs:num`; `bc:num`; `k:num`; `out:num list`] THEN
  PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `bc:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--7) THEN FD_SLICE_TAC `ofs - bc DIV 8` `s7:armstate` THEN
    ZSTD_STEPS_TAC (8--9) THEN
    FD_MLOOP_BODY_TAC `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (1--6) THEN FD_MLOOP_TAIL_TAC `ofs:num` `bc:num`;
    ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [ZSTD_STEPS_TAC (1--9) THEN FD_SLICE_TAC `ofs - bc DIV 8` `s9:armstate` THEN
    ZSTD_STEPS_TAC (10--14) THEN
    FD_MLOOP_BODY_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    ZSTD_STEPS_TAC (1--13) THEN FD_SLICE_TAC `0` `s13:armstate` THEN
    ZSTD_STEPS_TAC [14] THEN
    FD_MLOOP_TAIL_TAC `0` `bc - 8 * ofs`]);;

(* ------------------------------------------------------------------------- *)
(* The start: BIT_initDStream and the reads of the two states, the stream    *)
(* needing at least as many bits as the two states. An empty stream, and one *)
(* whose last byte is 0, are errors.                                         *)
(* ------------------------------------------------------------------------- *)

(*** At the return, for the stream st ***)

let fd_spost = with_memsafe fd_rr fd_wr `\s.
  read PC s = returnaddress /\ read SP s = stackpointer /\
  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
  read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
  read X25 s = x25 /\ read X29 s = x29 /\ read X30 s = returnaddress /\
  (!w. fse_stream cs tl st w
       ==> read X0 s = word(LENGTH w) /\
           read (memory :> bytes(dst,LENGTH w)) s =
           num_of_bytelist(MAP (word:num->byte) w)) /\
  ((!w. ~fse_stream cs tl st w) ==> zstd_is_error(read X0 s))`;;

(*** At 0x12e0, after the reads of the two states a and b, before the ***)
(*** reload of the main loop                                          ***)

let fd_i3 = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x12e0) /\
       read X3 s = word a /\ read X12 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X0 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read X6 s = word_add (word pc) (word 0x7000) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (!w. fse_stream cs tl st w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,[]) w)`;
      fd_common]));;

let FD_I3_TAC ofs' bc' =
  FD_POS_TAC ofs' bc' THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_MLOOP
   [`a:num`,`s1:num`; `b:num`,`s2:num`; `8 * ofs + 64 - bc`,`q0:num`] THEN
  MEMSAFE_ELIM_TAC THEN EXISTS_TAC `63 - 0` THEN
  MAP_EVERY EXISTS_TAC
   [`a:num`; `b:num`; ofs'; bc'; `0`; `[]:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[LENGTH; MAP; num_of_bytelist; READ_MEMORY_BYTES_0;
                  WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FD_I3 = prove
 (mk_fd_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`] fd_i3 fd_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `bc:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--5) THEN FD_SLICE_TAC `ofs - bc DIV 8` `s5:armstate` THEN
    ZSTD_STEPS_TAC (6--11) THEN FD_I3_TAC `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (1--10) THEN FD_I3_TAC `ofs:num` `bc:num`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [ZSTD_STEPS_TAC (1--10) THEN
    FD_SLICE_TAC `ofs - bc DIV 8` `s10:armstate` THEN
    ZSTD_STEPS_TAC (11--17) THEN
    FD_I3_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    ZSTD_STEPS_TAC (1--13) THEN FD_SLICE_TAC `0` `s13:armstate` THEN
    ZSTD_STEPS_TAC (14--20) THEN FD_I3_TAC `0` `bc - 8 * ofs`]);;

(*** The pieces before the reads of the states, with the workspace wksp, ***)
(*** the table being at wksp + 512                                       ***)

let fdw_dt = `word_add wksp (word 512):int64`;;

let fdw_hyps = subst [fdw_dt,`dt:int64`] fd_hyps;;

let fdw_vars =
  map (fun v -> if v = `dt:int64` then `wksp:int64` else v) fd_vars;;

let mk_fdw_goal extra pre post =
  let tm = mk_imp(fdw_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; fd_frame]) in
  let vs = fdw_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fdw_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let fdw_spost = subst [fdw_dt,`dt:int64`] fd_spost;;

(*** The facts of fd_common but those about X8 and X19 ***)

let fd_common0 =
  let cs = conjuncts fd_common in
  list_mk_conj(filter (fun c ->
    not(can (term_match [] `read X8 s = x`) c) &&
    not(can (term_match [] `read X19 s = x`) c)) cs);;

(*** At 0x1284, after the read of the first state, the stream having r ***)
(*** bits                                                               ***)

let fd_i2 = subst [fdw_dt,`dt:int64`] (with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x1284) /\
       read X3 s = word(zstd_back st r tl) /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X4 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X1 s = word tl /\
       read X10 s = word_zx(word(2 EXP tl - 1):int32) /\
       read X6 s = word_add (word pc) (word 0x7000) /\
       read X8 s = word_add src (word 8) /\ read X19 s = wksp /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (ofs = 0 \/ bc <= 7) /\
       zstd_end st r /\ tl <= r /\ 8 * ofs + 64 - bc = r - tl`;
      fd_common0])));;

(*** FD_BITS_NORMAL with the sum the other way round ***)

let FD_BITS_NORMAL_ALT = prove
 (`!(st:byte list) ofs bc nb.
        bc + nb <= 64 /\ nb < 32
        ==> word_and
             (word_jushr
               (word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                     18446744073709551616))
               (word_zx (word_sub (word 0) (word (bc + nb)):int32)))
             (word_zx (word (2 EXP nb - 1):int32)):int64 =
            word(zstd_back st (8 * ofs + 64 - bc) nb)`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(ARITH_RULE `bc + nb:num = nb + bc`) THEN
  MATCH_MP_TAC FD_BITS_NORMAL THEN ASM_ARITH_TAC);;

let FD_INITSTATE_TAC =
  W(fun (asl,w) ->
    let s = rand w in
    let conv tm =
      let ith = PART_MATCH (lhs o rand) FD_BITS_NORMAL_ALT tm in
      MP ith (TAC_PROOF((asl,lhand(concl ith)),
                        CONJ_TAC THEN SIMPLE_ARITH_TAC)) in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),_)
          when s' = s -> (try CONV_RULE(RAND_CONV conv) th
                          with Failure _ -> th)
      | _ -> th));;

(*** The position after a reload to ofs' and bc' as the target position ***)

let FD_POSQ_TAC ofs' bc' q =
  let tm0 = vsubst [ofs',`ofs:num`; bc',`bc:num`] `8 * ofs + 64 - bc` in
  let tm = rhs(concl(TRY_CONV NUM_REDUCE_CONV tm0)) in
  if tm = q then ALL_TAC else
  SUBGOAL_THEN (mk_eq(tm,q)) ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC];;

let FD_I2_I3_TAC ofs' bc' =
  FD_POSQ_TAC ofs' bc' `r - 2 * tl` THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_I3
   [fdw_dt,`dt:int64`; `zstd_back (st:byte list) r tl`,`a:num`;
    `zstd_back (st:byte list) (r - tl) tl`,`b:num`;
    ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FD_I2_LOOP_TAC =
  FD_POSQ_TAC `ofs:num` `bc + tl` `r - 2 * tl` THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_MLOOP
   [fdw_dt,`dt:int64`; `zstd_back (st:byte list) r tl`,`s1:num`;
    `zstd_back (st:byte list) (r - tl) tl`,`s2:num`;
    `r - 2 * tl`,`q0:num`] THEN
  MEMSAFE_ELIM_TAC THEN EXISTS_TAC `63 - 0` THEN
  MAP_EVERY EXISTS_TAC
   [`zstd_back (st:byte list) r tl`; `zstd_back (st:byte list) (r - tl) tl`;
    `ofs:num`; `bc + tl`; `0`; `[]:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[LENGTH; MAP; num_of_bytelist; READ_MEMORY_BYTES_0;
                  WORD_ADD_0; ZSTD_BACK_BOUND; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FD_I2 = prove
 (mk_fdw_goal [`r:num`; `ofs:num`; `bc:num`] fd_i2 fdw_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc + tl <= 64` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!w. ~fse_stream cs tl (st:byte list) w` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FSE_STREAM_SHORT THEN EXISTS_TAC `r:num` THEN
      ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC;
      ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--16) THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV] THEN
  SUBGOAL_THEN `2 * tl <= r` ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `st:byte list`; `r:num`]
    FSE_STREAM_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ZSTD_STEPS_TAC (1--7) THEN FD_INITSTATE_TAC THEN
  MP_TAC(SPEC `bc + tl:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 7`
    STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (8--12) THEN
    FD_SLICE_TAC `ofs - (bc + tl) DIV 8` `s12:armstate` THEN
    ZSTD_STEPS_TAC (13--14) THEN
    FD_I2_I3_TAC `ofs - (bc + tl) DIV 8` `(bc + tl) MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (8--15) THEN FD_I2_LOOP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 7`
  STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(bc + tl) DIV 8 <= ofs` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 /\ ~(ofs = 0) ==> x <= ofs`) THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (8--17) THEN
  FD_SLICE_TAC `ofs - (bc + tl) DIV 8` `s17:armstate` THEN
  ZSTD_STEPS_TAC (18--20) THEN
  FD_I2_I3_TAC `ofs - (bc + tl) DIV 8` `(bc + tl) - 8 * (bc + tl) DIV 8`);;

(*** At 0x1214, after BIT_initDStream, the stream having 8 * ofs + 64 - bc ***)
(*** bits                                                                  ***)

let fd_i1 = subst [fdw_dt,`dt:int64`] (with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x1214) /\
       read X7 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X9 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X19 s = wksp /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read (memory :> bytes16 (word_add wksp (word 512))) s = word tl /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (ofs = 0 \/ bc <= 8) /\ zstd_end st (8 * ofs + 64 - bc)`;
      fd_common0])));;

let FD_I1_TAC ofs' bc' =
  FD_POSQ_TAC ofs' bc' `(8 * ofs + 64 - bc) - tl` THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_I2
   [`8 * ofs + 64 - bc`,`r:num`; ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FD_I1 = prove
 (mk_fdw_goal [`ofs:num`; `bc:num`] fd_i1 fdw_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`; `tl:num`] ZSTD_BIT_MASK_READ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `tl <= 6` THEN ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o
      CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))] THEN
  SUBGOAL_THEN `val(word tl:int64) = tl` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `tl <= 6` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `bc + tl <= 64` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!w. ~fse_stream cs tl (st:byte list) w` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FSE_STREAM_SHORT THEN
      EXISTS_TAC `8 * ofs + 64 - bc` THEN
      ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC;
      ALL_TAC] THEN
    ZSTD_STEPS_TAC [1] THEN PUFF_ADRP_TAC THEN ZSTD_STEPS_TAC (2--21) THEN
    PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV] THEN
  ZSTD_STEPS_TAC [1] THEN PUFF_ADRP_TAC THEN
  ZSTD_STEPS_TAC (2--10) THEN FD_INITSTATE_TAC THEN
  ZSTD_STEPS_TAC (11--12) THEN
  MP_TAC(SPEC `bc + tl:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 8`
    STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (13--18) THEN
    FD_SLICE_TAC `ofs - (bc + tl) DIV 8` `s18:armstate` THEN
    ZSTD_STEPS_TAC (19--20) THEN
    FD_I1_TAC `ofs - (bc + tl) DIV 8` `(bc + tl) MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (13--18) THEN FD_I1_TAC `ofs:num` `bc + tl`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 8`
  STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(bc + tl) DIV 8 <= ofs` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 /\ ~(ofs = 0) ==> x <= ofs`) THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (13--23) THEN
  FD_SLICE_TAC `ofs - (bc + tl) DIV 8` `s23:armstate` THEN
  ZSTD_STEPS_TAC (24--25) THEN
  FD_I1_TAC `ofs - (bc + tl) DIV 8` `(bc + tl) - 8 * (bc + tl) DIV 8`);;

(*** At 0x11e0, the start of the decoding, with the stream st of the ***)
(*** bytes at src                                                    ***)

let fd_i0 = subst [fdw_dt,`dt:int64`] (with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x11e0) /\
       read X18 s = word(LENGTH(st:byte list)) /\ read X19 s = wksp /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read (memory :> bytes16 (word_add wksp (word 512))) s = word tl`;
      fd_common0])));;

(*** The last byte of the stream, and the container at offset 0 ***)

let FD_LASTBYTE_TAC =
  SUBGOAL_THEN `1 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`src:int64`; `st:byte list`; `LENGTH(st:byte list) - 1`;
                 `s2:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_PRED_LEMMA] THEN DISCH_TAC THEN
  ABBREV_TAC `b = EL (LENGTH(st:byte list) - 1) st` THEN
  ZSTD_STEPS_TAC [3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP ZSTD_LAST_ADDR
    (ASSUME `1 <= LENGTH(st:byte list)`)]) THEN
  ABBREV_TAC `vb = val(b:byte)` THEN
  SUBGOAL_THEN `vb < 256` ASSUME_TAC THENL
   [EXPAND_TAC "vb" THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC];;

let FD_VB_FACTS_TAC =
  SUBGOAL_THEN `1 <= bitsize vb /\ bitsize vb <= 8` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BITSIZE_LE; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                BITSIZE_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The errors when the stream has no end ***)

let FD_NOEND_TAC =
  SUBGOAL_THEN `!w. ~fse_stream cs tl (st:byte list) w` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FSE_STREAM_NOEND THEN GEN_TAC THEN
    MP_TAC(SPECL [`st:byte list`; `r:num`] ZSTD_END_LAST) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SIMPLE_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;;

(*** Going on with FD_I1 for the offset ofs' and bits used bc' ***)

let FD_I0_GOON_TAC ofs' bc' =
  let r = vsubst [ofs',`ofs:num`; bc',`bc:num`] `8 * ofs + 64 - bc` in
  SUBGOAL_THEN (mk_comb(`zstd_end (st:byte list)`,r)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`st:byte list`; r] ZSTD_END_LAST) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SIMPLE_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FD_I1
   [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0; WORD_CONTAINER_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (ZSTD_ARITH_TAC ORELSE (AP_TERM_TAC THEN ZSTD_ARITH_TAC));;

(*** A stream of k bytes, 1 <= k <= 7 ***)

let FD_SMALL_TAC k =
  let numt = mk_small_numeral in
  let els = map (fun i -> list_mk_icomb "EL" [numt i; `st:byte list`])
                (0--(k-1)) in
  let sum = itlist (fun e acc ->
              mk_binop `(+):num->num->num` (mk_icomb(`val:byte->num`,e))
                (mk_binop `( * ):num->num->num` `256` acc)) els `0` in
  let lst = mk_list(els,`:byte`) in
  let bc = subst [numt(8 * (8 - k)),`n:num`] `(32 - bitsize vb + n) - 23` in
  let memfact i =
    MP_TAC(ISPECL [`src:int64`; `st:byte list`; numt i; `s5:armstate`]
      READ_MEMORY_BYTES8_BYTELIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] in
  let range = ARITH_RULE(mk_eq(mk_binop `(<):num->num->bool` `i:num` (numt k),
                list_mk_disj(map (fun j -> mk_eq(`i:num`,numt j))
                                 (0--(k-1))))) in
  ZSTD_STEPS_TAC (4--5) THEN MAP_EVERY memfact (0--(k-1)) THEN
  SUBGOAL_THEN (mk_eq(`num_of_bytelist(st:byte list)`,sum)) ASSUME_TAC THENL
   [SUBGOAL_THEN (mk_eq(`st:byte list`,lst))
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] THEN
                 REWRITE_TAC[num_of_bytelist]) THEN
    REWRITE_TAC[LIST_EQ; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[range] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `vb = 0` THENL
   [ZSTD_RUN_TAC THEN FD_NOEND_TAC;
    FD_VB_FACTS_TAC THEN ZSTD_SIM_UNTIL_TAC [0x1214] THEN
    FD_I0_GOON_TAC `0` bc];;

let FD_I0 = prove
 (mk_fdw_goal [] fd_i0 fdw_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ASM_CASES_TAC `LENGTH(st:byte list) = 0` THENL
   [ZSTD_STEPS_TAC (1--10) THEN
    SUBGOAL_THEN `!w. ~fse_stream cs tl (st:byte list) w` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FSE_STREAM_NOEND THEN
      REWRITE_TAC[zstd_end] THEN ASM_MESON_TAC[LENGTH_EQ_NIL];
      ALL_TAC] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--2) THEN FD_LASTBYTE_TAC THEN
  ASM_CASES_TAC `8 <= LENGTH(st:byte list)` THENL
   [ASM_CASES_TAC `vb = 0` THENL
     [ZSTD_STEPS_TAC (4--15) THEN FD_NOEND_TAC;
      FD_VB_FACTS_TAC THEN ZSTD_STEPS_TAC (4--12) THEN
      FD_SLICE_TAC `LENGTH(st:byte list) - 8` `s12:armstate` THEN
      ZSTD_STEPS_TAC [13] THEN
      FD_I0_GOON_TAC `LENGTH(st:byte list) - 8` `32 - bitsize vb - 23`];
    SUBGOAL_THEN
     `LENGTH(st:byte list) = 1 \/ LENGTH st = 2 \/ LENGTH st = 3 \/
      LENGTH st = 4 \/ LENGTH st = 5 \/ LENGTH st = 6 \/ LENGTH st = 7`
    (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [SIMPLE_ARITH_TAC; FD_SMALL_TAC 1; FD_SMALL_TAC 2; FD_SMALL_TAC 3;
      FD_SMALL_TAC 4; FD_SMALL_TAC 5; FD_SMALL_TAC 6; FD_SMALL_TAC 7]]);;

(* ------------------------------------------------------------------------- *)
(* The fast copy, with the same structure: the bits read are the top nb of   *)
(* the container shifted left by bc, which needs nb >= 1. Its registers are  *)
(* different, and x12 holds the limit src + 8.                               *)
(* ------------------------------------------------------------------------- *)

(*** Fast mode: every state has at least one bit ***)

let FSE_FAST_NBITS = prove
 (`!cs alog u.
        5 <= alog /\ fse_valid cs alog /\ fse_fast cs alog = 1 /\
        u < 2 EXP alog
        ==> 1 <= fse_nbits cs alog u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `alog:num`; `u:num`] FSE_NEXT_BOUNDS) THEN
  MP_TAC(SPECL [`cs:int list`; `alog:num`; `u:num`] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t = fse_symbol cs alog u` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN `fse_init cs t < 2 EXP (alog - 1)` ASSUME_TAC THENL
   [UNDISCH_TAC `fse_fast cs alog = 1` THEN
    REWRITE_TAC[fse_fast; GSYM ALL_EL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN
    ASM_REWRITE_TAC[fse_init] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN TRANS_TAC LTE_TRANS `2 EXP 1` THEN
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `~(EL t (cs:int list) = -- &1)`
       (fun th -> REWRITE_TAC[th]) THENL
       [POP_ASSUM MP_TAC THEN SPEC_TAC(`EL t (cs:int list)`,`x:int`) THEN
        INT_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
      MP_TAC(ISPEC `EL t (cs:int list)` INT_OF_NUM_OF_INT) THEN
      ANTS_TAC THENL
       [POP_ASSUM MP_TAC THEN SPEC_TAC(`EL t (cs:int list)`,`x:int`) THEN
        INT_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `fse_next cs alog u < 2 EXP alog` ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP alog = 2 * 2 EXP (alog - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[fse_nbits] THEN
  MP_TAC(SPECL [`fse_next cs alog u`; `alog:num`] BITSIZE_LE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(*** The decoding part in fast mode ***)

let fdf_hyps = mk_conj(`fse_fast cs tl = 1`,fd_hyps);;

let mk_fdf_goal extra pre post =
  let tm = mk_imp(fdf_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; fd_frame]) in
  let vs = fd_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fdf_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

(*** fd_common with the limit pointer src + 8 in X12 instead of X8 ***)

let fdf_common =
  subst [`read X12 s = word_add src (word 8)`,
         `read X8 s = word_add src (word 8)`] fd_common;;

(*** At 0x18ac, the loop for the last weights ***)

let fdf_tinv = with_memsafe fd_rr fd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   list_mk_exists([`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`],
    list_mk_conj
     [`m = 256 - LENGTH(out:num list) /\ LENGTH out <= 253 /\
       read PC s = word(pc + 0x18ac) /\
       read X0 s = word a /\ read X13 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X9 s = word_add src (word ofs) /\ read X1 s = word bc /\
       read X10 s = word_add dst (word(LENGTH out)) /\
       read X7 s = word_add dst (word 253) /\
       read X6 s =
       word_add dst (word(if EVEN(LENGTH out) then 254 else 253)) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fdf_common])));;

(*** The new state after an update in fast mode ***)

let FDF_NEWSTATE = prove
 (`!(st:byte list) ofs bc nb base.
        1 <= nb /\ bc + nb <= 64
        ==> word_add
             (word_jushr
               (word(2 EXP bc *
                     (num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD
                     18446744073709551616))
               (word_zx (word_sub (word 0) (word nb):int32)))
             (word base):int64 =
            word(base + zstd_back st (8 * ofs + 64 - bc) nb)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  GEN_REWRITE_TAC RAND_CONV [WORD_ADD_SYM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[word_jushr; word_ushr; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(SPEC `nb:num` FD_SHIFT_NEG) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [MULT_SYM] THEN
  MATCH_MP_TAC ZSTD_WINDOW THEN ASM_ARITH_TAC);;

let FDF_NEWSTATE_TAC =
  W(fun (asl,w) ->
    let s = rand w in
    let conv tm =
      let ith = PART_MATCH (lhs o rand) FDF_NEWSTATE tm in
      MP ith (TAC_PROOF((asl,lhand(concl ith)),
                        CONJ_TAC THEN SIMPLE_ARITH_TAC)) in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),_)
          when s' = s -> (try CONV_RULE(RAND_CONV conv) th
                          with Failure _ -> th)
      | _ -> th));;

(*** At 0x1998, after both weights of an iteration ***)

let fdf_tend = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
   list_mk_conj
     [`LENGTH(out:num list) <= 254 /\
       read PC s = word(pc + 0x1998) /\
       read X0 s = word a /\ read X13 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X9 s = word_add src (word ofs) /\ read X1 s = word bc /\
       read X5 s = word_add dst (word(LENGTH out)) /\
       read X7 s = word_add dst (word 253) /\
       read X6 s =
       word_add dst (word(if EVEN(LENGTH out) then 254 else 253)) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fdf_common]));;

(*** At 0x191c, after the first weight y of an iteration ***)

let fdf_tmid = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
   list_mk_conj
     [`LENGTH(out:num list) <= 253 /\
       read PC s = word(pc + 0x191c) /\
       read X0 s = word a /\ read X13 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X2 s = word_add src (word ofs) /\ read X3 s = word bc /\
       read X10 s = word_add dst (word(LENGTH out)) /\
       read X7 s = word_add dst (word 253) /\
       read X6 s =
       word_add dst (word(if EVEN(LENGTH out) then 254 else 253)) /\
       read (memory :> bytes(dst,LENGTH out + 1)) s =
       num_of_bytelist(MAP (word:num->byte) (APPEND out [y])) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (b,a,8 * ofs + 64 - bc,APPEND out [y]) w)`;
      fdf_common]));;

let FDF_TC = prove
 (mk_fdf_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`]
   fdf_tend
   (let s = `s:armstate` in
    mk_abs(s,mk_disj(list_mk_comb(fdf_tinv,[`256 - LENGTH(out:num list)`;s]),
                     mk_comb(fd_post,s)))),
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ASM_CASES_TAC `LENGTH(out:num list) <= 253` THENL
   [ZSTD_STEPS_TAC (1--4) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ZSTD_STEPS_TAC (1--11) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    FD_FULL_TAC]);;

let FDF_TB_FIN_TAC ofs' bc' =
  let out' = `APPEND (APPEND out [y:num]) [fse_symbol cs tl b]` in
  let b' = `fse_base cs tl b +
            zstd_back (st:byte list) (8 * ofs + 64 - bc)
                      (fse_nbits cs tl b)` in
  let wtac =
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(p ==> p') ==> p \/ q ==> p' \/ q`) THEN
    DISCH_TAC THEN
    EXISTS_TAC (mk_binop `(-):num->num->num` `256`
                  (mk_comb(`LENGTH:num list->num`,out'))) THEN
    ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC in
  SUBGOAL_THEN (mk_eq(vsubst [ofs',`ofs:num`; bc',`bc:num`]
                        `8 * ofs + 64 - bc`,
                      `(8 * ofs + 64 - bc) - fse_nbits cs tl b`))
  ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:num list->num`,out'),
                      `LENGTH(out:num list) + 2`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ZSTD_CONTINUE_WITH_TAC wtac FDF_TC
   [b',`b:num`; ofs',`ofs:num`; bc',`bc:num`; out',`out:num list`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0; EVEN_ADD; ARITH; WORD_ADD_ASSOC_NUM] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let fdf_tb_post =
  let s = `s:armstate` and m' = `m':num` in
  mk_abs(s,mk_disj(mk_exists(m',mk_conj(`m' < 256 - LENGTH(out:num list)`,
                                        list_mk_comb(fdf_tinv,[m';s]))),
                   mk_comb(fd_post,s)));;

let FDF_TB = prove
 (mk_fdf_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`; `y:num`]
   fdf_tmid fdf_tb_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(out:num list) = 253` THENL
   [SUBGOAL_THEN `~EVEN(LENGTH(out:num list))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                          ASSUME_TAC th) THEN
    ZSTD_STEPS_TAC (1--11) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    FD_FULL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(out:num list) <= 252` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  FD_ENTRY2_TAC `b:num` `s0:armstate` THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `b:num`] FSE_FAST_NBITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `a:num`] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_CASES_TAC `EVEN(LENGTH(out:num list))` THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                        ASSUME_TAC th) THEN
  (ASM_CASES_TAC `bc + fse_nbits cs tl b <= 64` THENL
    [ZSTD_STEPS_TAC (1--16) THEN FDF_NEWSTATE_TAC THEN
     FD_SPEC_STEP_TAC `b:num` `a:num` `APPEND out [y:num]` THEN
     FD_MEM_SNOC_TAC `APPEND out [y:num]` `LENGTH(out:num list) + 1`
       `fse_symbol cs tl b` `s16:armstate` THEN
     FD_RELOAD_TAC 17 `bc + fse_nbits cs tl b` FDF_TB_FIN_TAC;
     ZSTD_STEPS_TAC (1--18) THEN
     FD_DTABLE_READ_TAC `a:num` `s18:armstate` THEN
     ZSTD_STEPS_TAC (19--30) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
     FD_MEM_SNOC_TAC `APPEND out [y:num]` `LENGTH(out:num list) + 1`
       `fse_symbol cs tl b` `s30:armstate` THEN
     FD_MEM_SNOC_TAC `APPEND (APPEND out [y:num]) [fse_symbol cs tl b]`
       `LENGTH(out:num list) + 2` `fse_symbol cs tl a` `s30:armstate` THEN
     FD_STOP_TAC `b:num` `a:num` `APPEND out [y:num]`]));;

(*** The tail loop at 0x18ac in fast mode ***)

let FDF_TA_FIN_TAC ofs' bc' =
  let a' = `fse_base cs tl a +
            zstd_back (st:byte list) (8 * ofs + 64 - bc)
                      (fse_nbits cs tl a)` in
  SUBGOAL_THEN (mk_eq(vsubst [ofs',`ofs:num`; bc',`bc:num`]
                        `8 * ofs + 64 - bc`,
                      `(8 * ofs + 64 - bc) - fse_nbits cs tl a`))
  ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_TB
   [a',`a:num`; ofs',`ofs:num`; bc',`bc:num`; `fse_symbol cs tl a`,`y:num`]
  THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FDF_TLOOP = prove
 (mk_fdf_goal []
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      list_mk_comb(fdf_tinv,[`m:num`; `s:armstate`]))))
   fd_post,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
   [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`] THEN
  PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  FD_ENTRY2_TAC `a:num` `s0:armstate` THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `a:num`] FSE_FAST_NBITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `b:num`] FSE_SYMBOL_RANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_CASES_TAC `bc + fse_nbits cs tl a <= 64` THENL
   [ZSTD_STEPS_TAC (1--13) THEN FDF_NEWSTATE_TAC THEN
    FD_SPEC_STEP_TAC `a:num` `b:num` `out:num list` THEN
    FD_MEM_SNOC_TAC `out:num list` `LENGTH(out:num list)`
      `fse_symbol cs tl a` `s13:armstate` THEN
    FD_RELOAD_TAC 14 `bc + fse_nbits cs tl a` FDF_TA_FIN_TAC;
    ZSTD_STEPS_TAC (1--15) THEN
    FD_DTABLE_READ_TAC `b:num` `s15:armstate` THEN
    ZSTD_STEPS_TAC (16--27) THEN PUFF_FINAL_TAC THEN DISJ2_TAC THEN
    FD_MEM_SNOC_TAC `out:num list` `LENGTH(out:num list)`
      `fse_symbol cs tl a` `s27:armstate` THEN
    FD_MEM_SNOC_TAC `APPEND out [fse_symbol cs tl a]`
      `LENGTH(out:num list) + 1` `fse_symbol cs tl b` `s27:armstate` THEN
    FD_STOP_TAC `a:num` `b:num` `out:num list`]);;

(*** At 0x1890, after the main loop, in fast mode ***)

let fdf_ttail = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
   list_mk_conj
     [`LENGTH(out:num list) <= 252 /\ EVEN(LENGTH out) /\
       read PC s = word(pc + 0x1890) /\
       read X0 s = word a /\ read X13 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X9 s = word_add src (word ofs) /\ read X1 s = word bc /\
       read X10 s = word_add dst (word(LENGTH out)) /\
       read X21 s = word_add dst (word 255) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\
       bc <= 64 /\ (ofs = 0 \/ bc <= 7) /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fdf_common]));;

let FDF_TAIL = prove
 (mk_fdf_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`]
   fdf_ttail fd_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN ZSTD_STEPS_TAC (1--7) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(REWR_CONV(MP
      (SPECL [`dst:int64`; `LENGTH(out:num list)`] FD_X11)
      (CONJ (ARITH_RULE `LENGTH(out:num list) <= 252
                         ==> LENGTH out <= 254`
             |> C MP (ASSUME `LENGTH(out:num list) <= 252`))
            (ASSUME `EVEN(LENGTH(out:num list))`))))) th
    with Failure _ -> th) THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_TLOOP [] THEN
  MEMSAFE_ELIM_TAC THEN
  EXISTS_TAC `256 - LENGTH(out:num list)` THEN
  MAP_EVERY EXISTS_TAC
   [`a:num`; `b:num`; `ofs:num`; `bc:num`; `out:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC);;

(*** At 0x1858, the main loop in fast mode ***)

let fdf_minv = with_memsafe fd_rr fd_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   list_mk_exists([`a:num`; `b:num`; `ofs:num`; `bc:num`; `k:num`;
                   `out:num list`],
    list_mk_conj
     [`m = 63 - k /\ LENGTH(out:num list) = 4 * k /\ k <= 63 /\
       read PC s = word(pc + 0x1858) /\
       read X0 s = word a /\ read X13 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X9 s = word_add src (word ofs) /\ read X1 s = word bc /\
       read X10 s = word_add dst (word(LENGTH out)) /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fdf_common])));;

(*** At 0x1798, after the reload, with the flag for room for 4 weights ***)

let fdf_mbody = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`LENGTH(out:num list) = 4 * k /\ k <= 63 /\
       read PC s = word(pc + 0x1798) /\
       read X0 s = word a /\ read X13 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X9 s = word_add src (word ofs) /\ read X1 s = word bc /\
       read X10 s = word_add dst (word(LENGTH out)) /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read X11 s = word(if 4 * k < 252 then 1 else 0) /\
       read (memory :> bytes(dst,LENGTH out)) s =
       num_of_bytelist(MAP (word:num->byte) out) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 7 /\
       (!w. fse_weights cs tl st (s1,s2,q0,[]) w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,out) w)`;
      fdf_common]));;

let fdf_mpost k =
  let s = `s:armstate` and m' = `m':num` in
  mk_abs(s,mk_disj(mk_exists(m',mk_conj(mk_binop `(<):num->num->bool` m'
                                          (mk_binop `(-):num->num->num`
                                             `63` k),
                                        list_mk_comb(fdf_minv,[m';s]))),
                   mk_comb(fd_post,s)));;

let FDF_ENTRY_TAC u s =
  FD_ENTRY2_TAC u s THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; u] FSE_FAST_NBITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let FDF_MBODY = prove
 (mk_fdf_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`; `k:num`; `out:num list`]
   fdf_mbody (fdf_mpost `k:num`),
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `4 * k < 252` THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                        ASSUME_TAC th) THENL
   [ALL_TAC;
    ZSTD_STEPS_TAC (1--6) THEN
    ZSTD_CONTINUE_WITH_TAC
     (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
      FIRST_ASSUM ACCEPT_TAC) FDF_TAIL [] THEN
    MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[EVEN_MULT; ARITH] THEN ZSTD_ARITH_TAC] THEN
  FIRST_ASSUM((fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         ASSUME_TAC th) o
    check (fun th -> concl th = `LENGTH(out:num list) = 4 * k`)) THEN
  SUBGOAL_THEN `k <= 62` ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  FDF_ENTRY_TAC `a:num` `s0:armstate` THEN
  ZSTD_STEPS_TAC (1--13) THEN FDF_ENTRY_TAC `b:num` `s13:armstate` THEN
  ZSTD_STEPS_TAC (14--16) THEN FDF_NEWSTATE_TAC THEN
  FD_SPEC_STEP2_TAC `a:num` `b:num` `bc:num` `out:num list` `a1:num` THEN
  ZSTD_STEPS_TAC (17--24) THEN FDF_NEWSTATE_TAC THEN
  FD_SPEC_STEP2_TAC `b:num` `a1:num` `fse_nbits cs tl a + bc`
    `APPEND out [fse_symbol cs tl a]` `b1:num` THEN
  ZSTD_STEPS_TAC (25--27) THEN FDF_ENTRY_TAC `a1:num` `s27:armstate` THEN
  ZSTD_STEPS_TAC (28--35) THEN FDF_ENTRY_TAC `b1:num` `s35:armstate` THEN
  ZSTD_STEPS_TAC (36--46) THEN FDF_NEWSTATE_TAC THEN
  FD_SPEC_STEP2_TAC `a1:num` `b1:num`
    `fse_nbits cs tl b + fse_nbits cs tl a + bc`
    `APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b]`
    `a2:num` THEN
  FD_SPEC_STEP2_TAC `b1:num` `a2:num`
    `fse_nbits cs tl a1 + fse_nbits cs tl b + fse_nbits cs tl a + bc`
    `APPEND (APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b])
            [fse_symbol cs tl a1]`
    `b2:num` THEN
  ZSTD_STEPS_TAC (47--48) THEN
  FD_MEM_SNOC2_TAC `out:num list` `4 * k` `fse_symbol cs tl a`
    `s48:armstate` THEN
  FD_MEM_SNOC2_TAC `APPEND out [fse_symbol cs tl a]` `4 * k + 1`
    `fse_symbol cs tl b` `s48:armstate` THEN
  FD_MEM_SNOC2_TAC
    `APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b]`
    `4 * k + 2` `fse_symbol cs tl a1` `s48:armstate` THEN
  FD_MEM_SNOC2_TAC
    `APPEND (APPEND (APPEND out [fse_symbol cs tl a]) [fse_symbol cs tl b])
            [fse_symbol cs tl a1]`
    `4 * k + 3` `fse_symbol cs tl b1` `s48:armstate` THEN
  ABBREV_TAC
   `out4 = APPEND (APPEND (APPEND (APPEND out [fse_symbol cs tl a])
                                  [fse_symbol cs tl b])
                          [fse_symbol cs tl a1])
                  [fse_symbol cs tl b1]` THEN
  SUBGOAL_THEN `LENGTH(out4:num list) = 4 * k + 4` ASSUME_TAC THENL
   [EXPAND_TAC "out4" THEN ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  PUFF_FINAL_TAC THEN DISJ1_TAC THEN EXISTS_TAC `63 - (k + 1)` THEN
  CONJ_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`a2:num`; `b2:num`; `ofs:num`;
    `fse_nbits cs tl b1 + fse_nbits cs tl a1 + fse_nbits cs tl b +
     fse_nbits cs tl a + bc`;
    `k + 1`; `out4:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[WORD_ADD_ASSOC_NUM] THEN
  ZSTD_ARITH_TAC);;

(*** The main loop at 0x1858 in fast mode ***)

let FDF_MLOOP_BODY_TAC ofs' bc' =
  FD_POS_TAC ofs' bc' THEN
  MP_TAC(SPECL [`dst:int64`; `k:num`] FD_CSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_MBODY
   [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FDF_MLOOP_TAIL_TAC ofs' bc' =
  FD_POS_TAC ofs' bc' THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISJ2_TAC THEN
    FIRST_ASSUM ACCEPT_TAC) FDF_TAIL
   [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[EVEN_MULT; ARITH; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FDF_MLOOP = prove
 (mk_fdf_goal []
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      list_mk_comb(fdf_minv,[`m:num`; `s:armstate`]))))
   fd_post,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  MAP_EVERY ENSURES_EXISTS_PRE_TAC
   [`a:num`; `b:num`; `ofs:num`; `bc:num`; `k:num`; `out:num list`] THEN
  PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `bc:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--7) THEN FD_SLICE_TAC `ofs - bc DIV 8` `s7:armstate` THEN
    ZSTD_STEPS_TAC (8--9) THEN
    FDF_MLOOP_BODY_TAC `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (1--6) THEN FDF_MLOOP_TAIL_TAC `ofs:num` `bc:num`;
    ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [ZSTD_STEPS_TAC (1--9) THEN FD_SLICE_TAC `ofs - bc DIV 8` `s9:armstate` THEN
    ZSTD_STEPS_TAC (10--14) THEN
    FDF_MLOOP_BODY_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    ZSTD_STEPS_TAC (1--13) THEN FD_SLICE_TAC `0` `s13:armstate` THEN
    ZSTD_STEPS_TAC [14] THEN
    FDF_MLOOP_TAIL_TAC `0` `bc - 8 * ofs`]);;

(*** The start of the decoding in fast mode ***)

(*** At 0x173c, after the reads of the two states ***)

let fdf_i3 = with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x173c) /\
       read X0 s = word a /\ read X13 s = word b /\
       a < 2 EXP tl /\ b < 2 EXP tl /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X2 s = word_add src (word ofs) /\ read X1 s = word bc /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (!w. fse_stream cs tl st w <=>
            fse_weights cs tl st (a,b,8 * ofs + 64 - bc,[]) w)`;
      fdf_common]));;

let FDF_I3_TAC ofs' bc' =
  FD_POS_TAC ofs' bc' THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_MLOOP
   [`a:num`,`s1:num`; `b:num`,`s2:num`; `8 * ofs + 64 - bc`,`q0:num`] THEN
  MEMSAFE_ELIM_TAC THEN EXISTS_TAC `63 - 0` THEN
  MAP_EVERY EXISTS_TAC
   [`a:num`; `b:num`; ofs'; bc'; `0`; `[]:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[LENGTH; MAP; num_of_bytelist; READ_MEMORY_BYTES_0;
                  WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FDF_I3 = prove
 (mk_fdf_goal [`a:num`; `b:num`; `ofs:num`; `bc:num`] fdf_i3 fd_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `bc:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
     [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--5) THEN FD_SLICE_TAC `ofs - bc DIV 8` `s5:armstate` THEN
    ZSTD_STEPS_TAC (6--9) THEN FDF_I3_TAC `ofs - bc DIV 8` `bc MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (1--8) THEN FDF_I3_TAC `ofs:num` `bc:num`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bc DIV 8 <= ofs` THENL
   [ZSTD_STEPS_TAC (1--10) THEN
    FD_SLICE_TAC `ofs - bc DIV 8` `s10:armstate` THEN
    ZSTD_STEPS_TAC (11--15) THEN
    FDF_I3_TAC `ofs - bc DIV 8` `bc - 8 * bc DIV 8`;
    ZSTD_STEPS_TAC (1--13) THEN FD_SLICE_TAC `0` `s13:armstate` THEN
    ZSTD_STEPS_TAC (14--18) THEN FDF_I3_TAC `0` `bc - 8 * ofs`]);;

(*** The reads of the states: the bits in either order of the sum ***)

let FDF_INITSTATE_TAC =
  W(fun (asl,w) ->
    let s = rand w in
    let conv tm =
      let ith = try PART_MATCH (lhs o rand) FD_BITS_NORMAL tm
                with Failure _ ->
                  PART_MATCH (lhs o rand) FD_BITS_NORMAL_ALT tm in
      MP ith (TAC_PROOF((asl,lhand(concl ith)),
                        CONJ_TAC THEN SIMPLE_ARITH_TAC)) in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),_)
          when s' = s -> (try CONV_RULE(RAND_CONV conv) th
                          with Failure _ -> th)
      | _ -> th));;

let fdf_common0 =
  let cs = conjuncts fdf_common in
  list_mk_conj(filter (fun c ->
    not(can (term_match [] `read X12 s = x`) c) &&
    not(can (term_match [] `read X19 s = x`) c)) cs);;

(*** At 0x16e0, after the read of the first state ***)

let fdf_i2 = subst [fdw_dt,`dt:int64`] (with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x16e0) /\
       read X0 s = word(zstd_back st r tl) /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X9 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X1 s = word tl /\
       read X3 s = word_zx(word(2 EXP tl - 1):int32) /\
       read X12 s = word_add src (word 8) /\ read X19 s = wksp /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (ofs = 0 \/ bc <= 7) /\
       zstd_end st r /\ tl <= r /\ 8 * ofs + 64 - bc = r - tl`;
      fdf_common0])));;

let fdfw_hyps = subst [fdw_dt,`dt:int64`] fdf_hyps;;

let mk_fdfw_goal extra pre post =
  let tm = mk_imp(fdfw_hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; fd_frame]) in
  let vs = fdw_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_fdfw_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let FDF_I2_I3_TAC ofs' bc' =
  FD_POSQ_TAC ofs' bc' `r - 2 * tl` THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_I3
   [fdw_dt,`dt:int64`; `zstd_back (st:byte list) r tl`,`a:num`;
    `zstd_back (st:byte list) (r - tl) tl`,`b:num`;
    ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[ZSTD_BACK_BOUND; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FDF_I2_LOOP_TAC =
  FD_POSQ_TAC `ofs:num` `tl + bc` `r - 2 * tl` THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_MLOOP
   [fdw_dt,`dt:int64`; `zstd_back (st:byte list) r tl`,`s1:num`;
    `zstd_back (st:byte list) (r - tl) tl`,`s2:num`;
    `r - 2 * tl`,`q0:num`] THEN
  MEMSAFE_ELIM_TAC THEN EXISTS_TAC `63 - 0` THEN
  MAP_EVERY EXISTS_TAC
   [`zstd_back (st:byte list) r tl`; `zstd_back (st:byte list) (r - tl) tl`;
    `ofs:num`; `tl + bc`; `0`; `[]:num list`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[LENGTH; MAP; num_of_bytelist; READ_MEMORY_BYTES_0;
                  WORD_ADD_0; ZSTD_BACK_BOUND; WORD_ADD_ASSOC_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FDF_I2 = prove
 (mk_fdfw_goal [`r:num`; `ofs:num`; `bc:num`] fdf_i2 fdw_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `tl + bc <= 64` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!w. ~fse_stream cs tl (st:byte list) w` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FSE_STREAM_SHORT THEN EXISTS_TAC `r:num` THEN
      ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC;
      ALL_TAC] THEN
    ZSTD_STEPS_TAC (1--16) THEN PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV] THEN
  SUBGOAL_THEN `2 * tl <= r` ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cs:int list`; `tl:num`; `st:byte list`; `r:num`]
    FSE_STREAM_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ZSTD_STEPS_TAC (1--7) THEN FDF_INITSTATE_TAC THEN
  MP_TAC(SPEC `tl + bc:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 7`
    STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (8--12) THEN
    FD_SLICE_TAC `ofs - (tl + bc) DIV 8` `s12:armstate` THEN
    ZSTD_STEPS_TAC (13--14) THEN
    FDF_I2_I3_TAC `ofs - (tl + bc) DIV 8` `(tl + bc) MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (8--13) THEN FDF_I2_LOOP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 7`
  STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(tl + bc) DIV 8 <= ofs` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 /\ ~(ofs = 0) ==> x <= ofs`) THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (8--17) THEN
  FD_SLICE_TAC `ofs - (tl + bc) DIV 8` `s17:armstate` THEN
  ZSTD_STEPS_TAC (18--20) THEN
  FDF_I2_I3_TAC `ofs - (tl + bc) DIV 8` `(tl + bc) - 8 * (tl + bc) DIV 8`);;

(*** At 0x1670, after BIT_initDStream, in fast mode ***)

let fdf_i1 = subst [fdw_dt,`dt:int64`] (with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x1670) /\
       read X8 s =
       word((num_of_bytelist st DIV 2 EXP (8 * ofs)) MOD 2 EXP 64) /\
       read X4 s = word_add src (word ofs) /\ read X2 s = word bc /\
       read X19 s = wksp /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read (memory :> bytes16 (word_add wksp (word 512))) s = word tl /\
       (ofs = 0 \/ ofs + 8 <= LENGTH(st:byte list)) /\ bc <= 64 /\
       (ofs = 0 \/ bc <= 8) /\ zstd_end st (8 * ofs + 64 - bc)`;
      fdf_common0])));;

let FDF_I1_TAC ofs' bc' =
  FD_POSQ_TAC ofs' bc' `(8 * ofs + 64 - bc) - tl` THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_I2
   [`8 * ofs + 64 - bc`,`r:num`; ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN ZSTD_ARITH_TAC;;

let FDF_I1 = prove
 (mk_fdfw_goal [`ofs:num`; `bc:num`] fdf_i1 fdw_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `ofs <= LENGTH(st:byte list)` ASSUME_TAC THENL
   [ZSTD_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`; `tl:num`] ZSTD_BIT_MASK_READ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `tl <= 6` THEN ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o
      CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))] THEN
  SUBGOAL_THEN `val(word tl:int64) = tl` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `tl <= 6` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `tl + bc <= 64` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!w. ~fse_stream cs tl (st:byte list) w` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FSE_STREAM_SHORT THEN
      EXISTS_TAC `8 * ofs + 64 - bc` THEN
      ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC;
      ALL_TAC] THEN
    ZSTD_STEPS_TAC [1] THEN PUFF_ADRP_TAC THEN ZSTD_STEPS_TAC (2--21) THEN
    PUFF_FINAL_TAC THEN
    ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV] THEN
  ZSTD_STEPS_TAC [1] THEN PUFF_ADRP_TAC THEN
  ZSTD_STEPS_TAC (2--10) THEN FDF_INITSTATE_TAC THEN
  ZSTD_STEPS_TAC (11--12) THEN
  MP_TAC(SPEC `tl + bc:num` DIVISION_8_ALT) THEN STRIP_TAC THEN
  ASM_CASES_TAC `8 <= ofs` THENL
   [SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 8`
    STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
    ZSTD_STEPS_TAC (13--18) THEN
    FD_SLICE_TAC `ofs - (tl + bc) DIV 8` `s18:armstate` THEN
    ZSTD_STEPS_TAC (19--20) THEN
    FDF_I1_TAC `ofs - (tl + bc) DIV 8` `(tl + bc) MOD 8`;
    ALL_TAC] THEN
  ASM_CASES_TAC `ofs = 0` THENL
   [ZSTD_STEPS_TAC (13--18) THEN FDF_I1_TAC `ofs:num` `tl + bc`; ALL_TAC] THEN
  SUBGOAL_THEN `ofs + 8 <= LENGTH(st:byte list) /\ bc <= 8`
  STRIP_ASSUME_TAC THENL [ZSTD_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(tl + bc) DIV 8 <= ofs` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 /\ ~(ofs = 0) ==> x <= ofs`) THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (13--23) THEN
  FD_SLICE_TAC `ofs - (tl + bc) DIV 8` `s23:armstate` THEN
  ZSTD_STEPS_TAC (24--25) THEN
  FDF_I1_TAC `ofs - (tl + bc) DIV 8` `(tl + bc) - 8 * (tl + bc) DIV 8`);;

(*** At 0x163c, the start of the decoding in fast mode ***)

let fdf_i0 = subst [fdw_dt,`dt:int64`] (with_memsafe fd_rr fd_wr
 (mk_abs(`s:armstate`,
    list_mk_conj
     [`read PC s = word(pc + 0x163c) /\
       read X18 s = word(LENGTH(st:byte list)) /\ read X19 s = wksp /\
       read X5 s = word_add dst (word 252) /\
       read X21 s = word_add dst (word 255) /\
       read (memory :> bytes16 (word_add wksp (word 512))) s = word tl`;
      fdf_common0])));;

let FDF_I0_GOON_TAC ofs' bc' =
  let r = vsubst [ofs',`ofs:num`; bc',`bc:num`] `8 * ofs + 64 - bc` in
  SUBGOAL_THEN (mk_comb(`zstd_end (st:byte list)`,r)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`st:byte list`; r] ZSTD_END_LAST) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SIMPLE_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN ZSTD_ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN ASM_REWRITE_TAC[]) FDF_I1
   [ofs',`ofs:num`; bc',`bc:num`] THEN
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0; WORD_CONTAINER_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (ZSTD_ARITH_TAC ORELSE (AP_TERM_TAC THEN ZSTD_ARITH_TAC));;

let FDF_SMALL_TAC k =
  let numt = mk_small_numeral in
  let els = map (fun i -> list_mk_icomb "EL" [numt i; `st:byte list`])
                (0--(k-1)) in
  let sum = itlist (fun e acc ->
              mk_binop `(+):num->num->num` (mk_icomb(`val:byte->num`,e))
                (mk_binop `( * ):num->num->num` `256` acc)) els `0` in
  let lst = mk_list(els,`:byte`) in
  let bc = subst [numt(8 * (8 - k)),`n:num`] `(32 - bitsize vb + n) - 23` in
  let memfact i =
    MP_TAC(ISPECL [`src:int64`; `st:byte list`; numt i; `s5:armstate`]
      READ_MEMORY_BYTES8_BYTELIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] in
  let range = ARITH_RULE(mk_eq(mk_binop `(<):num->num->bool` `i:num` (numt k),
                list_mk_disj(map (fun j -> mk_eq(`i:num`,numt j))
                                 (0--(k-1))))) in
  ZSTD_STEPS_TAC (4--5) THEN MAP_EVERY memfact (0--(k-1)) THEN
  SUBGOAL_THEN (mk_eq(`num_of_bytelist(st:byte list)`,sum)) ASSUME_TAC THENL
   [SUBGOAL_THEN (mk_eq(`st:byte list`,lst))
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] THEN
                 REWRITE_TAC[num_of_bytelist]) THEN
    REWRITE_TAC[LIST_EQ; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[range] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `vb = 0` THENL
   [ZSTD_RUN_TAC THEN FD_NOEND_TAC;
    FD_VB_FACTS_TAC THEN ZSTD_SIM_UNTIL_TAC [0x1670] THEN
    FDF_I0_GOON_TAC `0` bc];;

let FDF_I0 = prove
 (mk_fdfw_goal [] fdf_i0 fdw_spost,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  ASM_CASES_TAC `LENGTH(st:byte list) = 0` THENL
   [ZSTD_STEPS_TAC (1--10) THEN
    SUBGOAL_THEN `!w. ~fse_stream cs tl (st:byte list) w` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC FSE_STREAM_NOEND THEN
      REWRITE_TAC[zstd_end] THEN ASM_MESON_TAC[LENGTH_EQ_NIL];
      ALL_TAC] THEN
    PUFF_FINAL_TAC THEN ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--2) THEN FD_LASTBYTE_TAC THEN
  ASM_CASES_TAC `8 <= LENGTH(st:byte list)` THENL
   [ASM_CASES_TAC `vb = 0` THENL
     [ZSTD_STEPS_TAC (4--15) THEN FD_NOEND_TAC;
      FD_VB_FACTS_TAC THEN ZSTD_STEPS_TAC (4--12) THEN
      FD_SLICE_TAC `LENGTH(st:byte list) - 8` `s12:armstate` THEN
      ZSTD_STEPS_TAC [13] THEN
      FDF_I0_GOON_TAC `LENGTH(st:byte list) - 8` `32 - bitsize vb - 23`];
    SUBGOAL_THEN
     `LENGTH(st:byte list) = 1 \/ LENGTH st = 2 \/ LENGTH st = 3 \/
      LENGTH st = 4 \/ LENGTH st = 5 \/ LENGTH st = 6 \/ LENGTH st = 7`
    (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [SIMPLE_ARITH_TAC; FDF_SMALL_TAC 1; FDF_SMALL_TAC 2; FDF_SMALL_TAC 3;
      FDF_SMALL_TAC 4; FDF_SMALL_TAC 5; FDF_SMALL_TAC 6; FDF_SMALL_TAC 7]]);;

(* ------------------------------------------------------------------------- *)
(* The entry: FSE_readNCount, the checks of the Accuracy_Log and of the      *)
(* workspace, FSE_buildDTable and the decoding in the mode of its header.    *)
(* ------------------------------------------------------------------------- *)

(*** The counts at nc as 16-bit words, from the list of all of them ***)

let READ_MEMORY_NCLIST_PREFIX = prove
 (`!(a:int64) cs n s.
        LENGTH cs <= n /\
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist(fse_nclist cs n)
        ==> read (memory :> bytes(a,2 * LENGTH cs)) s =
            num_of_wordlist(MAP (iword:int->int16) cs)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MAP (iword:int->int16) cs =
                SUB_LIST(0,LENGTH cs) (fse_nclist cs n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_SUB_LIST; LENGTH_FSE_NCLIST] THEN
    ASM_SIMP_TAC[SUB_0; ARITH_RULE `l <= n ==> MIN l n = l`] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_MAP; EL_SUB_LIST; LENGTH_FSE_NCLIST; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[EL_FSE_NCLIST; ARITH_RULE `i < l /\ l <= n ==> i < n`];
    ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; DIMINDEX_16] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `16 * k = 8 * (2 * k)`;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  ASM_ARITH_TAC);;

(*** The header of the table: tableLog and fastMode ***)

let READ_DTABLE_HEADER = prove
 (`!(dt:int64) tl f s.
        tl < 65536 /\ f < 65536 /\
        read (memory :> bytes32 dt) s = word(tl + 65536 * f)
        ==> read (memory :> bytes16 dt) s = word tl /\
            read (memory :> bytes16 (word_add dt (word 2))) s = word f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (bytes(dt,4)) (read memory s) = tl + 65536 * f`
  MP_TAC THENL
   [ASM_REWRITE_TAC[VAL_READ_MEMORY_BYTES32] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(ARITH_RULE `4 = 2 + 2`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; VAL_READ_MEMORY_BYTES16] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ABBREV_TAC `x = val(read (memory :> bytes16 dt) s)` THEN
  ABBREV_TAC `y = val(read (memory :> bytes16 (word_add dt (word 2))) s)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `x < 65536 /\ y < 65536` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN CONJ_TAC THEN
    W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
    REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `x:num = tl /\ y:num = f` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`tl + 65536 * f`; `65536`; `f:num`; `tl:num`]
      DIVMOD_UNIQ) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `tl + 65536 * f`)) THEN
    MP_TAC(SPECL [`x + 65536 * y`; `65536`; `y:num`; `x:num`]
      DIVMOD_UNIQ) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["tl"; "f"] THEN MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
  REWRITE_TAC[WORD_VAL]);;

(*** The frame, with the stack below the stack pointer as one region ***)

let FDE_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 96):int64 =
  word_add (word_sub stackpointer (word 256)) (word 160)`;;

let FDE_FRAME_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[FDE_STACK_REBASE; WORD_ADD_ASSOC_NUM]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  MONOTONE_MAYCHANGE_TAC;;

(*** An error return with the result x0 ***)

let FDE_ERROR_TAC =
  ZSTD_RUN_TAC THEN PUFF_FINAL_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[zstd_is_error; FD_SP_RESTORE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    FDE_FRAME_TAC];;

let FDE_START_TAC =
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
  ENSURES_PRESERVED_TAC "x29" `X29` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  REWRITE_TAC[C_ARGUMENTS] THEN ENSURES_INIT_TAC "s0" THEN
  ZSTD_STEPS_TAC (1--26) THEN
  SUBGOAL_THEN `~(word_sub stackpointer (word 96):int64 = word 0)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB_EQ_0]; ALL_TAC] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 4440):int64`; `word_sub stackpointer (word 96):int64`;
    `wksp:int64`; `word_add (word_sub stackpointer (word 96)) (word 92):int64`;
    `word_add (word_sub stackpointer (word 96)) (word 88):int64`;
    `cSrc:int64`; `blk:byte list`; `255`; `fcpy:int64`; `fset:int64`;
    `ea:int64`; `el:num`; `ev:num`] FSE_READ_NCOUNT_CORRECT))) THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM] THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC
                      NUM_LE_CONV)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC ZSTD_EXEC "s27" THEN EVENTS_UNABBREV_TAC;;

let FDE_ERRVAL_LEMMA = prove
 (`!x:int64. 18446744073709551496 < val x
             ==> 18446744073709551616 <= val x + 120 /\
                 ~(val(word_add x (word 120)) = 0)`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(x:int64)`,`v:num`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(v + 120) MOD 18446744073709551616 = (v + 120) - 18446744073709551616`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(*** No description: the error of FSE_readNCount ***)

let FDE_NONC_TAC =
  SUBGOAL_THEN `!r. ~fse_ncount T 15 256 (blk:byte list) r` ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_neg(concl th) && is_exists(rand(concl th)))) THEN
    REWRITE_TAC[NOT_EXISTS_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s27 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s27 = x0r`] THEN
  SUBGOAL_THEN `!w. ~fse_weight_block T (blk:byte list) w` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FSE_WEIGHT_BLOCK_NONE]; ALL_TAC] THEN
  ZSTD_STEPS_TAC (28--30) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  FDE_ERROR_TAC;;

let FDE_VALID_LENGTH_TAC : tactic = fun (asl,w as gl) ->
  let th = snd(find (fun (_,th) ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "fse_valid"
    with Failure _ -> false) asl) in
  ASSUME_TAC(MATCH_MP FSE_VALID_LENGTH th) gl;;

(*** With the description (cs,alog,m) ***)

let FDE_NC_TAC =
  FIRST_X_ASSUM(X_CHOOSE_THEN `cs:int list` (X_CHOOSE_THEN `alog:num`
     (X_CHOOSE_TAC `m:num`))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cs:int list`; `alog:num`; `m:num`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `fse_ncount`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`T`; `15`; `256`; `blk:byte list`; `cs:int list`; `alog:num`;
                `m:num`] FSE_NCOUNT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`T`; `15`; `256`; `blk:byte list`; `cs:int list`; `alog:num`;
                `m:num`] FSE_NCOUNT_VALID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FDE_VALID_LENGTH_TAC THEN
  SUBGOAL_THEN `val(word m:int64) = m` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `m <= LENGTH(blk:byte list)` THEN
    UNDISCH_TAC `LENGTH(blk:byte list) < 2 EXP 24` THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (28--30);;

(*** An error after the description: no weights ***)

let FDE_NC_FACT asl =
  snd(find (fun (_,th) ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "fse_ncount"
    with Failure _ -> false) asl);;

let FDE_NOBLOCK_TAC : tactic = fun (asl,w as gl) ->
  let th = MATCH_MP FSE_WEIGHT_BLOCK_STREAM (FDE_NC_FACT asl) in
  (SUBGOAL_THEN `!w. ~fse_weight_block T (blk:byte list) w` ASSUME_TAC THENL
    [REWRITE_TAC[th] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
     ALL_TAC]) gl;;

(*** The workspace check for 876 bytes, for tableLog 6 and 5 ***)

let FDE_SIZE_LEMMA = prove
 (`!l. 1 <= l
       ==> (876 < 4 * (195 + (75 + 2 * (l - 1 + 1)) DIV 4) <=> ~(l <= 12)) /\
           (876 < 4 * (163 + (43 + 2 * (l - 1 + 1)) DIV 4) <=> ~(l <= 92))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUB_ADD] THEN
  REWRITE_TAC[ARITH_RULE `876 < 4 * (195 + q) <=> 25 <= q`;
              ARITH_RULE `876 < 4 * (163 + q) <=> 57 <= q`] THEN
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC);;

(*** The case split on the workspace check, at the branch of the PC ***)

let FDE_SIZE_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let pcth = snd(find (fun (_,th) ->
    let c = concl th in
    is_eq c && lhs c = mk_comb(`read PC`,s) && is_cond(rhs c)) asl) in
  let cnd = rand(lhand(rator(rhs(concl pcth)))) in
  (ASM_CASES_TAC cnd THEN
   FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         ASSUME_TAC th)) gl;;

let FSE_FAST_LE1 = prove
 (`!cs tl. fse_fast cs tl <= 1`,
  REWRITE_TAC[fse_fast] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ARITH_TAC);;

(*** The header facts after FSE_buildDTable, at the state s ***)

let FDE_HEADER_TAC tl s =
  MP_TAC(SPECL [`word_add wksp (word 512):int64`; tl;
                mk_comb(mk_comb(`fse_fast`,`cs:int list`),tl); s]
    READ_DTABLE_HEADER) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`cs:int list`; tl] FSE_FAST_LE1) THEN ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o
      CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))];;

(*** Going on with the decoding, from FD_I0 or FDF_I0 (theorem th, with  ***)
(*** the instantiation insts, for the trace at the current state), in    ***)
(*** the frame of the entry                                               ***)

let FDE_HYPS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN
         CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN CONV_TAC NUM_REDUCE_CONV THEN
         NONOVERLAPPING_TAC;
         ASM_REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN SIMPLE_ARITH_TAC;
         ASM_REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN MEMSAFE_VAL_ARITH_TAC];;

let FDE_GOON_TAC wtac th insts =
  let frame_rule =
    REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
                 MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
                 SOME_FLAGS] in
  W(fun (asl,w as gl) ->
    let ev = current_events gl in
    let th1 = INST ((ev,`e:uarch_event list`)::insts) (SPEC_ALL th) in
    let hyp = lhand(concl th1) in
    let hth = TAC_PROOF((asl,hyp), FDE_HYPS_TAC) in
    let eth0 = frame_rule(MP th1 hth) in
    let _,bod = dest_abs(rand(rator w)) in
    let c = rator(rator(rand bod)) in
    let c0 = rand(concl eth0) in
    let sth = TAC_PROOF(([],list_mk_icomb "subsumed" [c0;c]),
                        SUBSUMED_MAYCHANGE_TAC) in
    let eth = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ sth eth0) in
    MATCH_MP_TAC(MATCH_MP EVENTUALLY_ENSURES eth) THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [BETA_TAC;
      CONJ_TAC THENL [FDE_FRAME_TAC; BETA_TAC THEN wtac]]);;

(*** The weights of the block as those of the stream after the description ***)

let FDE_BLOCK_EQ_TAC : tactic = fun (asl,w as gl) ->
  let th = MATCH_MP FSE_WEIGHT_BLOCK_STREAM (FDE_NC_FACT asl) in
  (MP_TAC th THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC) gl;;

let FDE_WTAC =
  X_GEN_TAC `s':armstate` THEN REWRITE_TAC[puff_memsafe] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e3:uarch_event list` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  RULE_ASSUM_TAC(fun th ->
    if (try fst(dest_const(fst(strip_comb(concl th)))) = "memaccess_inbounds"
        with Failure _ -> false)
    then CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
           (REWRITE_RULE[LENGTH_ZSTD_SUBLIST] th)
    else th) THEN
  W(fun (asl,w) ->
    let ms = find is_memsafe_clause (conjuncts w) in
    SUBGOAL_THEN ms ASSUME_TAC THENL [MEMSAFE_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[];;

let FDE_PRE_TAC =
  MEMSAFE_ELIM_TAC THEN ASM_REWRITE_TAC[LENGTH_ZSTD_SUBLIST] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(*** The call of FSE_buildDTable, for the table log of the description ***)

let FDE_REGVAL asl s r =
  rhs(concl(snd(find (fun (_,th) ->
    let c = concl th in
    is_eq c &&
    lhs c = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            r),s)) asl)));;

let FDE_BUILD_TAC : tactic = fun (asl,w as gl) ->
  let s = rand w in
  let x3 = FDE_REGVAL asl s `X3` and x4 = FDE_REGVAL asl s `X4`
  and x5 = FDE_REGVAL asl s `X5` in
  let tl = rand x3 and wsz = rand x5 in
  (MP_TAC(SPECL [`wksp:int64`; `cs:int list`; `256`; s]
     READ_MEMORY_NCLIST_PREFIX) THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN EVENTS_ABBREV_TAC THEN
   W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
    [`pc:num`; `word(pc + 4544):int64`; `word_add wksp (word 512):int64`;
     `wksp:int64`; x4; `cs:int list`; tl; wsz]
    FSE_BUILD_DTABLE_CORRECT))) THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
   REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
               MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
               MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
   ARM_BIGSTEP_TAC ZSTD_EXEC "s54" THEN EVENTS_UNABBREV_TAC) gl;;

(*** The decoding, in normal or fast mode as the header says ***)

let FDE_DECODE_TAC : tactic = fun (asl,w as gl) ->
  let ncf = concl(FDE_NC_FACT asl) in
  let tl = lhand(rand(rand ncf)) in
  let insts =
   [`word_add cSrc (word m):int64`,`src:int64`;
    `zstd_sublist blk m (LENGTH(blk:byte list) - m)`,`st:byte list`;
    tl,`tl:num`] in
  let ff = list_mk_comb(`fse_fast`,[`cs:int list`; tl]) in
  (FDE_HEADER_TAC tl `s54:armstate` THEN
   SUBGOAL_THEN `val(word_add cSrc (word m):int64) = val cSrc + m`
   ASSUME_TAC THENL
    [MATCH_MP_TAC VAL_WORD_ADD_NOWRAP THEN
     UNDISCH_TAC `val(cSrc:int64) + LENGTH(blk:byte list) + 8 < 2 EXP 64` THEN
     UNDISCH_TAC `m <= LENGTH(blk:byte list)` THEN ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(SPECL [`cSrc:int64`; `blk:byte list`; `m:num`; `s54:armstate`]
     READ_MEMORY_ZSTD_SUBLIST) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FDE_BLOCK_EQ_TAC THEN
   ASM_CASES_TAC (mk_eq(ff,`1`)) THENL
    [ZSTD_STEPS_TAC (55--62) THEN
     FDE_GOON_TAC FDE_WTAC FDF_I0 insts THEN FDE_PRE_TAC;
     SUBGOAL_THEN (mk_eq(ff,`0`)) ASSUME_TAC THENL
      [MP_TAC(SPECL [`cs:int list`; tl] FSE_FAST_LE1) THEN ASM_ARITH_TAC;
       ALL_TAC] THEN
     ZSTD_STEPS_TAC (55--62) THEN
     FDE_GOON_TAC FDE_WTAC FD_I0 insts THEN FDE_PRE_TAC]) gl;;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For the block blk of LENGTH blk bytes at cSrc, the      *)
(* result is the number of weights that it gives (fse_weight_block T, in the *)
(* zstd dialect), with them at dst, if it gives any, and an error code       *)
(* otherwise. The accesses, including those of memcpy and memset in          *)
(* FSE_readNCount, are loads from the block, the workspace, the stack (the   *)
(* 256 bytes below the stack pointer), the pointers to memcpy and memset and *)
(* their region (ea,el) and BIT_mask, and stores to dst, the workspace and   *)
(* the stack. FSE_readNCount needs its stack pointer, 96 below this one, to  *)
(* be nonzero.                                                               *)
(* ------------------------------------------------------------------------- *)

let FSE_DECOMPRESS_WKSP_CORRECT = prove
 (`!pc returnaddress stackpointer dst cSrc (blk:byte list) wksp fcpy fset
    ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 96) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     LENGTH blk < 2 EXP 24 /\ 8 <= val(cSrc:int64) /\
     val cSrc + LENGTH blk + 8 < 2 EXP 64 /\ val(dst:int64) + 255 < 2 EXP 64 /\
     nonoverlapping (dst,255) (cSrc,LENGTH blk) /\
     nonoverlapping (dst,255) (wksp:int64,876) /\
     nonoverlapping (dst,255) (word pc,0x20018) /\
     nonoverlapping (dst,255) (word_sub stackpointer (word 256),256) /\
     nonoverlapping (wksp,876) (cSrc,LENGTH blk) /\
     nonoverlapping (wksp,876) (word pc,0x20018) /\
     nonoverlapping (wksp,876) (word_sub stackpointer (word 256),256) /\
     nonoverlapping (wksp,876) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 256),256)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 256),256)
                    (cSrc,LENGTH blk) /\
     nonoverlapping (word_sub stackpointer (word 256),256) (ea,el)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0x10f4) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [dst; word 255; cSrc; word(LENGTH blk); word 6;
                            wksp; word 876] s /\
               read (memory :> bytes(cSrc,LENGTH blk)) s =
               num_of_bytelist blk /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!w. fse_weight_block T blk w
                    ==> read X0 s = word(LENGTH w) /\
                        read (memory :> bytes(dst,LENGTH w)) s =
                        num_of_bytelist(MAP word w)) /\
               ((!w. ~fse_weight_block T blk w)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [cSrc,LENGTH blk; wksp,876;
                       word_sub stackpointer (word 256),256;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [dst,255; wksp,876;
                       word_sub stackpointer (word 256),256]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(dst,255); memory :> bytes(wksp,876);
                      memory :> bytes(word_sub stackpointer (word 256),256)])`,
  REWRITE_TAC[GSYM puff_memsafe] THEN FDE_START_TAC THEN
  ASM_CASES_TAC `?cs alog m. fse_ncount T 15 256 (blk:byte list) (cs,alog,m)`
  THENL [ALL_TAC; FDE_NONC_TAC] THEN
  FDE_NC_TAC THEN ASM_CASES_TAC `alog <= 6` THENL
   [ALL_TAC;
    ZSTD_STEPS_TAC (31--33) THEN FDE_NOBLOCK_TAC THEN FDE_ERROR_TAC] THEN
  SUBGOAL_THEN `alog = 5 \/ alog = 6` MP_TAC THENL
   [UNDISCH_TAC `5 <= alog` THEN UNDISCH_TAC `alog <= 6` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  ZSTD_STEPS_TAC (31--46) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_SIZE_LEMMA
    (ASSUME `1 <= LENGTH(cs:int list)`)]) THEN
  (FDE_SIZE_SPLIT_TAC THENL [ALL_TAC; FDE_NOBLOCK_TAC THEN FDE_ERROR_TAC]) THEN
  ZSTD_STEPS_TAC (47--53) THEN FDE_BUILD_TAC THEN FDE_DECODE_TAC);;

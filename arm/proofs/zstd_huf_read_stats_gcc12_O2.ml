(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reading the description of a Huffman tree: zstd's HUF_readStats_wksp,     *)
(* compiled by gcc 12 at -O2 for AArch64.                                    *)
(* ========================================================================= *)

needs "arm/proofs/zstd_fse_decompress_gcc12_O2.ml";;

(* ------------------------------------------------------------------------- *)
(* HUF_readStats_wksp at 0xca0 branches to HUF_readStats_body_default at     *)
(* 0x770, which reads the description of a Huffman tree at the start of the  *)
(* input src, as HUF_readDTableX1_wksp calls it, with room for 256 weights   *)
(* at huffWeight and a workspace of 876 bytes (an argument on the stack).    *)
(* With a header byte of 128 or more, the weights are 4-bit numbers in the   *)
(* bytes after it, which the loop at 0x7d0 stores two at a time; otherwise   *)
(* they are FSE-compressed in the next bytes, which FSE_decompress_wksp_bmi2 *)
(* decodes, called at 0x898. The loop at 0x844 then counts the weights of    *)
(* each value in rankStats, 13 words, and sums 2^(Weight - 1), stopping at a *)
(* weight of more than 12, and the code at 0x8cc checks the sum, computes    *)
(* tableLog and the last weight, and checks the weights 1. The pieces are    *)
(* the tail at 0x8cc (rs_tail), the loop over the weights at 0x844 (rs_linv) *)
(* and the loop for the 4-bit weights at 0x7d0 (rs_uinv), with the result as *)
(* in rs_post for the weights w of the description, and the main theorem.    *)
(* Each has the conjunct puff_memsafe e rr wr s, for the trace e at the      *)
(* entry of the function.                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Words in the code, and rankStats zeroed ***)

let RS_WORD_SUB32 = prove
 (`!m n. n <= m ==> word_sub (word m) (word n):int32 = word(m - n)`,
  SIMP_TAC[WORD_SUB]);;

let RS_WORD_ZX32 = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 4294967296 ==> n < 18446744073709551616`]);;

let RS_POW2_JUSHR = prove
 (`!k. 1 <= k /\ k <= 32
       ==> word_jushr (word 2147483648:int32) (word (32 - k)) =
           word(2 EXP (k - 1))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_jushr; word_ushr; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(32 - k) MOD 4294967296 MOD 32 = 32 - k` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT; ARITH_RULE `1 <= k ==> 32 - k < 32`;
                 ARITH_RULE `32 - k < 4294967296`];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `2147483648 = 2 EXP (32 - k) * 2 EXP (k - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `(32 - k) + (k - 1) = 31` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]]);;

let RS_BIT0_WORD32 = prove
 (`!n. bit 0 (word n:int32) <=> ODD n`,
  REWRITE_TAC[BIT_WORD; DIMINDEX_32; EXP; DIV_1] THEN ARITH_TAC);;

let RS_LOW_NIBBLE = prove
 (`!b:byte. word_zx(word_and (word(val b):int32) (word 15)):byte =
            word(val b MOD 16)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_8] THEN
  SUBGOAL_THEN `word 15:int32 = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[VAL_WORD_AND_MASK_WORD]] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 4294967296`;
               ARITH_RULE `n MOD 16 < 256`; MOD_MOD_REFL] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `n MOD 16 < 16`;
           ARITH_RULE `n MOD 16 < 256`]);;

let READ_MEMORY_BYTES52_ZERO = prove
 (`!a s:armstate.
        read (memory :> bytes128 a) s = word 0 /\
        read (memory :> bytes128(word_add a (word 16))) s = word 0 /\
        read (memory :> bytes128(word_add a (word 32))) s = word 0 /\
        read (memory :> bytes32(word_add a (word 48))) s = word 0
        ==> read (memory :> bytes(a,52)) s = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `52 = 16 + 16 + 16 + 4`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              VAL_READ_MEMORY_BYTES128; VAL_READ_MEMORY_BYTES32] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC);;

(*** Rewriting the values read at the current state with conditional  ***)
(*** rules ths, whose conditions follow from the assumptions, and then ***)
(*** with the equations eqs; deciding the branch with an assumption tm ***)

let RS_REG_CONV_TAC ths eqs =
  W(fun (asl,w) ->
    let s = rand w in
    let prove_cond c =
      TAC_PROOF((asl,c), CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC) in
    let rule_conv th =
      let pm = PART_MATCH (lhs o rand) th in
      fun tm -> let ith = pm tm in MP ith (prove_cond(lhand(concl ith))) in
    let conv = TOP_DEPTH_CONV(FIRST_CONV(map rule_conv ths)) THENC
               REWRITE_CONV eqs in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s')),_)
          when s' = s -> CONV_RULE(RAND_CONV conv) th
      | _ -> th));;

let RS_DECIDE_TAC tm =
  W(fun (asl,w) ->
    let s = rand w in
    let th = ASSUME tm in
    RULE_ASSUM_TAC(fun a -> match concl a with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),_)
        when s' = s && c = `PC` -> REWRITE_RULE[th] a
      | _ -> a));;

(*** The weights as 4-bit numbers, for a header byte of 128 or more ***)

let rs_nibbles = new_definition
 `rs_nibbles (l:byte list) n =
    list_of_seq (\i. if EVEN i then val(EL (1 + i DIV 2) l) DIV 16
                     else val(EL (1 + i DIV 2) l) MOD 16) n`;;

let LENGTH_RS_NIBBLES = prove
 (`!l n. LENGTH(rs_nibbles l n) = n`,
  REWRITE_TAC[rs_nibbles; LENGTH_LIST_OF_SEQ]);;

let RS_NIBBLES_SUC = prove
 (`!l n. rs_nibbles l (n + 1) =
         APPEND (rs_nibbles l n)
          [if EVEN n then val(EL (1 + n DIV 2) (l:byte list)) DIV 16
           else val(EL (1 + n DIV 2) l) MOD 16]`,
  REWRITE_TAC[rs_nibbles; GSYM ADD1; list_of_seq]);;

let RS_NIBBLES_BOUND = prove
 (`!l n. ALL (\x. x < 256) (rs_nibbles l n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_EL; LENGTH_RS_NIBBLES] THEN
  SIMP_TAC[rs_nibbles; EL_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  MP_TAC(ISPEC `EL (1 + i DIV 2) (l:byte list)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let RS_NIBBLES_PREFIX = prove
 (`!l m n. m <= n ==> SUB_LIST(0,m) (rs_nibbles l n) = rs_nibbles l m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH_RS_NIBBLES] THEN
  ASM_SIMP_TAC[SUB_0; ARITH_RULE `m <= n ==> MIN m n = m`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_RS_NIBBLES; ADD_CLAUSES;
               ARITH_RULE `i < m /\ m <= n ==> i < n`] THEN
  ASM_SIMP_TAC[rs_nibbles; EL_LIST_OF_SEQ;
               ARITH_RULE `i < m /\ m <= n ==> i < n`]);;

let RS_NIBBLES_PAIR = prove
 (`!l k. rs_nibbles l (2 * k + 2) =
         APPEND (rs_nibbles l (2 * k))
          [val(EL (k + 1) (l:byte list)) DIV 16; val(EL (k + 1) l) MOD 16]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * k + 2 = (2 * k + 1) + 1`; RS_NIBBLES_SUC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; EVEN_ADD; EVEN_MULT; ARITH] THEN
  SUBGOAL_THEN `(2 * k) DIV 2 = k /\ (2 * k + 1) DIV 2 = k`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL
     [EXISTS_TAC `0`; EXISTS_TAC `1`] THEN ARITH_TAC;
    REWRITE_TAC[ADD_SYM]]);;

let RS_NIBBLES_TRUNC = prove
 (`!l m n. m <= n
           ==> SUB_LIST(0,m) (MAP (word:num->byte) (rs_nibbles l n)) =
               MAP word (rs_nibbles l m)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH_MAP; LENGTH_RS_NIBBLES] THEN
  ASM_SIMP_TAC[SUB_0; ARITH_RULE `m <= n ==> MIN m n = m`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_SUB_LIST; EL_MAP; LENGTH_MAP; LENGTH_RS_NIBBLES;
               ADD_CLAUSES; ARITH_RULE `i < m /\ m <= n ==> i < n`] THEN
  ASM_SIMP_TAC[rs_nibbles; EL_LIST_OF_SEQ;
               ARITH_RULE `i < m /\ m <= n ==> i < n`]);;

(* ------------------------------------------------------------------------- *)
(* The pieces after the frame of 64 bytes is pushed, for the weights w of    *)
(* the description of h bytes: the regions, the hypotheses, the frame, the   *)
(* result as in rs_post, and the facts that hold all through.                *)
(* ------------------------------------------------------------------------- *)

let rs_rr =
 `[src,LENGTH(l:byte list); hw,256; rs,52; wk,876;
   word_sub stackpointer (word 320),320; stackpointer,8;
   word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
   word_add (word pc) (word 31600),128]:(int64#num)list`
and rs_wr =
 `[hw,256; rs,52; nbp,4; tlp,4; wk,876;
   word_sub stackpointer (word 320),320]:(int64#num)list`;;

let rs_hyps =
 `aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
  aligned 16 (stackpointer:int64) /\
  nonoverlapping (hw:int64,256) (rs:int64,52) /\
  nonoverlapping (hw,256) (nbp:int64,4) /\
  nonoverlapping (hw,256) (tlp:int64,4) /\
  nonoverlapping (rs,52) (nbp,4) /\ nonoverlapping (rs,52) (tlp,4) /\
  nonoverlapping (nbp,4) (tlp,4) /\
  nonoverlapping (hw,256) (word_sub stackpointer (word 320),320) /\
  nonoverlapping (rs,52) (word_sub stackpointer (word 320),320) /\
  nonoverlapping (nbp,4) (word_sub stackpointer (word 320),320) /\
  nonoverlapping (tlp,4) (word_sub stackpointer (word 320),320) /\
  nonoverlapping (hw,256) (word pc,0x20018) /\
  nonoverlapping (rs,52) (word pc,0x20018) /\
  nonoverlapping (nbp,4) (word pc,0x20018) /\
  nonoverlapping (tlp,4) (word pc,0x20018)`;;

let rs_frame =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
  MAYCHANGE [X19; X20; X21; X22; X23; X29; X30; SP] ,,
  MAYCHANGE [memory :> bytes(hw,256); memory :> bytes(rs,52);
             memory :> bytes(nbp,4); memory :> bytes(tlp,4);
             memory :> bytes(wk,876);
             memory :> bytes(word_sub stackpointer (word 320),320)]`;;

let rs_vars =
 [`pc:num`; `returnaddress:int64`; `stackpointer:int64`; `hw:int64`;
  `rs:int64`; `nbp:int64`; `tlp:int64`; `src:int64`; `l:byte list`;
  `wk:int64`; `ea:int64`; `el:num`; `w:num list`; `h:num`;
  `x19:int64`; `x20:int64`; `x21:int64`; `x22:int64`; `x23:int64`;
  `x29:int64`; `e:uarch_event list`];;

let mk_rs_goal extra hyps pre post =
  let tm = mk_imp(hyps,
                  list_mk_icomb "ensures" [`arm`; pre; post; rs_frame]) in
  let vs = rs_vars @ extra in
  let fvs = frees tm in
  (match subtract fvs vs with
     [] -> ()
   | v::_ -> failwith ("mk_rs_goal: free variable " ^ string_of_term v));
  list_mk_forall(filter (fun v -> mem v fvs) vs,tm);;

let rs_post = with_memsafe rs_rr rs_wr `\s.
  read PC s = returnaddress /\ read SP s = stackpointer /\
  read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
  read X22 s = x22 /\ read X23 s = x23 /\ read X29 s = x29 /\
  read X30 s = returnaddress /\
  (!ws ml. huf_readstats w ws ml
           ==> read X0 s = word h /\
               read (memory :> bytes(hw,LENGTH ws)) s =
               num_of_bytelist(MAP (word:num->byte) ws) /\
               read (memory :> bytes(rs,52)) s =
               num_of_wordlist
                (list_of_seq (\j. word(huf_rank ws j):int32) 13) /\
               read (memory :> bytes32 nbp) s = word(LENGTH ws) /\
               read (memory :> bytes32 tlp) s = word ml) /\
  ((!ws ml. ~huf_readstats w ws ml) ==> zstd_is_error(read X0 s))`;;

let rs_common =
 `aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
  read SP s = word_sub stackpointer (word 64) /\
  read (memory :> bytes64 (word_sub stackpointer (word 64))) s = x29 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 64)) (word 8))) s =
  returnaddress /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 64)) (word 16))) s = x19 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 64)) (word 24))) s = x20 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 64)) (word 32))) s = x21 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 64)) (word 40))) s = x22 /\
  read (memory :> bytes64
         (word_add (word_sub stackpointer (word 64)) (word 48))) s = x23 /\
  read X19 s = hw /\ read X20 s = rs /\ read X21 s = tlp /\
  read X22 s = nbp`;;

let RS_SP_RESTORE = prove
 (`!x:int64. word_add (word_sub x (word 64)) (word 64) = x`,
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The tail at 0x8cc, after the statistics of the weights w: the sum t of    *)
(* 2^(Weight - 1), tableLog b, the rest r = 2^b - t, which must be a power   *)
(* of 2, the last weight lw, the number k1 of the weights 1, which must be   *)
(* at least 2 and even, and the stores of tableLog, the last weight and the  *)
(* number of weights.                                                        *)
(* ------------------------------------------------------------------------- *)

let rs_tail = with_memsafe rs_rr rs_wr
 (mk_abs(`s:armstate`,list_mk_conj
   [`read PC s = word(pc + 0x8cc) /\
     read X0 s = word(huf_total w) /\ read X3 s = word 1 /\
     read X8 s = word(LENGTH(w:num list)) /\ read X23 s = word h /\
     read (memory :> bytes(hw,LENGTH w)) s =
     num_of_bytelist(MAP (word:num->byte) w) /\
     read (memory :> bytes(rs,52)) s =
     num_of_wordlist(list_of_seq (\j. word(huf_rank w j):int32) 13) /\
     1 <= LENGTH w /\ LENGTH w <= 255 /\ ALL (\x. x <= 12) w`;
    rs_common]));;

let RS_ERROR_TAC reason =
  PUFF_FINAL_TAC THEN
  SUBGOAL_THEN `!ws ml. ~huf_readstats w ws ml` ASSUME_TAC THENL
   [reason; ALL_TAC] THEN
  ASM_REWRITE_TAC[RS_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;;

let RS_NONE_TAC =
  REWRITE_TAC[HUF_READSTATS_NONE] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;;

let RS_TAIL_SETUP_TAC =
  ABBREV_TAC `b = bitsize t` THEN
  SUBGOAL_THEN `32 - (32 - b) = b` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `t:num` BITSIZE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP b <= 4096` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `2 EXP 12` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `r = 2 EXP b - t` THEN
  SUBGOAL_THEN `1 <= r /\ r < 4096` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= bitsize r /\ bitsize r <= 12` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[BITSIZE_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                    BITSIZE_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `r:num` BITSIZE_REV) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `lw = bitsize r` THEN
  SUBGOAL_THEN `32 - (32 - lw) = lw` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC];;

let RS_TAIL_LAST_TAC =
  MP_TAC(ISPECL [`hw:int64`; `MAP (word:num->byte) w`; `word lw:byte`;
                 `s16:armstate`] READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  SUBGOAL_THEN `APPEND (MAP (word:num->byte) w) [word lw] =
                MAP word (APPEND w [lw])` SUBST1_TAC THENL
   [REWRITE_TAC[MAP_APPEND; MAP]; DISCH_TAC] THEN
  SUBGOAL_THEN `lw < 13` ASSUME_TAC THENL
   [UNDISCH_TAC `lw <= 12` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rs:int64`; `list_of_seq (\j. word(huf_rank w j):int32) 13`;
                 `lw:num`; `s16:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP (ISPECL
    [`\j. word(huf_rank w j):int32`; `lw:num`; `13`] EL_LIST_OF_SEQ)
    (ASSUME `lw < 13`)]) THEN
  SUBGOAL_THEN `val(word lw:int64) = lw` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `lw < 13` THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (17--19) THEN
  MP_TAC(ISPECL [`rs:int64`; `list_of_seq (\j. word(huf_rank w j):int32) 13`;
    `list_of_seq (\j. word(huf_rank (APPEND w [lw]) j):int32) 13`;
    `lw:num`; `s19:armstate`] READ_MEMORY_WORDLIST32_UPDATE) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ; HUF_RANK_APPEND1] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `(lw:num = i) <=> (i = lw)`; ADD_CLAUSES];
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`rs:int64`;
    `list_of_seq (\j. word(huf_rank (APPEND w [lw]) j):int32) 13`;
    `13`; `1`; `s19:armstate`] READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `huf_rank (APPEND (w:num list) [lw]) 1 <= 256` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`APPEND (w:num list) [lw]`; `1`] HUF_RANK_LE) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    UNDISCH_TAC `LENGTH(w:num list) <= 255` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `k1 = huf_rank (APPEND w [lw]) 1` THEN
  ZSTD_STEPS_TAC [20] THEN
  RS_REG_CONV_TAC [RS_WORD_ZX32]
   [ASSUME `huf_rank (APPEND w [lw]) 1 = k1`];;

let RS_TAIL = prove
 (mk_rs_goal [] rs_hyps rs_tail rs_post,
  ZSTD_INTRO_TAC THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(SPEC `w:num list` HUF_TOTAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `huf_total w < 2 EXP 32` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `huf_total w = 0` THENL
   [ZSTD_STEPS_TAC (1--8) THEN
    RS_ERROR_TAC(ASM_REWRITE_TAC[huf_readstats]);
    ALL_TAC] THEN
  ABBREV_TAC `t = huf_total w` THEN
  SUBGOAL_THEN `bitsize t <= 32` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[BITSIZE_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `32 - (32 - bitsize t) = bitsize t` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `bitsize t <= 12` THENL
   [ALL_TAC;
    ZSTD_STEPS_TAC (1--13) THEN RS_ERROR_TAC RS_NONE_TAC] THEN
  SUBGOAL_THEN `~(t = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RS_TAIL_SETUP_TAC THEN
  ZSTD_STEPS_TAC (1--9) THEN
  RS_REG_CONV_TAC [RS_WORD_SUB32; RS_WORD_ZX32; WORD_CLZ_WORD32]
   [ASSUME `2 EXP b - t = r`; ASSUME `32 - (32 - b) = b`;
    ASSUME `bitsize r = lw`] THEN
  ZSTD_STEPS_TAC (10--12) THEN
  RS_REG_CONV_TAC [RS_POW2_JUSHR; RS_WORD_ZX32] [] THEN
  ASM_CASES_TAC `2 EXP (lw - 1) = r` THENL
   [ALL_TAC;
    ZSTD_STEPS_TAC (13--21) THEN RS_ERROR_TAC RS_NONE_TAC] THEN
  ZSTD_STEPS_TAC (13--16) THEN
  RS_REG_CONV_TAC [RS_WORD_SUB32; RS_WORD_ZX32]
   [ASSUME `32 - (32 - lw) = lw`] THEN
  RS_TAIL_LAST_TAC THEN
  ASM_CASES_TAC `k1 <= 1` THENL
   [ZSTD_STEPS_TAC (21--29) THEN
    RS_ERROR_TAC(REWRITE_TAC[HUF_READSTATS_NONE] THEN ASM_REWRITE_TAC[] THEN
                 UNDISCH_TAC `k1 <= 1` THEN ARITH_TAC);
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN k1` THENL
   [ALL_TAC;
    SUBGOAL_THEN `bit 0 (word k1:int32)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[RS_BIT0_WORD32; GSYM NOT_EVEN]; ALL_TAC] THEN
    ZSTD_STEPS_TAC (21--23) THEN RS_DECIDE_TAC `bit 0 (word k1:int32)` THEN
    ZSTD_STEPS_TAC (24--30) THEN RS_ERROR_TAC RS_NONE_TAC] THEN
  SUBGOAL_THEN `~bit 0 (word k1:int32)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RS_BIT0_WORD32; GSYM NOT_EVEN]; ALL_TAC] THEN
  ZSTD_STEPS_TAC (21--23) THEN RS_DECIDE_TAC `~bit 0 (word k1:int32)` THEN
  ZSTD_STEPS_TAC (24--33) THEN PUFF_FINAL_TAC THEN
  SUBGOAL_THEN `2 <= k1` ASSUME_TAC THENL
   [UNDISCH_TAC `~(k1 <= 1)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[RS_SP_RESTORE; HUF_READSTATS_SOME; HUF_READSTATS_NONE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `SUC 0 = 1`]);;

(* ------------------------------------------------------------------------- *)
(* The loop at 0x844 over the weights w, with the statistics of the first n  *)
(* of them, for the measure LENGTH w - n. A weight of more than 12 is an     *)
(* error.                                                                    *)
(* ------------------------------------------------------------------------- *)

let rs_linv = with_memsafe rs_rr rs_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`n:num`,list_mk_conj
    [`m = LENGTH(w:num list) - n /\ n < LENGTH w /\
      read PC s = word(pc + 0x844) /\
      read X1 s = word n /\ read X2 s = word n /\
      read X0 s = word(huf_total(SUB_LIST(0,n) w)) /\
      read X3 s = word 1 /\ read X8 s = word(LENGTH w) /\
      read X23 s = word h /\
      read (memory :> bytes(hw,LENGTH w)) s =
      num_of_bytelist(MAP (word:num->byte) w) /\
      read (memory :> bytes(rs,52)) s =
      num_of_wordlist
       (list_of_seq (\j. word(huf_rank (SUB_LIST(0,n) w) j):int32) 13) /\
      ALL (\x. x <= 12) (SUB_LIST(0,n) w) /\
      LENGTH w <= 255 /\ ALL (\x. x < 256) w`;
     rs_common])));;

let RS_LAST_SPLIT = prove
 (`!(w:num list) n.
        n + 1 = LENGTH w ==> w = APPEND (SUB_LIST(0,n) w) [EL n w]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:num list`; `n:num`] SUB_LIST_SNOC) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_REWRITE_TAC[SUB_LIST_LENGTH]);;

let RS_LAST_REWRITE_TAC =
  W(fun (asl,w) ->
    let th = MATCH_MP RS_LAST_SPLIT
      (ASSUME `n + 1 = LENGTH (w:num list)`) in
    let tot = REWRITE_RULE[HUF_TOTAL_APPEND1] (AP_TERM `huf_total` th) in
    let rnk = GEN `j:num` (REWRITE_RULE[HUF_RANK_APPEND1]
      (AP_THM (AP_TERM `huf_rank` th) `j:num`)) in
    let all = REWRITE_RULE[ALL_APPEND; ALL]
      (AP_TERM `ALL (\x:num. x <= 12)` th) in
    REWRITE_TAC[tot; rnk; all]);;

let RS_NEXT_REWRITE_TAC =
  W(fun (asl,w) ->
    let th = MATCH_MP SUB_LIST_SNOC (ASSUME `n < LENGTH (w:num list)`) in
    REWRITE_TAC[th; HUF_TOTAL_APPEND1; HUF_RANK_APPEND1; ALL_APPEND; ALL]);;

let RS_LOOP = prove
 (mk_rs_goal [] rs_hyps
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      list_mk_comb(rs_linv,[`m:num`; `s:armstate`]))))
   rs_post,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `n:num` THEN PUFF_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`hw:int64`; `MAP (word:num->byte) w`; `n:num`;
                 `s0:armstate`] READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN ASM_SIMP_TAC[EL_MAP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `EL n (w:num list) < 256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `ALL (\x. x < 256) (w:num list)`)) THEN
    REWRITE_TAC[GSYM ALL_EL] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `EL n (w:num list) <= 12` THENL
   [ALL_TAC;
    ZSTD_STEPS_TAC (1--11) THEN
    RS_ERROR_TAC
     (REWRITE_TAC[HUF_READSTATS_NONE] THEN
      SUBGOAL_THEN `~ALL (\x. x <= 12) (w:num list)`
       (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM ALL_EL; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[])] THEN
  ZSTD_STEPS_TAC (1--4) THEN
  SUBGOAL_THEN `EL n (w:num list) < 13` ASSUME_TAC THENL
   [UNDISCH_TAC `EL n (w:num list) <= 12` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (EL n (w:num list)) <= 4096` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `2 EXP 12` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `huf_total(SUB_LIST(0,n) w) <= 2048 * 255` ASSUME_TAC THENL
   [MP_TAC(SPEC `SUB_LIST(0,n) (w:num list)` HUF_TOTAL_BOUND) THEN
    ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN
    UNDISCH_TAC `n < LENGTH(w:num list)` THEN
    UNDISCH_TAC `LENGTH(w:num list) <= 255` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rs:int64`;
    `list_of_seq (\j. word(huf_rank (SUB_LIST(0,n) w) j):int32) 13`;
    `EL n (w:num list)`; `s4:armstate`] READ_MEMORY_WORDLIST32_SPLIT) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP (ISPECL
    [`\j. word(huf_rank (SUB_LIST(0,n) w) j):int32`; `EL n (w:num list)`;
     `13`] EL_LIST_OF_SEQ) (ASSUME `EL n (w:num list) < 13`)]) THEN
  SUBGOAL_THEN `val(word(EL n (w:num list)):int64) = EL n w` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `EL n (w:num list) < 13` THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (5--11) THEN
  MP_TAC(ISPECL [`rs:int64`;
    `list_of_seq (\j. word(huf_rank (SUB_LIST(0,n) w) j):int32) 13`;
    `list_of_seq (\j. word(huf_rank (SUB_LIST(0,n) w) j +
                          (if EL n w = j then 1 else 0)):int32) 13`;
    `EL n (w:num list)`; `s11:armstate`] READ_MEMORY_WORDLIST32_UPDATE) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `(EL n (w:num list) = i) <=> (i = EL n w)`;
                    ADD_CLAUSES];
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC] THEN
  ASM_CASES_TAC `n + 1 < LENGTH(w:num list)` THENL
   [ZSTD_STEPS_TAC (12--13) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `LENGTH(w:num list) - (n + 1)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `m = LENGTH(w:num list) - n` THEN
      UNDISCH_TAC `n + 1 < LENGTH(w:num list)` THEN ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `n + 1` THEN RS_NEXT_REWRITE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n + 1 = LENGTH(w:num list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(n + 1 < LENGTH(w:num list))` THEN
    UNDISCH_TAC `n < LENGTH(w:num list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (12--13) THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC)
   RS_TAIL [] THEN
  MEMSAFE_ELIM_TAC THEN RS_LAST_REWRITE_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `n + 1 = LENGTH(w:num list)` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop at 0x7d0 storing the os weights as 4-bit numbers, two at a time, *)
(* the first 2k of them stored so far, for the measure os - 2k; then         *)
(* rankStats zeroed and the loop at 0x844.                                   *)
(* ------------------------------------------------------------------------- *)

let rs_uhyps = mk_conj(rs_hyps,
 `nonoverlapping (hw:int64,256) (src:int64,LENGTH(l:byte list))`);;

let rs_uinv = with_memsafe rs_rr rs_wr
 (list_mk_abs([`m:num`; `s:armstate`],
   mk_exists(`k:num`,list_mk_conj
    [`m = os - 2 * k /\ 2 * k < os /\ os <= 128 /\
      h = (os + 1) DIV 2 + 1 /\ h <= LENGTH(l:byte list) /\
      read PC s = word(pc + 0x7d0) /\
      read X1 s = word(2 * k) /\ read X2 s = src /\
      read X3 s = word_add hw (word 1) /\
      read X8 s = word os /\ read X23 s = word h /\
      read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
      read (memory :> bytes(hw,2 * k)) s =
      num_of_bytelist(MAP (word:num->byte) (rs_nibbles l (2 * k)))`;
     rs_common])));;

let rs_upost = subst [`rs_nibbles l os`,`w:num list`] rs_post;;

let RS_HW_PAIR_TAC s =
  RULE_ASSUM_TAC(REWRITE_RULE[RS_LOW_NIBBLE;
    ARITH_RULE `1 + 2 * k = 2 * k + 1`]) THEN
  MP_TAC(ISPECL [`hw:int64`; `MAP (word:num->byte) (rs_nibbles l (2 * k))`;
    `word(val(EL (k + 1) (l:byte list)) DIV 16):byte`; s]
    READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_RS_NIBBLES] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hw:int64`;
    `APPEND (MAP (word:num->byte) (rs_nibbles l (2 * k)))
            [word(val(EL (k + 1) (l:byte list)) DIV 16)]`;
    `word(val(EL (k + 1) (l:byte list)) MOD 16):byte`; s]
    READ_MEMORY_BYTELIST_SNOC) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_RS_NIBBLES; LENGTH;
                  ARITH_RULE `SUC 0 = 1`] THEN
  SUBGOAL_THEN
   `APPEND (APPEND (MAP (word:num->byte) (rs_nibbles l (2 * k)))
                   [word(val(EL (k + 1) (l:byte list)) DIV 16)])
           [word(val(EL (k + 1) l) MOD 16)] =
    MAP word (rs_nibbles l (2 * k + 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RS_NIBBLES_PAIR; MAP_APPEND; MAP; GSYM APPEND_ASSOC; APPEND];
    REWRITE_TAC[ARITH_RULE `(2 * k + 1) + 1 = 2 * k + 2`] THEN DISCH_TAC];;

let RS_UNPACK = prove
 (mk_rs_goal [`os:num`] rs_uhyps
   (mk_abs(`s:armstate`,mk_exists(`m:num`,
      list_mk_comb(rs_uinv,[`m:num`; `s:armstate`]))))
   rs_upost,
  ZSTD_INTRO_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE_EXISTS THEN
  REPEAT CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC; SUBSUMED_ID_MAYCHANGE_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN BETA_TAC THEN
  ENSURES_EXISTS_PRE_TAC `k:num` THEN PUFF_INIT_TAC "s0" THEN
  SUBGOAL_THEN `k + 1 < LENGTH(l:byte list)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`2 * k < os`; `h = (os + 1) DIV 2 + 1`; `h <= LENGTH(l:byte list)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`src:int64`; `l:byte list`; `k + 1`; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(2 * k) DIV 2 = k` ASSUME_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_zx(word_zx(word(k + 1):int64):int32):int64 = word(k + 1)`
  ASSUME_TAC THENL
   [W(fun (asl,w) -> CONV_TAC(LAND_CONV(ZSTD_SMALL_WORD_CONV asl))) THEN
    REFL_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (1--8) THEN RS_HW_PAIR_TAC `s8:armstate` THEN
  ASM_CASES_TAC `2 * k + 2 < os` THENL
   [ZSTD_STEPS_TAC (9--11) THEN PUFF_FINAL_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `os - 2 * (k + 1)` THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m = os - 2 * k`; `2 * k + 2 < os`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `k + 1` THEN
    REWRITE_TAC[ARITH_RULE `2 * (k + 1) = 2 * k + 2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `os <= 2 * k + 2` ASSUME_TAC THENL
   [UNDISCH_TAC `~(2 * k + 2 < os)` THEN ARITH_TAC; ALL_TAC] THEN
  ZSTD_STEPS_TAC (9--20) THEN
  MP_TAC(ISPECL [`rs:int64`; `s20:armstate`] READ_MEMORY_BYTES52_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hw:int64`; `MAP (word:num->byte) (rs_nibbles l (2 * k + 2))`;
                 `2 * k + 2`; `os:num`; `s20:armstate`]
    READ_MEMORY_BYTES_TRUNC) THEN
  ASM_SIMP_TAC[LENGTH_MAP; LENGTH_RS_NIBBLES; RS_NIBBLES_TRUNC] THEN
  DISCH_TAC THEN
  ZSTD_CONTINUE_WITH_TAC
   (GEN_TAC THEN DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC)
   RS_LOOP [`rs_nibbles l os`,`w:num list`; `(os + 1) DIV 2 + 1`,`h:num`] THEN
  EXISTS_TAC `os - 0` THEN EXISTS_TAC `0` THEN
  MEMSAFE_ELIM_TAC THEN
  ASM_REWRITE_TAC[LENGTH_RS_NIBBLES; SUB_LIST_CLAUSES; HUF_TOTAL_NIL;
                  HUF_RANK_NIL; ALL; NUM_OF_WORDLIST_LIST_OF_SEQ_0;
                  RS_NIBBLES_BOUND] THEN
  MAP_EVERY UNDISCH_TAC [`2 * k < os`; `os <= 128`] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The entry: the description at the start of the input l, raw or            *)
(* FSE-compressed, and the result for it as that for its weights.            *)
(* ------------------------------------------------------------------------- *)

let RS_HEADER_RAW = prove
 (`!(l:byte list).
        ~(l = []) /\ 128 <= val(EL 0 l) /\
        (val(EL 0 l) - 126) DIV 2 + 1 <= LENGTH l
        ==> huf_header T l (rs_nibbles l (val(EL 0 l) - 127))
                       ((val(EL 0 l) - 126) DIV 2 + 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_header; rs_nibbles] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let RS_HEADER_FSE = prove
 (`!(l:byte list) w.
        ~(l = []) /\ val(EL 0 l) < 128 /\ val(EL 0 l) + 1 <= LENGTH l /\
        fse_weight_block T (zstd_sublist l 1 (val(EL 0 l))) w
        ==> huf_header T l w (val(EL 0 l) + 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[huf_header] THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN ARITH_TAC);;

let RS_NOHEADER = prove
 (`!(l:byte list).
        l = [] \/
        128 <= val(EL 0 l) /\ LENGTH l < 1 + (val(EL 0 l) - 126) DIV 2 \/
        val(EL 0 l) < 128 /\ LENGTH l < 1 + val(EL 0 l) \/
        val(EL 0 l) < 128 /\
        (!w. ~fse_weight_block T (zstd_sublist l 1 (val(EL 0 l))) w)
        ==> !ws ml h. ~huf_weights T l ws ml h`,
  GEN_TAC THEN DISCH_THEN(fun th ->
    MATCH_MP_TAC HUF_WEIGHTS_NOHEADER THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[huf_header] THEN STRIP_TAC THEN
    MP_TAC th) THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    lhs(concl th) = `h:num`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
  FIRST [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

let RS_WTAC hdr =
  X_GEN_TAC `s':armstate` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MATCH_MP HUF_WEIGHTS_READSTATS hdr;
              TAUT `~(a /\ b) <=> a ==> ~b`; IMP_CONJ; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[];;

let RS_STACK_REBASE = WORD_RULE
 `word_sub stackpointer (word 64):int64 =
  word_add (word_sub stackpointer (word 320)) (word 256)`;;

let RS_FRAME_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[RS_STACK_REBASE; WORD_ADD_ASSOC_NUM]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) THEN
  MONOTONE_MAYCHANGE_TAC;;

let RS_TOP_FAIL_TAC reason =
  PUFF_FINAL_TAC THEN
  SUBGOAL_THEN `!ws ml h. ~huf_weights T (l:byte list) ws ml h` ASSUME_TAC
  THENL [reason; ALL_TAC] THEN
  ASM_REWRITE_TAC[RS_SP_RESTORE; zstd_is_error] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN TRY RS_FRAME_TAC;;

let RS_TOP_ERROR_TAC reason =
  RS_TOP_FAIL_TAC (MATCH_MP_TAC RS_NOHEADER THEN reason);;

let RS_GOON_TAC wtac th insts =
  let frame_rule =
    REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
                 MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
                 SOME_FLAGS] in
  W(fun (asl,w) ->
    let th1 = INST insts (SPEC_ALL th) in
    let hyp = lhand(concl th1) in
    let hth = TAC_PROOF((asl,hyp),
                REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
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
      CONJ_TAC THENL [RS_FRAME_TAC; BETA_TAC THEN wtac]]);;

let RS_START_TAC =
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

let RS_CALL_TAC =
  SUBGOAL_THEN `val(word_add src (word 1):int64) = val src + 1` ASSUME_TAC
  THENL
   [MATCH_MP_TAC VAL_WORD_ADD_NOWRAP THEN
    UNDISCH_TAC `val(src:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word_sub stackpointer (word 64):int64 = word 96)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (x:int64) (word 64) = word 96 <=>
                           x = word 160`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`src:int64`; `l:byte list`; `1`; `val(EL 0 (l:byte list))`;
                 `s25:armstate`] READ_MEMORY_BYTELIST_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~(LENGTH(l:byte list) < 1 + val(EL 0 (l:byte list)))` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `SUB_LIST(1,val(EL 0 (l:byte list))) l =
                zstd_sublist l 1 (val(EL 0 l))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ZSTD_SUBLIST_SUB_LIST THEN
    UNDISCH_TAC `~(LENGTH(l:byte list) < 1 + val(EL 0 (l:byte list)))` THEN
    ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `val(EL 0 (l:byte list)) < 2 EXP 24 /\
    8 <= val(word_add src (word 1):int64) /\
    val(word_add src (word 1):int64) + val(EL 0 l) + 8 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`val(EL 0 (l:byte list)) <= 127`; `8 <= val(src:int64)`;
      `val(src:int64) + LENGTH(l:byte list) + 8 < 2 EXP 64`;
      `~(LENGTH(l:byte list) < 1 + val(EL 0 (l:byte list)))`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ZSTD_STEPS_TAC [26] THEN
  EVENTS_ABBREV_TAC THEN
  W(fun gl -> MP_TAC(EVENTS_SPEC gl (ISPECL
   [`pc:num`; `word(pc + 2204):int64`; `word_sub stackpointer (word 64):int64`;
    `hw:int64`; `word_add src (word 1):int64`;
    `zstd_sublist l 1 (val(EL 0 (l:byte list)))`; `wk:int64`;
    `fcpy:int64`; `fset:int64`; `ea:int64`; `el:num`; `ev:num`]
   FSE_DECOMPRESS_WKSP_CORRECT))) THEN
  REWRITE_TAC[WORD_SUB_SUB_NUM; LENGTH_ZSTD_SUBLIST] THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC
                      NUM_LE_CONV)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [CALLEE_HYPS_TAC; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_GPRS; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC ZSTD_EXEC "s27" THEN EVENTS_UNABBREV_TAC;;

let RS_NOBLOCK_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term ((=) `zstd_is_error`)) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[zstd_is_error] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  X_CHOOSE_TAC `x0r:int64` (MESON[] `?x:int64. read X0 s27 = x`) THEN
  NC_ASSUME_REWRITE_TAC [`read X0 s27 = x0r`] THEN
  ZSTD_STEPS_TAC (28--29) THEN
  FIRST_ASSUM((fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FDE_ERRVAL_LEMMA th])) o
    check (fun th -> concl th = `18446744073709551496 < val(x0r:int64)`)) THEN
  ZSTD_STEPS_TAC (30--36) THEN
  RS_TOP_ERROR_TAC
   (DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `val(EL 0 (l:byte list)) <= 127` THEN ARITH_TAC;
      ASM_REWRITE_TAC[]]);;

let RS_BLOCK_TAC =
  FIRST_X_ASSUM(X_CHOOSE_TAC `w:num list` o check (is_exists o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:num list` o check (fun th ->
    is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`zstd_sublist l 1 (val(EL 0 (l:byte list)))`; `w:num list`]
    FSE_WEIGHT_BLOCK_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `w:num list`] RS_HEADER_FSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL];
      UNDISCH_TAC `val(EL 0 (l:byte list)) <= 127` THEN ARITH_TAC;
      UNDISCH_TAC `~(LENGTH(l:byte list) < 1 + val(EL 0 (l:byte list)))` THEN
      ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `val(word(LENGTH(w:num list)):int64) = LENGTH w` ASSUME_TAC
  THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `LENGTH(w:num list) <= 255` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(w:num list) = 0` THENL
   [ZSTD_STEPS_TAC (28--43) THEN
    RS_TOP_FAIL_TAC
     (REWRITE_TAC[MATCH_MP HUF_WEIGHTS_READSTATS
       (ASSUME `huf_header T l w (val(EL 0 (l:byte list)) + 1)`)] THEN
      REWRITE_TAC[huf_readstats; DE_MORGAN_THM] THEN
      REPEAT GEN_TAC THEN DISJ2_TAC THEN
      SUBGOAL_THEN `w:num list = []` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL]; ALL_TAC] THEN
      REWRITE_TAC[HUF_TOTAL_NIL]);
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (28--40) THEN
  MP_TAC(ISPECL [`rs:int64`; `s40:armstate`] READ_MEMORY_BYTES52_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RS_GOON_TAC
   (RS_WTAC (ASSUME `huf_header T l w (val(EL 0 (l:byte list)) + 1)`))
   RS_LOOP [`val(EL 0 (l:byte list)) + 1`,`h:num`] THEN
  EXISTS_TAC `LENGTH(w:num list) - 0` THEN EXISTS_TAC `0` THEN
  MEMSAFE_ELIM_TAC THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; HUF_TOTAL_NIL; HUF_RANK_NIL; ALL;
                  NUM_OF_WORDLIST_LIST_OF_SEQ_0] THEN
  UNDISCH_TAC `~(LENGTH(w:num list) = 0)` THEN ARITH_TAC;;

let RS_FSE_PATH_TAC =
  ASM_CASES_TAC `LENGTH(l:byte list) < 1 + val(EL 0 (l:byte list))` THENL
   [ZSTD_STEPS_TAC (16--25) THEN
    RS_TOP_ERROR_TAC
     (DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `val(EL 0 (l:byte list)) <= 127` THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_sub stackpointer (word 64)) (word 64):int64 =
                stackpointer` ASSUME_TAC THENL
   [REWRITE_TAC[RS_SP_RESTORE]; ALL_TAC] THEN
  ZSTD_STEPS_TAC (16--25) THEN RS_CALL_TAC THEN
  ASM_CASES_TAC
   `?w. fse_weight_block T (zstd_sublist l 1 (val(EL 0 (l:byte list)))) w`
  THENL [RS_BLOCK_TAC; RS_NOBLOCK_TAC];;

let RS_RAW_PATH_TAC =
  ABBREV_TAC `b0 = val(EL 0 (l:byte list))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `128 <= b0` ASSUME_TAC THENL
   [UNDISCH_TAC `~(b0 <= 127)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) < (b0 - 126) DIV 2 + 1` THENL
   [ZSTD_STEPS_TAC (16--29) THEN
    RS_TOP_ERROR_TAC
     (DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `LENGTH(l:byte list) < (b0 - 126) DIV 2 + 1` THEN
      ARITH_TAC);
    ALL_TAC] THEN
  ZSTD_STEPS_TAC (16--25) THEN
  MP_TAC(SPEC `l:byte list` RS_HEADER_RAW) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [UNDISCH_TAC `~(LENGTH(l:byte list) < (b0 - 126) DIV 2 + 1)` THEN
           ARITH_TAC;
           ASM_MESON_TAC[LENGTH_EQ_NIL]];
    DISCH_TAC] THEN
  RS_GOON_TAC
   (RS_WTAC (ASSUME `huf_header T l (rs_nibbles l (b0 - 127))
                                 ((b0 - 126) DIV 2 + 1)`))
   RS_UNPACK [`b0 - 127`,`os:num`; `(b0 - 126) DIV 2 + 1`,`h:num`] THEN
  EXISTS_TAC `b0 - 127 - 2 * 0` THEN EXISTS_TAC `0` THEN
  MEMSAFE_ELIM_TAC THEN
  SUBGOAL_THEN `(b0 - 127) + 1 = b0 - 126` SUBST1_TAC THENL
   [UNDISCH_TAC `128 <= b0` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_0; rs_nibbles; list_of_seq;
                  MAP; num_of_bytelist] THEN
  MAP_EVERY UNDISCH_TAC [`128 <= b0`; `b0 < 256`] THEN ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The main theorem. For the input l of LENGTH l bytes at src, if l starts   *)
(* with a Huffman tree description (huf_weights T, in the zstd dialect) of h *)
(* bytes for the weights ws and Max_Number_of_Bits ml, the result is h, with *)
(* ws at huffWeight hw, the number of the weights of each value up to 12 at  *)
(* rankStats rs, LENGTH ws at nbSymbolsPtr nbp and ml at tableLogPtr tlp;    *)
(* otherwise it is an error code. The accesses, including those of           *)
(* FSE_decompress_wksp_bmi2, are loads from the input, the outputs, the      *)
(* workspace wk, the stack (the 320 bytes below the stack pointer, and the 8 *)
(* bytes of wkspSize above it), the pointers to memcpy and memset and their  *)
(* region (ea,el) and BIT_mask, and stores to the outputs, the workspace and *)
(* the stack. FSE_decompress_wksp_bmi2 needs its stack pointer, 64 below     *)
(* this one, not to be 96.                                                   *)
(* ------------------------------------------------------------------------- *)

let HUF_READSTATS_WKSP_CORRECT = prove
 (`!pc returnaddress stackpointer hw rs nbp tlp src (l:byte list) wk
    fcpy fset ea el ev e.
     aligned 4096 (word pc:int64) /\ pc + 0x20018 <= 2 EXP 64 /\
     aligned 16 (stackpointer:int64) /\ ~(stackpointer = word 160) /\
     memcpy_memsafe_contract fcpy ea el ev /\
     memset_memsafe_contract fset ea el ev /\
     LENGTH l < 2 EXP 24 /\ 8 <= val(src:int64) /\
     val src + LENGTH l + 8 < 2 EXP 64 /\ val(hw:int64) + 255 < 2 EXP 64 /\
     nonoverlapping (hw,256) (rs:int64,52) /\
     nonoverlapping (hw,256) (nbp:int64,4) /\
     nonoverlapping (hw,256) (tlp:int64,4) /\
     nonoverlapping (rs,52) (nbp,4) /\ nonoverlapping (rs,52) (tlp,4) /\
     nonoverlapping (nbp,4) (tlp,4) /\
     nonoverlapping (hw,256) (src,LENGTH l) /\
     nonoverlapping (hw,256) (wk:int64,876) /\
     nonoverlapping (hw,256) (word pc,0x20018) /\
     nonoverlapping (rs,52) (word pc,0x20018) /\
     nonoverlapping (nbp,4) (word pc,0x20018) /\
     nonoverlapping (tlp,4) (word pc,0x20018) /\
     nonoverlapping (hw,256) (word_sub stackpointer (word 320),320) /\
     nonoverlapping (rs,52) (word_sub stackpointer (word 320),320) /\
     nonoverlapping (nbp,4) (word_sub stackpointer (word 320),320) /\
     nonoverlapping (tlp,4) (word_sub stackpointer (word 320),320) /\
     nonoverlapping (wk,876) (src,LENGTH l) /\
     nonoverlapping (wk,876) (word pc,0x20018) /\
     nonoverlapping (wk,876) (word_sub stackpointer (word 320),320) /\
     nonoverlapping (wk,876) (ea:int64,el) /\
     nonoverlapping (word_sub stackpointer (word 320),320)
                    (word pc,0x20018) /\
     nonoverlapping (word_sub stackpointer (word 320),320) (src,LENGTH l) /\
     nonoverlapping (word_sub stackpointer (word 320),320) (ea,el)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) zstd_huf_gcc12_O2_mc /\
               read PC s = word(pc + 0xca0) /\ read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [hw; word 256; rs; nbp; tlp; src; word(LENGTH l);
                            wk] s /\
               read (memory :> bytes64 stackpointer) s = word 876 /\
               read (memory :> bytes(src,LENGTH l)) s = num_of_bytelist l /\
               read (memory :> bytes64 (word(pc + 0x20000))) s = fcpy /\
               read (memory :> bytes64 (word(pc + 0x20010))) s = fset /\
               read (memory :> bytes(ea,el)) s = ev /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (!ws ml h. huf_weights T l ws ml h
                          ==> read X0 s = word h /\
                              read (memory :> bytes(hw,LENGTH ws)) s =
                              num_of_bytelist(MAP word ws) /\
                              read (memory :> bytes(rs,52)) s =
                              num_of_wordlist
                               (list_of_seq (\j. word(huf_rank ws j):int32)
                                            13) /\
                              read (memory :> bytes32 nbp) s =
                              word(LENGTH ws) /\
                              read (memory :> bytes32 tlp) s = word ml) /\
               ((!ws ml h. ~huf_weights T l ws ml h)
                ==> zstd_is_error(read X0 s)) /\
               (?e2. read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                      [src,LENGTH l; hw,256; rs,52; wk,876;
                       word_sub stackpointer (word 320),320; stackpointer,8;
                       word(pc + 0x20000),8; word(pc + 0x20010),8; ea,el;
                       word_add (word pc) (word 31600),128]
                      [hw,256; rs,52; nbp,4; tlp,4; wk,876;
                       word_sub stackpointer (word 320),320]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
           MAYCHANGE [memory :> bytes(hw,256); memory :> bytes(rs,52);
                      memory :> bytes(nbp,4); memory :> bytes(tlp,4);
                      memory :> bytes(wk,876);
                      memory :> bytes(word_sub stackpointer (word 320),320)])`,
  RS_START_TAC THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 0` THENL
   [ZSTD_STEPS_TAC (1--5) THEN
    RS_TOP_ERROR_TAC(ASM_MESON_TAC[LENGTH_EQ_NIL]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`src:int64`; `l:byte list`; `0`; `s0:armstate`]
    READ_MEMORY_BYTES8_BYTELIST) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(LENGTH(l:byte list) = 0)` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  MP_TAC(ISPEC `EL 0 (l:byte list)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_CASES_TAC `val(EL 0 (l:byte list)) <= 127` THEN
  ZSTD_STEPS_TAC (1--15) THENL [RS_FSE_PATH_TAC; RS_RAW_PATH_TAC]);;

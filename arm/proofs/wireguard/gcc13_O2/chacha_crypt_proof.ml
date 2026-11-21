(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of chacha_crypt_spec.ml, with the byte arrays as     *)
(* functions (wg_bytes in arm/proofs/utils/wireguard.ml): fs for the source  *)
(* and cf for the output. With n the size, the loop over the n DIV 64 whole  *)
(* blocks (if n >= 64) reaches join1 with the first 64 * (n DIV 64) bytes at *)
(* dst done, the counter advanced by n DIV 64 and the rest of the source     *)
(* unchanged; then if n MOD 64 is not 0 one more block is computed and the   *)
(* n MOD 64 remaining bytes are xored with the start of it by __crypto_xor.  *)
(* Each block is computed by chacha_block_generic into the buffer on the     *)
(* stack, and the loop body xors it with the source 64 bits at a time. As    *)
(* for __crypto_xor, the proof is the same when dst is src (in place) as     *)
(* when they are disjoint, the source aa of the tactics being either.        *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/chacha_crypt_spec.ml";;

let WIREGUARD_CHACHA_CRYPT_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "chacha_crypt"; layout_range "plt_memset"];;

let CC_EXEC = WIREGUARD_CHACHA_CRYPT_GCC13_O2_EXEC;;

let CC_BLOCK_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA_BLOCK_GENERIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CC_XOR_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CC_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CRYPTO_XOR_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the number of bytes of whole blocks, the size and the number of   *)
(* remaining bytes as the code computes them from the 32-bit size, and the   *)
(* arithmetic of the block indices and of the number of blocks used.         *)
(* ------------------------------------------------------------------------- *)

let CC_NBLOCKS_BYTES = prove
 (`!len:int64 n. 64 <= n /\ n < 2 EXP 32 /\ val len = n
     ==> word_shl (word_subword (word_zx (word_add (word_ushr (word_sub
            (word_subword len (0,32):int32) (word 64)) 6) (word 1)):int64)
            (0,27):int64) 6 =
         word(64 * (n DIV 64))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_SUBWORD; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
              VAL_WORD_USHR; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[DIV_1] THEN
  SUBGOAL_THEN `n MOD 4294967296 = n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `n < 2 EXP 32` THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(n - 64) DIV 64 + 1 = n DIV 64` SUBST1_TAC THENL
   [UNDISCH_TAC `64 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n DIV 64 < 134217728` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n DIV 64 < 4294967296 /\ n DIV 64 < 18446744073709551616`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n DIV 64 < 134217728` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let CC_LEN_ZX = prove
 (`!len:int64. val len < 2 EXP 32
     ==> word_zx(word_subword len (0,32):int32):int64 = len`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  UNDISCH_TAC `val(len:int64) < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN
  ASM_ARITH_TAC);;

let CC_TAIL_LENGTH = prove
 (`!len:int64. val len < 2 EXP 32
     ==> word_zx (word_and (word_subword len (0,32):int32) (word 63)):int64 =
         word(val len MOD 64)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`word_subword (len:int64) (0,32):int32`; `6`]
    (CONJUNCT1 WORD_AND_MASK_WORD)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  UNDISCH_TAC `val(len:int64) < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `val(len:int64) MOD 64 < 4294967296` ASSUME_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN
  SUBGOAL_THEN `val(len:int64) MOD 64 < 18446744073709551616` ASSUME_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

let CC_MOD_DIV_64 = prove
 (`!j r. r < 64 ==> (64 * j + r) MOD 64 = r /\ (64 * j + r) DIV 64 = j`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; MOD_LT; DIV_LT;
               ADD_CLAUSES]);;

let CC_CEIL_DIV = prove
 (`!n. (n + 63) DIV 64 = if n MOD 64 = 0 then n DIV 64 else n DIV 64 + 1`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `64`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = n DIV 64` THEN ABBREV_TAC `r = n MOD 64` THEN
  STRIP_TAC THEN UNDISCH_TAC `n = q * 64 + r` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; EQ_ADD_LCANCEL] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r - 1` THEN ASM_ARITH_TAC);;

let CC_WORD_SUB_ADD = WORD_RULE
  `word_sub (word_add (x:int64) a) (word_add x b) = word_sub a b`;;

(* ------------------------------------------------------------------------- *)
(* The setup: the source as the function fs, the output as cf, n the size.   *)
(* The memset contract is kept for chacha_block_generic as well as expanded  *)
(* (labelled) for the call here.                                             *)
(* ------------------------------------------------------------------------- *)

let CC_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `dst:int64`; `src:int64`; `len:int64`; `xs:num->int32`;
    `sl:byte list`; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "memset" (REWRITE_RULE[memset_contract] th))
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 25; 26; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 112):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  REWRITE_TAC[WG_NUM_OF_BYTELIST_SEQ] THEN
  ASM_SIMP_TAC[WG_BYTES_OF_LIST] THEN
  ABBREV_TAC `cf = \i. word_xor (EL i (sl:byte list))
                        (EL (i MOD 64) (chacha20_kblock xs (i DIV 64)))` THEN
  ABBREV_TAC `fs = \i. EL i (sl:byte list)` THEN
  SUBGOAL_THEN
   `!i. (cf:num->byte) i =
        word_xor (fs i) (EL (i MOD 64) (chacha20_kblock xs (i DIV 64)))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cf"; "fs"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n = val(len:int64)`;;

(* ------------------------------------------------------------------------- *)
(* The frame (from SP + 112, the stack pointer after the entry being         *)
(* stackpointer + 112 here), the invariant of the loop over the blocks after *)
(* j of them, and the state at join1 (after the whole blocks).               *)
(* ------------------------------------------------------------------------- *)

let cc_slots =
  map (fun (k,v) -> vsubst [mk_small_numeral k,`k:num`; v,`v:int64`]
        `read (memory :> bytes64 (word_add stackpointer (word k))) s = v`)
   [112,`x29_init:int64`; 120,`returnaddress:int64`; 128,`x19_init:int64`;
    136,`x20_init:int64`; 144,`x21_init:int64`; 152,`x22_init:int64`;
    160,`x23_init:int64`; 168,`x24_init:int64`; 176,`x25_init:int64`;
    184,`x26_init:int64`];;

let cc_loop_tm aa =
  let body = list_mk_conj(
    [`read SP s = word_add stackpointer (word 112)`;
     `read X29 s = word_add stackpointer (word 112)`;
     `read X19 s = st`; `read X20 s = word 20`;
     `read X21 s = word(64 * (n DIV 64))`;
     subst [aa,`aa:int64`] `read X22 s = word_add aa (word(64 * (n DIV 64)))`;
     `read X23 s = len`; `read X24 s = dst`;
     subst [aa,`aa:int64`] `read X25 s = word_add aa (word(64 * j))`;
     `read X26 s = word_add dst (word(64 * j))`] @ cc_slots @
    [`read (memory :> bytes64 (word_add (word pc) (word 37016))) s = mset`;
     `read (memory :> bytes(ea1,el1)) s = ev1`;
     `!i. i < 16 ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s =
                     chacha20_ctr xs j i`;
     `read (memory :> bytes(dst,64 * j)) s = wg_bytes (cf:num->byte) (64 * j)`;
     subst [aa,`aa:int64`]
      `read (memory :> bytes(word_add aa (word(64 * j)),n - 64 * j)) s =
       wg_bytes (\i. (fs:num->byte)(64 * j + i)) (n - 64 * j)`]) in
  list_mk_abs([`j:num`; `s:armstate`],
    mk_conj(body,`read ZF s <=> j = n DIV 64`));;

let cc_join_tm aa =
  let body = list_mk_conj(
    [`read SP s = word_add stackpointer (word 112)`;
     `read X29 s = word_add stackpointer (word 112)`;
     `read X19 s = st`; `read X20 s = word 20`;
     subst [aa,`aa:int64`] `read X22 s = word_add aa (word(64 * (n DIV 64)))`;
     `read X23 s = word(n MOD 64)`;
     `read X24 s = word_add dst (word(64 * (n DIV 64)))`] @ cc_slots @
    [`read (memory :> bytes64 (word_add (word pc) (word 37016))) s = mset`;
     `read (memory :> bytes(ea1,el1)) s = ev1`;
     `!i. i < 16 ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s =
                     chacha20_ctr xs (n DIV 64) i`;
     `read (memory :> bytes(dst,64 * (n DIV 64))) s =
      wg_bytes (cf:num->byte) (64 * (n DIV 64))`;
     subst [aa,`aa:int64`]
      `read (memory :> bytes(word_add aa (word(64 * (n DIV 64))),n MOD 64)) s =
       wg_bytes (\i. (fs:num->byte)(64 * (n DIV 64) + i)) (n MOD 64)`]) in
  mk_abs(`s:armstate`,body);;

(* ------------------------------------------------------------------------- *)
(* Common steps: the state words as 16 facts; the 32-bit size; the number of *)
(* bytes of whole blocks; the state words at the end, unchanged for no       *)
(* blocks; the block and the state after chacha_block_generic for the        *)
(* counter advanced by jt, the block as a function.                          *)
(* ------------------------------------------------------------------------- *)

let CC_STATE_EXPAND_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `st:int64`)) (concl th))) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

let CC_ZX3_TAC =
  SUBGOAL_THEN
   `val(word_zx (word_zx (word_zx (len:int64):int32):int64):int32) = n`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n < 2 EXP 32 /\ n < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

let cc_ls63 =
  MP (SPECL [`word_zx (word_zx (word_zx (len:int64):int32):int64):int32`;
             `63`] WG_VAL_LS_COND32)
     (ARITH_RULE `63 < 2 EXP 32`);;

let CC_NB_TAC =
  SUBGOAL_THEN `64 <= n /\ n < 2 EXP 32 /\ val(len:int64) = n` (fun th ->
    ASSUME_TAC(MP (SPECL [`len:int64`; `n:num`] CC_NBLOCKS_BYTES) th)) THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC];;

let CC_STATE_POST_TAC =
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[chacha20_ctr; WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0];;

let CC_BLOCK_POST_AT_TAC s jt =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) s)) (concl th))) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> t = `chacha20_words`)) (concl th) &&
       can (find_term ((=) s)) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM chacha20_kblock] th)
    else failwith "") THEN
  FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> t = `chacha20_kblock`)) (concl th) &&
       can (find_term ((=) s)) (concl th) && is_eq (concl th)
    then ASSUME_TAC(REWRITE_RULE[MATCH_MP WG_BYTES_OF_LIST
           (ISPECL [`xs:num->int32`; jt] LENGTH_CHACHA20_KBLOCK)] th)
    else failwith "");;

(* ------------------------------------------------------------------------- *)
(* The loop body for block j: the 8 words of the source (at aa) and of the   *)
(* block (at stackpointer + 192) as memory words, and the rest of the        *)
(* source; then the 8 words stored at dst as arrays of 8 bytes of cf, and    *)
(* these appended to the output so far.                                      *)
(* ------------------------------------------------------------------------- *)

let cc_src64 aa =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,aa),`word(64 * j):int64`);;

let cc_srcf = `\i. (fs:num->byte)(64 * j + i)`;;

let cc_srcaddr aa m =
  if m = 0 then cc_src64 aa else
  mk_comb(mk_comb(`word_add:int64->int64->int64`,aa),
    mk_comb(`word:num->int64`,
            mk_binop `(+):num->num->num` `64 * j` (mk_small_numeral(8*m))));;

let cc_strf = `\i. EL i (chacha20_kblock xs j)`;;

let cc_straddr m =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral(192 + 8*m)));;

let CC_CHUNKS_TAC aa s =
  MAP_EVERY (fun m ->
    WG_BYTES_FUN_SUB_TAC (cc_src64 aa) cc_srcf `n - 64 * j` s
                         (mk_small_numeral(8*m)) `8` THEN
    WG_WORD_FACT_AT_TAC (cc_srcaddr aa m) s 8 THEN
    WG_BYTES_FUN_SUB_TAC `word_add stackpointer (word 192):int64` cc_strf `64`
                         s (mk_small_numeral(8*m)) `8` THEN
    WG_WORD_FACT_AT_TAC (cc_straddr m) s 8) (0--7) THEN
  WG_BYTES_FUN_SUB_TAC (cc_src64 aa) cc_srcf `n - 64 * j` s `64`
                       `n - (64 * j + 64)`;;

let cc_dstaddr m = cc_srcaddr `dst:int64` m;;

let cc_cffun m =
  if m = 0 then `\i. (cf:num->byte)(64 * j + i)` else
  mk_abs(`i:num`,mk_comb(`cf:num->byte`,
    mk_binop `(+):num->num->num` `64 * j`
             (mk_binop `(+):num->num->num` (mk_small_numeral(8*m)) `i:num`)));;

let cc_low m =
  if m = 0 then `i:num` else
  mk_binop `(+):num->num->num` (mk_small_numeral(8*m)) `i:num`;;

let CC_CHUNK_OUT_TAC s m =
  let tm = vsubst [cc_dstaddr m,`x:int64`; s,`s:armstate`;
                   cc_cffun m,`g:num->byte`]
             `read (memory :> bytes(x,8)) s = wg_bytes g 8` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 WG_READ_BYTES_OF_WORDS) THEN CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq(concl th) &&
         lhand(concl th) = vsubst [cc_dstaddr m,`x:int64`; s,`s:armstate`]
                             `read (memory :> bytes64 x) s`
        then REWRITE_TAC[th] else failwith "CC_CHUNK_OUT_TAC") THEN
      REWRITE_TAC[CONJUNCT1 WG_XOR_BYTES_FUN] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC WG_BYTES_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`j:num`; cc_low m] CC_MOD_DIV_64) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 8` THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> ASM_REWRITE_TAC[th]);
      REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP (8 * 8)`; WG_BYTES_BOUND]];
    ALL_TAC];;

let CC_COMBINE_TAC s m =
  let k = if m = 0 then `64 * j` else
          mk_binop `(+):num->num->num` `64 * j` (mk_small_numeral(8*m)) in
  MP_TAC(SPECL [`dst:int64`; `cf:num->byte`; k; `8`; s]
               WG_READ_BYTES_FUN_COMBINE) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* From the entry to join1: the entry (with the zeroing of the block buffer  *)
(* by memset) and the size test, then no blocks (n <= 63) or the loop.       *)
(* ------------------------------------------------------------------------- *)

let CC_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN CC_STATE_EXPAND_TAC THEN
  ARM_STEPS_TAC CC_EXEC (1--15) THEN
  WG_PLT_TAC CC_EXEC 15 THEN
  WG_CALL_TAC "memset" CC_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC CC_EXEC (21--22) THEN CC_ZX3_TAC;;

let CC_SHORT_TAC =
  CC_ENTRY_TAC THEN
  WG_PC_REWRITE_TAC[cc_ls63;
    ASSUME `val(word_zx (word_zx (word_zx (len:int64):int32):int64):int32) = n`;
    ASSUME `n <= 63`] THEN
  WG_STEPS_TAC CC_EXEC (23--24) THEN
  SUBGOAL_THEN `n DIV 64 = 0 /\ n MOD 64 = n` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIV_LT; MOD_LT; ARITH_RULE `n <= 63 ==> n < 64`]; ALL_TAC] THEN
  SUBGOAL_THEN `word_zx(word_subword (len:int64) (0,32):int32):int64 = len`
  ASSUME_TAC THENL [MATCH_MP_TAC CC_LEN_ZX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `word n:int64 = len` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `val(len:int64) = n`); WORD_VAL]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; ADD_CLAUSES; ETA_AX] THEN
  CONJ_TAC THENL
   [CC_STATE_POST_TAC;
    REWRITE_TAC[wg_bytes; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]];;

let CC_LOOP_TAC aa =
  ENSURES_WHILE_PUP_TAC `n DIV 64` `pc + chacha_crypt_loop1`
    `pc + chacha_crypt_loop1_back` (cc_loop_tm aa) THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;

    CC_ENTRY_TAC THEN
    WG_PC_REWRITE_TAC[cc_ls63;
      ASSUME
       `val(word_zx (word_zx (word_zx (len:int64):int32):int64):int32) = n`;
      ASSUME `~(n <= 63)`] THEN
    WG_STEPS_TAC CC_EXEC (23--28) THEN CC_NB_TAC THEN
    SUBGOAL_THEN `word_zx(word_subword (len:int64) (0,32):int32):int64 = len`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CC_LEN_ZX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; ADD_CLAUSES; ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [CC_STATE_POST_TAC;
      REWRITE_TAC[wg_bytes; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL]];

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    CC_STATE_EXPAND_TAC THEN
    SUBGOAL_THEN `64 * j + 64 <= n` ASSUME_TAC THENL
     [UNDISCH_TAC `j < n DIV 64` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC CC_EXEC (1--4) THEN
    SUBGOAL_THEN
     `!i. i < 16 ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s4 =
                     chacha20_ctr xs j i`
    ASSUME_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[WORD_ADD_0];
      ALL_TAC] THEN
    GOT_ENTRY_TAC `got_memset:num` `s4:armstate` THEN
    CC_BLOCK_TAC [`read X0 s`; `read X1 s`; `chacha20_ctr xs j`; `mset:int64`;
                  `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`; `read SP s`;
                  `read X30 s`] 5 THEN
    CC_BLOCK_POST_AT_TAC `s5:armstate` `j:num` THEN
    CC_CHUNKS_TAC aa `s5:armstate` THEN
    WG_STEPS_TAC CC_EXEC (6--66) THEN
    MAP_EVERY (CC_CHUNK_OUT_TAC `s66:armstate`) (0--7) THEN
    MAP_EVERY (CC_COMBINE_TAC `s66:armstate`) (0--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN REWRITE_TAC[chacha20_ctr] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      REWRITE_TAC[CC_WORD_SUB_ADD] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) WG_VAL_WORD_SUB_EQ_0 o
        lhand o snd) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `64 * j + 64 <= n` THEN UNDISCH_TAC `n < 2 EXP 32` THEN
        ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN ARITH_TAC]];

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    CC_STATE_EXPAND_TAC THEN
    ARM_STEPS_TAC CC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];

    ENSURES_INIT_TAC "s0" THEN CC_STATE_EXPAND_TAC THEN
    WG_STEPS_TAC CC_EXEC (1--3) THEN
    SUBGOAL_THEN `val(len:int64) < 2 EXP 32` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[CC_TAIL_LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `n MOD 64 = n - 64 * (n DIV 64)`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0]];;

(* ------------------------------------------------------------------------- *)
(* From join1 to the return: no remaining bytes, or the last block and the   *)
(* call of __crypto_xor for the n MOD 64 remaining bytes (the inputs given   *)
(* as lists: the rest of the source and the start of the block).             *)
(* ------------------------------------------------------------------------- *)

let CC_RET_TAC =
  REWRITE_TAC[ASSUME `n MOD 64 = 0`] THEN
  ENSURES_INIT_TAC "s0" THEN CC_STATE_EXPAND_TAC THEN
  ARM_STEPS_TAC CC_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `64 * n DIV 64 = n` ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `64`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes(dst,64 * n DIV 64)) s7 =
                 wg_bytes (cf:num->byte) (64 * n DIV 64)` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[CC_CEIL_DIV] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0]];;

let CC_R_TAC =
  SUBGOAL_THEN `val(word_zx (word (n MOD 64):int64):int32) = n MOD 64`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    SUBGOAL_THEN `n MOD 64 < 2 EXP 32 /\ n MOD 64 < 2 EXP 64`
    STRIP_ASSUME_TAC THENL [ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC];;

let cc_la = `list_of_seq (\i. (fs:num->byte) (64 * n DIV 64 + i)) (n MOD 64)`;;

let cc_lb =
  `list_of_seq (\i. EL i (chacha20_kblock xs (n DIV 64))) (n MOD 64)`;;

let CC_XOR_PRE_TAC aa s =
  SUBGOAL_THEN `val(word (n MOD 64):int64) = n MOD 64` ASSUME_TAC THENL
   [MATCH_MP_TAC WG_VAL_WORD_SMALL THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_zx (word_subword (word (n MOD 64):int64) (0,32):int32):int64 =
    word (n MOD 64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CC_LEN_ZX THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `word_zx (word_subword (word (n MOD 64):int64) (0,32):int32):int64 =
    word (n MOD 64)`]) THEN
  ASSUME_TAC(ARITH_RULE `n MOD 64 < 2 EXP 32`) THEN
  ASSUME_TAC(ISPECL [`\i. (fs:num->byte) (64 * n DIV 64 + i)`; `n MOD 64`]
                    LENGTH_LIST_OF_SEQ) THEN
  ASSUME_TAC(ISPECL [`\i. EL i (chacha20_kblock xs (n DIV 64))`; `n MOD 64`]
                    LENGTH_LIST_OF_SEQ) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       lhand(concl th) = vsubst [aa,`aa:int64`; s,`s:armstate`]
        `read (memory :> bytes(word_add aa (word(64 * n DIV 64)),n MOD 64)) s`
    then ASSUME_TAC(REWRITE_RULE[GSYM WG_NUM_OF_BYTELIST_SEQ] th)
    else failwith "CC_XOR_PRE_TAC") THEN
  MP_TAC(SPECL [`word_add stackpointer (word 192):int64`;
                `\i. EL i (chacha20_kblock xs (n DIV 64))`; `64`; `0`;
                `n MOD 64`; s] WG_READ_BYTES_FUN_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE
    [WORD_ADD_0; ADD_CLAUSES; ETA_AX; GSYM WG_NUM_OF_BYTELIST_SEQ]);;

let CC_TAIL_OUT_TAC s =
  SUBGOAL_THEN
   (vsubst [s,`s:armstate`]
     `read (memory :> bytes(word_add dst (word(64 * n DIV 64)),n MOD 64)) s =
      wg_bytes (\i. (cf:num->byte)(64 * n DIV 64 + i)) (n MOD 64)`)
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       lhand(concl th) = vsubst [s,`s:armstate`]
         `read (memory :> bytes(word_add dst (word(64 * n DIV 64)),n MOD 64)) s`
      then REWRITE_TAC[th] else failwith "CC_TAIL_OUT_TAC") THEN
    REWRITE_TAC[WG_NUM_OF_BYTELIST_SEQ] THEN
    MATCH_MP_TAC WG_BYTES_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    SUBGOAL_THEN `i < 64` ASSUME_TAC THENL
     [TRANS_TAC LT_TRANS `n MOD 64` THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ASM_SIMP_TAC[CC_MOD_DIV_64]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`dst:int64`; `cf:num->byte`; `64 * n DIV 64`; `n MOD 64`; s]
               WG_READ_BYTES_FUN_COMBINE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `64 * n DIV 64 + n MOD 64 = n` SUBST1_TAC THENL
   [MP_TAC(SPECL [`n:num`; `64`] DIVISION) THEN ARITH_TAC; DISCH_TAC];;

let CC_TAIL_TAC aa =
  ENSURES_INIT_TAC "s0" THEN CC_STATE_EXPAND_TAC THEN
  ARM_STEPS_TAC CC_EXEC [1] THEN CC_R_TAC THEN
  WG_PC_REWRITE_TAC
   [ASSUME `val(word_zx (word (n MOD 64):int64):int32) = n MOD 64`;
    ASSUME `~(n MOD 64 = 0)`] THEN
  ARM_STEPS_TAC CC_EXEC (2--5) THEN
  SUBGOAL_THEN
   `!i. i < 16 ==> read (memory :> bytes32 (word_add st (word(4 * i)))) s5 =
                   chacha20_ctr xs (n DIV 64) i`
  ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  GOT_ENTRY_TAC `got_memset:num` `s5:armstate` THEN
  CC_BLOCK_TAC [`read X0 s`; `read X1 s`; `chacha20_ctr xs (n DIV 64)`;
                `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
                `read SP s`; `read X30 s`] 6 THEN
  CC_BLOCK_POST_AT_TAC `s6:armstate` `n DIV 64` THEN
  WG_STEPS_TAC CC_EXEC (7--11) THEN
  CC_XOR_PRE_TAC aa `s11:armstate` THEN
  CC_XOR_TAC [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; cc_la; cc_lb;
              `pc:num`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC CC_EXEC (13--18) THEN CC_TAIL_OUT_TAC `s18:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CC_CEIL_DIV] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM CHACHA20_CTR_ADD] THEN REWRITE_TAC[CHACHA20_CTR_1] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let CC_MAIN_TAC aa =
  ENSURES_SEQUENCE_TAC `pc + chacha_crypt_join1` (cc_join_tm aa) THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n <= 63` THENL [CC_SHORT_TAC; CC_LOOP_TAC aa];
    ASM_CASES_TAC `n MOD 64 = 0` THENL [CC_RET_TAC; CC_TAIL_TAC aa]];;

let WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CC_SETUP_TAC THEN ASM_CASES_TAC `dst:int64 = src` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                  check (fun th -> concl th = `dst:int64 = src`)) THEN
    CC_MAIN_TAC `dst:int64`;
    UNDISCH_TAC
     `dst:int64 = src \/
      nonoverlapping_modulo (2 EXP 64) (val dst,n) (val(src:int64),n)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CC_MAIN_TAC `src:int64`]);;

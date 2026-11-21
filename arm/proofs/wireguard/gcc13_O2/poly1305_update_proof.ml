(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of poly1305_update_spec.ml. With b and q the length  *)
(* of d mod and div 16 and n the size, rho (the number of bytes left for the *)
(* buffer at the end) is n if b + n < 16 and (b + n) mod 16 otherwise. All   *)
(* paths reach join1 with the state for d followed by the first n - rho      *)
(* bytes of m, the buffer then being empty unless b + n < 16; from there the *)
(* rho bytes are copied to the buffer (memcpy) and buflen updated. From the  *)
(* entry: (A) if b + n < 16 join1 is reached at once; otherwise (B0) if b is *)
(* 0 the n div 16 whole blocks at src are absorbed by poly1305_core_blocks,  *)
(* or (B1) the buffer is completed with the first 16 - b bytes (memcpy) and  *)
(* absorbed, and then the whole blocks of the rest, if any.                  *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/poly1305_update_spec.ml";;

let WIREGUARD_POLY1305_UPDATE_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "poly1305_update"; layout_range "plt_memcpy"];;

let PU_EXEC = WIREGUARD_POLY1305_UPDATE_GCC13_O2_EXEC;;

let PU_BLOCKS_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,PU_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: rho and the lengths at join1, the lists of the bytes absorbed and *)
(* buffered, and the accumulator after the buffer is completed.              *)
(* ------------------------------------------------------------------------- *)

let PU_RHO = prove
 (`!L n rho.
     rho = (if L MOD 16 + n < 16 then n else (L MOD 16 + n) MOD 16)
     ==> rho <= n /\ rho < 16 /\
         (L + n - rho) MOD 16 + rho = (L + n) MOD 16 /\
         (L + n - rho) DIV 16 = (L + n) DIV 16`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`L:num`; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = L DIV 16`; `b = L MOD 16`] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[SUB_REFL; ADD_CLAUSES] THEN
    MP_TAC(SPECL [`L + n`; `16`; `q:num`; `b + n`] DIVMOD_UNIQ) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`b + n`; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    MAP_EVERY ABBREV_TAC [`c = (b + n) DIV 16`; `r = (b + n) MOD 16`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `1 <= c` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r <= n` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`b + n = c * 16 + r`; `1 <= c`; `b < 16`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`L + n - r`; `16`; `q + c`; `0`] DIVMOD_UNIQ) THEN
    MP_TAC(SPECL [`L + n`; `16`; `q + c`; `r:num`] DIVMOD_UNIQ) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let PU_E_PREFIX = prove
 (`!(d:byte list) m j.
     j <= LENGTH m
     ==> APPEND d (SUB_LIST(0,j) m) = SUB_LIST(0,LENGTH d + j) (APPEND d m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:byte list`; `m:byte list`; `0`; `LENGTH(d:byte list)`;
                 `j:num`] WG_SUB_LIST_APPEND_STRADDLE) THEN
  REWRITE_TAC[ADD_CLAUSES; SUB_LIST_LENGTH] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

let PU_TAIL_LIST = prove
 (`!(d:byte list) m j r Q R0.
     j + r <= LENGTH m /\ LENGTH d + j = 16 * Q + R0
     ==> APPEND (SUB_LIST(16 * Q,R0) (APPEND d (SUB_LIST(0,j) m)))
                (SUB_LIST(j,r) m) =
         SUB_LIST(16 * Q,R0 + r) (APPEND d m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:byte list`; `m:byte list`; `j:num`] PU_E_PREFIX) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [SUB_LIST_SPLIT] THEN BINOP_TAC THENL
   [MATCH_MP_TAC WG_SUB_LIST_SUB_LIST_0 THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhand(concl th) = `LENGTH(d:byte list) + j`)) THEN
    REWRITE_TAC[WG_SUB_LIST_APPEND_RIGHT]]);;

let PU_KACC_E = prove
 (`!r a (d:byte list) m j hb Q.
     j <= LENGTH m /\ 16 * Q <= LENGTH d + j
     ==> poly1305_kacc r a (APPEND d (SUB_LIST(0,j) m)) hb Q =
         poly1305_kacc r a (APPEND d m) hb Q`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PU_E_PREFIX] THEN
  MATCH_MP_TAC POLY1305_KACC_PREFIX THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WG_SUB_LIST_SUB_LIST_0 THEN ASM_ARITH_TAC);;

(* In path B1, the q blocks of d, then the buffer of the last b bytes of d   *)
(* and the first 16 - b of m, then j more blocks of m.                       *)

let PU_KACC_FILL = prove
 (`!r (d:byte list) (m:byte list) q b j.
     LENGTH d = 16 * q + b /\ b <= 16 /\ (16 - b) + 16 * j <= LENGTH m
     ==> poly1305_kacc r 0 (APPEND d (SUB_LIST(0,(16 - b) + 16 * j) m)) 1
                       ((q + 1) + j) =
         poly1305_kacc r
          (poly1305_kacc r (poly1305_kacc r 0 d 1 q)
             (APPEND (SUB_LIST(16 * q,b) d) (SUB_LIST(0,16 - b) m)) 1 1)
          (SUB_LIST(16 - b,16 * j) m) 1 j`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RATOR_CONV o RAND_CONV o RAND_CONV)
   [SUB_LIST_SPLIT] THEN
  REWRITE_TAC[ADD_CLAUSES; APPEND_ASSOC] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,16 - b) (m:byte list)) = 16 - b /\
                LENGTH(SUB_LIST(0,16 * q) (d:byte list)) = 16 * q`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
     [`r:num`; `0`; `APPEND d (SUB_LIST(0,16 - b) (m:byte list))`;
      `SUB_LIST(16 - b,16 * j) (m:byte list)`; `1`; `q + 1`; `j:num`]
     POLY1305_KACC_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `d = APPEND (SUB_LIST(0,16 * q) d) (SUB_LIST(16 * q,b) (d:byte list))`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o funpow 2 RATOR_CONV o RAND_CONV o
                              LAND_CONV) [th]) THENL
   [REWRITE_TAC[GSYM(REWRITE_RULE[ADD_CLAUSES] (ISPECL
      [`d:byte list`; `16 * q`; `b:num`; `0`] SUB_LIST_SPLIT))] THEN
    REWRITE_TAC[GSYM(ASSUME `LENGTH(d:byte list) = 16 * q + b`);
                SUB_LIST_LENGTH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MP_TAC(ISPECL
     [`r:num`; `0`; `SUB_LIST(0,16 * q) (d:byte list)`;
      `APPEND (SUB_LIST(16 * q,b) d) (SUB_LIST(0,16 - b) (m:byte list))`;
      `1`; `q:num`; `1`] POLY1305_KACC_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC POLY1305_KACC_PREFIX THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WG_SUB_LIST_SUB_LIST_0 THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the words of the code, the sizes being below 2^32.                *)
(* ------------------------------------------------------------------------- *)

let PU_ZX32 = prove
 (`!x. x < 2 EXP 32 ==> word_zx(word x:int64):int32 = word x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `x < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `x < 2 EXP 32` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

let PU_BULK_WORD = prove
 (`!x:int32. word_and x (word 4294967280) = word_shl (word_ushr x 4) 4`,
  BITBLAST_TAC);;

let PU_AND_MASKS = prove
 (`!n. n < 2 EXP 32
       ==> val(word_and (word n:int32) (word 4294967280)) = 16 * n DIV 16 /\
           val(word_and (word n:int32) (word 15)) = n MOD 16`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[PU_BULK_WORD; VAL_WORD_SHL; VAL_WORD_USHR; VAL_WORD;
                DIMINDEX_32] THEN
    ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `15 = 2 EXP 4 - 1`; VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN ASM_SIMP_TAC[MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* In path B1, the size of the rest b + (n - 16) computed in 32 bits.        *)

let PU_X19_B1 = prove
 (`!b n (nbytes:int64).
     b < 16 /\ val nbytes = n /\ n < 2 EXP 32 /\ 16 <= b + n
     ==> word_zx (word_add (word_zx (word b:int64):int32)
           (word_zx (word_zx (word_sub (word_zx nbytes:int32)
                                       (word 16)):int64):int32)):int64 =
         word((b + n) - 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WG_WORD_ZX_ZX] THEN
  SUBGOAL_THEN `b < 2 EXP 32 /\ (b + n) - 16 < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_zx(nbytes:int64):int32 = word n` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PU_ZX32] THEN
  SUBGOAL_THEN `word_add (word b) (word_sub (word n) (word 16)):int32 =
                word((b + n) - 16)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_add (a:int32) (word_sub c d) =
                           word_sub (word_add a c) d`] THEN
    ASM_SIMP_TAC[GSYM WORD_ADD; WORD_SUB];
    ASM_SIMP_TAC[WG_WORD_ZX_SMALL]]);;

(* ------------------------------------------------------------------------- *)
(* The setup, and the state at join1, after the first n - rho bytes.         *)
(* ------------------------------------------------------------------------- *)

let PU_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`desc:int64`; `src:int64`; `nbytes:int64`; `k:byte list`; `d:byte list`;
    `m:byte list`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "memcpy" o REWRITE_RULE[memcpy_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ABBREV_TAC `n = val(nbytes:int64)` THEN
  ABBREV_TAC `b = LENGTH(d:byte list) MOD 16` THEN
  ABBREV_TAC `q = LENGTH(d:byte list) DIV 16`;;

let pu_slots =
  map (fun (k,v) -> vsubst [mk_small_numeral k,`k:num`; v,`v:int64`]
        `read (memory :> bytes64 (word_add stackpointer (word k))) s = v`)
   [0,`x29_init:int64`; 8,`returnaddress:int64`; 16,`x19_init:int64`;
    24,`x20_init:int64`; 32,`x21_init:int64`; 40,`x22_init:int64`];;

let pu_j1 = mk_abs(`s:armstate`, list_mk_conj(
   [`read SP s = stackpointer`; `read X29 s = stackpointer`;
    `read X19 s = word rho`; `read X20 s = desc`;
    `read X21 s = word_add src (word(n - rho))`; `read X23 s = x23_init`] @
   map (subst [`stackpointer:int64`,`word_add (stackpointer:int64) (word 0)`])
       pu_slots @
   [`read (memory :> bytes(src,n)) s = num_of_bytelist m`;
    `read (memory :> bytes64 (word_add (word pc) (word 36888))) s = mcpy`;
    `read (memory :> bytes (ea2,el2)) s = ev2`;
    `poly1305_desc_at desc k (APPEND d (SUB_LIST(0,n - rho) m)) s`]));;

(* ------------------------------------------------------------------------- *)
(* From join1: the rho bytes are copied to the buffer after the rb there.    *)
(* ------------------------------------------------------------------------- *)

let PU_W_TAC =
  SUBGOAL_THEN `b < 16` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `rho < 16 /\ rho <= n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `b + n < 16` THEN ARITH_TAC;
      MP_TAC(SPECL [`b + n`; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
      SUBGOAL_THEN `1 <= (b + n) DIV 16` MP_TAC THENL
       [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN UNDISCH_TAC `~(b + n < 16)` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `~(b + n < 16)` THEN UNDISCH_TAC `b < 16` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx(word rho:int64):int32) = rho` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    SUBGOAL_THEN `rho < 2 EXP 32 /\ rho < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `rho < 16` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC];;

let PU_TAIL_SETUP_TAC =
  ABBREV_TAC `e = APPEND d (SUB_LIST(0,n - rho) (m:byte list))` THEN
  REWRITE_TAC[poly1305_desc_at; poly1305_h_at; poly1305_key_at] THEN
  ABBREV_TAC `rb = LENGTH(e:byte list) MOD 16` THEN
  ABBREV_TAC `qb = LENGTH(e:byte list) DIV 16` THEN
  GHOST_INTRO_TAC `h0w:int64`
   `read (memory :> bytes64 (word_add desc (word 40)))` THEN
  GHOST_INTRO_TAC `h1w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 8)))` THEN
  GHOST_INTRO_TAC `h2w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 16)))` THEN
  ENSURES_INIT_TAC "s0" THEN PU_W_TAC THEN
  SUBGOAL_THEN `LENGTH(m:byte list) = n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`LENGTH(d:byte list)`; `n:num`; `rho:num`] PU_RHO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `(if b + n < 16 then n else (b + n) MOD 16) = rho`);
                SYM(ASSUME `LENGTH(d:byte list) MOD 16 = b`)];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(d:byte list) + n - rho = 16 * qb + rb /\ rb < 16 /\
    rb + rho < 16 /\ LENGTH(APPEND d (m:byte list)) MOD 16 = rb + rho /\
    LENGTH(APPEND d (m:byte list)) DIV 16 = qb`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH(e:byte list) = LENGTH(d:byte list) + n - rho`
    (fun th -> REWRITE_TAC[SYM th] THEN
               REWRITE_TAC[SYM(ASSUME `LENGTH(e:byte list) MOD 16 = rb`);
                           SYM(ASSUME `LENGTH(e:byte list) DIV 16 = qb`)] THEN
               REWRITE_TAC[th; LENGTH_APPEND;
                           ASSUME `LENGTH(m:byte list) = n`] THEN
               REPEAT CONJ_TAC THENL
                [MP_TAC(SPECL [`LENGTH(d:byte list) + n - rho`; `16`]
                        DIVISION) THEN
                 REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
                 REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
                 REWRITE_TAC[ASSUME `(LENGTH(d:byte list) + n - rho) MOD 16 +
                                     rho = (LENGTH d + n) MOD 16`] THEN
                 REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
                 CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
                 CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC]) THEN
    REWRITE_TAC[SYM(ASSUME
      `APPEND d (SUB_LIST (0,n - rho) m) = (e:byte list)`)] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST;
                ASSUME `LENGTH(m:byte list) = n`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC PU_EXEC [1];;

(* rho = 0: return at once.                                                  *)

let PU_TAIL0_TAC =
  WG_PC_REWRITE_TAC[ASSUME `val(word_zx(word rho:int64):int32) = rho`;
                    ASSUME `rho = 0`] THEN
  ARM_STEPS_TAC PU_EXEC (2--5) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `e = APPEND d (m:byte list)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[ASSUME `rho = 0`; SUB_0] THEN
    REWRITE_TAC[GSYM(ASSUME `LENGTH(m:byte list) = n`); SUB_LIST_LENGTH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES];;

(* Otherwise memcpy(desc + rb, src + n - rho, rho) and buflen += rho.        *)

let PU_ZX_TAC tms =
  MAP_EVERY (fun t ->
    MP_TAC(SPEC t WG_WORD_ZX_SMALL) THEN ANTS_TAC THENL
     [MAP_EVERY MP_TAC [ASSUME `rho < 16`; ASSUME `rb < 16`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms;;

let PU_TAIL1_TAC =
  WG_PC_REWRITE_TAC[ASSUME `val(word_zx(word rho:int64):int32) = rho`;
                    ASSUME `~(rho = 0)`] THEN
  ARM_STEPS_TAC PU_EXEC (2--6) THEN PU_ZX_TAC [`rb:num`; `rho:num`] THEN
  MP_TAC(ISPECL [`src:int64`; `m:byte list`; `n:num`; `n - rho`; `rho:num`;
                 `s6:armstate`] WG_READ_BYTES_SUBLIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `rho <= n` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `val(word rho:int64) = rho` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `rho < 16` THEN ARITH_TAC;
    ALL_TAC] THEN
  WG_PLT_TAC PU_EXEC 6 THEN
  WG_CALL_TAC "memcpy" PU_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `num_of_bytelist(SUB_LIST(n - rho,rho) (m:byte list))`;
    `read X30 s`] 11 THEN
  ARM_STEPS_TAC PU_EXEC (12--18) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(16 * qb,rb) (e:byte list)) = rb`
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN
    SUBGOAL_THEN `LENGTH(e:byte list) = 16 * qb + rb` SUBST1_TAC THENL
     [REWRITE_TAC[SYM(ASSUME
        `APPEND d (SUB_LIST (0,n - rho) m) = (e:byte list)`)] THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST;
                  ASSUME `LENGTH(m:byte list) = n`] THEN
      UNDISCH_TAC `LENGTH(d:byte list) + n - rho = 16 * qb + rb` THEN
      ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`desc:int64`; `SUB_LIST(16 * qb,rb) (e:byte list)`;
      `SUB_LIST(n - rho,rho) (m:byte list)`; `rho:num`; `s18:armstate`]
      WG_READ_BYTES_APPEND) THEN
    REWRITE_TAC[ASSUME `LENGTH(SUB_LIST(16 * qb,rb) (e:byte list)) = rb`] THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[SYM(ASSUME
      `APPEND d (SUB_LIST (0,n - rho) m) = (e:byte list)`)] THEN
    MATCH_MP_TAC PU_TAIL_LIST THEN
    REWRITE_TAC[ASSUME `LENGTH(m:byte list) = n`;
                ASSUME `LENGTH(d:byte list) + n - rho = 16 * qb + rb`] THEN
    UNDISCH_TAC `rho <= n` THEN ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN
    MAP_EVERY MP_TAC [ASSUME `rb < 16`; ASSUME `rho < 16`] THEN
    SPEC_TAC(`rb:num`,`x:num`) THEN SPEC_TAC(`rho:num`,`y:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x < 4294967296 /\ y < 4294967296 /\ x + y < 4294967296 /\
                  x < 18446744073709551616 /\ y < 18446744073709551616 /\
                  x + y < 18446744073709551616`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT];
    REWRITE_TAC[SYM(ASSUME
      `APPEND d (SUB_LIST (0,n - rho) m) = (e:byte list)`)] THEN
    MATCH_MP_TAC PU_KACC_E THEN
    REWRITE_TAC[ASSUME `LENGTH(m:byte list) = n`;
                ASSUME `LENGTH(d:byte list) + n - rho = 16 * qb + rb`] THEN
    UNDISCH_TAC `rho <= n` THEN ARITH_TAC];;

let PU_TAIL_TAC =
  PU_TAIL_SETUP_TAC THEN ASM_CASES_TAC `rho = 0` THENL
   [PU_TAIL0_TAC; PU_TAIL1_TAC];;

(* ------------------------------------------------------------------------- *)
(* From the entry to join1: the test of b + n <= 15.                         *)
(* ------------------------------------------------------------------------- *)

let PU_ENTRY_SETUP_TAC =
  REWRITE_TAC[poly1305_desc_at; poly1305_h_at; poly1305_key_at] THEN
  GHOST_INTRO_TAC `h0w:int64`
   `read (memory :> bytes64 (word_add desc (word 40)))` THEN
  GHOST_INTRO_TAC `h1w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 8)))` THEN
  GHOST_INTRO_TAC `h2w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 16)))` THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `b < 16 /\ LENGTH(m:byte list) = n /\ n < 2 EXP 32 /\
                LENGTH(d:byte list) = 16 * q + b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `LENGTH(d:byte list) MOD 16 = b`);
                  MOD_LT_EQ; ARITH_EQ];
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `n + 16 < 2 EXP 32` THEN ARITH_TAC;
      MP_TAC(SPECL [`LENGTH(d:byte list)`; `16`] DIVISION) THEN
      REWRITE_TAC[ARITH_EQ; ASSUME `LENGTH(d:byte list) DIV 16 = q`;
                  ASSUME `LENGTH(d:byte list) MOD 16 = b`] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  ARM_STEPS_TAC PU_EXEC (1--11);;

let PU_COND_TAC (asl,w as gl) =
  let pcth = snd(find (fun (_,th) -> let c = concl th in is_eq c &&
     lhand c = `read PC s11`) asl) in
  let t = lhand(find_term (fun t -> match t with
      Comb(Comb(Const("word_sub",_),x),Comb(Const("word",_),k)) -> k = `15`
    | _ -> false) (concl pcth)) in
  let vt = TAC_PROOF((asl,
      mk_eq(mk_comb(mk_const("val",[`:32`,`:N`]),t),`b + n`)),
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `b < 4294967296 /\ b < 18446744073709551616 /\
                  n < 4294967296 /\ b + n < 4294967296 /\
                  b + n < 18446744073709551616 /\ n < 18446744073709551616`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY MP_TAC [ASSUME `b < 16`; ASSUME `n + 16 < 2 EXP 32`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]]) in
  let cth = MP (SPECL [t; `15`] WG_VAL_LS_COND32)
               (ARITH_RULE `15 < 2 EXP 32`) in
  WG_PC_REWRITE_TAC[cth; vt] gl;;

(* (A) b + n <= 15: straight to join1 with rho = n.                          *)

let PU_PATHA_TAC =
  WG_PC_REWRITE_TAC[ASSUME `b + n <= 15`] THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `rho:num = n` SUBST_ALL_TAC THENL
   [REWRITE_TAC[SYM(ASSUME
      `(if b + n < 16 then n else (b + n) MOD 16) = rho`)] THEN
    REWRITE_TAC[MP (ARITH_RULE `b + n <= 15 ==> b + n < 16`)
                   (ASSUME `b + n <= 15`)];
    ALL_TAC] THEN
  REWRITE_TAC[SUB_REFL; SUB_LIST_CLAUSES; APPEND_NIL; WORD_ADD_0] THEN
  REWRITE_TAC[poly1305_desc_at; poly1305_h_at; poly1305_key_at] THEN
  ASM_REWRITE_TAC[] THEN
  TRY(ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `n < 2 EXP 32`) THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `n < 18446744073709551616` ASSUME_TAC THENL
       [UNDISCH_TAC `n < 4294967296` THEN ARITH_TAC;
        ASM_SIMP_TAC[MOD_LT]]);;

(* ------------------------------------------------------------------------- *)
(* (B) b + n >= 16: the test of b = 0 and, for a size x of the rest, the     *)
(* number of bytes 16 * (x DIV 16) of whole blocks and x MOD 16 left, as     *)
(* the code computes them, and the arguments of poly1305_core_blocks.        *)
(* ------------------------------------------------------------------------- *)

let PU_VB_TAC =
  SUBGOAL_THEN `val(word_zx(word_zx(word b:int32):int64):int32) = b`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    SUBGOAL_THEN `b < 2 EXP 32 /\ b < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `b < 16` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC];;

let PU_MASK_FACTS_TAC x =
  let sub tm = vsubst [x,`x:num`] tm in
  MP_TAC(SPEC x PU_AND_MASKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN (sub `16 * x DIV 16 < 2 EXP 32 /\ x MOD 16 < 16`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    MP_TAC(SPECL [x; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC (sub `x < 2 EXP 32`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   (sub `val(word_zx(word_zx(word_and (word x) (word 4294967280):int32):int64)
              :int32) = 16 * x DIV 16 /\
         word_zx(word_and (word x) (word 4294967280):int32):int64 =
         word(16 * x DIV 16) /\
         word_zx(word_and (word x) (word 15):int32):int64 = word(x MOD 16)`)
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ONCE_REWRITE_TAC[GSYM VAL_EQ]) THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (sub `16 * x DIV 16 < 2 EXP 64 /\ x MOD 16 < 2 EXP 32 /\
                       x MOD 16 < 2 EXP 64`)
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [sub `16 * x DIV 16 < 2 EXP 32`;
                             sub `x MOD 16 < 16`] THEN
      ARITH_TAC;
      ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME (sub `word_zx(word_and (word x) (word 4294967280):int32):int64 =
                 word(16 * x DIV 16)`);
    ASSUME (sub `word_zx(word_and (word x) (word 15):int32):int64 =
                 word(x MOD 16)`)]);;

let PU_BULK_NORM_TAC x =
  let sub tm = vsubst [x,`x:num`] tm in
  SUBGOAL_THEN
   (sub `word_zx (word_ushr (word_zx (word (16 * x DIV 16):int64):int32) 4)
           :int64 = word(x DIV 16) /\
         word_zx (word_zx (word (16 * x DIV 16):int64):int32):int64 =
         word(16 * x DIV 16) /\
         val(word(x DIV 16):int64) = x DIV 16 /\ x DIV 16 < 2 EXP 32`)
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN (sub `x DIV 16 < 2 EXP 32 /\ 16 * x DIV 16 < 2 EXP 64 /\
                       x DIV 16 < 2 EXP 64`) STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC (sub `16 * x DIV 16 < 2 EXP 32`) THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ONCE_REWRITE_TAC[GSYM VAL_EQ]) THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 4 = 16`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ; ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME (sub `word_zx (word_ushr (word_zx (word (16 * x DIV 16):int64)
                                             :int32) 4):int64 =
                 word(x DIV 16)`);
    ASSUME (sub `word_zx (word_zx (word (16 * x DIV 16):int64):int32):int64 =
                 word(16 * x DIV 16)`)]);;

(* (B0) b = 0: the n div 16 whole blocks from src, then join1.               *)

let PU_NB_TAC =
  SUBGOAL_THEN
   `word_zx(word_zx(word_zx (nbytes:int64):int32):int64):int32 = word n`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n < 2 EXP 32 /\ n < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC];;

let PU_B0_TAC =
  WG_PC_REWRITE_TAC
   [ASSUME `val(word_zx(word_zx(word b:int32):int64):int32) = b`;
    ASSUME `b = 0`] THEN
  ARM_STEPS_TAC PU_EXEC (13--15) THEN
  PU_NB_TAC THEN PU_MASK_FACTS_TAC `n:num` THEN
  SUBGOAL_THEN `val(word_zx(word(16 * n DIV 16):int64):int32) =
                16 * n DIV 16 /\ ~(16 * n DIV 16 = 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
      SUBGOAL_THEN `16 * n DIV 16 < 2 EXP 64` ASSUME_TAC THENL
       [UNDISCH_TAC `16 * n DIV 16 < 2 EXP 32` THEN ARITH_TAC;
        ASM_SIMP_TAC[MOD_LT]];
      REWRITE_TAC[MULT_EQ_0; ARITH_EQ; DIV_EQ_0] THEN
      MAP_EVERY UNDISCH_TAC [`~(b + n <= 15)`; `b = 0`] THEN ARITH_TAC];
    ALL_TAC] THEN
  WG_PC_REWRITE_TAC[ASSUME `val(word_zx(word(16 * n DIV 16):int64):int32) =
                            16 * n DIV 16`;
                    ASSUME `~(16 * n DIV 16 = 0)`] THEN
  ARM_STEPS_TAC PU_EXEC (16--22) THEN PU_BULK_NORM_TAC `n:num` THEN

  (*** poly1305_core_blocks for the n div 16 blocks ***)

  SUBGOAL_THEN
   `poly1305_h_at (word_add desc (word 40))
                  (poly1305_kacc (poly1305_r k) 0 d 1 q) s22 /\
    poly1305_key_at (word_add desc (word 64)) (poly1305_r k) s22`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[poly1305_h_at; poly1305_key_at] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`src:int64`; `m:byte list`; `n:num`; `0`; `16 * n DIV 16`;
                 `s22:armstate`] WG_READ_BYTES_SUBLIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(SUB_LIST(0,16 * n DIV 16) (m:byte list)) =
    16 * val(word(n DIV 16):int64) /\
    read (memory :> bytes(src,16 * val(word(n DIV 16):int64))) s22 =
    num_of_bytelist(SUB_LIST(0,16 * n DIV 16) m)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN
    MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(SPEC `k:byte list` POLY1305_R_BOUND) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 1:int64)`) THEN
  PU_BLOCKS_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `SUB_LIST(0,16 * n DIV 16) (m:byte list)`;
    `poly1305_kacc (poly1305_r k) 0 d 1 q`; `poly1305_r k`; `pc:num`;
    `read X30 s`] 23 THEN
  POLY1305_H_GHOST_TAC `s23:armstate` THEN ARM_STEPS_TAC PU_EXEC [24] THEN
  ENSURES_FINAL_STATE_TAC THEN

  (*** The state at join1 ***)

  SUBGOAL_THEN `rho = n MOD 16 /\ n - rho = 16 * n DIV 16`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME
      `(if b + n < 16 then n else (b + n) MOD 16) = rho`)] THEN
    REWRITE_TAC[ASSUME `b = 0`; ADD_CLAUSES] THEN
    SUBGOAL_THEN `~(n < 16)` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC [`~(b + n <= 15)`; `b = 0`] THEN ARITH_TAC;
      MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(SUB_LIST(0,16 * n DIV 16) (m:byte list)) = 16 * n DIV 16 /\
    LENGTH(APPEND d (SUB_LIST(0,16 * n DIV 16) (m:byte list))) MOD 16 = 0 /\
    LENGTH(APPEND d (SUB_LIST(0,16 * n DIV 16) (m:byte list))) DIV 16 =
    q + n DIV 16`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `LENGTH(SUB_LIST(0,16 * n DIV 16) (m:byte list)) = 16 * n DIV 16`
    ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST; ASSUME `LENGTH(m:byte list) = n`] THEN
      MP_TAC(SPECL [`n:num`; `16`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN
    REWRITE_TAC[ASSUME `b = 0`; ADD_CLAUSES; GSYM LEFT_ADD_DISTRIB] THEN
    SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; SUB_LIST_CLAUSES;
              num_of_bytelist; WORD_ADD_0] THEN
  SUBGOAL_THEN `LENGTH(d:byte list) = 16 * q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY1305_KACC_SPLIT THEN
  FIRST_ASSUM ACCEPT_TAC;;

(* (B1) b > 0: memcpy(desc + b, src, 16 - b), the one block of the buffer,   *)
(* buflen = 0, then the (b + n - 16) div 16 whole blocks from src + 16 - b,  *)
(* if any, and join1.                                                        *)

let PU_BUF_NORM_TAC =
  let ths = [ASSUME `LENGTH(d:byte list) MOD 16 = b`;
             ASSUME `LENGTH(d:byte list) DIV 16 = q`] in
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) `memory`)) (concl th) then REWRITE_RULE ths th
    else th);;

let PU_B1_ZX_TAC =
  SUBGOAL_THEN `b < 2 EXP 32 /\ 16 - b < 2 EXP 32 /\ b <= 16`
  STRIP_ASSUME_TAC THENL [UNDISCH_TAC `b < 16` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `b:num` WG_WORD_ZX_SMALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(SPEC `b:num` PU_ZX32) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(ISPECL [`16`; `b:num`] (INST_TYPE [`:32`,`:N`] WORD_SUB)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
  MP_TAC(SPEC `16 - b` WG_WORD_ZX_SMALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

let PU_B1_TAC =
  PU_BUF_NORM_TAC THEN
  WG_PC_REWRITE_TAC
   [ASSUME `val(word_zx(word_zx(word b:int32):int64):int32) = b`;
    ASSUME `~(b = 0)`] THEN
  ARM_STEPS_TAC PU_EXEC (13--19) THEN PU_B1_ZX_TAC THEN

  (*** memcpy(desc + b, src, 16 - b) ***)

  MP_TAC(ISPECL [`src:int64`; `m:byte list`; `n:num`; `0`; `16 - b`;
                 `s19:armstate`] WG_READ_BYTES_SUBLIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(b + n <= 15)` THEN ARITH_TAC;
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `val(word(16 - b):int64) = 16 - b` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    ARITH_TAC;
    ALL_TAC] THEN
  WG_PLT_TAC PU_EXEC 19 THEN
  WG_CALL_TAC "memcpy" PU_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `num_of_bytelist(SUB_LIST(0,16 - b) (m:byte list))`; `read X30 s`] 24 THEN
  ARM_STEPS_TAC PU_EXEC (25--30) THEN
  MP_TAC(SPECL [`b:num`; `n:num`; `nbytes:int64`] PU_X19_B1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(b + n <= 15)` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN

  (*** poly1305_core_blocks for the buffer ***)

  MP_TAC(ISPECL [`desc:int64`; `SUB_LIST(16 * q,b) (d:byte list)`;
                 `SUB_LIST(0,16 - b) (m:byte list)`; `16 - b`; `s30:armstate`]
         WG_READ_BYTES_APPEND) THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(16 * q,b) (d:byte list)) = b /\
                LENGTH(SUB_LIST(0,16 - b) (m:byte list)) = 16 - b`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(b + n <= 15)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b + 16 - b = 16 * val(word 1:int64)` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `b < 16` THEN ARITH_TAC;
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
                         ASSUME_TAC(REWRITE_RULE[VAL_WORD_1] th))] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (SUB_LIST(16 * q,b) d) (SUB_LIST(0,16 - b) (m:byte list))) =
    16 * val(word 1:int64)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; VAL_WORD_1] THEN
    UNDISCH_TAC `b < 16` THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC PU_EXEC [31] THEN
  SUBGOAL_THEN
   `poly1305_h_at (word_add desc (word 40))
                  (poly1305_kacc (poly1305_r k) 0 d 1 q) s31 /\
    poly1305_key_at (word_add desc (word 64)) (poly1305_r k) s31`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[poly1305_h_at; poly1305_key_at] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(SPEC `k:byte list` POLY1305_R_BOUND) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 1:int64)`) THEN
  SUBGOAL_THEN `1 < 2 EXP 32` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  PU_BLOCKS_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `APPEND (SUB_LIST(16 * q,b) d) (SUB_LIST(0,16 - b) (m:byte list))`;
    `poly1305_kacc (poly1305_r k) 0 d 1 q`; `poly1305_r k`; `pc:num`;
    `read X30 s`] 32 THEN
  POLY1305_H_GHOST_TAC `s32:armstate` THEN ARM_STEPS_TAC PU_EXEC (33--37) THEN

  (*** The rest of b + n - 16 bytes ***)

  SUBGOAL_THEN `(b + n) - 16 < 2 EXP 32` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`n < 2 EXP 32`; `b < 16`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `(b + n) - 16` PU_ZX32) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  PU_MASK_FACTS_TAC `(b + n) - 16` THEN
  SUBGOAL_THEN
   `rho = ((b + n) - 16) MOD 16 /\
    n - rho = (16 - b) + 16 * ((b + n) - 16) DIV 16 /\
    (16 - b) + 16 * ((b + n) - 16) DIV 16 <= n`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q /\ r) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SYM(ASSUME
        `(if b + n < 16 then n else (b + n) MOD 16) = rho`)] THEN
      SUBGOAL_THEN `~(b + n < 16)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `~(b + n <= 15)` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `b + n = 1 * 16 + ((b + n) - 16)`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
       [UNDISCH_TAC `~(b + n <= 15)` THEN ARITH_TAC;
        REWRITE_TAC[MOD_MULT_ADD]];
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`(b + n) - 16`; `16`] DIVISION) THEN
      REWRITE_TAC[ARITH_EQ] THEN
      MAP_EVERY UNDISCH_TAC [`~(b + n <= 15)`; `b < 16`] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx(word(16 * ((b + n) - 16) DIV 16):int64):int32) =
                16 * ((b + n) - 16) DIV 16` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    SUBGOAL_THEN `16 * ((b + n) - 16) DIV 16 < 2 EXP 64` ASSUME_TAC THENL
     [UNDISCH_TAC `16 * ((b + n) - 16) DIV 16 < 2 EXP 32` THEN ARITH_TAC;
      ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `16 * ((b + n) - 16) DIV 16 = 0` THENL
   [(*** No whole blocks left: join1 ***)

    ARM_STEPS_TAC PU_EXEC [38] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN
     `LENGTH(APPEND d (SUB_LIST(0,16 - b) (m:byte list))) = 16 * (q + 1)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST] THEN
      MAP_EVERY UNDISCH_TAC [`~(b + n <= 15)`; `b < 16`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; SUB_LIST_CLAUSES;
                num_of_bytelist] THEN
    MP_TAC(SPECL [`poly1305_r k`; `d:byte list`; `m:byte list`; `q:num`;
                  `b:num`; `0`] PU_KACC_FILL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; poly1305_kacc] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(b + n <= 15)`; `b < 16`] THEN ARITH_TAC;
      DISCH_THEN(ACCEPT_TAC o SYM)];

    (*** poly1305_core_blocks for the whole blocks, then join1 ***)

    ARM_STEPS_TAC PU_EXEC (38--46) THEN PU_BULK_NORM_TAC `(b + n) - 16` THEN
    MP_TAC(ISPECL [`src:int64`; `m:byte list`; `n:num`; `16 - b`;
                   `16 * ((b + n) - 16) DIV 16`; `s46:armstate`]
           WG_READ_BYTES_SUBLIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `LENGTH(SUB_LIST(16 - b,16 * ((b + n) - 16) DIV 16) (m:byte list)) =
      16 * val(word(((b + n) - 16) DIV 16):int64) /\
      read (memory :> bytes(word_add src (word(16 - b)),
                            16 * val(word(((b + n) - 16) DIV 16):int64))) s46 =
      num_of_bytelist(SUB_LIST(16 - b,16 * ((b + n) - 16) DIV 16) m)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN
      UNDISCH_TAC `16 - b + 16 * ((b + n) - 16) DIV 16 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `poly1305_h_at (word_add desc (word 40))
        (poly1305_kacc (poly1305_r k) (poly1305_kacc (poly1305_r k) 0 d 1 q)
           (APPEND (SUB_LIST (16 * q,b) d) (SUB_LIST (0,16 - b) m)) 1 1) s46 /\
      poly1305_key_at (word_add desc (word 64)) (poly1305_r k) s46`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[poly1305_h_at; poly1305_key_at] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    PU_BLOCKS_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
      `SUB_LIST(16 - b,16 * ((b + n) - 16) DIV 16) (m:byte list)`;
      `poly1305_kacc (poly1305_r k) (poly1305_kacc (poly1305_r k) 0 d 1 q)
         (APPEND (SUB_LIST (16 * q,b) d) (SUB_LIST (0,16 - b) m)) 1 1`;
      `poly1305_r k`; `pc:num`; `read X30 s`] 47 THEN
    POLY1305_H_GHOST_TAC `s47:armstate` THEN ARM_STEPS_TAC PU_EXEC [48] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
    SUBGOAL_THEN
     `LENGTH(APPEND d (SUB_LIST(0,16 - b + 16 * ((b + n) - 16) DIV 16)
                               (m:byte list))) =
      16 * ((q + 1) + ((b + n) - 16) DIV 16)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST] THEN
      MAP_EVERY UNDISCH_TAC [`16 - b + 16 * ((b + n) - 16) DIV 16 <= n`;
                             `b < 16`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; SUB_LIST_CLAUSES;
                num_of_bytelist] THEN
    MP_TAC(SPECL [`poly1305_r k`; `d:byte list`; `m:byte list`; `q:num`;
                  `b:num`; `((b + n) - 16) DIV 16`] PU_KACC_FILL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `b < 16` THEN ARITH_TAC;
      DISCH_THEN(ACCEPT_TAC o SYM)]];;

let PU_ENTRY_TAC =
  PU_ENTRY_SETUP_TAC THEN PU_COND_TAC THEN
  ASM_CASES_TAC `b + n <= 15` THENL
   [PU_PATHA_TAC;
    WG_PC_REWRITE_TAC[ASSUME `~(b + n <= 15)`] THEN
    ARM_STEPS_TAC PU_EXEC [12] THEN PU_VB_TAC THEN
    ASM_CASES_TAC `b = 0` THENL [PU_B0_TAC; PU_B1_TAC]];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  PU_SETUP_TAC THEN
  ABBREV_TAC `rho = if b + n < 16 then n else (b + n) MOD 16` THEN
  ENSURES_SEQUENCE_TAC `pc + poly1305_update_join1` pu_j1 THEN
  CONJ_TAC THENL [PU_ENTRY_TAC; PU_TAIL_TAC]);;

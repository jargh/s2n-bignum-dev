(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of poly1305_final_spec.ml. With b and q the length   *)
(* of d mod and div 16, join1 is reached with the accumulator of RFC 8439    *)
(* (poly1305_acc in common/rfc8439.ml) for all of d: at once if b is 0 (the  *)
(* q whole blocks, poly1305_kacc with the 2^128 bit), and otherwise after    *)
(* the buffer of the last b bytes is padded with a one byte and zeros        *)
(* (memset) and absorbed by poly1305_core_blocks without the 2^128 bit.      *)
(* From join1 poly1305_core_emit adds the s of the key and writes the tag,   *)
(* and memset zeroes the struct.                                             *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/poly1305_final_spec.ml";;

let WIREGUARD_POLY1305_FINAL_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc
  [layout_range "poly1305_final"; layout_range "plt_memset"];;

let PF_EXEC = WIREGUARD_POLY1305_FINAL_GCC13_O2_EXEC;;

let PF_BLOCKS_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,PF_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let PF_EMIT_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,PF_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the kernel's accumulator and the RFC one. They agree on whole     *)
(* blocks; a last partial block of b bytes is the buffer padded with a one   *)
(* byte and zeros, without the 2^128 bit; the tag is the low 128 bits of the *)
(* accumulator plus s.                                                       *)
(* ------------------------------------------------------------------------- *)

let POLY1305_KACC_1 = prove
 (`!r a (m:byte list) hb.
     poly1305_kacc r a m hb 1 =
     ((a + num_of_bytelist(SUB_LIST(0,16) m) + 2 EXP 128 * hb) * r) MOD
     (2 EXP 130 - 5)`,
  REWRITE_TAC[ONE; poly1305_kacc; MULT_CLAUSES]);;

let POLY1305_KACC_ACC = prove
 (`!r (m:byte list) j.
     16 * j <= LENGTH m ==> poly1305_acc r m j = poly1305_kacc r 0 m 1 j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[poly1305_acc; poly1305_kacc; LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [UNDISCH_TAC `16 * SUC j <= LENGTH(m:byte list)` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(16 * j,16) (m:byte list)) = 16`
  SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN
    UNDISCH_TAC `16 * SUC j <= LENGTH(m:byte list)` THEN ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV]);;

let POLY1305_KACC_PAD = prove
 (`!r (d:byte list) q b.
     LENGTH d = 16 * q + b /\ b < 16
     ==> poly1305_acc r d (q + 1) =
         poly1305_kacc r (poly1305_kacc r 0 d 1 q)
           (APPEND (SUB_LIST(16 * q,b) d)
                   (CONS (word 1) (REPLICATE (15 - b) (word 0)))) 0 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ADD1; poly1305_acc; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[POLY1305_KACC_1; MULT_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`r:num`; `d:byte list`; `q:num`] POLY1305_KACC_ACC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `SUB_LIST(16 * q,16) (d:byte list) = SUB_LIST(16 * q,b) d`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`d:byte list`; `b:num`; `16 - b`; `16 * q`]
           SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE `b < 16 ==> b + 16 - b = 16`] THEN
    DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM APPEND_NIL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(16 * q,b) (d:byte list)) = b` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `SUB_LIST(0,16) (APPEND (SUB_LIST(16 * q,b) d)
                   (CONS (word 1) (REPLICATE (15 - b) (word 0)))) =
    APPEND (SUB_LIST(16 * q,b) (d:byte list))
           (CONS (word 1) (REPLICATE (15 - b) (word 0)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUB_LIST_REFL THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_REPLICATE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[WG_NUM_OF_BYTELIST_APPEND; num_of_bytelist;
                  NUM_OF_BYTELIST_REPLICATE_0] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let POLY1305_TAG = prove
 (`!k (d:byte list) a.
     poly1305_acc (poly1305_r k) d ((LENGTH d + 15) DIV 16) = a
     ==> num_of_bytelist(poly1305 k d) =
         (a + num_of_bytelist(SUB_LIST(16,16) k)) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[poly1305; NUM_OF_BYTELIST_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the nonce s at desc + 20 is not NULL, and the padded buffer.      *)
(* ------------------------------------------------------------------------- *)

let PF_NONCE_NZ = prove
 (`!desc:int64. nonoverlapping (desc,280) (word 0:int64,1)
                ==> ~(word_add desc (word 20) = word 0)`,
  GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_0; VAL_WORD;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`20`; `0`] THEN
  ASM_REWRITE_TAC[CONG; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let PF_BUF_LEMMA = prove
 (`!a:int64 (l:byte list) b s.
     LENGTH l = b /\ b < 16 /\
     read (memory :> bytes(a,b)) s = num_of_bytelist l /\
     read (memory :> bytes8(word_add a (word b))) s = word 1 /\
     read (memory :> bytes(word_add a (word(b + 1)),15 - b)) s = 0
     ==> read (memory :> bytes(a,16)) s =
         num_of_bytelist
          (APPEND l (CONS (word 1) (REPLICATE (15 - b) (word 0))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `16 = b + 1 + (15 - b)` SUBST1_TAC THENL
   [UNDISCH_TAC `b < 16` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_REWRITE_TAC[WG_NUM_OF_BYTELIST_APPEND; num_of_bytelist;
                  NUM_OF_BYTELIST_REPLICATE_0] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The setup, and the state at join1 with the accumulator for all of d.      *)
(* ------------------------------------------------------------------------- *)

let PF_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`desc:int64`; `dst:int64`; `k:byte list`; `d:byte list`; `mset:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 48 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(MATCH_MP PF_NONCE_NZ (find (can (term_match []
      `nonoverlapping (x:int64,280) (word 0:int64,1)`) o concl)
      (CONJUNCTS th))) THEN
    MP_TAC th) THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "memset" o REWRITE_RULE[memset_contract])
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30`;;

let pf_j1 =
 `\s. read SP s = stackpointer /\ read X29 s = stackpointer /\
      read X19 s = desc /\ read X20 s = dst /\
      read X21 s = word_add desc (word 40) /\
      read (memory :> bytes64 stackpointer) s = x29_init /\
      read (memory :> bytes64 (word_add stackpointer (word 8))) s =
        returnaddress /\
      read (memory :> bytes64 (word_add stackpointer (word 16))) s =
        x19_init /\
      read (memory :> bytes64 (word_add stackpointer (word 24))) s =
        x20_init /\
      read (memory :> bytes64 (word_add stackpointer (word 32))) s =
        x21_init /\
      read (memory :> bytes64 (word_add (word pc) (word 37016))) s = mset /\
      read (memory :> bytes (ea,el)) s = ev /\
      read (memory :> bytes (word_add desc (word 20),16)) s =
        num_of_bytelist(SUB_LIST(16,16) k) /\
      poly1305_h_at (word_add desc (word 40))
        (poly1305_acc (poly1305_r k) d ((LENGTH d + 15) DIV 16)) s`;;

(* ------------------------------------------------------------------------- *)
(* From the entry to join1: the test of buflen = b.                          *)
(* ------------------------------------------------------------------------- *)

let PF_ENTRY_SETUP_TAC =
  REWRITE_TAC[poly1305_desc_at; poly1305_h_at; poly1305_key_at] THEN
  ABBREV_TAC `b = LENGTH(d:byte list) MOD 16` THEN
  ABBREV_TAC `q = LENGTH(d:byte list) DIV 16` THEN
  GHOST_INTRO_TAC `h0w:int64`
   `read (memory :> bytes64 (word_add desc (word 40)))` THEN
  GHOST_INTRO_TAC `h1w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 8)))` THEN
  GHOST_INTRO_TAC `h2w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 16)))` THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `b < 16 /\ LENGTH(d:byte list) = 16 * q + b`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `LENGTH(d:byte list) MOD 16 = b`);
                  MOD_LT_EQ; ARITH_EQ];
      MP_TAC(SPECL [`LENGTH(d:byte list)`; `16`] DIVISION) THEN
      REWRITE_TAC[ARITH_EQ; ASSUME `LENGTH(d:byte list) DIV 16 = q`;
                  ASSUME `LENGTH(d:byte list) MOD 16 = b`] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  ARM_STEPS_TAC PF_EXEC (1--9) THEN
  SUBGOAL_THEN `val(word_zx(word_zx(word b:int32):int64):int32) = b`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    SUBGOAL_THEN `b < 2 EXP 32 /\ b < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `b < 16` THEN ARITH_TAC; ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC];;

(* b = 0: the q whole blocks.                                                *)

let PF_B0_TAC =
  SUBGOAL_THEN
   `poly1305_acc (poly1305_r k) d (((16 * q + b) + 15) DIV 16) =
    poly1305_kacc (poly1305_r k) 0 d 1 q`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `((16 * q + b) + 15) DIV 16 = q` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `15` THEN
      UNDISCH_TAC `b = 0` THEN ARITH_TAC;
      MATCH_MP_TAC POLY1305_KACC_ACC THEN
      UNDISCH_TAC `LENGTH(d:byte list) = 16 * q + b` THEN ARITH_TAC];
    ALL_TAC] THEN
  WG_PC_REWRITE_TAC
   [ASSUME `val(word_zx(word_zx(word b:int32):int64):int32) = b`;
    ASSUME `b = 0`] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[poly1305_h_at];;

(* b > 0: buf[b] = 1 and buflen = b + 1, memset(desc + b + 1, 0, 15 - b),    *)
(* and the buffer as one block without the 2^128 bit.                        *)

let PF_B1_NORM_TAC =
  SUBGOAL_THEN `b + 1 < 2 EXP 32 /\ 15 - b < 2 EXP 32 /\ b + 1 <= 16 /\
                16 - (b + 1) = 15 - b`
  STRIP_ASSUME_TAC THENL [UNDISCH_TAC `b < 16` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WG_WORD_ZX_ZX]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(INST_TYPE [`:32`,`:N`] WORD_ADD)]) THEN
  MP_TAC(ISPECL [`16`; `b + 1`] (INST_TYPE [`:32`,`:N`] WG_WORD_SUB_LE)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(SPEC `b + 1` WG_WORD_ZX_SMALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(SPEC `15 - b` WG_WORD_ZX_SMALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

let pf_buf_tm =
 `APPEND (SUB_LIST(16 * q,b) d)
         (CONS (word 1) (REPLICATE (15 - b) (word 0))):byte list`;;

let PF_B1_TAC =
  WG_PC_REWRITE_TAC
   [ASSUME `val(word_zx(word_zx(word b:int32):int64):int32) = b`;
    ASSUME `~(b = 0)`] THEN
  ARM_STEPS_TAC PF_EXEC (10--18) THEN PF_B1_NORM_TAC THEN

  (*** memset(desc + b + 1, 0, 15 - b) ***)

  MP_TAC(SPEC `15 - b` WG_VAL_WORD_SMALL) THEN ANTS_TAC THENL
   [UNDISCH_TAC `b < 16` THEN ARITH_TAC; DISCH_TAC] THEN
  WG_PLT_TAC PF_EXEC 18 THEN
  WG_CALL_TAC "memset" PF_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 23 THEN
  MEMSET_ZERO_BYTES_TAC THEN

  (*** poly1305_core_blocks for the padded buffer ***)

  MP_TAC(ISPECL [`desc:int64`; `SUB_LIST(16 * q,b) (d:byte list)`; `b:num`;
                 `s23:armstate`] PF_BUF_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN
    UNDISCH_TAC `LENGTH(d:byte list) = 16 * q + b` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   (subst [pf_buf_tm,`l:byte list`]
     `read (memory :> bytes(desc,16 * val(word 1:int64))) s23 =
      num_of_bytelist l /\
      read (memory :> bytes(desc,16 * 1)) s23 = num_of_bytelist l /\
      LENGTH(l:byte list) = 16 * val(word 1:int64)`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_1; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_REPLICATE; LENGTH_SUB_LIST] THEN
    MAP_EVERY UNDISCH_TAC [`LENGTH(d:byte list) = 16 * q + b`; `b < 16`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC PF_EXEC (24--29) THEN
  SUBGOAL_THEN
   `poly1305_h_at (word_add desc (word 40))
                  (poly1305_kacc (poly1305_r k) 0 d 1 q) s29 /\
    poly1305_key_at (word_add desc (word 64)) (poly1305_r k) s29`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[poly1305_h_at; poly1305_key_at] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(SPEC `k:byte list` POLY1305_R_BOUND) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 1:int64)`) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 0:int64)`) THEN
  SUBGOAL_THEN `1 < 2 EXP 32` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  PF_BLOCKS_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    pf_buf_tm; `poly1305_kacc (poly1305_r k) 0 d 1 q`; `poly1305_r k`;
    `pc:num`; `read X30 s`] 30 THEN

  (*** join1, the accumulator being the RFC one ***)

  POLY1305_H_GHOST_TAC `s30:armstate` THEN ARM_STEPS_TAC PF_EXEC [31] THEN
  SUBGOAL_THEN
   (subst [pf_buf_tm,`l:byte list`]
     `poly1305_acc (poly1305_r k) d (((16 * q + b) + 15) DIV 16) =
      poly1305_kacc (poly1305_r k) (poly1305_kacc (poly1305_r k) 0 d 1 q)
                    l 0 1`)
  SUBST1_TAC THENL
   [SUBGOAL_THEN `((16 * q + b) + 15) DIV 16 = q + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `b - 1` THEN
      MAP_EVERY UNDISCH_TAC [`~(b = 0)`; `b < 16`] THEN ARITH_TAC;
      MATCH_MP_TAC POLY1305_KACC_PAD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[poly1305_h_at];;

(* ------------------------------------------------------------------------- *)
(* From join1: poly1305_core_emit and memset(desc, 0, 280).                  *)
(* ------------------------------------------------------------------------- *)

let PF_TAIL_TAC =
  ABBREV_TAC `a = poly1305_acc (poly1305_r k) d ((LENGTH d + 15) DIV 16)` THEN
  REWRITE_TAC[poly1305_h_at] THEN
  GHOST_INTRO_TAC `h0w:int64`
   `read (memory :> bytes64 (word_add desc (word 40)))` THEN
  GHOST_INTRO_TAC `h1w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 8)))` THEN
  GHOST_INTRO_TAC `h2w:int64`
   `read (memory :> bytes64
           (word_add (word_add desc (word 40)) (word 16)))` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC PF_EXEC (1--4) THEN
  SUBGOAL_THEN `poly1305_h_at (word_add desc (word 40)) a s4 /\
                LENGTH(SUB_LIST(16,16) (k:byte list)) = 16`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[poly1305_h_at; LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  PF_EMIT_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `a:num`;
    `SUB_LIST(16,16) (k:byte list)`; `pc:num`; `read X30 s`] 5 THEN
  ARM_STEPS_TAC PF_EXEC (6--9) THEN WG_PLT_TAC PF_EXEC 9 THEN
  WG_CALL_TAC "memset" PF_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 14 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  ARM_STEPS_TAC PF_EXEC (15--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY1305_TAG THEN
  FIRST_ASSUM ACCEPT_TAC;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  PF_SETUP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + poly1305_final_join1` pf_j1 THEN
  CONJ_TAC THENL
   [PF_ENTRY_SETUP_TAC THEN ASM_CASES_TAC `b = 0` THENL
     [PF_B0_TAC; PF_B1_TAC];
    PF_TAIL_TAC]);;

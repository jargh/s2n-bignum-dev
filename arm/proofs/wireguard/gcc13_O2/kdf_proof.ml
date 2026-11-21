(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of kdf_spec.ml: a simulation of the four paths       *)
(* (NULL first destination, then the tests for the second and third), the    *)
(* calls of hmac being simulated with its theorem. The secret is at          *)
(* stackpointer + 735 and the output buffer (33 bytes) at stackpointer + 767 *)
(* (unaligned: gcc packs the byte arrays).                                   *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/kdf_spec.ml";;

let WIREGUARD_KDF_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "kdf"];;

let KDF_HMAC_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,WIREGUARD_KDF_GCC13_O2_EXEC,0,
   wireguard_gcc13_O2_mc,WIREGUARD_HMAC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let kdf_hmac_args kb m =
  [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; kb; m;
   `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
   `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

(* The outputs t1, t2, t3, and the inputs of the HMACs for t2 and t3.        *)

let kdf_append_byte t c =
  mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,t),
          mk_list([mk_comb(`word:num->byte`,mk_small_numeral c)],`:byte`));;

let kdf_t1_tm = `wg_hmac (wg_hmac ckb db) [word 1]`;;
let kdf_m2_tm = kdf_append_byte kdf_t1_tm 2;;
let kdf_t2_tm = mk_comb(`wg_hmac (wg_hmac ckb db)`,kdf_m2_tm);;
let kdf_m3_tm = kdf_append_byte kdf_t2_tm 3;;

(* The 33 bytes at a in state s as the output t and the byte c stored after  *)
(* it, with the length facts for the HMAC of them.                           *)

let KDF_INPUT_TAC t c a s =
  let m = kdf_append_byte t c in
  SUBGOAL_THEN
   (vsubst [a,`a:int64`; s,`s:armstate`; m,`m:byte list`]
      `read (memory :> bytes(a,33)) s = num_of_bytelist m`)
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [a; t; rand m; `1`; s] WG_READ_BYTES_APPEND) THEN
    REWRITE_TAC[LENGTH_WG_HMAC] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC WG_ADDR_CONV THEN
      REWRITE_TAC[READ_MEMORY_BYTES_BYTES8; num_of_bytelist] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,m),`33`)) ASSUME_TAC
  THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_WG_HMAC; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 33:int64)`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 33 < 2 EXP 64`);;

(* The postcondition at the end of each path, after the zeroing of the       *)
(* secret and the output buffer: the outputs written are put together from   *)
(* their 64-bit words, the others are excluded by the cases.                 *)

let KDF_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WG_KDF_T_CLAUSES] THEN
  REPEAT CONJ_TAC THEN WG_BYTES32_OF_WORDS_TAC[LENGTH_WG_HMAC];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_KDF_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_KDF_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`d1:int64`; `d2:int64`; `d3:int64`; `data:int64`; `len2:int64`;
    `len3:int64`; `datalen:int64`; `ck:int64`; `db:byte list`;
    `ckb:byte list`; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 800 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            (19--29) THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 640):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The secret, the HMAC of the data with the chaining key ***)

  ARM_STEPS_TAC EXEC (1--24) THEN
  KDF_HMAC_TAC (kdf_hmac_args `ckb:byte list` `db:byte list`) 25 THEN
  ARM_STEPS_TAC EXEC [26] THEN
  ASM_CASES_TAC `val(d1:int64) = 0` THENL
   [WG_PC_REWRITE_TAC[ASSUME `val(d1:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (27--38) THEN KDF_FINAL_TAC;
    WG_PC_REWRITE_TAC[ASSUME `~(val(d1:int64) = 0)`]] THEN

  (*** The first output, the HMAC of 0x1 with the secret ***)

  ARM_STEPS_TAC EXEC (27--33) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 767),1)) s33 =
    num_of_bytelist [word 1:byte]`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_BYTES_BYTES8; num_of_bytelist] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 1:int64)`) THEN
  ASSUME_TAC(ISPECL [`ckb:byte list`; `db:byte list`] LENGTH_WG_HMAC) THEN
  ASSUME_TAC(LENGTH_CONV `LENGTH [word 1:byte]`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 1 < 2 EXP 64`) THEN
  KDF_HMAC_TAC (kdf_hmac_args `wg_hmac ckb db` `[word 1:byte]`) 34 THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 767):int64`
    `s34:armstate` THEN
  ARM_STEPS_TAC EXEC (35--42) THEN
  WG_PC_REWRITE_TAC[WORD_SUB_0] THEN
  ASM_CASES_TAC `val(d2:int64) = 0` THENL
   [WG_PC_REWRITE_TAC[ASSUME `val(d2:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (43--54) THEN KDF_FINAL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `val(len2:int64) = 0` THENL
   [WG_PC_REWRITE_TAC[ASSUME `~(val(d2:int64) = 0)`;
                      ASSUME `val(len2:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (43--54) THEN KDF_FINAL_TAC;
    ALL_TAC] THEN
  WG_PC_REWRITE_TAC[ASSUME `~(val(d2:int64) = 0)`;
                    ASSUME `~(val(len2:int64) = 0)`] THEN
  UNDISCH_TAC `val(len2:int64) = 0 \/ val len2 = 32` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  WG_NONOVERLAP_RULE_TAC[ASSUME `val(len2:int64) = 32`] THEN

  (*** The second output, the HMAC of t1 and 0x2 ***)

  ARM_STEPS_TAC EXEC (43--49) THEN
  KDF_INPUT_TAC kdf_t1_tm 2 `word_add stackpointer (word 767):int64`
    `s49:armstate` THEN
  KDF_HMAC_TAC (kdf_hmac_args `wg_hmac ckb db` kdf_m2_tm) 50 THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 767):int64`
    `s50:armstate` THEN
  ARM_STEPS_TAC EXEC (51--58) THEN
  WG_PC_REWRITE_TAC[WORD_SUB_0] THEN
  ASM_CASES_TAC `val(d3:int64) = 0` THENL
   [WG_PC_REWRITE_TAC[ASSUME `val(d3:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (59--70) THEN KDF_FINAL_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `val(len3:int64) = 0` THENL
   [WG_PC_REWRITE_TAC[ASSUME `~(val(d3:int64) = 0)`;
                      ASSUME `val(len3:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (59--70) THEN KDF_FINAL_TAC;
    ALL_TAC] THEN
  WG_PC_REWRITE_TAC[ASSUME `~(val(d3:int64) = 0)`;
                    ASSUME `~(val(len3:int64) = 0)`] THEN
  UNDISCH_TAC `val(len3:int64) = 0 \/ val len3 = 32` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  WG_NONOVERLAP_RULE_TAC[ASSUME `val(len3:int64) = 32`] THEN

  (*** The third output, the HMAC of t2 and 0x3 ***)

  ARM_STEPS_TAC EXEC (59--65) THEN
  KDF_INPUT_TAC kdf_t2_tm 3 `word_add stackpointer (word 767):int64`
    `s65:armstate` THEN
  KDF_HMAC_TAC (kdf_hmac_args `wg_hmac ckb db` kdf_m3_tm) 66 THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 767):int64`
    `s66:armstate` THEN
  ARM_STEPS_TAC EXEC (67--84) THEN KDF_FINAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* With no second output: the first part of the proof above, and the path    *)
(* of the test of d2.                                                        *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_KDF_D1_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_KDF_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`d1:int64`; `d3:int64`; `data:int64`; `len2:int64`;
    `len3:int64`; `datalen:int64`; `ck:int64`; `db:byte list`;
    `ckb:byte list`; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 800 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            (19--29) THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 640):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--24) THEN
  KDF_HMAC_TAC (kdf_hmac_args `ckb:byte list` `db:byte list`) 25 THEN
  ARM_STEPS_TAC EXEC [26] THEN
  ASM_CASES_TAC `val(d1:int64) = 0` THENL
   [WG_PC_REWRITE_TAC[ASSUME `val(d1:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC (27--38) THEN KDF_FINAL_TAC;
    WG_PC_REWRITE_TAC[ASSUME `~(val(d1:int64) = 0)`]] THEN
  ARM_STEPS_TAC EXEC (27--33) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add stackpointer (word 767),1)) s33 =
    num_of_bytelist [word 1:byte]`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_BYTES_BYTES8; num_of_bytelist] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 1:int64)`) THEN
  ASSUME_TAC(ISPECL [`ckb:byte list`; `db:byte list`] LENGTH_WG_HMAC) THEN
  ASSUME_TAC(LENGTH_CONV `LENGTH [word 1:byte]`) THEN
  ASSUME_TAC(ARITH_RULE `64 + 1 < 2 EXP 64`) THEN
  KDF_HMAC_TAC (kdf_hmac_args `wg_hmac ckb db` `[word 1:byte]`) 34 THEN
  WG_BYTES32_WORDS_TAC `word_add stackpointer (word 767):int64`
    `s34:armstate` THEN
  ARM_STEPS_TAC EXEC (35--42) THEN
  WG_PC_REWRITE_TAC[WORD_SUB_0; VAL_WORD_0] THEN
  ARM_STEPS_TAC EXEC (43--54) THEN KDF_FINAL_TAC);;

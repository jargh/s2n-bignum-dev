(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of cookie_add_mac_to_packet_spec.ml: mac1 by the     *)
(* keyed blake2s (blake2s_constprop_0_2, simulated with its theorem) under   *)
(* down_write, its copy into the cookie 64 bits at a time, then under        *)
(* down_read either mac2 by the keyed blake2s or zero, on three paths: an    *)
(* invalid cookie, an expired one (the signed comparison of the time with    *)
(* the birthdate plus 115 seconds) and a fresh one. The length of the        *)
(* message before the MACs is named n.                                       *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/cookie_add_mac_to_packet_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_cookie_add_mac_to_packet"; layout_range "plt_down_write";
    layout_range "plt_up_write"; layout_range "plt_down_read";
    layout_range "plt_up_read";
    layout_range "plt_ktime_get_coarse_with_offset"];;

let AM_EXEC = WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_EXEC;;

let AM_MAC_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,AM_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let am_got =
  [`got_memset:num`; `got_memcpy:num`; `got_down_write:num`;
   `got_up_write:num`; `got_down_read:num`; `got_up_read:num`;
   `got_ktime_get_coarse_with_offset:num`];;

let am_mac_args kb mb =
  [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; kb; mb;
   `mset:int64`; `ea:int64`; `el:num`; `ev:num`;
   `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
   `read SP s`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* The setup, and mac1 (named m1) under down_write.                          *)
(* ------------------------------------------------------------------------- *)

let AM_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`msg:int64`; `len:int64`; `peer:int64`; `mb:byte list`; `mk:byte list`;
    `ck:byte list`; `valid:bool`; `bd:int64`; `mset:int64`; `mcpy:int64`;
    `dwr:int64`; `uwr:int64`; `drd:int64`; `urd:int64`; `ktc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4160 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  WG_LABEL_CONTRACTS_TAC
   [`rwsem_contract dwr ea el ev`,"down_write";
    `rwsem_contract uwr ea el ev`,"up_write";
    `rwsem_contract drd ea el ev`,"down_read";
    `rwsem_contract urd ea el ev`,"up_read";
    `ktime_get_coarse_with_offset_contract ktc ea el ev`,"ktime"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) am_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4096):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) am_got;;

let AM_MAC1_TAC =
  ARM_STEPS_TAC AM_EXEC (1--13) THEN WG_PLT_TAC AM_EXEC 13 THEN
  WG_CALL_TAC "down_write" AM_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 18 THEN
  ARM_STEPS_TAC AM_EXEC (19--24) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WG_WORD_SUB_VAL
     (ASSUME `32 <= val(len:int64)`)]) THEN
  ABBREV_TAC `n = val(len:int64) - 32` THEN
  SUBGOAL_THEN `n + 64 < 2 EXP 64 /\ n + 32 = val(len:int64)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(MP (SPEC `n:num` WG_VAL_WORD_SMALL)
                (ARITH_RULE `n + 64 < 2 EXP 64 ==> n < 2 EXP 64`
                 |> C MP (ASSUME `n + 64 < 2 EXP 64`))) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  AM_MAC_TAC (am_mac_args `mk:byte list` `mb:byte list`) 25 THEN
  ABBREV_TAC `m1 = blake2s mk 16 mb` THEN
  SUBGOAL_THEN `LENGTH(m1:byte list) = 16` ASSUME_TAC THENL
   [EXPAND_TAC "m1" THEN REWRITE_TAC[LENGTH_BLAKE2S] THEN ARITH_TAC;
    ALL_TAC];;

(* The copy of mac1 into the cookie, and the locks.                          *)

let AM_COPY_TAC =
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`word_add msg (word n):int64`; `m1:byte list`; `16`;
                  mk_small_numeral k; `s25:armstate`]
                 WG_READ_BYTES64_BYTELIST) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV WG_ADDR_CONV) THEN DISCH_TAC)
   [0; 8] THEN
  ARM_STEPS_TAC AM_EXEC (26--32) THEN
  MP_TAC(ISPECL [`word_add peer (word 706):int64`;
                 `SUB_LIST(0,8) (m1:byte list)`;
                 `SUB_LIST(8,8) (m1:byte list)`;
                 `s32:armstate`] WG_READ_BYTES_16_OF_CHUNKS) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WG_ADDR_CONV)) THEN
  ASM_SIMP_TAC[WG_SUB_LIST_HALVES_16] THEN DISCH_TAC THEN
  WG_PLT_TAC AM_EXEC 32 THEN
  WG_CALL_TAC "up_write" AM_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 37 THEN
  ARM_STEPS_TAC AM_EXEC (38--39) THEN WG_PLT_TAC AM_EXEC 39 THEN
  WG_CALL_TAC "down_read" AM_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] 44 THEN
  ARM_STEPS_TAC AM_EXEC (45--46);;

(* ------------------------------------------------------------------------- *)
(* The three paths for mac2, each ending with up_read (at step n + 5 from    *)
(* the bl at step n) and the return.                                         *)
(* ------------------------------------------------------------------------- *)

let AM_TAIL_TAC n =
  WG_PLT_TAC AM_EXEC n THEN
  WG_CALL_TAC "up_read" AM_EXEC
   [`read X0 s`; `read SP s`; `read X30 s`] (n+5) THEN
  ARM_STEPS_TAC AM_EXEC ((n+6)--(n+10)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `val(len:int64) - 16 = n + 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[wg_mac];;

let AM_INVALID_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~valid`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  ARM_STEPS_TAC AM_EXEC (47--49) THEN AM_TAIL_TAC 49 THEN WG_ZERO_BYTES_TAC;;

let am_fresh =
  `ival(now:int64) < ival(word_add bd (word 115000000000):int64)`;;

let AM_TIME_TAC =
  WG_PC_REWRITE_TAC [ASSUME `valid:bool`] THEN
  WG_PC_CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[]) THEN
  ARM_STEPS_TAC AM_EXEC (47--53) THEN WG_PLT_TAC AM_EXEC 53 THEN
  WG_CALL_TAC "ktime" AM_EXEC [`read X0 s`; `read SP s`; `read X30 s`] 58 THEN
  ABBREV_TAC `now = read X0 s58` THEN
  ARM_STEPS_TAC AM_EXEC (59--60);;

let AM_EXPIRED_TAC =
  WG_PC_REWRITE_TAC [WG_IVAL_GT_FLAGS; ASSUME (mk_neg am_fresh)] THEN
  ARM_STEPS_TAC AM_EXEC (61--63) THEN AM_TAIL_TAC 63 THEN
  EXISTS_TAC `now:int64` THEN ASM_REWRITE_TAC[] THEN WG_ZERO_BYTES_TAC;;

let AM_FRESH_TAC =
  WG_PC_REWRITE_TAC [WG_IVAL_GT_FLAGS; ASSUME am_fresh] THEN
  ARM_STEPS_TAC AM_EXEC (61--66) THEN
  SUBGOAL_THEN `word_sub len (word 16):int64 = word(n + 16)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`len:int64`; `16`] WG_WORD_SUB_VAL) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  WG_REG_REWRITE_TAC `X3`
    [ASSUME `word_sub len (word 16):int64 = word(n + 16)`] THEN
  WG_REG_REWRITE_TAC `X0` [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  SUBGOAL_THEN `read (memory :> bytes(msg,n + 16)) s66 =
                num_of_bytelist(APPEND mb m1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`msg:int64`; `mb:byte list`; `m1:byte list`; `16`;
                   `s66:armstate`] WG_READ_BYTES_APPEND) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(APPEND mb m1:byte list) = n + 16 /\
                (n + 16) + 64 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASSUME_TAC(MP (SPEC `n + 16` WG_VAL_WORD_SMALL)
                (ARITH_RULE `(n + 16) + 64 < 2 EXP 64 ==> n + 16 < 2 EXP 64`
                 |> C MP (ASSUME `(n + 16) + 64 < 2 EXP 64`))) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 16:int64)`) THEN
  AM_MAC_TAC (am_mac_args `ck:byte list` `APPEND mb m1:byte list`) 67 THEN
  ARM_STEPS_TAC AM_EXEC (68--69) THEN AM_TAIL_TAC 69 THEN
  EXISTS_TAC `now:int64` THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_COOKIE_ADD_MAC_TO_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  AM_SETUP_TAC THEN AM_MAC1_TAC THEN AM_COPY_TAC THEN
  ASM_CASES_TAC `valid:bool` THENL [ALL_TAC; AM_INVALID_TAC] THEN
  AM_TIME_TAC THEN
  ASM_CASES_TAC am_fresh THENL [AM_FRESH_TAC; AM_EXPIRED_TAC]);;

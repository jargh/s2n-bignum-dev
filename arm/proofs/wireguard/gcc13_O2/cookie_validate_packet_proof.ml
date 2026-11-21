(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of cookie_validate_packet_spec.ml: mac1 by the keyed *)
(* blake2s (blake2s_constprop_0_2) and its comparison by crypto_memneq; then *)
(* (if check_cookie) make_cookie, mac2 and its comparison, and               *)
(* wg_ratelimiter_allow from its contract: five paths. The length of the     *)
(* message before the MACs is named n.                                       *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/cookie_validate_packet_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_cookie_validate_packet";
    layout_range "plt_wg_ratelimiter_allow"];;

let VP_EXEC = WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_EXEC;;

let VP_MAC_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,VP_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_BLAKE2S_CONSTPROP_0_2_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let VP_MEMNEQ_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,VP_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let VP_COOKIE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,VP_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_MAKE_COOKIE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let vp_got =
  [`got_memset:num`; `got_memcpy:num`; `got_down_write:num`;
   `got_up_write:num`; `got_down_read:num`; `got_up_read:num`;
   `got_ktime_get_coarse_with_offset:num`; `got_get_random_bytes:num`;
   `got_wg_ratelimiter_allow:num`];;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the test of check_cookie and the result of the rate limiter.      *)
(* ------------------------------------------------------------------------- *)

let VP_CHECK_BIT = prove
 (`!cc:int64 b.
     word_and cc (word 255) = (if b then word 1 else word 0)
     ==> (bit 0 (word_zx(word_zx(word_and ((word_zx:int64->int32) cc)
                                          (word 255)):int64):int32) <=> b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `bit 0 (word_zx(word_zx(word_and ((word_zx:int64->int32) cc)
                                    (word 255)):int64):int32) <=>
    bit 0 (word_and (cc:int64) (word 255))` SUBST1_TAC THENL
   [BITBLAST_TAC; ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

let VP_RL_RESULT = prove
 (`!rl:int64 b.
     word_and rl (word 255) = (if b then word 1 else word 0)
     ==> word_zx(word_add (word_zx(word_zx(word_and ((word_zx:int64->int32) rl)
                                                    (word 255)):int64):int32)
                          (word 2)):int64 =
         (if b then word 3 else word 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word_and ((word_zx:int64->int32) rl)
                             (word 255)):int64):int32 =
    word_zx(word_and (rl:int64) (word 255))` SUBST1_TAC THENL
   [BITBLAST_TAC; ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

(* The MAC computed at s (16 bytes at stackpointer + 4336, mac) compared by  *)
(* crypto_memneq at step k with the 16 bytes of the message sub: the result  *)
(* X0 in s is 0 just when they are equal.                                    *)

let VP_COMPARE_TAC mac sub k =
  let len16 t = mk_eq(mk_comb(`LENGTH:byte list->num`,t),`16`) in
  let sk = mk_var("s"^string_of_int k,`:armstate`) in
  VP_MEMNEQ_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; mk_comb(`num_of_bytelist`,mac);
    mk_comb(`num_of_bytelist`,sub); `pc:num`; `read X30 s`] k THEN
  SUBGOAL_THEN (len16 mac) ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_BLAKE2S] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term ((=) sk)) (concl th) &&
       can (find_term ((=) mac)) (concl th)
    then REWRITE_RULE[MATCH_MP WG_NUM_OF_BYTELIST_EQ
           (TRANS (ASSUME (len16 mac)) (SYM(ASSUME (len16 sub))))] th
    else th);;

(* A case assumption c used for the other assumptions only.                  *)

let VP_USE_TAC c =
  RULE_ASSUM_TAC(fun th ->
    if concl th = c then th else REWRITE_RULE[ASSUME c] th);;

let vp_mac1 = `blake2s mk 16 (SUB_LIST(0,n) msg)`;;

let vp_mac1ok = mk_eq(vp_mac1,`SUB_LIST(n,16) (msg:byte list)`);;

let vp_ck = `wg_mac sec' (wg_cookie_data proto a4 a6 port)`;;

let vp_mac2 = mk_comb(mk_comb(mk_comb(`blake2s`,vp_ck),`16`),
                      `SUB_LIST(0,n + 16) (msg:byte list)`);;

let vp_mac2ok = mk_eq(vp_mac2,`SUB_LIST(n + 16,16) (msg:byte list)`);;

(* ------------------------------------------------------------------------- *)
(* The setup and mac1, compared.                                             *)
(* ------------------------------------------------------------------------- *)

let VP_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`checker:int64`; `skb:int64`; `cc:int64`; `check:bool`; `len:int32`;
    `data:int64`; `msg:byte list`; `mk:byte list`; `proto:int16`;
    `th:int16`; `nh:int16`; `head:int64`; `sec:byte list`; `bd:int64`;
    `a4:byte list`; `a6:byte list`; `port:byte list`; `mset:int64`;
    `mcpy:int64`; `dwr:int64`; `uwr:int64`; `drd:int64`; `urd:int64`;
    `ktc:int64`; `grb:int64`; `rla:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4368 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `wg_ratelimiter_allow_contract f a b c`) (concl th)
    then LABEL_TAC "ratelimiter"
           (REWRITE_RULE[wg_ratelimiter_allow_contract] th)
    else NO_TAC) THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) vp_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4288):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) vp_got;;

let VP_MAC1_TAC =
  ARM_STEPS_TAC VP_EXEC (1--17) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WG_LEN32_SUB
    (ASSUME `32 <= val(len:int32)`)]) THEN
  ABBREV_TAC `n = val(len:int32) - 32` THEN
  SUBGOAL_THEN `n + 32 = val(len:int32) /\ n + 64 < 2 EXP 64 /\
                n < 2 EXP 64 /\ (n + 16) + 64 < 2 EXP 64 /\
                n + 16 < 2 EXP 64 /\ val(len:int32) - 16 = n + 16`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `len:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun (i,k) ->
    MP_TAC(SPECL [`data:int64`; `msg:byte list`; `val(len:int32)`; i; k;
                  `s17:armstate`] WG_READ_BYTES_SUBLIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
   [`0`,`n:num`; `n:num`,`16`; `0`,`n + 16`; `n + 16`,`16`] THEN
  ASSUME_TAC(MP (SPEC `n:num` WG_VAL_WORD_SMALL) (ASSUME `n < 2 EXP 64`)) THEN
  ASSUME_TAC(MP (SPEC `n + 16` WG_VAL_WORD_SMALL)
                (ASSUME `n + 16 < 2 EXP 64`)) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 32:int64)`) THEN
  ASSUME_TAC(WORD_REDUCE_CONV `val(word 16:int64)`) THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,n) (msg:byte list)) = n /\
                LENGTH(SUB_LIST(n,16) (msg:byte list)) = 16 /\
                LENGTH(SUB_LIST(0,n + 16) (msg:byte list)) = n + 16 /\
                LENGTH(SUB_LIST(n + 16,16) (msg:byte list)) = 16`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  VP_MAC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mk:byte list`; `SUB_LIST(0,n) (msg:byte list)`; `mset:int64`;
    `ea:int64`; `el:num`; `ev:num`; `mcpy:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 18 THEN
  ARM_STEPS_TAC VP_EXEC (19--22) THEN
  VP_COMPARE_TAC vp_mac1 `SUB_LIST(n,16) (msg:byte list)` 23;;

(* ------------------------------------------------------------------------- *)
(* The five paths, to the final states, with the result as in the spec.      *)
(* ------------------------------------------------------------------------- *)

(* A comparison that fails: its result (X0 at step k, named r) is not 0, so  *)
(* the cbnz is taken.                                                        *)

let VP_TAKEN_TAC c k =
  let sk = mk_var("s"^string_of_int k,`:armstate`) in
  let rv = mk_var("r"^string_of_int k,`:int64`) in
  VP_USE_TAC (mk_neg c) THEN
  ABBREV_TAC (mk_eq(rv,list_mk_comb(
    `read:(armstate,int64)component->armstate->int64`,[`X0`; sk]))) THEN
  ARM_STEPS_TAC VP_EXEC [k+1] THEN
  WG_PC_REWRITE_TAC
   [VAL_EQ_0; ASSUME (mk_neg(mk_eq(rv,`word 0:int64`)))];;

let VP_BAD_MAC1_TAC =
  VP_TAKEN_TAC vp_mac1ok 23 THEN
  ARM_STEPS_TAC VP_EXEC (25--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wg_mac] THEN ASM_REWRITE_TAC[];;

let VP_NOCHECK_TAC =
  WG_PC_REWRITE_TAC [ASSUME `~check`] THEN
  ARM_STEPS_TAC VP_EXEC (26--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wg_mac] THEN ASM_REWRITE_TAC[];;

let VP_COOKIE_MAC2_TAC =
  WG_PC_REWRITE_TAC [ASSUME `check:bool`] THEN
  ARM_STEPS_TAC VP_EXEC (26--29) THEN
  VP_COOKIE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `proto:int16`; `th:int16`;
    `nh:int16`; `head:int64`; `sec:byte list`; `bd:int64`; `a4:byte list`;
    `a6:byte list`; `port:byte list`; `mset:int64`; `mcpy:int64`;
    `dwr:int64`; `uwr:int64`; `drd:int64`; `urd:int64`; `ktc:int64`;
    `grb:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 30 THEN
  ARM_STEPS_TAC VP_EXEC (31--37) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WG_LEN32_SUB
    (MP (ARITH_RULE `32 <= val(len:int32) ==> 16 <= val len`)
        (ASSUME `32 <= val(len:int32)`))]) THEN
  WG_REG_REWRITE_TAC `X3` [ASSUME `val(len:int32) - 16 = n + 16`] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,vp_ck),`16`))
  ASSUME_TAC THENL
   [REWRITE_TAC[wg_mac; LENGTH_BLAKE2S] THEN ARITH_TAC; ALL_TAC] THEN
  VP_MAC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    vp_ck; `SUB_LIST(0,n + 16) (msg:byte list)`; `mset:int64`; `ea:int64`;
    `el:num`; `ev:num`; `mcpy:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 38 THEN
  ARM_STEPS_TAC VP_EXEC (39--42) THEN
  WG_REG_REWRITE_TAC `X1` [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  VP_COMPARE_TAC vp_mac2 `SUB_LIST(n + 16,16) (msg:byte list)` 43;;

let VP_BAD_MAC2_TAC =
  VP_TAKEN_TAC vp_mac2ok 43 THEN
  ARM_STEPS_TAC VP_EXEC (45--49) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`sec':byte list`; `T`] THEN
  REWRITE_TAC[wg_mac] THEN
  ASM_REWRITE_TAC[REWRITE_RULE[wg_mac] (ASSUME (mk_neg vp_mac2ok))];;

let VP_RATELIMIT_TAC =
  VP_USE_TAC vp_mac2ok THEN
  ARM_STEPS_TAC VP_EXEC (44--49) THEN WG_PLT_TAC VP_EXEC 49 THEN
  WG_CALL_TAC "ratelimiter" VP_EXEC
   [`read X0 s`; `read X1 s`; `read SP s`; `read X30 s`] 54 THEN
  ABBREV_TAC `rl = read X0 s54` THEN
  ARM_STEPS_TAC VP_EXEC (55--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`sec':byte list`; `b:bool`] THEN
  REWRITE_TAC[wg_mac] THEN
  ASM_REWRITE_TAC[REWRITE_RULE[wg_mac] (ASSUME vp_mac2ok)] THEN
  MATCH_MP_TAC VP_RL_RESULT THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_COOKIE_VALIDATE_PACKET_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  VP_SETUP_TAC THEN VP_MAC1_TAC THEN
  ASM_CASES_TAC vp_mac1ok THENL [ALL_TAC; VP_BAD_MAC1_TAC] THEN
  VP_USE_TAC vp_mac1ok THEN ARM_STEPS_TAC VP_EXEC (24--25) THEN
  WG_PC_REWRITE_TAC [MATCH_MP VP_CHECK_BIT
    (ASSUME `word_and (cc:int64) (word 255) =
             (if check then word 1 else word 0)`)] THEN
  ASM_CASES_TAC `check:bool` THENL [ALL_TAC; VP_NOCHECK_TAC] THEN
  VP_COOKIE_MAC2_TAC THEN
  ASM_CASES_TAC vp_mac2ok THENL [VP_RATELIMIT_TAC; VP_BAD_MAC2_TAC]);;

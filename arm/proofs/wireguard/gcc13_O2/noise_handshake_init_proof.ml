(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of noise_handshake_init_spec.ml: memset of the       *)
(* handshake (with the zero facts for its 64-bit words and the index, which  *)
(* the simulation keeps), __init_rwsem, the stores, the copy of the          *)
(* preshared key if there is one (two paths), and                            *)
(* wg_noise_precompute_static_static. The handshake is named by the address  *)
(* peer + 240 from the start, in the form of the simulation.                 *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/noise_handshake_init_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/noise_common.ml";;

let WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "wg_noise_handshake_init"; layout_range "plt_memset";
    layout_range "plt_init_rwsem"];;

let HI_EXEC = WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_EXEC;;

let HI_PS_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,HI_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_NOISE_PRECOMPUTE_STATIC_STATIC_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let hi_got = [`got_memset:num`; `got_init_rwsem:num`];;

(* The offsets in the handshake of the 64-bit words that stay zero.          *)

let hi_zero_words =
  [8; 16; 40; 56; 64; 72; 80; 120; 128; 136; 144; 184; 192; 200; 208;
   216; 224; 232; 240; 248; 256; 264; 272; 280; 288];;

(* wg_noise_precompute_static_static at step k (with the remote static key   *)
(* as 32 bytes), the return, and a field of the handshake that is zero or    *)
(* 32 bytes from their words.                                                *)

let HI_TAIL_TAC k =
  SUBGOAL_THEN
   (vsubst [mk_var("s"^string_of_int (k-1),`:armstate`),`s:armstate`]
      `read (memory :> bytes(word_add peer (word 328),32)) s =
       num_of_bytelist rpub`)
  ASSUME_TAC THENL [WG_BYTES32_OF_WORDS_TAC[]; ALL_TAC] THEN
  HI_PS_TAC
   [`read X0 s`; `si:int64`; `hid:bool`; `spriv:byte list`;
    `rpub:byte list`; `cfn:int64`; `dwr:int64`; `uwr:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] k THEN
  ARM_STEPS_TAC HI_EXEC ((k+1)--(k+5)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let HI_FIELD_TAC : tactic =
  W(fun (asl,w) -> if rand w = `0` then WG_ZERO_BYTES_TAC
                   else WG_BYTES32_OF_WORDS_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_NOISE_HANDSHAKE_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`hs:int64`; `si:int64`; `pub:int64`; `psk:int64`; `peer:int64`;
    `hid:bool`; `spriv:byte list`; `rpub:byte list`; `pskb:byte list`;
    `mset:int64`; `irw:int64`; `cfn:int64`; `dwr:int64`; `uwr:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 4208 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; PAIRWISE; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `hs = word_add peer (word 240):int64`)) THEN
  CONV_TAC WG_ADDR_CONV THEN
  WG_LABEL_CONTRACTS_TAC
   [`memset_contract mset ea el ev`,"memset";
    `init_rwsem_contract irw ea el ev`,"init_rwsem"] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) hi_got) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 4144):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun g -> GOT_ENTRY_TAC g `s0:armstate`) hi_got THEN
  WG_BYTES32_WORDS_TAC `pub:int64` `s0:armstate` THEN

  (*** memset, __init_rwsem and the stores ***)

  ARM_STEPS_TAC HI_EXEC (1--13) THEN WG_PLT_TAC HI_EXEC 13 THEN
  WG_CALL_TAC "memset" HI_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 18 THEN
  MEMSET_ZERO_BYTES_TAC THEN
  MEMSET_ZERO_WORDS64_TAC `word_add peer (word 240):int64` 336 hi_zero_words
    `s18:armstate` THEN
  MP_TAC(ISPECL [`word_add peer (word 240):int64`; `336`; `0`; `28`; `4`;
                 `s18:armstate`] WG_READ_BYTES_OF_NUM) THEN
  ASM_REWRITE_TAC[DIV_0; MOD_0; WG_READ_BYTES_VAL; VAL_EQ_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV WG_ADDR_CONV) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC HI_EXEC (19--24) THEN WG_PLT_TAC HI_EXEC 24 THEN
  WG_CALL_TAC "init_rwsem" HI_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read SP s`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC HI_EXEC (30--38) THEN

  (*** The two paths, as the preshared key is NULL or not ***)

  ASM_CASES_TAC `psk:int64 = word 0` THENL
   [WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `psk:int64 = word 0`] THEN
    ARM_STEPS_TAC HI_EXEC (39--42) THEN HI_TAIL_TAC 43;
    WG_PC_REWRITE_TAC [VAL_EQ_0; ASSUME `~(psk:int64 = word 0)`] THEN
    WG_IMP_ASSUM_REWRITE_TAC[ASSUME `~(psk:int64 = word 0)`] THEN
    WG_BYTES32_WORDS_TAC `psk:int64` `s38:armstate` THEN
    ARM_STEPS_TAC HI_EXEC (39--46) THEN HI_TAIL_TAC 47] THEN
  REPEAT CONJ_TAC THEN HI_FIELD_TAC);;

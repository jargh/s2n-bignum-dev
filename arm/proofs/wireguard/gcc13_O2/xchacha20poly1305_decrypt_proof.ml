(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of xchacha20poly1305_decrypt_spec.ml: memset of the  *)
(* state on the stack, then xchacha_init and __chacha20poly1305_decrypt,     *)
(* simulated with their theorems.                                            *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/xchacha20poly1305_decrypt_spec.ml";;
needs "common/wireguard_kernel.ml";;

let WIREGUARD_XCHACHA20POLY1305_DECRYPT_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "xchacha20poly1305_decrypt"; layout_range "plt_memset"];;

let XD_EXEC = WIREGUARD_XCHACHA20POLY1305_DECRYPT_GCC13_O2_EXEC;;

let XD_INIT_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,XD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_XCHACHA_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let XD_INNER_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,XD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_XCHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
 prove
 (WIREGUARD_XCHACHA20POLY1305_DECRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `len:int64`; `ad:int64`; `adlen:int64`;
    `nonce:int64`; `key:int64`; `kb:byte list`; `nb:byte list`;
    `ct:byte list`; `al:byte list`; `kv:int64`; `ms:int64`; `mset:int64`;
    `ea1:int64`; `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 800 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "memset" (REWRITE_RULE[memset_contract] th))
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 25; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 656):int64)`
  ASSUME_TAC THENL [ALIGNED_WORD_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  GOT_ENTRY_TAC `got_memset:num` `s0:armstate` THEN

  (*** The zeroing of the state at stackpointer + 736 and xchacha_init ***)

  ARM_STEPS_TAC XD_EXEC (1--17) THEN WG_PLT_TAC XD_EXEC 17 THEN
  WG_CALL_TAC "memset" XD_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC XD_EXEC (23--26) THEN
  XD_INIT_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `kb:byte list`; `nb:byte list`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
    `read SP s`; `read X30 s`] 27 THEN

  (*** __chacha20poly1305_decrypt and the return ***)

  ARM_STEPS_TAC XD_EXEC (28--34) THEN
  ASSUME_TAC(MATCH_MP LENGTH_XCHACHA20_NONCE
    (ASSUME `LENGTH(nb:byte list) = 24`)) THEN
  ASSUME_TAC(ISPECL [`kb:byte list`; `SUB_LIST(0,16) (nb:byte list)`]
    LENGTH_HCHACHA20) THEN
  SUBGOAL_THEN
   `dst:int64 = src \/
    nonoverlapping (dst,val(len:int64) - 16) (src:int64,val len)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  XD_INNER_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `read X5 s`; `hchacha20 kb (SUB_LIST(0,16) nb)`;
    `xchacha20_nonce nb`; `ct:byte list`; `al:byte list`; `kv:int64`;
    `ms:int64`; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`; `pc:num`;
    `read SP s`; `read X30 s`] 35 THEN
  ARM_STEPS_TAC XD_EXEC (36--41) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[wg_xaead_decrypt; xchacha20_poly1305_decrypt]);;

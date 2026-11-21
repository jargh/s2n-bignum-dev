(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of chacha20poly1305_decrypt_inner_spec.ml            *)
(* (__chacha20poly1305_decrypt). If src_len < 16 the result is false at      *)
(* once. Otherwise the simulation is as for encryption (with the shared      *)
(* lemmas and tactics of chacha20poly1305_common.ml) up to the tag of the    *)
(* first src_len - 16 bytes of the input, computed into the block buffer at  *)
(* stackpointer + 344, through the two optional calls for the padding; then  *)
(* __crypto_memneq compares it with the last 16 bytes, and if they are the   *)
(* same the ciphertext is decrypted into dst by chacha_crypt. Nine paths.    *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_decrypt_inner_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_common.ml";;

let WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "__chacha20poly1305_decrypt"; layout_range "plt_memset"];;

let CD_EXEC = WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_EXEC;;

let CD_CRYPT_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CD_INIT_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CD_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CD_FINAL_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CD_MEMNEQ_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CD_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CRYPTO_MEMNEQ_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the length tests of the code, the RFC decryption as the kernel    *)
(* computes it, and the comparison of the tags as numbers.                   *)
(* ------------------------------------------------------------------------- *)

let CP_SUB16 = prove
 (`!x:int64. 16 <= val x ==> word_sub x (word 16) = word(val x - 16)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  ASM_SIMP_TAC[WG_WORD_SUB_LE]);;

let CP_LS15 = prove
 (`!x:int64.
     (15 <= val x /\ ~(val(word_sub x (word 15)) = 0)) <=> 16 <= val x`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let CP_DEC_SHORT = prove
 (`!key nonce (ct:byte list) al.
     LENGTH ct < 16 ==> aead_chacha20_poly1305_decrypt key nonce ct al = NONE`,
  SIMP_TAC[aead_chacha20_poly1305_decrypt]);;

let CP_NUM_INJ = prove
 (`!l1 l2:byte list.
     LENGTH l1 = LENGTH l2
     ==> (num_of_bytelist l1 = num_of_bytelist l2 <=> l1 = l2)`,
  MESON_TAC[BYTELIST_OF_NUM_OF_BYTELIST]);;

let CP_LENGTH_POLY1305 = prove
 (`!k m. LENGTH(poly1305 k m) = 16`,
  REWRITE_TAC[poly1305; LENGTH_BYTELIST_OF_NUM]);;

let CP_DEC_EQ = prove
 (`!key nonce (ct:byte list) al.
     16 <= LENGTH ct
     ==> aead_chacha20_poly1305_decrypt key nonce ct al =
         if poly1305 (SUB_LIST(0,32) (chacha20_block key 0 nonce))
             (APPEND (APPEND (APPEND (APPEND al (poly1305_pad16 (LENGTH al)))
                                     (SUB_LIST(0,LENGTH ct - 16) ct))
                             (poly1305_pad16 (LENGTH ct - 16)))
                     (APPEND (bytelist_of_num 8 (LENGTH al))
                             (bytelist_of_num 8 (LENGTH ct - 16)))) =
            SUB_LIST(LENGTH ct - 16,16) ct
         then SOME(chacha20_encrypt key 1 nonce
                    (SUB_LIST(0,LENGTH ct - 16) ct))
         else NONE`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[aead_chacha20_poly1305_decrypt; aead_chacha20_poly1305_tag;
                  LET_DEF; LET_END_DEF; GSYM NOT_LE] THEN
  SUBGOAL_THEN
   `LENGTH(SUB_LIST(0,LENGTH ct - 16) (ct:byte list)) = LENGTH ct - 16`
  SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC;
    REWRITE_TAC[GSYM APPEND_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* The bytes absorbed after the ad and its padding (cp_d2), the ciphertext   *)
(* (the first src_len - 16 bytes of the input) and its padding, and the      *)
(* lengths, and their lengths mod and div 16; the tags computed and given.   *)
(* ------------------------------------------------------------------------- *)

let cd_n = `val(len:int64) - 16`;;

let cd_c = `SUB_LIST(0,val(len:int64) - 16) (ct:byte list)`;;

let cd_d3 = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,cp_d2),
                    cd_c);;

let cd_d4 = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,cd_d3),
                    `poly1305_pad16 (val(len:int64) - 16)`);;

let cd_lens = `APPEND (bytelist_of_num 8 (val(adlen:int64)))
                      (bytelist_of_num 8 (val(len:int64) - 16))`;;

let cd_d5 = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,cd_d4),
                    cd_lens);;

let cd_qac = `(val(adlen:int64) + 15) DIV 16 +
              ((val(len:int64) - 16) + 15) DIV 16`;;

let CD_D3_LENS_TAC =
  SUBGOAL_THEN
   (subst [cd_d3,`d3:byte list`]
     `LENGTH(d3:byte list) MOD 16 = (val(len:int64) - 16) MOD 16 /\
      LENGTH(d3:byte list) DIV 16 =
      (val(adlen:int64) + 15) DIV 16 + (val(len:int64) - 16) DIV 16`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN
    REWRITE_TAC[ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,cd_c),cd_n));
                ASSUME `LENGTH(al:byte list) = val(adlen:int64)`] THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL CP_PAD_LEN)] THEN
    REWRITE_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC];;

let cd_d3_lens () =
  [ASSUME(subst [cd_d3,`d3:byte list`]
     `LENGTH(d3:byte list) MOD 16 = (val(len:int64) - 16) MOD 16`);
   ASSUME(subst [cd_d3,`d3:byte list`]
     `LENGTH(d3:byte list) DIV 16 =
      (val(adlen:int64) + 15) DIV 16 + (val(len:int64) - 16) DIV 16`)];;

let CD_D4_LENS_TAC =
  SUBGOAL_THEN
   (subst [cd_d4,`d4:byte list`; cd_qac,`qq:num`]
     `LENGTH(d4:byte list) MOD 16 = 0 /\ LENGTH(d4:byte list) DIV 16 = qq`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND] THEN
    REWRITE_TAC[ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,cd_c),cd_n));
                ASSUME `LENGTH(al:byte list) = val(adlen:int64)`] THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL CP_PAD_LEN)] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL CP_PAD_LEN)] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ];
    ALL_TAC];;

let cd_d4_lens () =
  [ASSUME(subst [cd_d4,`d4:byte list`] `LENGTH(d4:byte list) MOD 16 = 0`);
   ASSUME(subst [cd_d4,`d4:byte list`; cd_qac,`qq:num`]
     `LENGTH(d4:byte list) DIV 16 = qq`)];;

let CD_D5_LENS_TAC =
  W(fun _ ->
    MP_TAC(ISPECL [cd_d4; cd_lens; cd_qac] CP_LEN_APPEND16) THEN
    ANTS_TAC THENL
     [REWRITE_TAC (cd_d4_lens ()) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN
      CONV_TAC NUM_REDUCE_CONV;
      STRIP_TAC]);;

let cd_d5_lens () =
  [ASSUME(subst [cd_d5,`d5:byte list`] `LENGTH(d5:byte list) MOD 16 = 0`);
   ASSUME(subst [cd_d5,`d5:byte list`; cd_qac,`qq:num`]
     `LENGTH(d5:byte list) DIV 16 = qq + 1`)];;

let cd_tag =
  mk_comb(`poly1305 (SUB_LIST(0,32) (chacha20_block key 0 nonce))`,cd_d5);;

let cd_rtag = `SUB_LIST(val(len:int64) - 16,16) (ct:byte list)`;;

(* ------------------------------------------------------------------------- *)
(* Up to the test of src_len: the zero page address and the zeroing of the   *)
(* poly1305_desc_ctx and the block buffer (as stack variables); if src_len   *)
(* < 16, the result is false.                                                *)
(* ------------------------------------------------------------------------- *)

let CD_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `len:int64`; `ad:int64`; `adlen:int64`;
    `st:int64`; `key:byte list`; `nonce:byte list`; `ct:byte list`;
    `al:byte list`; `kv:int64`; `ms:int64`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 656 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN
               LABEL_TAC "memset" (REWRITE_RULE[memset_contract] th))
    (CONJUNCTS_THEN2
      (fun th -> ASSUME_TAC th THEN
                 LABEL_TAC "memcpy" (REWRITE_RULE[memcpy_contract] th))
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `data_kimage_voffset:num`] WORD_ADD;
              SPECL [`pc:num`; `data_memstart_addr:num`] WORD_ADD] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x" ^ string_of_int n ^ "_init")
                        (mk_const("X" ^ string_of_int n,[])))
            [19; 20; 21; 22; 23; 24; 25; 26; 29] THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN
  GOT_ENTRY_TAC `got_memset:num` `s0:armstate` THEN
  GOT_ENTRY_TAC `got_memcpy:num` `s0:armstate`;;

let CD_ENTRY_TAC =
  ARM_STEPS_TAC CD_EXEC (1--3) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC CD_EXEC (4--7) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC CD_EXEC (8--27) THEN CP_ZPA_TAC THEN
  WG_PLT_TAC CD_EXEC 27 THEN
  WG_CALL_TAC "memset" CD_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 32 THEN
  ARM_STEPS_TAC CD_EXEC (33--37);;

let CD_SHORT_TAC =
  WG_PC_REWRITE_TAC[CP_LS15; ASSUME `~(16 <= val(len:int64))`] THEN
  ARM_STEPS_TAC CD_EXEC (38--45) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`key:byte list`; `nonce:byte list`; `ct:byte list`;
                 `al:byte list`] CP_DEC_SHORT) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(16 <= val(len:int64))`;
                           `LENGTH(ct:byte list) = val(len:int64)`] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[distinctness "option"] THEN CONV_TAC WORD_REDUCE_CONV;;


(* ------------------------------------------------------------------------- *)
(* Otherwise: the one-time key, poly1305_init and the update with the ad,    *)
(* then (with or without the padding of the ad) the update with the          *)
(* ciphertext, up to the test of its length mod 16 at step 63 or 69.         *)
(* ------------------------------------------------------------------------- *)

let CD_PART1_TAC =
  WG_PC_REWRITE_TAC[CP_LS15; ASSUME `16 <= val(len:int64)`] THEN
  ARM_STEPS_TAC CD_EXEC (38--43) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(zpa,val(word 32:int64))) s43 =
    num_of_bytelist(REPLICATE 32 (word 0:byte)) /\
    read (memory :> bytes(zpa,32)) s43 =
    num_of_bytelist(REPLICATE 32 (word 0:byte)) /\
    LENGTH(REPLICATE 32 (word 0:byte)) = val(word 32:int64) /\
    val(word 32:int64) = 32 /\ 32 < 2 EXP 32 /\
    num_of_bytelist(REPLICATE 32 (word 0:byte)) = 0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NUM_OF_BYTELIST_REPLICATE_0; LENGTH_REPLICATE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CD_CRYPT_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `chacha20_state key 0 nonce`; `REPLICATE 32 (word 0:byte)`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
    `read SP s`; `read X30 s`] 44 THEN
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if can (find_term (fun t -> try let n,_ = dest_const t in
              n = "chacha20_ctr" || n = "list_of_seq"
              with Failure _ -> false)) c
    then CONV_RULE NUM_REDUCE_CONV
          (REWRITE_RULE[CP_OTK; CHACHA20_CTR_STATE] th)
    else th) THEN
  ARM_STEPS_TAC CD_EXEC (45--47) THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,32) (chacha20_block key 0 nonce)) = 32`
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; CP_LENGTH_CHACHA20_BLOCK] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CD_INIT_TAC
   [`read X0 s`; `read X1 s`; `SUB_LIST(0,32) (chacha20_block key 0 nonce)`;
    `pc:num`; `read SP s`; `read X30 s`] 48 THEN
  CP_DESC_EXPAND_TAC [] `s48:armstate` THEN
  ARM_STEPS_TAC CD_EXEC (49--52) THEN
  MP_TAC(SPEC `adlen:int64` CP_ZX_ZX) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(adlen:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  CP_DESC_FOLD_TAC [] `[]:byte list` `s52:armstate` THEN
  CD_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; `[]:byte list`;
    `al:byte list`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 53 THEN
  CP_DESC_EQ_TAC (ISPEC `al:byte list` (CONJUNCT1 APPEND)) `s53:armstate` THEN
  CP_DESC_EXPAND_TAC [] `s53:armstate` THEN
  ARM_STEPS_TAC CD_EXEC (54--55);;

let CD_X21_TAC =
  MP_TAC(SPEC `len:int64` CP_SUB16) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(SPEC `val(len:int64) - 16` WG_WORD_ZX_SMALL) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

let CD_C_FACTS_TAC s =
  let sub = vsubst [s,`s:armstate`] in
  MP_TAC(ISPECL [`src:int64`; `ct:byte list`; `val(len:int64)`; `0`;
                 `val(len:int64) - 16`; s] WG_READ_BYTES_SUBLIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC;
                  REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   (sub `val(word(val(len:int64) - 16):int64) = val len - 16 /\
         LENGTH(SUB_LIST(0,val len - 16) (ct:byte list)) = val len - 16 /\
         LENGTH(SUB_LIST(0,val len - 16) (ct:byte list)) =
         val(word(val len - 16):int64) /\
         read (memory :> bytes(src,val(word(val len - 16):int64))) s =
         num_of_bytelist(SUB_LIST(0,val len - 16) ct) /\
         val(word(val len - 16):int64) + 16 < 2 EXP 32 /\
         (val len - 16) + 16 < 2 EXP 32`)
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word(val(len:int64) - 16):int64) = val len - 16`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN
    UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC];;

let CD_PAD1Z_TAC =
  WG_PC_REWRITE_TAC[CP_AND15; ASSUME `val(adlen:int64) MOD 16 = 0`] THEN
  CP_DESC_FOLD_TAC [] `al:byte list` `s55:armstate` THEN
  SUBGOAL_THEN (mk_eq(`al:byte list`,cp_d2)) ASSUME_TAC THENL
   [MP_TAC(SPEC `val(adlen:int64)` CP_PAD_Z) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  CP_DESC_EQ_TAC (ASSUME (mk_eq(`al:byte list`,cp_d2))) `s55:armstate` THEN
  CP_D2_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cp_d2_lens ()) `s55:armstate`) THEN
  ARM_STEPS_TAC CD_EXEC (56--60) THEN CD_X21_TAC THEN
  CD_C_FACTS_TAC `s60:armstate` THEN
  W(fun _ -> CP_DESC_FOLD_TAC (cp_d2_lens ()) cp_d2 `s60:armstate`) THEN
  CD_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; cp_d2; cd_c;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 61 THEN
  CD_D3_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cd_d3_lens ()) `s61:armstate`) THEN
  ARM_STEPS_TAC CD_EXEC (62--63);;

let CD_PAD1N_TAC =
  WG_PC_REWRITE_TAC[CP_AND15; ASSUME `~(val(adlen:int64) MOD 16 = 0)`] THEN
  ARM_STEPS_TAC CD_EXEC (56--61) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CP_PADLEN_WORD]) THEN
  MP_TAC(SPEC `len:int64` CP_SUB16) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  CP_PAD_FACTS_TAC `val(adlen:int64)` `s61:armstate` THEN
  CP_DESC_FOLD_TAC [] `al:byte list` `s61:armstate` THEN
  CD_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; `al:byte list`;
    `poly1305_pad16 (val(adlen:int64))`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 62 THEN
  CP_D2_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cp_d2_lens ()) `s62:armstate`) THEN
  ARM_STEPS_TAC CD_EXEC (63--66) THEN
  MP_TAC(SPEC `val(len:int64) - 16` WG_WORD_ZX_SMALL) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  CD_C_FACTS_TAC `s66:armstate` THEN
  W(fun _ -> CP_DESC_FOLD_TAC (cp_d2_lens ()) cp_d2 `s66:armstate`) THEN
  CD_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; cp_d2; cd_c;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 67 THEN
  CD_D3_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cd_d3_lens ()) `s67:armstate`) THEN
  ARM_STEPS_TAC CD_EXEC (68--69);;

(* The padding of the ciphertext (from step j), reaching 0x62a4 at step j or *)
(* j + 7.                                                                    *)

let CD_VALN_TAC =
  RULE_ASSUM_TAC(fun th ->
    if concl th = `val(word(val(len:int64) - 16):int64) = val len - 16` then th
    else REWRITE_RULE
          [ASSUME `val(word(val(len:int64) - 16):int64) = val len - 16`] th);;

let CD_PAD2Z_TAC j =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in
  WG_PC_REWRITE_TAC[CP_AND15;
    ASSUME `val(word(val(len:int64) - 16):int64) = val len - 16`;
    ASSUME `(val(len:int64) - 16) MOD 16 = 0`] THEN
  W(fun _ -> CP_DESC_FOLD_TAC (cd_d3_lens ()) cd_d3 (sk j)) THEN
  SUBGOAL_THEN (mk_eq(cd_d3,cd_d4)) ASSUME_TAC THENL
   [MP_TAC(SPEC `val(len:int64) - 16` CP_PAD_Z) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  CP_DESC_EQ_TAC (ASSUME (mk_eq(cd_d3,cd_d4))) (sk j) THEN
  CD_D4_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cd_d4_lens ()) (sk j));;

let CD_PAD2N_TAC j =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in
  WG_PC_REWRITE_TAC[CP_AND15;
    ASSUME `val(word(val(len:int64) - 16):int64) = val len - 16`;
    ASSUME `~((val(len:int64) - 16) MOD 16 = 0)`] THEN
  ARM_STEPS_TAC CD_EXEC ((j+1)--(j+5)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CP_PADLEN_WORD]) THEN CD_VALN_TAC THEN
  CP_PAD_FACTS_TAC cd_n (sk(j+5)) THEN
  W(fun _ -> CP_DESC_FOLD_TAC (cd_d3_lens ()) cd_d3 (sk(j+5))) THEN
  CD_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; cd_d3;
    `poly1305_pad16 (val(len:int64) - 16)`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] (j+6) THEN
  CD_D4_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cd_d4_lens ()) (sk(j+6))) THEN
  ARM_STEPS_TAC CD_EXEC [j+7];;

(* ------------------------------------------------------------------------- *)
(* From 0x62a4 (step j): the lengths, poly1305_final into the block buffer,  *)
(* __crypto_memneq with the last 16 bytes of the input (its result as the    *)
(* variable r), and in each case of the tags being the same the result.      *)
(* ------------------------------------------------------------------------- *)

let CD_PART3A_TAC j =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in
  ARM_STEPS_TAC CD_EXEC ((j+1)--(j+5)) THEN
  MP_TAC(CP_ADDR_NORM_RULE(ISPECL [`word_add stackpointer (word 344):int64`;
                 `adlen:int64`; `word(val(len:int64) - 16):int64`; sk(j+5)]
                 CP_LENS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   (subst [cd_lens,`l:byte list`; sk(j+5),`s:armstate`]
     `read (memory :> bytes(word_add stackpointer (word 344),
                            val(word 16:int64))) s =
      num_of_bytelist l /\
      LENGTH(l:byte list) = val(word 16:int64) /\
      val(word 16:int64) = 16 /\ val(word 16:int64) + 16 < 2 EXP 32`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  W(fun _ -> CP_DESC_FOLD_TAC (cd_d4_lens ()) cd_d4 (sk(j+5))) THEN
  CD_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; cd_d4; cd_lens;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] (j+6) THEN
  CD_D5_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cd_d5_lens ()) (sk(j+6))) THEN
  ARM_STEPS_TAC CD_EXEC ((j+7)--(j+9)) THEN
  W(fun _ -> CP_DESC_FOLD_TAC (cd_d5_lens ()) cd_d5 (sk(j+9))) THEN
  CD_FINAL_TAC
   [`read X0 s`; `read X1 s`; `SUB_LIST(0,32) (chacha20_block key 0 nonce)`;
    cd_d5; `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
    `read SP s`; `read X30 s`] (j+10);;

let CD_MEMNEQ_PRE_TAC s =
  let sub = vsubst [s,`s:armstate`] in
  MP_TAC(ISPECL [`src:int64`; `ct:byte list`; `val(len:int64)`;
                 `val(len:int64) - 16`; `16`; s] WG_READ_BYTES_SUBLIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
                  UNDISCH_TAC `16 <= val(len:int64)` THEN ARITH_TAC;
                  DISCH_TAC] THEN
  SUBGOAL_THEN
   (subst [cd_tag,`t:byte list`; cd_rtag,`r:byte list`]
     (sub `read (memory :> bytes(word_add stackpointer (word 344),
                                 val(word 16:int64))) s =
           num_of_bytelist t /\
           read (memory :> bytes(word_add src (word(val(len:int64) - 16)),
                                 val(word 16:int64))) s =
           num_of_bytelist r`))
  STRIP_ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let CD_X0_TAC s =
  let x0s = mk_comb(`read X0`,s) in
  X_CHOOSE_TAC `r:int64`
   (MESON[] (mk_exists(`r:int64`,mk_eq(x0s,`r:int64`)))) THEN
  RULE_ASSUM_TAC(fun th ->
    if concl th = mk_eq(x0s,`r:int64`) then th
    else REWRITE_RULE[ASSUME(mk_eq(x0s,`r:int64`))] th);;

let CD_CMP_TAC s =
  CD_X0_TAC s THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,cd_tag),
                      mk_comb(`LENGTH:byte list->num`,cd_rtag)))
  ASSUME_TAC THENL
   [REWRITE_TAC[CP_LENGTH_POLY1305; LENGTH_SUB_LIST] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `16 <= val(len:int64)` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && lhand(concl th) = `r:int64 = word 0`
    then ASSUME_TAC(REWRITE_RULE[MATCH_MP CP_NUM_INJ
           (ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,cd_tag),
                         mk_comb(`LENGTH:byte list->num`,cd_rtag))))] th)
    else failwith "CD_CMP_TAC");;

let CD_MATCH_TAC j =
  SUBGOAL_THEN `r:int64 = word 0` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ARM_STEPS_TAC CD_EXEC ((j+16)--(j+24)) THEN
  MP_TAC(SPEC `val(len:int64) - 16` WG_WORD_ZX_SMALL) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN
   `(dst:int64 = src \/
     nonoverlapping (dst,val(len:int64) - 16) (src:int64,val len - 16)) /\
    val(word(val(len:int64) - 16):int64) < 2 EXP 32 /\
    val(len:int64) - 16 < 2 EXP 32 /\
    val(len:int64) - 16 <= val len`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
       [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        DISJ2_TAC THEN NONOVERLAPPING_TAC];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC];
    ALL_TAC] THEN
  CD_CRYPT_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `chacha20_state key 1 nonce`; cd_c;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
    `read SP s`; `read X30 s`] (j+25) THEN
  MP_TAC(ISPECL [`key:byte list`; `nonce:byte list`; cd_c; cd_n] CP_ENC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARM_STEPS_TAC CD_EXEC ((j+26)--(j+34)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`key:byte list`; `nonce:byte list`; `ct:byte list`;
                 `al:byte list`] CP_DEC_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option";
              FORALL_UNWIND_THM1] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[CP_LENGTH_ENC];;

let CD_MISMATCH_TAC j =
  ARM_STEPS_TAC CD_EXEC ((j+16)--(j+18)) THEN
  SUBGOAL_THEN `~(val(word_sub (r:int64) (word 0)) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  WG_PC_REWRITE_TAC[ASSUME `~(val(word_sub (r:int64) (word 0)) = 0)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `~(val(word_sub (r:int64) (word 0)) = 0)`]) THEN
  ARM_STEPS_TAC CD_EXEC ((j+19)--(j+27)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`key:byte list`; `nonce:byte list`; `ct:byte list`;
                 `al:byte list`] CP_DEC_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[distinctness "option"] THEN CONV_TAC WORD_REDUCE_CONV;;

let CD_PART3_TAC j =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in
  CD_PART3A_TAC j THEN
  ARM_STEPS_TAC CD_EXEC ((j+11)--(j+14)) THEN
  CD_MEMNEQ_PRE_TAC (sk(j+14)) THEN
  CD_MEMNEQ_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; mk_comb(`num_of_bytelist`,cd_tag);
    mk_comb(`num_of_bytelist`,cd_rtag); `pc:num`; `read X30 s`] (j+15) THEN
  CD_CMP_TAC (sk(j+15)) THEN
  ASM_CASES_TAC (mk_eq(cd_tag,cd_rtag)) THENL
   [CD_MATCH_TAC j; CD_MISMATCH_TAC j];;

let CD_REST_TAC j =
  ASM_CASES_TAC `(val(len:int64) - 16) MOD 16 = 0` THENL
   [CD_PAD2Z_TAC j THEN CD_PART3_TAC j;
    CD_PAD2N_TAC j THEN CD_PART3_TAC (j+7)];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
  (WIREGUARD_CHACHA20POLY1305_DECRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
   CD_SETUP_TAC THEN CD_ENTRY_TAC THEN
   ASM_CASES_TAC `16 <= val(len:int64)` THENL
    [CD_PART1_TAC THEN
     ASM_CASES_TAC `val(adlen:int64) MOD 16 = 0` THENL
      [CD_PAD1Z_TAC THEN CD_REST_TAC 63;
       CD_PAD1N_TAC THEN CD_REST_TAC 69];
     CD_SHORT_TAC]);;

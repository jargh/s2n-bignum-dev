(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of chacha20poly1305_encrypt_inner_spec.ml            *)
(* (__chacha20poly1305_encrypt). A straight-line simulation through the      *)
(* calls, with two optional calls for the padding of the ad and of the       *)
(* ciphertext (four paths). Between the calls of poly1305_* the              *)
(* poly1305_desc_ctx on the stack is kept as the facts of poly1305_desc_at   *)
(* for the bytes absorbed so far; the tag goes to dst + src_len, named       *)
(* dtag for the nonoverlapping conditions of poly1305_final.                 *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_encrypt_inner_spec.ml";;
needs "arm/proofs/wireguard/gcc13_O2/chacha20poly1305_common.ml";;

let WIREGUARD_CHACHA20POLY1305_ENCRYPT_INNER_GCC13_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE wireguard_gcc13_O2_mc
   [layout_range "__chacha20poly1305_encrypt"; layout_range "plt_memset"];;

let CE_EXEC = WIREGUARD_CHACHA20POLY1305_ENCRYPT_INNER_GCC13_O2_EXEC;;

let CE_CRYPT_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CE_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_CHACHA_CRYPT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CE_INIT_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CE_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_INIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

let CE_UPDATE_TAC = ARM_SUBROUTINE_SIM_TAC
  (wireguard_gcc13_O2_mc,CE_EXEC,0,wireguard_gcc13_O2_mc,
   WIREGUARD_POLY1305_UPDATE_GCC13_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Lemmas: the region of the tag at dst + src_len, and the RFC AEAD as the   *)
(* kernel computes it (the others are in chacha20poly1305_common.ml).        *)
(* ------------------------------------------------------------------------- *)

let CP_TAG_CONTAINED = prove
 (`!dst:int64 l.
     contained_modulo (2 EXP 64) (val(word_add dst (word l)),16)
                      (val dst,l + 16)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONTAINED_MODULO_LMOD] THEN
  REWRITE_TAC[contained_modulo] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  EXISTS_TAC `l + i:num` THEN CONJ_TAC THENL
   [UNDISCH_TAC `i < 16` THEN ARITH_TAC;
    REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ADD_ASSOC]]);;

let CP_TAG_NONOVERLAP = prove
 (`!dst:int64 l a n.
     nonoverlapping_modulo (2 EXP 64) (val dst,l + 16) (a,n)
     ==> nonoverlapping_modulo (2 EXP 64)
           (val(word_add dst (word l)),16) (a,n) /\
         nonoverlapping_modulo (2 EXP 64)
           (a,n) (val(word_add dst (word l)),16)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
    MAP_EVERY EXISTS_TAC [`val(dst:int64)`; `l + 16`; `a:num`; `n:num`] THEN
    ASM_REWRITE_TAC[CP_TAG_CONTAINED; CONTAINED_MODULO_REFL; LE_REFL];
    MESON_TAC[NONOVERLAPPING_MODULO_SYM]]);;

let CP_TAG_DST = prove
 (`!dst:int64 l.
     l + 16 <= 2 EXP 64
     ==> nonoverlapping_modulo (2 EXP 64) (val dst,l)
                               (val(word_add dst (word l)),16) /\
         nonoverlapping_modulo (2 EXP 64) (val(word_add dst (word l)),16)
                               (val dst,l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`dst:int64`; `0`; `l:num`; `l:num`; `16`]
         NONOVERLAPPING_MODULO_64_OFFSET_BOTH) THEN
  REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[NONOVERLAPPING_MODULO_SYM]);;
let CP_AEAD_EQ = prove
 (`!key nonce (pl:byte list) al.
     aead_chacha20_poly1305_encrypt key nonce pl al =
     APPEND (chacha20_encrypt key 1 nonce pl)
      (poly1305 (SUB_LIST(0,32) (chacha20_block key 0 nonce))
        (APPEND (APPEND (APPEND (APPEND al (poly1305_pad16 (LENGTH al)))
                                (chacha20_encrypt key 1 nonce pl))
                        (poly1305_pad16 (LENGTH pl)))
                (APPEND (bytelist_of_num 8 (LENGTH al))
                        (bytelist_of_num 8 (LENGTH pl)))))`,
  REWRITE_TAC[aead_chacha20_poly1305_encrypt; aead_chacha20_poly1305_tag;
              LET_DEF; LET_END_DEF; GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[chacha20_encrypt; LENGTH_LIST_OF_SEQ]);;
(* ------------------------------------------------------------------------- *)
(* The bytes absorbed after the ad and its padding (cp_d2), the ciphertext   *)
(* and its padding, and the lengths, and their lengths mod and div 16.       *)
(* ------------------------------------------------------------------------- *)

let ce_c = `chacha20_encrypt key 1 nonce (pl:byte list)`;;

let ce_d3 = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,cp_d2),
                    ce_c);;

let ce_d4 = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,ce_d3),
                    `poly1305_pad16 (val(len:int64))`);;

let ce_lens = `APPEND (bytelist_of_num 8 (val(adlen:int64)))
                      (bytelist_of_num 8 (val(len:int64)))`;;

let ce_d5 = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,ce_d4),
                    ce_lens);;

let ce_qac = `(val(adlen:int64) + 15) DIV 16 + (val(len:int64) + 15) DIV 16`;;

let CE_D3_LENS_TAC =
  SUBGOAL_THEN
   (subst [ce_d3,`d3:byte list`]
     `LENGTH(d3:byte list) MOD 16 = val(len:int64) MOD 16 /\
      LENGTH(d3:byte list) DIV 16 =
      (val(adlen:int64) + 15) DIV 16 + val(len:int64) DIV 16`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; CP_LENGTH_ENC] THEN
    REWRITE_TAC[ASSUME `LENGTH(al:byte list) = val(adlen:int64)`;
                ASSUME `LENGTH(pl:byte list) = val(len:int64)`] THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL CP_PAD_LEN)] THEN
    REWRITE_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC];;

let ce_d3_lens () =
  [ASSUME(subst [ce_d3,`d3:byte list`]
     `LENGTH(d3:byte list) MOD 16 = val(len:int64) MOD 16`);
   ASSUME(subst [ce_d3,`d3:byte list`]
     `LENGTH(d3:byte list) DIV 16 =
      (val(adlen:int64) + 15) DIV 16 + val(len:int64) DIV 16`)];;

let CE_D4_LENS_TAC =
  SUBGOAL_THEN
   (subst [ce_d4,`d4:byte list`; ce_qac,`qq:num`]
     `LENGTH(d4:byte list) MOD 16 = 0 /\ LENGTH(d4:byte list) DIV 16 = qq`)
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; CP_LENGTH_ENC] THEN
    REWRITE_TAC[ASSUME `LENGTH(al:byte list) = val(adlen:int64)`;
                ASSUME `LENGTH(pl:byte list) = val(len:int64)`] THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL CP_PAD_LEN)] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL CP_PAD_LEN)] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ];
    ALL_TAC];;

let ce_d4_lens () =
  [ASSUME(subst [ce_d4,`d4:byte list`] `LENGTH(d4:byte list) MOD 16 = 0`);
   ASSUME(subst [ce_d4,`d4:byte list`; ce_qac,`qq:num`]
     `LENGTH(d4:byte list) DIV 16 = qq`)];;

let CE_D5_LENS_TAC =
  W(fun _ ->
    MP_TAC(ISPECL [ce_d4; ce_lens; ce_qac] CP_LEN_APPEND16) THEN
    ANTS_TAC THENL
     [REWRITE_TAC (ce_d4_lens ()) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN
      CONV_TAC NUM_REDUCE_CONV;
      STRIP_TAC]);;

let ce_d5_lens () =
  [ASSUME(subst [ce_d5,`d5:byte list`] `LENGTH(d5:byte list) MOD 16 = 0`);
   ASSUME(subst [ce_d5,`d5:byte list`; ce_qac,`qq:num`]
     `LENGTH(d5:byte list) DIV 16 = qq + 1`)];;

(* ------------------------------------------------------------------------- *)
(* Up to the test of ad_len & 15: the zero page address, the zeroing of the  *)
(* poly1305_desc_ctx (as a stack variable), the one-time key into the        *)
(* buffer at stackpointer + 344, poly1305_init and the update with the ad.   *)
(* ------------------------------------------------------------------------- *)

let CE_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `len:int64`; `ad:int64`; `adlen:int64`;
    `st:int64`; `key:byte list`; `nonce:byte list`; `pl:byte list`;
    `al:byte list`; `kv:int64`; `ms:int64`; `mset:int64`; `ea1:int64`;
    `el1:num`; `ev1:num`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 656 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  ABBREV_TAC
   `zpa = wg_zero_page_va (word(pc + data_empty_zero_page)) kv ms` THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
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

let CE_PART1_TAC =
  ARM_STEPS_TAC CE_EXEC (1--3) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC CE_EXEC (4--7) THEN WG_ADRP_TAC THEN
  ARM_STEPS_TAC CE_EXEC (8--27) THEN
  CP_ZPA_TAC THEN

  (*** memset of the poly1305_desc_ctx ***)

  WG_PLT_TAC CE_EXEC 27 THEN
  WG_CALL_TAC "memset" CE_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 32 THEN

  (*** The one-time key: chacha_crypt of 32 bytes of the zero page ***)

  ARM_STEPS_TAC CE_EXEC (33--41) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(zpa,val(word 32:int64))) s41 =
    num_of_bytelist(REPLICATE 32 (word 0:byte)) /\
    read (memory :> bytes(zpa,32)) s41 =
    num_of_bytelist(REPLICATE 32 (word 0:byte)) /\
    LENGTH(REPLICATE 32 (word 0:byte)) = val(word 32:int64) /\
    val(word 32:int64) = 32 /\ 32 < 2 EXP 32 /\
    num_of_bytelist(REPLICATE 32 (word 0:byte)) = 0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NUM_OF_BYTELIST_REPLICATE_0; LENGTH_REPLICATE] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CE_CRYPT_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `chacha20_state key 0 nonce`; `REPLICATE 32 (word 0:byte)`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
    `read SP s`; `read X30 s`] 42 THEN
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if can (find_term (fun t -> try let n,_ = dest_const t in
              n = "chacha20_ctr" || n = "list_of_seq"
              with Failure _ -> false)) c
    then CONV_RULE NUM_REDUCE_CONV
          (REWRITE_RULE[CP_OTK; CHACHA20_CTR_STATE] th)
    else th) THEN

  (*** poly1305_init with the one-time key ***)

  ARM_STEPS_TAC CE_EXEC (43--45) THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,32) (chacha20_block key 0 nonce)) = 32`
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; CP_LENGTH_CHACHA20_BLOCK] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CE_INIT_TAC
   [`read X0 s`; `read X1 s`; `SUB_LIST(0,32) (chacha20_block key 0 nonce)`;
    `pc:num`; `read SP s`; `read X30 s`] 46 THEN
  CP_DESC_EXPAND_TAC [] `s46:armstate` THEN

  (*** poly1305_update with the ad ***)

  ARM_STEPS_TAC CE_EXEC (47--50) THEN
  MP_TAC(SPEC `adlen:int64` CP_ZX_ZX) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(adlen:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  CP_DESC_FOLD_TAC [] `[]:byte list` `s50:armstate` THEN
  CE_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; `[]:byte list`;
    `al:byte list`; `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] 51 THEN
  CP_DESC_EQ_TAC (ISPEC `al:byte list` (CONJUNCT1 APPEND)) `s51:armstate` THEN
  CP_DESC_EXPAND_TAC [] `s51:armstate` THEN
  ARM_STEPS_TAC CE_EXEC (52--53);;

(* The padding of the ad: none (the absorbed bytes being rewritten as al     *)
(* with the empty padding), or by poly1305_update from the zero page; then   *)
(* 0x611c is reached at step 53 or 60.                                       *)

let CE_PAD1Z_TAC =
  WG_PC_REWRITE_TAC[CP_AND15; ASSUME `val(adlen:int64) MOD 16 = 0`] THEN
  CP_DESC_FOLD_TAC [] `al:byte list` `s53:armstate` THEN
  SUBGOAL_THEN (mk_eq(`al:byte list`,cp_d2)) ASSUME_TAC THENL
   [MP_TAC(SPEC `val(adlen:int64)` CP_PAD_Z) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  CP_DESC_EQ_TAC (ASSUME (mk_eq(`al:byte list`,cp_d2))) `s53:armstate` THEN
  CP_D2_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cp_d2_lens ()) `s53:armstate`);;

let CE_PAD1N_TAC =
  WG_PC_REWRITE_TAC[CP_AND15; ASSUME `~(val(adlen:int64) MOD 16 = 0)`] THEN
  ARM_STEPS_TAC CE_EXEC (54--58) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CP_PADLEN_WORD]) THEN
  CP_PAD_FACTS_TAC `val(adlen:int64)` `s58:armstate` THEN
  CP_DESC_FOLD_TAC [] `al:byte list` `s58:armstate` THEN
  CE_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; `al:byte list`;
    `poly1305_pad16 (val(adlen:int64))`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] 59 THEN
  CP_D2_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (cp_d2_lens ()) `s59:armstate`) THEN
  ARM_STEPS_TAC CE_EXEC [60];;

(* ------------------------------------------------------------------------- *)
(* From 0x611c (step k): chacha_crypt of the plaintext into dst from block 1 *)
(* and poly1305_update with the ciphertext, up to the test of src_len & 15.  *)
(* ------------------------------------------------------------------------- *)

let CE_PART2_TAC k =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in
  ARM_STEPS_TAC CE_EXEC ((k+1)--(k+6)) THEN
  MP_TAC(SPEC `len:int64` CP_ZX_ZX) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN
   `(dst:int64 = src \/
     nonoverlapping (dst,val(len:int64)) (src:int64,val len)) /\
    val(len:int64) < 2 EXP 32`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
       [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        DISJ2_TAC THEN NONOVERLAPPING_TAC];
      UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC];
    ALL_TAC] THEN
  CE_CRYPT_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `chacha20_state key 1 nonce`; `pl:byte list`;
    `mset:int64`; `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
    `read SP s`; `read X30 s`] (k+7) THEN
  MP_TAC(ISPECL [`key:byte list`; `nonce:byte list`; `pl:byte list`;
                 `val(len:int64)`] CP_ENC) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARM_STEPS_TAC CE_EXEC ((k+8)--(k+11)) THEN
  MP_TAC(SPEC `len:int64` CP_ZX_ZX) THEN ANTS_TAC THENL
   [UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,ce_c),`val(len:int64)`))
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CP_LENGTH_ENC]; ALL_TAC] THEN
  W(fun _ -> CP_DESC_FOLD_TAC (cp_d2_lens ()) cp_d2 (sk(k+11))) THEN
  CE_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; cp_d2; ce_c;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] (k+12) THEN
  CE_D3_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (ce_d3_lens ()) (sk(k+12))) THEN
  ARM_STEPS_TAC CE_EXEC ((k+13)--(k+14));;

(* The padding of the ciphertext (from step j), reaching 0x614c at step j    *)
(* or j + 7.                                                                 *)

let CE_PAD2Z_TAC j =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in
  WG_PC_REWRITE_TAC[CP_AND15; ASSUME `val(len:int64) MOD 16 = 0`] THEN
  W(fun _ -> CP_DESC_FOLD_TAC (ce_d3_lens ()) ce_d3 (sk j)) THEN
  SUBGOAL_THEN (mk_eq(ce_d3,ce_d4)) ASSUME_TAC THENL
   [MP_TAC(SPEC `val(len:int64)` CP_PAD_Z) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  CP_DESC_EQ_TAC (ASSUME (mk_eq(ce_d3,ce_d4))) (sk j) THEN
  CE_D4_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (ce_d4_lens ()) (sk j));;

let CE_PAD2N_TAC j =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in
  WG_PC_REWRITE_TAC[CP_AND15; ASSUME `~(val(len:int64) MOD 16 = 0)`] THEN
  ARM_STEPS_TAC CE_EXEC ((j+1)--(j+5)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CP_PADLEN_WORD]) THEN
  CP_PAD_FACTS_TAC `val(len:int64)` (sk(j+5)) THEN
  W(fun _ -> CP_DESC_FOLD_TAC (ce_d3_lens ()) ce_d3 (sk(j+5))) THEN
  CE_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; ce_d3;
    `poly1305_pad16 (val(len:int64))`; `mcpy:int64`; `ea2:int64`;
    `el2:num`; `ev2:num`; `pc:num`; `read SP s`; `read X30 s`] (j+6) THEN
  CE_D4_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (ce_d4_lens ()) (sk(j+6))) THEN
  ARM_STEPS_TAC CE_EXEC [j+7];;

(* ------------------------------------------------------------------------- *)
(* From 0x614c (step j): the lengths, poly1305_final into dst + src_len (as  *)
(* the variable dtag, as the nonoverlapping facts for it are proved here),   *)
(* memzero_explicit of the state, and the result.                            *)
(* ------------------------------------------------------------------------- *)

let CE_X1_TAC s =
  FIRST_X_ASSUM(fun th ->
    if concl th = mk_eq(mk_comb(`read X1`,s),`word_add (dst:int64) len`)
    then ASSUME_TAC(TRANS th (AP_TERM `word_add (dst:int64)`
                               (SYM(ISPEC `len:int64` WORD_VAL))))
    else failwith "CE_X1_TAC");;

let CE_TAG_FACTS_TAC =
  let tms = [`nonoverlapping (dst:int64,val(len:int64) + 16)
                             (word_add stackpointer (word 376):int64,280)`;
             `nonoverlapping (dst:int64,val(len:int64) + 16)
                             (word pc:int64,29472)`;
             `nonoverlapping (dst:int64,val(len:int64) + 16) (ea1:int64,el1)`;
             `nonoverlapping (dst:int64,val(len:int64) + 16)
                             (word(pc + 37016):int64,8)`;
             `nonoverlapping (dst:int64,val(len:int64) + 16)
                             (word_add stackpointer (word 208):int64,48)`;
             `nonoverlapping (dst:int64,val(len:int64) + 16)
                             (stackpointer:int64,656)`;
             `nonoverlapping (dst:int64,val(len:int64) + 16) (st:int64,64)`] in
  MAP_EVERY (fun t ->
    SUBGOAL_THEN t
     (fun th -> STRIP_ASSUME_TAC(MATCH_MP CP_TAG_NONOVERLAP
                  (REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)))
    THENL [NONOVERLAPPING_TAC; ALL_TAC]) tms THEN
  MP_TAC(SPECL [`dst:int64`; `val(len:int64)`] CP_TAG_DST) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `val(len:int64) + 16 < 2 EXP 32` THEN ARITH_TAC;
    STRIP_TAC];;

let CE_DTAG_TAC =
  X_CHOOSE_TAC `dtag:int64`
   (prove(`?dtag:int64. word_add dst (word(val(len:int64))) = dtag`,
          MESON_TAC[])) THEN
  RULE_ASSUM_TAC(fun th ->
    if concl th = `word_add (dst:int64) (word(val(len:int64))) = dtag` then th
    else REWRITE_RULE
          [ASSUME `word_add (dst:int64) (word(val(len:int64))) = dtag`] th);;

let CE_FINAL_CALL_TAC n (asl,w as gl) =
  let facts = mapfilter (fun (_,th) ->
     if can (find_term ((=) `dtag:int64`)) (concl th) &&
        (try fst(dest_const(repeat rator (concl th))) = "nonoverlapping_modulo"
         with Failure _ -> false)
     then th else failwith "") asl in
  let th1 = SPECL
    [`word_add stackpointer (word 376):int64`; `dtag:int64`;
     `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; ce_d5; `mset:int64`;
     `ea1:int64`; `el1:num`; `ev1:num`; `pc:num`;
     `word_add stackpointer (word 256):int64`; `word(pc + 24940):int64`]
    WIREGUARD_POLY1305_FINAL_GCC13_O2_IMAGE_SUBROUTINE_CORRECT in
  let th2 =
    REWRITE_RULE (ALL :: NONOVERLAPPING_CLAUSES :: facts)
     (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th1) in
  ARM_SUBROUTINE_SIM_TAC
   (wireguard_gcc13_O2_mc,CE_EXEC,0,wireguard_gcc13_O2_mc,th2) [] n gl;;

let CE_PART3_TAC j =
  let sk n = mk_var("s"^string_of_int n,`:armstate`) in

  (*** poly1305_update with the lengths ***)

  ARM_STEPS_TAC CE_EXEC ((j+1)--(j+5)) THEN
  MP_TAC(CP_ADDR_NORM_RULE(ISPECL [`word_add stackpointer (word 344):int64`;
                 `adlen:int64`; `len:int64`; sk(j+5)] CP_LENS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   (subst [ce_lens,`l:byte list`; sk(j+5),`s:armstate`]
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
  W(fun _ -> CP_DESC_FOLD_TAC (ce_d4_lens ()) ce_d4 (sk(j+5))) THEN
  CE_UPDATE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `SUB_LIST(0,32) (chacha20_block key 0 nonce)`; ce_d4; ce_lens;
    `mcpy:int64`; `ea2:int64`; `el2:num`; `ev2:num`;
    `pc:num`; `read SP s`; `read X30 s`] (j+6) THEN

  (*** poly1305_final into dst + src_len ***)

  CE_D5_LENS_TAC THEN
  W(fun _ -> CP_DESC_EXPAND_TAC (ce_d5_lens ()) (sk(j+6))) THEN
  ARM_STEPS_TAC CE_EXEC ((j+7)--(j+9)) THEN
  W(fun _ -> CP_DESC_FOLD_TAC (ce_d5_lens ()) ce_d5 (sk(j+9))) THEN
  CE_X1_TAC (sk(j+9)) THEN CE_TAG_FACTS_TAC THEN CE_DTAG_TAC THEN
  CE_FINAL_CALL_TAC (j+10) THEN

  (*** memzero_explicit of the ChaCha20 state, and the return ***)

  ARM_STEPS_TAC CE_EXEC ((j+11)--(j+14)) THEN
  WG_PLT_TAC CE_EXEC (j+14) THEN
  WG_CALL_TAC "memset" CE_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (j+19) THEN
  MEMSET_ZERO_BYTES_TAC THEN
  ARM_STEPS_TAC CE_EXEC ((j+20)--(j+27)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `word_add (dst:int64) (word(val(len:int64))) = dtag`)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CP_AEAD_EQ] THEN
  REWRITE_TAC[ASSUME `LENGTH(al:byte list) = val(adlen:int64)`;
              ASSUME `LENGTH(pl:byte list) = val(len:int64)`] THEN
  W(fun (asl,w) ->
    let s = rand(lhand w) in
    let tag = rand(rand(rand w)) in
    MP_TAC(ISPECL [`dst:int64`; ce_c; tag; `16`; s] WG_READ_BYTES_APPEND)) THEN
  REWRITE_TAC[ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,ce_c),
                           `val(len:int64)`))] THEN
  ASM_REWRITE_TAC[];;

let CE_REST_TAC k =
  CE_PART2_TAC k THEN
  ASM_CASES_TAC `val(len:int64) MOD 16 = 0` THENL
   [CE_PAD2Z_TAC (k+14) THEN CE_PART3_TAC (k+14);
    CE_PAD2N_TAC (k+14) THEN CE_PART3_TAC (k+21)];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_CHACHA20POLY1305_ENCRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
  (WIREGUARD_CHACHA20POLY1305_ENCRYPT_INNER_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
   CE_SETUP_TAC THEN CE_PART1_TAC THEN
   ASM_CASES_TAC `val(adlen:int64) MOD 16 = 0` THENL
    [CE_PAD1Z_TAC THEN CE_REST_TAC 53;
     CE_PAD1N_TAC THEN CE_REST_TAC 60]);;

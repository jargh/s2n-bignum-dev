(* ============================================================================
   Functional-correctness proof of the SLOTHY-scheduled shipping AES-GCM
   kernel aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S (swpS_mc),
   transferred from its de-interleaved sibling (_swp_deint) across the proven
   whole-function program equivalence.

   NB: this is the EQUIVALENCE-ROUTE correctness proof.  The CANONICAL correctness
   proof of this kernel is the DIRECT one in
   aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S.ml (a single
   mid-pipeline invariant, no program-equivalence detour).  This file is retained
   as an alternative development.

   Entry pc2+0x2c -> exit pc2+0x710, matching ..._SWP_DEINT_CORRECT.  Clean interface:
   the only precondition beyond the standard buffer-disjointness is a single
   problem-size bound (16 * val len_bits DIV 128 + 1856 <= 2 EXP 40) - no phantom
   code-location pc, no absolute-address facts (nonoverlapping is translation-invariant).

   This file is self-contained: it `needs` only the shared substrate proofs, then
   inlines the full development (formerly the DEVEL_swp_S_* / monolith_* fragments):

     base: _swp_deint proof  (aes_gcm_deint_mc, DEINT_EXEC, MERGE_CTR128_TAC,
             inv_tm/leg1_lc2_stmt/drain_gen_stmt, deint _CORRECT)
         + _swp_S_via_equiv.ml        (swpS_mc, the 6 whole-fn equivalences, POSTAMBLE
             apparatus, gti/graft_goal/trans_ helpers)
         + _swp_S_via_equiv_stageB.ml (POSTAMBLE_STRONG, STEADY_STRONG output-agreement equiv)

     stage C - deint standalone ensures_n legs at the 0x354 seam:
         FILL_N ++ STEADY_LOOP_N ++ DRAIN_N ++ DEINT_TAIL_N(_REM0) ++ LEG1_LC1_N/LC0_N
         -> DEINT_FROM88_N (deint ensures_n 0x88->0x710, all loop shapes)

     stage D - ENSURES_N_ENSURES2_CONJ + ENSURES2_ENSURES_N + ENSURES_N_ENSURES
         transfer (engine PROVE_SWPS_CORRECT_CASE) -> 8 SWP_S_CORRECT_* cases

     SWPS_FROM88 (combine 8 cases) ; HOLE_EXISTS + phantom-pc elimination ;
         toplevel _SWP_S_CORRECT (0x2c->0x710, clean single-size-bound interface).
   ============================================================================ *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

needs "arm/proofs/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_deint.ml";;
needs "arm/proofs/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S_via_equiv.ml";;
needs "arm/proofs/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S_via_equiv_stageB.ml";;

(* ---- Stage C: deint ensures_n legs (inv_tm/leg1_lc2_stmt/drain_gen_stmt come from the _swp_deint proof) ---- *)(* ===== FILL_N: deint ensures_n 0x88->0x354 (fill leg, @179) ===== *)
let FILL_N = prove(
 `!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       2 <= loop_count /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x354) /\
           read X0 s = word_add in_p (word (64 * 1)) /\
        read X2 s = word_add out_p (word (64 * 1)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * 1 + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word (loop_count - 1) /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * 1))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * 1
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])
      (\(s:armstate). 179)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4 <= nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
      UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`;
    ARITH_RULE `16 * 2 = 32`; ARITH_RULE `16 * 3 = 48`; WORD_ADD_0]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
    check (fun th -> let c = concl th in
      is_eq c && can (find_term (fun t -> t = `(memory :> bytes128 in_p)`)) (lhs c))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
    UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s1" None None) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word loop_count:int64) = loop_count`;
                             ASSUME `~(loop_count = 0)`; COND_CLAUSES]) THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (2--11) THEN
  MERGE_CTR128_TAC 192 "s11" THEN
  (ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s12" None None) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  MERGE_CTR128_TAC 176 "s12" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (13--19) THEN
  MERGE_CTR128_TAC 160 "s19" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (20--24) THEN
  MERGE_CTR128_TAC 208 "s24" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (25--31) THEN
  MERGE_CTR128_TAC 192 "s31" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (32--37) THEN
  MERGE_CTR128_TAC 208 "s37" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (38--88) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
    UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word loop_count:int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[VAL_WORD_SUB_CASES; th; VAL_WORD_1]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count - 1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s89" None None) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1`;
                             ASSUME `~(loop_count - 1 = 0)`; COND_CLAUSES]) THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (90--96) THEN
  MERGE_CTR128_TAC 176 "s96" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (97--116) THEN
  MERGE_CTR128_TAC 160 "s116" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (117--179) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 2) + n = 4 * i + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[(prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST))] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  DISCARD_STATE_TAC "s179" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  REWRITE_TAC[CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (INST [`0`,`i:num`] AES_CTR_BLOCK_RECONSTRUCT)] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  (*** peel pointer/counter conjuncts; the X1 conjunct word_sub(word loop_count)(word 1) =
   *** word(loop_count-1) needs the no-underflow fact (1<=loop_count), so give the peel a
   *** WORD_SUB branch guarded by ASM_ARITH. ***)
  REPEAT(CONJ_TAC THENL
   [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST ORELSE
    (CONV_TAC SYM_CONV THEN
     ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `2 <= loop_count ==> 1 <= loop_count`]);
    ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`cipherblock_0 = nist_cipher_block nonce rk inblock 0`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock 1`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock 2`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock 3`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (tag0:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `tag0:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;
Printf.printf "*** FILL_N proved? hyps=%d ***\n" (length(hyp FILL_N));;
(* ===== STEADY_LOOP_N: deint ensures_n steady loop 0x354->0x354 ===== *)
(* STEADY_LOOP_N (deint ensures_n steady loop @nsum178); inv_tm/leg1_lc2_stmt/drain_gen_stmt from deint file *)
let steady_pre =
  let _,body = strip_forall leg1_lc2_stmt in
  let ant,_ = dest_imp body in
  let cs = conjuncts ant in
  let cs' = List.concat_map (fun c -> if c = `2 <= loop_count` then [c; `~(loop_count = 2)`] else [c]) cs in
  list_mk_conj cs';;
let inv_at e = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(inv_tm,e))));;
let mk_leg pcexpr inve =
  mk_abs(`s:armstate`, list_mk_conj(
    [`aligned_bytes_loaded s (word pc) aes_gcm_deint_mc`;
     mk_eq(`read PC s`, mk_comb(`word:num->int64`, pcexpr))]
    @ conjuncts (rhs(concl(BETA_CONV(mk_comb(inve,`s:armstate`)))))));;
let steady_pre_state = mk_leg `pc + 0x354` (inv_at `0`);;
let steady_post_state = mk_leg `pc + 0x354` (inv_at `loop_count - 2`);;
let steady_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let steady_count = `\(s:armstate). nsum(0..(loop_count-2)-1)(\i. 178) + ((loop_count-2)-1)*0`;;
let steady_loop_goal = list_mk_forall(fst(strip_forall leg1_lc2_stmt), mk_imp(steady_pre,
   list_mk_icomb "ensures_n" [`arm`; steady_pre_state; steady_post_state; steady_frame; steady_count]));;

let STEADY_LOOP_N = prove(steady_loop_goal,

REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_N_WHILE_UP_TAC `loop_count - 2` `pc + 0x354` `pc + 0x354` inv_tm
    `\i:num. 178` `0` `0` `0` THEN
  ASM_REWRITE_TAC[htable_mem_4] THEN REPEAT CONJ_TAC THENL
   [(*** g1 ~(k=0) ***) UNDISCH_TAC `~(loop_count = 2)` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
    (*** g2 base ***) ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[htable_mem_4];
    (*** g3 BODY ***)
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+0))))) s0 = inblock (4*(i+1)+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+1))))) s0 = inblock (4*(i+1)+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+2))))) s0 = inblock (4*(i+1)+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*(i+1)+3))))) s0 = inblock (4*(i+1)+3)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4*(i+1)+3 < nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < loop_count - 2` THEN UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
      UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*(i+1)+0) = 64*(i+1)`;
    ARITH_RULE `16 * (4*(i+1)+1) = 64*(i+1)+16`;
    ARITH_RULE `16 * (4*(i+1)+2) = 64*(i+1)+32`;
    ARITH_RULE `16 * (4*(i+1)+3) = 64*(i+1)+48`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (1--10) THEN
  MERGE_CTR128_TAC 192 "s10" THEN
  (ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s11" None None) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  MERGE_CTR128_TAC 176 "s11" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (12--18) THEN
  MERGE_CTR128_TAC 160 "s18" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (19--23) THEN
  MERGE_CTR128_TAC 208 "s23" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (24--30) THEN
  MERGE_CTR128_TAC 192 "s30" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (31--36) THEN
  MERGE_CTR128_TAC 208 "s36" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (37--87) THEN
  SUBGOAL_THEN `val(word (loop_count - (i + 1)):int64) = loop_count - (i + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN
    UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_sub (word (loop_count - (i + 1))) (word 1):int64) = loop_count - (i + 1) - 1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word (loop_count - (i + 1)):int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[VAL_WORD_SUB_CASES; th; VAL_WORD_1]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count - (i + 1) - 1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC; ALL_TAC] THEN
  (ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s88" None None) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word (loop_count - (i + 1))) (word 1):int64) = loop_count - (i + 1) - 1`;
                             ASSUME `~(loop_count - (i + 1) - 1 = 0)`; COND_CLAUSES]) THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (89--95) THEN
  MERGE_CTR128_TAC 176 "s95" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (96--115) THEN
  MERGE_CTR128_TAC 160 "s115" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (116--178) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 * ((i+1) + 1) <=>
                          j < 4 * (i+1) \/ j = 4 * (i+1) \/ j = 4 * (i+1) + 1 \/
                          j = 4 * (i+1) + 2 \/ j = 4 * (i+1) + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * (i+1) + 2) + n = 4 * (i+1) + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
  DISCARD_STATE_TAC "s178" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** The 4 TAG keystream blocks have counters 4*i+6..9; AES_CTR_BLOCK_RECONSTRUCT needs the
   *** counter in `?+2` shape to fire, so present them as (4*i+4..7)+2, fold, THEN normalize the
   *** resulting block indices (and sofar's list length) to a single canonical flat 4*i+N so the
   *** ABBREVs below catch BOTH the machine-LHS blocks and the RHS uniformly (else block0 / sofar
   *** leak inblock/nonce/rk/tag0 into the karatsuba BITBLAST and blow it up). ***)
  REWRITE_TAC[ARITH_RULE `4*i+6 = (4*i+4)+2`; ARITH_RULE `4*i+7 = (4*i+5)+2`;
              ARITH_RULE `4*i+8 = (4*i+6)+2`; ARITH_RULE `4*i+9 = (4*i+7)+2`] THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  (*** canonicalize all block indices to flat 4*i+N (kills the (4*i+4)+2 / 4*(i+1)+0 variants) ***)
  REWRITE_TAC[ARITH_RULE `(4*i+4)+2 = 4*i+6`; ARITH_RULE `(4*i+5)+2 = 4*i+7`;
              ARITH_RULE `4*(i+1)+0 = 4*i+4`; ARITH_RULE `4*(i+1) = 4*i+4`;
              ARITH_RULE `4*(i+1)+1 = 4*i+5`; ARITH_RULE `4*(i+1)+2 = 4*i+6`;
              ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  (*** X1's next value is a DOUBLE decrement: word_sub(if i+1<=loop_count then
   *** word_sub(word loop_count)(word(i+1)) else 0)(word 1) = if i+2<=loop_count then
   *** word_sub(word loop_count)(word(i+2)) else 0.  Resolve both CONDs (i<loop_count-2) then
   *** the word_sub-of-word_sub identity. ***)
  TRY(SUBGOAL_THEN `i + 1 <= loop_count /\ i + 2 <= loop_count` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC; ALL_TAC]) THEN
  REPEAT(CONJ_TAC THENL
   [CONV_TAC WORD_RULE ORELSE
    (ASM_REWRITE_TAC[] THEN
     TRY(REWRITE_TAC[WORD_RULE `word_sub (word_sub x (word a)) (word 1) = word_sub x (word(a+1))`]) THEN
     TRY(REWRITE_TAC[ARITH_RULE `(i+1)+1 = i+2`]) THEN TRY(CONV_TAC WORD_RULE));
    ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i + 4)))`;
    `cipherblock_0 = nist_cipher_block nonce rk inblock (4*i+4)`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock (4*i+5)`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock (4*i+6)`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock (4*i+7)`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `sofar:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  EXPAND_TAC "sofar" THEN
  (*** RHS tag index is (4*i+6)+2 (the machine's last-block counter form); canonicalize to flat
   *** 4*i+8 = SUC^4(4*i+4); list_of_seq(4*i+8) = APPEND (list_of_seq(4*i+4)) [the 4 blocks]. ***)
  REWRITE_TAC[ARITH_RULE `(4*i+6)+2 = 4*i+8`] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4*i+8 = SUC(SUC(SUC(SUC(4*i+4))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL];
    (*** g4 back-edge (0-step identity, pc1=pc2) ***) REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
      ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[htable_mem_4];
    (*** g5 post ***)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[htable_mem_4];
    (*** g6 count-eq ***) REWRITE_TAC[ADD_CLAUSES]]);;
Printf.printf "*** STEADY_LOOP_N proved? hyps=%d ***\n" (length(hyp STEADY_LOOP_N));;
(* ===== DRAIN_N: deint ensures_n 0x354->0x61c (drain leg, @178) ===== *)
(* DRAIN_N (deint ensures_n 0x354->0x61c @178); inv_tm/leg1_lc2_stmt/drain_gen_stmt from deint file *)
let drain_n_goal =
  let vs,body = strip_forall drain_gen_stmt in
  let ant,ccl = dest_imp body in
  let f,eargs = strip_comb ccl in
  let arm_t,pre,post,frame = el 0 eargs, el 1 eargs, el 2 eargs, el 3 eargs in
  list_mk_icomb "ensures_n" [arm_t; pre; post; frame; `\(s:armstate). 178`] |> fun c ->
  list_mk_forall(vs, mk_imp(ant, c));;

let DRAIN_N = prove(drain_n_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   (*** g5 DRAIN: A_last (produce group (loop_count-2)+1) ; reduce_last -> bridge 0x61c.
    *** Set m = loop_count-2 so the state is g3-shaped (group m+1); loop_count = m+2. ***)
   RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
   ENSURES_INIT_TAC "s0" THEN
   ABBREV_TAC `m = loop_count - 2` THEN
   SUBGOAL_THEN `loop_count = m + 2` ASSUME_TAC THENL
    [EXPAND_TAC "m" THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+0))))) s0 = inblock (4*(m+1)+0) /\
     read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+1))))) s0 = inblock (4*(m+1)+1) /\
     read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+2))))) s0 = inblock (4*(m+1)+2) /\
     read (memory :> bytes128 (word_add in_p (word (16 * (4*(m+1)+3))))) s0 = inblock (4*(m+1)+3)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*(m+1)+3 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `loop_count = m + 2` THEN
       ARITH_TAC;
       ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   (*** Simplify X1 s0 = word(loop_count-(m+1)) to word 1 WITHOUT destroying loop_count=m+2:
    *** rewrite only the X1 read, using loop_count=m+2 then (m+2)-(m+1)=1. ***)
   FIRST_X_ASSUM(fun th -> if can (term_match [] `read X1 s0 = word (loop_count - (m+1))`) (concl th)
     then ASSUME_TAC(REWRITE_RULE[ASSUME `loop_count = m + 2`; ARITH_RULE `(m + 2) - (m + 1) = 1`] th)
     else NO_TAC) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*(m+1)+0) = 64*(m+1)`;
     ARITH_RULE `16 * (4*(m+1)+1) = 64*(m+1)+16`;
     ARITH_RULE `16 * (4*(m+1)+2) = 64*(m+1)+32`;
     ARITH_RULE `16 * (4*(m+1)+3) = 64*(m+1)+48`]) THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in
       is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (1--10) THEN
   MERGE_CTR128_TAC 192 "s10" THEN
   (ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s11" None None) THEN
   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
   MERGE_CTR128_TAC 176 "s11" THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (12--18) THEN
   MERGE_CTR128_TAC 160 "s18" THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (19--23) THEN
   MERGE_CTR128_TAC 208 "s23" THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (24--30) THEN
   MERGE_CTR128_TAC 192 "s30" THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (31--36) THEN
   MERGE_CTR128_TAC 208 "s36" THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (37--88) THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (89--95) THEN
   MERGE_CTR128_TAC 176 "s95" THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (96--115) THEN
   MERGE_CTR128_TAC 160 "s115" THEN
   MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
     DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (116--178) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (*** the POST is the bridge (uses loop_count); rewrite loop_count->m+2 in the GOAL so it aligns
   *** with the machine's m+1 forms (4*loop_count = 4*(m+2) = 4*((m+1)+1)). ***)
  FIRST_ASSUM(fun th -> if concl th = `loop_count = m + 2` then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE `4 * (m + 2) = 4 * ((m+1) + 1)`;
              ARITH_RULE `64 * (m + 2) = 64 * ((m+1) + 1)`;
              ARITH_RULE `(m + 2) - (m + 1) = 1`; ARITH_RULE `(m + 2) - (m + 2) = 0`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 * ((m+1) + 1) <=>
                          j < 4 * (m+1) \/ j = 4 * (m+1) \/ j = 4 * (m+1) + 1 \/
                          j = 4 * (m+1) + 2 \/ j = 4 * (m+1) + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * m = 64 * m`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * (m+1) + 2) + n = 4 * (m+1) + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `m < l ==> m + 1 <= l`] THEN
  DISCARD_STATE_TAC "s178" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** The 4 TAG keystream blocks have counters 4*m+6..9; AES_CTR_BLOCK_RECONSTRUCT needs the
   *** counter in `?+2` shape to fire, so present them as (4*m+4..7)+2, fold, THEN normalize the
   *** resulting block indices (and sofar's list length) to a single canonical flat 4*m+N so the
   *** ABBREVs below catch BOTH the machine-LHS blocks and the RHS uniformly (else block0 / sofar
   *** leak inblock/nonce/rk/tag0 into the karatsuba BITBLAST and blow it up). ***)
  REWRITE_TAC[ARITH_RULE `4*m+6 = (4*m+4)+2`; ARITH_RULE `4*m+7 = (4*m+5)+2`;
              ARITH_RULE `4*m+8 = (4*m+6)+2`; ARITH_RULE `4*m+9 = (4*m+7)+2`] THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  (*** canonicalize all block indices to flat 4*m+N (kills the (4*m+4)+2 / 4*(m+1)+0 variants) ***)
  REWRITE_TAC[ARITH_RULE `(4*m+4)+2 = 4*m+6`; ARITH_RULE `(4*m+5)+2 = 4*m+7`;
              ARITH_RULE `4*(m+1)+0 = 4*m+4`; ARITH_RULE `4*(m+1) = 4*m+4`;
              ARITH_RULE `4*(m+1)+1 = 4*m+5`; ARITH_RULE `4*(m+1)+2 = 4*m+6`;
              ARITH_RULE `4*(m+1)+3 = 4*m+7`] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  (*** X1's next value is a DOUBLE decrement: word_sub(if m+1<=loop_count then
   *** word_sub(word loop_count)(word(m+1)) else 0)(word 1) = if m+2<=loop_count then
   *** word_sub(word loop_count)(word(m+2)) else 0.  Resolve both CONDs (m<loop_count-2) then
   *** the word_sub-of-word_sub identity. ***)
  TRY(SUBGOAL_THEN `m + 1 <= loop_count /\ m + 2 <= loop_count` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `m < loop_count - 2` THEN ARITH_TAC; ALL_TAC]) THEN
  REPEAT(CONJ_TAC THENL
   [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST ORELSE
    (ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_RULE `word_sub (word_sub x (word a)) (word 1) = word_sub x (word(a+1))`;
                 ARITH_RULE `(m+1)+1 = m+2`]);
    ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * m + 4)))`;
    `cipherblock_0 = nist_cipher_block nonce rk inblock (4*m+4)`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock (4*m+5)`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock (4*m+6)`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock (4*m+7)`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `sofar:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  EXPAND_TAC "sofar" THEN
  (*** RHS tag index is (4*m+6)+2 (the machine's last-block counter form); canonicalize to flat
   *** 4*m+8 = SUC^4(4*m+4); list_of_seq(4*m+8) = APPEND (list_of_seq(4*m+4)) [the 4 blocks]. ***)
  REWRITE_TAC[ARITH_RULE `(4*m+6)+2 = 4*m+8`] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4*m+8 = SUC(SUC(SUC(SUC(4*m+4))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;
Printf.printf "*** DRAIN_N proved? hyps=%d ***\n" (length(hyp DRAIN_N));;
(* ===== DEINT_TAIL_N: deint ensures_n 0x61c->0x710 (remainder loop + finalize, lr>=1) ===== *)
let DEINT_TAIL_N = prove(
 `!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       16 * nblocks < 2 EXP 64 /\
       1 <= loop_remain /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x61c) /\
           read X0 s = word_add in_p (word (64 * loop_count)) /\
           read X2 s = word_add out_p (word (64 * loop_count)) /\
           read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
           read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
           read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
           read X16 s = word loop_remain /\
           read Q30 s = byteswap128
               (nist_ghash (aes128_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
           (!j. j < 4 * loop_count
                ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < nblocks
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) nblocks)) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nblocks + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])
      (\(s:armstate). 4 + (nsum(0..loop_remain-1)(\i. 51) + (loop_remain-1)*1) + 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** loop_remain = 0: no tail iterations, just the finalize (ivec/tag writeback) ***)
  SUBGOAL_THEN `~(loop_remain = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (*** loop_remain >= 1: tail loop via ENSURES_WHILE (0x62c head, 0x6f8 back-edge) ***)
  ENSURES_N_WHILE_UP_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6f8`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
      read SP s = stackpointer /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
      read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
      read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
      read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
      read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
      read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
      read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
      read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
      read Q7 s = word 13979173243358019584 /\
      read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
      read X12 s = word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
      read X13 s = word_zx (word (4 * loop_count + i + 2):int32):int64 /\
      read X15 s = word(len_bits DIV 8) /\ read X16 s = word(loop_remain - i) /\
      read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block nonce rk j) (inblock j))`
    `\i:num. 51` `4` `1` `6` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [(*** base case: bridge 0x61c -> 0x62c, i=0 ***)
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
          DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (1--3) THEN
    (ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s4" None None) THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),Var("s4",_))),
             Comb(Comb(Comb(Const("COND",_),_),_),_)) ->
          ASSUME_TAC(REWRITE_RULE[ASSUME `val(word loop_remain:int64) = loop_remain`;
                                  ASSUME `~(loop_remain = 0)`; COND_CLAUSES] th)
      | _ -> NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** loop body: 0x62c -> 0x6f8, one block; Inv(i) -> Inv(i+1) ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
      check (fun th -> let c = concl th in
        is_eq c && free_in `in_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))) THEN
    (*** store-in-region bound: needed so the output store's write-preservation fires ***)
    SUBGOAL_THEN `4 * loop_count + i < nblocks` ASSUME_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
        [`i < loop_remain`; `nblocks MOD 4 = loop_remain`; `nblocks DIV 4 = loop_count`] THEN
      ARITH_TAC; ALL_TAC] THEN
    (*** step the body; MERGE at STORE states s5 (counter) and s28 (scalar_rk round-trip) ***)
    MAP_EVERY(fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN SUBWORD_NONFORALL THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (1--5) THEN
    MERGE_CTR128_TAC 160 "s5" THEN
    MAP_EVERY(fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN SUBWORD_NONFORALL THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (6--28) THEN
    MERGE_CTR128_TAC 160 "s28" THEN
    MAP_EVERY(fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN SUBWORD_NONFORALL THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (29--51) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** discharge the output-region forall FIRST, while the MAYCHANGE frame is live ***)
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    (*** counter + scalar_rk + AES-CTR reconstruction ***)
    REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
    REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s51" THEN
    REWRITE_TAC[ADD_ASSOC; ARITH] THEN
    REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
    REWRITE_TAC[GSYM cipher_block] THEN
    REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    (*** fold the spelled-out round-key list back to `rk` (deint's AES reconstruction     ***)
    (*** re-expands it), using the lemma's first hypothesis [EL 0 rk;..] = rk.             ***)
    FIRST_ASSUM(fun th -> if can (term_match []
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    (*** the goal is a conjunction of pointer/counter eqs (WORD_RULE-closable) followed by  ***)
    (*** the GHASH tag equation; peel the WORD_RULE ones, then settle the tag.              ***)
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
    `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
     word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count + i)))`;
      `cipherblock = nist_cipher_block nonce rk inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3 (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND; NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** trivial loop-back: 0x6f8 test taken.  The back-branch test is                ***)
    (*** cbnz on X16 = word(loop_remain - i); ARM_SIM leaves the residual PC as        ***)
    (*** (if ~(word loop_remain = word i) then loop-top else exit) = loop-top, so we   ***)
    (*** must show ~(word loop_remain = word i).  Unlike the counter-decrement form,   ***)
    (*** this compares loop_remain and i directly, so we need val(word loop_remain) =  ***)
    (*** loop_remain (from loop_remain = nblocks MOD 4 < 4 < 2^64) before GSYM VAL_EQ. ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES_GCM_DEINT_EXEC [1] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_ARITH_TAC;

    (*** finalize: 0x6f8 test not taken -> ivec/tag writeback -> 0x710 ***)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
          DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST]);;
Printf.printf "*** DEINT_TAIL_N proved? hyps=%d ***\n" (length(hyp DEINT_TAIL_N));;
(* ===== DEINT_TAIL_N_REM0: deint ensures_n tail, loop_remain=0 (9-step finalize) ===== *)
(* DEINT_TAIL_N_REM0: the loop_remain=0 finalize leg (0x61c->0x710, 9 steps) as ensures_n.
   The deint-side tail for the REM0 case (cbz taken, no remainder loop - just ivec/tag writeback).
   Transformed from the deint DEINT_TAIL proof's `loop_remain=0` branch (deint proof lines 833-855).
   Load in the deint stepper context (head-746 prefix + equiv.ml) after DEINT_TAIL_N (for the pre/post shapes).

   Precond = DEINT_TAIL_N's pre at loop_remain:=0 (0x61c entry, X1=X16=word 0, Q30=ghash(4*loop_count)).
   Postcond = deint final @0x710 (tag=word_reversefields 8 (nist_ghash..nblocks), ivec=ctr_block(nblocks+2)).
   Antecedent = DEINT_TAIL_N's ant with `1 <= loop_remain` DROPPED, loop_remain:=0.  Count = \s.9.

   ENDING: unlike FILL_N/DEINT_TAIL_N (whose finalize WORD_BLAST closes because the frame was already
   consumed), here ENSURES_FINAL_STATE_TAC leaves the MAYCHANGE frame as the LAST conjunct alongside the
   tag/ivec word-algebra.  So after the recon convs: REPEAT CONJ_TAC THEN FIRST[WORD_BLAST (word-algebra
   conjuncts); frame-closer (REWRITE[ABI] + MP the live per-step MAYCHANGE + MONOTONE_MAYCHANGE_TAC)]. *)

let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let frame_of th = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let ant_of th = fst(dest_imp(snd(strip_forall(concl th))));;
let tail_pre_lr0 = subst[`0`,`loop_remain:num`] (pre_of DEINT_TAIL_N);;
let ant_lr0 = subst[`0`,`loop_remain:num`]
  (list_mk_conj (filter (fun t -> not(aconv t `1 <= loop_remain`)) (conjuncts (ant_of DEINT_TAIL_N))));;
let rem0_tail_goal =
  list_mk_forall(fst(strip_forall(concl DEINT_TAIL_N)),
    mk_imp(ant_lr0,
      list_mk_icomb "ensures_n" [`arm`; tail_pre_lr0; subst[`0`,`loop_remain:num`](post_of DEINT_TAIL_N);
                                 subst[`0`,`loop_remain:num`](frame_of DEINT_TAIL_N); `\s:armstate. 9`]));;
let DEINT_TAIL_N_REM0 = prove(rem0_tail_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (fun th -> let c = concl th in
      is_eq c && free_in `ivec_p:int64` (lhs c) &&
      not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
      not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
  MAP_EVERY(fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
        DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(fun t ->
    if is_eq t && free_in `ivec_p:int64` (lhs t) &&
       not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
    then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[byteswap128; ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [ CONV_TAC WORD_BLAST;
          (REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
           REPEAT(FIRST_X_ASSUM(fun th -> if can(find_term(fun x->is_comb x &&
              (try fst(dest_const(rator(rator x)))="MAYCHANGE" with _->false)))(concl th)
              then MP_TAC th else NO_TAC)) THEN
           REWRITE_TAC[] THEN MONOTONE_MAYCHANGE_TAC) ]);;
Printf.printf "*** DEINT_TAIL_N_REM0 proven (0x61c->0x710 @9, lr=0 finalize), hyps=%d ***\n"
  (length(hyp DEINT_TAIL_N_REM0));;
(* ===== LEG1_LC1_N: deint ensures_n lc=1 body 0x88->0x61c ===== *)
let LEG1_LC1_N = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       loop_count = 1 /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,192) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,192) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,192) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,192) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
           read Q18 s = word_reversefields 8 (EL 0 rk) /\
           read Q19 s = word_reversefields 8 (EL 1 rk) /\
           read Q20 s = word_reversefields 8 (EL 2 rk) /\
           read Q21 s = word_reversefields 8 (EL 3 rk) /\
           read Q22 s = word_reversefields 8 (EL 4 rk) /\
           read Q23 s = word_reversefields 8 (EL 5 rk) /\
           read Q24 s = word_reversefields 8 (EL 6 rk) /\
           read Q25 s = word_reversefields 8 (EL 7 rk) /\
           read Q26 s = word_reversefields 8 (EL 8 rk) /\
           read Q27 s = word_reversefields 8 (EL 9 rk) /\
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word 2:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_deint_mc /\
           read PC s = word (pc + 0x61c) /\
           read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce 2):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce 2):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + 2):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])
      (\(s:armstate). 179)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  (*** derive the 4 group-0 input blocks from the nblocks-forall (nblocks >= 4) ***)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4 <= nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`;
    ARITH_RULE `16 * 2 = 32`; ARITH_RULE `16 * 3 = 48`; WORD_ADD_0]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
    check (fun th -> let c = concl th in
      is_eq c && can (find_term (fun t -> t = `(memory :> bytes128 in_p)`)) (lhs c))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (1--11) THEN
  MERGE_CTR128_TAC 192 "s11" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (12--12) THEN
  MERGE_CTR128_TAC 176 "s12" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (13--19) THEN
  MERGE_CTR128_TAC 160 "s19" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (20--24) THEN
  MERGE_CTR128_TAC 208 "s24" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (25--31) THEN
  MERGE_CTR128_TAC 192 "s31" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (32--37) THEN
  MERGE_CTR128_TAC 208 "s37" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (38--96) THEN
  MERGE_CTR128_TAC 176 "s96" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (97--116) THEN
  MERGE_CTR128_TAC 160 "s116" THEN
  MAP_EVERY (fun n -> ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] ("s"^string_of_int n) None None THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC ["s"^string_of_int n] false) (117--179) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `loop_count = 1` SUBST_ALL_TAC THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 2) + n = 4 * i + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[(prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST))] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  DISCARD_STATE_TAC "s179" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** loop_count=1 => the 4 blocks have LITERAL counters 2,3,4,5, so the symbolic     ***)
  (*** AES_CTR_BLOCK_RECONSTRUCT (pattern i+2) cannot fire; use its i=0 specialization. ***)
  REWRITE_TAC[CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
               (INST [`0`,`i:num`] AES_CTR_BLOCK_RECONSTRUCT)] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST; ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64)
             (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64)
                  (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64)
                  (word_subword y (64,64):int64):int128`) THEN
  (*** loop_count=1 => the GHASH accumulator is still tag0 (nist_ghash h tag0 [] = tag0), ***)
  (*** so there is no `sofar` to abbreviate: block 0 is word_xor tag0 cipherblock_0.       ***)
  MAP_EVERY ABBREV_TAC
   [`cipherblock_0 = nist_cipher_block nonce rk inblock 0`;
    `cipherblock_1 = nist_cipher_block nonce rk inblock 1`;
    `cipherblock_2 = nist_cipher_block nonce rk inblock 2`;
    `cipherblock_3 = nist_cipher_block nonce rk inblock 3`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor
        (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor
        (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor
        (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (tag0:int128) cipherblock_0)
                   (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) =
      word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `tag0:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;
Printf.printf "*** LEG1_LC1_N proved? hyps=%d ***\n" (length(hyp LEG1_LC1_N));;
(* ===== LEG1_LC0_N: deint ensures_n lc=0 head (@1, cbz taken) ===== *)
(* LEG1_LC0_N: deint ensures_n 0x88->0x61c for loop_count=0 (@1 step).  For lc=0 the cbz@0x88 is
   taken straight to 0x61c (nothing produced; nist_ghash []=tag0, Q30=byteswap128 tag0, X0=in_p+64*0).
   Transformed (trivially) from the deint DEINT_FROM88 assembly's loop_count=0 branch (source ~2348-2355).
   Load in the deint stepper context after LEG1_LC1_N (for the parametric pre/post shapes).

   Goal: entry = LEG1_LC1_N.pre[lc:=0], post = LEG1_LC1_N.post[lc:=0], ant = LEG1_LC1_N ant with
   loop_count=1 -> loop_count=0, count = \s.1.  Proof: SUBST loop_count=0, unfold htable, ENSURES_INIT,
   1 ARM_N_STEP, ENSURES_FINAL, ASM_REWRITE with [htable_mem_4;MULT/ADD_CLAUSES;WORD_ADD_0;list_of_seq;
   nist_ghash] + CONJUNCT1 LT (the j<0 output-forall is vacuous). *)
let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let cframe = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl LEG1_LC1_N)))))));;
let leg1_ant = fst(dest_imp(snd(strip_forall(concl LEG1_LC1_N))));;
let lc0_ant = list_mk_conj (map (fun t -> if aconv t `loop_count = 1` then `loop_count = 0` else t) (conjuncts leg1_ant));;
let leg1_lc0_goal = list_mk_forall(fst(strip_forall(concl LEG1_LC1_N)),
  mk_imp(lc0_ant, list_mk_icomb "ensures_n" [`arm`; subst[`0`,`loop_count:num`](pre_of LEG1_LC1_N);
     subst[`0`,`loop_count:num`](post_of LEG1_LC1_N); cframe; `\s:armstate. 1`]));;
let LEG1_LC0_N = prove(leg1_lc0_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) `loop_count = 0` then SUBST_ALL_TAC th else NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_N_STEP_TAC AES_GCM_DEINT_EXEC [] "s1" None None THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[htable_mem_4; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; list_of_seq; nist_ghash] THEN
  REWRITE_TAC[CONJUNCT1 LT]);;
Printf.printf "*** LEG1_LC0_N proven (0x88->0x61c @1, lc=0), hyps=%d ***\n" (length(hyp LEG1_LC0_N));;

(* REMAINING for the lc=0 CORRECT cases: the equiv-side LC0_*_STRONG.  BLOCKER: gti HEAD_LC0_G throws
   "dest_comb: not a combination" - the lc=0 head leg (HEAD_LC0_G) has a DIFFERENT pre/post structure
   than the STEADY/lc1 legs (its pre isn't the flat entry88 conjunction; it has exists-guards / the
   `?a. bignum..` whole-buffer form), so the generic f_tagivec graft (gti) doesn't apply.  Need either
   a HEAD_LC0-specific graft (adapt f_tagivec/FP_TAGIVEC_TAC to its post shape) OR compose the weak
   SWP_DEINT_SWPS_EQUIV_LC0_* with a separately-grafted tail.  Once LC0_REMPOS_STRONG / LC0_REM0_STRONG
   exist: dens = LEG1_LC0_N ++ [DEINT_TAIL_N | DEINT_TAIL_N_REM0] (seam by arith like lc=1), engine. *)
(* ===== DEINT_FROM88_N: compose the legs -> deint ensures_n 0x88->0x710 (all shapes) ===== *)
(* DEINT_FROM88_N: deint standalone ensures_n 0x88->0x710 for the STEADY case (lc>=3, lr>=1).
   Composes the 4 proven legs (FILL_N, STEADY_LOOP_N, DRAIN_N, DEINT_TAIL_N) via ENSURES_N_TRANS,
   collapses the C,,C,,C,,C frame to C via ENSURES_N_FRAME_SUBSUMED.  hyps=0.
   Count = 179 + nsum(0..lc-2-1)(178) + 178 + 4 + (nsum(0..lr-1)(51)+(lr-1)) + 6, which EQUALS f_n1
   (the equivalence's outer count) at all (lc,lr) - verified numerically; prove equality by NSUM+ARITH
   for the Stage-D transfer.
   Load after the 4 leg files (needs FILL_N, STEADY_LOOP_N, DRAIN_N, DEINT_TAIL_N bound + deint context). *)

let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let fill_ant = fst(dest_imp(snd(strip_forall(concl FILL_N))));;
let unified_pre = list_mk_conj(conjuncts fill_ant @ [`~(loop_count = 2)`; `1 <= loop_remain`]);;
let rawchain =
  let f=UNDISCH(SPEC_ALL FILL_N) and st=UNDISCH(SPEC_ALL STEADY_LOOP_N)
  and d=UNDISCH(SPEC_ALL DRAIN_N) and t=UNDISCH(SPEC_ALL DEINT_TAIL_N) in
  MATCH_MP ENSURES_N_TRANS (CONJ (MATCH_MP ENSURES_N_TRANS
     (CONJ (MATCH_MP ENSURES_N_TRANS (CONJ f st)) d)) t);;
let rawcount = last(snd(strip_comb(concl rawchain)));;
let cframe = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl FILL_N)))))));;
let sub_th = prove(list_mk_icomb "subsumed" [el 3 (snd(strip_comb(concl rawchain))); cframe],
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;
let deint_from88_n_goal = list_mk_forall(fst(strip_forall(concl FILL_N)), mk_imp(unified_pre,
   list_mk_icomb "ensures_n" [`arm`; pre_of FILL_N; post_of DEINT_TAIL_N; cframe; rawcount]));;

let DEINT_FROM88_N = prove(deint_from88_n_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let rec prove_conj t =
     if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else find (fun th -> aconv (concl th) t) asm_ths in
   let spec_leg leg =
     let ant = fst(dest_imp(snd(strip_forall(concl leg)))) in
     MP (SPEC_ALL leg) (prove_conj ant) in
   let f = spec_leg FILL_N and st = spec_leg STEADY_LOOP_N
   and d = spec_leg DRAIN_N and t = spec_leg DEINT_TAIL_N in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ (MATCH_MP ENSURES_N_TRANS
       (CONJ (MATCH_MP ENSURES_N_TRANS (CONJ f st)) d)) t) in
   ACCEPT_TAC (MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch))));;
Printf.printf "*** DEINT_FROM88_N proved, hyps=%d ***\n" (length(hyp DEINT_FROM88_N));;

(* Count reconciliation: DEINT_FROM88_N's count = f_n1 (the equivalence's outer count) under the
   STEADY hypotheses.  Needed for the Stage-D transfer (ENSURES_N_ENSURES2_CONJ wants deint's ensures_n
   at exactly f_n1).  Proof: derive 3<=loop_count from 2<=loop_count /\ ~(loop_count=2), then NSUM_CONST
   + ARITH. *)
let count_eq = prove(
  `2 <= loop_count /\ ~(loop_count = 2)
   ==> ((179 + nsum (0..loop_count - 2 - 1) (\i. 178) + (loop_count - 2 - 1) * 0) + 178) + 4 +
       (nsum (0..loop_remain - 1) (\i. 51) + (loop_remain - 1) * 1) + 6 =
       ((((89 + 0 + (nsum (0..loop_count - 1 - 1) (\i. 177) + (loop_count - 1 - 1 - 0) * 1) + 1) + 93) + 1) +
        0 + (nsum (0..loop_remain - 1) (\i. 51) + (loop_remain - 1 - 0) * 1) + 1) + 4 + 1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NSUM_CONST_NUMSEG] THEN
  SUBGOAL_THEN `loop_count - 1 - 1 = loop_count - 2` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> ((loop_count-2)-1)+1-0 = loop_count-2`] THEN
  ASM_ARITH_TAC);;
Printf.printf "*** count_eq (deint count = f_n1) proved ***\n";;

(* ---- Stage D: transfer engine + STEADY, then the other 7 cases ---- *)(* ===== Stage D transfer engine PROVE_SWPS_CORRECT_CASE + STEADY case (lc>=3,lr>=1) ===== *)
(* Stage D: transfer DEINT_FROM88_N (deint ensures_n) + STEADY_STRONG (equiv ensures2 with output
   agreement) -> swpS ensures (_swp_S CORRECT), STEADY case (loop_count>=3, loop_remain>=1).
   Load in the COMBINED session: deint prefix head-746 + equiv.ml + invdefs + 4 legs + DEINT_FROM88_N
   + count_eq (all deint side) THEN _swp_S.ml (equiv: deint_mc/swpS_mc/6 EQUIV theorems) THEN
   _swp_S_stageB.ml (STEADY_STRONG).  _swp_S.ml's htable_mem_4 new_definition is idempotent (returns
   the deint proof's cached def since identical); ctr_block etc. come from the deint prefix.

   STEP 1: bridge deint_mc = aes_gcm_deint_mc (both define_from_elf of swp_deint.o). *)
let MC_BRIDGE = prove(`aes_gcm_deint_mc = deint_mc`, REWRITE_TAC[aes_gcm_deint_mc; deint_mc]);;

(* STEP 2: rewrite DEINT_FROM88_N to (a) count = STEADY_STRONG's f_n1 (via count_eq), (b) deint_mc. *)
let ss_fn1 = el 4 (snd(strip_comb (concl STEADY_STRONG)));;
let df_body = snd(dest_abs (last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N)))))))));;
let goal_fn1 =
  let vs = fst(strip_forall(concl DEINT_FROM88_N)) in
  let ant = fst(dest_imp(snd(strip_forall(concl DEINT_FROM88_N)))) in
  let ens = snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N)))) in
  let a = snd(strip_comb ens) in
  list_mk_forall(vs, mk_imp(ant, list_mk_icomb "ensures_n" [el 0 a; el 1 a; el 2 a; el 3 a; ss_fn1]));;
let DEINT_FROM88_N_FN1 = prove(goal_fn1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(ss_fn1, mk_abs(`s:armstate`, df_body))) SUBST1_TAC THENL
   [ABS_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC count_eq THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DEINT_FROM88_N THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]);;
let DEINT_FROM88_N_D = REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_FN1;;

(* STEP 3: align variable names to the equivalence (in_p->in_b, out_p->out_b, htable_p->htab_b). *)
let DFD_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`] DEINT_FROM88_N_D;;

(* STEP 4: ENSURES_N_ENSURES2_CONJ - conjoin deint ensures_n into the equivalence ensures2. *)
let conj = MATCH_MP ENSURES_N_ENSURES2_CONJ (CONJ (UNDISCH DFD_ALIGNED) STEADY_STRONG);;
Printf.printf "*** Stage D step 4: conjoined ensures2 built, hyps=%d ***\n" (length(hyp conj));;

(* STEP 5: ENSURES2_ENSURES_N transfer.  Extract the swpS-side P2/Q2 (deint's OWN entry/post from
   DFD_ALIGNED, renamed pc->pc2, deint_mc->swpS_mc) and the factored frame C1/C2, discharge the 3
   side-conditions, then MATCH_MP to get swpS ensures_n @ f_n2.  STEP 6: ENSURES_N_ENSURES -> ensures. *)

(* Frame-factoring lemma: monomorphic (armstate) so the pair-slot types are pinned and SEQ_PAIR_SPLIT
   fires; the polymorphic SEQ_PAIR_SPLIT alone leaves type-var-polluted operands that won't unify. *)
let SEQ_PAIR_SPLIT_FN = prove(
  `!(P:armstate->armstate->bool) (Q:armstate->armstate->bool)
     (R:armstate->armstate->bool) (S:armstate->armstate->bool).
     ((\(s:armstate,s2:armstate) (s':armstate,s2':armstate). P s s' /\ Q s2 s2') ,,
      (\(s:armstate,s2:armstate) (s':armstate,s2':armstate). R s s' /\ S s2 s2'))
     = (\(s:armstate,s2:armstate) (s':armstate,s2':armstate). (P ,, R) s s' /\ (Q ,, S) s2 s2')`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN REWRITE_TAC[SEQ_PAIR_SPLIT]);;

let full_beta tm = rhs(concl(TOP_DEPTH_CONV GEN_BETA_CONV tm));;

(* Instantiate the transfer lemma with the swpS-side P2/Q2/C2.  ISPECL (not SPECL) so S:=armstate. *)
let r_P = ref `T` and r_Q = ref `T` and r_C = ref `T` and r_f1 = ref `T` and r_f2 = ref `T`
and r_P2 = ref `T` and r_Q2 = ref `T` and r_C2 = ref `T` and r_C1 = ref `T`;;
let () =
  let a = snd(strip_comb (concl conj)) in
  r_P := el 1 a; r_Q := el 2 a; r_C := el 3 a; r_f1 := el 4 a; r_f2 := el 5 a;
  (* P2/Q2 from DFD_ALIGNED's entry/post (deint naming, already in_b/out_b/htab_b), renamed to swpS. *)
  let sw = [`pc2:num`,`pc:num`; `swpS_mc:((8)word)list`,`deint_mc:((8)word)list`] in
  let ens = snd(dest_imp(concl DFD_ALIGNED)) in
  let ea = snd(strip_comb ens) in
  r_P2 := mk_abs(`s:armstate`, subst sw (snd(dest_abs (el 1 ea))));
  r_Q2 := mk_abs(`s:armstate`, subst sw (snd(dest_abs (el 2 ea))));;

(* Factor conj's frame C into deint-side C1 and swpS-side C2 (both bare armstate->armstate->bool). *)
let cfac_applied =
  let ap = list_mk_comb(!r_C, [`(s1:armstate,s2:armstate)`;`(s1':armstate,s2':armstate)`]) in
  (TOP_DEPTH_CONV GEN_BETA_CONV THENC TOP_DEPTH_CONV (REWR_CONV SEQ_PAIR_SPLIT_FN)
   THENC TOP_DEPTH_CONV GEN_BETA_CONV) ap;;
let () =
  let atoms = conjuncts(rhs(concl cfac_applied)) in
  let deint = filter (fun t -> vfree_in `s1:armstate` t || vfree_in `s1':armstate` t) atoms in
  let swps  = filter (fun t -> vfree_in `s2:armstate` t || vfree_in `s2':armstate` t) atoms in
  r_C1 := list_mk_abs([`a:armstate`;`b:armstate`], subst [`a:armstate`,`s1:armstate`;`b:armstate`,`s1':armstate`] (list_mk_conj deint));
  r_C2 := list_mk_abs([`a:armstate`;`b:armstate`], subst [`a:armstate`,`s2:armstate`;`b:armstate`,`s2':armstate`] (list_mk_conj swps));;

let e2en_inst = ISPECL [`arm`; !r_P; !r_Q; !r_C; !r_P2; !r_Q2; !r_C2; !r_f1; !r_f2] ENSURES2_ENSURES_N;;
let r_sideA = ref `T` and r_sideB = ref `T` and r_sideC = ref `T`;;
let () =
  let cs = conjuncts(fst(dest_imp(concl e2en_inst))) in
  r_sideA := el 1 cs; r_sideB := el 2 cs; r_sideC := el 3 cs;;

(* side B (postcond transfer): agreement (out/tag/ivec s1=s2) + deint functional post on s1 => swpS post s2 *)
let sideB_thm = prove(!r_sideB,
  REPEAT GEN_TAC THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY (GEN_TAC THEN DISCH_TAC) THEN ASM_MESON_TAC[]);;

(* side C (frame factoring): exists C1. C(...) <=> C1 s1 s1' /\ C2 s2 s2' - by the applied factoring. *)
let sideC_tm =
  mk_exists(`C1:armstate->armstate->bool`,
    list_mk_forall([`s1:armstate`;`s2:armstate`;`s1':armstate`;`s2':armstate`],
      mk_iff(list_mk_comb(!r_C, [`(s1:armstate,s2:armstate)`;`(s1':armstate,s2':armstate)`]),
             mk_conj(list_mk_comb(`C1:armstate->armstate->bool`,[`s1:armstate`;`s1':armstate`]),
                     list_mk_comb(!r_C2,[`s2:armstate`;`s2':armstate`])))));;
let sideC_thm = prove(sideC_tm,
  EXISTS_TAC !r_C1 THEN REPEAT GEN_TAC THEN REWRITE_TAC[cfac_applied] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC CONJ_ACI_RULE);;

(* side A (deint-entry exists given swpS entry): TODO - EXISTS interm_state (write deint_mc @ pc, PC=pc+136
   into the swpS state s2); all data inherited from s2 so cross-relations (mk_equiv_regs, input-equal) and
   deint88(s1) hold.  interm_state below; discharge via PROVE_CONJ_OF_EQ_READS-style read resolution. *)
let interm_state =
  `write (memory :> bytelist (word pc, LENGTH (deint_mc:((8)word)list)))
         deint_mc (write PC (word (pc+136)) s2)`;;
let LEN_DEINT = prove(`LENGTH (deint_mc:((8)word)list) = 1856`,
  REWRITE_TAC[GSYM MC_BRIDGE; fst AES_GCM_DEINT_EXEC]);;
let ALIGNED_INTERM = prove(
  `4 divides pc ==>
   aligned_bytes_loaded
     (write (memory :> bytelist (word pc, LENGTH (deint_mc:((8)word)list))) deint_mc (s:armstate))
     (word pc) deint_mc`,
  DISCH_TAC THEN
  REWRITE_TAC[aligned_bytes_loaded_word; DIVIDES_4_VAL_WORD_64; bytes_loaded] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC READ_OVER_WRITE_MEMORY_BYTELIST THEN REWRITE_TAC[LEN_DEINT] THEN ARITH_TAC);;
prove_conj_of_eq_reads_unfold_rules :=
  htable_mem_4 :: mk_equiv_regs :: LEN_DEINT ::
  (filter (fun th -> not(mem (concl th) [concl htable_mem_4; concl mk_equiv_regs; concl LEN_DEINT]))
          (!prove_conj_of_eq_reads_unfold_rules));;

(* ---- Side A: PROVEN (2026-07-30).  Given a swpS entry state s2, construct the deint entry state
   interm_state = (write deint_mc @ word pc; PC:=pc+136 into s2) and show it satisfies the conjoined
   entry predicate P (deint88 + swpS88 + cross-agreement + input-equal).  All data is inherited from
   s2 (only PC + the code page change), so the cross-relations/reads reduce to s2's.
   Needs 3 EXTRA preconds absent from the equivalence precond (legitimate; pc = deint's free code loc):
     4 divides pc ; nonoverlapping (htab_b,192)(word pc,1856) ; nonoverlapping (in_b,16*nblocks)(word pc,1856).
   MEMEQ (reduce a read-of-interm to the same read-of-s2) proves the reduce as a CLEAN sub-lemma with
   ONLY the relevant nonoverlap + bound facts as antecedents (zero ambient asms), then MP + ASM_REWRITE;
   this decouples READ_OVER_WRITE_ORTHOGONAL_TAC from the ~90-assumption pollution that made it throw. *)
let MEMEQ_CLEAN = W(fun (asl,w) ->
  let is_ir t = can (fun t -> if fst(dest_const(rator(rator t)))="read"
      && can(find_term(fun x->is_comb x && (try fst(dest_const(rator x))="write" with _->false)))(rand t)
      then () else failwith "") t in
  let ir = find_term is_ir w in
  let redeqn = mk_eq(ir, mk_comb(rator ir, `s2:armstate`)) in
  let asmtms = map (concl o snd) asl in
  let want t = is_comb t &&
     ((try fst(dest_const(fst(strip_comb t)))="nonoverlapping" with _->false)
      || (try fst(dest_const(fst(strip_comb t)))="<" with _->false)
      || (is_eq t && (try fst(dest_const(fst(strip_comb(rhs t))))="*" with _->false))) in
  let relevant = filter want asmtms in
  let red_lemma = prove(itlist (curry mk_imp) relevant redeqn,
      REPEAT DISCH_TAC THEN REWRITE_TAC[LEN_DEINT] THEN READ_OVER_WRITE_ORTHOGONAL_TAC) in
  MP_TAC red_lemma THEN REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN ASM_REWRITE_TAC[];;

let SIDEA_TAC =
  STRIP_TAC THEN X_GEN_TAC `s2:armstate` THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  EXISTS_TAC interm_state THEN
  REWRITE_TAC[mk_equiv_regs; BIGNUM_FROM_MEMORY_BYTES; htable_mem_4] THEN
  REPEAT CONJ_TAC THEN
  FIRST [
    (MATCH_MP_TAC ALIGNED_INTERM THEN FIRST_ASSUM ACCEPT_TAC);
    (GEN_TAC THEN DISCH_TAC THEN
     FIRST_X_ASSUM(fun th -> if is_forall(concl th) && vfree_in `inblock:num->int128` (concl th)
                             then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MEMEQ_CLEAN THEN NO_TAC);
    (W(fun (asl,w) -> let _,body = dest_exists w in
        let readC = rator(lhs(fst(dest_conj body))) in EXISTS_TAC (mk_comb(readC,`s2:armstate`)))
     THEN REWRITE_TAC[LEN_DEINT] THEN REPEAT CONJ_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC);
    (MEMEQ_CLEAN THEN NO_TAC);
    (PROVE_CONJ_OF_EQ_READS_TAC DEINT_EXEC THEN NO_TAC)
  ];;
let sideA_full = mk_imp(list_mk_conj
  (`4 divides pc` ::
   `nonoverlapping (htab_b:int64,192) (word pc:int64,1856)` ::
   `nonoverlapping (in_b:int64,16*nblocks) (word pc:int64,1856)` :: hyp conj), !r_sideA);;
let SIDEA = prove(sideA_full, SIDEA_TAC);;
Printf.printf "*** Stage D side A proved (hyps=%d) ***\n" (length(hyp SIDEA));;

(* STEP 6: assemble.  Note ENSURES2_ENSURES_N's C2 in e2en_inst must match sideC_thm's C2 (both from
   the SAME !r_C2 - rebuild r_sideC from e2en_inst then re-prove sideC to be safe). *)
let () = let cs = conjuncts(fst(dest_imp(concl e2en_inst))) in
         r_sideA := el 1 cs; r_sideB := el 2 cs; r_sideC := el 3 cs;;
let sideC_final = prove(!r_sideC,
  EXISTS_TAC !r_C1 THEN REPEAT GEN_TAC THEN REWRITE_TAC[cfac_applied] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC CONJ_ACI_RULE);;
let swpS_ens_n = MATCH_MP e2en_inst (CONJ conj (CONJ (UNDISCH SIDEA) (CONJ sideB_thm sideC_final)));;
let swpS_ensures = MATCH_MP ENSURES_N_ENSURES swpS_ens_n;;
(* clean closed theorem: forall params. preconds ==> ensures arm <swpS entry> <functional post> <frame> *)
let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_CORRECT_STEADY =
  GEN_ALL (itlist DISCH (rev(hyp swpS_ensures)) swpS_ensures);;
Printf.printf "*** _SWP_S CORRECT (STEADY case) PROVEN: hyps=%d, head=ensures, axiom-free ***\n"
  (length(hyp AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_CORRECT_STEADY));;

(* ============================================================================
   REUSABLE STAGE-D ENGINE (verified: reproduces STEADY exactly, aconv-identical).
   PROVE_SWPS_CORRECT_CASE dens eqs  where
     dens = deint `ensures_n arm P1 Q1 C1 f1` (equiv naming: in_b/out_b/htab_b, deint_mc),
     eqs  = strong equiv `ensures2 arm P Q C f1 f2` (exit carries FULL output agreement),
   returns swpS `ensures arm P2 Q2 C2` (P2/Q2 = deint entry/post renamed pc->pc2/deint_mc->swpS_mc),
   carrying dens+eqs hyps + the 3 sideA preconds (4 divides pc; htab_b/in_b vs word pc nonoverlap).
   Each of the 5 remaining cases: build its dens (Stage C at that case's loop bounds) + its eqs
   (Stage B strong-equiv for that case), then call this.  Prerequisites in scope: SEQ_PAIR_SPLIT_FN,
   LEN_DEINT, ALIGNED_INTERM, interm_state, DEINT_EXEC, prove_conj_of_eq_reads_unfold_rules augmented. *)
let PROVE_SWPS_CORRECT_CASE dens eqs =
  let conjc = MATCH_MP ENSURES_N_ENSURES2_CONJ (CONJ dens eqs) in
  let a = snd(strip_comb (concl conjc)) in
  let cP = el 1 a and cC = el 3 a and cf1 = el 4 a and cf2 = el 5 a in
  let densb = snd(strip_comb(concl dens)) in
  let sw = [`pc2:num`,`pc:num`; `swpS_mc:((8)word)list`,`deint_mc:((8)word)list`] in
  let cP2 = mk_abs(`s:armstate`, subst sw (snd(dest_abs (el 1 densb)))) in
  let cQ2 = mk_abs(`s:armstate`, subst sw (snd(dest_abs (el 2 densb)))) in
  let cfac = (TOP_DEPTH_CONV GEN_BETA_CONV THENC TOP_DEPTH_CONV (REWR_CONV SEQ_PAIR_SPLIT_FN)
              THENC TOP_DEPTH_CONV GEN_BETA_CONV)
             (list_mk_comb(cC, [`(s1:armstate,s2:armstate)`;`(s1':armstate,s2':armstate)`])) in
  let atoms = conjuncts(rhs(concl cfac)) in
  let dts = filter (fun t -> vfree_in `s1:armstate` t || vfree_in `s1':armstate` t) atoms in
  let sts = filter (fun t -> vfree_in `s2:armstate` t || vfree_in `s2':armstate` t) atoms in
  let cC1 = list_mk_abs([`a:armstate`;`b:armstate`], subst [`a:armstate`,`s1:armstate`;`b:armstate`,`s1':armstate`] (list_mk_conj dts)) in
  let cC2 = list_mk_abs([`a:armstate`;`b:armstate`], subst [`a:armstate`,`s2:armstate`;`b:armstate`,`s2':armstate`] (list_mk_conj sts)) in
  let e2i = ISPECL [`arm`; cP; el 2 a; cC; cP2; cQ2; cC2; cf1; cf2] ENSURES2_ENSURES_N in
  let cs = conjuncts(fst(dest_imp(concl e2i))) in
  let sA_tm = el 1 cs and sB_tm = el 2 cs and sC_tm = el 3 cs in
  let sB = prove(sB_tm,
    REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN DISCH_TAC) THEN ASM_MESON_TAC[]) in
  let sC = prove(sC_tm,
    EXISTS_TAC cC1 THEN REPEAT GEN_TAC THEN REWRITE_TAC[cfac] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC CONJ_ACI_RULE) in
  let extra = [`4 divides pc`;
               `nonoverlapping (htab_b:int64,192) (word pc:int64,1856)`;
               `nonoverlapping (in_b:int64,16*nblocks) (word pc:int64,1856)`] in
  let sA_full = mk_imp(list_mk_conj (extra @ hyp conjc), sA_tm) in
  let MEMEQ_C = W(fun (asl,w) ->
    let is_ir t = can (fun t -> if fst(dest_const(rator(rator t)))="read"
        && can(find_term(fun x->is_comb x && (try fst(dest_const(rator x))="write" with _->false)))(rand t)
        then () else failwith "") t in
    let ir = find_term is_ir w in
    let redeqn = mk_eq(ir, mk_comb(rator ir, `s2:armstate`)) in
    let asmtms = map (concl o snd) asl in
    let want t = is_comb t && ((try fst(dest_const(fst(strip_comb t)))="nonoverlapping" with _->false)
        || (try fst(dest_const(fst(strip_comb t)))="<" with _->false)
        || (is_eq t && (try fst(dest_const(fst(strip_comb(rhs t))))="*" with _->false))) in
    let red_lemma = prove(itlist (curry mk_imp) (filter want asmtms) redeqn,
        REPEAT DISCH_TAC THEN REWRITE_TAC[LEN_DEINT] THEN READ_OVER_WRITE_ORTHOGONAL_TAC) in
    MP_TAC red_lemma THEN REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN ASM_REWRITE_TAC[] in
  let sA = prove(sA_full,
    STRIP_TAC THEN X_GEN_TAC `s2:armstate` THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    EXISTS_TAC interm_state THEN
    REWRITE_TAC[mk_equiv_regs; BIGNUM_FROM_MEMORY_BYTES; htable_mem_4] THEN
    REPEAT CONJ_TAC THEN
    FIRST [
      (MATCH_MP_TAC ALIGNED_INTERM THEN FIRST_ASSUM ACCEPT_TAC);
      (GEN_TAC THEN DISCH_TAC THEN
       FIRST_X_ASSUM(fun th -> if is_forall(concl th) && vfree_in `inblock:num->int128` (concl th)
                               then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
       ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MEMEQ_C THEN NO_TAC);
      (W(fun (asl,w) -> let _,body = dest_exists w in
          let readC = rator(lhs(fst(dest_conj body))) in EXISTS_TAC (mk_comb(readC,`s2:armstate`)))
       THEN REWRITE_TAC[LEN_DEINT] THEN REPEAT CONJ_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC);
      (MEMEQ_C THEN NO_TAC);
      (PROVE_CONJ_OF_EQ_READS_TAC DEINT_EXEC THEN NO_TAC)
    ]) in
  let ens_n = MATCH_MP e2i (CONJ conjc (CONJ (UNDISCH sA) (CONJ sB sC))) in
  MATCH_MP ENSURES_N_ENSURES ens_n;;

(* STEADY via the engine (VERIFIED aconv-identical to the manual swpS_ensures):
   let SWP_S_CORRECT_STEADY = GEN_ALL(itlist DISCH (rev(hyp t)) t)
     where t = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_ALIGNED) STEADY_STRONG. *)

(* stageD binds the STEADY case under its long name; combine (SWPS_CASES) wants the short one. *)
let SWP_S_CORRECT_STEADY =
  AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_CORRECT_STEADY;;
(* ===== SWP_S_CORRECT_LC2 (lc=2, lr>=1) ===== *)
(* Stage D, lc=2 sub-case of STEADY (loop_count=2, loop_remain>=1).  Completes lr>=1 for ALL lc>=2.
   STEADY_STRONG already covers lc=2 (needs only 2<=loop_count, NOT ~(loop_count=2)); only the deint
   ensures_n needed an lc=2 variant.  Load after the 4 legs + seam infra + STAGE-D engine.

   For lc=2 the STEADY loop runs 0 iterations, so the deint ensures_n = FILL_N ++ DRAIN_N ++ DEINT_TAIL_N
   (skip STEADY_LOOP_N, whose count nsum(0..lc-2-1) is WRONG at lc=2: 2-2-1 underflows to 0 -> nsum(0..0)=1
   iter, not 0).  The FILL->DRAIN seam needs a small arithmetic weakening (FILL.post[lc:=2] has 64*1,
   4*1+2, loop_count-1; DRAIN.pre[lc:=2] has 64*(2-2+1), 4*(2-2+1)+2, 2-(2-2+1) - equal by ARITH). *)

let seam_lc2 =                       (* FILL.post[lc2] ==> DRAIN.pre[lc2] *)
  let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th))))))) in
  let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th))))))) in
  let fpl = subst [`2`,`loop_count:num`] (post_of FILL_N)
  and dpl = subst [`2`,`loop_count:num`] (pre_of DRAIN_N) in
  prove(mk_forall(`s:armstate`, mk_imp(mk_comb(fpl,`s:armstate`), mk_comb(dpl,`s:armstate`))),
    GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[ARITH_RULE `2-2+1=1`; ARITH_RULE `2-(2-2+1)=1`; ARITH_RULE `4*(2-2+1)=4`;
                ARITH_RULE `4*1=4`; ARITH_RULE `4*(2-2+1)+2=6`; ARITH_RULE `4*1+2=6`;
                ARITH_RULE `64*(2-2+1)=64`; ARITH_RULE `64*1=64`; ARITH_RULE `2-1=1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let cframe = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl FILL_N)))))));;
let fill_ant = fst(dest_imp(snd(strip_forall(concl FILL_N))));;
let tail_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_TAIL_N)))))));;
let lc2_count = mk_abs(`s:armstate`, mk_binary "+" (`179`, mk_binary "+" (`178`, snd(dest_abs tail_count))));;
let lc2_pre = list_mk_conj(conjuncts fill_ant @ [`loop_count = 2`; `1 <= loop_remain`]);;
let lc2_goal = list_mk_forall(fst(strip_forall(concl FILL_N)),
  mk_imp(lc2_pre, list_mk_icomb "ensures_n" [`arm`; pre_of FILL_N; post_of DEINT_TAIL_N; cframe; lc2_count]));;

let DEINT_FROM88_N_LC2 = prove(lc2_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) `loop_count = 2` then SUBST_ALL_TAC th else NO_TAC) THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let rec prove_conj t = if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else (try find (fun th -> aconv (concl th) t) asm_ths
           with _ -> prove(t, ASM_REWRITE_TAC[] THEN ARITH_TAC)) in
   let spec_leg leg = let legi = INST [`2`,`loop_count:num`] (SPEC_ALL leg) in
     MP legi (prove_conj (fst(dest_imp(concl legi)))) in
   let f0 = spec_leg FILL_N in
   let fw = MATCH_MP ENSURES_N_POSTCONDITION_THM (CONJ seam_lc2 f0) in
   let d = spec_leg DRAIN_N and t = spec_leg DEINT_TAIL_N in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ (MATCH_MP ENSURES_N_TRANS (CONJ fw d)) t) in
   let cf = el 3 (snd(strip_comb(concl ch))) in
   let sub_th = prove(list_mk_icomb "subsumed" [cf; cframe],
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
   let ch2 = MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch) in
   let count_eq2 = prove(mk_eq(last(snd(strip_comb(concl ch2))), last(snd(strip_comb w))),
      ABS_TAC THEN ARITH_TAC) in
   ACCEPT_TAC (REWRITE_RULE[count_eq2] ch2)));;

(* count -> f_n1 at lc=2, bridge to deint_mc, align, feed the engine with STEADY_STRONG. *)
let ss_fn1 = el 4 (snd(strip_comb (concl STEADY_STRONG)));;
let count_eq_lc2 = prove(mk_imp(`loop_count = 2`,
    mk_eq(snd(dest_abs lc2_count), snd(dest_abs ss_fn1))),
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ARITH_TAC);;
let lc2_fn1_goal =
  let vs = fst(strip_forall(concl DEINT_FROM88_N_LC2)) in
  let ant = fst(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC2)))) in
  let a = snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC2)))))) in
  list_mk_forall(vs, mk_imp(ant, list_mk_icomb "ensures_n" [el 0 a; el 1 a; el 2 a; el 3 a; ss_fn1]));;
let DEINT_FROM88_N_LC2_FN1 = prove(lc2_fn1_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(ss_fn1, lc2_count)) SUBST1_TAC THENL
   [ABS_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC count_eq_lc2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DEINT_FROM88_N_LC2 THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]);;
let DFD_LC2_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`]
   (REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_LC2_FN1);;

let SWP_S_CORRECT_LC2 =
  let r = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_LC2_ALIGNED) STEADY_STRONG in
  GEN_ALL(itlist DISCH (rev(hyp r)) r);;
Printf.printf "*** _SWP_S CORRECT (lc=2, lr>=1) PROVEN via engine: hyps=%d ***\n" (length(hyp SWP_S_CORRECT_LC2));;
(* STEADY (lc>=3) + LC2 => all loop_count>=2, loop_remain>=1. *)
(* ===== REM0_STRONG: strong (output-agreement) equiv for loop_remain=0 ===== *)
(* Stage B generalization: REM0_STRONG - the strong (output-agreement) whole-function equivalence
   for the loop_remain=0 case (cbz taken, remainder loop skipped), lc>=2.  This is the equiv-side
   ingredient (`eqs`) for feeding the REM0 case through PROVE_SWPS_CORRECT_CASE.
   Load in the combined session AFTER _swp_S.ml (gives PA_TI..RL_TI, CBZ_TAKEN_G, gti, f_tagivec,
   trans_exact/trans_weaken, mk_weaken, WEAKEN_TAC, PREAMBLE_G/MAIN_G/REDUCE_G) and stageB.ml
   (gives POSTAMBLE_STRONG).

   KEY FACTS established:
   - The 6 SWP_DEINT_SWPS_EQUIV_* share the SAME 0x710 exit STRUCTURE but the WEAK exit (6 conjuncts:
     Q30 agreement + ivec[12..16) agreement).  STEADY_STRONG/REM0_STRONG add the FULL 9-conjunct exit
     (+ out-buffer forall + tag128 + ivec128 agreement).
   - REM0's leg path = PREAMBLE ++ MAIN ++(weaken 0x4b4)++ REDUCE ++ CBZ_TAKEN, reaching 0x6fc (pc+1788),
     the SAME seam as STEADY's c_pre_ti.  So POSTAMBLE_STRONG (0x6fc->0x710, shared) composes on.
   - Graft f_tagivec onto the CBZ-taken leg: CBZT_TI = gti CBZ_TAKEN_G (adds tag/ivec agreement to its
     0x6fc exit so POSTAMBLE_STRONG's precond is met).
   - POSTAMBLE_STRONG is bare (STEADY, loop_remain symbolic); INST loop_remain:=0 -> PS0 (matches the
     lr=0 leg shapes: X16=word(0-0), 64*loop_count+16*0). *)

let ens_args_b t = snd(strip_comb t);;
let po_b th = List.nth (ens_args_b(concl th)) 2 and pr_b th = List.nth (ens_args_b(concl th)) 1;;

let CBZT_TI = gti CBZ_TAKEN_G;;   (* graft f_tagivec onto the CBZ-taken (lr=0) leg *)

let REM0_STRONG =
  let inst0 th = INST [`0`,`loop_remain:num`] (SPEC_ALL th) in
  let pg = UNDISCH (inst0 PA_TI) in
  let mg = UNDISCH (inst0 MN_TI) in
  let rg = UNDISCH (inst0 RD_TI) in
  let ct = UNDISCH (SPEC_ALL CBZT_TI) in
  let wk_mr = prove(mk_weaken (po_b mg) (pr_b rg), WEAKEN_TAC) in
  let c1 = trans_exact pg mg in
  let c2 = trans_weaken c1 wk_mr rg in
  let c3 = trans_exact c2 ct in
  let PS0 = INST [`0`,`loop_remain:num`] POSTAMBLE_STRONG in
  let wk_cp = prove(mk_weaken (po_b c3) (pr_b PS0), WEAKEN_TAC) in
  trans_weaken c3 wk_cp PS0;;
Printf.printf "*** REM0_STRONG built: hyps=%d, exit=9-conjunct full output agreement, f2 (no rem-loop term) ***\n"
  (length(hyp REM0_STRONG));;

(* REM0's `dens` (deint ensures_n at loop_remain=0) still TODO: chain FILL_N ++ STEADY_LOOP_N ++
   DRAIN_N ++ DEINT_TAIL_N_REM0 where DEINT_TAIL_N_REM0 = the 9-step lr=0 finalize (0x61c->0x710) as
   ensures_n - transform the deint DEINT_TAIL proof's `loop_remain=0` branch (deint proof lines 833-855)
   like DEINT_TAIL_N was built (ARM_STEPS->ARM_N_STEP).  Then split REM0 into lc=2 (STEADY 0 iters, use
   the lc2 seam) vs lc>=3, reconcile count to REM0_STRONG's f2, feed PROVE_SWPS_CORRECT_CASE. *)
(* ===== SWP_S_CORRECT_REM0 (lc>=3, lr=0) + REM0_LC2 (lc=2, lr=0) ===== *)
(* Stage D, REM0 case (loop_count>=3, loop_remain=0) - PROVEN via the engine + REM0-specific ingredients.
   Load after: the 4 STEADY legs + DEINT_TAIL_N_REM0 (deint ensures_n legs), REM0_STRONG (stageB_rem0),
   the PROVE_SWPS_CORRECT_CASE engine (stageD), MC_BRIDGE.

   dens (deint ensures_n, lr=0):  DEINT_FROM88_N_REM0 = FILL_N ++ STEADY_LOOP_N ++ DRAIN_N ++
     DEINT_TAIL_N_REM0 (all INST loop_remain:=0; DRAIN.post[lr:=0] aconv DEINT_TAIL_N_REM0.pre).
     Count = 179 + steady + 178 + 9.  Frame collapsed by ENSURES_N_FRAME_SUBSUMED.  Count reconciled to
     REM0_STRONG's f_n1 (= (((89 + steady + 1) + 93) + 1) + 4 + 1, NO remainder-loop term) via count_eq_rem0.
   GOTCHA: the goal's ENTRY must be FILL_N.pre at loop_remain:=0 (X16=word 0), not the symbolic pre_of
   FILL_N - else the ACCEPT_TAC frame/entry won't match the lr:=0-specialized chain.
   GOTCHA: MATCH_MP DEINT_FROM88_N_REM0 leaves `exists key_p loop_remain. <nonoverlaps>` -> discharge
     MAP_EVERY EXISTS_TAC [key_p; 0] THEN ASM_REWRITE.

   eqs = REM0_STRONG (see DEVEL_swp_S_stageB_rem0.ml).
   result = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_REM0_ALIGNED) REM0_STRONG -> SWP_S_CORRECT_REM0 (hyps=0). *)

let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let cframe = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl FILL_N)))))));;
let fill_ant = fst(dest_imp(snd(strip_forall(concl FILL_N))));;
let rem0_pre = list_mk_conj(conjuncts (subst[`0`,`loop_remain:num`] fill_ant) @ [`~(loop_count = 2)`; `loop_remain = 0`]);;
let steady_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl STEADY_LOOP_N)))))));;
let rem0_count = mk_abs(`s:armstate`,
  mk_binary "+" (`179`, mk_binary "+" (snd(dest_abs steady_count), mk_binary "+" (`178`, `9`))));;
let dfn_rem0_goal =
  list_mk_forall(fst(strip_forall(concl FILL_N)),
    mk_imp(rem0_pre, list_mk_icomb "ensures_n" [`arm`; subst[`0`,`loop_remain:num`](pre_of FILL_N);
       subst[`0`,`loop_remain:num`](post_of DEINT_TAIL_N_REM0); cframe; rem0_count]));;
let DEINT_FROM88_N_REM0 = prove(dfn_rem0_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let rec prove_conj t = if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else (try find (fun th -> aconv (concl th) t) asm_ths with _ -> prove(t, ASM_REWRITE_TAC[] THEN ARITH_TAC)) in
   let spec_leg leg = let legi = INST [`0`,`loop_remain:num`] (SPEC_ALL leg) in
     MP legi (prove_conj (fst(dest_imp(concl legi)))) in
   let f = spec_leg FILL_N and st = spec_leg STEADY_LOOP_N
   and d = spec_leg DRAIN_N and t = spec_leg DEINT_TAIL_N_REM0 in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ (MATCH_MP ENSURES_N_TRANS
       (CONJ (MATCH_MP ENSURES_N_TRANS (CONJ f st)) d)) t) in
   let cf = el 3 (snd(strip_comb(concl ch))) in
   let sub_th = prove(list_mk_icomb "subsumed" [cf; cframe],
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
   let ch2 = MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch) in
   let count_eq2 = prove(mk_eq(last(snd(strip_comb(concl ch2))), last(snd(strip_comb w))), ABS_TAC THEN ARITH_TAC) in
   ACCEPT_TAC (REWRITE_RULE[count_eq2] ch2)));;

let rem0_ss_fn1 = el 4 (snd(strip_comb(concl REM0_STRONG)));;
let dfnrem0_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_REM0)))))));;
let count_eq_rem0 = prove(
  mk_imp(`2 <= loop_count /\ ~(loop_count = 2) /\ loop_remain = 0`,
    mk_eq(snd(dest_abs dfnrem0_count), snd(dest_abs rem0_ss_fn1))),
  STRIP_TAC THEN SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NSUM_CONST_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> loop_count-1-1 = loop_count-2`] THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> ((loop_count-2)-1)+1-0 = loop_count-2`] THEN ASM_ARITH_TAC);;
let dfnrem0_fn1_goal =
  let vs = fst(strip_forall(concl DEINT_FROM88_N_REM0)) in
  let ant = fst(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_REM0)))) in
  let a = snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_REM0)))))) in
  list_mk_forall(vs, mk_imp(ant, list_mk_icomb "ensures_n" [el 0 a; el 1 a; el 2 a; el 3 a; rem0_ss_fn1]));;
let DEINT_FROM88_N_REM0_FN1 = prove(dfnrem0_fn1_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(rem0_ss_fn1, dfnrem0_count)) SUBST1_TAC THENL
   [ABS_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC count_eq_rem0 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DEINT_FROM88_N_REM0 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`key_p:int64`; `0`] THEN ASM_REWRITE_TAC[]]);;
let DFD_REM0_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`]
   (REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_REM0_FN1);;
let SWP_S_CORRECT_REM0 =
  let r = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_REM0_ALIGNED) REM0_STRONG in
  GEN_ALL(itlist DISCH (rev(hyp r)) r);;
Printf.printf "*** _SWP_S CORRECT (REM0: lc>=3, lr=0) PROVEN: hyps=%d ***\n" (length(hyp SWP_S_CORRECT_REM0));;

(* ---- lc=2, lr=0 sub-case (completes ALL loop_count>=2) ----
   REM0_STRONG covers lc=2 too (needs only 2<=loop_count).  Deint dens for lc=2/lr=0:
   DEINT_FROM88_N_REM0_LC2 = FILL_N ++(seam_lc2 INST lr:=0)++ DRAIN_N ++ DEINT_TAIL_N_REM0,
   all INST loop_count:=2, loop_remain:=0 (STEADY loop skipped, like the lr>=1 lc2 case).
   Count 179+178+9 -> f_n1 at loop_count=2.  Feed engine -> SWP_S_CORRECT_REM0_LC2 (hyps=0). *)
let rem0lc2_pre = list_mk_conj(conjuncts (subst[`0`,`loop_remain:num`] fill_ant) @ [`loop_count = 2`; `loop_remain = 0`]);;
let rem0lc2_count = mk_abs(`s:armstate`, mk_binary "+" (`179`, mk_binary "+" (`178`, `9`)));;
let rem0lc2_goal =
  list_mk_forall(fst(strip_forall(concl FILL_N)),
    mk_imp(rem0lc2_pre, list_mk_icomb "ensures_n" [`arm`;
       subst[`0`,`loop_remain:num`](pre_of FILL_N);
       subst[`0`,`loop_remain:num`](post_of DEINT_TAIL_N_REM0); cframe; rem0lc2_count]));;
let DEINT_FROM88_N_REM0_LC2 = prove(rem0lc2_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) `loop_count = 2` then SUBST_ALL_TAC th else NO_TAC) THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let rec prove_conj t = if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else (try find (fun th -> aconv (concl th) t) asm_ths with _ -> prove(t, ASM_REWRITE_TAC[] THEN ARITH_TAC)) in
   let spec_leg leg = let legi = INST [`2`,`loop_count:num`; `0`,`loop_remain:num`] (SPEC_ALL leg) in
     MP legi (prove_conj (fst(dest_imp(concl legi)))) in
   let f0 = spec_leg FILL_N in
   let fw = MATCH_MP ENSURES_N_POSTCONDITION_THM (CONJ (INST [`0`,`loop_remain:num`] seam_lc2) f0) in
   let d = spec_leg DRAIN_N and t = spec_leg DEINT_TAIL_N_REM0 in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ (MATCH_MP ENSURES_N_TRANS (CONJ fw d)) t) in
   let cf = el 3 (snd(strip_comb(concl ch))) in
   let sub_th = prove(list_mk_icomb "subsumed" [cf; cframe],
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
   let ch2 = MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch) in
   let count_eq2 = prove(mk_eq(last(snd(strip_comb(concl ch2))), last(snd(strip_comb w))), ABS_TAC THEN ARITH_TAC) in
   ACCEPT_TAC (REWRITE_RULE[count_eq2] ch2)));;
let dfnrem0lc2_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_REM0_LC2)))))));;
let count_eq_rem0lc2 = prove(mk_imp(`loop_count = 2`,
    mk_eq(snd(dest_abs dfnrem0lc2_count), snd(dest_abs rem0_ss_fn1))),
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ARITH_TAC);;
let dfnrem0lc2_fn1_goal =
  let vs = fst(strip_forall(concl DEINT_FROM88_N_REM0_LC2)) in
  let ant = fst(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_REM0_LC2)))) in
  let a = snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_REM0_LC2)))))) in
  list_mk_forall(vs, mk_imp(ant, list_mk_icomb "ensures_n" [el 0 a; el 1 a; el 2 a; el 3 a; rem0_ss_fn1]));;
let DEINT_FROM88_N_REM0_LC2_FN1 = prove(dfnrem0lc2_fn1_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(rem0_ss_fn1, dfnrem0lc2_count)) SUBST1_TAC THENL
   [ABS_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC count_eq_rem0lc2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DEINT_FROM88_N_REM0_LC2 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`key_p:int64`; `0`] THEN ASM_REWRITE_TAC[]]);;
let DFD_REM0_LC2_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`]
   (REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_REM0_LC2_FN1);;
let SWP_S_CORRECT_REM0_LC2 =
  let r = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_REM0_LC2_ALIGNED) REM0_STRONG in
  GEN_ALL(itlist DISCH (rev(hyp r)) r);;
Printf.printf "*** _SWP_S CORRECT (lc=2, lr=0) PROVEN: hyps=%d.  ALL loop_count>=2 now covered. ***\n"
  (length(hyp SWP_S_CORRECT_REM0_LC2));;
(* ===== LC1_{REM0,REMPOS}_STRONG: strong equivs for loop_count=1 ===== *)
(* Stage B for the lc=1 cases: LC1_REM0_STRONG (loop_count=1, loop_remain=0) strong equiv.
   Demonstrates the Stage-B graft+compose recipe extends to the lc=1 head-leg set.  Load after
   _swp_S.ml (HEAD_LC1_A_G, REDUCE_GEN_G, CBZ_TAKEN_G, gti, f_tagivec, trans_exact/weaken) + stageB
   (POSTAMBLE_STRONG) + stageB_rem0 (CBZT_TI = gti CBZ_TAKEN_G).

   composed_lc1_rem0 (from _swp_S.ml) = HEAD_LC1_A ++ REDUCE_GEN ++ CBZ_TAKEN ++ POSTAMBLE_EQUIV (weak).
   Strong version: graft f_tagivec on the three pre-postamble legs (HEAD_LC1_A_TI/REDUCE_GEN_TI/CBZT_TI),
   compose to the shared 0x6fc seam, trans_weaken with POSTAMBLE_STRONG (INST loop_remain:=0). *)
let ens_args_b t = snd(strip_comb t);;
let po_b th = List.nth (ens_args_b(concl th)) 2 and pr_b th = List.nth (ens_args_b(concl th)) 1;;
let HEAD_LC1_A_TI = gti HEAD_LC1_A_G;;
let REDUCE_GEN_TI = gti REDUCE_GEN_G;;
(* CBZT_TI assumed already built (stageB_rem0); rebuild here for standalone loading *)
let CBZT_TI = gti CBZ_TAKEN_G;;
let LC1_REM0_STRONG =
  let inst0 th = INST [`0`,`loop_remain:num`] (SPEC_ALL th) in
  let hg = UNDISCH (inst0 HEAD_LC1_A_TI) in
  let rg = UNDISCH (inst0 REDUCE_GEN_TI) in
  let ct = UNDISCH (SPEC_ALL CBZT_TI) in
  let PS0 = INST [`0`,`loop_remain:num`] POSTAMBLE_STRONG in
  let c1 = trans_exact hg rg in
  let c2 = trans_exact c1 ct in
  let wk = prove(mk_weaken (po_b c2) (pr_b PS0), WEAKEN_TAC) in
  trans_weaken c2 wk PS0;;
Printf.printf "*** LC1_REM0_STRONG built: hyps=%d, exit=9-conjunct output agreement, f2=((89+93)+1)+4+1 ***\n"
  (length(hyp LC1_REM0_STRONG));;

(* dens for lc=1/lr=0 (TODO, the remaining stepping task): LEG1_LC1_N ++ DEINT_TAIL_N_REM0.
   LEG1_LC1_N = deint LEG1_LC1 (0x88->0x61c, ~178 steps + 9 MERGE_CTR128 + GHASH reconstruction) as
   ensures_n - transform ARM_STEPS->ARM_N_STEP like FILL_N; it's a ~500s stepping leg past the head-746
   prefix, so load LEG1_LC1's statement/proof text (deint lines 1054-1272) and transform.  Then
   LEG1_LC1_N.post (0x61c) = DEINT_TAIL_N_REM0.pre at lr=0; chain, count-reconcile to LC1_REM0_STRONG's
   f2, feed PROVE_SWPS_CORRECT_CASE.  Similarly LC1_REMPOS uses LEG1_LC1_N ++ DEINT_TAIL_N (lr>=1). *)

(* ---- LC1_REMPOS_STRONG (lc=1, lr>=1) ---- mirror composed_lc1_rempos:
   HEAD_LC1_A ++ REDUCE_GEN ++ CBZ ++ REMLOOP ++ POSTAMBLE, grafting f_tagivec on the 4 pre-postamble
   legs (CBZ_TI = gti CBZ_G, REMLOOP_TI = gti REMLOOP_G) + POSTAMBLE_STRONG (symbolic lr). *)
let CBZ_TI = gti CBZ_G;;
let REMLOOP_TI = gti REMLOOP_G;;
let LC1_REMPOS_STRONG =
  let hg = UNDISCH (SPEC_ALL HEAD_LC1_A_TI) in
  let rg = UNDISCH (SPEC_ALL REDUCE_GEN_TI) in
  let cg = UNDISCH (SPEC_ALL CBZ_TI) in
  let lg = UNDISCH (SPEC_ALL REMLOOP_TI) in
  let c1 = trans_exact hg rg in
  let c2 = trans_exact c1 cg in
  let c3 = trans_exact c2 lg in
  let wk = prove(mk_weaken (po_b c3) (pr_b POSTAMBLE_STRONG), WEAKEN_TAC) in
  trans_weaken c3 wk POSTAMBLE_STRONG;;
Printf.printf "*** LC1_REMPOS_STRONG built: hyps=%d ***\n" (length(hyp LC1_REMPOS_STRONG));;
(* ===== SWP_S_CORRECT_LC1_REM0 (lc=1, lr=0) ===== *)
(* Stage D, lc=1 cases.  Load after LEG1_LC1_N (DEVEL_swp_S_stageC_LEG1_LC1_N.ml), DEINT_TAIL_N +
   DEINT_TAIL_N_REM0, LC1_REM0_STRONG (stageB_lc1), engine (stageD), MC_BRIDGE.

   LEG1_LC1_N (0x88->0x61c @179, loop_count=1): the deint lc=1 body as ensures_n, transformed from
   the deint LEG1_LC1 proof (ARM_STEPS->ARM_N_STEP, 9 MERGE_CTR128 sites, GHASH reconstruction verbatim).
   It is the SHARED heavy leg for both lc=1 cases.

   lc=1, lr=0:  dens = LEG1_LC1_N ++(seam_lc1rem0)++ DEINT_TAIL_N_REM0, count 179+9=188 = LC1_REM0_STRONG
   f2 (unconditional).  seam_lc1rem0 = LEG1_LC1_N.post[lc:=1,lr:=0] ==> DEINT_TAIL_N_REM0.pre[lc:=1]
   (arith 64*1=64, 4*1+2=6).  -> SWP_S_CORRECT_LC1_REM0 (hyps=0). *)
let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let cframe = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl LEG1_LC1_N)))))));;
let leg1_ant = fst(dest_imp(snd(strip_forall(concl LEG1_LC1_N))));;
let leg1post = post_of LEG1_LC1_N;;
let s_lc1lr0 t = subst[`1`,`loop_count:num`](subst[`0`,`loop_remain:num`] t);;
let seam_lc1rem0 = prove(
  mk_forall(`s:armstate`, mk_imp(mk_comb(s_lc1lr0 leg1post,`s:armstate`),
                                 mk_comb(subst[`1`,`loop_count:num`](pre_of DEINT_TAIL_N_REM0),`s:armstate`))),
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `64*1=64`; ARITH_RULE `4*1=4`; ARITH_RULE `4*1+2=6`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let lc1rem0_pre = list_mk_conj(conjuncts (subst[`0`,`loop_remain:num`] leg1_ant) @ [`loop_remain = 0`]);;
let lc1rem0_goal =
  list_mk_forall(fst(strip_forall(concl LEG1_LC1_N)),
    mk_imp(lc1rem0_pre, list_mk_icomb "ensures_n" [`arm`;
       subst[`0`,`loop_remain:num`](pre_of LEG1_LC1_N);
       subst[`0`,`loop_remain:num`](post_of DEINT_TAIL_N_REM0); cframe; `\s:armstate. 179 + 9`]));;
let DEINT_FROM88_N_LC1_REM0 = prove(lc1rem0_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) `loop_count = 1` then SUBST_ALL_TAC th else NO_TAC) THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let rec prove_conj t = if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else (try find (fun th -> aconv (concl th) t) asm_ths with _ -> prove(t, ASM_REWRITE_TAC[] THEN ARITH_TAC)) in
   let spec_leg leg = let legi = INST [`1`,`loop_count:num`; `0`,`loop_remain:num`] (SPEC_ALL leg) in
     MP legi (prove_conj (fst(dest_imp(concl legi)))) in
   let l0 = spec_leg LEG1_LC1_N in
   let lw = MATCH_MP ENSURES_N_POSTCONDITION_THM (CONJ seam_lc1rem0 l0) in
   let t = spec_leg DEINT_TAIL_N_REM0 in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ lw t) in
   let cf = el 3 (snd(strip_comb(concl ch))) in
   let sub_th = prove(list_mk_icomb "subsumed" [cf; cframe],
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
   let ch2 = MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch) in
   let count_eq2 = prove(mk_eq(last(snd(strip_comb(concl ch2))), last(snd(strip_comb w))), ABS_TAC THEN ARITH_TAC) in
   ACCEPT_TAC (REWRITE_RULE[count_eq2] ch2)));;
let lc1rem0_ss_fn1 = el 4 (snd(strip_comb(concl LC1_REM0_STRONG)));;
let dfnlc1rem0_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC1_REM0)))))));;
let count_eq_lc1rem0 = prove(mk_eq(snd(dest_abs dfnlc1rem0_count), snd(dest_abs lc1rem0_ss_fn1)), ARITH_TAC);;
let dfnlc1rem0_fn1_goal =
  let vs = fst(strip_forall(concl DEINT_FROM88_N_LC1_REM0)) in
  let ant = fst(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC1_REM0)))) in
  let a = snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC1_REM0)))))) in
  list_mk_forall(vs, mk_imp(ant, list_mk_icomb "ensures_n" [el 0 a; el 1 a; el 2 a; el 3 a; lc1rem0_ss_fn1]));;
let DEINT_FROM88_N_LC1_REM0_FN1 = prove(dfnlc1rem0_fn1_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(lc1rem0_ss_fn1, dfnlc1rem0_count)) SUBST1_TAC THENL
   [ABS_TAC THEN CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC count_eq_lc1rem0;
    MATCH_MP_TAC DEINT_FROM88_N_LC1_REM0 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`key_p:int64`; `0`] THEN ASM_REWRITE_TAC[]]);;
let DFD_LC1_REM0_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`]
   (REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_LC1_REM0_FN1);;
let SWP_S_CORRECT_LC1_REM0 =
  let r = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_LC1_REM0_ALIGNED) LC1_REM0_STRONG in
  GEN_ALL(itlist DISCH (rev(hyp r)) r);;
Printf.printf "*** _SWP_S CORRECT (lc=1, lr=0) PROVEN: hyps=%d ***\n" (length(hyp SWP_S_CORRECT_LC1_REM0));;
(* ===== SWP_S_CORRECT_LC1_REMPOS (lc=1, lr>=1) ===== *)
(* Stage D, lc=1/lr>=1 case.  dens = LEG1_LC1_N ++(seam_lc1rempos)++ DEINT_TAIL_N (lr>=1), both proven.
   seam_lc1rempos = LEG1_LC1_N.post[lc:=1] ==> DEINT_TAIL_N.pre[lc:=1] (arith).  count 179+tailcount =
   LC1_REMPOS_STRONG f2 (unconditional ARITH).  eqs = LC1_REMPOS_STRONG.  -> SWP_S_CORRECT_LC1_REMPOS. *)
let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let cframe = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl LEG1_LC1_N)))))));;
let leg1_ant = fst(dest_imp(snd(strip_forall(concl LEG1_LC1_N))));;
let seam_lc1rempos = prove(
  mk_forall(`s:armstate`, mk_imp(mk_comb(subst[`1`,`loop_count:num`](post_of LEG1_LC1_N),`s:armstate`),
                                 mk_comb(subst[`1`,`loop_count:num`](pre_of DEINT_TAIL_N),`s:armstate`))),
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `64*1=64`; ARITH_RULE `4*1=4`; ARITH_RULE `4*1+2=6`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let tail_count = snd(dest_abs(last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_TAIL_N)))))))));;
let lc1rp_count = mk_abs(`s:armstate`, mk_binary "+" (`179`, tail_count));;
let lc1rp_pre = list_mk_conj(conjuncts leg1_ant @ [`1 <= loop_remain`]);;
let lc1rp_goal =
  list_mk_forall(fst(strip_forall(concl LEG1_LC1_N)),
    mk_imp(lc1rp_pre, list_mk_icomb "ensures_n" [`arm`;
       subst[`1`,`loop_count:num`](pre_of LEG1_LC1_N);
       subst[`1`,`loop_count:num`](post_of DEINT_TAIL_N); cframe; lc1rp_count]));;
let DEINT_FROM88_N_LC1_REMPOS = prove(lc1rp_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) `loop_count = 1` then SUBST_ALL_TAC th else NO_TAC) THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let rec prove_conj t = if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else (try find (fun th -> aconv (concl th) t) asm_ths with _ -> prove(t, ASM_REWRITE_TAC[] THEN ARITH_TAC)) in
   let spec_leg leg = let legi = INST [`1`,`loop_count:num`] (SPEC_ALL leg) in
     MP legi (prove_conj (fst(dest_imp(concl legi)))) in
   let l0 = spec_leg LEG1_LC1_N in
   let lw = MATCH_MP ENSURES_N_POSTCONDITION_THM (CONJ seam_lc1rempos l0) in
   let t = spec_leg DEINT_TAIL_N in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ lw t) in
   let cf = el 3 (snd(strip_comb(concl ch))) in
   let sub_th = prove(list_mk_icomb "subsumed" [cf; cframe],
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
   let ch2 = MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch) in
   let count_eq2 = prove(mk_eq(last(snd(strip_comb(concl ch2))), last(snd(strip_comb w))), ABS_TAC THEN ARITH_TAC) in
   ACCEPT_TAC (REWRITE_RULE[count_eq2] ch2)));;
let lc1rp_ss_fn1 = el 4 (snd(strip_comb(concl LC1_REMPOS_STRONG)));;
let dfnlc1rp_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC1_REMPOS)))))));;
let count_eq_lc1rp = prove(mk_eq(snd(dest_abs dfnlc1rp_count), snd(dest_abs lc1rp_ss_fn1)), ARITH_TAC);;
let dfnlc1rp_fn1_goal =
  let vs = fst(strip_forall(concl DEINT_FROM88_N_LC1_REMPOS)) in
  let ant = fst(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC1_REMPOS)))) in
  let a = snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC1_REMPOS)))))) in
  list_mk_forall(vs, mk_imp(ant, list_mk_icomb "ensures_n" [el 0 a; el 1 a; el 2 a; el 3 a; lc1rp_ss_fn1]));;
let DEINT_FROM88_N_LC1_REMPOS_FN1 = prove(dfnlc1rp_fn1_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(lc1rp_ss_fn1, dfnlc1rp_count)) SUBST1_TAC THENL
   [ABS_TAC THEN CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC count_eq_lc1rp;
    MATCH_MP_TAC DEINT_FROM88_N_LC1_REMPOS THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`key_p:int64`; `1`] THEN ASM_REWRITE_TAC[]]);;
let DFD_LC1_REMPOS_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`]
   (REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_LC1_REMPOS_FN1);;
let SWP_S_CORRECT_LC1_REMPOS =
  let r = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_LC1_REMPOS_ALIGNED) LC1_REMPOS_STRONG in
  GEN_ALL(itlist DISCH (rev(hyp r)) r);;
Printf.printf "*** _SWP_S CORRECT (lc=1, lr>=1) PROVEN: hyps=%d ***\n" (length(hyp SWP_S_CORRECT_LC1_REMPOS));;
(* ===== LC0_{REM0,REMPOS}_STRONG: strong equivs for loop_count=0 ===== *)
(* Stage B for the lc=0 cases: LC0_REMPOS_STRONG (loop_count=0, loop_remain>=1) and
   LC0_REM0_STRONG (loop_count=0, loop_remain=0) strong equivs.  Load after _swp_S.ml
   (HEAD_LC0_G, CBZ_G, REMLOOP_G, CBZ_TAKEN_G, gti, f_tagivec, f_ptr, trans_exact/weaken,
   graft_goal_extra, GRAFT_TAC, FP_TAGIVEC_TAC) + stageB (POSTAMBLE_STRONG) + stageB_lc1
   (CBZ_TI = gti CBZ_G, REMLOOP_TI = gti REMLOOP_G, CBZT_TI = gti CBZ_TAKEN_G).

   KEY (2026-07-30): HEAD_LC0_G will NOT graft with the plain ti_extra used for the steady/lc1
   legs.  HEAD_LC0's internal frame uses the region `64 * loop_count` (not `16 * nblocks`), so
   step_ro inside FP_TAGIVEC_TAC needs the tag/ivec-vs-`(out_b, 64*loop_count)` nonoverlaps in
   context.  Augment ti_extra with those two (ti_extra_lc0) and use a shape-based frame finder
   (FP_TAGIVEC_ROBUST) so the graft succeeds -> HEAD_LC0_TI.

   The mirror of _swp_S.ml's composed_lc0_rempos/composed_lc0_rem0 (which used the WEAK
   POSTAMBLE_EQUIV) with the tag/ivec-grafted legs + POSTAMBLE_STRONG. *)
let ens_args_b t = snd(strip_comb t);;
let po_b th = List.nth (ens_args_b(concl th)) 2 and pr_b th = List.nth (ens_args_b(concl th)) 1;;
let instlc0 th = INST [`0`,`loop_count:num`] (SPEC_ALL th);;

(* ti_extra augmented with the two (out_b, 64*loop_count) nonoverlaps HEAD_LC0's frame needs. *)
let ti_extra_lc0 = `nonoverlapping (tag_p:int64,16) (out_b:int64,16*nblocks) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
   nonoverlapping (ivec_p:int64,16) (out_b:int64,16*nblocks) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64) /\
   nonoverlapping (tag_p:int64,16) (out_b:int64,64*loop_count) /\
   nonoverlapping (ivec_p:int64,16) (out_b:int64,64*loop_count)`;;

(* shape-based frame finder: locate the tag/ivec-carrying MAYCHANGE frame among the assumptions
   by STRUCTURE (contains a ",," combinator and mentions s_final / s_final2), not by position.
   FP_TAGIVEC_TAC assumed a fixed assumption index that HEAD_LC0's frame layout breaks; this finds
   the frame for each of s_final/s_final2 then discharges read-preservation of tag_p/ivec_p via
   step_ro (both bound in the stageB scope). *)
let FP_TAGIVEC_ROBUST : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN BETA_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th)) THEN
  W(fun (asl,w) ->
    let is_frame th = let c = concl th in
      is_comb c && is_comb(rator c) && can(find_term(fun x->is_comb x && (try fst(dest_const(rator(rator x)))=",," with _->false))) c in
    let frames = filter is_frame (map snd asl) in
    let hf = find (fun th -> vfree_in `s_final:armstate` (concl th)) frames in
    let hf2 = find (fun th -> vfree_in `s_final2:armstate` (concl th)) frames in
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (mk_conj(
          mk_eq(list_mk_icomb "read" [c;`s_final:armstate`], list_mk_icomb "read" [c;`s:armstate`]),
          mk_eq(list_mk_icomb "read" [c;`s_final2:armstate`], list_mk_icomb "read" [c;`s2:armstate`])))
        STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [step_ro hf; step_ro hf2]; ALL_TAC])
      [`memory :> bytes128 tag_p`; `memory :> bytes128 ivec_p`] THEN
    ASM_REWRITE_TAC[]);;
let gti_lc0 leg = prove(graft_goal_extra leg f_tagivec ti_extra_lc0 [`tag_p:int64`;`ivec_p:int64`],
    REPEAT STRIP_TAC THEN GRAFT_TAC f_tagivec FP_TAGIVEC_ROBUST leg);;
let HEAD_LC0_TI = gti_lc0 HEAD_LC0_G;;
Printf.printf "*** HEAD_LC0_TI grafted (hyps=%d) ***\n" (length(hyp HEAD_LC0_TI));;

(* LC0_REMPOS_STRONG = HEAD_LC0_TI ++ CBZ_TI[lc0] ++ REMLOOP_TI[lc0] ++ POSTAMBLE_STRONG[lc0].
   POSTAMBLE_STRONG is a bare ensures2 (no precond) -> do NOT UNDISCH it. *)
let LC0_REMPOS_STRONG =
  let hg  = UNDISCH (SPEC_ALL HEAD_LC0_TI) in
  let cg  = UNDISCH (instlc0 CBZ_TI) in
  let lg  = UNDISCH (instlc0 REMLOOP_TI) in
  let pog = instlc0 POSTAMBLE_STRONG in
  let wk = prove(mk_weaken (po_b lg) (pr_b pog), WEAKEN_TAC) in
  let c1 = trans_exact hg cg in
  let c2 = trans_exact c1 lg in
  trans_weaken c2 wk pog;;
Printf.printf "*** LC0_REMPOS_STRONG built: hyps=%d ***\n" (length(hyp LC0_REMPOS_STRONG));;

(* LC0_REM0_STRONG = HEAD_LC0_TI[lr0] ++ CBZ_TAKEN_TI[lc0] ++ POSTAMBLE_STRONG[lc0,lr0]. *)
let LC0_REM0_STRONG =
  let hg = UNDISCH (INST [`0`,`loop_remain:num`] (SPEC_ALL HEAD_LC0_TI)) in
  let ct = UNDISCH (instlc0 CBZT_TI) in
  let PS = INST [`0`,`loop_count:num`;`0`,`loop_remain:num`] POSTAMBLE_STRONG in
  let c1 = trans_exact hg ct in
  let wk = prove(mk_weaken (po_b c1) (pr_b PS), WEAKEN_TAC) in
  trans_weaken c1 wk PS;;
Printf.printf "*** LC0_REM0_STRONG built: hyps=%d ***\n" (length(hyp LC0_REM0_STRONG));;
(* ===== SWP_S_CORRECT_LC0_{REM0,REMPOS} (lc=0) ===== *)
(* Stage D, lc=0 cases (the two degenerate cases: nblocks < 4, main loop skipped via cbz@0x88).
   Load after LEG1_LC0_N (DEVEL_swp_S_stageC_LEG1_LC0_N.ml), DEINT_TAIL_N + DEINT_TAIL_N_REM0,
   LC0_REMPOS_STRONG + LC0_REM0_STRONG (stageB_lc0), engine + MC_BRIDGE (stageD).

   LEG1_LC0_N (0x88->0x61c @1, loop_count=0): the deint cbz-taken degenerate head; nist_ghash[]=tag0,
   Q30=byteswap128 tag0, no blocks produced (4*0).  Shared by both lc=0 cases.

   lc=0, lr=0:   dens = LEG1_LC0_N ++(seam)++ DEINT_TAIL_N_REM0,  count 1+9  = LC0_REM0_STRONG f1.
   lc=0, lr>=1:  dens = LEG1_LC0_N ++(seam)++ DEINT_TAIL_N,       count 1+tail = LC0_REMPOS_STRONG f1.
   Both seams: LEG1_LC0_N.post[lc:=0] ==> tail.pre[lc:=0] (arith 64*0=0, 4*0+2=2; for lr=0 also
   substitute loop_remain:=0 in the post so X16 = word 0 matches).

   prove_conj fallback here uses a CLEAN implication lemma discharged by ASM_ARITH_TAC then MP'd with
   the ambient numeric facts (LEG1_LC0_N needs `nblocks MOD 4 = loop_remain` etc. to close its own
   `nblocks MOD 4 = 0` / `1 <= loop_remain` side-conditions after loop_count:=0), avoiding the
   "additional assumptions in result" leak that a bare prove(t,ASM_ARITH_TAC) would cause. *)
let pre_of th = el 1 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let post_of th = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th)))))));;
let cframe0 = el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl LEG1_LC0_N)))))));;
let lc0_ant = fst(dest_imp(snd(strip_forall(concl LEG1_LC0_N))));;

(* ---- lc=0, lr=0 ---- *)
let leg0post_0 = subst[`0`,`loop_count:num`](subst[`0`,`loop_remain:num`](post_of LEG1_LC0_N));;
let tailrem0_pre_0 = subst[`0`,`loop_count:num`](pre_of DEINT_TAIL_N_REM0);;
let seam_lc0rem0 = prove(
  mk_forall(`s:armstate`, mk_imp(mk_comb(leg0post_0,`s:armstate`), mk_comb(tailrem0_pre_0,`s:armstate`))),
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `64*0=0`; ARITH_RULE `4*0=0`; ARITH_RULE `4*0+2=2`; MULT_CLAUSES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let lc0rem0_pre = list_mk_conj(conjuncts lc0_ant @ [`loop_remain = 0`]);;
let lc0rem0_goal =
  list_mk_forall(fst(strip_forall(concl LEG1_LC0_N)),
    mk_imp(lc0rem0_pre, list_mk_icomb "ensures_n" [`arm`;
       subst[`0`,`loop_remain:num`](pre_of LEG1_LC0_N);
       subst[`0`,`loop_count:num`](post_of DEINT_TAIL_N_REM0); cframe0; `\s:armstate. 1 + 9`]));;
let DEINT_FROM88_N_LC0_REM0 = prove(lc0rem0_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) `loop_count = 0` then SUBST_ALL_TAC th else NO_TAC) THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let numeqs = filter (fun th -> let c = concl th in
       (is_eq c && type_of(lhs c) = `:num`) ||
       (is_comb c && (try mem (fst(dest_const(rator(rator c)))) ["<";"<=";">";">="] with _ -> false))) asm_ths in
   let prove_arith t =
     let lemma = prove(itlist (curry mk_imp) (map concl numeqs) t, REPEAT DISCH_TAC THEN ASM_ARITH_TAC) in
     List.fold_left (fun acc th -> MP acc th) lemma numeqs in
   let rec prove_conj t = if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else (try find (fun th -> aconv (concl th) t) asm_ths with _ -> prove_arith t) in
   let spec_leg leg = let legi = INST [`0`,`loop_count:num`; `0`,`loop_remain:num`] (SPEC_ALL leg) in
     MP legi (prove_conj (fst(dest_imp(concl legi)))) in
   let l0 = spec_leg LEG1_LC0_N in
   let lw = MATCH_MP ENSURES_N_POSTCONDITION_THM (CONJ seam_lc0rem0 l0) in
   let t = spec_leg DEINT_TAIL_N_REM0 in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ lw t) in
   let cf = el 3 (snd(strip_comb(concl ch))) in
   let sub_th = prove(list_mk_icomb "subsumed" [cf; cframe0],
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
   let ch2 = MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch) in
   let count_eq2 = prove(mk_eq(last(snd(strip_comb(concl ch2))), last(snd(strip_comb w))), ABS_TAC THEN ARITH_TAC) in
   ACCEPT_TAC (REWRITE_RULE[count_eq2] ch2)));;
Printf.printf "*** DEINT_FROM88_N_LC0_REM0 proved? hyps=%d ***\n" (length(hyp DEINT_FROM88_N_LC0_REM0));;

let lc0rem0_ss_fn1 = el 4 (snd(strip_comb(concl LC0_REM0_STRONG)));;
let dfnlc0rem0_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC0_REM0)))))));;
let count_eq_lc0rem0 = prove(mk_eq(snd(dest_abs dfnlc0rem0_count), snd(dest_abs lc0rem0_ss_fn1)), ARITH_TAC);;
let DEINT_FROM88_N_LC0_REM0_FN1 = REWRITE_RULE[count_eq_lc0rem0] DEINT_FROM88_N_LC0_REM0;;
let DFD_LC0_REM0_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`]
   (REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_LC0_REM0_FN1);;
let SWP_S_CORRECT_LC0_REM0 =
  let r = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_LC0_REM0_ALIGNED) LC0_REM0_STRONG in
  GEN_ALL(itlist DISCH (rev(hyp r)) r);;
Printf.printf "*** _SWP_S CORRECT (lc=0, lr=0) PROVEN: hyps=%d ***\n" (length(hyp SWP_S_CORRECT_LC0_REM0));;

(* ---- lc=0, lr>=1 ---- *)
let leg0post_lc0 = subst[`0`,`loop_count:num`](post_of LEG1_LC0_N);;
let tail_pre_lc0 = subst[`0`,`loop_count:num`](pre_of DEINT_TAIL_N);;
let seam_lc0rempos = prove(
  mk_forall(`s:armstate`, mk_imp(mk_comb(leg0post_lc0,`s:armstate`), mk_comb(tail_pre_lc0,`s:armstate`))),
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `64*0=0`; ARITH_RULE `4*0=0`; ARITH_RULE `4*0+2=2`; MULT_CLAUSES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let lc0rempos_pre = list_mk_conj(conjuncts lc0_ant @ [`1 <= loop_remain`]);;
let lc0rempos_goal =
  list_mk_forall(fst(strip_forall(concl LEG1_LC0_N)),
    mk_imp(lc0rempos_pre, list_mk_icomb "ensures_n" [`arm`;
       pre_of LEG1_LC0_N;
       subst[`0`,`loop_count:num`](post_of DEINT_TAIL_N); cframe0;
       `\s:armstate. 1 + (4 + (nsum (0..loop_remain - 1) (\i. 51) + (loop_remain - 1) * 1) + 6)`]));;
let DEINT_FROM88_N_LC0_REMPOS = prove(lc0rempos_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) `loop_count = 0` then SUBST_ALL_TAC th else NO_TAC) THEN
  W(fun (asl,w) ->
   let asm_ths = map snd asl in
   let numeqs = filter (fun th -> let c = concl th in
       (is_eq c && type_of(lhs c) = `:num`) ||
       (is_comb c && (try mem (fst(dest_const(rator(rator c)))) ["<";"<=";">";">="] with _ -> false))) asm_ths in
   let prove_arith t =
     let lemma = prove(itlist (curry mk_imp) (map concl numeqs) t, REPEAT DISCH_TAC THEN ASM_ARITH_TAC) in
     List.fold_left (fun acc th -> MP acc th) lemma numeqs in
   let rec prove_conj t = if is_conj t then CONJ (prove_conj (lhand t)) (prove_conj (rand t))
     else (try find (fun th -> aconv (concl th) t) asm_ths with _ -> prove_arith t) in
   let spec_leg leg = let legi = INST [`0`,`loop_count:num`] (SPEC_ALL leg) in
     MP legi (prove_conj (fst(dest_imp(concl legi)))) in
   let l0 = spec_leg LEG1_LC0_N in
   let lw = MATCH_MP ENSURES_N_POSTCONDITION_THM (CONJ seam_lc0rempos l0) in
   let t = spec_leg DEINT_TAIL_N in
   let ch = MATCH_MP ENSURES_N_TRANS (CONJ lw t) in
   let cf = el 3 (snd(strip_comb(concl ch))) in
   let sub_th = prove(list_mk_icomb "subsumed" [cf; cframe0],
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
   let ch2 = MATCH_MP ENSURES_N_FRAME_SUBSUMED (CONJ sub_th ch) in
   let count_eq2 = prove(mk_eq(last(snd(strip_comb(concl ch2))), last(snd(strip_comb w))), ABS_TAC THEN ARITH_TAC) in
   ACCEPT_TAC (REWRITE_RULE[count_eq2] ch2)));;
Printf.printf "*** DEINT_FROM88_N_LC0_REMPOS proved? hyps=%d ***\n" (length(hyp DEINT_FROM88_N_LC0_REMPOS));;

let lc0rempos_ss_fn1 = el 4 (snd(strip_comb(concl LC0_REMPOS_STRONG)));;
let dfnlc0rempos_count = last(snd(strip_comb(snd(dest_imp(snd(strip_forall(concl DEINT_FROM88_N_LC0_REMPOS)))))));;
let count_eq_lc0rempos = prove(mk_eq(snd(dest_abs dfnlc0rempos_count), snd(dest_abs lc0rempos_ss_fn1)),
  REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ARITH_TAC);;
let DEINT_FROM88_N_LC0_REMPOS_FN1 = REWRITE_RULE[count_eq_lc0rempos] DEINT_FROM88_N_LC0_REMPOS;;
let DFD_LC0_REMPOS_ALIGNED = SPECL [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
   `pc:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`]
   (REWRITE_RULE[MC_BRIDGE] DEINT_FROM88_N_LC0_REMPOS_FN1);;
let SWP_S_CORRECT_LC0_REMPOS =
  let r = PROVE_SWPS_CORRECT_CASE (UNDISCH DFD_LC0_REMPOS_ALIGNED) LC0_REMPOS_STRONG in
  GEN_ALL(itlist DISCH (rev(hyp r)) r);;
Printf.printf "*** _SWP_S CORRECT (lc=0, lr>=1) PROVEN: hyps=%d ***\n" (length(hyp SWP_S_CORRECT_LC0_REMPOS));;

(* ---- combine 8 cases -> SWPS_FROM88 ; hole ; phantom-pc elimination ; toplevel ---- *)(* ===== SWPS_FROM88: combine the 8 cases -> unified swpS 0x88->0x710 ===== *)
(* Combine the 8 proven per-(loop_count,loop_remain) sub-cases into one unified swpS 0x88->0x710
   correctness theorem SWPS_FROM88 (the swpS analog of deint's DEINT_FROM88).

   Load after all 8 SWP_S_CORRECT_* theorems are in scope:
     STEADY (lc>=3,lr>=1), LC2 (lc=2,lr>=1), LC1_REMPOS, LC0_REMPOS,
     REM0 (lc>=3,lr=0), REM0_LC2, LC1_REM0, LC0_REM0.
   Each is `!vars. <case precond chain> ==> ensures arm <swpS entry @ pc2+0x88> <functional post> <case C2 frame>`
   where the entry/post/frame are the deint entry/post renamed pc->pc2/deint_mc->swpS_mc (from the
   Stage-D transfer engine PROVE_SWPS_CORRECT_CASE).  All 8 share the SAME functional postcondition;
   entries differ only in X1/X16 (word loop_count/word loop_remain vs the specialized word 0); frames
   differ only in the C1-side (deint) MAYCHANGE leaves + the out_b region (64*loop_count vs 16*nblocks).

   TARGET: a single clean statement with
     - precond = the 50 atoms common to all 8 + {nblocks MOD 4=loop_remain, loop_remain<4,
       64*loop_count+16*loop_remain<2^64, nblocks=4*loop_count+loop_remain} (target_core),
     - entry P = the symbolic STEADY entry (X1=word loop_count, X16=word loop_remain),
     - post Q  = the shared functional postcond,
     - frame   = clean ABI frame C_ABI (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, callee-saved ,,
       memory[out_b,16*nblocks; tag_p,16; ivec_p,16; sp+160,64]).

   PROOF: case-split loop_count in {0,1,2,>=3} x loop_remain in {0,>=1}; kill the arithmetically
   inconsistent branches (two distinct numeral loop_count assumptions -> ARITH_TAC); in each real
   branch dispatch to the matching sub-case via USE_SWPS_CASE_W:
     (1) MATCH_MP_TAC ENSURES_FRAME_SUBSUMED, EXISTS the sub-case's own (raw) C2 frame, and discharge
         `C2 subsumed C_ABI` via the equiv.ml frame idiom [subsumed;FORALL_PAIR_THM;SEQ_PAIR_SPLIT;
         ETA_AX;SOME_FLAGS] then re-wrap + SUBSUMED_MAYCHANGE_TAC.  The out_b 64*loop_count region is
         contained in 16*nblocks after SUBST1_TAC of `nblocks = 4*loop_count+loop_remain`.
     (2) MATCH_MP_TAC the (IMP_IMP/CONJ_ASSOC-uncurried) sub-case theorem; supply the witnesses for the
         antecedent's unpinned existentials (the theorem vars absent from its conclusion: key_p, pc, and
         for the specialized cases loop_remain/loop_count), then discharge every antecedent conjunct with
         ACCEPT / ASM_ARITH_TAC / NONOVERLAPPING_TAC / ASM_REWRITE_TAC / REFL_TAC.
   Degenerate cases (lc in {0,1,2}) are pre-specialized (INST loop_count:=k, and loop_remain:=0 when lr=0)
   so the theorem's frame/entry are literal-consistent with the branch-substituted goal.

   Prereq lemmas already in scope from the Stage-D session: ENSURES_FRAME_SUBSUMED, SEQ_PAIR_SPLIT,
   SUBSUMED_MAYCHANGE_TAC, NONOVERLAPPING_TAC, SOME_FLAGS, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI. *)

let rec strip_all_imp t =
  if is_imp t then let a,b = dest_imp t in let ants,c = strip_all_imp b in (a::ants, c)
  else ([],t);;
let ens_and_ants th = strip_all_imp(snd(strip_forall(concl th)));;

(* The eight cases, keyed by (loop_count-shape, loop_remain-shape). *)
let SWPS_CASES = [
  "STEADY", SWP_S_CORRECT_STEADY;   "LC2", SWP_S_CORRECT_LC2;
  "REM0", SWP_S_CORRECT_REM0;       "REM0_LC2", SWP_S_CORRECT_REM0_LC2;
  "LC1_REM0", SWP_S_CORRECT_LC1_REM0; "LC1_REMPOS", SWP_S_CORRECT_LC1_REMPOS;
  "LC0_REM0", SWP_S_CORRECT_LC0_REM0; "LC0_REMPOS", SWP_S_CORRECT_LC0_REMPOS];;

(* shared postcond Q and symbolic entry P (from STEADY), and the clean ABI frame C_ABI. *)
let post0 = let _,e = ens_and_ants SWP_S_CORRECT_STEADY in el 2 (snd(strip_comb e));;
let entS  = let _,e = ens_and_ants SWP_S_CORRECT_STEADY in el 1 (snd(strip_comb e));;
let C_ABI = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_b:int64, 16 * nblocks);
                  memory :> bytes(tag_p:int64, 16);
                  memory :> bytes(ivec_p:int64, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)]`;;

(* target precond = atoms common to all 8 + the 4 generic bound/shape facts. *)
let rec flat_conj t = if is_conj t then flat_conj(lhand t) @ flat_conj(rand t) else [t];;
let atoms_of th = let ants,_ = ens_and_ants th in
  setify(itlist (fun a acc -> flat_conj a @ acc) ants []);;
let all_case_atoms = map (fun (nm,th) -> atoms_of th) SWPS_CASES;;
let mem_ac t l = List.exists (aconv t) l;;
let common = List.filter (fun t -> List.for_all (mem_ac t) all_case_atoms)
                         (setify(List.concat all_case_atoms));;
let target_core = common @
  [`nblocks MOD 4 = loop_remain`; `loop_remain < 4`;
   `64 * loop_count + 16 * loop_remain < 2 EXP 64`; `nblocks = 4 * loop_count + loop_remain`];;
let target_pre = list_mk_conj target_core;;

let swps_from88_goal =
  let vs = [`in_b:int64`;`out_b:int64`;`len_bits:num`;`tag_p:int64`;`ivec_p:int64`;`key_p:int64`;
            `htab_b:int64`;`tag0:int128`;`nonce:96 word`;`rk:(int128)list`;`inblock:num->int128`;
            `pc:num`;`pc2:num`;`stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`] in
  list_mk_forall(vs, mk_imp(target_pre, list_mk_icomb "ensures" [`arm`; entS; post0; C_ABI]));;

(* unpinned vars = theorem quants absent from its (uncurried) conclusion -> the antecedent existentials. *)
let unpinned_of th =
  let uc = REWRITE_RULE[IMP_IMP;GSYM CONJ_ASSOC] th in
  let vs = fst(strip_forall(concl uc)) in
  let _,c = strip_all_imp(snd(strip_forall(concl uc))) in
  filter (fun v -> not(vfree_in v c)) vs;;

(* specialize a degenerate case: INST loop_count:=k and (if lr=0) loop_remain:=0. *)
let specialize_case lcval lr0 th =
  let insts = (match lcval with Some k -> [mk_small_numeral k, `loop_count:num`] | None -> [])
              @ (if lr0 then [`0`,`loop_remain:num`] else []) in
  if insts = [] then th else INST insts (SPEC_ALL th);;

(* weaken frame to C_ABI, then apply the case theorem with the given existential witnesses. *)
let USE_SWPS_CASE_W wlist case_thm =
  let uc = REWRITE_RULE[IMP_IMP; GSYM CONJ_ASSOC] case_thm in
  let _,e = strip_all_imp(snd(strip_forall(concl uc))) in
  let case_frame = el 3 (snd(strip_comb e)) in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC case_frame THEN CONJ_TAC THENL [
    FIRST_ASSUM(fun th -> if is_eq(concl th) && aconv(lhs(concl th))`nblocks:num` then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REWRITE_TAC[subsumed;FORALL_PAIR_THM;SEQ_PAIR_SPLIT;ETA_AX;SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
    (fun (asl,g) -> let st,st' = rand(rator g), rand g in
       (FIRST_X_ASSUM (fun th -> if rand(concl th) = st' then
           MP_TAC th THEN MAP_EVERY SPEC_TAC [(st',st');(st,st)] else NO_TAC)) (asl,g)) THEN
    REWRITE_TAC[GSYM subsumed; ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC;
    MATCH_MP_TAC uc THEN MAP_EVERY EXISTS_TAC wlist THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE NONOVERLAPPING_TAC ORELSE ASM_REWRITE_TAC[] ORELSE REFL_TAC)];;

let DISPATCH_ONE =
  W(fun (asl,w) ->
    let atms = map (concl o snd) asl in
    let has t = List.exists (aconv t) atms in
    let lr0 = has `loop_remain = 0` in
    let lcval = if has `loop_count=0` then Some 0 else if has `loop_count=1` then Some 1
                else if has `loop_count=2` then Some 2 else None in
    let base_thm =
      (match lcval with Some 0 -> (if lr0 then SWP_S_CORRECT_LC0_REM0 else SWP_S_CORRECT_LC0_REMPOS)
       | Some 1 -> (if lr0 then SWP_S_CORRECT_LC1_REM0 else SWP_S_CORRECT_LC1_REMPOS)
       | Some 2 -> (if lr0 then SWP_S_CORRECT_REM0_LC2 else SWP_S_CORRECT_LC2)
       | _ -> (if lr0 then SWP_S_CORRECT_REM0 else SWP_S_CORRECT_STEADY)) in
    let case_thm = specialize_case lcval lr0 base_thm in
    let wl = map (fun v -> if aconv v `loop_remain:num` && lr0 then `0`
                           else (match lcval with Some k when aconv v `loop_count:num` -> mk_small_numeral k | _ -> v))
                 (unpinned_of case_thm) in
    REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_eq c && (aconv(lhs c)`loop_count:num` || aconv(lhs c)`loop_remain:num`) && is_numeral(rhs c)
      then SUBST_ALL_TAC th else NO_TAC)) THEN
    USE_SWPS_CASE_W wl case_thm);;

let SWPS_FROM88 = prove(swps_from88_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `loop_remain = 0` THEN ASM_CASES_TAC `loop_count = 0` THEN
  ASM_CASES_TAC `loop_count = 1` THEN ASM_CASES_TAC `loop_count = 2` THEN
  W(fun (asl,w) ->
    let atms = map (concl o snd) asl in
    let lc_eqs = filter (fun c -> is_eq c && aconv (lhs c) `loop_count:num` && is_numeral(rhs c)) atms in
    if length(setify(map rhs lc_eqs)) >= 2 then (MAP_EVERY UNDISCH_TAC lc_eqs THEN ARITH_TAC)
    else DISPATCH_ONE));;
Printf.printf "*** SWPS_FROM88 PROVEN: hyps=%d (unified swpS 0x88->0x710, all loop shapes) ***\n"
  (length(hyp SWPS_FROM88));;
(* ===== HOLE_EXISTS: search-free translation-invariant aligned-hole existence ===== *)
(* HOLE_EXISTS: a general, search-free "aligned disjoint code hole exists" lemma, used to eliminate
   the phantom deint-code-location `pc` from _SWP_S_CORRECT (the equiv-transfer artifact) the way
   montmul/emontredc use FIND_HOLE_TAC - but WITHOUT FIND_HOLE's exponential-in-pointer-count search
   (intractable at AES-GCM's 7 regions).

   Given a FINITE set R of memory regions (base:int64, len:num), a block size B, and a 4-divisible
   stride G with G >= B + each region length and (CARD R + 1)*G <= 2^64 (i.e. CARD R + 1 spread
   candidates all fit below 2^64), there is an aligned pc whose (word pc, B) region is nonoverlapping
   with every region in R.  NO assumption about WHERE the regions sit - not even that they fit below
   2^64 - only their sizes/count.

   `nonoverlapping` is TRANSLATION-INVARIANT (it is nonoverlapping_modulo 2^64, comparing relative
   distances mod 2^64), so no absolute-address hypothesis is sound OR needed: only a problem-size
   bound.  This is the crux of the whole lemma - the earlier version carried spurious `val a + l <=
   2^64` non-wrap facts; they are gone.

   Proof: candidates c_m = m*G, m in 0..CARD R (CARD R + 1 of them, each 4-aligned since 4 divides G).
   By SPREAD2 each region overlaps at most one candidate (consecutive candidates are G >= B+l apart,
   and both candidates and their +B extents stay below 2^64, so no wraparound identifies them).  So
   the set of "bad" candidate indices injects into R, hence has CARD <= CARD R < CARD R + 1 =
   CARD(0..CARD R); pigeonhole gives a surviving good index.

   Depends only on the word/int libraries + set/CARD theory + nonoverlapping/nonoverlapping_modulo.
   Loadable standalone (does not need the AES-GCM proof context).  Axiom-free (hyps=0). *)

(* overlap of an [p,p+b) block with region (a,l), all mod 2^64 *)
let overlaps = new_definition
  `overlaps (p:num) (b:num) (a:num) (l:num) <=> ~(nonoverlapping_modulo (2 EXP 64) (p,b) (a,l))`;;

let OVERLAPS_CONG = prove(`overlaps p b a l <=> ?i j. i < b /\ j < l /\ (p + i == a + j) (mod (2 EXP 64))`,
  REWRITE_TAC[overlaps; nonoverlapping_modulo] THEN MESON_TAC[]);;

(* ---- integer discreteness scaffolding for the translation-invariant spread argument ---- *)

(* every integer is <= -1, = 0, or >= 1 (needs discreteness; INT_ARITH cannot do this alone) *)
let INT_TRICH = prove(`!d:int. d <= --(&1) \/ d = &0 \/ &1 <= d`,
  GEN_TAC THEN
  DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC)
    (SPECL [`d:int`; `&0:int`] INT_LT_TOTAL) THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    DISJ1_TAC THEN
    MP_TAC(SPECL [`d:int`; `&0:int`] INT_LT_DISCRETE) THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN
    MP_TAC(SPECL [`&0:int`; `d:int`] INT_LT_DISCRETE) THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* a multiple n*d strictly between -n and n (with n>0) forces d = 0 *)
let MUL_FORCE_ZERO = prove(`!n d:int. &0 < n /\ --n < n*d /\ n*d < n ==> d = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(&1):int < d /\ d < &1` MP_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL[`--(&1):int`;`d:int`;`n:int`] INT_LT_LMUL_EQ) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[INT_MUL_RNEG; INT_MUL_RID] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL[`d:int`;`&1:int`;`n:int`] INT_LT_LMUL_EQ) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[INT_MUL_RID] THEN ASM_REWRITE_TAC[]];
    INT_ARITH_TAC]);;

(* the arithmetic core: two candidates spaced >= b+l apart, both staying below N, cannot have the
   SAME region point (a+j == a+j') hit from both - the congruence gap would have to be an N-multiple
   strictly inside (-N,N), i.e. 0, forcing p+i = p'+i', impossible given the spread. *)
let SPREAD_INT = prove(
 `!(p:num) p' i j i' j' b l (d:int) N.
     p + b + l <= p' /\ p' + b + l <= N /\ i<b /\ j<l /\ i'<b /\ j'<l /\
     (&(p'+i'):int) - &(p+i) - (&j' - &j) = &N * d ==> F`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD] THEN STRIP_TAC THEN
  SUBGOAL_THEN `d:int = &0` (fun th -> SUBST_ALL_TAC th ORELSE ASSUME_TAC th) THENL
   [MP_TAC(SPECL[`&N:int`;`d:int`] MUL_FORCE_ZERO) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN ASM_INT_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    RULE_ASSUM_TAC(REWRITE_RULE[INT_MUL_RZERO]) THEN ASM_INT_ARITH_TAC]);;

(* two candidates spaced >= b+l apart (both extents below 2^64) cannot both overlap one region.
   TRANSLATION-INVARIANT: NO hypothesis on where region base `a` sits. *)
let SPREAD2 = prove(
  `!p p' a l b. p + (b + l) <= p' /\ p' + b + l <= 2 EXP 64
    ==> ~(overlaps p b a l /\ overlaps p' b a l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[OVERLAPS_CONG] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC))
                             (X_CHOOSE_THEN `i':num` (X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(&(p'+i') - &(p+i):int == &j' - &j) (mod &(2 EXP 64))` MP_TAC THENL
   [SUBGOAL_THEN `(&(p+i):int == &(a+j)) (mod &(2 EXP 64)) /\ (&(p'+i'):int == &(a+j')) (mod &(2 EXP 64))`
       MP_TAC THENL [ASM_REWRITE_TAC[GSYM num_congruent];
                     REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN CONV_TAC INTEGER_RULE];
    ALL_TAC] THEN
  REWRITE_TAC[int_congruent] THEN DISCH_THEN(X_CHOOSE_THEN `d:int` (fun eqn ->
    MP_TAC(SPECL[`p:num`;`p':num`;`i:num`;`j:num`;`i':num`;`j':num`;`b:num`;`l:num`;`d:int`;`2 EXP 64`]
                SPREAD_INT) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC eqn THEN INT_ARITH_TAC)));;

(* bridge nonoverlapping (word p,b)(a,l) to the `overlaps` predicate *)
let NONOV_OVERLAPS = prove(`!p b a l. nonoverlapping (word p:int64,b) (a:int64,l) <=> ~(overlaps (p MOD 2 EXP 64) b (val a) l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[overlaps; nonoverlapping; VAL_WORD; DIMINDEX_64] THEN
  REWRITE_TAC[nonoverlapping_modulo] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[] THEN MESON_TAC[CONG_ADD_LCANCEL_EQ; CONG; CONG_LMOD; CONG_REFL; MOD_MOD_REFL]);;

(* ---- arithmetic + counting scaffolding ---- *)
let MULT_LE_R = prove(`!x y G:num. x <= y ==> x * G <= y * G`,
  REWRITE_TAC[LE_MULT_RCANCEL] THEN MESON_TAC[]);;

let MG_LT = prove(`!m c G. m <= c /\ (c + 1) * G <= 2 EXP 64 ==> m * G < 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `G = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC(ARITH_RULE `!cg g E. mg <= cg /\ cg + g <= E /\ 0 < g ==> mg < E`) THEN
    MAP_EVERY EXISTS_TAC [`c * G:num`; `G:num`] THEN
    ASM_SIMP_TAC[MULT_LE_R] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(c + 1) * G <= 2 EXP 64` THEN
      REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES];
      ASM_REWRITE_TAC[LT_NZ]]]);;

let VAL_WORD_MG = prove(`!m G. m * G < 2 EXP 64 ==> val(word(m * G):int64) = m * G`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

let DIV4_MG = prove(
  `!m G. 4 divides G /\ m * G < 2 EXP 64 ==> 4 divides val(word(m * G):int64)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_MG] THEN
  MATCH_MP_TAC DIVIDES_LMUL THEN ASM_REWRITE_TAC[]);;

let GAP = prove(`!m1 m2 G. m1 < m2 ==> m1 * G + G <= m2 * G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m1 + 1`; `m2:num`; `G:num`] MULT_LE_R) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES]);;

let TOPFIT = prove(
  `!m2 c G. m2 <= c /\ (c + 1) * G <= 2 EXP 64 ==> m2 * G + G <= 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m2 + 1`; `c + 1`; `G:num`] MULT_LE_R) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC);;

(* two DISTINCT candidates m1<m2<=c cannot both overlap region (a,l); spacing G >= b+l and top-fit
   (c+1)*G<=2^64 supply SPREAD2's two hypotheses.  NO val-a bound. *)
let UNIQUE_OVL = prove(
 `!c G b a l m1 m2.
    m1 < m2 /\ m2 <= c /\ (c + 1) * G <= 2 EXP 64 /\ b + l <= G
    ==> ~(overlaps (m1 * G) b (val(a:int64)) l /\ overlaps (m2 * G) b (val a) l)`,
 REPEAT STRIP_TAC THEN
 MP_TAC(SPECL [`m1 * G`; `m2 * G`; `val(a:int64)`; `l:num`; `b:num`] SPREAD2) THEN
 ASM_REWRITE_TAC[] THEN
 MP_TAC(SPECL [`m1:num`; `m2:num`; `G:num`] GAP) THEN ASM_REWRITE_TAC[] THEN
 MP_TAC(SPECL [`m2:num`; `c:num`; `G:num`] TOPFIT) THEN ASM_REWRITE_TAC[] THEN
 ASM_ARITH_TAC);;

let UNIQUE_OVL2 = prove(
 `!c G b a l m1 m2.
    m1 <= c /\ m2 <= c /\ (c + 1) * G <= 2 EXP 64 /\ b + l <= G /\
    overlaps (m1 * G) b (val(a:int64)) l /\ overlaps (m2 * G) b (val a) l
    ==> m1 = m2`,
 REPEAT STRIP_TAC THEN
 DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC)
   (SPECL [`m1:num`; `m2:num`] LT_CASES) THENL
  [MP_TAC(SPECL [`c:num`;`G:num`;`b:num`;`a:int64`;`l:num`;`m1:num`;`m2:num`] UNIQUE_OVL) THEN
   ASM_REWRITE_TAC[];
   MP_TAC(SPECL [`c:num`;`G:num`;`b:num`;`a:int64`;`l:num`;`m2:num`;`m1:num`] UNIQUE_OVL) THEN
   ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

let UNIQUE_OVL2_PAIR = prove(
 `!c G b p m1 m2.
    m1 <= c /\ m2 <= c /\ (c + 1) * G <= 2 EXP 64 /\
    b + SND(p:int64#num) <= G /\
    overlaps (m1 * G) b (val(FST p)) (SND p) /\
    overlaps (m2 * G) b (val(FST p)) (SND p)
    ==> m1 = m2`,
 REPEAT GEN_TAC THEN
 MP_TAC(SPECL [`c:num`;`G:num`;`b:num`;`FST(p:int64#num)`;`SND(p:int64#num)`;
               `m1:num`;`m2:num`] UNIQUE_OVL2) THEN
 REWRITE_TAC[]);;

let PIGEON = prove(
 `!S BAD:num->bool. FINITE S /\ BAD SUBSET S /\ CARD BAD < CARD S
                    ==> ?m. m IN S /\ ~(m IN BAD)`,
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `~((S:num->bool) SUBSET BAD)` MP_TAC THENL
  [DISCH_TAC THEN
   SUBGOAL_THEN `(S:num->bool) = BAD` SUBST_ALL_TAC THENL
    [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_ARITH_TAC;
   REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN MESON_TAC[]]);;

let INJ_CARD_LE = prove(
 `!(f:A->B) s t. FINITE t /\ FINITE s /\
          (!x. x IN s ==> f x IN t) /\
          (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
          ==> CARD s <= CARD t`,
 REPEAT STRIP_TAC THEN
 MP_TAC(ISPECL [`f:A->B`; `s:A->bool`] CARD_IMAGE_INJ) THEN
 ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
 MP_TAC(ISPECL [`IMAGE (f:A->B) s`; `t:B->bool`] CARD_SUBSET) THEN
 ASM_REWRITE_TAC[SUBSET; IN_IMAGE] THEN
 DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let PAIR_EXISTS_EQ = prove(
 `!R G B m. (?a l. (a,l) IN (R:int64#num->bool) /\ overlaps (m*G) B (val a) l) <=>
            (?p. p IN R /\ overlaps (m*G) B (val(FST p)) (SND p))`,
 REPEAT GEN_TAC THEN EQ_TAC THENL
  [STRIP_TAC THEN EXISTS_TAC `(a:int64,l:num)` THEN ASM_REWRITE_TAC[FST; SND];
   REWRITE_TAC[EXISTS_PAIR_THM; FST; SND] THEN MESON_TAC[]]);;

let REGION_PAIR = prove(
 `!R b G p:int64#num.
    (!a l. (a,l) IN (R:int64#num->bool) ==> b + l <= G) /\ p IN R
    ==> b + SND p <= G`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 FIRST_X_ASSUM(MP_TAC o SPECL [`FST(p:int64#num)`; `SND(p:int64#num)`]) THEN
 REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[]);;

let CARD_BAD_LE_ABS = prove(
 `!R G B c (f:num->int64#num).
    FINITE R /\ (c + 1) * G <= 2 EXP 64 /\
    (!a l. (a,l) IN (R:int64#num->bool) ==> B + l <= G) /\
    (!m. m IN {m | m IN 0..c /\
                   (?a l. (a,l) IN R /\ overlaps (m*G) B (val a) l)}
         ==> f m IN R /\ overlaps (m*G) B (val(FST(f m))) (SND(f m)))
    ==> CARD {m | m IN 0..c /\
                  (?a l. (a,l) IN R /\ overlaps (m*G) B (val a) l)}
        <= CARD R`,
 REPEAT STRIP_TAC THEN
 MATCH_MP_TAC INJ_CARD_LE THEN EXISTS_TAC `f:num->int64#num` THEN
 ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..c` THEN
   REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
   X_GEN_TAC `m:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(f:num->int64#num) m IN R /\ overlaps (m*G) B (val(FST(f m))) (SND(f m))`
     (fun th -> ACCEPT_TAC(CONJUNCT1 th)) THEN
   FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   MAP_EVERY X_GEN_TAC [`m1:num`; `m2:num`] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; IN_NUMSEG]) THEN
   SUBGOAL_THEN `(f:num->int64#num) m1 IN R /\ overlaps (m1*G) B (val(FST(f m1))) (SND(f m1))`
     STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(f:num->int64#num) m2 IN R /\ overlaps (m2*G) B (val(FST(f m2))) (SND(f m2))`
     STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `m1 <= c /\ m2 <= c` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`R:int64#num->bool`;`B:num`;`G:num`;`(f:num->int64#num) m1`] REGION_PAIR) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   MP_TAC(SPECL [`c:num`;`G:num`;`B:num`;`(f:num->int64#num) m2`;`m1:num`;`m2:num`] UNIQUE_OVL2_PAIR) THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CARD_BAD_LE = prove(
 `!R G B c.
    FINITE R /\ (c + 1) * G <= 2 EXP 64 /\
    (!a l. (a,l) IN (R:int64#num->bool) ==> B + l <= G)
    ==> CARD {m | m IN 0..c /\
                  (?a l. (a,l) IN R /\ overlaps (m*G) B (val a) l)}
        <= CARD R`,
 REPEAT STRIP_TAC THEN
 MP_TAC(SPECL [`R:int64#num->bool`;`G:num`;`B:num`;`c:num`;
               `\m. @p. p IN (R:int64#num->bool) /\ overlaps (m*G) B (val(FST p)) (SND p)`]
              CARD_BAD_LE_ABS) THEN
 ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
 BETA_TAC THEN
 SUBGOAL_THEN `?p. p IN (R:int64#num->bool) /\ overlaps (m*G) B (val(FST p)) (SND p)`
   (MP_TAC o SELECT_RULE) THENL
  [ASM_MESON_TAC[PAIR_EXISTS_EQ]; REWRITE_TAC[]]);;

let HOLE_EXISTS = prove(
 `!R B G.
      FINITE R /\ 0 < B /\ 4 divides G /\
      (!a l. (a,l) IN (R:int64#num->bool) ==> B + l <= G) /\
      (CARD R + 1) * G <= 2 EXP 64
      ==> ?pc. (4 divides val(word pc:int64)) /\
               (!a l. (a,l) IN R ==> nonoverlapping (word pc:int64,B) (a,l))`,
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN
   `?m. m IN 0..CARD(R:int64#num->bool) /\
        ~(m IN {m | m IN 0..CARD R /\
                    (?a l. (a,l) IN R /\ overlaps (m*G) B (val a) l)})`
   STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC PIGEON THEN
   REWRITE_TAC[FINITE_NUMSEG; SUBSET_RESTRICT] THEN
   REWRITE_TAC[CARD_NUMSEG] THEN
   MATCH_MP_TAC(ARITH_RULE `x <= c ==> x < (c+1)-0`) THEN
   MATCH_MP_TAC CARD_BAD_LE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
 FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_ELIM_THM]) THEN
 ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
 DISCH_TAC THEN
 RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
 SUBGOAL_THEN `m * G < 2 EXP 64` ASSUME_TAC THENL
  [MATCH_MP_TAC MG_LT THEN EXISTS_TAC `CARD(R:int64#num->bool)` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
 EXISTS_TAC `m * G` THEN CONJ_TAC THENL
  [MATCH_MP_TAC DIV4_MG THEN ASM_REWRITE_TAC[];
   MAP_EVERY X_GEN_TAC [`a:int64`; `l:num`] THEN DISCH_TAC THEN
   REWRITE_TAC[NONOV_OVERLAPS] THEN
   ASM_SIMP_TAC[MOD_LT] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a:int64`; `l:num`]) THEN
   ASM_REWRITE_TAC[]]);;

Printf.printf "*** HOLE_EXISTS (translation-invariant, no absolute-address hyps) PROVEN: hyps=%d ***\n"
  (length(hyp HOLE_EXISTS));;

(* ---- CARD-bound helpers for discharging (CARD R + 1)*G <= 2^64 on an explicit region set ---- *)
let CARD_INS_LE = prove(`!(x:A) s. FINITE s ==> CARD(x INSERT s) <= CARD s + 1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES] THEN COND_CASES_TAC THEN ARITH_TAC);;

let CARD_LE_7 = prove(`!a b c d e f g:A. CARD {a,b,c,d,e,f,g} <= 7`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL[`a:A`;`{b,c,d,e,f,g}:A->bool`]CARD_INS_LE) THEN
  MP_TAC(ISPECL[`b:A`;`{c,d,e,f,g}:A->bool`]CARD_INS_LE) THEN
  MP_TAC(ISPECL[`c:A`;`{d,e,f,g}:A->bool`]CARD_INS_LE) THEN
  MP_TAC(ISPECL[`d:A`;`{e,f,g}:A->bool`]CARD_INS_LE) THEN
  MP_TAC(ISPECL[`e:A`;`{f,g}:A->bool`]CARD_INS_LE) THEN
  MP_TAC(ISPECL[`f:A`;`{g}:A->bool`]CARD_INS_LE) THEN
  MP_TAC(ISPECL[`g:A`;`{}:A->bool`]CARD_INS_LE) THEN
  REWRITE_TAC[FINITE_INSERT;FINITE_EMPTY;CARD_CLAUSES] THEN ARITH_TAC);;
Printf.printf "*** CARD_LE_7 proven ***\n";;
(* ===== SWPS_PC_EXISTS: phantom-pc existential from a single size bound ===== *)
(* Phantom-pc elimination for _SWP_S_CORRECT.

   The ensures2-transfer gives SWPS_FROM88 (and hence _SWP_S_CORRECT) a spurious deint-code-location
   parameter `pc` with disjointness constraints against the 7 data/code regions - swpS never touches
   `pc`; it is only where the ghost deint image sits in the sideA interm_state.  montmul/emontredc
   eliminate their analogous phantom with FIND_HOLE_TAC, but that tactic is exponential in the number
   of distinct region pointers and is intractable at AES-GCM's 7 (times out).

   This file bridges the general search-free HOLE_EXISTS (DEVEL_swp_S_hole.ml) to the exact
   explicit-conjunction phantom-pc existential SWPS_FROM88 carries, so the phantom can be discharged
   inside _SWP_S_CORRECT via SUBGOAL_THEN + CHOOSE, leaving a clean single-pc2 interface.

   `nonoverlapping` is translation-invariant (nonoverlapping_modulo 2^64), so HOLE_EXISTS - and hence
   the bridge below - needs NO absolute-address ("buffer doesn't wrap 2^64") facts: the ONLY hypothesis
   is a single problem-size bound `16 * nblocks + 1856 <= 2^40`.  (AES-GCM caps nblocks < 2^32, so this
   is astronomically slack; G := 2^40 is 4-divisible, exceeds 1856 + 16*nblocks, and 8*2^40 = 2^43 <=
   2^64 covers the CARD R + 1 = 8 spread candidates.)

   Load after DEVEL_swp_S_hole.ml (HOLE_EXISTS, CARD_LE_7). *)

(* Unfold set-membership over the explicit 7-region set to a 7-way conjunction (generic in P). *)
let unfold_mem = prove(
  `(!a l. (a,l) IN {(word pc2:int64,1856),(in_b:int64,16*nblocks),(out_b:int64,16*nblocks),
                    (htab_b:int64,192),(tag_p:int64,16),(ivec_p:int64,16),
                    (word_add stackpointer (word 160):int64,64)}
          ==> P a l)
   <=> P (word pc2) 1856 /\ P in_b (16*nblocks) /\ P out_b (16*nblocks) /\ P htab_b 192 /\
       P tag_p 16 /\ P ivec_p 16 /\ P (word_add stackpointer (word 160)) 64`,
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN MESON_TAC[]);;

(* The bridge: a single clean fit hypothesis (16*nblocks + 1856 <= 2^40; GCM caps nblocks < 2^32 so
   this is astronomically slack) implies the phantom-pc existential in SWPS_FROM88's exact
   explicit-conjunction shape.  G := 2^40 (4-divisible; > 1856 + 16*nblocks; 8*2^40 = 2^43 <= 2^64).
   NO per-region non-wrap facts (nonoverlapping is translation-invariant).  hyps=0. *)
let SWPS_PC_EXISTS = prove(
  `16 * nblocks + 1856 <= 2 EXP 40
   ==> ?pc. nonoverlapping (word pc:int64,1856) (word pc2:int64,1856) /\
            nonoverlapping (word pc:int64,1856) (in_b:int64,16*nblocks) /\
            nonoverlapping (word pc:int64,1856) (out_b:int64,16*nblocks) /\
            nonoverlapping (word pc:int64,1856) (htab_b:int64,192) /\
            nonoverlapping (word pc:int64,1856) (tag_p:int64,16) /\
            nonoverlapping (word pc:int64,1856) (ivec_p:int64,16) /\
            nonoverlapping (word pc:int64,1856) (word_add stackpointer (word 160):int64,64) /\
            4 divides val (word pc:int64)`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`{(word pc2:int64,1856),(in_b:int64,16*nblocks),(out_b:int64,16*nblocks),
                  (htab_b:int64,192),(tag_p:int64,16),(ivec_p:int64,16),
                  (word_add stackpointer (word 160):int64,64)}`; `1856`; `2 EXP 40`] HOLE_EXISTS) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[unfold_mem] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIVIDES_DIV_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_ARITH_TAC;
      MP_TAC(ISPECL [`(word pc2:int64,1856)`;`(in_b:int64,16*nblocks)`;`(out_b:int64,16*nblocks)`;
        `(htab_b:int64,192)`;`(tag_p:int64,16)`;`(ivec_p:int64,16)`;
        `(word_add stackpointer (word 160):int64,64)`] CARD_LE_7) THEN
      ARITH_TAC];
    REWRITE_TAC[unfold_mem] THEN STRIP_TAC THEN EXISTS_TAC `pc:num` THEN ASM_REWRITE_TAC[]]);;
Printf.printf "*** SWPS_PC_EXISTS (single size-bound, no non-wrap facts) proven: hyps=%d ***\n"
  (length(hyp SWPS_PC_EXISTS));;

(* INTEGRATION into _SWP_S_CORRECT (recipe; requires SWPS_FROM88 in scope):
   The clean _SWP_S_CORRECT statement drops `pc` and the 12 phantom disjointness preconditions,
   REPLACING them with the SINGLE fit bound `16 * val len_bits DIV 128 + 1856 <= 2 EXP 40`
   (nblocks = len_bits DIV 128), which the eventual subroutine caller discharges trivially (GCM caps
   nblocks < 2^32).  There are NO `val ptr + size <= 2^64` non-wrap facts - `nonoverlapping` is
   translation-invariant, so none are sound or needed.  Inside the proof, right before the leg-2
   `MATCH_MP_TAC SWPS_FROM88_EXP_PCID`, insert:

     SUBGOAL_THEN <phantom-pc existential> STRIP_ASSUME_TAC THENL
      [MATCH_MP_TAC SWPS_PC_EXISTS THEN ... discharge the fit bound ; ALL_TAC] THEN
     ... then the CHOSEN pc + its 7 nonoverlaps + `4 divides val(word pc)` feed SWPS_FROM88's
     pc-antecedents (via DIVIDES_4_VAL_WORD_64 for the raw `4 divides pc`), so MATCH_MP_TAC
     SWPS_FROM88_EXP_PCID closes as before but with `pc` supplied from the CHOSE rather than a
     universally-quantified spec parameter.

   Net: _SWP_S_CORRECT's precond has NO phantom pc and NO absolute-address facts; the only addition
   over _SWP_DEINT_CORRECT is the single mild fit bound, matching montmul/emontredc's clean-interface
   standard as closely as the variable-length AES-GCM buffers allow. *)
(* ===== _SWP_S_CORRECT: toplevel 0x2c->0x710, phantom-pc-free single-size-bound interface ===== *)
(* Phantom-pc-ELIMINATED top-level _SWP_S_CORRECT.  The goal
   carries NO phantom deint-code-location `pc` (and none of its 13 disjointness constraints); instead
   it takes a SINGLE standard "the problem is not astronomically large" precondition:
     16 * val len_bits DIV 128 + 1856 <= 2 EXP 40
   (AES-GCM caps the block count nblocks = val len_bits DIV 128 well below 2^32, so this is
   astronomically slack).  There are NO `val ptr + size <= 2^64` non-wrap facts: `nonoverlapping` is
   translation-invariant (nonoverlapping_modulo 2^64), so absolute-address bounds are neither sound
   nor needed.

   Inside the proof, SWPS_PC_EXISTS (proven earlier from just this size bound) discharges the
   existence of a disjoint aligned ghost-code location pc, which is X_CHOOSE'd and fed to SWPS_FROM88
   exactly as the phantom version did.  So the interface is clean (single-pc, montmul-grade modulo the
   one mild fit fact) while the proof body is the standard preamble + SWPS_FROM88 leg after the CHOOSE.

   Load after DEVEL_swp_S_combine.ml (SWPS_FROM88) + DEVEL_swp_S_hole.ml + DEVEL_swp_S_phantom.ml
   (SWPS_PC_EXISTS) + swpS_mc/SWPS_EXEC + the deint-prefix preamble helpers. *)

let SWPS_FROM88_EXP = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] SWPS_FROM88;;
let SWPS_FROM88_EXP_PCID =
  GENL (subtract (fst(strip_forall(concl SWPS_FROM88_EXP))) [`pc:num`]) (SPEC_ALL SWPS_FROM88_EXP);;

(* nonoverlapping is symmetric (nonoverlapping_modulo is): used to derive the reverse-direction
   pc-nonoverlaps SWPS_FROM88 wants (e.g. `nonoverlapping (htab_b,192) (word pc,1856)`) from the
   forward ones SWPS_PC_EXISTS supplies. *)
let NONOV_SYM = prove(`!a b. nonoverlapping a b ==> nonoverlapping b a`,
  REWRITE_TAC[FORALL_PAIR_THM; nonoverlapping] THEN MESON_TAC[NONOVERLAPPING_MODULO_SYM]);;

let seqpred_2 =
  subst[`in_p:int64`,`in_b:int64`;`out_p:int64`,`out_b:int64`;`htable_p:int64`,`htab_b:int64`]
    (let rec sai t = if is_imp t then sai(snd(dest_imp t)) else t in
     el 1 (snd(strip_comb(sai(snd(strip_forall(concl SWP_S_CORRECT_STEADY)))))));;

(* SWPS_PC_EXISTS renamed to the C-args interface (in_b->in_p, out_b->out_p, htab_b->htable_p). *)
let SWPS_PC_EXISTS_P =
  INST [`in_p:int64`,`in_b:int64`; `out_p:int64`,`out_b:int64`; `htable_p:int64`,`htab_b:int64`]
       SWPS_PC_EXISTS;;

let AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc2
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p:int64, 16 * val len_bits DIV 128); (tag_p:int64, 16); (ivec_p:int64, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc2:int64, LENGTH (swpS_mc:((8)word)list));
         (in_p:int64,  16 * val len_bits DIV 128); (key_p:int64, 176); (htable_p:int64, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p:int64, 16 * val len_bits DIV 128); (tag_p:int64, 16); (ivec_p:int64, 16);
         (word_add stackpointer (word 160), 64)] /\
       16 * val len_bits DIV 128 + 1856 <= 2 EXP 40
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc2) swpS_mc /\
           read PC s = word (pc2 + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,11) s = MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s)
      (\s. read PC s = word (pc2 + 0x710) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (val len_bits DIV 128 + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst SWPS_EXEC] THEN
  ABBREV_TAC `nblocks = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN STRIP_TAC THEN
  (*** discharge the ghost-code-location pc existentially from the single fit bound (SWPS_PC_EXISTS),
       then CHOOSE it.  We CHOOSE the FULL both-directions bundle (7 forward + 6 reverse nonoverlaps +
       4 divides val(word pc)) so the resulting assumption set is a SUPERSET of what the phantom
       version took as preconditions - leg 2 then closes IDENTICALLY (no reliance on NONOVERLAPPING_TAC
       reproving reverse-from-forward in the rich leg-2 context).  SWPS_PC_EXISTS gives the 7 forward +
       divides; the 6 reverse follow by NONOV_SYM.  NO absolute-address facts - nonoverlapping is
       translation-invariant. ***)
  SUBGOAL_THEN
   `?pc. nonoverlapping (word pc:int64,1856) (word pc2:int64,1856) /\
         nonoverlapping (word pc:int64,1856) (in_p:int64,16*nblocks) /\
         nonoverlapping (word pc:int64,1856) (out_p:int64,16*nblocks) /\
         nonoverlapping (word pc:int64,1856) (htable_p:int64,192) /\
         nonoverlapping (word pc:int64,1856) (tag_p:int64,16) /\
         nonoverlapping (word pc:int64,1856) (ivec_p:int64,16) /\
         nonoverlapping (word pc:int64,1856) (word_add stackpointer (word 160):int64,64) /\
         nonoverlapping (in_p:int64,16*nblocks) (word pc:int64,1856) /\
         nonoverlapping (out_p:int64,16*nblocks) (word pc:int64,1856) /\
         nonoverlapping (htable_p:int64,192) (word pc:int64,1856) /\
         nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
         nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
         nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
         4 divides val (word pc:int64)`
   (X_CHOOSE_TAC `pc:num`) THENL
   [MP_TAC(SPEC_ALL SWPS_PC_EXISTS_P) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC); ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `pc:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `pc:num` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC NONOV_SYM THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (*** SWPS_FROM88's antecedent carries the RAW `4 divides pc`, but the CHOSE gives
       `4 divides val(word pc)`.  Convert the assumption forward (val(word pc) form -> raw pc form)
       via DIVIDES_4_VAL_WORD_64 so leg 2's `FIRST_ASSUM ACCEPT_TAC` closes it exactly as the phantom
       version did.  (GSYM-on-goal would loop: `4 divides ?n` -> `4 divides val(word ?n)` re-matches.) ***)
  RULE_ASSUM_TAC(REWRITE_RULE[DIVIDES_4_VAL_WORD_64]) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN
  ENSURES_SEQUENCE_TAC `pc2 + 0x88` seqpred_2 THEN CONJ_TAC THENL
   [(*** leg 1: preamble pc2+0x2c -> pc2+0x88 (verbatim) ***)
    REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce 2)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `key_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c) &&
        can (find_term (fun t -> t = `160`)) (lhs c))) THEN
    ARM_STEPS_TAC SWPS_EXEC (1--23) THEN ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X11_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X12_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X13_SETUP th) else NO_TAC);
      ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    (*** leg 2: main body pc2+0x88 -> pc2+0x710 via SWPS_FROM88 (pc supplied from the CHOSE) ***)
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC seqpred_2 THEN CONJ_TAC THENL [
      GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SWPS_FROM88_EXP_PCID THEN
      TRY(W(fun(_,w)-> if is_exists w then EXISTS_TAC `key_p:int64` else ALL_TAC)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE NONOVERLAPPING_TAC ORELSE
       (EXPAND_TAC "nblocks" THEN UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC) ORELSE ASM_REWRITE_TAC[])]]);;
Printf.printf "*** _SWP_S_CORRECT (phantom-pc ELIMINATED, single size-bound interface) PROVEN: hyps=%d ***\n"
  (length(hyp AES_GCM_ENC_KERNEL_X4_SCALAR_IV_MEM_LATE_TAG_SCALAR_RK_SWP_S_CORRECT));;

check_axioms ();;

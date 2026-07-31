(* ============================================================================
   Stage B of the _swp_S functional-correctness transfer: STRENGTHEN the proved
   whole-function equivalence so its EXIT relates the full functional output of
   the two runs (out-buffer, tag, ivec memory all equal at 0x710), not merely
   the internal registers.  This output-agreement (the transfer's `eqout`) is
   what carries "swpS's output = deint's proven-correct output" and is exactly
   what ENSURES2_ENSURES_N needs in Stage D.

   Load AFTER aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_S.ml
   (which supplies deint_mc/swpS_mc, DEINT_EXEC/SWPS_EXEC, the pre-POSTAMBLE
   equivalence legs PREAMBLE_G/MAIN_G/REDUCE_G/CBZ_G/REMLOOP_G, graft_goal/
   GRAFT_TAC, trans_exact/trans_weaken, step_ro, comp128, maych_post,
   post_entry_body/post_exit_body/post_precond, and the STEADY equivalence
   SWP_DEINT_SWPS_EQUIV_STEADY), and after equiv.ml (mk_equiv_regs etc.).

   Result: STEADY_STRONG, the strengthened whole-function equivalence
   0x88 -> 0x710 for the steady case (loop_count>=2, loop_remain>=1) whose exit
   asserts, between the deint run s1 and the swpS run s2:
       read Q30 s1 = read Q30 s2                                    (GHASH acc)
       read (bytes32 (ivec_p+12)) s1 = ... s2                       (counter lane)
       !j<nblocks. read (bytes128 (out_b+16j)) s1 = ... s2          (ciphertext)
       read (bytes128 tag_p)  s1 = read (bytes128 tag_p)  s2        (TAG)
       read (bytes128 ivec_p) s1 = read (bytes128 ivec_p) s2        (IVEC)

   CRITICAL LESSON: ctr_block/nonce are FREE VARS (type ?NNNNNN), not constants.
   f_tagivec is built from SWP_DEINT_SWPS_EQUIV_STEADY's EXACT rhs terms so the
   nonce var matches; a hand-parsed `nonce:(96)word` is a DIFFERENT var and the
   graft's final ACCEPT_TAC fails.  Keep type_invention_error FALSE around the
   trans_weaken composition (its ,, / SUBSUMED_REFL needs free type inference).
   ============================================================================ *)

let ssub h n = let nl=String.length n and hl=String.length h in
  let rec g i = if i+nl>hl then false else if String.sub h i nl = n then true else g(i+1) in g 0;;

(* ---- f_tagivec: absolute tag/ivec memory values (exact terms from the theorem) ---- *)
let concl_steady = concl SWP_DEINT_SWPS_EQUIV_STEADY;;
let ivec_rhs = rhs (find_term (fun t -> is_eq t &&
   (match lhs t with Comb(Comb(Const("read",_),c),_) -> ssub (string_of_term c) "bytes128 ivec_p" | _->false))
   concl_steady);;
let tag_rhs = rhs (find_term (fun t -> is_eq t &&
   (match lhs t with Comb(Comb(Const("read",_),c),_) -> ssub (string_of_term c) "bytes128 tag_p" | _->false))
   concl_steady);;
let mk_read comp s = list_mk_icomb "read" [comp; s];;
let f_tagivec = list_mk_abs([`s1:armstate`;`s2:armstate`], list_mk_conj [
    mk_eq(mk_read `memory :> bytes128 tag_p` `s1:armstate`, tag_rhs);
    mk_eq(mk_read `memory :> bytes128 tag_p` `s2:armstate`, tag_rhs);
    mk_eq(mk_read `memory :> bytes128 ivec_p` `s1:armstate`, ivec_rhs);
    mk_eq(mk_read `memory :> bytes128 ivec_p` `s2:armstate`, ivec_rhs)]);;

(* ---- frame-preservation tactic for the two memory reads (needs ti_extra nonoverlaps) ---- *)
let FP_TAGIVEC_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN BETA_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th)) THEN
  W(fun (asl,w) ->
    let h1 = snd(el 1 asl) and h2 = snd(el 0 asl) in
    MAP_EVERY (fun c ->
      SUBGOAL_THEN (mk_conj(
          mk_eq(list_mk_icomb "read" [c;`s_final:armstate`], list_mk_icomb "read" [c;`s:armstate`]),
          mk_eq(list_mk_icomb "read" [c;`s_final2:armstate`], list_mk_icomb "read" [c;`s2:armstate`])))
        STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [step_ro h1; step_ro h2]; ALL_TAC])
      [`memory :> bytes128 tag_p`; `memory :> bytes128 ivec_p`] THEN
    ASM_REWRITE_TAC[]);;

(* graft_goal + extra precond/quantifiers (mirrors main_gpm_goal). *)
let graft_goal_extra leg f extra qs_extra =
  let gg = graft_goal (concl leg) f in
  let q2,_ = strip_forall gg in
  let pre = fst(dest_imp (snd(strip_forall (concl leg)))) in
  let _,cc = dest_imp (snd(strip_forall gg)) in
  list_mk_forall(union q2 qs_extra, mk_imp(mk_conj(pre,extra), cc));;

let ti_extra = `nonoverlapping (tag_p:int64,16) (out_b:int64,16*nblocks) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
   nonoverlapping (ivec_p:int64,16) (out_b:int64,16*nblocks) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)`;;

let gti leg = prove(graft_goal_extra leg f_tagivec ti_extra [`tag_p:int64`;`ivec_p:int64`],
    REPEAT STRIP_TAC THEN GRAFT_TAC f_tagivec FP_TAGIVEC_TAC leg);;

(* ---- graft f_tagivec onto all 5 pre-POSTAMBLE legs (all hyps=0) ---- *)
let PA_TI = gti PREAMBLE_G;;
let MN_TI = gti MAIN_G;;
let RD_TI = gti REDUCE_G;;
let CB_TI = gti CBZ_G;;
let RL_TI = gti REMLOOP_G;;

(* weaken lemma for the 0x4b4 seam (MN_TI.post -> RD_TI.pre). *)
let mk_weaken post pre =
  mk_forall(`s:armstate`, mk_forall(`s':armstate`,
    mk_imp(mk_comb(post,`(s:armstate,s':armstate)`), mk_comb(pre,`(s:armstate,s':armstate)`))));;
let WEAKEN_TAC =
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MESON_TAC[];;
let po2 th = List.nth (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th))))))) 2;;
let pr2 th = List.nth (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl th))))))) 1;;
let wk_mr_ti = prove(mk_weaken (po2 MN_TI) (pr2 RD_TI), WEAKEN_TAC);;

(* ---- recompose the strengthened pre-POSTAMBLE composite (0x88 -> 0x6fc) ---- *)
let c_pre_ti =
  let pg = UNDISCH (SPEC_ALL PA_TI) in
  let mg = UNDISCH (SPEC_ALL MN_TI) in
  let rg = UNDISCH (SPEC_ALL RD_TI) in
  let cg = UNDISCH (SPEC_ALL CB_TI) in
  let lg = UNDISCH (SPEC_ALL RL_TI) in
  let c1 = trans_exact pg mg in
  let c2 = trans_weaken c1 wk_mr_ti rg in
  let c3 = trans_exact c2 cg in
  trans_exact c3 lg;;

Printf.printf "*** Stage B: c_pre_ti (0x88->0x6fc, strengthened) built, hyps=%d ***\n"
  (length(hyp c_pre_ti));;

(* ---- strengthened POSTAMBLE goal pieces (entry += f_tagivec, exit += out/tag/ivec eq) ---- *)
let ftv12 =
  let b = list_mk_comb(f_tagivec, [`s1:armstate`;`s2:armstate`]) in
  conjuncts (rhs(concl(REWRITE_CONV[] b)));;
let outeq_at sv1 sv2 =
  let ad = mk_binop `word_add:int64->int64->int64` `out_b:int64` (mk_comb(`word:num->int64`,`16 * j`)) in
  mk_forall(`j:num`, mk_imp(`j < nblocks`, mk_eq(mk_read (comp128 ad) sv1, mk_read (comp128 ad) sv2)));;
let tageq_at sv1 sv2 = mk_eq(mk_read `memory :> bytes128 tag_p` sv1, mk_read `memory :> bytes128 tag_p` sv2);;
let iveceq_at sv1 sv2 = mk_eq(mk_read `memory :> bytes128 ivec_p` sv1, mk_read `memory :> bytes128 ivec_p` sv2);;
let post_entry_strong sv1 sv2 = list_mk_conj (conjuncts (post_entry_body (sv1,sv2)) @ ftv12);;
let post_exit_strong sv1 sv2 =
  list_mk_conj (conjuncts (post_exit_body (sv1,sv2)) @ [outeq_at sv1 sv2; tageq_at sv1 sv2; iveceq_at sv1 sv2]);;

(* strengthened precondition = post_precond + the 3 out/tag/ivec nonoverlaps needed to
   forward the out-buffer forall and separate tag_p/ivec_p across the postamble stores. *)
let post_precond_strong = list_mk_conj (conjuncts post_precond @ [
   `nonoverlapping (out_b:int64,16*nblocks) (tag_p:int64,16)`;
   `nonoverlapping (out_b:int64,16*nblocks) (ivec_p:int64,16)`;
   `nonoverlapping (tag_p:int64,16) (ivec_p:int64,16)`]);;

(* entry_B (at 0x70c): the facts leg B needs.  Both sides. *)
let entryB_body sv1 sv2 = list_mk_conj [
  mk_eq(mk_read `X3` sv1, `tag_p:int64`); mk_eq(mk_read `X3` sv2, `tag_p:int64`);
  mk_eq(mk_read `X4` sv1, `ivec_p:int64`); mk_eq(mk_read `X4` sv2, `ivec_p:int64`);
  mk_eq(mk_read `X14` sv1, mk_read `X14` sv2);   (* counter value equal (for the store) *)
  mk_eq(mk_read `Q30` sv1, mk_read `Q30` sv2);   (* GHASH accumulator equal *)
  mk_eq(mk_read `memory :> bytes128 tag_p` sv1, mk_read `Q30` sv1);
  mk_eq(mk_read `memory :> bytes128 tag_p` sv2, mk_read `Q30` sv2);
  mk_eq(mk_read `memory :> bytes128 ivec_p` sv1, ivec_rhs);
  mk_eq(mk_read `memory :> bytes128 ivec_p` sv2, ivec_rhs);
  (let ad = mk_binop `word_add:int64->int64->int64` `out_b:int64` (mk_comb(`word:num->int64`,`16 * j`)) in
   mk_forall(`j:num`, mk_imp(`j < nblocks`, mk_eq(mk_read (comp128 ad) sv1, mk_read (comp128 ad) sv2)))) ];;

(* POSTAMBLE_A goal: 0x6fc -> 0x70c (4 instrs), entry = post_entry_strong, exit = entryB_body. *)
let postA_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
   `stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`;`tag0:int128`;`nonce:(96)word`;`rk:(int128)list`],
  mk_imp(post_precond_strong,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x6fc)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x6fc)`;
          post_entry_strong `s1:armstate` `s2:armstate`]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x70c)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x70c)`;
          entryB_body `s1:armstate` `s2:armstate`]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_post,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_post,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 4`; `\(s:armstate). 4`]));;

(* POSTAMBLE_B goal: 0x70c -> 0x710 (1 instr, the ivec store), entry = entryB_body,
   exit = post_exit_strong (full output agreement). *)
let postB_goal = list_mk_forall(
  [`pc:num`;`pc2:num`;`in_b:int64`;`out_b:int64`;`htab_b:int64`;`tag_p:int64`;`ivec_p:int64`;
   `stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`;`tag0:int128`;`nonce:(96)word`;`rk:(int128)list`],
  mk_imp(post_precond_strong,
    list_mk_icomb "ensures2"
      [`arm`;
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x70c)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x70c)`;
          entryB_body `s1:armstate` `s2:armstate`]);
       mk_gabs(`(s1:armstate,s2:armstate)`, list_mk_conj [
          `aligned_bytes_loaded s1 (word pc) deint_mc`; `read PC s1 = word (pc + 0x710)`;
          `aligned_bytes_loaded s2 (word pc2) swpS_mc`; `read PC s2 = word (pc2 + 0x710)`;
          post_exit_strong `s1:armstate` `s2:armstate`]);
       mk_gabs(`(s1:armstate,s2:armstate)`,mk_gabs(`(s1':armstate,s2':armstate)`,
          mk_conj(list_mk_comb(maych_post,[`s1:armstate`;`s1':armstate`]),
                  list_mk_comb(maych_post,[`s2:armstate`;`s2':armstate`]))));
       `\(s:armstate). 1`; `\(s:armstate). 1`]));;

(* word_join injectivity (forward) at the two widths we need. *)
let WJ_INJ = prove(
  `!(a:(64)word) (b:(64)word) c d.
      (word_join a b :(128)word = word_join c d) ==> a = c /\ b = d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; DIMINDEX_64; DIMINDEX_128] THEN
  DISCH_TAC THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL [
    FIRST_X_ASSUM(MP_TAC o SPEC `i + 64`) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> i + 64 < 128`;
       ARITH_RULE `i < 64 ==> ~(i + 64 < 64)`; ARITH_RULE `(i + 64) - 64 = i`];
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> i < 128`] ]);;

let WJ_INJ32 = prove(
  `!(a:(32)word) (b:(32)word) c d.
      (word_join a b :(64)word = word_join c d) ==> a = c /\ b = d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; DIMINDEX_32; DIMINDEX_64] THEN
  DISCH_TAC THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL [
    FIRST_X_ASSUM(MP_TAC o SPEC `i + 32`) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 32 ==> i + 32 < 64`;
       ARITH_RULE `i < 32 ==> ~(i + 32 < 32)`; ARITH_RULE `(i + 32) - 32 = i`];
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 32 ==> i < 64`] ]);;

let addnorm = WORD_RULE `word_add (word_add ivec_p (word 8)) (word 4):int64 = word_add ivec_p (word 12)`;;

(* ---- POSTAMBLE_B: 0x70c -> 0x710 (the single ivec-store instruction) ---- *)
let postb_pin = [`X0`;`X2`;`X6`;`SP`;`X3`;`X4`;`X16`;`X14`;`Q30`];;
let split64 th = CONV_RULE(BINOP_CONV(GEN_REWRITE_CONV I [el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)])) th;;
let sta_B = ref ([]:(int*thm)list);;
let entB_saved = ref ([]:thm list);;
let ENTB_SNAP (asl,w) =
  entB_saved := map snd (List.filter (fun (_,th)->let s=string_of_term(concl th) in
     (ssub s "read Q30 s0 = read Q30 s0'") || (ssub s "read X14 s0 = read X14 s0'") ||
     (ssub s "bytes128 ivec_p" && ssub s "reversefields") ||
     (ssub s "word_add out_b (word (16 * j))")) asl);
  ALL_TAC(asl,w);;

let POSTAMBLE_B = prove(postB_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  ENTB_SNAP THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--1) sta_B (Some (replicate postb_pin 1)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--1) (1--1) sta_B (Some (replicate postb_pin 1)) THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    W(fun (asl,w) ->
      let fL = snd(find (fun (_,th)->match concl th with Comb(Comb(_,a),b) when is_var a && is_var b && name_of a="s0" && name_of b="s1" && ssub(string_of_term(concl th))"MAYCHANGE"->true|_->false) asl) in
      let fR = snd(find (fun (_,th)->match concl th with Comb(Comb(_,a),b) when is_var a && is_var b && name_of a="s0'" && name_of b="s1'" && ssub(string_of_term(concl th))"MAYCHANGE"->true|_->false) asl) in
      let fwd c st0 st1 fr = SUBGOAL_THEN (mk_eq(mk_read c st1, mk_read c st0)) SUBST1_TAC THENL [step_ro fr; ALL_TAC] in
      let iv0 = find (fun th->ssub(string_of_term(concl th))"ivec_p) s0 =") !entB_saved in
      let iv0' = find (fun th->ssub(string_of_term(concl th))"ivec_p) s0' =") !entB_saved in
      let lv th = CONV_RULE (LAND_CONV (GEN_REWRITE_CONV I [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)])) th in
      let outer = MATCH_MP WJ_INJ (TRANS (lv iv0) (SYM (lv iv0'))) in
      let b64_8_eq = CONJUNCT1 outer in         (* bytes64(ivec_p+8) s0 = s0' *)
      let b64_0_eq = CONJUNCT2 outer in         (* bytes64 ivec_p s0 = s0' *)
      let b8p = MATCH_MP WJ_INJ32 (split64 b64_8_eq) in
      let b8eq = CONJUNCT2 b8p in               (* bytes32(ivec_p+8) *)
      let b0p = MATCH_MP WJ_INJ32 (split64 b64_0_eq) in
      let b4eq = CONJUNCT1 b0p and b0eq = CONJUNCT2 b0p in
      MP_TAC (end_itlist CONJ !entB_saved) THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
      TRY(fwd `Q30` `s0:armstate` `s1:armstate` fL THEN fwd `Q30` `s0':armstate` `s1':armstate` fR THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      TRY(GEN_TAC THEN DISCH_TAC THEN fwd `memory :> bytes128 (word_add out_b (word (16 * j)))` `s0:armstate` `s1:armstate` fL THEN fwd `memory :> bytes128 (word_add out_b (word (16 * j)))` `s0':armstate` `s1':armstate` fR THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
      TRY(GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
          GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
          REWRITE_TAC[addnorm] THEN
          fwd `memory :> bytes32 (word_add ivec_p (word 8))` `s0:armstate` `s1:armstate` fL THEN
          fwd `memory :> bytes32 (word_add ivec_p (word 8))` `s0':armstate` `s1':armstate` fR THEN
          fwd `memory :> bytes32 (word_add ivec_p (word 4))` `s0:armstate` `s1:armstate` fL THEN
          fwd `memory :> bytes32 (word_add ivec_p (word 4))` `s0':armstate` `s1':armstate` fR THEN
          fwd `memory :> bytes32 ivec_p` `s0:armstate` `s1:armstate` fL THEN
          fwd `memory :> bytes32 ivec_p` `s0':armstate` `s1':armstate` fR THEN
          ASM_REWRITE_TAC[b8eq; b4eq; b0eq] THEN NO_TAC));
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;
Printf.printf "*** POSTAMBLE_B PROVED hyps=%d ***\n" (length(hyp POSTAMBLE_B));;

(* ---- POSTAMBLE_A: 0x6fc -> 0x70c (4 instrs: the tag rev64+store + counter shuffles) ---- *)
let sta_A = ref ([]:(int*thm)list);;
let outA_saved = ref ([]:thm list);;
let OUTA_SNAP (asl,w) =
  outA_saved := map snd (List.filter (fun (_,th)->ssub (string_of_term(concl th)) "word_add out_b (word (16 * j))") asl);
  ALL_TAC(asl,w);;
let POSTAMBLE_A = prove(postA_goal,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst DEINT_EXEC; fst SWPS_EXEC] THEN ENSURES2_INIT_TAC "s0" "s0'" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mk_equiv_regs]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then CONJUNCTS_THEN ASSUME_TAC th
     else if is_exists (concl th) then CHOOSE_THEN ASSUME_TAC th else fail())) THEN
  OUTA_SNAP THEN
  ARM_N_STEPS_AND_ABBREV_TAC DEINT_EXEC (1--4) sta_A (Some (replicate postb_pin 4)) THEN
  ARM_N_STEPS_AND_REWRITE_KEEP_TAC SWPS_EXEC (1--4) (1--4) sta_A (Some (replicate postb_pin 4)) THEN
  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (* out forall: forward entry out-forall s4<-s0 both sides.  The s0->s4 frame writes
       tag_p + ivec[12] + regs, NOT out_b, so it forwards with out_b-vs-tag_p/ivec_p
       nonoverlaps (in post_precond_strong). *)
    W(fun (asl,w) ->
      let fL = snd(find (fun (_,th)->match concl th with Comb(Comb(_,a),b) when is_var a && is_var b && name_of a="s0" && name_of b="s4" && ssub(string_of_term(concl th))"MAYCHANGE"->true|_->false) asl) in
      let fR = snd(find (fun (_,th)->match concl th with Comb(Comb(_,a),b) when is_var a && is_var b && name_of a="s0'" && name_of b="s4'" && ssub(string_of_term(concl th))"MAYCHANGE"->true|_->false) asl) in
      let fwd c st0 st1 fr = SUBGOAL_THEN (mk_eq(mk_read c st1, mk_read c st0)) SUBST1_TAC THENL [step_ro fr; ALL_TAC] in
      MP_TAC (end_itlist CONJ !outA_saved) THEN STRIP_TAC THEN
      GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `nonoverlapping (word_add out_b (word (16*j)):int64,16) (tag_p:int64,16) /\
                    nonoverlapping (word_add out_b (word (16*j)):int64,16) (ivec_p:int64,16)`
        STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
      fwd `memory :> bytes128 (word_add out_b (word (16 * j)))` `s0:armstate` `s4:armstate` fL THEN
      fwd `memory :> bytes128 (word_add out_b (word (16 * j)))` `s0':armstate` `s4':armstate` fR THEN
      ASM_SIMP_TAC[]);
    MONOTONE_MAYCHANGE_CONJ_TAC ]);;
Printf.printf "*** POSTAMBLE_A PROVED hyps=%d ***\n" (length(hyp POSTAMBLE_A));;

(* ---- compose POSTAMBLE_A ++ POSTAMBLE_B (exact seam 0x70c = entryB_body) ---- *)
let poA = List.nth (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl POSTAMBLE_A))))))) 2;;
let prB = List.nth (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl POSTAMBLE_B))))))) 1;;
Printf.printf "POSTAMBLE_A.exit aconv POSTAMBLE_B.entry (0x70c seam): %b\n" (aconv poA prB);;
let POSTAMBLE_STRONG = trans_exact (UNDISCH(SPEC_ALL POSTAMBLE_A)) (UNDISCH(SPEC_ALL POSTAMBLE_B));;
Printf.printf "*** POSTAMBLE_STRONG (0x6fc->0x710, step \\s.4+1=5) built, hyps=%d ***\n"
  (length(hyp POSTAMBLE_STRONG));;

(* ---- compose c_pre_ti ++ POSTAMBLE_STRONG (weakened seam 0x6fc) ---- *)
let cpost = List.nth (snd(strip_comb(concl c_pre_ti))) 2;;
let pspre = List.nth (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl (DISCH_ALL POSTAMBLE_STRONG)))))))) 1;;
let wk_seam = prove(mk_weaken cpost pspre, WEAKEN_TAC);;
let STEADY_STRONG = trans_weaken c_pre_ti wk_seam POSTAMBLE_STRONG;;
Printf.printf "*** STEADY_STRONG (whole-fn 0x88->0x710, FULL output agreement) built, hyps=%d ***\n"
  (length(hyp STEADY_STRONG));;

(* verify the strengthened exit relates the full functional output *)
let ss_post = List.nth (snd(strip_comb(concl STEADY_STRONG))) 2;;
let () =
  let s = string_of_term ss_post in
  Printf.printf "STEADY_STRONG exit @0x710 carries:  Q30 s1=s2 %b | out forall %b | tag128 %b | ivec128 %b\n"
    (ssub s "read Q30 s1 = read Q30 s2")
    (ssub s "word_add out_b (word (16 * j))")
    (ssub s "read (memory :> bytes128 tag_p) s1 = read (memory :> bytes128 tag_p) s2")
    (ssub s "read (memory :> bytes128 ivec_p) s1 = read (memory :> bytes128 ivec_p) s2");;

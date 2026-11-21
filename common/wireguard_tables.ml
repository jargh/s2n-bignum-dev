(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Explicit tables for the 16-word states of BLAKE2s and ChaCha20, used to   *)
(* evaluate the specifications of common/rfc7693.ml and common/rfc8439.ml,   *)
(* both on constants (tests/wireguard/wg_eval.ml) and on symbolic values,    *)
(* such as the abbreviations of a simulation of machine code (the proofs in  *)
(* arm/proofs/wireguard).                                                    *)
(*                                                                           *)
(* The states are functions num->int32 of which only the values below 16     *)
(* matter (below 8 for the BLAKE2s chained state). Evaluation keeps them as  *)
(* explicit tables \i. EL i [c0; ...; c15], related to the actual states by  *)
(* wg_agree n v w (v and w agree below n), as tests/mlkem/fips202_eval.ml    *)
(* does for the Keccak lanes. Each update of four entries (BLAKE2s G or the  *)
(* ChaCha20 quarter round) is evaluated on a table, and the symbolic version *)
(* identifies the new entries with given terms (WG_SYM_G_STEP).              *)
(* ========================================================================= *)

needs "common/rfc7693.ml";;
needs "common/rfc8439.ml";;

let wg_agree = new_definition
 `wg_agree n (v:num->int32) w <=> !i. i < n ==> v i = w i`;;

let WG_AGREE_REFL = prove
 (`!n v. wg_agree n v v`,
  REWRITE_TAC[wg_agree]);;

let WG_AGREE_TRANS = prove
 (`!n u v w. wg_agree n u v /\ wg_agree n v w ==> wg_agree n u w`,
  REWRITE_TAC[wg_agree] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The update functions only look at the state below 16.                     *)
(* ------------------------------------------------------------------------- *)

let BLAKE2S_G_AGREE = prove
 (`!a b c d x y v w.
        a < 16 /\ b < 16 /\ c < 16 /\ d < 16 /\ wg_agree 16 v w
        ==> wg_agree 16 (blake2s_g a b c d x y v) (blake2s_g a b c d x y w)`,
  REWRITE_TAC[wg_agree; blake2s_g] THEN REPEAT STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC[]);;

let CHACHA20_QROUND_AGREE = prove
 (`!a b c d v w.
        a < 16 /\ b < 16 /\ c < 16 /\ d < 16 /\ wg_agree 16 v w
        ==> wg_agree 16 (chacha20_qround a b c d v) (chacha20_qround a b c d w)`,
  REWRITE_TAC[wg_agree; chacha20_qround] THEN REPEAT STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC[]);;

let BLAKE2S_SIGMA_BOUND = prove
 (`!r j. j < 16 ==> EL j (EL (r MOD 10) blake2s_sigma) < 16`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r MOD 10 < 10` MP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`r MOD 10`,`k:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`j:num`,`j:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[blake2s_sigma] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BLAKE2S_ROUND_AGREE = prove
 (`!r m m' v w.
        wg_agree 16 m m' /\ wg_agree 16 v w
        ==> wg_agree 16 (blake2s_round r m v) (blake2s_round r m' w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[blake2s_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `!j. j < 16 ==> (m:num->int32)(EL j (EL (r MOD 10) blake2s_sigma)) =
                   (m':num->int32)(EL j (EL (r MOD 10) blake2s_sigma))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[wg_agree]) THEN
    ASM_SIMP_TAC[BLAKE2S_SIGMA_BOUND];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC BLAKE2S_G_AGREE THEN CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;

let BLAKE2S_ROUNDS_AGREE = prove
 (`!n m m' v w.
        wg_agree 16 m m' /\ wg_agree 16 v w
        ==> wg_agree 16 (blake2s_rounds n m v) (blake2s_rounds n m' w)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[blake2s_rounds; BLAKE2S_ROUND_AGREE]);;

let CHACHA20_DOUBLE_ROUND_AGREE = prove
 (`!v w. wg_agree 16 v w
         ==> wg_agree 16 (chacha20_double_round v) (chacha20_double_round w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chacha20_double_round] THEN
  REPEAT(MATCH_MP_TAC CHACHA20_QROUND_AGREE THEN CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;

let CHACHA20_ROUNDS_AGREE = prove
 (`!n v w. wg_agree 16 v w
           ==> wg_agree 16 (chacha20_rounds n v) (chacha20_rounds n w)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[chacha20_rounds; CHACHA20_DOUBLE_ROUND_AGREE]);;

let BLAKE2S_WORKVEC_AGREE = prove
 (`!h h' t f. wg_agree 8 h h'
              ==> wg_agree 16 (blake2s_workvec h t f) (blake2s_workvec h' t f)`,
  SIMP_TAC[wg_agree; blake2s_workvec]);;

let BLAKE2S_COMPRESS_AGREE = prove
 (`!h h' m m' t f.
        wg_agree 8 h h' /\ wg_agree 16 m m'
        ==> wg_agree 8 (blake2s_compress h m t f) (blake2s_compress h' m' t f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[blake2s_compress] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`10`; `m:num->int32`; `m':num->int32`;
                `blake2s_workvec h t f`; `blake2s_workvec h' t f`]
               BLAKE2S_ROUNDS_AGREE) THEN
  ASM_SIMP_TAC[BLAKE2S_WORKVEC_AGREE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wg_agree]) THEN
  SIMP_TAC[wg_agree] THEN REPEAT STRIP_TAC THEN
  BINOP_TAC THEN ASM_SIMP_TAC[] THEN BINOP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let BLAKE2S_BYTES_AGREE = prove
 (`!h h'. wg_agree 8 h h' ==> blake2s_bytes h = blake2s_bytes h'`,
  REWRITE_TAC[wg_agree; blake2s_bytes] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  ASM_SIMP_TAC[IN_NUMSEG; ARITH_RULE `i <= 7 ==> i < 8`]);;

(* ------------------------------------------------------------------------- *)
(* Explicit tables, and turning 16 (or 8) equations into wg_agree.           *)
(* ------------------------------------------------------------------------- *)

let wg_table cs = mk_abs(`i:num`,
  mk_comb(mk_comb(`EL:num->int32 list->int32`,`i:num`),mk_list(cs,`:int32`)));;

let WG_AGREE_EXPAND =
  let expand n =
    let th = REWRITE_CONV[wg_agree]
      (list_mk_comb(`wg_agree`,[mk_small_numeral n; `v:num->int32`;
                                `w:num->int32`])) in
    CONV_RULE(RAND_CONV EXPAND_CASES_CONV) th in
  let ths = [8,expand 8; 16,expand 16] in
  fun n -> assoc n ths;;

(* Given a function term v and the theorems |- v k = c_k for k < n, the      *)
(* theorem |- wg_agree n v (\i. EL i [c_0; ...]).                            *)

let WG_AGREE_RULE n v ths =
  let cs = map (rand o concl) ths in
  let w = wg_table cs in
  let eths = map2 (fun k th ->
    let el = (BETA_CONV THENC EL_CONV) (mk_comb(w,mk_small_numeral k)) in
    TRANS th (SYM el)) (0--(n-1)) ths in
  let th = INST [v,`v:num->int32`; w,`w:num->int32`] (WG_AGREE_EXPAND n) in
  EQ_MP (SYM th) (end_itlist CONJ eths);;

(* The table of values of v at 0 .. n-1 computed by conv.                    *)

let WG_EVAL_TABLE conv n v =
  WG_AGREE_RULE n v (map (fun k ->
    (conv THENC WORD_REDUCE_CONV) (mk_comb(v,mk_small_numeral k))) (0--(n-1)));;

(* The values of a function at k < n from |- wg_agree n v tab.               *)

let WG_AGREE_AT th k =
  let th1 = MP (SPEC (mk_small_numeral k) (REWRITE_RULE[wg_agree] th))
               (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool`
                  (mk_small_numeral k) (rand(rator(rator(concl th))))))) in
  CONV_RULE(RAND_CONV(TRY_CONV BETA_CONV THENC EL_CONV)) th1;;

(* Evaluation of explicit word expressions with table lookups.               *)

let WG_REDUCE_CONV =
  TOP_DEPTH_CONV let_CONV THENC TOP_DEPTH_CONV BETA_CONV THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC TOP_DEPTH_CONV EL_CONV THENC
  WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* One step of a 4-word update (G or the quarter round) on a table: from     *)
(* |- wg_agree 16 inner tab and tm = f args inner, |- wg_agree 16 tm tab'.   *)
(* ------------------------------------------------------------------------- *)

let WG_UPDATE_STEP agreelemma defn agreeth tm =
  let f_args,inner = dest_comb tm in
  let tab = rand(concl agreeth) in
  let args = snd(strip_comb f_args) in
  let idx = filter (fun t -> type_of t = `:num`) args in
  let bnds = map (fun x -> EQT_ELIM(NUM_REDUCE_CONV
                    (mk_binop `(<):num->num->bool` x `16`))) idx in
  let th1 = MATCH_MP (SPECL (args @ [inner;tab]) agreelemma)
                     (end_itlist CONJ (bnds @ [agreeth])) in
  let gtab = rand(concl th1) in
  let th2 = WG_EVAL_TABLE (RATOR_CONV(REWR_CONV defn) THENC WG_REDUCE_CONV)
                          16 gtab in
  MATCH_MP WG_AGREE_TRANS (CONJ th1 th2);;

let BLAKE2S_G_STEP = WG_UPDATE_STEP BLAKE2S_G_AGREE blake2s_g;;

let CHACHA20_QROUND_STEP = WG_UPDATE_STEP CHACHA20_QROUND_AGREE chacha20_qround;;

(* A nest f(f(...(f base))) of updates, with base an explicit table.         *)

let rec WG_NEST_EVAL step name tm =
  match tm with
    Comb(f_args,inner) when
      (try fst(dest_const(fst(strip_comb f_args))) = name
       with Failure _ -> false) ->
      step (WG_NEST_EVAL step name inner) tm
  | _ -> ISPECL [`16`; tm] WG_AGREE_REFL;;

(* ------------------------------------------------------------------------- *)
(* BLAKE2s: rounds, compression and the hash.                                *)
(* ------------------------------------------------------------------------- *)

(* Instantiate variables whether MATCH_MP has left them free or bound.       *)

let WG_SPEC ilist th =
  let th' = SPEC_ALL th in
  INST (map (fun (t,v) ->
    t,(try find (fun v' -> name_of v' = name_of v) (frees(concl th'))
       with Failure _ -> v)) ilist) th';;

let CHACHA20_WORDS_AGREE = prove
 (`!n v w. wg_agree n v w ==> chacha20_words n v = chacha20_words n w`,
  REWRITE_TAC[wg_agree; chacha20_words] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; bytelist_of_num] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let CHACHA20_ADD_AGREE = prove
 (`!x x' y y'. wg_agree 16 x x' /\ wg_agree 16 y y'
               ==> wg_agree 16 (\i. word_add (y i) (x i))
                               (\i. word_add (y' i) (x' i))`,
  SIMP_TAC[wg_agree]);;

(* ------------------------------------------------------------------------- *)
(* Symbolic evaluation of BLAKE2s rounds on tables of terms, the new entries *)
(* of each G being identified with other terms by ident stops e (|- e = e'), *)
(* where stops are the entries of the table that G is applied to.            *)
(* ------------------------------------------------------------------------- *)

(* As WG_REDUCE_CONV but without evaluating word operations on numerals, so  *)
(* that the entries keep the forms they have in the simulation.              *)

let WG_SYM_REDUCE_CONV =
  TOP_DEPTH_CONV let_CONV THENC TOP_DEPTH_CONV BETA_CONV THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC TOP_DEPTH_CONV EL_CONV;;

let WG_SYM_G_STEP ident agreeth tm =
  let f_args,inner = dest_comb tm in
  let tab = rand(concl agreeth) in
  let args = snd(strip_comb f_args) in
  let idxs = filter (fun t -> type_of t = `:num`) args in
  let bnds = map (fun x -> EQT_ELIM(NUM_REDUCE_CONV
                    (mk_binop `(<):num->num->bool` x `16`))) idxs in
  let th1 = MATCH_MP (SPECL (args @ [inner;tab]) BLAKE2S_G_AGREE)
                     (end_itlist CONJ (bnds @ [agreeth])) in
  let gtab = rand(concl th1) in
  let entries = dest_list(rand(body(rand(concl agreeth)))) in
  let stops = filter is_var entries in
  let ks = map dest_small_numeral idxs in
  let ths = map (fun k ->
      let th = (RATOR_CONV(REWR_CONV blake2s_g) THENC WG_SYM_REDUCE_CONV)
                 (mk_comb(gtab,mk_small_numeral k)) in
      if mem k ks then TRANS th (ident stops (rand(concl th))) else th)
    (0--15) in
  let th2 = WG_AGREE_RULE 16 gtab ths in
  MATCH_MP WG_AGREE_TRANS (CONJ th1 th2);;

(* |- wg_agree 16 (blake2s_round r m vtab) tab' with m a message function.   *)

let WG_SYM_ROUND_RULE ident r m vtab =
  let tm = list_mk_comb(`blake2s_round`,[r;m;vtab]) in
  let th1 = (REWR_CONV blake2s_round THENC TOP_DEPTH_CONV let_CONV THENC
             TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV THENC
             PURE_REWRITE_CONV[blake2s_sigma] THENC
             TOP_DEPTH_CONV EL_CONV) tm in
  let th2 = WG_NEST_EVAL (WG_SYM_G_STEP ident) "blake2s_g" (rand(concl th1)) in
  CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM th1)))) th2;;

(* |- wg_agree 16 (blake2s_rounds n m v) tab from |- wg_agree 16 v vtab.     *)

let WG_SYM_ROUNDS_RULE ident n m vth =
  let mth = ISPECL [`16`; m] WG_AGREE_REFL in
  let v = rand(rator(concl vth)) in
  let r0,rs = CONJ_PAIR blake2s_rounds in
  let th0 = CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM(REWR_CONV r0
              (list_mk_comb(`blake2s_rounds`,[`0`;m;v]))))))) vth in
  let rec iter k th =
    if k = n then th else
    let kk = mk_small_numeral k in
    let th1 = WG_SPEC [kk,`r:num`]
                (MATCH_MP BLAKE2S_ROUND_AGREE (CONJ mth th)) in
    let th2 = WG_SYM_ROUND_RULE ident kk m (rand(concl th)) in
    let th3 = MATCH_MP WG_AGREE_TRANS (CONJ th1 th2) in
    let eq = CONV_RULE(LAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV
               NUM_SUC_CONV))))
              (REWR_CONV rs (list_mk_comb(`blake2s_rounds`,
                 [mk_comb(`SUC`,kk);m;v]))) in
    iter (k + 1) (CONV_RULE(RATOR_CONV(RAND_CONV(K(SYM eq)))) th3) in
  iter 0 th0;;

(* ------------------------------------------------------------------------- *)
(* The 64-bit BLAKE2s counter as one word tt (t[0] and t[1] of the kernel's  *)
(* state), as compiled code updates it: the 32-bit increment is added to the *)
(* low half and the carry to the high half.                                  *)
(* ------------------------------------------------------------------------- *)

let WG_COUNTER_ADD_LO = prove
 (`!(tt:int64) (i:int32).
     word_subword (word_add tt (word_zx i)) (0,32):int32 =
     word_add (word_subword tt (0,32)) i`,
  BITBLAST_TAC);;

let WG_WORD_VAL_HALVES = prove
 (`(!x:int64. word(val x):int32 = word_subword x (0,32)) /\
   (!x:int64. word(val x DIV 2 EXP 32):int32 = word_subword x (32,32))`,
  CONJ_TAC THEN GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  ARITH_TAC);;

let WG_CARRY_ULT = prove
 (`!a i:int32. val a + val i = val(word_add a i) <=> ~(word_ult (word_add a i) a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ULT; VAL_WORD_ADD; DIMINDEX_32] THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN MP_TAC(ISPEC `i:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `val(a:int32) + val(i:int32) < 2 EXP 32` THEN
  ASM_SIMP_TAC[MOD_LT] THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(val(a:int32) + val(i:int32)) MOD 2 EXP 32 = (val a + val i) - 2 EXP 32`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let WG_COUNTER_ADD_HI = prove
 (`!(tt:int64) (i:int32).
     word_subword (word_add tt (word_zx i)) (32,32):int32 =
     if val(word_subword tt (0,32):int32) + val i =
        val(word_add (word_subword tt (0,32)) i)
     then word_subword tt (32,32) else word_add (word_subword tt (32,32)) (word 1)`,
  REWRITE_TAC[WG_CARRY_ULT] THEN BITBLAST_TAC);;

(* The initial work vector of a compression with counter ctr + x, as a table *)
(* in the forms of compiled code: the counter as the halves of ctr with the  *)
(* carry, and the final flag as the word (all ones or zero) that it xors.    *)

let BLAKE2S_WORKVEC_COUNTER = prove
 (`!(hh:num->int32) (ctr:int64) (x:int32) f.
     wg_agree 16 (blake2s_workvec hh (val(word_add ctr (word_zx x))) f)
       (\i. EL i
         [hh 0; hh 1; hh 2; hh 3; hh 4; hh 5; hh 6; hh 7;
          word 0x6A09E667; word 0xBB67AE85; word 0x3C6EF372; word 0xA54FF53A;
          word_xor (word 0x510E527F) (word_add (word_subword ctr (0,32)) x);
          word_xor (word 0x9B05688C)
           (if val(word_subword ctr (0,32):int32) + val x =
               val(word_add (word_subword ctr (0,32)) x)
            then word_subword ctr (32,32)
            else word_add (word_subword ctr (32,32)) (word 1));
          word_xor (word 0x1F83D9AB) (if f then word_not(word 0) else word 0);
          word 0x5BE0CD19])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wg_agree] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[blake2s_workvec; blake2s_iv; WG_WORD_VAL_HALVES;
              WG_COUNTER_ADD_LO; WG_COUNTER_ADD_HI] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  BOOL_CASES_TAC `f:bool` THEN CONV_TAC WORD_REDUCE_CONV);;

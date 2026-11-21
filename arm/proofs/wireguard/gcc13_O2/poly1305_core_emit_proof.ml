(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of poly1305_core_emit_spec.ml. The arithmetic is     *)
(* POLY1305_DONNA_EMIT of ../poly1305.ml: two rounds of carries give the     *)
(* limbs of a value H' < 2p congruent to h; the top limb y of H' + 5 decides *)
(* whether H' - p or H' is selected; the nonce is added and the result       *)
(* packed in 128 bits. For the code, the intermediate words are abbreviated  *)
(* (as the C computes them, with gcc's variants) and their values derived in *)
(* turn; the masks of the selection are constants once it is known whether  *)
(* y >= 2^42.                                                                *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_emit_spec.ml";;
needs "arm/proofs/wireguard/poly1305.ml";;

let WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "poly1305_core_emit"];;

(* ------------------------------------------------------------------------- *)
(* Word-level facts for the code: the bit of the top limb as 0 or 5 (sbfx), *)
(* the high mask as an addition, the packing of the 128-bit result, the      *)
(* 16 bytes as two words, and the masks of the selection.                    *)
(* ------------------------------------------------------------------------- *)

let EM_SX_WORD = prove
 (`!x:int64. word_and (word_sxfrom 0 (word_subword x (42,1):int64)) (word 5) =
             if bit 42 x then word 5 else word 0`,
  BITBLAST_TAC);;
let EM_SX_LEMMA = prove
 (`!x:int64. val x < 2 EXP 43
     ==> val(word_and (word_sxfrom 0 (word_subword x (42,1):int64))
                      (word 5)) = 5 * val x DIV 2 EXP 42`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EM_SX_WORD; BIT_VAL] THEN
  SUBGOAL_THEN `val(x:int64) DIV 2 EXP 42 < 2` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 EXP 1 ==> x < 2`) THEN POLY1305_DIVB_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`val(x:int64) DIV 2 EXP 42`,`q:num`) THEN
  REWRITE_TAC[ARITH_RULE `q < 2 <=> q = 0 \/ q = 1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;
let EM_OR_WORD = prove
 (`!x:int64. word_or x (word 18446739675663040512) =
             word_add (word_and x (word 4398046511103))
                      (word 18446739675663040512)`,
  BITBLAST_TAC);;
let EM_PACK_WORDS = prove
 (`!n0 n1 n2:int64.
     word_or (word_and n0 (word 17592186044415))
             (word_shl (word_and n1 (word 17592186044415)) 44) =
     word_add (word_and n0 (word 17592186044415))
              (word_shl (word_and n1 (word 17592186044415)) 44) /\
     word_or (word_shl (word_and n2 (word 4398046511103)) 24)
             (word_ushr (word_and n1 (word 17592186044415)) 20) =
     word_add (word_shl (word_and n2 (word 4398046511103)) 24)
              (word_ushr (word_and n1 (word 17592186044415)) 20)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN BITBLAST_TAC);;

let EM_PACK_LEMMA = prove
 (`!n0 n1 n2:int64.
     val(word_or (word_and n0 (word 17592186044415))
                 (word_shl (word_and n1 (word 17592186044415)) 44)) +
     2 EXP 64 *
     val(word_or (word_shl (word_and n2 (word 4398046511103)) 24)
                 (word_ushr (word_and n1 (word 17592186044415)) 20)) =
     (val n0 MOD 2 EXP 44 + 2 EXP 44 * val n1 MOD 2 EXP 44 +
      2 EXP 88 * val n2 MOD 2 EXP 42) MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EM_PACK_WORDS] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD_USHR; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `17592186044415 = 2 EXP 44 - 1`;
              ARITH_RULE `4398046511103 = 2 EXP 42 - 1`;
              VAL_WORD_AND_MASK_WORD] THEN
  MAP_EVERY ABBREV_TAC
   [`A = val(n0:int64) MOD 2 EXP 44`; `B = val(n1:int64) MOD 2 EXP 44`;
    `C = val(n2:int64) MOD 2 EXP 42`] THEN
  SUBGOAL_THEN `A < 2 EXP 44 /\ B < 2 EXP 44 /\ C < 2 EXP 42`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"; "C"] THEN REWRITE_TAC[MOD_LT_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 44 * 2 EXP 20`; MOD_MULT2] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 44 * 2 EXP 20 = 2 EXP 24 * 2 EXP 40`;
              MOD_MULT2] THEN
  SUBGOAL_THEN `B MOD 2 EXP 20 < 2 EXP 20 /\ C MOD 2 EXP 40 < 2 EXP 40 /\
                B DIV 2 EXP 20 < 2 EXP 24`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN POLY1305_DIVB_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(A + 2 EXP 44 * B MOD 2 EXP 20) MOD (2 EXP 24 * 2 EXP 40) =
    A + 2 EXP 44 * B MOD 2 EXP 20 /\
    (2 EXP 24 * C MOD 2 EXP 40 + B DIV 2 EXP 20) MOD (2 EXP 24 * 2 EXP 40) =
    2 EXP 24 * C MOD 2 EXP 40 + B DIV 2 EXP 20`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MAP_EVERY UNDISCH_TAC
     [`A < 2 EXP 44`; `B MOD 2 EXP 20 < 2 EXP 20`;
      `C MOD 2 EXP 40 < 2 EXP 40`; `B DIV 2 EXP 20 < 2 EXP 24`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `C DIV 2 EXP 40` THEN
  MP_TAC(SPECL [`B:num`; `2 EXP 20`] DIVISION) THEN
  MP_TAC(SPECL [`C:num`; `2 EXP 40`] DIVISION) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  MAP_EVERY UNDISCH_TAC
   [`A < 2 EXP 44`; `B MOD 2 EXP 20 < 2 EXP 20`;
    `C MOD 2 EXP 40 < 2 EXP 40`; `B DIV 2 EXP 20 < 2 EXP 24`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let EM_BYTES16 = prove
 (`!a:int64 s:armstate.
     read (memory :> bytes(a,16)) s =
     val(read (memory :> bytes64 a) s) +
     2 EXP 64 * val(read (memory :> bytes64 (word_add a (word 8))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `16 = 8 + 8`) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; WG_READ_BYTES_8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let EM_ISHR = prove
 (`!x:int64. word_ishr x 63 =
             if bit 63 x then word 18446744073709551615 else word 0`,
  BITBLAST_TAC);;
let EM_AND_ONES = prove
 (`!x:int64. word_and x (word 18446744073709551615) = x`, BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The intermediate words of the code, as abbreviations in the goal (each    *)
(* term must occur), in the order of the computation.                        *)
(* ------------------------------------------------------------------------- *)

let EM_ABBREV_TAC (v,t) (asl,w as gl) =
  if can (find_term ((=) t)) w then ABBREV_TAC (mk_eq(v,t)) gl
  else failwith ("EM_ABBREV_TAC: " ^ fst(dest_var v));;

let em_abbrevs =
 [`w_x0a:int64`, `word_add (h2w:int64) (word_ushr (h1w:int64) 44)`;
  `w_c1:int64`, `word_ushr (w_x0a:int64) 42`;
  `w_x0c:int64`,
  `word_add (word_add (w_c1:int64) (word_shl w_c1 2)) (h0w:int64)`;
  `w_x0d:int64`,
  `word_add (word_and (h1w:int64) (word 17592186044415))
            (word_ushr (w_x0c:int64) 44)`;
  `w_x0e:int64`,
  `word_add (word_and (w_x0a:int64) (word 4398046511103))
            (word_ushr (w_x0d:int64) 44)`;
  `w_x0h:int64`,
  `word_add (word_and (word_sxfrom 0 (word_subword (w_x0e:int64) (42,1):int64))
                      (word 5))
            (word_and (w_x0c:int64) (word 17592186044415))`;
  `w_h0f:int64`, `word_and (w_x0h:int64) (word 17592186044415)`;
  `w_g0:int64`, `word_add (w_h0f:int64) (word 5)`;
  `w_h1f:int64`,
  `word_add (word_and (w_x0d:int64) (word 17592186044415))
            (word_ushr (w_x0h:int64) 44)`;
  `w_g1:int64`, `word_add (w_h1f:int64) (word_ushr (w_g0:int64) 44)`;
  `w_g2:int64`,
  `word_add (word_or (w_x0e:int64) (word 18446739675663040512))
            (word_ushr (w_g1:int64) 44)`;
  `w_m:int64`, `word_sub (word_ushr (w_g2:int64) 63) (word 1)`;
  `w_mn:int64`, `word_ishr (w_g2:int64) 63`;
  `w_s0:int64`,
  `word_or (word_and (word_and (w_g0:int64) (w_m:int64))
                     (word 17592186044415))
           (word_and (w_h0f:int64) (w_mn:int64))`;
  `w_s1:int64`,
  `word_or (word_and (word_and (w_g1:int64) (w_m:int64))
                     (word 17592186044415))
           (word_and (w_h1f:int64) (w_mn:int64))`;
  `w_s2:int64`,
  `word_or (word_and (w_g2:int64) (w_m:int64))
           (word_and (word_and (w_x0e:int64) (word 4398046511103))
                     (w_mn:int64))`;
  `w_n0:int64`,
  `word_add (word_and (t0w:int64) (word 17592186044415)) (w_s0:int64)`;
  `w_n1:int64`,
  `word_add (word_add (word_and (word_subword (word_join (t1w:int64)
                                   (t0w:int64):int128) (44,64))
                                (word 17592186044415)) (w_s1:int64))
            (word_ushr (w_n0:int64) 44)`;
  `w_n2:int64`,
  `word_add (word_add (w_s2:int64) (word_ushr (t1w:int64) 24))
            (word_ushr (w_n1:int64) 44)`];;

(* The same quantities as numbers (POLY1305_DONNA_EMIT), the selected limbs *)
(* being q0, q1, q2.                                                         *)

let em_ndefs_tm =
 [`x0a = val(h2w:int64) + val(h1w:int64) DIV 2 EXP 44`;
  `c1 = x0a DIV 2 EXP 42`;
  `x0c = 5 * c1 + val(h0w:int64)`;
  `x0d = val(h1w:int64) MOD 2 EXP 44 + x0c DIV 2 EXP 44`;
  `x0e = x0a MOD 2 EXP 42 + x0d DIV 2 EXP 44`;
  `x0h = 5 * x0e DIV 2 EXP 42 + x0c MOD 2 EXP 44`;
  `h0f = x0h MOD 2 EXP 44`;
  `h1f = x0d MOD 2 EXP 44 + x0h DIV 2 EXP 44`;
  `h2f = x0e MOD 2 EXP 42`;
  `g0 = h0f + 5`; `g1 = h1f + g0 DIV 2 EXP 44`; `y = h2f + g1 DIV 2 EXP 44`;
  `q0 = if 2 EXP 42 <= y then g0 MOD 2 EXP 44 else h0f`;
  `q1 = if 2 EXP 42 <= y then g1 MOD 2 EXP 44 else h1f`;
  `q2 = if 2 EXP 42 <= y then y - 2 EXP 42 else h2f`;
  `n0 = val(t0w:int64) MOD 2 EXP 44 + q0`;
  `n1 = ((val(t0w:int64) DIV 2 EXP 44 +
          2 EXP 20 * val(t1w:int64) MOD 2 EXP 24) + q1) + n0 DIV 2 EXP 44`;
  `n2 = (q2 + val(t1w:int64) DIV 2 EXP 24) + n1 DIV 2 EXP 44`];;

let EM_MATH_TAC =
  MAP_EVERY ABBREV_TAC em_ndefs_tm THEN
  MP_TAC(SPECL
   [`val(h0w:int64)`; `val(h1w:int64)`; `val(h2w:int64)`;
    `val(t0w:int64)`; `val(t1w:int64)`;
    `x0a:num`; `c1:num`; `x0c:num`; `x0d:num`; `x0e:num`; `x0h:num`;
    `h0f:num`; `h1f:num`; `h2f:num`; `g0:num`; `g1:num`; `y:num`;
    `q0:num`; `q1:num`; `q2:num`; `n0:num`; `n1:num`; `n2:num`]
   POLY1305_DONNA_EMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND] THEN
    REPEAT CONJ_TAC THEN
    TRY(CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY EXPAND_TAC ["q0"; "q1"; "q2"] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `h0f < 2 EXP 44 /\ g0 < 2 EXP 45 /\ h2f < 2 EXP 42`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g0"; "h0f"; "h2f"] THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    MP_TAC(SPECL [`x0h:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(t0w:int64) DIV 2 EXP 44 < 2 EXP 20 /\
    val(t1w:int64) MOD 2 EXP 24 < 2 EXP 24 /\
    val(t1w:int64) DIV 2 EXP 24 < 2 EXP 40 /\
    val(t0w:int64) MOD 2 EXP 44 < 2 EXP 44`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC POLY1305_DIV_BOUND THEN
    CONV_TAC(RAND_CONV(RAND_CONV NUM_ADD_CONV)) THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The values of the words one at a time: val w = n from the definitions,   *)
(* the values of the earlier words and the bounds. A sum below 2^64 drops    *)
(* its MOD (EM_MODLT_TAC, with only the bounds about its variables).         *)
(* ------------------------------------------------------------------------- *)

let em_find asl p = snd(find (fun (_,th) -> p(concl th)) asl);;

let em_wdef asl v = em_find asl (fun c -> is_eq c && rand c = v);;

let em_ndefs asl =
  mapfilter (fun (_,th) -> let c = concl th in
    if is_eq c && is_var(rand c) && type_of(rand c) = `:num` &&
       not(is_cond(lhand c)) then th else failwith "") asl;;

let em_isval t = is_comb t && rator t = `val:int64->num`;;

let em_vfacts asl =
  mapfilter (fun (_,th) -> let c = concl th in
    if is_eq c && em_isval(lhand c) then th else failwith "") asl;;

let em_ndef asl n =
  em_find asl (fun c -> is_eq c && rand c = n && not(em_isval(lhand c)));;

let em_bounds asl =
  mapfilter (fun (_,th) -> let c = concl th in
    if (is_binop `(<):num->num->bool` c || is_binop `(<=):num->num->bool` c) &&
       not(can (find_term (fun t ->
             try fst(dest_const t) = "read" with Failure _ -> false)) c)
    then th else failwith "") asl;;

let EM_MODLT_TAC (bounds:thm list) : tactic = fun (asl,w as gl) ->
  let is_mod64 t = match t with
     Comb(Comb(Const("MOD",_),x),n) ->
       n = `2 EXP 64` || n = `18446744073709551616`
   | _ -> false in
  let ts = setify(find_terms is_mod64 w) in
  let sz t = String.length (string_of_term t) in
  let ts = map snd (sort (fun (a,_) (b,_) -> a < b)
                         (map (fun t -> sz t,t) ts)) in
  let try_one t = let x = lhand t and n = rand t in
     let vs = frees x in
     let rel = filter (fun th -> exists (fun v -> mem v vs) (frees(concl th)))
                      bounds in
     let lt = TAC_PROOF(([], mk_binop `(<):num->num->bool` x n),
       MAP_EVERY MP_TAC rel THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) in
     MP (SPECL [x;n] MOD_LT) lt in
  let ths = mapfilter try_one ts in
  if ths = [] then failwith "EM_MODLT_TAC" else REWRITE_TAC ths gl;;

let EM_MASKS = [ARITH_RULE `17592186044415 = 2 EXP 44 - 1`;
                ARITH_RULE `4398046511103 = 2 EXP 42 - 1`];;

let EM_M1V = REWRITE_RULE[ARITH_RULE `17592186044415 = 2 EXP 44 - 1`;
                          VAL_WORD_AND_MASK_WORD] POLY1305_M1;;

let EM_VAL_TAC (v,n) (asl,w as gl) =
  let wd = em_wdef asl v and nd = em_ndef asl n
  and ndefs = em_ndefs asl and bnds = em_bounds asl in
  let th = TAC_PROOF((asl,mk_eq(mk_comb(`val:int64->num`,v),n)),
    REWRITE_TAC[SYM wd] THEN REWRITE_TAC EM_MASKS THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_SHL;
                VAL_WORD_AND_MASK_WORD; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC(EM_M1V :: em_vfacts asl) THEN REWRITE_TAC ndefs THEN
    REPEAT(EM_MODLT_TAC bnds THEN REWRITE_TAC ndefs) THEN
    TRY(FIRST [MATCH_ACCEPT_TAC nd; MATCH_ACCEPT_TAC (SYM nd)]) THEN
    MP_TAC nd THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC) in
  ASSUME_TAC th gl;;

let EM_SX_TAC (asl,w as gl) =
  let v5 = em_find asl (fun c -> c = `val(w_x0e:int64) = x0e`) in
  ASSUME_TAC(MP (SPEC `w_x0e:int64` EM_SX_LEMMA)
    (TAC_PROOF((asl,`val(w_x0e:int64) < 2 EXP 43`),
       REWRITE_TAC[v5] THEN MP_TAC(ASSUME `x0e <= 2 EXP 42`) THEN
       ARITH_TAC))) gl;;

let EM_G2_TAC (asl,w as gl) =
  let wd = em_wdef asl `w_g2:int64` and nd = em_ndef asl `y:num`
  and ndefs = em_ndefs asl and bnds = em_bounds asl in
  ASSUME_TAC(TAC_PROOF((asl,
             `val(w_g2:int64) = (y + 18446739675663040512) MOD 2 EXP 64`),
    REWRITE_TAC[SYM wd; EM_OR_WORD] THEN REWRITE_TAC EM_MASKS THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD;
                DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC(em_vfacts asl) THEN REWRITE_TAC ndefs THEN
    TRY(EM_MODLT_TAC bnds) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC nd THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC)) gl;;

(* The selection, in each case of 2^42 <= y: the masks as constants, and    *)
(* the values q0, q1, q2 of the selected limbs.                              *)

let EM_SEL_TAC (asl,w as gl) =
  let caseA = exists (fun (_,th) -> concl th = `2 EXP 42 <= y`) asl in
  let cth = ASSUME(if caseA then `2 EXP 42 <= y` else `~(2 EXP 42 <= y)`) in
  let yb = ASSUME `y < 2 EXP 43` in
  let v11 = em_find asl (fun c -> is_eq c && lhand c = `val(w_g2:int64)`) in
  let g2v =
    if caseA then
      TAC_PROOF((asl,`val(w_g2:int64) = y - 2 EXP 42`),
        REWRITE_TAC[v11] THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
        MAP_EVERY MP_TAC [cth; yb] THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC)
    else
      TAC_PROOF((asl,`val(w_g2:int64) = y + 18446739675663040512`),
        REWRITE_TAC[v11] THEN MATCH_MP_TAC MOD_LT THEN MP_TAC cth THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
        ARITH_TAC) in
  let q = if caseA then `0` else `1` in
  let hiv = TAC_PROOF((asl,mk_eq(`val(w_g2:int64) DIV 2 EXP 63`,q)),
     REWRITE_TAC[g2v] THEN
     (if caseA then MATCH_MP_TAC DIV_LT
      else MATCH_MP_TAC DIV_UNIQ THEN
           EXISTS_TAC `y + 18446739675663040512 - 2 EXP 63`) THEN
     MAP_EVERY MP_TAC [cth; yb] THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) in
  let ushr = TAC_PROOF((asl,mk_eq(`word_ushr (w_g2:int64) 63`,
                                  mk_comb(`word:num->int64`,q))),
     ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_USHR; hiv] THEN
     CONV_TAC WORD_REDUCE_CONV) in
  let ones = `word 18446744073709551615:int64` and zero = `word 0:int64` in
  let mth = TAC_PROOF((asl,mk_eq(`w_m:int64`,if caseA then ones else zero)),
     REWRITE_TAC[SYM(em_wdef asl `w_m:int64`); ushr] THEN
     CONV_TAC WORD_REDUCE_CONV) in
  let mnth = TAC_PROOF((asl,mk_eq(`w_mn:int64`,if caseA then zero else ones)),
     REWRITE_TAC[SYM(em_wdef asl `w_mn:int64`); EM_ISHR; BIT_VAL; hiv] THEN
     CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]) in
  let sel v n = TAC_PROOF((asl,mk_eq(mk_comb(`val:int64->num`,v),n)),
     REWRITE_TAC[SYM(em_wdef asl v); mth; mnth] THEN
     REWRITE_TAC[EM_AND_ONES; WORD_AND_0; WORD_OR_0] THEN
     REWRITE_TAC EM_MASKS THEN REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
     REWRITE_TAC(g2v :: filter (fun th ->
       lhand(concl th) <> `val(w_g2:int64)`) (em_vfacts asl)) THEN
     REWRITE_TAC[SYM(em_ndef asl n)] THEN REWRITE_TAC[cth] THEN
     REWRITE_TAC(em_ndefs asl)) in
  MAP_EVERY ASSUME_TAC
   [sel `w_s0:int64` `q0:num`; sel `w_s1:int64` `q1:num`;
    sel `w_s2:int64` `q2:num`] gl;;

(* The nonce as its two words, and the final equality.                       *)

let EM_SB_TAC =
  SUBGOAL_THEN
   `num_of_bytelist sb = val(t0w:int64) + 2 EXP 64 * val(t1w:int64)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [GSYM(REWRITE_RULE[ASSUME `LENGTH(sb:byte list) = 16`]
             (ISPEC `sb:byte list` SUB_LIST_LENGTH))] THEN
    REWRITE_TAC[WG_SUB_LIST_16; WG_NUM_OF_BYTELIST_APPEND] THEN
    SUBGOAL_THEN `LENGTH(SUB_LIST(0,8) (sb:byte list)) = 8 /\
                  LENGTH(SUB_LIST(0 + 8,8) (sb:byte list)) = 8`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[SYM(ASSUME
      `word(num_of_bytelist(SUB_LIST(0,8) sb)):int64 = t0w`);
                SYM(ASSUME
      `word(num_of_bytelist(SUB_LIST(8,8) sb)):int64 = t1w`)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    ASM_SIMP_TAC[WG_VAL_WORD_BYTES8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let EM_FINAL_TAC =
  REWRITE_TAC[ASSUME `val(w_n0:int64) = n0`; ASSUME `val(w_n1:int64) = n1`;
              ASSUME `val(w_n2:int64) = n2`] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) =
    `(n0 MOD 2 EXP 44 + 2 EXP 44 * n1 MOD 2 EXP 44 + 2 EXP 88 * n2 MOD 2 EXP 42)
     MOD 2 EXP 128` then REWRITE_TAC[th] else failwith "EM_FINAL_TAC") THEN
  REWRITE_TAC[ASSUME
   `(val(h0w:int64) + 2 EXP 44 * val(h1w:int64) + 2 EXP 88 * val(h2w:int64))
    MOD (2 EXP 130 - 5) = a`] THEN
  EM_SB_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_ASSOC];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_POLY1305_CORE_EMIT_GCC13_O2_EXEC in
  MAP_EVERY X_GEN_TAC [`state:int64`; `nonce:int64`; `dst:int64`; `a:num`;
                       `sb:byte list`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES; poly1305_h_at] THEN
  STRIP_TAC THEN
  GHOST_INTRO_TAC `h0w:int64` `read (memory :> bytes64 state)` THEN
  GHOST_INTRO_TAC `h1w:int64`
   `read (memory :> bytes64 (word_add state (word 8)))` THEN
  GHOST_INTRO_TAC `h2w:int64`
   `read (memory :> bytes64 (word_add state (word 16)))` THEN
  ABBREV_TAC `t0w:int64 = word(num_of_bytelist(SUB_LIST(0,8) sb))` THEN
  ABBREV_TAC `t1w:int64 = word(num_of_bytelist(SUB_LIST(8,8) sb))` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`nonce:int64`; `sb:byte list`; `16`; `0`; `s0:armstate`]
         WG_READ_BYTES64_BYTELIST) THEN
  MP_TAC(ISPECL [`nonce:int64`; `sb:byte list`; `16`; `8`; `s0:armstate`]
         WG_READ_BYTES64_BYTELIST) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN
  ARM_STEPS_TAC EXEC (1--38) THEN
  SUBGOAL_THEN `~(val(nonce:int64) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
  WG_PC_REWRITE_TAC[ASSUME `~(val(nonce:int64) = 0)`] THEN
  ARM_STEPS_TAC EXEC (39--55) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[EM_BYTES16] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EM_ABBREV_TAC em_abbrevs THEN
  REWRITE_TAC[EM_PACK_LEMMA] THEN
  EM_MATH_TAC THEN
  MAP_EVERY EM_VAL_TAC
   [`w_x0a:int64`,`x0a:num`; `w_c1:int64`,`c1:num`; `w_x0c:int64`,`x0c:num`;
    `w_x0d:int64`,`x0d:num`; `w_x0e:int64`,`x0e:num`] THEN
  EM_SX_TAC THEN
  MAP_EVERY EM_VAL_TAC
   [`w_x0h:int64`,`x0h:num`; `w_h0f:int64`,`h0f:num`; `w_g0:int64`,`g0:num`;
    `w_h1f:int64`,`h1f:num`; `w_g1:int64`,`g1:num`] THEN
  EM_G2_TAC THEN
  ASM_CASES_TAC `2 EXP 42 <= y` THEN EM_SEL_TAC THEN
  MAP_EVERY EM_VAL_TAC
   [`w_n0:int64`,`n0:num`; `w_n1:int64`,`n1:num`; `w_n2:int64`,`n2:num`] THEN
  EM_FINAL_TAC);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proof of the theorem of poly1305_core_blocks_spec.ml. The arithmetic of   *)
(* one block of poly1305-donna64 is POLY1305_DONNA_BLOCK of ../poly1305.ml:  *)
(* with the limbs a of h plus the block and those of r, the three sums d0,   *)
(* d1, d2 of products (with 20 * r for the wrap-around, as 2^130 = 5 mod p)  *)
(* and the carries between them, the new limbs are bounded again and         *)
(* congruent to (h + m) * r modulo p = 2^130 - 5. For the code, each sum is  *)
(* a 128-bit value in two registers (mul/umulh, adds/adc), for which         *)
(* POLY1305_PAIR_RULE proves 2^64 * hi + lo = d; the carries are extracted   *)
(* with extr.                                                                *)
(* ========================================================================= *)

needs "arm/proofs/wireguard/gcc13_O2/poly1305_core_blocks_spec.ml";;
needs "arm/proofs/wireguard/poly1305.ml";;

let WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_EXEC = ARM_MK_EXEC_RANGES_RULE
  wireguard_gcc13_O2_mc [layout_range "poly1305_core_blocks"];;

(* ------------------------------------------------------------------------- *)
(* 128-bit values in two 64-bit words as the code computes them: products    *)
(* (mul and umulh), sums (adds and adc, with the two orders of the operands, *)
(* or adds and cinc for a 64-bit operand) and shifts (extr).                 *)
(* ------------------------------------------------------------------------- *)

let POLY1305_MUL128N = prove
 (`!p. p < 2 EXP 128
       ==> 2 EXP 64 * val(word(p DIV 2 EXP 64):int64) +
           val(word(0 + p):int64) = p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64; ADD_CLAUSES] THEN
  SUBGOAL_THEN `p DIV 2 EXP 64 < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC POLY1305_DIV_BOUND THEN
    CONV_TAC(RAND_CONV(RAND_CONV NUM_ADD_CONV)) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MOD_LT] THEN
    MP_TAC(SPECL [`p:num`; `2 EXP 64`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC]);;

let POLY1305_ADD128 = prove
 (`!(xh:int64) (xl:int64) (yh:int64) (yl:int64).
     (2 EXP 64 * val xh + val xl) + (2 EXP 64 * val yh + val yl) < 2 EXP 128
     ==> 2 EXP 64 * val(word_add (word_add xh yh)
                         (word(bitval(2 EXP 64 <= val xl + val yl)))) +
         val(word_add xl yl) =
         (2 EXP 64 * val xh + val xl) + (2 EXP 64 * val yh + val yl)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_BITVAL; DIMINDEX_64] THEN
  MP_TAC(ISPEC `xl:int64` VAL_BOUND) THEN
  MP_TAC(ISPEC `yl:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  MAP_EVERY SPEC_TAC [`val(xh:int64)`,`a:num`; `val(yh:int64)`,`b:num`;
                      `val(xl:int64)`,`c:num`; `val(yl:int64)`,`d:num`] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `2 EXP 64 <= c + d` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
   [SUBGOAL_THEN `(a + b) + 1 < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c + d) MOD 2 EXP 64 = (c + d) - 2 EXP 64` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `(a + b) + 1 < n ==> a + b < n`] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `a + b < 2 EXP 64 /\ c + d < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; ADD_CLAUSES] THEN ARITH_TAC]);;

let POLY1305_ADD128_SWAP = prove
 (`!(xh:int64) (xl:int64) (yh:int64) (yl:int64).
     (2 EXP 64 * val xh + val xl) + (2 EXP 64 * val yh + val yl) < 2 EXP 128
     ==> 2 EXP 64 * val(word_add (word_add xh yh)
                         (word(bitval(2 EXP 64 <= val yl + val xl)))) +
         val(word_add yl xl) =
         (2 EXP 64 * val xh + val xl) + (2 EXP 64 * val yh + val yl)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`xh:int64`; `xl:int64`; `yh:int64`; `yl:int64`]
         POLY1305_ADD128) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ISPECL [`val(yl:int64)`; `val(xl:int64)`] ADD_SYM;
              ISPECL [`yl:int64`; `xl:int64`] WORD_ADD_SYM]);;

let POLY1305_CINC128 = prove
 (`!(c:int64) (h:int64) (l:int64).
     val c + (2 EXP 64 * val h + val l) < 2 EXP 128
     ==> 2 EXP 64 * val(if val c + val l < 2 EXP 64 then h
                         else word_add h (word 1)) +
         val(word_add c l) =
         val c + (2 EXP 64 * val h + val l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word 0:int64`; `c:int64`; `h:int64`; `l:int64`]
         POLY1305_ADD128) THEN
  REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM NOT_LE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[WORD_ADD_SYM]);;

let POLY1305_EXTR = prove
 (`!(h:int64) (l:int64) k.
     k <= 64 /\ 2 EXP 64 * val h + val l < 2 EXP (64 + k)
     ==> val(word_subword (word_join h l:int128) (k,64):int64) =
         (2 EXP 64 * val h + val l) DIV 2 EXP k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_128] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 64 = 64`] THEN
  SUBGOAL_THEN `2 EXP 64 * val(h:int64) + val(l:int64) < 2 EXP 128`
  ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (64 + k)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    UNDISCH_TAC `k <= 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC POLY1305_DIV_BOUND THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ADD_SYM] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The computation of the code: the low and high words of 128-bit sums.      *)
(* 2^64 * val hi + val lo = N for the 128-bit values built by mul/umulh,      *)
(* adds/adc and adds/cinc, N a sum of products and vals; the side            *)
(* conditions (the sums below 2^128) are proved by the given tactic. The     *)
(* other low word of a sum, and the three limbs at the end of the block.     *)
(* ------------------------------------------------------------------------- *)

let rec POLY1305_PAIR_RULE (bndtac:tactic) (hi,lo) =
  let expected =
    mk_binop `(+):num->num->num`
     (mk_binop `( * ):num->num->num` `2 EXP 64`
        (mk_comb(`val:int64->num`,hi)))
     (mk_comb(`val:int64->num`,lo)) in
  let finish th =
    if lhand(concl(UNDISCH th)) <> expected then failwith "pair" else
    let ant = lhand(concl th) in
    let ath = TAC_PROOF(([],ant),bndtac) in MP th ath in
  let try_mul () =
    match lo with
      Comb(Const("word",_),Comb(Comb(Const("+",_),z),p)) when z = `0` ->
        finish (SPEC p POLY1305_MUL128N)
    | _ -> failwith "mul" in
  let try_add () =
    match hi with
      Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),h1),h2)),
           Comb(Const("word",_),Comb(Const("bitval",_),cond))) ->
        let l1,l2 = match lo with
            Comb(Comb(Const("word_add",_),l1),l2) -> l1,l2
          | _ -> failwith "add" in
        (try let th1 = POLY1305_PAIR_RULE bndtac (h1,l1)
             and th2 = POLY1305_PAIR_RULE bndtac (h2,l2) in
             finish (REWRITE_RULE[th1;th2]
                       (SPECL [h1;l1;h2;l2] POLY1305_ADD128))
         with Failure _ ->
           let th1 = POLY1305_PAIR_RULE bndtac (h1,l2)
           and th2 = POLY1305_PAIR_RULE bndtac (h2,l1) in
           finish (REWRITE_RULE[th1;th2]
                     (SPECL [h1;l2;h2;l1] POLY1305_ADD128_SWAP)))
    | _ -> failwith "add" in
  let try_cinc () =
    match hi with
      Comb(Comb(Comb(Const("COND",_),_),h),_) ->
        let c,l = match lo with
            Comb(Comb(Const("word_add",_),c),l) -> c,l
          | _ -> failwith "cinc" in
        let th1 = POLY1305_PAIR_RULE bndtac (h,l) in
        finish (REWRITE_RULE[th1] (SPECL [c;h;l] POLY1305_CINC128))
    | _ -> failwith "cinc" in
  try try_mul () with Failure _ ->
  try try_add () with Failure _ ->
  try_cinc ();;

let POLY1305_FINAL_LEMMA = prove
 (`!(e:int64) (l0:int64) (l1:int64) (l2:int64) d0 d1 d2 f.
     val e = d2 DIV 2 EXP 42 /\ val l0 = d0 MOD 2 EXP 64 /\
     val l1 = d1 MOD 2 EXP 64 /\ val l2 = d2 MOD 2 EXP 64 /\
     f = 5 * d2 DIV 2 EXP 42 + d0 MOD 2 EXP 44 /\ f < 2 EXP 54 /\
     d1 MOD 2 EXP 44 + f DIV 2 EXP 44 < 2 EXP 45 /\ d2 < 2 EXP 92
     ==> val(word_and (word_add (word_add e (word_shl e 2))
                                (word_and l0 (word 17592186044415)))
                      (word 17592186044415)) = f MOD 2 EXP 44 /\
         val(word_add (word_and l1 (word 17592186044415))
                      (word_ushr (word_add (word_add e (word_shl e 2))
                                    (word_and l0 (word 17592186044415))) 44)) =
         d1 MOD 2 EXP 44 + f DIV 2 EXP 44 /\
         val(word_and l2 (word 4398046511103)) = d2 MOD 2 EXP 42`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `17592186044415 = 2 EXP 44 - 1`;
              ARITH_RULE `4398046511103 = 2 EXP 42 - 1`;
              VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN
   `val(word_add (word_add (e:int64) (word_shl e 2))
                 (word_and (l0:int64) (word(2 EXP 44 - 1)))) = f`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD_AND_MASK_WORD;
                DIMINDEX_64] THEN
    ASM_REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
    SUBGOAL_THEN `d2 DIV 2 EXP 42 < 2 EXP 50` MP_TAC THENL
     [POLY1305_DIVB_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`d0:num`; `2 EXP 44`] MOD_LT_EQ) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ABBREV_TAC `q = d2 DIV 4398046511104` THEN
    ABBREV_TAC `m0 = d0 MOD 17592186044416` THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ARITH_RULE
     `q < 1125899906842624 /\ m0 < 17592186044416
      ==> 4 * q < 18446744073709551616 /\
          q + 4 * q < 18446744073709551616 /\
          (q + 4 * q) + m0 < 18446744073709551616`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> rand(concl th) = `f:num` &&
                                           is_comb(lhand(concl th)))) THEN
  SPEC_TAC(`word_add (word_add (e:int64) (word_shl e 2))
                     (word_and (l0:int64) (word(2 EXP 44 - 1)))`,
           `ff:int64`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ASSUME `val(ff:int64) = f`] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD;
              DIMINDEX_64] THEN
  REWRITE_TAC[ASSUME `val(ff:int64) = f`;
              ASSUME `val(l1:int64) = d1 MOD 2 EXP 64`;
              ASSUME `val(l2:int64) = d2 MOD 2 EXP 64`; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 44 = 44 /\ MIN 64 42 = 42`] THEN
  MATCH_MP_TAC MOD_LT THEN
  UNDISCH_TAC `d1 MOD 2 EXP 44 + f DIV 2 EXP 44 < 2 EXP 45` THEN
  ARITH_TAC);;

let POLY1305_LO_LEMMA = prove
 (`!(h:int64) (l:int64) d.
     2 EXP 64 * val h + val l = d ==> val l = d MOD 2 EXP 64`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MOD_MULT_ADD; ONCE_REWRITE_RULE[MULT_SYM] MOD_MULT_ADD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Other lemmas: the end of the input from the 32-bit number of blocks, and *)
(* the step of the test.                                                     *)
(* ------------------------------------------------------------------------- *)

let PB_END_LEMMA = prove
 (`!nb:int64. val nb < 2 EXP 32
     ==> word_shl (word_zx (word_zx nb:int32):int64) 4 = word(16 * val nb)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 2 EXP 32 ==> n < 2 EXP 64`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 4 * n = 16 * n`]);;

let PB_WORD_SUB_ADD = WORD_RULE
  `word_sub (word_add (x:int64) a) (word_add x b) = word_sub a b`;;

(* ------------------------------------------------------------------------- *)
(* The setup: the limbs of the state as ghosts, those of r (rr0, rr1, rr2)   *)
(* and the key words (r0w ... s2w); the 32-bit number of blocks.             *)
(* ------------------------------------------------------------------------- *)

let PB_SETUP_TAC =
  MAP_EVERY X_GEN_TAC
    [`state:int64`; `key:int64`; `src:int64`; `nb:int64`; `hbw:int64`;
     `m:byte list`; `a:num`; `r:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES; poly1305_key_at; poly1305_h_at] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GHOST_INTRO_TAC `h0w:int64` `read (memory :> bytes64 state)` THEN
  GHOST_INTRO_TAC `h1w:int64`
   `read (memory :> bytes64 (word_add state (word 8)))` THEN
  GHOST_INTRO_TAC `h2w:int64`
   `read (memory :> bytes64 (word_add state (word 16)))` THEN
  ABBREV_TAC `rr0 = r MOD 2 EXP 44` THEN
  ABBREV_TAC `rr1 = (r DIV 2 EXP 44) MOD 2 EXP 44` THEN
  ABBREV_TAC `rr2 = r DIV 2 EXP 88` THEN
  ABBREV_TAC `r0w:int64 = word rr0` THEN
  ABBREV_TAC `r1w:int64 = word rr1` THEN
  ABBREV_TAC `r2w:int64 = word rr2` THEN
  ABBREV_TAC `s1w:int64 = word(20 * rr1)` THEN
  ABBREV_TAC `s2w:int64 = word(20 * rr2)` THEN
  SUBGOAL_THEN `rr0 < 2 EXP 44 /\ rr1 < 2 EXP 44 /\ rr2 < 2 EXP 36 /\
                rr0 + 2 EXP 44 * rr1 + 2 EXP 88 * rr2 = r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST1_TAC o SYM o check
                 (fun th -> rand(concl th) = v)))
     [`rr0:num`; `rr1:num`; `rr2:num`] THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLY1305_DIV_BOUND THEN
      CONV_TAC(RAND_CONV(RAND_CONV NUM_ADD_CONV)) THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`r:num`; `2 EXP 44`] DIVISION) THEN
      MP_TAC(SPECL [`r DIV 2 EXP 44`; `2 EXP 44`] DIVISION) THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ; DIV_DIV; GSYM EXP_ADD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(r0w:int64) = rr0 /\ val(r1w:int64) = rr1 /\ val(r2w:int64) = rr2 /\
    val(s1w:int64) = 20 * rr1 /\ val(s2w:int64) = 20 * rr2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST1_TAC o SYM o check
                 (fun th -> rand(concl th) = v)))
     [`r0w:int64`; `r1w:int64`; `r2w:int64`; `s1w:int64`; `s2w:int64`] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN
    MAP_EVERY UNDISCH_TAC
     [`rr0 < 2 EXP 44`; `rr1 < 2 EXP 44`; `rr2 < 2 EXP 36`] THEN
    ARITH_TAC;
    ALL_TAC];;

let PB_ZX_TAC =
  SUBGOAL_THEN `val(word_zx (nb:int64):int32) = val nb` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop after i blocks (the limbs in X1, X14 and X5),   *)
(* with the flags of the test at the end; the limbs as ghosts.               *)
(* ------------------------------------------------------------------------- *)

let pb_inv = `\i s.
   (read X0 s = state /\ read X30 s = returnaddress /\
    read X2 s = word_add src (word(16 * i)) /\
    read X11 s = word_add src (word(16 * val(nb:int64))) /\
    read X6 s = r0w /\ read X8 s = r1w /\ read X10 s = r2w /\
    read X9 s = s1w /\ read X7 s = s2w /\
    read X12 s = word_shl (hbw:int64) 40 /\
    read (memory :> bytes(src,16 * val nb)) s = num_of_bytelist m /\
    val(read X1 s) < 2 EXP 44 /\ val(read X14 s) < 2 EXP 45 /\
    val(read X5 s) < 2 EXP 42 /\
    (val(read X1 s) + 2 EXP 44 * val(read X14 s) + 2 EXP 88 * val(read X5 s))
    MOD (2 EXP 130 - 5) = poly1305_kacc r a m (val hbw) i) /\
   (read ZF s <=> i = val nb)`;;

let PB_GHOST_TAC =
  GHOST_INTRO_TAC `u0:int64` `read X1` THEN
  GHOST_INTRO_TAC `u1:int64` `read X14` THEN
  GHOST_INTRO_TAC `u2:int64` `read X5`;;

(* ------------------------------------------------------------------------- *)
(* The loop body for block i: the arithmetic of the block (from              *)
(* POLY1305_DONNA_BLOCK) before the simulation, the two words of the block   *)
(* (t0w, t1w), the simulation, and the code's limbs from its sums.           *)
(* ------------------------------------------------------------------------- *)

let PB_BODY_PRE_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN PB_GHOST_TAC THEN
  ABBREV_TAC `t0w:int64 = word(num_of_bytelist(SUB_LIST(16 * i,8) m))` THEN
  ABBREV_TAC `t1w:int64 = word(num_of_bytelist(SUB_LIST(16 * i + 8,8) m))` THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `val(t0w:int64) < 2 EXP 64 /\ val(t1w:int64) < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND]; ALL_TAC] THEN
  ABBREV_TAC `a0 = val(t0w:int64) MOD 2 EXP 44 + val(u0:int64)` THEN
  ABBREV_TAC `a1 = (val(t0w:int64) DIV 2 EXP 44 +
                    2 EXP 20 * val(t1w:int64) MOD 2 EXP 24) +
                   val(u1:int64)` THEN
  ABBREV_TAC `a2 = (2 EXP 40 * val(hbw:int64) + val(t1w:int64) DIV 2 EXP 24) +
                   val(u2:int64)` THEN
  ABBREV_TAC `d0 = a0 * rr0 + a1 * (20 * rr2) + a2 * (20 * rr1)` THEN
  ABBREV_TAC
   `d1 = (a0 * rr1 + a1 * rr0 + a2 * (20 * rr2)) + d0 DIV 2 EXP 44` THEN
  ABBREV_TAC `d2 = (a0 * rr2 + a1 * rr1 + a2 * rr0) + d1 DIV 2 EXP 44` THEN
  ABBREV_TAC `f = 5 * d2 DIV 2 EXP 42 + d0 MOD 2 EXP 44` THEN
  MP_TAC(SPECL [`val(u0:int64)`; `val(u1:int64)`; `val(u2:int64)`;
                `rr0:num`; `rr1:num`; `rr2:num`;
                `val(t0w:int64)`; `val(t1w:int64)`; `val(hbw:int64)`;
                `a0:num`; `a1:num`; `a2:num`; `d0:num`; `d1:num`; `d2:num`;
                `f:num`] POLY1305_DONNA_BLOCK) THEN
  ANTS_TAC THENL
   [REPLICATE_TAC 9 (CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `val(word_add (word_and t0w (word 17592186044415)) (u0:int64)) = a0 /\
    val(word_add (word_and (word_subword (word_join (t1w:int64) t0w:int128)
                                         (44,64))
                           (word 17592186044415)) (u1:int64)) = a1 /\
    val(word_add (word_or (word_shl hbw 40) (word_ushr t1w 24)) (u2:int64)) =
    a2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; POLY1305_M1] THEN
    ASM_SIMP_TAC[POLY1305_M2] THEN
    REWRITE_TAC[ARITH_RULE `17592186044415 = 2 EXP 44 - 1`;
                VAL_WORD_AND_MASK_WORD] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MAP_EVERY UNDISCH_TAC
     [`a0 < 2 EXP 45`; `a1 < 2 EXP 46`; `a2 < 2 EXP 43`] THEN
    ARITH_TAC;
    ALL_TAC];;

let PB_BODY_SIM_TAC =
  MP_TAC(ISPECL [`src:int64`; `m:byte list`; `16 * val(nb:int64)`; `16 * i`;
                 `s0:armstate`] WG_READ_BYTES64_BYTELIST) THEN
  MP_TAC(ISPECL [`src:int64`; `m:byte list`; `16 * val(nb:int64)`;
                 `16 * i + 8`; `s0:armstate`] WG_READ_BYTES64_BYTELIST) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(16 * i + 8) + 8 <= 16 * val(nb:int64) /\ 16 * i + 8 <= 16 * val nb`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `i < val(nb:int64)` THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  ARM_STEPS_TAC WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_EXEC (1--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* The 128-bit sums d0, d1 and d2 of the code (each with the carry of the    *)
(* previous one, extracted with extr) and the limbs from them.               *)

let pb_extrs k w =
  let ts = setify(find_terms (fun t -> match t with
      Comb(Comb(Const("word_subword",_),Comb(Comb(Const("word_join",_),_),_)),
           pr) -> pr = mk_pair(mk_small_numeral k,`64`)
    | _ -> false) w) in
  let sz t = String.length(string_of_term t) in
  map snd (sort (fun (a,_) (b,_) -> a < b) (map (fun t -> sz t,t) ts));;

let pb_hl t = let x = rand(rator t) in (rand(rator x),rand x);;

let pb_bnd_facts () = map ASSUME
  [`a0 * rr0 + a1 * (20 * rr2) + a2 * (20 * rr1) = d0`;
   `(a0 * rr1 + a1 * rr0 + a2 * (20 * rr2)) + d0 DIV 2 EXP 44 = d1`;
   `(a0 * rr2 + a1 * rr1 + a2 * rr0) + d1 DIV 2 EXP 44 = d2`;
   `d0 < 2 EXP 93`; `d1 < 2 EXP 92`; `d2 < 2 EXP 92`];;

let PB_BND_TAC xths =
  REWRITE_TAC xths THEN MAP_EVERY MP_TAC (pb_bnd_facts()) THEN ARITH_TAC;;

let PB_PAIR_RULE xths e d =
  let th = POLY1305_PAIR_RULE (PB_BND_TAC xths) (pb_hl e) in
  TRANS th (TAC_PROOF(([],mk_eq(rand(concl th),d)),PB_BND_TAC xths));;

let PB_EXTR_RULE th k =
  let l = lhand(concl th) in
  let h = rand(rand(lhand l)) and lo = rand(rand l) in
  let eth = SPECL [h; lo; mk_small_numeral k] POLY1305_EXTR in
  let ath = TAC_PROOF(([],lhand(concl eth)),
     REWRITE_TAC[th] THEN CONV_TAC NUM_REDUCE_CONV THEN
     MAP_EVERY MP_TAC (pb_bnd_facts()) THEN CONV_TAC NUM_REDUCE_CONV THEN
     ARITH_TAC) in
  REWRITE_RULE[th] (MP eth ath);;

let PB_LIMBS_TAC (asl,w as gl) =
  let e0 = el 0 (pb_extrs 44 w) and e1 = el 1 (pb_extrs 44 w)
  and e2 = el 0 (pb_extrs 42 w) in
  let th0 = PB_PAIR_RULE [] e0 `d0:num` in
  let x0 = PB_EXTR_RULE th0 44 in
  let th1 = PB_PAIR_RULE [x0] e1 `d1:num` in
  let x1 = PB_EXTR_RULE th1 44 in
  let th2 = PB_PAIR_RULE [x0; x1] e2 `d2:num` in
  let x2 = PB_EXTR_RULE th2 42 in
  let th = SPECL [e2; snd(pb_hl e0); snd(pb_hl e1); snd(pb_hl e2);
                  `d0:num`; `d1:num`; `d2:num`; `f:num`]
             POLY1305_FINAL_LEMMA in
  let fth = MP th (end_itlist CONJ
    [x2; MATCH_MP POLY1305_LO_LEMMA th0; MATCH_MP POLY1305_LO_LEMMA th1;
     MATCH_MP POLY1305_LO_LEMMA th2;
     SYM(ASSUME `5 * d2 DIV 2 EXP 42 + d0 MOD 2 EXP 44 = f`);
     ASSUME `f < 2 EXP 54`;
     ASSUME `d1 MOD 2 EXP 44 + f DIV 2 EXP 44 < 2 EXP 45`;
     ASSUME `d2 < 2 EXP 92`]) in
  REWRITE_TAC[fth] gl;;

(* The invariant after the block: the pointer, the limb bounds, the new      *)
(* accumulator (the block being t0w + 2^64 * t1w) and the test.              *)

let PB_BODY_FIN_TAC =
  PB_LIMBS_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `16 * (i + 1) = 16 * i + 16`; MOD_LT_EQ;
              EXP_EQ_0; ARITH_EQ; PB_WORD_SUB_ADD] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `i + 1 = SUC i`; poly1305_kacc] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term ((=) `poly1305_kacc`)) (concl th) &&
      is_eq(concl th))) THEN
    SUBGOAL_THEN
     `num_of_bytelist(SUB_LIST(16 * i,16) m) =
      val(t0w:int64) + 2 EXP 64 * val(t1w:int64)`
    SUBST1_TAC THENL
     [REWRITE_TAC[WG_SUB_LIST_16; WG_NUM_OF_BYTELIST_APPEND] THEN
      SUBGOAL_THEN `LENGTH(SUB_LIST(16 * i,8) (m:byte list)) = 8 /\
                    LENGTH(SUB_LIST(16 * i + 8,8) (m:byte list)) = 8`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN
        UNDISCH_TAC `LENGTH(m:byte list) = 16 * val(nb:int64)` THEN
        UNDISCH_TAC `i < val(nb:int64)` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SYM(ASSUME
        `word(num_of_bytelist(SUB_LIST(16 * i,8) m)):int64 = t0w`);
                  SYM(ASSUME
        `word(num_of_bytelist(SUB_LIST(16 * i + 8,8) m)):int64 = t1w`)] THEN
      ASM_SIMP_TAC[WG_VAL_WORD_BYTES8] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPECL
     [`val(u0:int64) + 2 EXP 44 * val(u1:int64) + 2 EXP 88 * val(u2:int64)`;
      `(val(u0:int64) + 2 EXP 44 * val(u1:int64) + 2 EXP 88 * val(u2:int64))
       MOD (2 EXP 130 - 5)`;
      `(val(t0w:int64) + 2 EXP 64 * val(t1w:int64)) +
       2 EXP 128 * val(hbw:int64)`;
      `r:num`; `2 EXP 130 - 5`] POLY1305_MOD_STEP) THEN
    REWRITE_TAC[MOD_MOD_REFL] THEN REWRITE_TAC[GSYM ADD_ASSOC];
    MP_TAC(SPECL [`16 * i + 16`; `16 * val(nb:int64)`]
                 WG_VAL_WORD_SUB_EQ_0) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `i < val(nb:int64)` THEN
      UNDISCH_TAC `val(nb:int64) < 2 EXP 32` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ARITH_TAC]];;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = WIREGUARD_POLY1305_CORE_BLOCKS_GCC13_O2_EXEC in
  PB_SETUP_TAC THEN ASM_CASES_TAC `val(nb:int64) = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--2) THEN PB_ZX_TAC THEN
    WG_PC_REWRITE_TAC[ASSUME `val(word_zx (nb:int64):int32) = val nb`;
                      ASSUME `val(nb:int64) = 0`] THEN
    ARM_STEPS_TAC EXEC [3] THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[poly1305_kacc];
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `val(nb:int64)` `pc + poly1305_core_blocks_loop1`
    `pc + poly1305_core_blocks_loop1_back` pb_inv THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--2) THEN PB_ZX_TAC THEN
    WG_PC_REWRITE_TAC[ASSUME `val(word_zx (nb:int64):int32) = val nb`;
                      ASSUME `~(val(nb:int64) = 0)`] THEN
    ARM_STEPS_TAC EXEC (3--10) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[PB_END_LEMMA; poly1305_kacc; MULT_CLAUSES; WORD_ADD_0];

    PB_BODY_PRE_TAC THEN PB_BODY_SIM_TAC THEN PB_BODY_FIN_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN PB_GHOST_TAC THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    PB_GHOST_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of libzstd_huf.so, zstd's Huffman and FSE     *)
(* decoding compiled by gcc 12 with -O2 (see arm/zstd/README.md), as one     *)
(* image, and tools for the proofs about the functions in it. As for puff,   *)
(* all the theorems about the image assume that it is loaded at an address   *)
(* pc that is a multiple of 4096 and does not wrap around the end of the     *)
(* address space, and the functions are then at pc + <address>, where        *)
(* <address> is that in the binary. The tools of puff.ml that are not        *)
(* specific to puff are used here too.                                       *)
(* ========================================================================= *)

needs "arm/proofs/utils/puff.ml";;
needs "common/rfc8878_theory.ml";;

let zstd_huf_gcc12_O2_mc = define_from_elf
  "zstd_huf_gcc12_O2_mc" "arm/zstd/zstd_huf_gcc12_O2.o";;

let LENGTH_ZSTD_HUF_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` zstd_huf_gcc12_O2_mc);;

(* ------------------------------------------------------------------------- *)
(* The code: the stubs of the procedure linkage table for memcpy and memset, *)
(* and the functions in the decoding of single-stream Huffman-coded          *)
(* literals.                                                                 *)
(* ------------------------------------------------------------------------- *)

let ZSTD_EXEC = ARM_MK_EXEC_RANGES_RULE zstd_huf_gcc12_O2_mc
  [0x640,0x650; 0x660,0x670; 0x770,0xc0c; 0xc60,0xc68; 0xca0,0xca4;
   0xe80,0x10e8; 0x10f4,0x1c20; 0x2850,0x2b2c; 0x66d4,0x6b88;
   0x7340,0x73d0];;

(* ------------------------------------------------------------------------- *)
(* Words of small numbers: the rules of SMALL_WORD_CONV in puff.ml and some  *)
(* more, for shifts and masks of numbers and offsets of pointers.            *)
(* ------------------------------------------------------------------------- *)

let WORD_USHR_WORD_SMALL = prove
 (`!a k. a < 2 EXP dimindex(:N)
         ==> word_ushr (word a:N word) k = word(a DIV 2 EXP k)`,
  SIMP_TAC[word_ushr; VAL_WORD; MOD_LT]);;

let WORD_AND_7_SMALL = prove
 (`!a. a < 2 EXP dimindex(:N)
       ==> word_and (word a) (word 7):N word = word(a MOD 8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num`; `3`] WORD_AND_MASK_SMALL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SIMP_TAC[]);;

let WORD_SUB_ADD_SMALL = prove
 (`!(x:N word) a b.
        b <= a
        ==> word_sub (word_add x (word a)) (word b) =
            word_add x (word(a - b))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let WORD_SUB_ZX_ADD = prove
 (`!(x:int64) a.
        word_sub (word_zx (word_add x (word a)):int32) (word_zx x) = word a`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_add x (word a):int64 = word(val x + a)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD; WORD_VAL]; ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (x:int64):int32 = word(val x)` SUBST1_TAC THENL
   [REWRITE_TAC[word_zx]; ALL_TAC] THEN
  SIMP_TAC[WORD_ZX_WORD_SIMPLE; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_SUB_BASE = prove
 (`!(x:N word) a. word_sub (word_add x (word a)) x = word a`,
  CONV_TAC WORD_RULE);;

let WORD_CLZ_WORD32 = prove
 (`!n. n < 2 EXP 32 ==> word_clz(word n:int32) = 32 - bitsize n`,
  SIMP_TAC[WORD_CLZ_BITSIZE; VAL_WORD; DIMINDEX_32; MOD_LT]);;

let ZSTD_SMALL_WORD_RULES =
  let split th =
    let th' = SPEC_ALL th in
    if is_imp(concl th') then
      let c = lhand(concl th') in
      map (GEN_ALL o DISCH c) (CONJUNCTS(UNDISCH th'))
    else map GEN_ALL (CONJUNCTS th') in
  SMALL_WORD_RULES @
  List.concat (map split
   [WORD_USHR_WORD_SMALL; WORD_AND_7_SMALL; WORD_SUB_ADD_SMALL;
    WORD_SUB_ZX_ADD; WORD_ADD_SUB_BASE; SUB_REFL; WORD_ADD_0;
    WORD_CLZ_WORD32]);;

(*** SMALL_WORD_CONV and SMALL_WORD_TAC of puff.ml with these rules ***)

let ZSTD_SMALL_WORD_CONV asl =
  let pc_tm = `pc:num` in
  let prove_cond c =
    let th1 = (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) c in
    let c' = rhs(concl th1) in
    let th2 =
      if c' = `T` then TRUTH else
      let divs = find_terms (is_binary "DIV") c'
      and mods = find_terms (is_binary "MOD") c' in
      let vals =
        find_terms (fun t -> is_comb t && rator t = `val:byte->num`) c' in
      let facts = map (fun t -> SPECL [lhand t; rand t] DIV_LE) divs @
                  map (fun t -> SPECL [lhand t; rand t] MOD_LE) mods @
                  map (fun t -> CONV_RULE (DEPTH_CONV DIMINDEX_CONV THENC
                                           NUM_REDUCE_CONV)
                                (ISPEC (rand t) VAL_BOUND)) vals in
      TAC_PROOF((asl,c'),MAP_EVERY MP_TAC facts THEN SIMPLE_ARITH_TAC) in
    EQ_MP (SYM th1) th2 in
  let rule_conv th =
    let th' = SPEC_ALL th in
    if is_imp(concl th') then
      let pm = PART_MATCH (lhs o rand) th in
      fun tm -> if free_in pc_tm tm then failwith "ZSTD_SMALL_WORD_CONV" else
                let ith = pm tm in MP ith (prove_cond(lhand(concl ith)))
    else
      let pm = PART_MATCH lhs th in
      fun tm -> if free_in pc_tm tm then failwith "ZSTD_SMALL_WORD_CONV" else
                pm tm in
  let conv = FIRST_CONV (map rule_conv ZSTD_SMALL_WORD_RULES) in
  TOP_DEPTH_CONV conv THENC NUM_REDUCE_CONV;;

let ZSTD_SMALL_WORD_TAC:tactic =
  let flags = [`NF`; `ZF`; `CF`; `VF`; `PC`; `events`] in
  fun (asl,w as gl) ->
    let s = try rand w with Failure _ -> w in
    let conv = ZSTD_SMALL_WORD_CONV asl in
    let rule th =
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),_)
          when s' = s && not(mem c flags) -> CONV_RULE (RAND_CONV conv) th
      | _ -> th in
    RULE_ASSUM_TAC rule gl;;

(* ------------------------------------------------------------------------- *)
(* Comparisons of pointers. The flags of a comparison of two pointers into   *)
(* the same region, or of a pointer with its base, are decided by expressing *)
(* them in terms of val a + k for the base a and offsets k, when the region  *)
(* does not wrap around the end of the address space. Conditions are         *)
(* decided by SIMPLE_ARITH_TAC or failing that by arithmetic that also uses  *)
(* the facts involving val.                                                  *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_SUB_EQ_0 = prove
 (`!x y:N word. val(word_sub x y) = 0 <=> val x = val y`,
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; VAL_EQ]);;

let VAL_WORD_NEG_EQ_0 = prove
 (`!x:N word. val(word_neg x) = 0 <=> val x = 0`,
  REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0]);;

let VAL_WORD_LT64 = prove
 (`!x. x < 2 EXP 64 ==> val(word x:int64) = x`,
  SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

let VAL_WORD_ADD_NOWRAP = prove
 (`!(a:int64) x.
        val a + x < 2 EXP 64 ==> val(word_add a (word x)) = val a + x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `x MOD 2 EXP 64 = x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

let VAL_WORD_SUB_NOWRAP = prove
 (`!(a:int64) x. x <= val a ==> val(word_sub a (word x)) = val a - x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND_64) THEN DISCH_TAC THEN
  SUBGOAL_THEN `x MOD 2 EXP 64 = x` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let VAL_WORD_SUB_ADD_NOWRAP = prove
 (`!(a:int64) x y.
        y <= val a + x /\ val a + x < 2 EXP 64
        ==> val(word_sub (word_add a (word x)) (word y)) = (val a + x) - y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add a (word x):int64 = word(val a + x)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD; WORD_VAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB2] THEN MATCH_MP_TAC VAL_WORD_LT64 THEN
  ASM_ARITH_TAC);;

let ZSTD_VAL_ARITH_TAC = SIMPLE_ARITH_TAC ORELSE MEMSAFE_VAL_ARITH_TAC;;

let PTR_VAL_CONV asl =
  let prove_cond c = TAC_PROOF((asl,c),ZSTD_VAL_ARITH_TAC) in
  let rule_conv th tm =
    let ith = PART_MATCH (lhs o rand) th tm in
    MP ith (prove_cond(lhand(concl ith))) in
  TOP_DEPTH_CONV(rule_conv VAL_WORD_SUB_ADD_NOWRAP ORELSEC
                 rule_conv VAL_WORD_ADD_NOWRAP ORELSEC
                 rule_conv VAL_WORD_SUB_NOWRAP ORELSEC
                 rule_conv VAL_WORD_LT64);;

(*** The same in the flags C and Z and the PC of the current state ***)

let PTR_FLAGS_TAC =
  let flags = [`ZF`; `CF`; `PC`] in
  W(fun (asl,w) ->
    let s = rand w in
    let conv = REWRITE_CONV[VAL_WORD_SUB_EQ_0; VAL_WORD_NEG_EQ_0] THENC
               PTR_VAL_CONV asl in
    RULE_ASSUM_TAC(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),_)
          when s' = s && mem c flags -> CONV_RULE (RAND_CONV conv) th
      | _ -> th));;

(*** DECIDE_PROP_TAC and DECIDE_BRANCH_TAC of puff.ml with that arithmetic ***)

let ZSTD_DECIDE_PROP_TAC c =
  let rule th th' = if aconv (concl th') (concl th) then th'
                    else REWRITE_RULE[EQT_INTRO th] th' in
  let keep th (asl,w as gl) =
    let c = concl th in
    if is_eq c &&
       exists (fun (_,a) -> aconv (concl a) c ||
                            aconv (concl a) (mk_eq(rhs c,lhs c))) asl
    then ALL_TAC gl else ASSUME_TAC th gl in
  (SUBGOAL_THEN c
    (fun th -> RULE_ASSUM_TAC(rule th) THEN keep th) THENL
    [ZSTD_VAL_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [ZSTD_VAL_ARITH_TAC; ALL_TAC]);;

let ZSTD_DECIDE_BRANCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not (is_cond r) || not(can (term_match [] `read PC s`) l)
    then failwith "ZSTD_DECIDE_BRANCH_TAC" else
    ZSTD_DECIDE_PROP_TAC (lhand(rator r)));;

(*** The signed comparison of small numbers, as WORD_CMP_32_SFLAGS ***)

let WORD_CMP_64_SFLAGS = prove
 (`!x y. x < 4611686018427387904 /\ y < 4611686018427387904
         ==> (ival(word_sub (word x) (word y):int64) < &0 <=> x < y) /\
             (ival(word x:int64) - &y =
              ival(word_sub (word x) (word y):int64)) /\
             (ival(word x:int64) - ival(word y:int64) =
              ival(word_sub (word x) (word y):int64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word x:int64) = &x /\ ival(word y:int64) = &y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word_sub (word x) (word y):int64) = &x - &y`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word x) (word y):int64 =
                           iword(&x - &y)`] THEN
    MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC;
    ASM_REWRITE_TAC[INT_LT_SUB_RADD; INT_ADD_LID; INT_OF_NUM_LT] THEN
    INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Simulation: ZSTD_STEP_TAC n is PUFF_STEP_TAC n for the image, with these  *)
(* rules and comparisons of pointers too. ZSTD_RUN_TAC simulates the code up *)
(* to the return, and ZSTD_SIM_UNTIL_TAC up to the return or one of the      *)
(* given addresses, as long as the branches are decided.                     *)
(* ------------------------------------------------------------------------- *)

let ZSTD_STEP_TAC n =
  let conditional (asl,w) =
    let s = rand w in
    exists (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s')),t)
          when s' = s && not(c = `events`) -> can (find_term is_cond) t
      | _ -> false) asl in
  ARM_STEPS_TAC ZSTD_EXEC [n] THEN ZSTD_SMALL_WORD_TAC THEN
  (fun gl -> if conditional gl then
               (TRY W32_DECIDE_FLAGS_TAC THEN TRY PTR_DECIDE_FLAGS_TAC THEN
                TRY(CMP_FLAGS_TAC `word_sub (word x) (word y):int64`
                                  WORD_CMP_64_SFLAGS) THEN
                TRY PTR_FLAGS_TAC THEN TRY DECIDE_FLAGS_TAC THEN
                PC_COND_NORM_TAC THEN TRY ZSTD_DECIDE_BRANCH_TAC THEN
                TRY DECIDE_IFS_TAC THEN ZSTD_SMALL_WORD_TAC) gl
             else ALL_TAC gl);;

let ZSTD_STEPS_TAC ns = MAP_EVERY ZSTD_STEP_TAC ns;;

let ZSTD_RUN_TAC =
  let num_of_state s =
    let n = fst(dest_var s) in
    int_of_string(String.sub n 1 (String.length n - 1)) in
  let rec run k n (asl,w as gl) =
    let pc = current_pc gl in
    if pc = `returnaddress:int64` then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "ZSTD_RUN_TAC"
    else (ZSTD_STEP_TAC n THEN run (k - 1) (n + 1)) gl in
  fun (asl,w as gl) -> run 40 (num_of_state(rand w) + 1) gl;;

let ZSTD_SIM_UNTIL_TAC stops =
  let num_of_state s =
    let n = fst(dest_var s) in
    int_of_string(String.sub n 1 (String.length n - 1)) in
  let stops =
    map (fun k -> mk_comb(`word:num->int64`,
           mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral k)))
        stops in
  let rec run k n (asl,w as gl) =
    let pc = current_pc gl in
    if pc = `returnaddress:int64` || mem pc stops then ALL_TAC gl
    else if k = 0 || is_cond pc then failwith "ZSTD_SIM_UNTIL_TAC"
    else (ZSTD_STEP_TAC n THEN run (k - 1) (n + 1)) gl in
  fun (asl,w as gl) -> run 60 (num_of_state(rand w) + 1) gl;;

(* ------------------------------------------------------------------------- *)
(* Proofs in pieces. The theorems for the pieces of a function have the same *)
(* frame, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI and some memory, which   *)
(* ZSTD_INTRO_TAC expands. In a simulation, ZSTD_CONTINUE_WITH_TAC wtac th   *)
(* insts goes on with the theorem th of a later piece, with the              *)
(* instantiation insts of its variables (the others having the names that   *)
(* they have in the goal) and its hypotheses among the assumptions, leaving  *)
(* its precondition to be proved for the current state, and proving with     *)
(* wtac that its postcondition implies that of the goal (ZSTD_CONTINUE_TAC   *)
(* for the simplest case).                                                   *)
(* ------------------------------------------------------------------------- *)

let ZSTD_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS];;

let EVENTUALLY_ENSURES = prove
 (`!(step:A->A->bool) P Q C Q' (s0:A) s.
        ensures step P Q C
        ==> C ,, C = C /\ P s /\ C s0 s /\ (!s'. Q s' ==> Q' s')
            ==> eventually step (\s'. Q' s' /\ C s0 s') s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN
  DISCH_THEN(MP_TAC o SPEC `s:A`) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  X_GEN_TAC `s':A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `(C:A->A->bool) ,, C = C` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[seq] THEN ASM_MESON_TAC[]);;

let ZSTD_CONTINUE_WITH_TAC wtac th insts =
  let frame_rule =
    REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_GPRS;
                 MODIFIABLE_SIMD_REGS; MODIFIABLE_UPPER_SIMD_REGS;
                 SOME_FLAGS] in
  W(fun (asl,w) ->
    let th1 = INST insts (SPEC_ALL th) in
    let hyp = lhand(concl th1) in
    let hth = TAC_PROOF((asl,hyp),
                REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
    let eth = frame_rule(MP th1 hth) in
    MATCH_MP_TAC(MATCH_MP EVENTUALLY_ENSURES eth) THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [BETA_TAC;
      CONJ_TAC THENL [MONOTONE_MAYCHANGE_TAC; BETA_TAC THEN wtac]]);;

let ZSTD_CONTINUE_TAC =
  ZSTD_CONTINUE_WITH_TAC (GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(*** A loop whose invariant lp n, for a measure n, holds at the start ***)

let ENSURES_WHILE_MEASURE_EXISTS = prove
 (`!(lp:num->A->bool) Q C.
        C ,, C = C /\ (=) subsumed C /\
        (!n. ensures step (lp n) (\s. (?m. m < n /\ lp m s) \/ Q s) C)
        ==> ensures step (\s. ?n. lp n s) Q C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_WHILE_MEASURE THEN
  EXISTS_TAC `lp:num->A->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ensures] THEN X_GEN_TAC `s:A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `((=):A->A->bool) subsumed C` THEN
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;

(*** At the end, the conditions in the goal decided by arithmetic ***)

let ZSTD_DECIDE_GOAL_TAC =
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(W(fun (asl,w) ->
    match find_terms is_cond w with
      [] -> NO_TAC
    | c::_ -> ZSTD_DECIDE_PROP_TAC (lhand(rator c)) THEN ASM_REWRITE_TAC[]));;

let ZSTD_FINAL_TAC = PUFF_FINAL_TAC THEN ZSTD_DECIDE_GOAL_TAC;;

(*** Arithmetic, splitting the conjunctions and disjunctions of facts ***)

let ZSTD_ARITH_TAC =
  let is_arith_disj tm =
    is_disj tm &&
    not(exists (fun v -> type_of v = `:armstate`) (frees tm)) in
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o
                       check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_arith_disj o concl))) THEN
  SIMPLE_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The error codes that zstd's functions return: ERR_isError.                *)
(* ------------------------------------------------------------------------- *)

let zstd_is_error = new_definition
 `zstd_is_error (x:int64) <=> 2 EXP 64 - 120 < val x`;;

(* ------------------------------------------------------------------------- *)
(* The bits of the specification, for a list of bytes in memory.            *)
(* ------------------------------------------------------------------------- *)

let ZSTD_BIT_NUM = prove
 (`!(st:byte list) i. zstd_bit st i <=> ODD(num_of_bytelist st DIV 2 EXP i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zstd_bit] THEN
  ASM_CASES_TAC `i < 8 * LENGTH(st:byte list)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[BIT_VAL] THEN
    MP_TAC(SPECL [`st:byte list`; `i DIV 8`] NUM_OF_BYTELIST_BYTE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN
    SUBGOAL_THEN `2 EXP 8 = 2 EXP (i MOD 8) * 2 EXP (8 - i MOD 8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      MP_TAC(SPECL [`i:num`; `8`] MOD_LT_EQ) THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_MOD; DIV_DIV; GSYM EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE `8 * i DIV 8 + i MOD 8 = i`] THEN
    REWRITE_TAC[ODD_MOD_POW2; TAUT `(a /\ b <=> b) <=> (b ==> a)`] THEN
    DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(SPECL [`i:num`; `8`] MOD_LT_EQ) THEN ARITH_TAC;
    SUBGOAL_THEN `num_of_bytelist (st:byte list) DIV 2 EXP i = 0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      TRANS_TAC LTE_TRANS `256 EXP LENGTH(st:byte list)` THEN
      REWRITE_TAC[NUM_OF_BYTELIST_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT; LE_EXP] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[ODD]]]);;

let ZSTD_BITS_NUM = prove
 (`!(st:byte list) p n.
        zstd_bits st p n = (num_of_bytelist st DIV 2 EXP p) MOD 2 EXP n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[zstd_bits; EXP; MOD_1] THEN GEN_TAC THEN
  REWRITE_TAC[ZSTD_BIT_NUM; BITVAL_ODD] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; EXP_1; MOD_MULT_MOD; ODD_MOD] THEN
  ARITH_TAC);;

(* An 8-byte load from within a region of bytes.                             *)

let READ_MEMORY_BYTES64_SLICE = prove
 (`!a n x ofs s.
        read (memory :> bytes(a,n)) s = x /\ ofs + 8 <= n
        ==> read (memory :> bytes64 (word_add a (word ofs))) s =
            word((x DIV 2 EXP (8 * ofs)) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP (8 * 8)`; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `ofs + 8 <= n ==> MIN (n - ofs) 8 = 8`] THEN
  REWRITE_TAC[BYTES64_WBYTES; wbytes; READ_COMPONENT_COMPOSE; asword;
              through; read; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The end of a backward stream, from its last byte: the stream has to be    *)
(* nonempty with a nonzero last byte, and the first bit is its top one.      *)
(* ------------------------------------------------------------------------- *)

let ODD_DIV_TOP = prove
 (`!m. ODD m /\ (!d. 0 < d ==> ~ODD(m DIV 2 EXP d)) <=> m = 1`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `2 <= m` ASSUME_TAC THENL
     [UNDISCH_TAC `ODD m` THEN UNDISCH_TAC `~(m = 1)` THEN
      REWRITE_TAC[ARITH_RULE `2 <= m <=> ~(m = 0) /\ ~(m = 1)`] THEN
      MESON_TAC[ODD];
      ALL_TAC] THEN
    SUBGOAL_THEN `2 <= bitsize m` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT; ARITH_RULE `n < 2 <=> n <= 1`; BITSIZE_LE] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `bitsize m - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `m DIV 2 EXP (bitsize m - 1) = 1`
     (fun th -> REWRITE_TAC[th; ODD; ARITH]) THEN
    SIMP_TAC[DIV_EQ_RANGE; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `(1 + 1) * x = 2 * x`] THEN
    ASM_SIMP_TAC[BITSIZE_REV; ARITH_RULE `2 <= m ==> ~(m = 0)`] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    SUBGOAL_THEN `SUC(bitsize m - 1) = bitsize m` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[BITSIZE]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `1 DIV 2 EXP d = 0`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; ARITH])) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP 1` THEN
    REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;

let ZSTD_END_BITSIZE = prove
 (`!(st:byte list) r.
        zstd_end st r <=>
        ~(st = []) /\ 8 * (LENGTH st - 1) <= r /\
        bitsize(num_of_bytelist st) = r + 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zstd_end; ZSTD_BIT_NUM] THEN
  ABBREV_TAC `x = num_of_bytelist(st:byte list)` THEN
  SUBGOAL_THEN
   `(ODD(x DIV 2 EXP r) /\ (!i. r < i ==> ~ODD(x DIV 2 EXP i))) <=>
    x DIV 2 EXP r = 1`
  (fun th -> REWRITE_TAC[GSYM CONJ_ASSOC; th]) THENL
   [REWRITE_TAC[GSYM ODD_DIV_TOP; DIV_DIV; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r + i:num`) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i - r:num`) THEN
      ASM_SIMP_TAC[ARITH_RULE `r < i ==> 0 < i - r /\ r + i - r = i`]];
    ALL_TAC] THEN
  SIMP_TAC[DIV_EQ_RANGE; EXP_EQ_0; ARITH_EQ; BITSIZE_UNIQUE_EQ] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; EXP_ADD; EXP_1; MULT_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `(1 + 1) * x = x * 2`] THEN
  REWRITE_TAC[ARITH_RULE `x * 2 <= 2 * y <=> x <= y`] THEN
  CONV_TAC TAUT);;

let ZSTD_END_LAST = prove
 (`!(st:byte list) r.
        ~(st = [])
        ==> (zstd_end st r <=>
             ~(val(EL (LENGTH st - 1) st) = 0) /\
             r = 8 * (LENGTH st - 1) +
                 bitsize(val(EL (LENGTH st - 1) st)) - 1)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ZSTD_END_BITSIZE] THEN
  MP_TAC(ISPEC `st:byte list` APPEND_BUTLAST_LAST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SPEC_TAC(`LAST(st:byte list)`,`b:byte`) THEN
  SPEC_TAC(`BUTLAST(st:byte list)`,`l:byte list`) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES; SUC_SUB1;
              NUM_OF_BYTELIST_APPEND] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  REWRITE_TAC[num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(ISPEC `l:byte list` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT] THEN
  ASM_CASES_TAC `val(b:byte) = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_TAC THENL
   [REWRITE_TAC[DE_MORGAN_THM] THEN
    MP_TAC(SPECL [`num_of_bytelist(l:byte list)`; `8 * LENGTH(l:byte list)`]
       BITSIZE_LE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_SIMP_TAC[BITSIZE_MULT_ADD] THEN
    MP_TAC(SPEC `val(b:byte)` BITSIZE_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

let ZSTD_END_UNIQUE = prove
 (`!(st:byte list) r r'. zstd_end st r /\ zstd_end st r' ==> r = r'`,
  REWRITE_TAC[ZSTD_END_BITSIZE] THEN ARITH_TAC);;

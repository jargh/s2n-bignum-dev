(* ========================================================================= *)
(* Reformulating overlap and containment in more straightforward ways.       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Add a word-level equivalent of contained.                                 *)
(* ------------------------------------------------------------------------- *)

let contained = new_definition
 `contained (base1:N word,len1) (base2:N word,len2) <=>
        contained_modulo (2 EXP dimindex(:N))
                         (val base1,len1) (val base2,len2)`;;

(* ------------------------------------------------------------------------- *)
(* Some elementary lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONTAINED = prove
 (`!(base1:N word) base2 len1 len2.
        contained (base1,len1) (base2,len2) <=>
        !i. i < len1
            ==> ?j. j < len2 /\
                    word_add base1 (word i) = word_add base2 (word j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contained; contained_modulo] THEN
  REWRITE_TAC[GSYM WORD_EQ; WORD_ADD; WORD_VAL]);;

let NONOVERLAPPING = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        ~(?i j. i < len1 /\ j < len2 /\
                word_add base1 (word i) = word_add base2 (word j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping; nonoverlapping_modulo] THEN
  REWRITE_TAC[GSYM WORD_EQ; WORD_ADD; WORD_VAL]);;

let CONTAINED_MODULO = prove
 (`!base1 base2 len1 len2.
      contained_modulo (2 EXP dimindex(:N)) (base1,len1) (base2,len2) <=>
      contained(word base1:N word,len1) (word base2:N word,len2)`,
  REWRITE_TAC[contained; contained_modulo] THEN
  REWRITE_TAC[VAL_WORD; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[]);;

let NONOVERLAPPING_MODULO = prove
 (`!base1 base2 len1 len2.
      nonoverlapping_modulo (2 EXP dimindex(:N)) (base1,len1) (base2,len2) <=>
      nonoverlapping(word base1:N word,len1) (word base2:N word,len2)`,
  REWRITE_TAC[nonoverlapping; nonoverlapping_modulo] THEN
  REWRITE_TAC[VAL_WORD; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[]);;

let NONOVERLAPPING_SYM = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        nonoverlapping (base2,len2) (base1,len1)`,
  REWRITE_TAC[nonoverlapping; NONOVERLAPPING_MODULO_SYM]);;

let NONOVERLAPPING_TRIVIAL = prove
 (`!(base1:N word) base2 len1 len2.
        len1 = 0 \/ len2 = 0
         ==> nonoverlapping (base1,len1) (base2,len2)`,
  SIMP_TAC[nonoverlapping; NONOVERLAPPING_MODULO_TRIVIAL]);;

let CONTAINED_TRIVIAL = prove
 (`!(base1:N word) base2 len2. contained (base1,0) (base2,len2)`,
  REWRITE_TAC[contained; CONTAINED_MODULO_TRIVIAL]);;

let NONOVERLAPPING_SUBREGIONS = prove
 (`!(base1:N word) len1 base2 len2 base1' len1' base2' len2'.
        nonoverlapping (base1,len1) (base2,len2) /\
        contained (base1',len1') (base1,len1) /\
        contained (base2',len2') (base2,len2)
        ==> nonoverlapping (base1',len1') (base2',len2')`,
  REWRITE_TAC[nonoverlapping; contained; NONOVERLAPPING_MODULO_SUBREGIONS]);;

(* ------------------------------------------------------------------------- *)
(* Relatively simple quantifier-free equivalents.                            *)
(* ------------------------------------------------------------------------- *)

let exists_mod_lemma = prove
 (`!n P len. ~(n = 0)
             ==> ((?i. i < len /\ P(i MOD n)) <=>
                  (?i. i < n /\ i < len /\ P i))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i MOD n` THEN ASM_SIMP_TAC[MOD_LT; MOD_LT_EQ] THEN
  ASM_MESON_TAC[MOD_LE; LET_TRANS]);;

let CONTAINED_QFREE = prove
 (`!(base1:N word) base2 len1 len2.
        contained (base1,len1) (base2,len2) <=>
        0 < len1 /\ len2 < 2 EXP dimindex(:N)
        ==> val(word_sub base1 base2) + len1 <= len2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTAINED] THEN
  REWRITE_TAC[WORD_RULE
   `word_add b x:N word = word_add c y <=> word_sub y x = word_sub b c`] THEN
  SPEC_TAC(`word_sub base1 base2:N word`,`d:N word`) THEN GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[CONJUNCT1 LT; LE_1] THEN
  REWRITE_TAC[WORD_RULE `word_sub a b:N word = c <=> a = word_add c b`] THEN
  REWRITE_TAC[WORD_VAL_GALOIS] THEN
  MP_TAC(SPEC `2 EXP dimindex(:N)` exists_mod_lemma) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[UNWIND_THM2; VAL_BOUND; ARITH_RULE
     `j:num < a /\ j < b /\ j = c <=> j = c /\ c < a /\ c < b`] THEN
  ASM_CASES_TAC `len2 < 2 EXP dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[VAL_BOUND; NOT_LT; LTE_TRANS]] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD] THEN CONV_TAC MOD_DOWN_CONV THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC
     `MIN len1 (2 EXP dimindex(:N) - val(d:N word)) - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o lhand o snd) THEN
    MP_TAC(ISPEC `d:N word` VAL_BOUND) THEN ASM_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN ASM_ARITH_TAC]);;

let NONOVERLAPPING_QFREE = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        0 < len1 /\ 0 < len2
        ==> len2 <= val(word_sub base1 base2) /\
            val(word_sub base1 base2) + len1 <= 2 EXP dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING] THEN
  REWRITE_TAC[WORD_RULE
   `word_add b x:N word = word_add c y <=> word_sub y x = word_sub b c`] THEN
  SPEC_TAC(`word_sub base1 base2:N word`,`d:N word`) THEN GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[CONJUNCT1 LT; LE_1] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_SIMP_TAC[CONJUNCT1 LT; LE_1] THEN
  REWRITE_TAC[WORD_RULE `word_sub a b:N word = c <=> a = word_add c b`] THEN
  REWRITE_TAC[WORD_VAL_GALOIS; RIGHT_EXISTS_AND_THM] THEN
  MP_TAC(SPEC `2 EXP dimindex(:N)` exists_mod_lemma) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[UNWIND_THM2; VAL_BOUND; ARITH_RULE
     `j:num < a /\ j < b /\ j = c <=> j = c /\ c < a /\ c < b`] THEN
  ASM_CASES_TAC `len2 < 2 EXP dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[VAL_BOUND; NOT_LT; LE_1; LTE_TRANS]] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM NOT_LT; GSYM DE_MORGAN_THM] THEN
  AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC `val(d:N word) + i < 2 EXP dimindex(:N)` THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC;
    STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_SIMP_TAC[ADD_CLAUSES; VAL_MOD_REFL; LE_1];
      EXISTS_TAC `2 EXP dimindex(:N) - val(d:N word)` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[VAL_BOUND; ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
      ASM_SIMP_TAC[MOD_REFL; LE_1]]]);;

let NONOVERLAPPING_QFREE' = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        0 < len1 /\ 0 < len2
        ==> len2 <= val(word_sub base1 base2) /\
            len1 <= val(word_sub base2 base1)`,
  REWRITE_TAC[NONOVERLAPPING_QFREE] THEN WORD_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One-way versions for practical use with base + iword offset.              *)
(* ------------------------------------------------------------------------- *)

let CONTAINED_SIMPLE = prove
 (`!(base:N word) off1 off2 len1 len2.
        (0 < len1 ==> &0 <= off1 - off2 /\ (off1 - off2) + &len1 <= &len2)
        ==> contained (word_add base (iword off1),len1)
                      (word_add base (iword off2),len2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[CONTAINED_TRIVIAL; LE_1] THEN
  REWRITE_TAC[CONTAINED_QFREE; WORD_RULE
  `word_sub (word_add b (iword x)) (word_add b (iword y)) = iword(x - y)`] THEN
  SPEC_TAC(`off1 - off2:int`,`y:int`) THEN
  REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE
   `val(word n:N word) <= n /\ n + l1 <= l2
    ==> val(word n:N word) + l1 <= l2`) THEN
  SIMP_TAC[VAL_WORD_LE; LE_REFL] THEN ASM_ARITH_TAC);;

let CONTAINED_SIMPLE_64 = INST_TYPE [`:64`,`:N`] CONTAINED_SIMPLE;;

let NONOVERLAPPING_SIMPLE_LEFT = prove
 (`!(base:N word) off1 off2 len1 len2.
      (0 < len1 /\ 0 < len2
       ==> &len2 <= off1 - off2 /\ (off1 - off2) + &len1 <= &2 pow dimindex(:N))
      ==> nonoverlapping (word_add base (iword off1),len1)
                         (word_add base (iword off2),len2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[NONOVERLAPPING_TRIVIAL; LE_1] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_SIMP_TAC[NONOVERLAPPING_TRIVIAL; LE_1] THEN
  REWRITE_TAC[NONOVERLAPPING_QFREE; WORD_RULE
  `word_sub (word_add b (iword x)) (word_add b (iword y)) = iword(x - y)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MESON[INT_POS; INT_LE_TRANS]
    `&len:int <= y <=> &0 <= y /\ &len <= y`] THEN
  SPEC_TAC(`off1 - off2:int`,`y:int`) THEN
  REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `val(word n:N word) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  INT_ARITH_TAC);;

let NONOVERLAPPING_SIMPLE = prove
 (`!(base:N word) off1 off2 len1 len2.
       (0 < len1 /\ 0 < len2
        ==> &len2 <= off1 - off2 /\
            (off1 - off2) + &len1 <= &2 pow dimindex(:N) \/
            &len1 <= off2 - off1 /\
            (off2 - off1) + &len2 <= &2 pow dimindex(:N))
        ==> nonoverlapping (word_add base (iword off1),len1)
                           (word_add base (iword off2),len2)`,
  MESON_TAC[NONOVERLAPPING_SIMPLE_LEFT; NONOVERLAPPING_SYM]);;

let NONOVERLAPPING_SIMPLE_64 =
  CONV_RULE INT_REDUCE_CONV
   (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] NONOVERLAPPING_SIMPLE));;

(* ------------------------------------------------------------------------- *)
(* Eliminate nonoverlapping_modulo in favour of nonoverlapping.              *)
(* Evetually we'll restructure all the proofs to keep this anyway.           *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAP_REVERT_CONV =
  let pth = prove
   (`!(base1:int64) base2 len1 len2.
        nonoverlapping_modulo (2 EXP 64) (val base1,len1) (val base2,len2) <=>
        nonoverlapping (base1,len1) (base2,len2)`,
     REWRITE_TAC[nonoverlapping; DIMINDEX_64])
  and qth = prove
   (`!base1 base2 len1 len2.
        nonoverlapping_modulo (2 EXP 64) (base1,len1) (base2,len2) <=>
        nonoverlapping (word base1:int64,len1) (word base2:int64,len2)`,
    REWRITE_TAC[nonoverlapping; NONOVERLAPPING_CLAUSES; DIMINDEX_64]) in
  GEN_REWRITE_CONV I [pth] ORELSEC
  (GEN_REWRITE_CONV I [qth] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* Normalizing as word_add base (iword x), even by introduceing iword(&0).   *)
(* ------------------------------------------------------------------------- *)

let INORMALIZE_RELATIVE_ADDRESS_CONV =
  let trivconv = GEN_REWRITE_CONV I
    [WORD_RULE `z:int64 = word_add z (iword(&0))`]
  and initconv =
   GEN_REWRITE_CONV TOP_DEPTH_CONV
     [WORD_ADD; IWORD_INT_ADD; WORD_VAL; GSYM WORD_ADD_ASSOC;
      WORD_RULE `word_sub x y:int64 = word_add x (word_neg y)`]
  and mainconv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [GSYM IWORD_INT_ADD; WORD_IWORD;
      GSYM IWORD_INT_NEG; GSYM IWORD_INT_MUL] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM INT_OF_NUM_CLAUSES] in
  let postconv tm =
    match tm with
      Var(_,_)
    | Comb(Const("word",_),_) -> trivconv tm
    | Comb(Comb(Const("word_add",_),_),_) -> RAND_CONV mainconv tm
    | _ -> mainconv tm in
  initconv THENC postconv;;

(* ------------------------------------------------------------------------- *)
(* Derive nonoverlapping-justifying reductions to arithmetic from a          *)
(* given context of nonoverlapping hypotheses, if any. In all cases          *)
(* add a theorem for the case where both regions have the same base.         *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_DRIVERS =
  let pth = prove
   (`!(base1:int64) base2 off1 off2 len1 len2 off1' off2' len1' len2'.
          nonoverlapping (word_add base1 (iword off1),len1)
                         (word_add base2 (iword off2),len2)
          ==> (0 < len1'
               ==> &0 <= off1' - off1 /\ (off1' - off1) + &len1' <= &len1) /\
              (0 < len2'
               ==> &0 <= off2' - off2 /\ (off2' - off2) + &len2' <= &len2)
              ==> nonoverlapping (word_add base1 (iword off1'),len1')
                                 (word_add base2 (iword off2'),len2')`,
    REPEAT GEN_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r ==> s <=> q /\ r ==> p ==> s`]
          NONOVERLAPPING_SUBREGIONS) THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTAINED_SIMPLE_64 THEN
    ASM_REWRITE_TAC[]) in
  let pth' = prove
   (`!(base1:int64) base2 off1 off2 len1 len2 off1' off2' len1' len2'.
          word_add base1 (iword off1) = word_add base2 (iword off2) \/
          nonoverlapping (word_add base1 (iword off1),len1)
                         (word_add base2 (iword off2),len2)
          ==> (0 < len1'
               ==> &0 <= off1' - off1 /\ (off1' - off1) + &len1' <= &len1) /\
              (0 < len2'
               ==> &0 <= off2' - off2 /\ (off2' - off2) + &len2' <= &len2) /\
              (0 < len1' /\ 0 < len2'
               ==> &len2' <= off1' - (off1 - off2 + off2') /\
                    off1' - (off1 - off2 + off2') + &len1'
                    <= &18446744073709551616 \/
                   &len1' <= (off1 - off2 + off2') - off1' /\
                   (off1 - off2 + off2') - off1' + &len2'
                   <= &18446744073709551616)
              ==> nonoverlapping (word_add base1 (iword off1'),len1')
                                 (word_add base2 (iword off2'),len2')`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[pth]] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (WORD_RULE
     `word_add b1 (iword off1) = word_add b2 (iword off2)
      ==> b2 = word_add b1 (iword(off1 - off2))`)) THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add b (iword x)) (iword y) =
      word_add b (iword(x + y))`] THEN
    MATCH_MP_TAC NONOVERLAPPING_SIMPLE_64 THEN ASM_REWRITE_TAC[]) in
  let pat1 =
   can (term_match [] `nonoverlapping (a:int64,m) (b,n)`)
  and pat2 =
   can (term_match [] `a = b \/ nonoverlapping (a:int64,m) (b,n)`)
  and rule1 = MATCH_MP pth
  and rule2 = MATCH_MP pth'
  and postrule =
    GEN_REWRITE_RULE TOP_DEPTH_CONV
     [GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD;
      INT_SUB_RZERO; INT_ADD_LID; INT_ADD_RID] in
  let OVERLAPPING_DRIVER th =
    let th1 = CONV_RULE (ONCE_DEPTH_CONV NONOVERLAP_REVERT_CONV) th in
    let tm = concl th1 in
    let th2 =
      if pat1 tm then
          rule1 (CONV_RULE
           (BINOP_CONV (LAND_CONV INORMALIZE_RELATIVE_ADDRESS_CONV)) th1)
      else if pat2 tm then
          rule2 (CONV_RULE
           (BINOP2_CONV (BINOP_CONV INORMALIZE_RELATIVE_ADDRESS_CONV)
              (BINOP_CONV (LAND_CONV INORMALIZE_RELATIVE_ADDRESS_CONV))) th1)
      else failwith "OVERLAPPING_DRIVER" in
    postrule th2 in
  fun thl ->
    let ths = mapfilter OVERLAPPING_DRIVER thl in
    let ths' = map (PURE_ONCE_REWRITE_RULE[NONOVERLAPPING_SYM]) ths in
    NONOVERLAPPING_SIMPLE_64 :: ths @ ths';;

(* ------------------------------------------------------------------------- *)
(* Simple conversion to integer versus natural number properties.            *)
(* ------------------------------------------------------------------------- *)

let INT_OF_NUM_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [DIMINDEX_64; NUM_REDUCE_CONV `2 EXP 64`;
    ARITH_RULE `~(n = 0) <=> 1 <= n`] THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [LT_MULT; ARITH_RULE `c:num < a - b <=> c + b < a`] THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_SUC;
    ARITH_RULE `!m n. &(m - n):int = max (&0) (&m - &n)`;
    ARITH_RULE `!n. &(PRE n):int = max (&0) (&n - &1)`;
    GSYM INT_OF_NUM_CLAUSES] THENC
  NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Filter away assumptions other than natural number predictes and any       *)
(* involving various other constructs, notably the "read" function. The idea *)
(* is to keep only those that might be involved in address calculation. When *)
(* a theorem passes the filter, normalize arithmetic to be on Z not N.       *)
(* ------------------------------------------------------------------------- *)

let FILTER_CANONIZE_ASSUMPTIONS =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "word"] in
  let avoiderp tm =
    match tm with
      Comb(Comb(Const("DIV",_),_),m) -> not(is_numeral m)
    | Comb(Comb(Const("MOD",_),_),m) -> not(is_numeral m)
    | Comb(Comb(Const("EXP",_),_),m) -> not(frees m = [])
    | Const(n,_) -> mem n avoiders
    | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop(rand tm))) &&
    not(can (find_term avoiderp) tm) in
  let FILTER_CANONIZE_ASSUMPTION th =
    if filtered(concl th) then CONV_RULE INT_OF_NUM_CONV th
    else failwith "FILTER_CANONIZE_ASSUMPTION" in
  mapfilter FILTER_CANONIZE_ASSUMPTION;;

let FILTER_CANONIZE_TAC thl =
  let thl' = FILTER_CANONIZE_ASSUMPTIONS thl in
  if thl' = [] then ALL_TAC else ASSUME_TAC(end_itlist CONJ thl');;

(* ------------------------------------------------------------------------- *)
(* Custom arithmetic rule/tactic targeted at the sideconditions arising in   *)
(* nonoverlapping reasoning. As much as possible, exploit information that   *)
(* the regions to be analyzed are nonempty, e.g. performing N -> Z mapping.  *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_INT_POS_RULE =
  let rule_mul = PART_MATCH rand INT_LE_MUL
  and rule_add = PART_MATCH rand INT_LE_ADD
  and rule_max = PART_MATCH I (INT_ARITH `&0:int <= max (&0) x`)
  and rule_num = PART_MATCH I INT_POS in
  let rec rule tm =
    try rule_max tm with Failure _ ->
    try rule_num tm with Failure _ ->
    let ith = (try rule_mul tm with Failure _ -> rule_add tm) in
    let ltm,rtm = dest_conj(lhand(concl ith)) in
    MP ith (CONJ (rule ltm) (rule rtm)) in
  rule;;

let CONTEXT_INT_ARITH ths tm =
  try SIMPLE_INT_POS_RULE tm with Failure _ ->
  try INT_ARITH tm with Failure _ ->
  if ths = [] then failwith "CONTEXT_INT_ARITH_RULE" else
  let tm' = itlist (curry mk_imp o concl) ths tm in
  rev_itlist (C MP) ths (INT_ARITH tm');;

let pth_mul = prove
 (`0 < a * b <=> &(a * b):int = &a * &b /\ 0 < a /\ 0 < b`,
  REWRITE_TAC[INT_OF_NUM_CLAUSES; LT_MULT])
and pth_sub = prove
 (`c < a - b <=> &(a - b):int = &a - &b /\ c + b < a`,
  ARITH_TAC);;

let rule_mul = GEN_REWRITE_RULE I [pth_mul]
and rule_sub = GEN_REWRITE_RULE I [pth_sub];;

let rec DECOMP_LT (dun,eqs,todo) =
  match todo with
    [] -> (map (CONV_RULE INT_OF_NUM_CONV) dun,eqs)
  | th::oths ->
     (try let th' = rule_mul th in
          let eth,rth = CONJ_PAIR th' in
          let th1,th2 = CONJ_PAIR rth in
          DECOMP_LT (dun,eth::eqs,th1::th2::oths)
      with Failure _ -> try
          let th' = rule_sub th in
          let eth,rth = CONJ_PAIR th' in
          DECOMP_LT (dun,eth::eqs,rth::oths)
      with Failure _ -> DECOMP_LT (th::dun,eqs,oths));;

let rec CORE_SPECIAL_ARITH_RULE ths tm =
  if is_conj tm then
    CONJ (CORE_SPECIAL_ARITH_RULE ths (lhand tm))
         (CORE_SPECIAL_ARITH_RULE ths (rand tm))
  else CONTEXT_INT_ARITH ths tm;;

let rec SPECIAL_ARITH_RULE ths tm =
  if is_conj tm then
    CONJ (SPECIAL_ARITH_RULE ths (lhand tm))
         (SPECIAL_ARITH_RULE ths (rand tm))
  else if is_imp tm then
    let atm,btm = dest_imp tm in
    let (aths,eqs) = DECOMP_LT ([],[],[ASSUME atm]) in
    let eth = (SUBS_CONV eqs THENC INT_OF_NUM_CONV) btm in
    let th = CORE_SPECIAL_ARITH_RULE (aths@ths) (rand(concl eth)) in
    DISCH atm (EQ_MP (SYM eth) th)
  else
    let eth = INT_OF_NUM_CONV tm in
    let th = CORE_SPECIAL_ARITH_RULE ths (rand(concl eth)) in
    EQ_MP (SYM eth) th;;

let SPECIAL_ARITH_TAC (asl,w) =
  ACCEPT_TAC(SPECIAL_ARITH_RULE (map snd asl) w) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Overall nonoverlapping rule whose first argument is a pair, the           *)
(* contextual lemmas and the current arithmetical assumptions.               *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_RULE (drivers,ariths) =
  let convs = map (PART_MATCH rand) drivers
  and arule = SPECIAL_ARITH_RULE ariths in
  let match_arith_rule tm =
    tryfind (fun cfn -> let ith = cfn tm in MP ith (arule(lhand(concl ith))))
            convs in
  let rec rule tm =
    if is_conj tm then CONJ (rule(lhand tm)) (rule(rand tm)) else
    let eth =
      (TRY_CONV NONOVERLAP_REVERT_CONV THENC
       BINOP_CONV (LAND_CONV INORMALIZE_RELATIVE_ADDRESS_CONV)) tm in
    EQ_MP (SYM eth) (match_arith_rule(rand(concl eth))) in
  rule;;

(* ------------------------------------------------------------------------- *)
(* We renamed the previous ORTHOGONAL_COMPONENTS_RULE to                     *)
(* ORTHOGONAL_COMPONENTS_RULE2 (it's a different interface and is            *)
(* not using assumptions)                                                    *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_COMPONENTS_RULE =
  let pth,qth = (CONJ_PAIR o prove)
   (`(nonoverlapping (a1,l1) (a2,l2)
      ==> orthogonal_components (bytes(a1,l1)) (bytes(a2,l2))) /\
     (orthogonal_components (bytes(a,32)) c
      ==> orthogonal_components (bytes256 a) c) /\
     (orthogonal_components d (bytes(a,32))
      ==> orthogonal_components d (bytes256 a)) /\
     (orthogonal_components (bytes(a,16)) c
      ==> orthogonal_components (bytes128 a) c) /\
     (orthogonal_components d (bytes(a,16))
      ==> orthogonal_components d (bytes128 a)) /\
     (orthogonal_components (bytes(a,8)) c
      ==> orthogonal_components (bytes64 a) c) /\
     (orthogonal_components d (bytes(a,8))
      ==> orthogonal_components d (bytes64 a)) /\
     (orthogonal_components (bytes(a,1)) c
      ==> orthogonal_components (bytes8 a) c) /\
     (orthogonal_components d (bytes(a,1))
      ==> orthogonal_components d (bytes8 a)) /\
     (orthogonal_components (bytes(a,2)) c
      ==> orthogonal_components (bytes16 a) c) /\
     (orthogonal_components d (bytes(a,2))
      ==> orthogonal_components d (bytes16 a)) /\
     (orthogonal_components (bytes(a,4)) c
      ==> orthogonal_components (bytes32 a) c) /\
     (orthogonal_components d (bytes(a,4))
      ==> orthogonal_components d (bytes32 a)) /\
     (orthogonal_components (bytes(a,k)) c
      ==> orthogonal_components (bytelist(a,k)) c) /\
     (orthogonal_components d (bytes(a,k))
      ==> orthogonal_components d (bytelist(a,k)))`,
    CONJ_TAC THENL
     [REWRITE_TAC[NONOVERLAPPING_MODULO; ORTHOGONAL_COMPONENTS_BYTES] THEN
      REWRITE_TAC[WORD_VAL];
      REWRITE_TAC[bytes256; bytes128; bytes64; bytes32; bytes16; bytes8;
                  bytelist; COMPONENT_COMPOSE_ASSOC] THEN
      REWRITE_TAC[ORTHOGONAL_COMPONENTS_SUB_LEFT;
                  ORTHOGONAL_COMPONENTS_SUB_RIGHT]]) in
  let baseconv = PART_MATCH rand pth
  and stepconvs = map (PART_MATCH rand) (CONJUNCTS qth)
  and breakconv = PART_MATCH (rand o rand)
   (REWRITE_RULE[IMP_CONJ] ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT)
  and redconv = BINOP_CONV(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) in
  fun cxt ->
    let novrule = NONOVERLAPPING_RULE cxt in
    let mainrule tm =
      let th = baseconv tm in
      let ith = CONV_RULE (LAND_CONV redconv) th in
      let rth = novrule (lhand(concl ith)) in
      MP ith rth in
    let rec midrule tm =
      try let ith = tryfind (fun f -> f tm) stepconvs in
          let rth = midrule(lhand(concl ith)) in
          MP ith rth
      with Failure _ -> mainrule tm in
    let rec toprule tm =
      try let th = breakconv tm in
          let ith = MP th (VALID_COMPONENT_CONV(lhand(concl th))) in
          let rth = toprule(lhand(concl ith)) in
          MP ith rth
      with Failure _ -> midrule tm in
    fun tm -> try ORTHOGONAL_COMPONENTS_CONV tm with Failure _ -> toprule tm;;

(* ------------------------------------------------------------------------- *)
(* Again, set up regression testing versus the old tactic. Shortcut the      *)
(* "easy" cases without preprocessing the context, or it's too slow.         *)
(* ------------------------------------------------------------------------- *)

let regression_list = ref ([]:goal list);;

let OLD_ORTHOGONAL_COMPONENTS_TAC = ORTHOGONAL_COMPONENTS_TAC;;

let TEST_ORTHOGONAL_COMPONENTS_TAC =
  CONV_TAC ORTHOGONAL_COMPONENTS_CONV ORELSE
  (fun  gl ->
   let thl = map snd (fst gl) and w = snd gl in
   let drivers = NONOVERLAPPING_DRIVERS thl
   and ariths = FILTER_CANONIZE_ASSUMPTIONS thl in
   let th = ORTHOGONAL_COMPONENTS_RULE(drivers,ariths) w in
   ACCEPT_TAC th gl);;

let ORTHOGONAL_COMPONENTS_TAC =
  TEST_ORTHOGONAL_COMPONENTS_TAC ORELSE
  (fun gl -> let res = OLD_ORTHOGONAL_COMPONENTS_TAC gl in
             let _ = (regression_list := gl::(!regression_list)) in
             let _ = Format.print_string
               "*** ORTHOGONAL_COMPONENTS REGRESSION ***" in
             let _ = Format.print_newline() in
             let _ = print_goal gl in
             res);;

(* ------------------------------------------------------------------------- *)
(* New code for applying existing assignment.                                *)
(* ------------------------------------------------------------------------- *)

let READ_OVER_WRITE_ORTHOGONAL_CONV =
  let pth = prove
   (`orthogonal_components c d ==> read c (write d y s) = read c s`,
    SIMP_TAC[orthogonal_components]) in
  let rwconv = PART_MATCH (lhand o rand) pth
  and imprule = MATCH_MP
   (TAUT `(p ==> (q <=> q')) ==> (p ==> q <=> p ==> q')`)
  and conjrule = MATCH_MP
   (TAUT `(p ==> (q <=> q')) ==> (p /\ q <=> p /\ q')`) in
  let singleconv cxt tm =
    let th = rwconv tm in
    MP th (ORTHOGONAL_COMPONENTS_RULE cxt (lhand(concl th))) in
  let rec repconv cxt tm =
    match tm with
      Comb(Comb(Const("read",_),_),
           Comb(Comb(Comb(Const("write",_),_),_),_)) ->
      let th = singleconv cxt tm in
      CONV_RULE (RAND_CONV(repconv cxt)) th
    | _ -> REFL tm in
  fun (drivers,ariths) ->
    let rec conv ths tm =
      match tm with
        Comb(Comb(Const("read",_),_),
             Comb(Comb(Comb(Const("write",_),_),_),_)) ->
          repconv (drivers,ths) tm
      | Abs(x,p) ->
          let x' = genvar(type_of x) in
          let p' = vsubst[x',x] p in
          CONV_RULE (BINOP_CONV(ALPHA_CONV x)) (ABS x' (conv ths p'))
      | Comb(Comb(Const("/\\",_) as op,l),r) ->
         (try let lth = conv ths l in
              try let rth = conv ths r in
                  MK_COMB(AP_TERM op lth,rth)
              with Unchanged -> AP_THM (AP_TERM op lth) r
          with Unchanged ->
              let ths' = ths @
                FILTER_CANONIZE_ASSUMPTIONS(CONJUNCTS(ASSUME l)) in
              let rth = DISCH l (conv ths' r) in
              conjrule rth)
      | Comb(Comb(Const("==>",_) as op,l),r) ->
         (try let lth = conv ths l in
              try let rth = conv ths r in
                  MK_COMB(AP_TERM op lth,rth)
              with Unchanged -> AP_THM (AP_TERM op lth) r
          with Unchanged ->
              let ths' = ths @
                FILTER_CANONIZE_ASSUMPTIONS(CONJUNCTS(ASSUME l)) in
              let rth = DISCH l (conv ths' r) in
              imprule rth)
      | Comb(l,r) ->
         (try let lth = conv ths l in
              try let rth = conv ths r in MK_COMB(lth,rth)
              with Unchanged -> AP_THM lth r
          with Unchanged ->
              AP_TERM l (conv ths r))
      | _ -> raise Unchanged in
  fun tm -> try conv ariths tm with Unchanged -> REFL tm;;

(* ------------------------------------------------------------------------- *)
(* New/generalized rule to apply a state update theorem                      *)
(* uth |- (write c1 t1) (... (write cn tn) s) = s'                           *)
(* to a theorem involving terms "read d s"                                   *)
(* and attempts to derive a corresponding theorem with s'.                   *)
(* Fails if the exact same theorem doesn't hold.                             *)
(* ------------------------------------------------------------------------- *)

let GEN_STATE_UPDATE_RULE cxt uth th =
  let utm,s' = dest_eq(concl uth)
  and tm = concl th in
  let s = repeat rand utm in
  if not(free_in s tm) then failwith "STATE_UPDATE_RULE" else
  let th0 = SUBS_CONV[SYM uth] (vsubst [s',s] (concl th)) in
  let th1 = CONV_RULE(RAND_CONV(READ_OVER_WRITE_ORTHOGONAL_CONV cxt)) th0 in
  EQ_MP (SYM th1) th;;

let ASSUMPTION_STATE_UPDATE_TAC gl =
  (DISCH_THEN(fun uth ->
   let thl = map snd (fst gl) in
   let drivers = NONOVERLAPPING_DRIVERS thl
   and ariths = FILTER_CANONIZE_ASSUMPTIONS thl in
   let update_rule = GEN_STATE_UPDATE_RULE (drivers,ariths) uth in
   let newthms = mapfilter update_rule thl in
   MP_TAC uth THEN MAP_EVERY ASSUME_TAC newthms)) gl;;

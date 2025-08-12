needs "arm/proofs/base.ml";;

prioritize_num();;

parse_as_infix ("++", (13, "right"));;
override_interface("++", `APPEND`);;

overload_interface("+",`word_add:N word->N word->N word`);;

(* ===== definition ===== *)

let drop = define
  `drop (n : num) (l : A list) : A list =
    SUB_LIST (n, LENGTH l - n) l`;;

let take = define
  `take (n : num) (l : A list) : A list =
    SUB_LIST (0, n) l`;;

let ceil_div = define
  `ceil_div (m : num) (n : num) = (m + n - 1) DIV n`;;

let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) s =
    ! i. i < LENGTH m ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

(* ===== thm ===== *)

let DOUBLE_INCL = prove
  (`! x y. (x <=> y) <=> ((x ==> y) /\ (y ==> x))`,
  ITAUT_TAC);;

let FORALL_LT_SUC = prove
  (`!P n. (!i. i < n + 1 ==> P i) <=> (!i. i < n ==> P i) /\ P n`,
  REWRITE_TAC[GSYM ADD1] THEN MESON_TAC[LT]);;

let MOD_0_ADD_DIV = prove
  (`!x y z.
    ~(z = 0) /\ x MOD z = 0 ==>
    (x + y) DIV z = x DIV z + y DIV z`,
  REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`x:num`; `y:num`; `z:num`] (GSYM ADD_DIV_MOD_SIMP_LEMMA)) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [ADD; ADD_SYM]);;

let DIV_MULT_LE = prove
  (`!x y. ~(y = 0) ==> x DIV y * y <= x`,
  REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`x:num`; `y:num`] DIVISION) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    REWRITE_TAC [LE_ADD]);;

let MOD_0_DIV_MULT = prove
  (`!x y. x MOD y = 0 ==> x DIV y * y = x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun th -> REWRITE_TAC
    [REWRITE_RULE [GSYM DIVIDES_MOD; DIVIDES_DIV_MULT] th]));;

let SUB_MOD_MOD = prove
  (`!x y. ~(y = 0) ==> (x - x MOD y) MOD y = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x:num`; `y:num`] DIVISION) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [th]) THEN
  REWRITE_TAC [ADD_SUB] THEN
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  REWRITE_TAC [MOD_MULT]);;

let ADD_MODULUS_MOD = prove
  (`!x y. (x + y) MOD y = x MOD y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x + y) MOD y = (x + y MOD y) MOD y` MP_TAC THENL
  [ REWRITE_TAC [ADD_MOD_MOD_REFL]; ALL_TAC ] THEN
  REWRITE_TAC [MOD_REFL; ADD_0]);;

let ADD_MOD_LT_ADD_DIV = prove
  (`!x y z. x MOD z + y < z ==> (x + y) DIV z = x DIV z`,
  REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`x:num`; `z:num`] DIVISION) THEN
    ANTS_TAC THENL
    [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [th]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    IMP_REWRITE_TAC [SPEC `x DIV z * z` MOD_0_ADD_DIV] THEN
    SUBGOAL_THEN `~(z = 0)` MP_TAC THENL
    [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
    DISCH_THEN (ASSUME_TAC o REWRITE_RULE [GSYM MOD_LT_EQ]) THEN
    ASM_SIMP_TAC [DIV_LT] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [MOD_MULT] THEN
    SIMPLE_ARITH_TAC);;

let LT_CEIL_DIV_MUL = prove
  (`!x y. ~(y=0) ==> x <= ceil_div x y * y`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [ceil_div] THEN
    MATCH_MP_TAC (ARITH_RULE `!x y z. SUC y = z ==> x <= (x + y) DIV z * z`) THEN
    SIMPLE_ARITH_TAC);;

let CONS_REPLICATE_REPLICATE_APPEND = prove
  (`!n x:A. CONS x (REPLICATE n x) = REPLICATE n x ++ [x]`,
  INDUCT_TAC THENL
    [ REWRITE_TAC [APPEND; REPLICATE];
      STRIP_TAC THEN REWRITE_TAC [REPLICATE] THEN
        POP_ASSUM (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
        REWRITE_TAC [APPEND] ]);;

let REPLICATE_APPEND = prove
  (`!a b x:A. REPLICATE a x ++ REPLICATE b x = REPLICATE (a + b) x`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [REPLICATE; ADD; APPEND]);;

let SUB_LIST_0_APPEND = prove
  (`!l m (n:A list). l <= LENGTH m ==>
    SUB_LIST (0, l) (m ++ n) = SUB_LIST (0, l) m`,
  INDUCT_TAC THENL
    [ REWRITE_TAC [SUB_LIST_CLAUSES];
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `~(m:A list = [])` ASSUME_TAC THENL
        [ DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th; LENGTH])) THEN
            POP_ASSUM MP_TAC THEN
            REWRITE_TAC [LE; NOT_SUC];
          ALL_TAC ] THEN
        POP_ASSUM (fun th -> ONCE_REWRITE_TAC [MATCH_MP CONS_HD_TL th] THEN ASSUME_TAC th) THEN
        REWRITE_TAC [APPEND; SUB_LIST] THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [`TL m:A list`; `n:A list`]) THEN
        POP_ASSUM (fun th -> ONCE_REWRITE_TAC [MATCH_MP LENGTH_TL th]) THEN
        ANTS_TAC THENL
        [ SIMPLE_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC [] ] ]);;

let SUB_LIST_1 = prove
  (`!(l:A list) n. SUB_LIST(n,1) l = if n < LENGTH l then [EL n l] else []`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; SUB_LIST_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:A list`] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LT_0; num_CONV `1`; EL; TL] THEN
  ASM_REWRITE_TAC[GSYM(num_CONV `1`); LT_SUC; HD]);;
  
let EL_SUB_LIST = prove(`!a b i (m:A list).
     a + b <= LENGTH m /\ i < b ==>
     EL i (SUB_LIST (a, b) m) = EL (a + i) m`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[CONJUNCT1 LT] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC] THEN
    LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC[SUB_LIST_CLAUSES; LENGTH; EL; HD; TL; LE_SUC];
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; LENGTH] THEN
    ASM_SIMP_TAC[LE_SUC; ADD_CLAUSES; EL; TL; ARITH_RULE `~(SUC n <= 0)`]]);;

let SUB_LIST_SUB_LIST = prove
  (`!(m:A list) a b c d.
    a + b <= d ==>
    SUB_LIST (a, b) (SUB_LIST (c,d) m) = SUB_LIST (c + a, b) m`,
  LIST_INDUCT_TAC THENL
    [ REWRITE_TAC [SUB_LIST_CLAUSES]; ALL_TAC ] THEN
    REPEAT GEN_TAC THEN
    SPEC_TAC (`a:num`, `a:num`) THEN
    SPEC_TAC (`c:num`, `c:num`) THEN
    SPEC_TAC (`b:num`, `b:num`) THEN
    SPEC_TAC (`d:num`, `d:num`) THEN
    INDUCT_TAC THENL
    [ REPEAT STRIP_TAC THEN
        MP_TAC (ARITH_RULE `a+b <= 0 ==> a=0 /\ b=0`) THEN
        ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [SUB_LIST_CLAUSES];
      POP_ASSUM (K ALL_TAC) THEN
        INDUCT_TAC THENL
        [ REWRITE_TAC [SUB_LIST_CLAUSES];
          POP_ASSUM (K ALL_TAC) THEN
            INDUCT_TAC THENL
            [ INDUCT_TAC THENL
              [ FIRST_ASSUM (MP_TAC o SPECL [`0`; `b:num`; `0`; `d:num`]) THEN
                  REWRITE_TAC [ADD; LE_SUC; SUB_LIST_CLAUSES] THEN
                  REPEAT DISCH_TAC THEN
                  ASM_SIMP_TAC [];
                POP_ASSUM (K ALL_TAC) THEN
                  FIRST_ASSUM (MP_TAC o SPECL [`a:num`; `SUC b`; `0`; `d:num`]) THEN  
                  REWRITE_TAC [ADD; SUB_LIST_CLAUSES; LE_SUC] ];
              POP_ASSUM (K ALL_TAC) THEN
                INDUCT_TAC THENL
                [ FIRST_ASSUM (MP_TAC o SPECL [`0`; `SUC b`; `c:num`; `SUC d`]) THEN
                    REWRITE_TAC [ADD; ADD_0; LE_SUC; SUB_LIST_CLAUSES];
                  POP_ASSUM (K ALL_TAC) THEN
                    FIRST_ASSUM (MP_TAC o SPECL [`SUC a`; `SUC b`; `c:num`; `SUC d`]) THEN
                    REWRITE_TAC [ADD; LE_SUC; SUB_LIST_CLAUSES] ] ] ] ]);;

let DROP_0 = prove(`! m. drop 0 m = m`,
  STRIP_TAC THEN REWRITE_TAC [drop; SUB_0; SUB_LIST_LENGTH]);;

let DROP_APPEND = prove
  (`!l m (n:A list).
    l <= LENGTH m  ==>
    drop l (m ++ n) = drop l m ++ n`,
  INDUCT_TAC THENL
    [ REWRITE_TAC [drop; SUB_0; SUB_LIST_LENGTH];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [drop] THEN
      SUBGOAL_THEN `~(m:A list = [])` ASSUME_TAC THENL
      [ DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th; LENGTH])) THEN
          POP_ASSUM MP_TAC THEN
          REWRITE_TAC [LE; NOT_SUC];
        ALL_TAC ] THEN
      POP_ASSUM (fun th -> ONCE_REWRITE_TAC [MATCH_MP CONS_HD_TL th] THEN ASSUME_TAC th) THEN
      REWRITE_TAC [APPEND; LENGTH; SUB_SUC; SUB_LIST] THEN
      REWRITE_TAC [GSYM drop] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`TL m:A list`; `n:A list`]) THEN
      POP_ASSUM (fun th -> ONCE_REWRITE_TAC [MATCH_MP LENGTH_TL th]) THEN
      ANTS_TAC THENL
      [ SIMPLE_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC [] ] ]);;

let SUB_LIST_DROP = prove
  (`!p l (m:A list).
    SUB_LIST (p, l) m = SUB_LIST (0, l) (drop p m)`,
  REWRITE_TAC [drop] THEN INDUCT_TAC THENL
  [ REWRITE_TAC [SUB_0; SUB_LIST_LENGTH];
    REPEAT GEN_TAC THEN
      ASM_CASES_TAC `(m:A list) = []` THENL
      [ ASM_REWRITE_TAC [SUB_LIST_CLAUSES];
        POP_ASSUM (fun th -> ONCE_REWRITE_TAC [MATCH_MP CONS_HD_TL th]) THEN
          REWRITE_TAC [APPEND; LENGTH; SUB_SUC; SUB_LIST] THEN
          FIRST_X_ASSUM
            (fun th -> REWRITE_TAC [GSYM (SPECL [`l:num`; `TL m:A list`] th)]) ] ]);;

let SUB_LIST_APPEND_L = prove
  (`!p l m (n:A list).
    p+l <= LENGTH m ==>
    SUB_LIST (p, l) (m ++ n) = SUB_LIST (p, l) m`,
  REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [SUB_LIST_DROP] THEN
    IMP_REWRITE_TAC [DROP_APPEND; SUB_LIST_0_APPEND] THEN
    REWRITE_TAC [drop; LENGTH_SUB_LIST] THEN
    SIMPLE_ARITH_TAC);;

let SUB_LIST_APPEND_R = prove
  (`!p l m n:A list.
      LENGTH m <= p ==>
      SUB_LIST (p, l) (m ++ n) = SUB_LIST (p - LENGTH m, l) n`,
    INDUCT_TAC THENL
    [ REWRITE_TAC [LE] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN
        POP_ASSUM (fun th -> REWRITE_TAC [REWRITE_RULE [LENGTH_EQ_NIL] th]) THEN
        REWRITE_TAC [APPEND; SUB];
      GEN_TAC THEN LIST_INDUCT_TAC THENL
        [ REWRITE_TAC [APPEND; LENGTH; SUB_0]; ALL_TAC ] THEN
        ASM_REWRITE_TAC [LENGTH; SUB_SUC; APPEND; SUB_LIST; LE_SUC] ]);;

let DROP_APPEND2 = prove
  (`!l m n:A list. LENGTH m <= l ==> drop l (m++n) = drop (l - LENGTH m) n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [drop] THEN
  IMP_REWRITE_TAC [SUB_LIST_APPEND_R] THEN
  REWRITE_TAC [LENGTH_APPEND] THEN
  MP_TAC (ARITH_RULE `!x y z. x <= y ==> (x + z) - y = z - (y - x)`) THEN
  DISCH_THEN (fun th -> ASM_SIMP_TAC[th]));;

let TAKE_APPEND = prove
  (`!l m n:A list.
      LENGTH m <= l ==>
      take l (m ++ n) = m ++ (take (l - LENGTH m) n)`,
    REPEAT STRIP_TAC THEN
      REWRITE_TAC [take] THEN
      SUBGOAL_THEN `l = LENGTH (m:A list) + (l - LENGTH m)`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
      [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      REWRITE_TAC [SUB_LIST_SPLIT] THEN
      SIMP_TAC [SPECL [`0`; `LENGTH (m:A list)`] SUB_LIST_APPEND_L;
        SPEC `0 + LENGTH (m:A list)` SUB_LIST_APPEND_R; LE_REFL; ADD_0; ADD] THEN
      REWRITE_TAC [SUB_LIST_LENGTH; SUB_REFL]);;

let QUANTIFIER_SPLIT = prove
  (`!m n P.
    (!i. i < m * n ==> P i) <=>
    (!i. i < m ==> !j. j < n ==> P (n * i + j))`,
  REWRITE_TAC [DOUBLE_INCL] THEN
    REPEAT STRIP_TAC THENL
    [ FIRST_X_ASSUM (MP_TAC o SPEC `n * i + j`) THEN
        ANTS_TAC THENL
        [ SUBGOAL_THEN `n*i+j < n*i+n /\ n*i+n <= m*n`
            (fun th -> REWRITE_TAC [MATCH_MP LTE_TRANS th]) THEN
            ASM_REWRITE_TAC [LT_ADD_LCANCEL] THEN
            REWRITE_TAC [ARITH_RULE `n*i+n = (SUC i)*n`] THEN
            ASM_REWRITE_TAC [LE_MULT_RCANCEL; LE_SUC_LT];
          ITAUT_TAC ];
      SUBGOAL_THEN `i = n * (i DIV n) + i MOD n` (fun th -> ONCE_REWRITE_TAC [th]) THENL
        [ MP_TAC (SPECL [`i:num`; `n:num`] DIVISION) THEN
            ANTS_TAC THENL
            [ DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th; MULT_0; LT])) THEN
                ASM_REWRITE_TAC [];
              SIMPLE_ARITH_TAC ];
          ALL_TAC ] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC `i DIV n`) THEN
        ANTS_TAC THENL
        [ IMP_REWRITE_TAC [RDIV_LT_EQ] THEN
            ASM_REWRITE_TAC [MULT_SYM] THEN
            DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th; MULT_0; LT])) THEN
            ASM_REWRITE_TAC [];
          ALL_TAC ] THEN
        DISCH_THEN (MP_TAC o SPEC `i MOD n`) THEN
        REWRITE_TAC [MOD_LT_EQ] THEN
        ANTS_TAC THENL
        [ ASM_REWRITE_TAC [MULT_SYM] THEN
            DISCH_THEN (fun th -> RULE_ASSUM_TAC (REWRITE_RULE [th; MULT_0; LT])) THEN
            ASM_REWRITE_TAC [];
          ITAUT_TAC ] ]);;

let BLS_LS = prove
  (`! x y : (N)word.
    ~(val y <= val x /\ ~(val(word_sub x y) = 0)) <=> val x <= val y`,
  WORD_ARITH_TAC);;

let BYTES8_BYTELIST = prove
  (`!p s.
    read (memory :> bytes8(p)) s = x <=>
    read (memory :> bytelist(p, 1)) s = [x]`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [bytes8; bytelist; asword; ONE; through; component_compose; read; o_DEF; bytelist_of_num] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM WORD_MOD_SIZE] THEN
    REWRITE_TAC [DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [DOUBLE_INCL] THEN
    CONJ_TAC THEN STRIP_TAC THENL
    [ ASM_REWRITE_TAC [];
      RULE_ASSUM_TAC (REWRITE_RULE [CONS_11]) THEN ASM_REWRITE_TAC [] ]);;

let BYTELIST_APPEND = prove
  (`!p n n' l l' s.
    read (memory :> bytelist(p, n)) s = l /\
    read (memory :> bytelist(p + word n, n')) s = l' ==>
    read (memory :> bytelist(p, n + n')) s = l ++ l'`,
  REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `n = LENGTH (l:byte list) /\ n' = LENGTH (l':byte list)` MP_TAC THENL
    [ RULE_ASSUM_TAC (REWRITE_RULE [READ_BYTELIST_EQ_BYTES]) THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    DISCH_THEN (fun th -> POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o rev) THEN REWRITE_TAC [th]) THEN
    REWRITE_TAC [GSYM LENGTH_APPEND; GSYM bytes_loaded] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [bytes_loaded_append]);;

let SHIFT_BYTE_LIST_AT = prove
  (`!l m. LENGTH m < 2 EXP 64 /\
    l <= LENGTH m /\
    byte_list_at m m_p s ==>
    byte_list_at (drop l m) (m_p + word l) s`,
  REWRITE_TAC [byte_list_at; drop; LENGTH_SUB_LIST; MIN; LE_REFL] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    IMP_REWRITE_TAC [EL_SUB_LIST] THEN
    SIMPLE_ARITH_TAC);;

let BYTE_LIST_AT_APPEND = prove
  (`!m n p s.
    byte_list_at (m ++ n) p s <=> byte_list_at m p s /\ byte_list_at n (p + word (LENGTH m)) s`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [byte_list_at] THEN
    REWRITE_TAC [TAUT `!P Q. (P <=> Q) <=> (P ==> Q) /\ (Q ==> P)`] THEN
    REPEAT STRIP_TAC THENL
    [ FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN
        DISCH_THEN (fun th -> IMP_REWRITE_TAC [th]) THEN
        ASM_REWRITE_TAC [LENGTH_APPEND; EL_APPEND] THEN
        SIMPLE_ARITH_TAC;
      FIRST_X_ASSUM (MP_TAC o SPEC `LENGTH (m:byte list) + i`) THEN
        REWRITE_TAC [LENGTH_APPEND; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        DISCH_THEN (fun th -> IMP_REWRITE_TAC [th]) THEN
        REWRITE_TAC [EL_APPEND] THEN
        REWRITE_TAC [ARITH_RULE `!x y. ~(x + y < x)`; ADD_SUB2] THEN
        SIMPLE_ARITH_TAC;
      REWRITE_TAC [EL_APPEND] THEN
        COND_CASES_TAC THENL
        [ FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC [];
          FIRST_X_ASSUM (MP_TAC o SPEC `(i - LENGTH (m:byte list))`) THEN
          ANTS_TAC THENL
          [ RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_APPEND]) THEN
              SIMPLE_ARITH_TAC;
            ALL_TAC ] THEN
          REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          ASM_SIMP_TAC [ARITH_RULE `!x y. ~(x < y) ==> y + x - y = x`] ] ]);;


(* ===== conv ===== *)

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;


(* ===== tactic ===== *)

let RENAME_TAC old_name new_name =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(old_name, new_name) THEN 
  STRIP_TAC THEN STRIP_TAC;;


let pth = prove
   (`!k pc1 pc2 (loopinvariant:num->A->bool).
       C ,, C = C /\
       ~(k = 0) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         loopinvariant 0 s)
                    C /\
       (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant (i + 1) s)
                             C) /\
       (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant k s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN
    DISCH_THEN(LABEL_TAC "*" o MATCH_MP
      (ONCE_REWRITE_RULE[IMP_CONJ] ENSURES_TRANS_SIMPLE)) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] th)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] th)) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC(`k - 1`,`j:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[ADD1] THEN CONJ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `0` o CONJUNCT1) THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `i:num`] THEN
    ASM_CASES_TAC `i + 1 < k` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `i + 1 < k ==> i < k`)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "*" (fun th ->
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] th)) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `i + 1`)) THEN
    MATCH_MP_TAC(TAUT
     `(p /\ r) /\ (q /\ s ==> t) ==> (p ==> q) ==> (r ==> s) ==> t`) THEN
    ASM_REWRITE_TAC[ENSURES_TRANS_SIMPLE] THEN ASM_ARITH_TAC);;

let pth_0 = prove
 (`!k pc1 pc2 (loopinvariant:num->A->bool).
     C ,, C = C /\
     ensures step (\s. program_decodes s /\
                       read pcounter s:N word = word pc /\
                       precondition s)
                  (\s. program_decodes s /\
                       read pcounter s = word pc2 /\
                       loopinvariant 0 s)
                  C /\
     (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
          ==> ensures step (\s. program_decodes s /\
                                read pcounter s = word pc1 /\
                                loopinvariant i s)
                           (\s. program_decodes s /\
                                read pcounter s = word pc2 /\
                                loopinvariant (i + 1) s)
                           C) /\
     (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
          ==> ensures step (\s. program_decodes s /\
                                read pcounter s = word pc2 /\
                                loopinvariant i s)
                           (\s. program_decodes s /\
                                read pcounter s = word pc1 /\
                                loopinvariant i s)
                           C) /\
     ensures step (\s. program_decodes s /\
                       read pcounter s = word pc2 /\
                       loopinvariant k s)
                   postcondition
                   C
     ==> ensures step
           (\s. program_decodes s /\
                read pcounter s = word pc /\
                precondition s)
           postcondition
           C`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ENSURES_TRANS];
    STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC
     [`k:num`; `pc1:num`; `pc2:num`; `loopinvariant:num->A->bool`] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`]
        ENSURES_TRANS_SIMPLE)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let ENSURES_WHILE_UP_OR_0_TAC =
 fun k pc1 pc2 iv ->
    (MATCH_MP_TAC pth_0 THEN
     MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;


let rth = prove
   (`!a b pc1 pc2 (loopinvariant:num->A->bool).
       C ,, C = C /\
       a < b /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc1 /\
                         loopinvariant a s)
                    C /\
       (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant (i + 1) s)
                             C) /\
       (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\
            ~(i = a) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant b s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`;
                          `\i. (loopinvariant:num->A->bool) (a + i)`] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC[ADD_ASSOC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;


let rth_0 = prove
   (`!a b pc1 pc2 (loopinvariant:num->A->bool).
       C ,, C = C /\
       a <= b /\
       ensures step (\s. program_decodes s /\
                         read pcounter s : N word = word pc /\
                         precondition s)
                    (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant a s)
                    C /\
       (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant (i + 1) s)
                             C) /\
       (!i. a <= i /\ i < b /\ ~(i = b) /\
            ~(b = 0) /\ 0 < b
            ==> ensures step (\s. program_decodes s /\
                                  read pcounter s = word pc2 /\
                                  loopinvariant i s)
                             (\s. program_decodes s /\
                                  read pcounter s = word pc1 /\
                                  loopinvariant i s)
                             C) /\
       ensures step (\s. program_decodes s /\
                         read pcounter s = word pc2 /\
                         loopinvariant b s)
                     postcondition
                     C
       ==> ensures step
             (\s. program_decodes s /\
                  read pcounter s = word pc /\
                  precondition s)
             postcondition
             C`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:num = b` THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ENSURES_TRANS];
    STRIP_TAC THEN MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC
     [`a:num`; `b:num`; `pc1:num`; `pc2:num`; `loopinvariant:num->A->bool`] THEN
    ASM_SIMP_TAC[LT_LE] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`]
        ENSURES_TRANS_SIMPLE)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let ENSURES_WHILE_AUP_OR_0_TAC =
  fun a b pc1 pc2 iv ->
    (MATCH_MP_TAC rth_0 THEN
     MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv] THEN
     BETA_TAC THEN
     CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

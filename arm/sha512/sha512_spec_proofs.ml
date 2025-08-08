needs "arm/sha512/sha512_specs.ml";;

(* ===== thm ===== *)
let EXPAND_HASH_THM = prove
  (`! h0 h1 h2 h3 h4 h5 h6 h7 h.
    (h0, h1, h2, h3, h4, h5, h6, h7) = h <=>
      h0 = SHA512_A h /\ h1 = SHA512_B h /\
      h2 = SHA512_C h /\ h3 = SHA512_D h /\
      h4 = SHA512_E h /\ h5 = SHA512_F h /\
      h6 = SHA512_G h /\ h7 = SHA512_H h`,
  REWRITE_TAC [FORALL_PAIR_THM; PAIR_EQ; SHA512_A; SHA512_B; SHA512_C;
    SHA512_D; SHA512_E; SHA512_F; SHA512_G; SHA512_H]);;

let COMPRESSION_STEP_AUX = prove(`! r i j h m.
  i + r = j /\ i <= j ==>
    compression_until (j + 1) i h m
      = compression_update
          (compression_until j i h m)
          (K_tbl j)
          (msg_schedule m j)`,
  INDUCT_TAC THENL
  [ (* Base case *)
    REWRITE_TAC[ADD_CLAUSES] THEN
      REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [compression_until] THEN
      ASM_REWRITE_TAC[ARITH_RULE `j < j + 1`] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ONCE_REWRITE_TAC [compression_until] THEN
      REWRITE_TAC[LT_REFL];
    (* Inductive case *)
    REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [compression_until] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `i + SUC r = (i + 1) + r`]) THEN
      MP_TAC (ARITH_RULE `(i + 1) + r = j ==> i < j + 1 /\ i < j`) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i + 1`; `j : num`; `compression_update h (K_tbl i) (msg_schedule m i)`; `m : num -> int64`]) THEN
      SUBGOAL_THEN `i + 1 <= j` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] ]);;

let COMPRESSION_STEP = prove(`! i j h m.
  i <= j ==>
    compression_until (j + 1) i h m
      = compression_update
        (compression_until j i h m)
        (K_tbl j)
        (msg_schedule m j)`,
  REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`j - i`; `i:num`; `j:num`;
             `h:hash_t`; `m:num->int64`] COMPRESSION_STEP_AUX) THEN
    IMP_REWRITE_TAC [ARITH_RULE `i <= j ==> i+j-i=j`]);;

let BYTES_MOD_BLOCKS_SUB_LIST = prove
  (`! m. bytes_mod_blocks m =
    SUB_LIST
      (LENGTH m DIV num_bytes_per_block * num_bytes_per_block,
       LENGTH m MOD num_bytes_per_block)
      m`,
  STRIP_TAC THEN
  REWRITE_TAC [bytes_mod_blocks; drop; num_bytes_per_block] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    [MATCH_MP DIVISION (ARITH_RULE `~(128 = 0)`)] THEN
  REWRITE_TAC [ADD_SUB2]);;

let BYTES_MOD_BLOCKS_REFL = prove
                (`!m. LENGTH m < 128 ==> bytes_mod_blocks m = m`,
                  REPEAT STRIP_TAC THEN
                    REWRITE_TAC [BYTES_MOD_BLOCKS_SUB_LIST; num_bytes_per_block] THEN
                    ASM_SIMP_TAC [DIV_LT; MOD_LT] THEN
                    REWRITE_TAC [MULT; SUB_LIST_LENGTH]);;

let LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD = prove
  (`! m. LENGTH (bytes_mod_blocks m) = LENGTH m MOD 128`,
  STRIP_TAC THEN
    REWRITE_TAC[bytes_mod_blocks; num_bytes_per_block; drop; LENGTH_SUB_LIST] THEN
    ARITH_TAC);;

let LENGTH_BYTES_MOD_BLOCKS_LT = prove
  (`! m. LENGTH (bytes_mod_blocks m) < num_bytes_per_block`,
  STRIP_TAC THEN
  REWRITE_TAC [num_bytes_per_block; BYTES_MOD_BLOCKS_SUB_LIST; LENGTH_SUB_LIST] THEN
  ARITH_TAC);;

let BYTES_TO_BLOCKS_LAST = prove
  (`!m0 m:byte list.
      LENGTH m0 MOD 128 = 0 /\
      LENGTH m = 128 ==>
      bytes_to_blocks (m0 ++ m) (LENGTH m0 DIV 128) = bytes_to_one_block m`,
    REPEAT STRIP_TAC THEN
      REWRITE_TAC[bytes_to_blocks; num_bytes_per_block] THEN
      MP_TAC (GSYM (SPECL [`LENGTH (m0:byte list)`;`128`] DIVISION)) THEN
      ASM_REWRITE_TAC [ADD_0; ARITH_RULE `~(0 = 128)`] THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC [SUB_LIST_APPEND_R; LE_REFL; SUB_REFL] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM SUB_LIST_LENGTH] THEN
      ASM_REWRITE_TAC []);;

let BYTES_TO_BLOCKS_APPEND_R = prove
  (`!i m n:byte list.
      LENGTH m MOD 128 = 0 ==>
      bytes_to_blocks (m ++ n) (LENGTH m DIV 128 + i) = bytes_to_blocks n i`,
    REPEAT STRIP_TAC THEN
      REWRITE_TAC [bytes_to_blocks; num_bytes_per_block; RIGHT_ADD_DISTRIB] THEN
      FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [GSYM DIVIDES_MOD; DIVIDES_DIV_MULT]) THEN
      ASM_REWRITE_TAC [] THEN
      SIMP_TAC [SUB_LIST_APPEND_R; LE_ADD; ADD_SUB2]);;

let BYTES_TO_BLOCKS_TAKE_BLOCKS = prove
  (`!i l. i < l /\ l <= LENGTH m DIV 128 ==>
    bytes_to_blocks (take (l * 128) m) i = bytes_to_blocks m i`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [take; bytes_to_blocks; num_bytes_per_block] THEN
    FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP (ARITH_RULE `i < l ==> i*128 + 128 <= l*128`)) THEN
    ASM_SIMP_TAC [SUB_LIST_SUB_LIST; ADD]);;

let MOD_0_BYTES_MOD_BLOCKS_APPEND = prove
  (`!m n. LENGTH m MOD 128 = 0 ==>
    bytes_mod_blocks (m ++ n) = bytes_mod_blocks n`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [bytes_mod_blocks; num_bytes_per_block; LENGTH_APPEND] THEN
    ASM_SIMP_TAC [MOD_0_ADD_DIV; ARITH] THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    ASM_SIMP_TAC [MOD_0_DIV_MULT] THEN
    SIMP_TAC [DROP_APPEND2; LE_ADD] THEN
    REWRITE_TAC [ADD_SUB2]);;

let TAKE_APPEND_MOD_BLOCKS_REFL = prove
  (`!m. take (LENGTH m DIV 128 * 128) m ++ bytes_mod_blocks m = m`,
  STRIP_TAC THEN
  REWRITE_TAC [take; BYTES_MOD_BLOCKS_SUB_LIST; num_bytes_per_block] THEN
  REWRITE_TAC [ARITH_RULE `!x. x MOD 128 = x - x DIV 128 * 128`; SUB_LIST_TOPSPLIT]);;

let BLOCKS_EQ_SHA512'_EQ = prove
  (`! h m m' l.
    (! i. i < l ==> m i = m' i) ==>
    sha512' h m l = sha512' h m' l`,
  REPLICATE_TAC 3 GEN_TAC THEN
    INDUCT_TAC THENL
    [ REWRITE_TAC [sha512'];
      STRIP_TAC THEN
        ONCE_REWRITE_TAC [sha512'] THEN
        REWRITE_TAC [NOT_SUC; SUC_SUB1] THEN
        NAME_ASSUMS_TAC THEN
        USE_THEN "H0" (fun th -> ASSUME_TAC (SPEC `l:num` th)) THEN
        ASM_SIMP_TAC [ARITH_RULE `l < SUC l`] THEN
        USE_THEN "H1" (fun th -> IMP_REWRITE_TAC [th]) THEN
        ARITH_TAC ]);;

let BLOCKS_EQ_SHA512_EQ = prove
  (`! m m' l.
    (! i. i < l ==> m i = m' i) ==>
    sha512 m l = sha512 m' l`,
  REWRITE_TAC [sha512; BLOCKS_EQ_SHA512'_EQ]);;

let BLOCKS_APPEND_EQ_LAND = prove
  (`! i m0 m. i < LENGTH m0 DIV 128 ==>
    bytes_to_blocks (m0 ++ m) i = bytes_to_blocks m0 i`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [bytes_to_blocks; num_bytes_per_block] THEN
    IMP_REWRITE_TAC [SUB_LIST_APPEND_L] THEN
    SIMPLE_ARITH_TAC);;

let SHA512'_BLOCK_STEP = prove
  (`!h m0 m:byte list.
    LENGTH m0 MOD 128 = 0 /\
    LENGTH m = 128 ==>
    sha512_block
      (bytes_to_one_block m)
      (sha512' h (bytes_to_blocks m0) (LENGTH m0 DIV 128)) =
    sha512' h (bytes_to_blocks (m0 ++ m)) (LENGTH (m0 ++ m) DIV 128)`,
  REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [sha512'] THEN
    ASM_REWRITE_TAC [LENGTH_APPEND] THEN
    IMP_REWRITE_TAC [MOD_0_ADD_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [ARITH_RULE `!x. ~(x+1=0) /\ (x+1)-1 = x`] THEN
    ASM_SIMP_TAC [SPECL [`h:hash_t`; `bytes_to_blocks (m0++m)`; `bytes_to_blocks m0`]
      BLOCKS_EQ_SHA512'_EQ; BLOCKS_APPEND_EQ_LAND; BYTES_TO_BLOCKS_LAST]);;

let SHA512'_BLOCKS_STEP = prove
  (`!h m0 m:byte list.
    LENGTH m0 MOD 128 = 0 ==>
    sha512'
      (sha512' h (bytes_to_blocks m0) (LENGTH m0 DIV 128))
      (bytes_to_blocks m)
      (LENGTH m DIV 128) =
    sha512' h (bytes_to_blocks (m0 ++ m)) (LENGTH (m0 ++ m) DIV 128)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC [LENGTH_APPEND] THEN
      ASM_SIMP_TAC [MOD_0_ADD_DIV; ARITH] THEN
      ABBREV_TAC `i = LENGTH (m:byte list) DIV 128` THEN
      POP_ASSUM MP_TAC THEN
      SPEC_TAC (`m:byte list`, `m:byte list`) THEN
      SPEC_TAC (`i:num`, `i:num`) THEN
      INDUCT_TAC THEN REPEAT STRIP_TAC THENL
      [ REWRITE_TAC [ADD_0] THEN
          GEN_REWRITE_TAC LAND_CONV [sha512'] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          ASM_SIMP_TAC [SPECL [`h:hash_t`; `bytes_to_blocks (m0++m)`; `bytes_to_blocks m0`]
            BLOCKS_EQ_SHA512'_EQ; BLOCKS_APPEND_EQ_LAND; BYTES_TO_BLOCKS_LAST];
        GEN_REWRITE_TAC BINOP_CONV [sha512'] THEN
          REWRITE_TAC [ADD_SUC; NOT_SUC; SUC_SUB1] THEN
          ASM_SIMP_TAC [BYTES_TO_BLOCKS_APPEND_R] THEN
          FIRST_X_ASSUM (MP_TAC o SPEC `take (i * 128) (m:byte list)`) THEN
          ANTS_TAC THENL
          [ REWRITE_TAC [take; LENGTH_SUB_LIST; SUB_0; MIN] THEN
              SIMPLE_ARITH_TAC;
            ALL_TAC ] THEN
          IMP_REWRITE_TAC [SPECL [`sha512' h (bytes_to_blocks m0) (LENGTH m0 DIV 128)`;
            `bytes_to_blocks (take (i * 128) m)`; `bytes_to_blocks m`; `i:num`]
            BLOCKS_EQ_SHA512'_EQ] THEN
          IMP_REWRITE_TAC [SPECL [`h:hash_t`; 
            `bytes_to_blocks (m0 ++ take (i * 128) m)`; 
            `bytes_to_blocks (m0 ++ m)`; `LENGTH (m0:byte list) DIV 128 + i`]
            BLOCKS_EQ_SHA512'_EQ] THEN
          REPEAT DISCH_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
          [ SUBGOAL_THEN `(m0:byte list ++ take (i*128) m) = take (LENGTH m0 + i*128) (m0 ++ m)`
                (fun th -> REWRITE_TAC [th]) THENL
              [ SIMP_TAC [TAKE_APPEND; LE_ADD; ADD_SUB2]; ALL_TAC ] THEN
              SUBGOAL_THEN `LENGTH (m0:byte list) + i * 128 = (LENGTH m0 DIV 128 + i) * 128`
                (fun th -> REWRITE_TAC [th]) THENL
              [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
              IMP_REWRITE_TAC [BYTES_TO_BLOCKS_TAKE_BLOCKS] THEN
              REWRITE_TAC [LENGTH_APPEND] THEN
              SIMPLE_ARITH_TAC;
            IMP_REWRITE_TAC [BYTES_TO_BLOCKS_TAKE_BLOCKS] THEN
              ARITH_TAC] ]);;

let SHA512'_BLOCK_BYTES_MOD_BLOCKS_STEP = prove
  (`!h m0 m.
    LENGTH m = 128 - LENGTH (bytes_mod_blocks m0) ==>
    sha512_block
      (bytes_to_one_block (bytes_mod_blocks m0 ++ m))
      (sha512' h (bytes_to_blocks m0) (LENGTH m0 DIV 128)) =
    sha512' h
      (bytes_to_blocks (m0 ++ m))
      (LENGTH (m0 ++ m) DIV 128)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `sha512' h (bytes_to_blocks m0) (LENGTH m0 DIV 128) =
      sha512' h (bytes_to_blocks (take (LENGTH m0 DIV 128 * 128) m0)) (LENGTH m0 DIV 128)`
      (fun th -> ONCE_REWRITE_TAC [th]) THENL
    [ IMP_REWRITE_TAC [SPECL [`h:hash_t`;
        `bytes_to_blocks (take (LENGTH m0 DIV 128 * 128) m0)`;
        `bytes_to_blocks m0`;
        `LENGTH (m0:byte list) DIV 128`] BLOCKS_EQ_SHA512'_EQ] THEN
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC [BYTES_TO_BLOCKS_TAKE_BLOCKS; LE_REFL];
      ALL_TAC ] THEN
    SUBGOAL_THEN `LENGTH m0 DIV 128 = LENGTH (take (LENGTH m0 DIV 128 * 128) m0:byte list) DIV 128`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
    [ REWRITE_TAC [take; LENGTH_SUB_LIST; MIN] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
    IMP_REWRITE_TAC [SPECL [`h:hash_t`; `take (LENGTH m0 DIV 128 * 128) m0:byte list`;
      `bytes_mod_blocks m0 ++ m`] SHA512'_BLOCK_STEP] THEN
    REWRITE_TAC [APPEND_ASSOC; TAKE_APPEND_MOD_BLOCKS_REFL] THEN
    MP_TAC (SPEC `m0:byte list` LENGTH_BYTES_MOD_BLOCKS_LT) THEN
    ASM_REWRITE_TAC [take; LENGTH_SUB_LIST; MIN; LENGTH_APPEND; num_bytes_per_block; SUB_0] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC [ARITH_RULE `!x y. x < y ==> x + y - x = y`] THEN
    REWRITE_TAC [ARITH_RULE `!x. x DIV 128 * 128 <= x`] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [MOD_MULT]);;

let ADD_128_SUB_MOD_0 = prove
  (`!x. (x + 128 - x MOD 128) MOD 128 = 0`,
  STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `n + 128 - n MOD 128 = 128 * 1 + n - n MOD 128`] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN
    SIMP_TAC [SUB_MOD_MOD; ARITH]);;

let SHA512'_BLOCKS_TAKE_DROP_STEP = prove
  (`!h m0 m.
    128 - LENGTH (bytes_mod_blocks m0) <= LENGTH m ==>
    sha512'
      (sha512' h
        (bytes_to_blocks (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m))
        (LENGTH (m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m) DIV 128))
      (bytes_to_blocks (drop (128 - LENGTH (bytes_mod_blocks m0)) m))
      ((LENGTH m - (128 - LENGTH (bytes_mod_blocks m0))) DIV 128) =
    sha512' h (bytes_to_blocks (m0 ++ m)) (LENGTH (m0 ++ m) DIV 128)`,
  REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `LENGTH (m:byte list) - (128 - LENGTH (bytes_mod_blocks m0)) =
      LENGTH (drop (128 - LENGTH (bytes_mod_blocks m0)) m)`
      (fun th -> REWRITE_TAC [th]) THENL
    [  REWRITE_TAC [drop; LENGTH_SUB_LIST] THEN ARITH_TAC; ALL_TAC ] THEN
    IMP_REWRITE_TAC [SPECL [`h:hash_t`; `m0 ++ take (128 - LENGTH (bytes_mod_blocks m0)) m`;
      `drop (128 - LENGTH (bytes_mod_blocks m0)) m:byte list`] SHA512'_BLOCKS_STEP] THEN
    REWRITE_TAC [GSYM APPEND_ASSOC; take; drop; SUB_LIST_TOPSPLIT] THEN
    ASM_REWRITE_TAC [LENGTH_APPEND; LENGTH_SUB_LIST; MIN; SUB_0] THEN
    REWRITE_TAC [LENGTH_BYTES_MOD_BLOCKS_LENGTH_MOD] THEN
    REWRITE_TAC[ADD_128_SUB_MOD_0]);;

let PAD_SOUND = prove
  (`!m. LENGTH (pad m) MOD num_bytes_per_block = 0 /\
    take (LENGTH m) (pad m) = m`,
  REPEAT STRIP_TAC THENL
    [ REWRITE_TAC [pad; num_bytes_per_block; LENGTH_REPLICATE; LENGTH_APPEND;
          int128_to_bytes; LENGTH] THEN
        REWRITE_TAC [ADD_AC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SIMP_TAC [SUB_ADD; LT_CEIL_DIV_MUL; ARITH] THEN
        ONCE_REWRITE_TAC [MULT_SYM] THEN
        REWRITE_TAC [MOD_MULT];
      REWRITE_TAC [pad] THEN
        SIMP_TAC [TAKE_APPEND; LE_REFL] THEN
        REWRITE_TAC [SUB_REFL; take; SUB_LIST; APPEND_NIL] ]);;

(* Lemmas involving data layout in memory *)

let MSG_BLOCK_AT_ALT = prove
  (`!m m_p s.
    msg_block_at m m_p s <=>
    (!i. i < 16 ==> read (memory :> bytes64 (m_p + word (8 * i))) s = m i)`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [msg_block_at] THEN
    CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [WORD_ADD_0]);;

let BYTE_LIST_AT_MSG_BLOCK_AT = prove
  (`!m m_p s.
    128 <= LENGTH m /\
    byte_list_at m m_p s ==>
    msg_block_at (bytes_to_one_block m) m_p s`,
  REWRITE_TAC [byte_list_at; MSG_BLOCK_AT_ALT] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!i. i < 16 * 8 ==>
      read (memory :> bytes8 (m_p + word i)) s = EL i m` MP_TAC THENL
    [ ASM_MESON_TAC[ARITH_RULE `i < 16 * 8 /\ 128 <= l ==> i < l`]; ALL_TAC ] THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [QUANTIFIER_SPLIT] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC (LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC [ADD_0] THEN STRIP_TAC THEN
    CONV_TAC (READ_MEMORY_SPLIT_CONV 3) THEN
    ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC [bytes_to_one_block; join_bytes_to_int64] THEN
    IMP_REWRITE_TAC [EL_SUB_LIST] THEN
    REWRITE_TAC [ADD_0] THEN
    REPEAT CONJ_TAC THEN REPEAT SIMPLE_ARITH_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    REFL_TAC);;

let BYTE_LIST_AT_MSG_BLOCKS_AT = prove
  (`!m m_p s.
    byte_list_at m m_p s ==>
    msg_blocks_at (bytes_to_blocks m) (LENGTH m DIV 128) m_p s`,
  REWRITE_TAC [byte_list_at; msg_blocks_at; bytes_to_blocks;  num_bytes_per_block] THEN
    REWRITE_TAC [MSG_BLOCK_AT_ALT] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `!i. i < LENGTH (m:byte list)  DIV 128 * 128 ==>
      read (memory :> bytes8 (m_p + word i)) s = EL i m` MP_TAC THENL
    [ ASM_MESON_TAC[ARITH_RULE `i < (l DIV 128) * 128 ==> i < l`] ; ALL_TAC ] THEN
    REWRITE_TAC [QUANTIFIER_SPLIT] THEN
    REWRITE_TAC[ARITH_RULE `j < 128 <=> j < 16 * 8`] THEN
    REWRITE_TAC [QUANTIFIER_SPLIT] THEN
    POP_ASSUM (K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPEC `i':num`) THEN
    ASM_REWRITE_TAC [] THEN
    CONV_TAC (LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC [ADD_0] THEN
    STRIP_TAC THEN
    CONV_TAC (READ_MEMORY_SPLIT_CONV 3) THEN
    ASM_REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC [bytes_to_one_block; join_bytes_to_int64] THEN
    IMP_REWRITE_TAC [EL_SUB_LIST] THEN
    REWRITE_TAC [LENGTH_SUB_LIST; ADD_0] THEN
    REPEAT CONJ_TAC THEN REPEAT SIMPLE_ARITH_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    REFL_TAC);;

let INT64_BYTE_LIST = prove
  (`!w p s. read (memory :> bytes64 p) s = w <=> byte_list_at (int64_to_bytes w) p s`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC [byte_list_at; int64_to_bytes; LENGTH] THEN
    CONV_TAC (TOP_DEPTH_CONV NUM_SUC_CONV) THEN
    CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC (TOP_DEPTH_CONV EL_CONV) THEN
    CONV_TAC (LAND_CONV (READ_MEMORY_SPLIT_CONV 3)) THEN
    CONV_TAC (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC [GSYM CONJ_ASSOC; WORD_ADD_0]);;

let INT64_HI_LO_INT128 = prove
  (`!x p s. x < 2 EXP 128 /\
    read (memory :> bytes64 p) s = word_bytereverse (word (x DIV 2 EXP 64)) /\
    read (memory :> bytes64 (p + word 8)) s = word_bytereverse (word (x MOD 2 EXP 64)) ==>
    byte_list_at (int128_to_bytes (word_bytereverse (word x))) p s`,
  REWRITE_TAC [INT64_BYTE_LIST; byte_list_at; int64_to_bytes; int128_to_bytes; LENGTH] THEN
    CONV_TAC (TOP_DEPTH_CONV NUM_SUC_CONV) THEN
    CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC (TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC (TOP_DEPTH_CONV NUM_ADD_CONV) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `word (x DIV 2 EXP 64):int64 = word_subword (word x:int128) (64, 64)`
      (fun th -> REWRITE_TAC [th]) THENL
    [ REWRITE_TAC [word_subword] THEN
        ASM_SIMP_TAC [VAL_WORD_EQ; DIMINDEX_128] THEN
        MP_TAC (ARITH_RULE `x < 2 EXP 128 ==> x DIV 2 EXP 64 < 2 EXP 64`) THEN
        ANTS_TAC THENL [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
        DISCH_THEN (ASSUME_TAC o MATCH_MP MOD_LT) THEN
        ASM_REWRITE_TAC [];
      ALL_TAC ] THEN
    SUBGOAL_THEN `word (x MOD 2 EXP 64):int64 = word_subword (word x:int128) (0, 64)`
      (fun th -> REWRITE_TAC [th]) THENL
    [ REWRITE_TAC [word_subword] THEN
        ASM_SIMP_TAC [VAL_WORD_EQ; DIMINDEX_128] THEN
        REWRITE_TAC [EXP; DIV_1];
      ALL_TAC ] THEN
    CONV_TAC WORD_BLAST);;


(* ===== tactic ===== *)

let ASSUM_EXPAND_SHA512_SPECS_TAC =
  RULE_ASSUM_TAC (REWRITE_RULE[sha512_ctx_at; byte_list_at; constants_at;
                              sha512_ctx_from; num_bytes_per_block;
                              hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC]) THEN
  RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV let_CONV)) THEN
  RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o rev) THEN
  STRIP_TAC;;

let EXPAND_SHA512_SPECS_TAC =
  REWRITE_TAC[sha512_ctx_at; byte_list_at; constants_at;
              sha512_ctx_from; num_bytes_per_block;
              hash_buffer_at; EXPAND_HASH_THM; GSYM CONJ_ASSOC] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV);;

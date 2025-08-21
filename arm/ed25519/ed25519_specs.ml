needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/edwards25519.ml";;
needs "arm/sha512/sha512_specs.ml";;

parse_as_infix ("++", (13, "right"));;
override_interface("++", `APPEND`);;
parse_as_infix("&&",(13,"right"));;
override_interface("&&",`word_and:N word->N word->N word`);;
parse_as_infix("||",(13,"right"));;
override_interface("||",`word_or:N word->N word->N word`);;

let ed25519_encode = new_definition
  `ed25519_encode (X,Y) =
        let x = num_of_int(X rem &p_25519)
        and y = num_of_int(Y rem &p_25519) in
        2 EXP 255 * x MOD 2 + y`;;

let ed25519_validencode = new_definition
  `ed25519_validencode n <=>
        ?P. P IN group_carrier edwards25519_group /\
            ed25519_encode P = n`;;

let ed25519_decode = new_definition
 `ed25519_decode n =
        @P. P IN group_carrier edwards25519_group /\
            ed25519_encode P = n`;;

let secret_scalar_of_seed_digest = define
  `secret_scalar_of_seed_digest h : byte list =
    [(HD h) && (word 0b11111000)] ++ SUB_LIST (1, 30) h ++
    [((EL 31 h) && (word 0b01111111)) || (word 0b01000000)]`;;

unparse_as_infix("&&");;
remove_interface("&&");;
unparse_as_infix("||");;
remove_interface("||");;

let phflag = define
  `phflag alg = if alg = 2 then 1 else 0`;;

let ascii_of_char = define
  `ascii_of_char (ASCII a0 a1 a2 a3 a4 a5 a6 a7) =
    (if a0 then 2 EXP 7 else 0) +
    (if a1 then 2 EXP 6 else 0) +
    (if a2 then 2 EXP 5 else 0) +
    (if a3 then 2 EXP 4 else 0) +
    (if a4 then 2 EXP 3 else 0) +
    (if a5 then 2 EXP 2 else 0) +
    (if a6 then 2 EXP 1 else 0) +
    (if a7 then 2 EXP 0 else 0)`;;

let byte_of_char = define
  `byte_of_char c = word (ascii_of_char c) : byte`;;

let dom2_prefix = define
  `dom2_prefix = MAP byte_of_char "SigEd25519 no Ed25519 collisions"`;;

let max_dom2_size = define
  `max_dom2_size = 289`;;

let dom2_valid = define
  `dom2_valid (alg : num) (ctx : byte list) =
    (LENGTH ctx <= 255 /\
     if alg = 0 then ctx = []
     else if alg = 1 then ~(ctx = [])
     else alg = 2)`;;

let public_key_of_seed = define
  `public_key_of_seed seed : byte list =
    let h = sha512_pad seed in
    let bytelist_s = secret_scalar_of_seed_digest h in
    let secret_s = num_of_bytelist bytelist_s : num in
    let s_B = group_pow edwards25519_group E_25519 secret_s : int#int in
    let enc_A = ed25519_encode s_B : num in
    let bytelist_A = bytelist_of_num 32 enc_A in
    bytelist_A`;;

let ph = define
  `ph alg = if alg = 2 then sha512_pad else \x.x`;;

let dom2_of = define
  `dom2_of alg ctx =
    if alg = 0 then []
      else dom2_prefix ++ [word (phflag alg)] ++ [word (LENGTH ctx)] ++ ctx`;;

let sign = define
  `sign (alg : num) (ctx : byte list) (seed : byte list) (m : byte list) =
    let h = sha512_pad seed in
    let bytelist_s = secret_scalar_of_seed_digest h in
    let secret_s = num_of_bytelist bytelist_s : num in
    let s_B = group_pow edwards25519_group E_25519 secret_s : int#int in
    let enc_A = ed25519_encode s_B : num in
    let bytelist_A = bytelist_of_num 32 enc_A in
    let prefix = SUB_LIST (32, 32) h in
    let dom2 = dom2_of alg ctx in
    let bytelist_r = sha512_pad (dom2 ++ prefix ++ ph alg m) in
    let r = num_of_bytelist bytelist_r : num in
    let r_B = group_pow edwards25519_group E_25519 r in
    let enc_R = ed25519_encode r_B : num in
    let bytelist_R = bytelist_of_num 32 enc_R in
    let bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph alg m) in
    let k = num_of_bytelist bytelist_k : num in
    let sig_S = (r + k * secret_s) MOD n_25519 in
    let bytelist_S = bytelist_of_num 32 sig_S in
    let sig = bytelist_R ++ bytelist_S in
    sig`;;

let ed25519_valid_bytelist = define
  `ed25519_valid_bytelist bytelist_P =
    ed25519_validencode (num_of_bytelist bytelist_P)`;;

let sig_valid = define
  `sig_valid (sig : byte list) =
    (LENGTH sig = 64 /\
     ed25519_valid_bytelist (SUB_LIST (0, 32) sig) /\
     num_of_bytelist (SUB_LIST (32, 32) sig) < n_25519)`;;

let verify_args_valid = define
  `verify_args_valid (bytelist_A : byte list) (sig : byte list) =
    (sig_valid sig /\
     LENGTH bytelist_A = 32 /\ ed25519_valid_bytelist bytelist_A)`;;

let verify = define
  `verify (alg : num) (ctx : byte list) (bytelist_A : byte list) (sig : byte list) (m : byte list) =
    let bytelist_R = SUB_LIST (0, 32) sig in
    let bytelist_S = SUB_LIST (32, 32) sig in
    let enc_R = num_of_bytelist bytelist_R : num in
    let dec_R = ed25519_decode enc_R : int#int in
    let sig_S = num_of_bytelist bytelist_S : num in
    let enc_A = num_of_bytelist bytelist_A : num in
    let dec_A = ed25519_decode enc_A : int#int in
    let dom2 = dom2_of alg ctx in
    let bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph alg m) in
    let k = num_of_bytelist bytelist_k : num in
    let sig_S_B = group_pow edwards25519_group E_25519 sig_S in
    let kA = group_pow edwards25519_group dec_A (k MOD n_25519) in
    sig_S_B = group_mul edwards25519_group dec_R kA`;;

let rfc_verify = define
  `rfc_verify (alg : num) (ctx : byte list) (bytelist_A : byte list) (sig : byte list) (m : byte list) =
    let bytelist_R = SUB_LIST (0, 32) sig in
    let bytelist_S = SUB_LIST (32, 32) sig in
    let enc_R = num_of_bytelist bytelist_R : num in
    let dec_R = ed25519_decode enc_R : int#int in
    let sig_S = num_of_bytelist bytelist_S : num in
    let enc_A = num_of_bytelist bytelist_A : num in
    let dec_A = ed25519_decode enc_A : int#int in
    let dom2 = dom2_of alg ctx in
    let bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph alg m) in
    let k = num_of_bytelist bytelist_k : num in
    let sig_S_B = group_pow edwards25519_group E_25519 (8 * sig_S) in
    let kA = group_pow edwards25519_group dec_A (8 * k) in
    let mul_8_R = group_pow edwards25519_group dec_R 8 in
    sig_S_B = group_mul edwards25519_group mul_8_R kA`;;


let P25519_NEQ_0 = prove
  (`~(p_25519 = 0)`, REWRITE_TAC [p_25519] THEN ARITH_TAC);;

let ED25519_ENCODE_LT_256_EXP_32 = prove
  (`!xy. ed25519_encode xy < 256 EXP 32`,
  STRIP_TAC THEN
    ONCE_REWRITE_TAC [ISPEC `xy:int#int` (GSYM PAIR)] THEN
    PURE_REWRITE_TAC [ed25519_encode] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    ASSUME_TAC (ARITH_RULE
      `2 EXP 255 * num_of_int (FST (xy:int#int) rem &p_25519) MOD 2 <= 2 EXP 255`) THEN
    SUBGOAL_THEN `p_25519 < 2 EXP 255` ASSUME_TAC THENL
    [ REWRITE_TAC [p_25519] THEN ARITH_TAC; ALL_TAC ] THEN
    SUBGOAL_THEN `num_of_int (SND (xy:int#int) rem &p_25519) < p_25519` ASSUME_TAC THENL
    [ REWRITE_TAC [GSYM INT_OF_NUM_LT] THEN
        IMP_REWRITE_TAC [INT_OF_NUM_OF_INT] THEN
        SIMP_TAC [INT_REM_POS; P25519_NEQ_0; INT_OF_NUM_EQ] THEN
        MATCH_MP_TAC INT_LT_REM THEN
        REWRITE_TAC [INT_OF_NUM_LT; p_25519; ARITH];
      ALL_TAC ] THEN
    SIMPLE_ARITH_TAC);;

let ED25519_ENCODE_DECODE = prove
  (`!n. ed25519_validencode n ==> 
    ed25519_decode n IN group_carrier edwards25519_group /\
    ed25519_encode (ed25519_decode n) = n`,
  REWRITE_TAC [ed25519_validencode; ed25519_decode] THEN
    MESON_TAC []);;

let ED25519_DECODE_ENCODE = prove
  (`!P. P IN group_carrier edwards25519_group ==>
    ed25519_decode (ed25519_encode P) = P`,
  REWRITE_TAC [ed25519_decode] THEN
    MESON_TAC [ED25519_ENCODE_INJECTIVE]);;

let SIGN_IMP_VERIFY = prove
  (`!sig alg ctx seed m. sig = sign alg ctx seed m ==>
    verify alg ctx (public_key_of_seed seed) sig m = true`,
  REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [sign; verify; public_key_of_seed] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `prefix = SUB_LIST (32,32) (sha512_pad seed)` THEN
    ABBREV_TAC `r = num_of_bytelist (sha512_pad (dom2_of alg ctx ++ prefix ++ ph alg m))` THEN
    ABBREV_TAC `r_B = group_pow edwards25519_group E_25519 r` THEN
    ABBREV_TAC `secret_s = num_of_bytelist (secret_scalar_of_seed_digest (sha512_pad seed))` THEN
    ABBREV_TAC `s_B = group_pow edwards25519_group E_25519 secret_s` THEN
    ABBREV_TAC `k = num_of_bytelist (sha512_pad (dom2_of alg ctx ++ bytelist_of_num 32 (ed25519_encode r_B) ++
      bytelist_of_num 32 (ed25519_encode s_B) ++ ph alg m))` THEN
    IMP_REWRITE_TAC [SPECL [`0`; `32`] SUB_LIST_APPEND_L] THEN
    IMP_REWRITE_TAC [SPECL [`32`; `32`] SUB_LIST_APPEND_R] THEN
    REWRITE_TAC [LENGTH_BYTELIST_OF_NUM; ARITH] THEN
    SUBGOAL_THEN `!n. SUB_LIST (0, LENGTH (bytelist_of_num 32 n)) (bytelist_of_num 32 n) = bytelist_of_num 32 n` MP_TAC THENL
    [ REWRITE_TAC [SUB_LIST_LENGTH]; ALL_TAC ] THEN
    REWRITE_TAC [LENGTH_BYTELIST_OF_NUM] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    ASM_REWRITE_TAC [] THEN
    SIMP_TAC [NUM_OF_BYTELIST_OF_NUM_EQ; ED25519_ENCODE_LT_256_EXP_32] THEN
    IMP_REWRITE_TAC [NUM_OF_BYTELIST_OF_NUM_EQ] THEN
    CONJ_TAC THENL [ ALL_TAC; REWRITE_TAC [n_25519] THEN ARITH_TAC ] THEN
    ONCE_REWRITE_TAC [GSYM MOD_ADD_MOD] THEN
    SUBGOAL_THEN `!x. group_pow edwards25519_group E_25519 (x MOD n_25519) =
      group_pow edwards25519_group E_25519 x` ASSUME_TAC THENL
    [ REWRITE_TAC [GSYM GROUP_ELEMENT_ORDER_EDWARDS25519_E25519] THEN
        SIMP_TAC [GROUP_POW_MOD_ELEMENT_ORDER; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519];
      ALL_TAC ] THEN
    ASM_REWRITE_TAC [] THEN
    SIMP_TAC [GROUP_POW_ADD; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
    FIRST_ASSUM (fun th -> (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th])) THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    ONCE_REWRITE_TAC [GSYM MOD_MULT_MOD2] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [GROUP_POW_MUL; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
    SUBGOAL_THEN `group_pow edwards25519_group E_25519 r IN group_carrier edwards25519_group` MP_TAC THENL
    [ SIMP_TAC [GROUP_POW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]; ALL_TAC ] THEN
    SUBGOAL_THEN `group_pow edwards25519_group E_25519 secret_s IN group_carrier edwards25519_group` MP_TAC THENL
    [ SIMP_TAC [GROUP_POW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]; ALL_TAC ] THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC [ED25519_DECODE_ENCODE]);;


let VERIFY_IMP_RFC_VERIFY = prove
  (`!alg ctx bytelist_A sig m.
    verify_args_valid bytelist_A sig /\ verify alg ctx bytelist_A sig m ==>
    rfc_verify alg ctx bytelist_A sig m`,
  REPEAT GEN_TAC THEN
    REWRITE_TAC [verify_args_valid; sig_valid; ed25519_valid_bytelist; verify; rfc_verify] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `R = num_of_bytelist (SUB_LIST (0,32) sig)` THEN
    ABBREV_TAC `A = num_of_bytelist bytelist_A` THEN
    ABBREV_TAC `k = num_of_bytelist (sha512_pad (dom2_of alg ctx ++ SUB_LIST (0,32) sig ++ bytelist_A ++ ph alg m))` THEN
    ABBREV_TAC `S = num_of_bytelist (SUB_LIST (32,32) sig)` THEN
    STRIP_TAC THEN
    ABBREV_TAC `dec_R = ed25519_decode R` THEN
    SUBGOAL_THEN `dec_R IN group_carrier edwards25519_group` ASSUME_TAC THENL
    [ ASM_MESON_TAC [ed25519_decode; ed25519_validencode]; ALL_TAC ] THEN
    ABBREV_TAC `dec_A = ed25519_decode A` THEN
    SUBGOAL_THEN `dec_A IN group_carrier edwards25519_group` ASSUME_TAC THENL
    [ ASM_MESON_TAC [ed25519_decode; ed25519_validencode]; ALL_TAC ] THEN
    REWRITE_TAC [MULT_SYM] THEN
    SIMP_TAC [GROUP_POW_MUL; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
    ASM_SIMP_TAC [ABELIAN_EDWARDS25519_GROUP; ABELIAN_GROUP_MUL_POW; GROUP_POW] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC [GROUP_POW_POW] THEN
    SUBGOAL_THEN `k MOD n_25519 * 8 = (k * 8) MOD (8 * n_25519)` MP_TAC THENL
    [ ONCE_REWRITE_TAC [MULT_SYM] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM MOD_MULT2] THEN
        REWRITE_TAC [MULT_SYM];
      ALL_TAC ] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC SIZE_EDWARDS25519_GROUP THEN
    REWRITE_TAC [HAS_SIZE] THEN
    STRIP_TAC THEN
    FIRST_ASSUM (fun th -> REWRITE_TAC [GSYM th]) THEN
    ASM_SIMP_TAC [GROUP_POW_MOD_ORDER]);;

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
    let kA = group_pow edwards25519_group dec_A k in
    sig_S_B = group_mul edwards25519_group dec_R kA`;;

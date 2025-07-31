needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";; ?may not need this
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

let bignum_of_bytelist = define
  `bignum_of_bytelist [] = 0 /\
   bignum_of_bytelist (CONS h t : byte list) = val h + 2 EXP 8 * bignum_of_bytelist t`;;

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

let dom2_valid = define
  `dom2_valid (alg : num) (ctxt : byte list) =
    (LENGTH ctxt <= 255 /\
     if alg = 0 then ctxt = []
     else if alg = 1 then ~(ctxt = [])
     else alg = 2)`;;

let public_key_of_seed = define
  `public_key_of_seed seed : byte list =
    let h = sha512_pad seed in
    let bytelist_s = secret_scalar_of_seed_digest h in
    let secret_s = bignum_of_bytelist bytelist_s : num in
    let s_B = group_pow edwards25519_group E_25519 secret_s : int#int in
    let enc_A = ed25519_encode s_B : num in
    let bytelist_A = bytelist_of_num 32 enc_A in
    bytelist_A`;;

let ph = define
  `ph alg = if alg = 2 then sha512_pad else \x.x`;;

let dom2_of = define
  `dom2_of alg ctx =
    if alg = 0 then []
      else dom2_prefix ++ [word (phflag alg)] ++ [word (LENGTH ctxt)] ++ ctxt`;;

let sign_args_valid = define
  `sign_args_valid (seed : byte list) =
    LENGTH seed = 32`;;

let sign = define
  `sign (alg : num) (ctxt : byte list) (seed : byte list) (m : byte list) =
    let h = sha512_pad seed in
    let bytelist_s = secret_scalar_of_seed_digest h in
    let secret_s = bignum_of_bytelist bytelist_s : num in
    let s_B = group_pow edwards25519_group E_25519 secret_s : int#int in
    let enc_A = ed25519_encode s_B : num in
    let bytelist_A = bytelist_of_num 32 enc_A in
    let prefix = SUB_LIST (32, 32) h in
    let dom2 = dom2_of alg ctx in
    let bytelist_r = sha512_pad (dom2 ++ prefix ++ ph alg m) in
    let r = bignum_of_bytelist bytelist_r : num in
    let r_B = group_pow edwards25519_group E_25519 r in
    let enc_R = ed25519_encode r_B : num in
    let bytelist_R = bytelist_of_num 32 enc_R in
    let bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph alg m) in
    let k = bignum_of_bytelist bytelist_k : num in
    let sig_S = (r + k * secret_s) MOD n_25519 in
    let bytelist_S = bytelist_of_num 32 sig_S in
    let sig = bytelist_R ++ bytelist_S in
    sig`;;

let ed25519_valid_bytelist = define
  `ed25519_valid_bytelist bytelist_P =
    ed25519_validencode (bignum_of_bytelist bytelist_P)`;;

let sig_valid = define
  `sig_valid (sig : byte list) =
    (LENGTH sig = 64 /\
     ed25519_valid_bytelist (SUB_LIST (0, 32) sig) /\
     bignum_of_bytelist (SUB_LIST (32, 32) sig) < n_25519)`;;

let verify_args_valid = define
  `verify_args_valid (bytelist_A : byte list) (sig : byte list) =
    (sig_valid sig /\
     LENGTH bytelist_A = 32 /\ ed25519_valid_bytelist bytelist_A)`;;

let verify = define
  `verify (alg : num) (ctxt : byte list) (bytelist_A : byte list) (sig : byte list) (m : byte list) =
    let bytelist_R = SUB_LIST (0, 32) sig in
    let bytelist_S = SUB_LIST (32, 32) sig in
    let enc_R = bignum_of_bytelist bytelist_R : num in
    let dec_R = ed25519_decode enc_R : int#int in
    let sig_S = bignum_of_bytelist bytelist_S : num in
    let enc_A = bignum_of_bytelist bytelist_A : num in
    let dec_A = ed25519_decode enc_A : int#int in
    let dom2 = dom2_of alg ctxt in
    let bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph alg m) in
    let k = bignum_of_bytelist bytelist_k : num in
    let sig_S_B = group_pow edwards25519_group E_25519 sig_S in
    let kA = group_pow edwards25519_group dec_A k in
    sig_S_B = group_mul edwards25519_group dec_R kA`;;



(* Pre- and post-conditions of Ed25519 subroutines - integration plan version 1 *)
void ed25519_keypair_from_seed_s2n_bignum (
  uint8_t out_public_key[ED25519_PUBLIC_KEY_LEN],
  const uint8_t seed[ED25519_SEED_LEN])
Pre:
  `seed` contains `seed_v` and `LENGTH seed_v = ED25519_SEED_LEN`
Post:
  `out_public_key` contains `public_key_of_seed seed_v`


int ed25519_sign_internal_s2n_bignum (
  ed25519_algorithm_t alg,
  uint8_t out_sig[ED25519_SIGNATURE_LEN],
  const uint8_t *message, size_t message_len,
  const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
  const uint8_t *ctx, size_t ctx_len)
Pre:
  `message` contains `ph alg m` and `message_len = LENGTH (ph alg m)`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `dom2_valid alg ctxt` then return `1` and `out_sig` contains `sign alg ctxt seed_v m`
  else return `0`
     

int ed25519_verify_internal_s2n_bignum (
  ed25519_algorithm_t alg,
  const uint8_t *message, size_t message_len,
  const uint8_t signature[ED25519_SIGNATURE_LEN],
  const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
  const uint8_t *ctx, size_t ctx_len)
Pre:
  `message` contains `ph alg m` and `message_len = LENGTH (ph alg m)`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `dom2_valid alg ctxt` then
    if `verify_args_valid bytelist_A sig /\ verify alg ctxt bytelist_A sig m`
    then return 1
    else return 0
  else return 2


int dom2_s2n_bignum (
  ed25519_algorithm_t alg,
  uint8_t dom2_buffer[MAX_DOM2_SIZE], uint64_t &dom2_buffer_len,
  uint8_t *ctx, size_t ctx_len)
Pre: `ctx` contains `ctxt` and `ctx_len = LENGTH ctxt`
Post:
  if `dom2_valid alg ctxt`
  then return `1` and `dom2_buffer` contains `dom2_of alg ctxt` and
    `dom2_buffer_len = LENGTH (dom2_of alg ctxt) <= MAX_DOM2_SIZE`
  else return `0`



(* Pre- and post-conditions of Ed25519 subroutines - integration plan version 2 *)
The checks for `message_len = SHA512_DIGEST_LENGTH` in the case of Ed25519ph in the internal functions become unnecessary.

int ED25519_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN])
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
Post:
  return `1` and `out_sig` contains `sign 0 [] seed_v m`


int ED25519_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN])
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
Post: 
  if `verify_args_valid bytelist_A sig /\ verify 0 [] bytelist_A sig m`
  then return 1
  else return 0

int ED25519ctx_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `0 < ctx_len <= 255 ` then return `1` and `out_sig` contains `sign 1 ctxt seed_v m`
  else return `0`


int ED25519ctx_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `0 < ctx_len <= 255 /\ verify_args_valid bytelist_A sig /\ verify 1 ctxt bytelist_A sig m`
  then return 1
  else return 0


int ED25519ph_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `ctx_len <= 255 ` then return `1` and `out_sig` contains `sign 2 ctxt seed_v (sha512_pad m)`
  else return `0`


int ED25519ph_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `ctx` contains `ctxt` and `LENGTH ctxt = ctx_len`
Post: 
  if `ctx_len <= 255 /\ verify_args_valid bytelist_A sig /\ verify 2 ctxt bytelist_A sig (sha512_pad m)`
  then return 1
  else return 0

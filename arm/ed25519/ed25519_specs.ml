Initial draft:

Public key generation:
private_key : byte list (LENGTH = 32)
h = sha512_pad private_key : byte list (LENGTH = 64)
bytelist_s = [(HD h) && 0b11111000] ++ SUB_LIST (1, 30) h ++ [EL 31 h && 0b01111111 || 0b01000000]
secret_s = bignum_of_bytelist bytelist_s : num
sB = group_pow edwards25519_group E_25519 secret_s : int#int
enc_A = ed25519_encode sB : num
bytelist_A = bytelist_of_num 32 enc_A

Sign:
m : byte list (LENGTH m < 2 EXP 64)
alg : num (0 for Ed25519, 1 for Ed25519ctx, 2 for Ed25519ph, else invalid)
phflag = if alg = 2 then 1 else 0 : byte
ctxt = byte list (LENGTH < 256)
dom2_prefix : byte list (LENGTH = 32)
dom2 = if alg = 0 then []
    else dom2_prefix ++ [phflag] ++ [word (LENGTH ctxt)] ++ ctxt : byte list
prefix = SUB_LIST (32, 32) h
ph = if phflag == 0 then \x.x else sha512_pad : byte list -> byte list
bytelist_r = sha512_pad (dom2 ++ prefix ++ ph(m))
r = bignum_of_bytelist bytelist_r : num
rB = group_pow edwards25519_group E_25519 r
enc_R = ed25519_encode rB : num
bytelist_R = bytelist_of_num 32 enc_R
bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph m)
k = bignum_of_bytelist bytelist_k : num
sig_S = (r + k * secret_s) MOD n_25519
bytelist_S = bytelist_of_num 32 sig_S
signature = bytelist_R ++ bytelist_S

Verify:
signature : byte list (LENGTH 64)
bytelist_A : byte list (LENGTH 32)
m : byte list (LENGTH < 2 EXP 64)
bytelist_R = SUB_LIST (0, 32) signature
bytelist_S = SUB_LIST (32, 32) signature
enc_R = bignum_of_bytelist bytelist_R : num
dec_R = ed25519_decode enc_R : int#int (may fail)
sig_S = bignum_of_bytelist bytelist_S : num (sig_S < n_25519 else fail)
enc_A = bignum_of_bytelist bytelist_A : num
dec_A = ed25519_decode enc_A : int#int (may fail)
bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph m)
k = bignum_of_bytelist bytelist_k : num
sig_SB = group_pow edwards25519_group E_25519 sig_S : int#int
kA = group_pow edwards25519_group dec_A k : int#int
computed_R = group_mul edwards25519_group sig_SB (group_inv edwards25519_group kA) : int#int
enc_computed_R = ed25519_encode computed_R
bytelist_computed_R = bytelist_of_num 32 enc_computed_R

Need:
bytelist_of_num 32 (ed25519_encode R) = bytelist_of_num 32 (ed25519_encode R') ==> R = R'
or change the implementation to compute the point R + [k]A and do point comparison.


parse_as_infix ("++", (13, "right"));;
override_interface("++", `APPEND`);;
parse_as_infix("&&",(13,"right"));;
override_interface("&&",`word_and:N word->N word->N word`);;
parse_as_infix("||",(13,"right"));;
override_interface("||",`word_or:N word->N word->N word`);;

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

let seed_valid = define
  `seed_valid (seed : byte list) = LENGTH seed = 32`;;

let dom2_valid = define
  `dom2_valid (alg : num) (ctxt : byte list) =
    (LENGTH ctxt < 256 /\
     if alg = 0 then ctxt = []
     else if alg = 1 then ~(ctxt = [])
     else alg = 2)`;;

(* ===== from ed25519_decode.ml ===== *)
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
(* ===== ??? Which files do we import for Ed25519 specs?
needs "arm/proofs/base.ml";;
needs "common/ecencoding.ml";;
needs "EC/edwards25519.ml";;
repeat the definitions above or import the entire edwards25519_decode.ml file along with the proofs? ===== *)

let public_key_of_seed = define
  `public_key_of_seed seed : byte list =
    let h = sha512_pad seed in
    let bytelist_s = secret_scalar_of_seed_digest h in
    let secret_s = bignum_of_bytelist bytelist_s : num in
    let sB = group_pow edwards25519_group E_25519 secret_s : int#int in
    let enc_A = ed25519_encode sB : num in
    let bytelist_A = bytelist_of_num 32 enc_A in
    bytelist_A`;;

let sign_args_valid = define
  `sign_args_valid (alg : num) (ctxt : byte list) =
    dom2_valid alg ctxt`;;
     (* ??? not checking length of seed *)

let sign = define
  `sign (alg : num) (ctxt : byte list) (seed : byte list) (m : byte list) =
    let h = sha512_pad seed in
    let bytelist_s = secret_scalar_of_seed_digest h in
    let secret_s = bignum_of_bytelist bytelist_s : num in
    let sB = group_pow edwards25519_group E_25519 secret_s : int#int in
    let enc_A = ed25519_encode sB : num in
    let bytelist_A = bytelist_of_num 32 enc_A in
    let prefix = SUB_LIST (32, 32) h in
    let dom2 =
      if alg = 0 then []
      else dom2_prefix ++ [word (phflag alg)] ++ [word (LENGTH ctxt)] ++ ctxt in
    let ph = if alg = 2 then sha512_pad else \x.x in
    let bytelist_r = sha512_pad (dom2 ++ prefix ++ ph m) in
    let r = bignum_of_bytelist bytelist_r : num in
    let rB = group_pow edwards25519_group E_25519 r in
    let enc_R = ed25519_encode rB : num in
    let bytelist_R = bytelist_of_num 32 enc_R in
    let bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph m) in
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
  `verify_args_valid (alg : num) (ctxt : byte list) (bytelist_A : byte list) (sig : byte list) =
    (dom2_valid alg ctxt /\
     sig_valid sig /\
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
    let dom2 =
      if alg = 0 then []
      else dom2_prefix ++ [word (phflag alg)] ++ [word (LENGTH ctxt)] ++ ctxt in
    let ph = if alg = 2 then sha512_pad else \x.x in
    let bytelist_k = sha512_pad (dom2 ++ bytelist_R ++ bytelist_A ++ ph m) in
    let k = bignum_of_bytelist bytelist_k : num in
    let sig_SB = group_pow edwards25519_group E_25519 sig_S in
    let kA = group_pow edwards25519_group dec_A k in
    sig_SB = group_mul edwards25519_group dec_R kA`;;
    (* ??? the implementation computes [S]B - [k]A and compares its bytelist encoding against enc_R
      The specification says "Check [S]B = R + [k]A. Why use subtraction in computation?
      Can compare int#int for equality in the specification? Canonical form? *)
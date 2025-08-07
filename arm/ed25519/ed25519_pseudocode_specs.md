(* Pre- and post-conditions of Ed25519 subroutines *)
void ed25519_keypair_from_seed_s2n_bignum (
  uint8_t out_public_key[ED25519_PUBLIC_KEY_LEN],
  const uint8_t seed[ED25519_SEED_LEN])
Pre:
  `seed` contains `seed_v` and `LENGTH seed_v = ED25519_SEED_LEN`
Post:
  `out_public_key` contains `public_key_of_seed seed_v`


size_t dom2_common(
    uint8_t dom2_buffer[MAX_DOM2_SIZE], const uint64_t phflag,
    const uint8_t *context, size_t context_len)
Pre:
  `context` contains `ctx` and `context_len = LENGTH ctx`
  `context_len <= 255`
Post:
  `dom2_buffer` contains `dom2_prefix ++ [word phflag] ++ [word context_len] ++ ctx` and
  return `LENGTH (dom2_prefix ++ [word phflag] ++ [word context_len] ++ ctx)`


void ed25519_sign_common(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len)
Pre:
  `message` contains `ph alg m` and `message_len = LENGTH (ph alg m)`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `dom2_valid alg ctx` and
  `dom2_buffer` contains `dom2_of alg ctx` and `dom2_buffer_len = LENGTH (dom2_of alg ctx)`
Post: 
  `out_sig` contains `sign alg ctx seed_v m`
  (* Note when each of our three top-level signing functions calls this subroutine,
     dom2-related pre-conditions must be true *)


int ed25519_verify_common(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len)
Pre:
  `message` contains `ph alg m` and `message_len = LENGTH (ph alg m)`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `dom2_valid alg ctx` and
  `dom2_buffer` contains `dom2_of alg ctx` and `dom2_buffer_len = LENGTH (dom2_of alg ctx)`
Post: 
  if `verify_args_valid bytelist_A sig /\ verify alg ctx bytelist_A sig m`
  then return 1
  else return 0
  (* Note when each of our three top-level signing functions calls this subroutine,
     dom2-related pre-conditions must be true *)


int ed25519_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN])
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
Post:
  return `1` and `out_sig` contains `sign 0 [] seed_v m`


int ed25519_verify_no_self_test_s2n_bignum(
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


int ed25519ctx_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `ctx` contains `ctx` and `LENGTH ctx = ctx_len`
Post: 
  if `0 < ctx_len <= 255 ` then return `1` and `out_sig` contains `sign 1 ctx seed_v m`
  else return `0`


int ed25519ctx_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `ctx` contains `ctx` and `LENGTH ctx = ctx_len`
Post: 
  if `0 < ctx_len <= 255 /\ verify_args_valid bytelist_A sig /\ verify 1 ctx bytelist_A sig m`
  then return 1
  else return 0


int ed25519ph_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `private_key` contains `seed_v ++ bytelist_A` and
    `LENGTH private_key = 64` and `bytelist_A = public_key_of_seed seed_v`
  `ctx` contains `ctx` and `LENGTH ctx = ctx_len`
Post: 
  if `ctx_len <= 255 ` then return `1` and `out_sig` contains `sign 2 ctx seed_v (sha512_pad m)`
  else return `0`


int ed25519ph_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len)
Pre:
  `message` contains `m` and `message_len = LENGTH m`
  `signature` contains `sig` and `LENGTH sig = ED25519_SIGNATURE_LEN`
  `public_key` contains `bytelist_A` and `LENGTH bytelist_A = ED25519_PUBLIC_KEY_LEN`
  `ctx` contains `ctx` and `LENGTH ctx = ctx_len`
Post: 
  if `ctx_len <= 255 /\ verify_args_valid bytelist_A sig /\ verify 2 ctx bytelist_A sig (sha512_pad m)`
  then return 1
  else return 0

#include <stdint.h>

void ed25519_keypair_from_seed_s2n_bignum (
  uint8_t A[ED25519_PUBLIC_KEY_LEN],
  const uint8_t seed[ED25519_SEED_LEN]){
  // Ed25519 key generation: rfc8032 5.1.5
  
  // Step: rfc8032 5.1.5.1
  // Compute SHA512(seed).
  // Through sha512_init, sha512_update, sha512_final
  uint8_t h[SHA512_DIGEST_LENGTH];
  h[0:63] = sha512_s2n_bignum(seed[0:31]);

  // Step: rfc8032 5.1.5.2
  // Clamp h[0:31]
  h[0] &= 248; // 11111000_2
  h[31] &= 127; // 01111111_2
  h[31] |= 64; // 01000000_2

  // Step: rfc8032 5.1.5.3
  // Compute [s]B and encode public key to a 32 byte octet
  //   where s = h[0:31]
  uint64_t s_B[8] = {0};
  edwards25519_scalarmulbase_selector(s_B, h);
  
  // Step: rfc8032 5.1.5.4
  edwards25519_encode(A, s_B);
}

void ed25519_sign_common(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    uint8_t *dom2_buffer, size_t dom2_buffer_len) {
  // Ed25519 sign: rfc8032 5.1.6

  // Step: rfc8032 5.1.6.1
  // This step is a repeat of rfc8032 5.1.5.[1,2].
  // seed = private_key[0:31]
  // Compute h = SHA512(seed).
  // Through sha512_init, sha512_update, sha512_final
  uint8_t h[SHA512_DIGEST_LENGTH];
  h[0:63] = sha512_s2n_bignum(private_key[0:31]);
  // Clamp h[0:31]
  h[0] &= 248; // 11111000_2
  h[31] &= 63; // 00111111_2
  h[31] |= 64; // 01000000_2
  
  // Step: rfc8032 5.1.6.2
  // prefix = h[32:63]
  uint8_t r[SHA512_DIGEST_LENGTH];
  r[0:63] = sha512_s2n_bignum(dom2_buffer || h[32:63] || message);

  // Step: rfc8032 5.1.6.3
  uint64_t r_B[8];

  // Reduce r modulo the order of the base-point B.
  bignum_mod_n25519(r, 8, r);

  // Compute [r]B.
  edwards25519_scalarmulbase_selector(r_B, r);
  edwards25519_encode(out_sig, r_B);
  
  // Step: rfc8032 5.1.6.4
  // R = out_sig[0:31]
  // A = private_key[32:63]
  uint8_t k[SHA512_DIGEST_LENGTH];
  k[0:63] = sha512_s2n_bignum(dom2_buffer || out_sig[0:31] || private_key[32:63] || message);
  
  // Step: rfc8032 5.1.6.5
  // Compute S = r + k * s modulo the order of the base-point B
  //   where s = h[0:31]
  // Step: rfc8032 5.1.6.6
  // out_sig = R || S
  bignum_mod_n25519(k, 8, k);
  bignum_madd_n25519_selector(out_sig + 32, k, s, r);
}

int ed25519_verify_common(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
    const uint8_t *dom2_buffer, size_t dom2_buffer_len) {
  // Ed25519 verify: rfc8032 5.1.7
  
  // Step: rfc8032 5.1.7.1
  // Decode signature as:
  //  - signature[0:31]: encoded point R.
  //  - signature[32:63]: integer S.

  // S must be in the range [0, ORDER) in order to prevent signature
  // malleability. ORDER is the order of curve25519 in little-endian form.
  uint8_t order[32] = ORDER;
  if (bignum_le(32, order, 32, signature + 32)) return 0;
  
  // Decode public key as A.
  uint64_t A[8];
  if (edwards25519_decode_selector(A, public_key) != 0) {
    return 0;
  }

  // Step: rfc8032 5.1.7.2
  uint8_t k[SHA512_DIGEST_LENGTH];
  k[0:63] = sha512_s2n_bignum(dom2_buffer || signature[0:31] || public_key || message).

  // Step: rfc8032 5.1.7.3
  // Recall, we must compute [S]B - [k]A'.
  // First negate A'. Point negation for the twisted edwards curve when points
  // are represented in the extended coordinate system is simply:
  //   -(X,Y,Z,T) = (-X,Y,Z,-T).
  // See "Twisted Edwards curves revisited" https://ia.cr/2008/522.
  // In standard coordinates, that is simply negating the x coordinate.
  // See rfc8032 5.1.4.
  bignum_neg_p25519(A, A);

  // Compute R_computed <- [S]B - [k]A'.
  uint64_t R_computed[8];
  uint8_t R_computed_encoded[32];
  bignum_mod_n25519(k, 8, k);
  edwards25519_scalarmuldouble_selector(R_computed, k, A, signature[32:63]);
  edwards25519_encode(R_computed_encoded, signature[0:31]);                            
                                  
  // Comparison [S]B - [k]A' =? R_expected.
  return memcmp(R_computed_encoded, signature[0:31], sizeof(R_computed_encoded)) == 0;
}

/* Pure Ed25519 */

int ed25519_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN]) {

  ed25519_sign_common(out_sig, message, message_len, private_key, NULL, 0);
  return 1;
}

int ed25519_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN]) {
  
  return ed25519_verify_common(
    message, message_len, signature[ED25519_SIGNATURE_LEN],
    public_key[ED25519_PUBLIC_KEY_LEN], NULL, 0);
}

/* Ed25519ctx */

int ed25519ctx_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len) {

  // Ed25519ctx requires a non-empty context at most 255 bytes long
  if (ctx_len = 0 || ctx_len > 255) {
     return 0;
  }
  // DOM2_PREFIX[0:32] = "SigEd25519 no Ed25519 collisions"
  dom2_buffer[MAX_DOM2_SIZE] =
     DOM2_PREFIX || 0x00 || (uint8_t) ctx_len || context[0:ctx_len - 1];

  ed25519_sign_common(out_sig, message, message_len, private_key,
    dom2_buffer, length(dom2_buffer));
  return 1;
}

int ed25519ctx_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len) {
  
  // Ed25519ctx requires a non-empty context at most 255 bytes long
  if (ctx_len = 0 || ctx_len > 255) {
     return 0;
  }
  // DOM2_PREFIX[0:32] = "SigEd25519 no Ed25519 collisions"
  dom2_buffer[MAX_DOM2_SIZE] =
     DOM2_PREFIX || 0x00 || (uint8_t) ctx_len || context[0:ctx_len - 1];
  
  return ed25519_verify_common(
    message, message_len, signature[ED25519_SIGNATURE_LEN],
    public_key[ED25519_PUBLIC_KEY_LEN], dom2_buffer, length(dom2_buffer));
}

/* Ed25519ph */

int ed25519ph_sign_no_self_test_s2n_bignum(
    uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
    size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
    const uint8_t *context, size_t context_len) {

  // Ed25519ph requires a context at most 255 bytes long
  if (ctx_len > 255) {
      return 0;
  }
  uint8_t dom2_buffer[MAX_DOM2_SIZE];
  // DOM2_PREFIX[0:32] = "SigEd25519 no Ed25519 collisions"
  dom2_buffer =
      DOM2_PREFIX || 0x01 || (uint8_t) ctx_len || context[0:ctx_len - 1];
  // Pre-hashing for Ed25519ph
  uint8_t digest[SHA512_DIGEST_LENGTH];
  digest[0:64] = sha512_s2n_bignum(message);

  ed25519_sign_common(out_sig, digest, SHA512_DIGEST_LEN, private_key,
    dom2_buffer, length(dom2_buffer));
  return 1;
}

int ed25519ph_verify_no_self_test_s2n_bignum(
    const uint8_t *message, size_t message_len,
    const uint8_t signature[ED25519_SIGNATURE_LEN],
    const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], const uint8_t *context,
    size_t context_len) {
  // Ed25519ph requires a context at most 255 bytes long
  if (ctx_len > 255) {
      return 0;
  }
  uint8_t dom2_buffer[MAX_DOM2_SIZE];
  // DOM2_PREFIX[0:32] = "SigEd25519 no Ed25519 collisions"
  dom2_buffer =
      DOM2_PREFIX || 0x01 || (uint8_t) ctx_len || context[0:ctx_len - 1];
  // Pre-hashing for Ed25519ph
  uint8_t digest[SHA512_DIGEST_LENGTH];
  digest[0:64] = sha512_s2n_bignum(message);
  
  return ed25519_verify_common(
    digest, SHA512_DIGEST_LEN, signature[ED25519_SIGNATURE_LEN],
    public_key[ED25519_PUBLIC_KEY_LEN], dom2_buffer, length(dom2_buffer));
  }
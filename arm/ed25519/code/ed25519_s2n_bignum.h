#include <stdint.h>

#define ED25519_SEED_LEN 32
#define ED25519_PUBLIC_KEY_LEN 32
#define ED25519_SIGNATURE_LEN 64
#define ED25519_PRIVATE_KEY_LEN 64

void ed25519_public_key_from_seed_s2n_bignum (
						uint8_t A[ED25519_PUBLIC_KEY_LEN],
						const uint8_t seed[ED25519_SEED_LEN]);

int ed25519_sign_no_self_test_s2n_bignum(
						uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
						size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN]);

int ed25519_verify_no_self_test_s2n_bignum(
						const uint8_t *message, size_t message_len,
						const uint8_t signature[ED25519_SIGNATURE_LEN],
						const uint8_t public_key[ED25519_PUBLIC_KEY_LEN]);

int ed25519ctx_sign_no_self_test_s2n_bignum(
						uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
						size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
						const uint8_t *context, size_t context_len);

int ed25519ctx_verify_no_self_test_s2n_bignum(
						const uint8_t *message, size_t message_len,
						const uint8_t signature[ED25519_SIGNATURE_LEN],
						const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
						const uint8_t *context, size_t context_len);

int ed25519ph_sign_no_self_test_s2n_bignum(
						uint8_t out_sig[ED25519_SIGNATURE_LEN], const uint8_t *message,
						size_t message_len, const uint8_t private_key[ED25519_PRIVATE_KEY_LEN],
						const uint8_t *context, size_t context_len) ;

int ed25519ph_verify_no_self_test_s2n_bignum(
						const uint8_t *message, size_t message_len,
						const uint8_t signature[ED25519_SIGNATURE_LEN],
						const uint8_t public_key[ED25519_PUBLIC_KEY_LEN],
						const uint8_t *context, size_t context_len);
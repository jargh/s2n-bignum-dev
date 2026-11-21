# Findings from the machine-code proofs of the kernel WireGuard handshake

Status: logged only. Which of these, if any, to report or fix is to be
decided at the end of the project.

Target: Linux 6.18.64 LTS, drivers/net/wireguard and the generic C crypto of
lib/crypto, compiled by gcc 13 -O2 for AArch64 (the image wireguard.so,
SHA-256 a110b25831dd6b6cc765db2bd699c000fa1d1a8880774cbd729e3cf73690f6a3).
Each finding names the spec file (in gcc13_O2/) whose theorem shows it.

## Secrets left in memory

F1. xchacha20poly1305_decrypt (lib/crypto/chacha20poly1305.c) never wipes
its ChaCha20 state, which holds the subkey that HChaCha20 derives from the
key and nonce: xchacha_init builds it on the stack, the inner decryption
does not clear it, and nor does the function. chacha20poly1305_decrypt, the
96-bit-nonce version, does wipe its state. In WireGuard the function only
decrypts cookie replies, whose key is derived from a public key, so the
material is of little value there, but the function is a library API.
(xchacha20poly1305_decrypt_spec.ml)

F2. chacha_crypt (chacha_crypt_generic in lib/crypto/chacha.c) leaves the
last keystream block in its 64-byte stack buffer. Together with the
ciphertext, which is public, that gives the plaintext of the last block, so
it matters only with a separate bug that discloses old stack contents. The
buffer is zero at entry only because the kernel zero-initializes stack
variables (CONFIG_INIT_STACK_ALL_ZERO). (chacha_crypt_spec.ml)

F3. cookie.c does not wipe its stack copies:
- the cookie in wg_cookie_message_create;
- the MACs that wg_cookie_validate_packet computes, to compare them with the
  packet's;
- the decrypted cookie in wg_cookie_message_consume.

A cookie is a MAC of the sender's address and port under a secret that
changes every two minutes, so these are of low value.
(cookie_message_create_spec.ml, cookie_validate_packet_spec.ml,
cookie_message_consume_spec.ml)

## Logic and concurrency (benign)

F4. make_cookie checks whether the cookie secret has expired before taking
the secret's lock, then takes the lock for writing and makes a new secret
without checking again. Two CPUs that both see the old secret can therefore
both replace it, one after the other. The only effect is an extra change of
secret, which invalidates cookies made with the first new one a little
early. (make_cookie_spec.ml)

F5. In wg_noise_handshake_consume_initiation the flood check (at most one
initiation per 20 ms) casts both sides to s64, but the constant added on the
left (the nanoseconds per second divided by INITIATIONS_PER_SECOND) has the
type of enum limits. That enumeration has members near U64_MAX, so its type
is unsigned 64-bit, and the comparison is unsigned (cset hi in the code).
The casts suggest otherwise, but the result is the same for real clock
values, which are far below 2^63.
(noise_handshake_consume_initiation_spec.ml)

F6. wg_noise_handshake_consume_response declares a local static_private and
wipes it at the end, but never uses it: the static-ephemeral Diffie-Hellman
reads the device's key directly, under the lock of the static identity.
This is dead code and harmless.

F7. wg_noise_handshake_init calls wg_noise_precompute_static_static with its
peer argument, which works on peer->handshake rather than on the handshake
argument. The function is therefore correct only when its handshake is the
peer's own, which holds at its only call, in peer.c.
(noise_handshake_init_spec.ml has that as a precondition.)

## Compiler behavior that matters for per-function proofs (not bugs)

F8. Interprocedural register allocation (-fipa-ra): hchacha_block_generic
relies on chacha_permute, a static function, preserving x0, which the
procedure call standard lets a callee change. The theorem for chacha_permute
has to state that it does preserve x0. (chacha_permute_spec.ml)

F9. Interprocedural value-range propagation: the copy of blake2s() that gcc
specializes for cookie.c (blake2s.constprop.0) omits the keylen == 0 test of
__blake2s_init, because both its callers pass a nonzero key length. Its
theorem therefore needs 0 < keylen. (blake2s_constprop_0_2_spec.ml)

F10. Code patched at boot: at each atomic operation in
wg_noise_keypair_get, wg_noise_keypair_put and
wg_noise_handshake_begin_session, the image has both the LL/SC sequence
(ldxr/stxr) and the ARMv8.1 LSE instruction (cas, ldaddl, ldaddal), chosen
by a branch that the kernel patches at boot when the CPU supports LSE. The
image as built takes the LL/SC path. Proofs of the bytes as built therefore
cover CPUs without LSE (or the code before patching); LSE-capable CPUs, such
as AWS Graviton2 and later, run the other path.
